
module Simulator.RegisterFile where

import Simulator.Evaluate
import Simulator.Parse
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.BitVector as BV
import qualified Data.HashMap as M
import qualified Data.Vector as V

import Data.Foldable (foldrM)
import Data.Maybe (fromJust, catMaybes)
import System.Environment (getArgs)

data RegFile = RegFile {
      fileName :: String
--    , offset :: Int
    , isWrMask :: Bool
    , chunkSize :: Int
    , readers :: T.RegFileReaders
    , write :: String
    , size :: Int
    , kind :: T.Kind
}

data FileState = FileState {
      methods :: M.Map String (FileCall,String) -- map between method names and method type + filename
    , int_regs :: M.Map String Val -- map between intermediate registers and their values
    , arrs :: M.Map String (V.Vector Val) -- map between filenames and arrays
    , files :: M.Map String RegFile -- map between filenames and files
}

empty_state :: FileState
empty_state = FileState {
      methods = M.empty
    , int_regs = M.empty
    , arrs = M.empty 
    , files = M.empty
}

data FileCall = AsyncRead | ReadReq String | ReadResp String | Write

data FileUpd = IntRegWrite String Val | ArrWrite String [(Int, Val)]

array_of_file :: FileState -> RegFile -> V.Vector Val
array_of_file state file =
    case M.lookup (fileName file) (arrs state) of
        Just arr -> arr
        Nothing -> error $ "File " ++ fileName file ++ " not found in current state."

file_async_read :: FileState -> RegFile -> Int -> V.Vector Val
file_async_read state file i 
    | i < 0 = error "Read out of bounds."
    | otherwise = V.slice i (chunkSize file) (array_of_file state file)

file_sync_readresp :: FileState -> RegFile -> String -> Val
file_sync_readresp state file regName = case readers file of
    T.Async _ -> error "Async encountered when Sync was expected."
    T.Sync isAddr rs -> if isAddr

        then

            --isAddr = True
            case M.lookup regName $ int_regs state of
                Just v -> ArrayVal $ V.slice (fromIntegral i) (chunkSize file) (array_of_file state file)

                    where i = BV.nat $ bvCoerce v

                Nothing -> error $ "Register " ++ regName ++ " not found."

        else

            --isAddr = False
            case M.lookup regName $ int_regs state of
                Just v -> v
                Nothing -> error $ "Register " ++ regName ++ " not found."

file_writes_mask :: RegFile -> Int -> V.Vector Bool -> V.Vector Val -> [(Int,Val)]
file_writes_mask file i mask vals =
    map (\j -> (i+j, vals V.! j)) $ filter (mask V.!) [0..(chunkSize file - 1)]

file_writes_no_mask :: RegFile -> Int -> V.Vector Val -> [(Int,Val)]
file_writes_no_mask file i vals =
    map (\j -> (i+j, vals V.! j)) [0 .. (chunkSize file - 1)]


rf_methcall :: FileState -> String -> Val -> Maybe (Maybe FileUpd,Val)
rf_methcall state methName val =
    case M.lookup methName $ methods state of --maybe use do notation here
        Just (fc, fileName) -> 
            case fc of
                AsyncRead -> Just (Nothing, ArrayVal $ file_async_read state (file_of_fname fileName) arg_index)
                ReadReq regName -> Just (Just $ IntRegWrite regName val, BVVal $ BV.nil)
                ReadResp regName -> Just (Nothing, file_sync_readresp state (file_of_fname fileName) regName)
                Write -> Just (Just $ ArrWrite fileName (writes fileName) , BVVal BV.nil)
        Nothing -> Nothing

    where 

        file_of_fname fn = fromJust $ M.lookup fn $ files state

        writes fn = let file = file_of_fname fn in
            if isWrMask file 
                then file_writes_mask file arg_addr arg_mask arg_data
                else file_writes_no_mask file arg_addr arg_data 

        arg_index = fromIntegral $ BV.nat $ bvCoerce val

        arg_addr = fromIntegral $ BV.nat $ bvCoerce $ struct_field_access "addr" val

        arg_data = arrayCoerce $ struct_field_access "data" val

        arg_mask = V.map boolCoerce $ arrayCoerce $ struct_field_access "mask" val

exec_file_update :: FileUpd -> FileState -> FileState
exec_file_update (IntRegWrite regName v) state =
    state { int_regs = M.adjust (const v) regName $ int_regs state }
exec_file_update (ArrWrite fileName changes) state =
    state { arrs = M.adjust (flip (V.//) changes) fileName $ arrs state }

exec_file_updates :: FileState -> [FileUpd] -> FileState
exec_file_updates = foldr exec_file_update

process_args :: [String] -> [(String,String)]
process_args = catMaybes . map (binary_split '=')

initialize_file :: [(String,FilePath)] -> T.RegFileBase -> FileState -> IO FileState
initialize_file args rfb state = do

    arr <- array

    let fn = T.rfDataArray rfb

    let rf = RegFile {
        fileName = fn
 --       , offset = 0 -- off
        , isWrMask = T.rfIsWrMask rfb
        , chunkSize = T.rfNum rfb
        , readers = T.rfRead rfb
        , write = T.rfWrite rfb
        , size = T.rfIdxNum rfb
        , kind = T.rfData rfb
    }

    let reads = case T.rfRead rfb of
                    T.Async rs -> map (\r -> (r,(AsyncRead, fn))) rs
                    T.Sync _ rs -> map (\r -> (T.readReqName r,(ReadReq $ T.readRegName r, fn))) rs ++
                                 map (\r -> (T.readResName r, (ReadResp $ T.readRegName r, fn))) rs

    let newmeths = (T.rfWrite rfb, (Write, T.rfDataArray rfb)) : reads

    let newregs = case T.rfRead rfb of
                    T.Async _ -> []
                    T.Sync _ rs -> map (\r -> (T.readReqName r, T.readRegName r)) rs ++
                                   map (\r -> (T.readResName r, T.readRegName r)) rs

    newvals <- case T.rfRead rfb of
                    T.Async _ -> return []
                    T.Sync b rs -> mapM (\r -> do
                                                v <- randVal (if b then T.Bit (log2 $ T.rfIdxNum rfb) else T.rfData rfb)
                                                return (T.readRegName r, v)) rs

    return $ state {
                      methods = inserts (methods state) newmeths
                    , int_regs = inserts (int_regs state) newvals
                    , arrs = M.insert fn arr $ arrs state
                    , files = M.insert fn rf $ files state
                }

     where

        array = case T.rfInit rfb of
            T.RFNonFile Nothing -> do
--                vs <- V.replicateM (T.rfIdxNum rfb) (randVal $ T.rfData rfb)
                vs <- mapM randVal $ V.replicate (T.rfIdxNum rfb) (T.rfData rfb)
                return vs
            T.RFNonFile (Just c) -> return $ V.replicate (T.rfIdxNum rfb) (eval c)
            T.RFFile isAscii isArg file _ _ _ -> 
                parseHex isAscii (T.rfData rfb) (T.rfIdxNum rfb) filepath

                where

                    filepath = if isArg then
                        case lookup file args of
                            Nothing -> error $ "Argument " ++ file ++ " not found."
                            Just fp -> fp

                        else file

initialize_files :: [T.RegFileBase] -> IO FileState
initialize_files rfbs = do
    args <- getArgs
    foldrM (initialize_file $ process_args args) empty_state rfbs
