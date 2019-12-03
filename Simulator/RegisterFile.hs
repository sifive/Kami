
module Simulator.RegisterFile where

import Simulator.Evaluate
import Simulator.Parse
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.BitVector as BV
import qualified Data.HashMap as M
import qualified Data.Array.MArray as MA
import qualified Data.Array.IO as A

import Debug.Trace
import Control.Monad
import Data.Foldable (foldrM)
import Data.Maybe (fromJust, catMaybes)
import System.Environment (getArgs)

data RegFile = RegFile {
      fileName :: String
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
    , arrs :: M.Map String (A.IOArray Int Val) -- map between filenames and arrays
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

array_of_file :: FileState -> RegFile -> A.IOArray Int Val
array_of_file state file =
    case M.lookup (fileName file) (arrs state) of
        Just arr -> arr
        Nothing -> error $ "File " ++ fileName file ++ " not found in current state."

file_async_read :: FileState -> RegFile -> Int -> IO (A.IOArray Int Val)
file_async_read state file i 
    | i < 0 = error "Read out of bounds."
    | otherwise = slice i (chunkSize file) (array_of_file state file)

file_sync_readreq :: Val -> FileState -> RegFile -> String -> IO Val
file_sync_readreq val state file regName = case readers file of
    T.Async _ -> error "Async encountered when Sync was expected."
    T.Sync isAddr rs -> if isAddr

        then

            --isAddr = True
            return $ trace (show $ bvCoerce val) val

        else

            --isAddr = False
            liftM ArrayVal $ slice (fromIntegral i) (chunkSize file) (array_of_file state file)

                where i = BV.nat $ bvCoerce val

file_sync_readresp :: FileState -> RegFile -> String -> IO Val
file_sync_readresp state file regName = case readers file of
    T.Async _ -> error "Async encountered when Sync was expected."
    T.Sync isAddr rs -> if isAddr

        then

            --isAddr = True
            case M.lookup regName $ int_regs state of
                Just v -> liftM ArrayVal $ slice (trace ("i = " ++ show i ++ "\n") $ fromIntegral i) (chunkSize file) (array_of_file state file)

                    where i = BV.nat $ bvCoerce v

                Nothing -> error $ "Register " ++ regName ++ " not found."

        else

            --isAddr = False
            case M.lookup regName $ int_regs state of
                Just v -> return v
                Nothing -> error $ "Register " ++ regName ++ " not found."

file_writes_mask :: RegFile -> Int -> IO (A.IOArray Int Bool) -> A.IOArray Int Val -> IO [(Int,Val)]
file_writes_mask file i mask vals = do
    m <- mask
    mask_indices <- filterM (MA.readArray m) [0..(chunkSize file - 1)] 
    pair_sequence $ map (\j -> (i+j, MA.readArray vals j)) mask_indices

file_writes_no_mask :: RegFile -> Int -> A.IOArray Int Val -> IO [(Int,Val)]
file_writes_no_mask file i vals =
   pair_sequence $ map (\j -> (i+j, MA.readArray vals j)) [0 .. (chunkSize file - 1)]

rf_methcall :: FileState -> String -> Val -> Maybe (Maybe (IO FileUpd), IO Val)
rf_methcall state methName val =
    case M.lookup methName $ methods state of
        Just (fc, fileName) -> 
            case fc of
                AsyncRead -> Just (Nothing, liftM ArrayVal $ file_async_read state (file_of_fname fileName) arg_index)
                ReadReq regName -> Just (Just $ liftM2 IntRegWrite (pure regName) $ file_sync_readreq val state (file_of_fname fileName) regName, return $ BVVal $ BV.nil)
                ReadResp regName -> Just (Nothing, file_sync_readresp state (file_of_fname fileName) regName)
                Write -> Just (Just $ liftM2 ArrWrite (pure fileName) (writes fileName) , return $ BVVal BV.nil)
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

        arg_mask = do
            let mask = arrayCoerce $ struct_field_access "mask" val
            MA.mapArray boolCoerce mask

        --arg_mask = V.map boolCoerce $ arrayCoerce $ struct_field_access "mask" val


exec_file_update :: FileUpd -> FileState -> IO FileState
exec_file_update (IntRegWrite regName v) state =
    return $ state { int_regs = M.adjust (const v) regName $ int_regs state }
exec_file_update (ArrWrite fileName changes) state = do
    let arr = arrs state M.! fileName
    do_writes arr changes
    return state

exec_file_updates :: FileState -> [FileUpd] -> IO FileState
exec_file_updates = foldrM exec_file_update

process_args :: [String] -> [(String,String)]
process_args = catMaybes . map (binary_split '=')

initialize_file :: Modes -> [(String,FilePath)] -> T.RegFileBase -> FileState -> IO FileState
initialize_file modes args rfb@(T.Build_RegFileBase rfIsWrMask rfNum rfDataArray rfRead rfWrite rfIdxNum rfData rfInit) state = do

    arr <- array

    let fn = rfDataArray

    let rf = RegFile {
        fileName = fn
        , isWrMask = rfIsWrMask 
        , chunkSize = rfNum 
        , readers = rfRead 
        , write = rfWrite 
        , size = rfIdxNum 
        , kind = rfData 
    }

    let reads = case rfRead of
                    T.Async rs -> map (\r -> (r,(AsyncRead, fn))) rs
                    T.Sync _ rs -> map (\r -> (T.readReqName r,(ReadReq $ T.readRegName r, fn))) rs ++
                                 map (\r -> (T.readResName r, (ReadResp $ T.readRegName r, fn))) rs

    let newmeths = (rfWrite, (Write, rfDataArray)) : reads

    let newregs = case rfRead of
                    T.Async _ -> []
                    T.Sync _ rs -> map (\r -> (T.readReqName r, T.readRegName r)) rs ++
                                   map (\r -> (T.readResName r, T.readRegName r)) rs

    newvals <- case rfRead of
                    T.Async _ -> return []
                    T.Sync b rs -> mapM (\r -> do
                                                v <- defVal (if b then T.Bit (log2 $ rfIdxNum) else rfData)
                                                return (T.readRegName r, v)) rs

    return $ state {
                      methods = inserts (methods state) newmeths
                    , int_regs = inserts (int_regs state) newvals
                    , arrs = M.insert fn arr $ arrs state
                    , files = M.insert fn rf $ files state
                }

     where

        array = case rfInit of
            T.RFNonFile Nothing -> do
                let debug = debug_mode modes
                dv <- defVal rfData
                MA.newArray (0,rfIdxNum-1) dv --TODO: add random vals back in
            T.RFNonFile (Just c) -> do
                v <- eval c
                MA.newArray (0,rfIdxNum-1) v
            T.RFFile isAscii isArg file _ _ _ -> 
                parseHex isAscii (rfData) (rfIdxNum) filepath

                where

                    filepath = if isArg then
                        case lookup file args of
                            Nothing -> error $ "Argument " ++ file ++ " not found."
                            Just fp -> fp

                        else file

initialize_files :: Modes -> [T.RegFileBase] -> IO FileState
initialize_files modes rfbs = do
    args <- getArgs
    foldrM (initialize_file modes $ process_args args) empty_state rfbs
