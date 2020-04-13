
module Simulator.RegisterFile where

import Simulator.Classes
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

data FileState m a v = FileState {
      methods :: m (FileCall,String) -- map between method names and method type + filename
    , int_regs :: m (Val v) -- map between intermediate registers and their values
    , arrs :: m (a (Val v)) -- map between filenames and arrays
    , files :: m RegFile -- map between filenames and files
}

empty_state :: StringMap m => FileState m a v
empty_state = FileState {
      methods = empty_map
    , int_regs = empty_map
    , arrs = empty_map
    , files = empty_map
}

data FileCall = AsyncRead | ReadReq String | ReadResp String | Write

data FileUpd v = IntRegWrite String (Val v) | ArrWrite String [(Int, Val v)]

array_of_file :: StringMap m => FileState m a v -> RegFile -> a (Val v)
array_of_file state file =
    case map_lookup (fileName file) (arrs state) of
        Just arr -> arr
        Nothing -> error $ "File " ++ fileName file ++ " not found in current state."

file_async_read :: (StringMap m, Array a, Vec v) => FileState m a v -> RegFile -> Int -> IO (v (Val v))
file_async_read state file i 
    | i < 0 = error "Read out of bounds."
    | otherwise = array_slice i (chunkSize file) (array_of_file state file)

file_sync_readreq :: (StringMap m, Array a, Vec v) => Val v -> FileState m a v -> RegFile -> String -> IO (Val v)
file_sync_readreq val state file regName = case readers file of
    T.Async _ -> error "Async encountered when Sync was expected."
    T.Sync isAddr rs -> if isAddr

        then

            --isAddr = True
            return $ {-trace (show $ bvCoerce val)-} val

        else

            --isAddr = False
            liftM ArrayVal $ array_slice (fromIntegral i) (chunkSize file) (array_of_file state file)

                where i = BV.nat $ bvCoerce val

file_sync_readresp :: (Array a, StringMap m, Vec v) => FileState m a v -> RegFile -> String -> IO (Val v)
file_sync_readresp state file regName = case readers file of
    T.Async _ -> error "Async encountered when Sync was expected."
    T.Sync isAddr rs -> if isAddr

        then

            --isAddr = True
            case map_lookup regName $ int_regs state of
                Just v -> liftM ArrayVal $ array_slice ({- trace ("i = " ++ show i ++ "\n") $-} fromIntegral i) (chunkSize file) (array_of_file state file)

                    where i = BV.nat $ bvCoerce v

                Nothing -> error $ "Register " ++ regName ++ " not found."

        else

            --isAddr = False
            case map_lookup regName $ int_regs state of
                Just v -> return v
                Nothing -> error $ "Register " ++ regName ++ " not found."

file_writes_mask :: Vec v => RegFile -> Int -> v Bool -> v (Val v) -> [(Int,Val v)]
file_writes_mask file i mask vals =
    let mask_indices = filter (\j -> vector_index j mask) [0..(chunkSize file - 1)] in
    map (\j -> (i+j, vector_index j vals)) mask_indices

file_writes_no_mask :: Vec v => RegFile -> Int -> v (Val v) -> [(Int,Val v)]
file_writes_no_mask file i vals =
   map (\j -> (i+j, vector_index j vals)) [0 .. (chunkSize file - 1)]

rf_methcall :: (StringMap m, Vec v, Array a) => FileState m a v -> String -> Val v -> Maybe (Maybe (IO (FileUpd v)), IO (Val v))
rf_methcall state methName val =
    case map_lookup methName $ methods state of
        Just (fc, fileName) -> 
            case fc of
                AsyncRead -> Just (Nothing, liftM ArrayVal $ file_async_read state (file_of_fname fileName) arg_index)
                ReadReq regName -> Just (Just $ liftM2 IntRegWrite (pure regName) $ file_sync_readreq val state (file_of_fname fileName) regName, return $ BVVal $ BV.nil)
                ReadResp regName -> Just (Nothing, file_sync_readresp state (file_of_fname fileName) regName)
                Write -> Just (Just $ return $ (ArrWrite fileName) (writes fileName) , return $ BVVal BV.nil)
        Nothing -> Nothing

    where 

        file_of_fname fn = fromJust $ map_lookup fn $ files state

        writes fn = let file = file_of_fname fn in
            if isWrMask file 
                then file_writes_mask file arg_addr arg_mask arg_data
                else file_writes_no_mask file arg_addr arg_data 

        arg_index = fromIntegral $ BV.nat $ bvCoerce val
        arg_addr = fromIntegral $ BV.nat $ bvCoerce $ struct_field_access "addr" val
        arg_data = arrayCoerce $ struct_field_access "data" val
        arg_mask = fmap boolCoerce $ arrayCoerce $ struct_field_access "mask" val

exec_file_update :: (Array a, StringMap m) => FileUpd v -> FileState m a v -> IO (FileState m a v)
exec_file_update (IntRegWrite regName v) state =
    return $ state { int_regs = map_insert regName v $ int_regs state }
exec_file_update (ArrWrite fileName changes) state = do
    let arr = case map_lookup fileName $ arrs state of
                    Nothing -> error ("File " ++ fileName ++ " not found.")
                    Just a -> a
    array_writes changes arr
    return state

exec_file_updates :: (Array a, StringMap m) => FileState m a v -> [FileUpd v] -> IO (FileState m a v)
exec_file_updates = foldrM exec_file_update

process_args :: [String] -> [(String,String)]
process_args = catMaybes . map (binary_split '=')

initialize_file :: (Array a, Vec v, StringMap m) => Modes -> [(String,FilePath)] -> T.RegFileBase -> FileState m a v -> IO (FileState m a v)
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
                                                let v = defVal (if b then T.Bit (log2 $ rfIdxNum) else rfData)
                                                return (T.readRegName r, v)) rs

    return $ state {
                      methods = map_inserts newmeths (methods state)
                    , int_regs = map_inserts newvals (int_regs state)
                    , arrs = map_insert fn arr $ arrs state
                    , files = map_insert fn rf $ files state
                }

     where

        array = case rfInit of
            T.RFNonFile Nothing -> do
                let debug = debug_mode modes
                let dv = defVal rfData
                array_replicate rfIdxNum dv --TODO: add random vals back in
            T.RFNonFile (Just c) -> do
                let v = eval_ConstT c
                array_replicate rfIdxNum v
            T.RFFile isAscii isArg file _ _ _ -> 
                parseHex isAscii (rfData) (rfIdxNum) filepath

                where

                    filepath = if isArg then
                        case lookup file args of
                            Nothing -> error $ "Argument " ++ file ++ " not found."
                            Just fp -> fp

                        else file

initialize_files :: (Array a, Vec v, StringMap m) => Modes -> [T.RegFileBase] -> IO (FileState m a v)
initialize_files modes rfbs = do
    args <- getArgs
    foldrM (initialize_file modes $ process_args args) empty_state rfbs
