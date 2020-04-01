
module Simulator.Util where

import qualified Data.HashMap as M
import qualified Data.BitVector as BV
import qualified Data.Text as T

import qualified Data.Array.MArray as MA

import Control.Monad
import Data.Hashable
import Data.Text.Read (hexadecimal)
import System.Environment (getArgs)
import System.IO.Unsafe (unsafePerformIO)

pair_sequence ::  [(a,IO b)] ->  IO [(a,b)]
--pair_sequence xs = sequence $ map (\(a,m) -> m >>= (\b -> return (a,b))) xs
pair_sequence xs = return $ map (\(a,m) -> (a, unsafePerformIO m)) xs

space_pad :: Int -> String -> String
space_pad n str = replicate (n - length str) ' ' ++ str

zero_pad :: Int -> String -> String
zero_pad n str = replicate (n - length str) '0' ++ str

resize_num :: Int -> String -> String
resize_num n num
    | n > length num = replicate (n - length num) '0' ++ num
    | otherwise = drop (length num - n) num

pair_update :: (Ord a, Hashable a) => (a,b) -> M.Map a b -> M.Map a b
pair_update (a,b) m = M.adjust (const b) a m

updates :: (Ord a, Hashable a) => M.Map a b -> [(a,b)] -> M.Map a b
updates = foldr pair_update 

inserts :: (Ord a, Hashable a) => M.Map a b -> [(a,b)] -> M.Map a b
inserts = foldr (uncurry M.insert)

execIOs :: [IO ()] -> IO ()
execIOs = foldr (>>) (return ())

cdiv :: Int -> Int -> Int
cdiv x y = ceiling (fromIntegral x / fromIntegral y)

log2 :: Int -> Int
log2 = ceiling . (logBase 2) . fromIntegral

hex_to_maybe_integer :: T.Text -> Maybe Integer
hex_to_maybe_integer txt = case hexadecimal txt of
    Left str -> Nothing
    Right (x,str) -> if T.null str then Just x else Nothing

hex_to_maybe_integer_str :: String -> Maybe Integer
hex_to_maybe_integer_str = hex_to_maybe_integer . T.pack

hex_to_integer :: T.Text -> Integer
hex_to_integer txt = case hexadecimal txt of
    Left str -> error $ "Formatting error: " ++ str
    Right (x,str) -> if T.null str then x else error $ "Formatting error, extra text: " ++ T.unpack str

hex_to_bv :: Int -> T.Text -> BV.BV
hex_to_bv n = (BV.bitVec n) . hex_to_integer

partition :: [Int] {- chunksizes -} -> BV.BV -> [BV.BV]
partition [] _ = []
partition (n:ns) v = (BV.most n v) : partition ns (BV.least (BV.size v - n) v)

--tries to split a list at the first occurrence of the given character, discarding that character
binary_split :: Eq a => a -> [a] -> Maybe ([a],[a])
binary_split x xs = go xs [] where
    go [] _ = Nothing
    go (y:ys) acc = if x == y then Just (reverse acc, ys) else go ys (y:acc)

--type of infinite streams
data Str a = (:+) a (Str a) | EndOfCycle (Str a)

unwind_list :: [a] -> Str a
unwind_list xs = go xs where
    go [] = EndOfCycle $ go xs
    go (y:ys) = y :+ go ys

--applies the function to every n+1th elt of the stream
intersperse_with_period :: Int -> (a -> a) -> Str a -> Str a
intersperse_with_period n f xs = go n xs where
    go 0 (x :+ ys) = f x :+ go n ys
    go m (x :+ ys) = x :+ go (m-1) ys

data Modes = Modes {
      debug_mode :: Bool
    , interactive_mode :: Bool
    , no_print_mode :: Bool
}

get_modes :: IO Modes
get_modes = do
    args <- getArgs
    return $ Modes {
          debug_mode = "--debug" `elem` args
        , interactive_mode = "--interactive" `elem` args
        , no_print_mode = "--noprint" `elem` args
    }

do_writes :: (MA.MArray a e m, MA.Ix i) => a i e -> [(i,e)] -> m ()
do_writes a ps = foldM (\_ (i,e) -> MA.writeArray a i e) () ps

slice :: (MA.MArray a e m) => Int -> Int -> a Int e -> m (a Int e)
slice i_0 size arr = do
    vals <- sequence $ map (\j -> MA.readArray arr (i_0 + j)) [0..(size-1)]
    MA.newListArray (0,size-1) vals

arr_length :: (MA.MArray a e m) => a Int e -> m Int
arr_length arr = do
    (i,j) <- MA.getBounds arr
    return (j - i)

{-
debug_mode :: IO Bool
debug_mode = do
    args <- getArgs
    return $ "--debug" `elem` args

interactive_mode :: IO Bool
interactive_mode = do
    args <- getArgs
    return $ "--interactive" `elem` args

no_print_mode :: IO Bool
no_print_mode = do
    args <- getArgs
    return $ "--noprint" `elem` args
-}
