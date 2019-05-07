
module Simulator.Util where

import qualified Data.Map as M

space_pad :: Int -> String -> String
space_pad n str = replicate (n - length str) ' ' ++ str

dropLast :: Int -> [a] -> [a]
dropLast n = reverse . (drop n) . reverse

list_lshift :: Int -> a -> [a] -> [a]
list_lshift n x xs = replicate (min n (length xs)) x ++ dropLast n xs

list_rshift :: Int -> a -> [a] -> [a]
list_rshift n x xs = drop n xs ++ replicate (min n (length xs)) x

list_rshift_a :: Int -> [a] -> [a]
list_rshift_a _ [] = []
list_rshift_a n xs = drop n xs ++ replicate (min n (length xs)) (last xs)

int_of_list :: [Bool] -> Int
int_of_list [] = 0
int_of_list (b:xs) = (if b then 1 else 0) + 2 * int_of_list xs

list_of_int :: Int {- length -} -> Int {- value -} -> [Bool]
list_of_int 0 _ = []
list_of_int n x = (not $ even x) : list_of_int (n-1) (x `div` 2)

pair_update :: Ord a => (a,b) -> M.Map a b -> M.Map a b
pair_update (a,b) m = M.adjust (const b) a m

updates :: Ord a => M.Map a b -> [(a,b)] -> M.Map a b
updates = foldr pair_update 

inserts :: Ord a => M.Map a b -> [(a,b)] -> M.Map a b
inserts = foldr (uncurry M.insert)

execIOs :: [IO ()] -> IO ()
execIOs = foldr (>>) (return ())

log2 :: Int -> Int
log2 = ceiling . (logBase 2) . fromIntegral

--tries to split a list at the first occurence of the given character, discarding that character
binary_split :: Eq a => a -> [a] -> Maybe ([a],[a])
binary_split x xs = go xs [] where
    go [] _ = Nothing
    go (y:ys) acc = if x == y then Just (reverse acc, ys) else go ys (y:acc)

--type of infinite streams
data Str a = (:+) a (Str a)

--applies the function to every n+1th elt of the stream
intersperse_with_period :: Int -> (a -> a) -> Str a -> Str a
intersperse_with_period n f xs = go n xs where
    go 0 (x :+ ys) = f x :+ go n ys
    go m (x :+ ys) = x :+ go (m-1) ys
