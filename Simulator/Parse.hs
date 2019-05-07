
module Simulator.Parse where

import qualified Target as T

import qualified Data.Vector as V

import Simulator.Util
import Simulator.Value
import Simulator.Evaluate

import Data.Char (isSpace)
import Data.List.Split (wordsBy)
import Numeric (readHex)

data Tok = Addr Int | Value [Bool] deriving (Show)

hex_to_int :: String -> Int
hex_to_int h = case readHex h of
    [] -> error "Formatting error."
    (x,str):_ -> if null str then x else error "Formatting error."

readTok :: Int -> String -> Tok
readTok _ ('@' : addr) = Addr $ hex_to_int (filter (/= '_') addr)
readTok n str = Value $ hex_to_bits n (filter (/= '_') str)

hex_to_bits :: Int -> String -> [Bool]
hex_to_bits n = (list_of_int n) . hex_to_int

getToks :: Int -> String -> [(Int, [Bool])]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (wordsBy isSpace)) $ lines text

word_of_bools :: [Bool] -> T.Coq_word
word_of_bools bs = T.natToWord (length bs) (int_of_list bs)

bools_to_expr :: [Bool] -> T.Expr Val
bools_to_expr bs = T.Const (T.Bit $ length bs) $ T.ConstBit (length bs) $ word_of_bools bs

toks_to_addr_vals :: [Tok] -> [(Int, [Bool])]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

offset_pairs :: [(Int, [Bool])] -> (Int, [(Int, [Bool])])
offset_pairs [] = (0, [])
offset_pairs ((n,v):ps) = (n, (0,v):map (\(i,v') -> (i-n, v')) ps)

parseHex :: Bool -> T.Kind -> Int ->  FilePath -> IO (V.Vector Val, Int)
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- readFile filepath
        let (n,pairs) = offset_pairs $ getToks (T.size k) text
        let v_init = V.replicate (arrSize - n) (defVal k)
        let val_pairs = map (\(i,bs) -> (i, eval $ T.unpack k $ bools_to_expr bs)) pairs
        return (v_init V.// val_pairs, n)

    | otherwise = error "Binary not yet supported."