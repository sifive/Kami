
module Simulator.Parse where

import qualified HaskellTarget as T

import qualified Data.BitVector as BV
import qualified Data.Vector as V

import Simulator.Util
import Simulator.Value
import Simulator.Evaluate

import Data.Char (isSpace)
import Data.List.Split (wordsBy)
import Numeric (readHex)

data Tok = Addr Integer | Value BV.BV deriving (Show)

hex_to_integer :: String -> Integer
hex_to_integer h = case readHex h of
    [] -> error "Formatting error."
    (x,str):_ -> if null str then x else error "Formatting error."

readTok :: Int -> String -> Tok
readTok _ ('@' : addr) = Addr $ hex_to_integer (filter (/= '_') addr)
readTok n str = Value $ hex_to_bv n (filter (/= '_') str)

hex_to_bv :: Int -> String -> BV.BV
hex_to_bv n = (BV.bitVec n) . hex_to_integer

getToks :: Int -> String -> [(Integer, BV.BV)]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (wordsBy isSpace)) $ lines text

word_of_bv :: BV.BV -> T.Coq_word
word_of_bv v = T.natToWord (BV.size v) (fromIntegral $ BV.nat v)

expr_of_bv :: BV.BV -> T.Expr Val
expr_of_bv v = T.Const (T.Bit $ BV.size v) $ T.ConstBit (BV.size v) $ word_of_bv v

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

offset_pairs :: [(Integer, BV.BV)] -> (Int, [(Integer, BV.BV)])
offset_pairs [] = (0, [])
offset_pairs ((n,v):ps) = (fromIntegral n, (0,v):map (\(i,v') -> (i-n, v')) ps)

parseHex :: Bool -> T.Kind -> Int ->  FilePath -> IO (V.Vector Val, Int)
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- readFile filepath
        let (n,pairs) = offset_pairs $ getToks (T.size k) text
        let v_init = V.replicate (arrSize - n) (defVal k)
        let val_pairs = map (\(i,v) -> (fromIntegral i, eval $ T.unpack k $ expr_of_bv v)) pairs
        return (v_init V.// val_pairs, n)

    | otherwise = error "Binary not yet supported."