
module Simulator.Parse where

import qualified HaskellTarget as H

import qualified Data.BitVector as BV
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Text.Read (hexadecimal)

import Simulator.Util
import Simulator.Value
import Simulator.Evaluate

import Data.Char (isSpace)
import Data.List.Split (wordsBy)

data Tok = Addr Integer | Value BV.BV deriving (Show)

readTok :: Int -> T.Text -> Tok
readTok n txt = let txt' = T.filter (/= '_') txt in
    case T.uncons txt' of
        Just ('@',addr) -> Addr $ hex_to_integer addr
        Just _ -> Value $ hex_to_bv n txt'
        Nothing -> error "Empty text chunk encountered."

getToks :: Int -> T.Text -> [(Integer, BV.BV)]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (filter (not . T.null)) . (T.split isSpace)) $ T.lines text

word_of_bv :: BV.BV -> H.Coq_word
word_of_bv v = H.natToWord (BV.size v) (fromIntegral $ BV.nat v)

expr_of_bv :: BV.BV -> H.Expr Val
expr_of_bv v = H.Const (H.Bit $ BV.size v) $ H.ConstBit (BV.size v) $ word_of_bv v

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

offset_pairs :: [(Integer, BV.BV)] -> (Int, [(Integer, BV.BV)])
offset_pairs [] = (0, [])
offset_pairs ((n,v):ps) = (fromIntegral n, (0,v):map (\(i,v') -> (i-n, v')) ps)

parseHex :: Bool -> H.Kind -> Int ->  FilePath -> IO (V.Vector Val, Int)
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- T.readFile filepath
        let (n,pairs) = offset_pairs $ getToks (H.size k) text
        let v_init = V.replicate (arrSize - n) (defVal k)
        let val_pairs = map (\(i,v) -> (fromIntegral i, eval $ H.unpack k $ expr_of_bv v)) pairs
        return (v_init V.// val_pairs, n)

    | otherwise = error "Binary not yet supported."