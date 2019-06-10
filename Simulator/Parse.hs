
module Simulator.Parse where

import qualified HaskellTarget as H

import qualified Data.BitVector as BV
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Text.Read (hexadecimal)

import Simulator.Util
import Simulator.Value
--import Simulator.Evaluate

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

word_of_bv :: BV.BV -> (Int,Integer)
word_of_bv v = (BV.size v, BV.nat v)

expr_of_bv :: BV.BV -> H.Expr Val
expr_of_bv v = H.Const (H.Bit $ BV.size v) $ H.ConstBit (BV.size v) $ word_of_bv v

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

offset_pairs :: Int -> [(Integer, BV.BV)] -> [(Integer, BV.BV)]
offset_pairs offset ps = map (\(i,v) -> (i - fromIntegral offset,v)) ps

partition :: [Int] {- chunksizes -} -> BV.BV -> [BV.BV]
partition [] _ = []
partition (n:ns) v = (BV.most n v) : partition ns (BV.least (BV.size v - n) v)

myunpack :: H.Kind -> BV.BV -> Val
myunpack H.Bool v = BoolVal $ v BV.@. 0
myunpack (H.Bit _) v = BVVal v
myunpack (H.Array n k) v = ArrayVal $ V.fromList $ map (myunpack k) $ BV.split n v
myunpack (H.Struct n kinds names) v =
    let names' = map names $ H.getFins n in
    let kinds' = map kinds $ H.getFins n in
    let bvs = partition (map H.size kinds') v in
        StructVal $ zip names' (zipWith myunpack kinds' bvs) 



parseHex :: Bool -> H.Kind -> Int -> Int -> FilePath -> IO (V.Vector Val)
parseHex isAscii k arrSize offset filepath
    | isAscii = do
        text <- T.readFile filepath
        let pairs = offset_pairs offset $ getToks (H.size k) text
        let v_init = V.replicate (arrSize - offset) (defVal k)
--        let val_pairs = map (\(i,v) -> (fromIntegral i, eval $ H.unpack k $ expr_of_bv v)) pairs
        let val_pairs = map (\(i,v) -> (fromIntegral i, myunpack k v)) pairs
        return $ v_init V.// val_pairs

    | otherwise = error "Binary not yet supported."