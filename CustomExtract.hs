
module CustomExtract where

import qualified Data.Bits
import qualified Data.Char
import qualified Data.BitVector as BV
import Debug.Trace
import Numeric

import Control.Monad
import Data.Text.Read (hexadecimal)

type EWord = (Int,Integer)

wordNil :: EWord
wordNil = (0,0)

wordCons :: Bool -> Int -> EWord -> EWord
wordCons b _ (n,v) = let v' = Data.Bits.shiftL v 1 in if b then (n+1, Data.Bits.setBit v' 0) else (n+1,v')

wordRec :: (() -> a) -> (Bool -> Int -> EWord -> a) -> EWord -> a
wordRec fnil fcons (n,v) = if n == 0 then fnil () else fcons (Data.Bits.testBit v 0) (n-1) (n-1,Data.Bits.shiftR v 1)

type EFin = (Int,Int)

fin0 :: Int -> EFin
fin0 n = (n,0)

finS :: Int -> EFin -> EFin
finS m (n,i) = (n+1,i+1)

finRec :: (Int -> a) -> (Int -> EFin -> a) -> EFin -> a
finRec f0 fS (n,i) = if i == 0 then f0 n else fS n (n-1, i-1)

type EVector = []

vecNil :: EVector a
vecNil = []

vecCons :: a -> Int -> EVector a -> EVector a
vecCons x _ xs = x:xs

vecRec :: (() -> b) -> (a -> Int -> EVector a -> b) -> EVector a -> b
vecRec fnil fcons v = case v of
    [] -> fnil ()
    (x:v') -> fcons x (length v') v'

nat_bin :: Integer -> String
nat_bin n = showIntAtBase 2 Data.Char.intToDigit n ""

nat_dec :: Integer -> String
nat_dec = show

nat_hex :: Integer -> String
nat_hex n = showHex n ""

bv_bin :: BV.BV -> String
bv_bin = nat_bin . BV.nat

bv_dec :: BV.BV -> String
bv_dec = nat_dec . BV.nat

bv_hex :: BV.BV -> String
bv_hex = nat_hex . BV.nat

{-
word_of_bv :: BV.BV -> (Int,Integer)
word_of_bv v = (BV.size v, BV.nat v)
expr_of_bv :: BV.BV -> H.Expr Val
expr_of_bv v = H.Const (H.Bit $ BV.size v) $ H.ConstBit (BV.size v) $ word_of_bv v
toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks
val_unpack :: H.Kind -> BV.BV -> IO Val
val_unpack H.Bool v = return $ BoolVal $ v BV.@. 0
val_unpack (H.Bit _) v = return $ BVVal v
val_unpack (H.Array n k) v = do
    vs <- mapM (val_unpack k) $ BV.split n v
    liftM ArrayVal $ M.newListArray (0,n-1) vs
val_unpack (H.Struct n kinds names) v =
    let names' = map names $ H.getFins n in
    let kinds' = map kinds $ H.getFins n in
    let bvs = partition (map H.size kinds') v in do
        ps <- pair_sequence $ zip names' (zipWith val_unpack kinds' bvs)
        return $ StructVal ps
parseHex :: Bool -> H.Kind -> Int -> FilePath -> IO (A.IOArray Int Val)
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- T.readFile filepath
        let pairs = getToks (H.size k) text
        v <- defVal k
        v_init <- M.newArray (0,arrSize-1) v
        val_pairs <- pair_sequence $ map (\(i,v) -> (fromIntegral i, val_unpack k v)) pairs
        do_writes v_init val_pairs
        return v_init
    | otherwise = error "Binary not yet supported."
    -}