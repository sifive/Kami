
module CustomExtract(
      module Data.Bits
    , module Data.Char
    , EWord
    , wordNil
    , wordCons
    , wordRec
    , EFin
    , fin0
    , finS
    , finRec
    , EVector
    , vecNil
    , vecCons
    , vecRec
    ) where

import qualified Data.Bits
import qualified Data.Char
import Debug.Trace

type EWord = (Int,Integer)

wordNil :: EWord
wordNil = (0,0)

wordCons :: Bool -> Int -> EWord -> EWord
wordCons b _ (n,v) = let v' = Data.Bits.shiftL v 1 in if b then (n+1, Data.Bits.setBit v' 0) else (n+1,v')

wordRec :: (() -> a) -> (Bool -> Int -> EWord -> a) -> EWord -> a
wordRec fnil fcons (n,v) = if n == 0 then fnil () else fcons (Data.Bits.testBit v 0) (n-1) (n-1,Data.Bits.shiftR v 1)

type EFin = (Int,Int)

fin0 :: Int -> EFin
fin0 n = (n+1,0)

finS :: Int -> EFin -> EFin
finS m (n,i) = {- trace ("{{{[finS constructor]: " ++ show m ++ " " ++ show n ++ " " ++ show i ++ " VALUE " ++ show (m == n) ++ "}}}")-} (n+1,i+1)

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

