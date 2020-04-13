{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Strict #-}

module Simulator.Evaluate where

import Simulator.Util
import Simulator.Classes
import Simulator.Value

--import Debug.Trace

import qualified HaskellTarget as T

import Control.Monad
import Data.Bits
import qualified Data.Array.IO as A
import qualified Data.Array.MArray as M
import qualified Data.BitVector as BV
import qualified Data.Vector as V

import GHC.Base (unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#

eval_ConstT :: Vec v => T.ConstT -> Val v
eval_ConstT (T.ConstBool b) = BoolVal b
eval_ConstT (T.ConstBit n v) = BVVal $ BV.bitVec n v
eval_ConstT (T.ConstStruct n _ names fields) =
        StructVal $ map (\i -> (names i, eval_ConstT $ fields i)) $ T.getFins n
eval_ConstT (T.ConstArray n k vals) =
        ArrayVal $ vector_of_list $ map (eval_ConstT . vals) $ T.getFins n

eval_UniBoolOp :: T.UniBoolOp -> Bool -> Bool
eval_UniBoolOp T.Neg = not

eval_CABoolOp :: T.CABoolOp -> [Bool] -> Bool
eval_CABoolOp T.And = foldr (&&) True
eval_CABoolOp T.Xor = foldr (/=) False

eval_UniBitOp :: T.UniBitOp -> BV.BV -> BV.BV
eval_UniBitOp (T.Inv _) = BV.not
eval_UniBitOp (T.TruncLsb m _) = if m == 0 then const BV.nil else BV.least m
eval_UniBitOp (T.TruncMsb _ n) = if n == 0 then const BV.nil else BV.most n
eval_UniBitOp (T.UAnd _) = \v -> BV.fromBool $ BV.foldr (&&) True v
eval_UniBitOp (T.UOr _) = \v -> BV.fromBool $ BV.foldr (||) False v
eval_UniBitOp (T.UXor _) = \v -> BV.fromBool $ BV.foldr (/=) False v

eval_BinBitOp :: T.BinBitOp -> BV.BV -> BV.BV -> BV.BV
eval_BinBitOp (T.Sub _) = (-)
eval_BinBitOp (T.Div _) = div
eval_BinBitOp (T.Rem _) = rem
eval_BinBitOp (T.Sll _ _) = BV.shl
eval_BinBitOp (T.Srl _ _) = BV.shr
eval_BinBitOp (T.Sra _ _) = BV.ashr
eval_BinBitOp (T.Concat _ _) = (BV.#)

eval_CABitOp :: T.CABitOp -> Int -> [BV.BV] -> BV.BV
eval_CABitOp T.Add _ = foldr (+) 0
eval_CABitOp T.Mul _ = foldr (*) 1
eval_CABitOp T.Band n = foldr (.&.) $ BV.ones n
eval_CABitOp T.Bxor n = foldr xor $ BV.zeros n

eval_Expr :: forall v ty. Vec v => T.Expr ty -> Val v
eval_Expr (T.Var (T.SyntaxKind _) x) = unsafeCoerce x
eval_Expr (T.Var (T.NativeKind _) x) = unsafeCoerce x
eval_Expr (T.Const _ c) = eval_ConstT c
eval_Expr (T.UniBool o e) = (BoolVal . eval_UniBoolOp o . boolCoerce) $ eval_Expr @v e
eval_Expr (T.CABool o es) = (BoolVal . eval_CABoolOp o) $ map (boolCoerce . eval_Expr @v) es
eval_Expr (T.UniBit m n o e) = (BVVal . eval_UniBitOp o . bvCoerce) $ eval_Expr @v e
eval_Expr (T.CABit n o es) = (BVVal . eval_CABitOp o n) $ map (bvCoerce . eval_Expr @v) es
eval_Expr (T.BinBit _ _ _ o e1 e2) = BVVal $ (eval_BinBitOp o) (bvCoerce $ eval_Expr @v e1) (bvCoerce $ eval_Expr @v e2)
eval_Expr (T.BinBitBool _ _ _ e1 e2) = BoolVal $ (BV.<.) (bvCoerce $ eval_Expr @v e1) (bvCoerce $ eval_Expr @v e2)
eval_Expr (T.Kor k es) = foldr bitwise_or (defVal k) (map eval_Expr es)
eval_Expr (T.ITE _ e1 e2 e3) = if boolCoerce (eval_Expr @v e1) then eval_Expr e2 else eval_Expr e3
eval_Expr (T.Eq _ e1 e2) = BoolVal $ eval_Expr @v e1 .== eval_Expr e2
eval_Expr (T.ReadStruct _ _ names e i) = case lookup (names i) (structCoerce $ eval_Expr e) of
    Just v' -> v'
    Nothing -> error ("Field " ++ names i ++ " not found.")
eval_Expr (T.BuildStruct n _ names exprs) = 
    StructVal $ map (\i -> (names i, eval_Expr $ exprs i)) (T.getFins n)
eval_Expr (T.ReadArray n m k a v) =
    let i = fromIntegral $ BV.nat $ bvCoerce $ (eval_Expr @v v) in
    if i < n then vector_index i (arrayCoerce $ eval_Expr a) else defVal k
eval_Expr (T.ReadArrayConst n _ a i) =
    let j = T.to_nat n i in
    vector_index j (arrayCoerce $ eval_Expr a)
eval_Expr (T.BuildArray n _ exprs) =
    ArrayVal $ vector_of_list $ map (eval_Expr . exprs) $ T.getFins n