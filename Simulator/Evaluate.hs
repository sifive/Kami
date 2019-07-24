{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Simulator.Evaluate where

import Simulator.Util
import Simulator.Value

--import Debug.Trace

import qualified HaskellTarget as T

import Data.Bits
import qualified Data.BitVector as BV
import qualified Data.Vector as V

import GHC.Base (unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#

-- list_of_word :: T.Coq_word -> [Bool]
-- list_of_word T.WO = []
-- list_of_word (T.WS b _ w) = b : (list_of_word w)

class Eval a b where
    eval :: a -> b

instance Eval T.ConstT Val where
    eval (T.ConstBool b) = BoolVal b
    eval (T.ConstBit _ (n,v)) = BVVal $ BV.bitVec n v
    eval (T.ConstStruct n _ names fields) = StructVal $ map 
        (\i -> (names i, eval $ fields i)) (T.getFins n)
    eval (T.ConstArray n _ vals) = ArrayVal $ V.map (eval . vals) (V.fromList $ T.getFins n)

instance Eval (T.UniBoolOp) (Bool -> Bool) where
    eval T.Neg = not

instance Eval (T.CABoolOp) ([Bool] -> Bool) where
    eval T.And = foldr (&&) True
    eval T.Or = foldr (||) False
    eval T.Xor = foldr (/=) False

instance Eval T.UniBitOp (BV.BV -> BV.BV) where
    eval (T.Inv _) = BV.not
    eval (T.TruncLsb m _) = if m == 0 then const BV.nil else BV.least m
    eval (T.TruncMsb _ n) = if n == 0 then const BV.nil else BV.most n
    eval (T.UAnd _) = \v -> BV.fromBool $ BV.foldr (&&) True v
    eval (T.UOr _) = \v -> BV.fromBool $ BV.foldr (||) False v
    eval (T.UXor _) = \v -> BV.fromBool $ BV.foldr (/=) False v

instance Eval T.BinBitOp (BV.BV -> BV.BV -> BV.BV) where
    eval (T.Sub _) = (-)
    eval (T.Div _) = div
    eval (T.Rem _) = rem
    eval (T.Sll _ _) = BV.shl
    eval (T.Srl m n) = BV.shr
    eval (T.Sra m n) = BV.ashr
    eval (T.Concat _ _) = (BV.#)

instance Eval T.CABitOp (Int -> [BV.BV] -> BV.BV) where
    eval T.Add _ = foldr (+) 0
    eval T.Mul _ = foldr (*) 1
    eval T.Band n = foldr (.&.) $ BV.ones n
    eval T.Bor n = foldr (.|.) $ BV.zeros n
    eval T.Bxor n = foldr xor $ BV.zeros n

instance Eval (T.Expr ty) Val where
    eval (T.Var (T.SyntaxKind _) x) = unsafeCoerce x
    eval (T.Var (T.NativeKind _) _) = error "Encountered a NativeKind."
    eval (T.Const _ c) = eval c
    eval (T.UniBool o e) = BoolVal $ eval o $ boolCoerce $ eval e
    eval (T.CABool o es) = BoolVal $ eval o $ map (boolCoerce . eval) es
    eval (T.UniBit m n o e) = BVVal $ eval o $ bvCoerce $ eval e
    eval (T.CABit n o es) = BVVal $ eval o n $ map (bvCoerce . eval) es
    eval (T.BinBit _ _ _ o e1 e2) = BVVal $ eval o (bvCoerce $ eval e1) (bvCoerce $ eval e2)
    eval (T.BinBitBool _ _ _ e1 e2) = BoolVal $ (bvCoerce $ eval e1) BV.<. (bvCoerce $ eval e2) --only works a.t.m. because there is only one BinBitBoolOp
    eval (T.ITE _ e1 e2 e3) = if (boolCoerce $ eval e1) then eval e2 else eval e3
    eval (T.Eq _ e1 e2) = case eval e1 of
        BoolVal b -> BoolVal $ b == (boolCoerce $ eval e2)
        BVVal v -> BoolVal $ v == (bvCoerce $ eval e2)
        StructVal s -> BoolVal $ s == (structCoerce $ eval e2)
        ArrayVal a -> BoolVal $ a == (arrayCoerce $ eval e2)
    eval (T.ReadStruct _ _ names e i) = case lookup (names i) (structCoerce $ eval e) of
        Just v -> v
        Nothing -> error ("Field " ++ names i ++ " not found.")
    eval (T.BuildStruct n _ names exprs) = StructVal $ map (\i -> (names i, eval $ exprs i)) (T.getFins n)
    eval (T.ReadArray n _ k a v) = 
        let i = fromIntegral $ BV.nat $ bvCoerce $ eval v in
            if i < n then (arrayCoerce $ eval a) V.! i else defVal k
    eval (T.ReadArrayConst n _ a i) = (arrayCoerce $ eval a) V.! (T.to_nat n i)
    eval (T.BuildArray n _ exprs) = ArrayVal $ V.map (eval . exprs) (V.fromList $ T.getFins n)

-- defVal :: T.Kind -> Val
-- defVal k = eval (T.getDefaultConst k)
