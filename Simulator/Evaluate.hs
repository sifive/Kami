{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Strict #-}

module Simulator.Evaluate where

import Simulator.Util
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

class Eval a b where
    eval :: a -> b

instance Eval T.ConstT (IO Val) where
    eval (T.ConstBool b) = return $ BoolVal b
    eval (T.ConstBit n v) = return $ BVVal $ BV.bitVec n v
    eval (T.ConstStruct n _ names fields) =
        liftM StructVal $ pair_sequence $ map (\i -> (names i, eval $ fields i)) $ T.getFins n
    eval (T.ConstArray n k vals) = do
        vs <- sequence $ map (eval . vals) $ T.getFins n
        liftM ArrayVal $ M.newListArray (0,(n-1)) vs

instance Eval (T.UniBoolOp) (Bool -> Bool) where
    eval T.Neg = not

instance Eval (T.CABoolOp) ([Bool] -> Bool) where
    eval T.And = foldr (&&) True
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
    eval T.Bxor n = foldr xor $ BV.zeros n

instance Eval (T.Expr ty) (IO Val) where
    eval (T.Var (T.SyntaxKind _) x) = return $ unsafeCoerce x
    eval (T.Var (T.NativeKind _) x) = return $ unsafeCoerce x
    eval (T.Const _ c) = eval c
    eval (T.UniBool o e) = liftM (BoolVal . eval o . boolCoerce) $ eval e
    eval (T.CABool o es) = liftM (BoolVal . eval o) $ mapM (liftM boolCoerce . eval) es
    eval (T.UniBit m n o e) = liftM (BVVal . eval o . bvCoerce) $ eval e
    eval (T.CABit n o es) = liftM (BVVal . eval o n) $ mapM (liftM bvCoerce . eval) es
    eval (T.BinBit _ _ _ o e1 e2) = liftM BVVal $ (liftM2 $ eval o) (liftM bvCoerce $ eval e1) (liftM bvCoerce $ eval e2)  
    eval (T.BinBitBool _ _ _ e1 e2) = liftM BoolVal $ liftM2 (BV.<.) (liftM bvCoerce $ eval e1) (liftM bvCoerce $ eval e2) --only works a.t.m. because there is only one BinBitBoolOp
    eval (T.Kor k es) = do
        d <- defVal k
        vals <- mapM eval es
        foldM bitwise_or d vals
    eval (T.ITE _ e1 e2 e3) = do
        b <- eval e1
        if boolCoerce b then eval e2 else eval e3
    eval (T.Eq _ e1 e2) = do
        v1 <- eval e1
        v2 <- eval e2
        liftM BoolVal $ v1 .== v2
    eval (T.ReadStruct _ _ names e i) = do
        v <- eval e
        return $ case lookup (names i) (structCoerce v) of
                    Just v' -> v'
                    Nothing -> error ("Field " ++ names i ++ " not found.")
    eval (T.BuildStruct n _ names exprs) = 
        liftM StructVal $ pair_sequence $ map (\i -> (names i, eval $ exprs i)) (T.getFins n)
    eval (T.ReadArray n m k a v) = do
        x <- eval v
        let i = fromIntegral $ BV.nat $ bvCoerce x
        if i < n 
            then do
                y <- eval a
                let arr = arrayCoerce y
                M.readArray arr i
            else defVal k

    eval (T.ReadArrayConst n _ a i) = do
        let j = T.to_nat n i
        y <- eval a
        let arr = arrayCoerce y
        M.readArray arr j

    eval (T.BuildArray n _ exprs) = do
        vs <- sequence $ map (eval . exprs) $ T.getFins n
        liftM ArrayVal $ M.newListArray (0,(n-1)) vs







