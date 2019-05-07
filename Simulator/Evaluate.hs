{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Simulator.Evaluate where

import Simulator.Util
import Simulator.Value


import qualified Target as T

import qualified Data.Vector as V

import GHC.Base (unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#

list_of_word :: T.Coq_word -> [Bool]
list_of_word T.WO = []
list_of_word (T.WS b _ w) = b : (list_of_word w)

class Eval a b where
    eval :: a -> b

instance Eval T.ConstT Val where
    eval (T.ConstBool b) = BoolVal b
    eval (T.ConstBit _ w) = BitvectorVal $ list_of_word w
    eval (T.ConstStruct n _ names fields) = StructVal $ map 
        (\i -> (names i, eval $ fields i)) (T.getFins n)
    eval (T.ConstArray n _ vals) = ArrayVal $ V.map (eval . vals) (V.fromList $ T.getFins n)

instance Eval (T.UniBoolOp) (Bool -> Bool) where
    eval T.Neg = not

instance Eval (T.CABoolOp) ([Bool] -> Bool) where
    eval T.And = foldr (&&) True
    eval T.Or = foldr (||) False
    eval T.Xor = foldr (/=) False

instance Eval T.UniBitOp ([Bool] -> [Bool]) where
    eval (T.Inv _) = map not
    eval (T.TruncLsb _ m) = take m
    eval (T.TruncMsb _ m) = reverse . (take m) . reverse
    eval (T.UAnd _) = \xs -> [foldr (&&) True xs]
    eval (T.UOr _) = \xs -> [foldr (||) False xs]
    eval (T.UXor _) = \xs -> [foldr (/=) False xs]

instance Eval T.BinBitOp ([Bool] -> [Bool] -> [Bool]) where
    eval (T.Sub n) = \xs ys -> list_of_int n ((int_of_list xs) + (int_of_list $ map not ys) + 1)
    eval (T.Div n) = \xs ys -> list_of_int n ((int_of_list xs) `div` (int_of_list ys))
    eval (T.Rem n) = \xs ys -> list_of_int n (rem (int_of_list xs) (int_of_list ys))
    eval (T.Sll m n) = \xs ys -> list_lshift (int_of_list xs) False ys
    eval (T.Srl m n) = \xs ys -> list_rshift (int_of_list xs) False ys
    eval (T.Sra m n) = \xs ys -> list_rshift_a (int_of_list xs) ys
    eval (T.Concat _ _) = (++)

instance Eval T.CABitOp (Int -> [[Bool]] -> [Bool]) where
    eval T.Add = \n xss -> list_of_int n $ foldr (+) 0 (map int_of_list xss) 
    eval T.Mul = \n xss -> list_of_int n $ foldr (*) 1 (map int_of_list xss) 
    eval T.Band = \n -> foldr (zipWith (&&)) (replicate n True)
    eval T.Bor = \n -> foldr (zipWith (||)) (replicate n False)
    eval T.Bxor = \n -> foldr (zipWith (/=)) (replicate n False)

instance Eval (T.Expr ty) Val where
    eval (T.Var (T.SyntaxKind _) x) = unsafeCoerce x
    eval (T.Var T.NativeKind _) = error "Encountered a NativeKind."
    eval (T.Const _ c) = eval c
    eval (T.UniBool o e) = BoolVal $ eval o $ boolCoerce $ eval e
    eval (T.CABool o es) = BoolVal $ eval o $ map (boolCoerce . eval) es
    eval (T.UniBit m n o e) = BitvectorVal $ eval o $ bvCoerce $ eval e
    eval (T.CABit n o es) = BitvectorVal $ eval o n $ map (bvCoerce . eval) es
    eval (T.BinBit _ _ _ o e1 e2) = BitvectorVal $ eval o (bvCoerce $ eval e1) (bvCoerce $ eval e2)
    eval (T.BinBitBool _ _ _ e1 e2) = BoolVal $ (int_of_list $ bvCoerce $ eval e1) < (int_of_list $ bvCoerce $ eval e2) --only works a.t.m. because there is only one BinBitBoolOp
    eval (T.ITE _ e1 e2 e3) = if (boolCoerce $ eval e1) then eval e2 else eval e3
    eval (T.Eq _ e1 e2) = case eval e1 of
        BoolVal b -> BoolVal $ b == (boolCoerce $ eval e2)
        BitvectorVal v -> BoolVal $ v == (bvCoerce $ eval e2)
        StructVal s -> BoolVal $ s == (structCoerce $ eval e2)
        ArrayVal a -> BoolVal $ a == (arrayCoerce $ eval e2)
    eval (T.ReadStruct _ _ names e i) = case lookup (names i) (structCoerce $ eval e) of
        Just v -> v
        Nothing -> error ("Field " ++ names i ++ " not found.")
    eval (T.BuildStruct n _ names exprs) = StructVal $ map (\i -> (names i, eval $ exprs i)) (T.getFins n)
    eval (T.ReadArray _ _ a i) = (arrayCoerce $ eval a) V.! (int_of_list $ bvCoerce $ eval i) 
    eval (T.ReadArrayConst n _ a i) = (arrayCoerce $ eval a) V.! (T.to_nat n i)
    eval (T.BuildArray n _ exprs) = ArrayVal $ V.map (eval . exprs) (V.fromList $ T.getFins n)

defVal :: T.Kind -> Val
defVal k = eval (T.getDefaultConst k)

defVal_FK :: T.FullKind -> Val
defVal_FK T.NativeKind = error "Encountered a NativeKind."
defVal_FK (T.SyntaxKind k) = defVal k