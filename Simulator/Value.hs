{-# LANGUAGE Strict #-}

module Simulator.Value where

import Simulator.Util

import qualified HaskellTarget as T

--import qualified Data.Vector as V
import Data.Array.IO as A
import Data.Array.MArray as M
import qualified Data.BitVector as BV
import  Control.Monad
import System.Random (randomRIO)

import Debug.Trace

data Val = BoolVal Bool | BVVal BV.BV | StructVal [(String,Val)] | ArrayVal (A.IOArray Int Val) --deriving (Eq)

(.==) :: Val -> Val -> IO Bool
(.==) (BoolVal b1) (BoolVal b2) = return $ b1 == b2
(.==) (BVVal bv1) (BVVal bv2) = return $ bv1 == bv2
(.==) (StructVal ps1) (StructVal ps2) = do
    let names1 = map fst ps1
    let names2 = map fst ps2
    let b1 = names1 == names2
    let vals1 = map snd ps1
    let vals2 = map snd ps2
    bs <- sequence $ zipWith (.==) vals1 vals2
    return $ b1 && foldr (&&) True bs
(.==) (ArrayVal arr1) (ArrayVal arr2) = do
    es1 <- M.getElems arr1
    es2 <- M.getElems arr2
    bs <- sequence $ zipWith (.==) es1 es2
    return $ foldr (&&) True bs
(.==) _ _ = return False

bitwise_or :: Val -> Val -> IO Val
bitwise_or (BoolVal b1) (BoolVal b2) = return $ BoolVal $ b1 || b2
bitwise_or (BVVal bv1) (BVVal bv2) = return $ BVVal $ bv1 BV..|. bv2
bitwise_or (StructVal ps1) (StructVal ps2) = do
    ps3 <- zipWithM (\(name,v1) (_,v2) -> do
        v3 <- bitwise_or v1 v2
        return (name, v3)
        ) ps1 ps2
    return $ StructVal ps3
bitwise_or (ArrayVal a1) (ArrayVal a2) = do
    elts1 <- M.getElems a1
    elts2 <- M.getElems a2
    elts3 <- zipWithM bitwise_or elts1 elts2
    let n = length elts1
    arr <- M.newListArray (0,n-1) elts3
    return $ ArrayVal arr
bitwise_or _ _ = error "Kind mismatch."


boolCoerce :: Val -> Bool
boolCoerce (BoolVal b) = b
boolCoerce v = error $ "Encountered a non-boolean value when a boolean was expected. "

bvCoerce :: Val -> BV.BV
bvCoerce (BVVal bs) = bs
bvCoerce v = error $ "Encountered a non-bitvector value when a bitvector was expected. "

structCoerce :: Val -> [(String,Val)]
structCoerce (StructVal fields) = fields
structCoerce v = error $ "Encountered a non-struct value when a struct was expected. "

arrayCoerce :: Val -> A.IOArray Int Val
arrayCoerce (ArrayVal vs) = vs
arrayCoerce v = error $ "Encountered a non-array value when an array was expected. "

struct_field_access :: String -> Val -> Val
struct_field_access fieldName v =
    case lookup fieldName $ structCoerce v of
        Just v' -> v'
        _ -> error $ "Field " ++ fieldName ++ " not found."

defVal :: T.Kind -> IO Val
defVal T.Bool = return $ BoolVal False
defVal (T.Bit n) = return $ BVVal $ BV.zeros n
defVal (T.Struct n kinds names) =
    liftM StructVal $ pair_sequence $ map (\i -> (names i, defVal $ kinds i)) $ T.getFins n
defVal (T.Array n k) = do
    v <- defVal k
    liftM ArrayVal $ M.newArray (0,n-1)  v

defVal_FK :: T.FullKind -> IO Val
defVal_FK (T.NativeKind c) = return $ T.unsafeCoerce c
defVal_FK (T.SyntaxKind k) = defVal k

randVal :: T.Kind -> IO Val
randVal T.Bool = do
    k <- randomRIO (0,1)
    return $ BoolVal $ k == (1 :: Int)
randVal (T.Bit n) = do
    k <- randomRIO ((0 :: Integer), 2^n - 1)
    return $ BVVal $ BV.bitVec n k
randVal (T.Struct n ks names) = do
    let ks' = map ks (T.getFins n)
    let names' = map names (T.getFins n)
    vs <- mapM randVal ks'
    return $ StructVal $ zip names' vs
randVal (T.Array n k) = do
    ps <- mapM (\i -> (randVal k) >>= (\v -> return (i,v))) [0..(n-1)]
    v <- defVal k
    arr <- M.newArray (0,(n-1)) v
    do_writes arr ps
    return $ ArrayVal arr

-- -- for debugging purposes

-- randVal :: T.Kind -> IO Val
-- randVal = pure . defVal

randVal_FK :: T.FullKind -> IO Val
randVal_FK (T.SyntaxKind k) = randVal k
randVal_FK (T.NativeKind c) = return $ T.unsafeCoerce c
