{-# LANGUAGE Strict #-}

module Simulator.Value where

import Simulator.Util
import Simulator.Classes


import qualified HaskellTarget as T

--import qualified Data.Vector as V
import Data.Array.IO as A
import Data.Array.MArray as M
import qualified Data.BitVector as BV
import  Control.Monad
import System.Random (randomRIO)

import Debug.Trace

data Val v =
      BoolVal Bool
    | BVVal BV.BV
    | StructVal [(String,Val v)]
    | ArrayVal (v (Val v))

(.==) :: Vec v => Val v -> Val v -> Bool
(.==) (BoolVal b1) (BoolVal b2) = b1 == b2
(.==) (BVVal bv1) (BVVal bv2) = bv1 == bv2
(.==) (StructVal ps1) (StructVal ps2) =
       (map fst ps1 == map fst ps2)
    && (foldr (&&) True $ zipWith (.==) (map snd ps1) (map snd ps2))
(.==) (ArrayVal arr1) (ArrayVal arr2) = vector_eq (.==) arr1 arr2
(.==) _ _ = False

bitwise_or :: Vec v => Val v -> Val v -> Val v
bitwise_or (BoolVal b1) (BoolVal b2) = BoolVal $ b1 || b2
bitwise_or (BVVal bv1) (BVVal bv2) = BVVal $ bv1 BV..|. bv2
bitwise_or (StructVal ps1) (StructVal ps2) =
    StructVal $ zipWith (\(name,v1) (_,v2) -> (name, bitwise_or v1 v2)) ps1 ps2
bitwise_or (ArrayVal a1) (ArrayVal a2) =
    ArrayVal $ vector_of_list $ zipWith bitwise_or (list_of_vector a1) (list_of_vector a2)
bitwise_or _ _ = error "Kind mismatch."

boolCoerce :: Val v -> Bool
boolCoerce (BoolVal b) = b
boolCoerce v = error $ "Encountered a non-boolean value when a boolean was expected. "

bvCoerce :: Val v -> BV.BV
bvCoerce (BVVal bs) = bs
bvCoerce v = error $ "Encountered a non-bitvector value when a bitvector was expected. "

structCoerce :: Val v -> [(String,Val v)]
structCoerce (StructVal fields) = fields
structCoerce v = error $ "Encountered a non-struct value when a struct was expected. "

arrayCoerce :: Val v -> v (Val v)
arrayCoerce (ArrayVal vs) = vs
arrayCoerce v = error $ "Encountered a non-array value when an array was expected. "

struct_field_access :: String -> Val v -> Val v
struct_field_access fieldName v =
    case lookup fieldName $ structCoerce v of
        Just v' -> v'
        _ -> error $ "Field " ++ fieldName ++ " not found."


defVal :: Vec v => T.Kind -> Val v
defVal T.Bool = BoolVal False
defVal (T.Bit n) = BVVal $ BV.zeros n
defVal (T.Struct n kinds names) =
    StructVal $ map (\i -> (names i, defVal $ kinds i)) $ T.getFins n
defVal (T.Array n k) =
    ArrayVal $ vector_of_list $ replicate n $ defVal k

defVal_FK :: Vec v => T.FullKind -> Val v
defVal_FK (T.NativeKind c) = T.unsafeCoerce c
defVal_FK (T.SyntaxKind k) = defVal k

randVal :: Vec v => T.Kind -> IO (Val v)
randVal T.Bool = do
    k <- randomRIO (0,1 :: Int)
    return $ BoolVal $ k == 1
randVal (T.Bit n) = do
    k <- randomRIO ((0 :: Integer), 2^n - 1)
    return $ BVVal $ BV.bitVec n k
randVal (T.Struct n ks names) = do
    let ks' = map ks (T.getFins n)
    let names' = map names (T.getFins n)
    vs <- mapM randVal ks'
    return $ StructVal $ zip names' vs
randVal (T.Array n k) = do
    ps <- mapM (\_ -> randVal k) [0..(n-1)]
    return $ ArrayVal $ vector_of_list ps

-- -- for debugging purposes

-- randVal :: T.Kind -> IO Val
-- randVal = pure . defVal

randVal_FK :: Vec v => T.FullKind -> IO (Val v)
randVal_FK (T.SyntaxKind k) = randVal k
randVal_FK (T.NativeKind c) = return $ T.unsafeCoerce c
