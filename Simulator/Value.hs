
module Simulator.Value where

import Simulator.Util

import qualified HaskellTarget as T

import qualified Data.Vector as V
import qualified Data.BitVector as BV

import System.Random (randomRIO)

import Debug.Trace

data Val = BoolVal Bool | BitvectorVal BV.BV | StructVal [(String,Val)] | ArrayVal (V.Vector Val) deriving (Eq,Show)

-- unit val
tt :: Val
tt = BitvectorVal BV.nil

boolCoerce :: Val -> Bool
boolCoerce (BoolVal b) = b
boolCoerce v = error $ "Encountered a non-boolean value when a boolean was expected. " ++ show v

bvCoerce :: Val -> BV.BitVector
bvCoerce (BitvectorVal bs) = bs
bvCoerce v = error $ "Encountered a non-bitvector value when a bitvector was expected. " ++ show v

structCoerce :: Val -> [(String,Val)]
structCoerce (StructVal fields) = fields
structCoerce v = error $ "Encountered a non-struct value when a struct was expected. " ++ show v

arrayCoerce :: Val -> V.Vector Val
arrayCoerce (ArrayVal vs) = vs
arrayCoerce v = error $ "Encountered a non-array value when an array was expected. " ++ show v

struct_field_access :: String -> Val -> Val
struct_field_access fieldName v =
    case lookup fieldName $ structCoerce v of
        Just v' -> v'
        _ -> error $ "Field " ++ fieldName ++ " not found." ++ show v

randVal :: T.Kind -> IO Val
randVal T.Bool = do
    k <- randomRIO (0,1)
    return $ BoolVal $ k == (1 :: Int)
randVal (T.Bit n) = do
    k <- randomRIO ((0 :: Integer), 2^n - 1)
    return $ BitvectorVal $ BV.bitVec n k
randVal (T.Struct n ks names) = do
    let ks' = map ks (T.getFins n)
    let names' = map names (T.getFins n)
    vs <- mapM randVal ks'
    return $ StructVal $ zip names' vs
randVal (T.Array n k) = do
    vs <- V.mapM randVal (V.replicate n k)
    return $ ArrayVal vs

randVal_FK :: T.FullKind -> IO Val
randVal_FK (T.SyntaxKind k) = randVal k
randVal_FK (T.NativeKind) = error "Encountered a NativeKind."