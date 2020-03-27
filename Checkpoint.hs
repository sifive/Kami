
module Checkpoint where

import qualified Data.BitVector as BV
import qualified Data.Char as C
import Data.String.Builder as B
import System.IO

import Control.Monad
import Unsafe.Coerce

import qualified Data.Vector.Mutable as MV
import Control.Monad.Primitive
import Data.Vector as V (fromList)
import qualified Data.Vector.Generic as G
import qualified Data.Map.Strict as Map

import Syntax hiding (unsafeCoerce)
import Eval hiding (unsafeCoerce, Any)
import Simulator hiding (unsafeCoerce, Any)
import RegisterFile hiding (unsafeCoerce, Any)

--Printing

print_mvec :: FilePath -> (a -> String) -> MV.MVector (PrimState IO) a -> IO ()
print_mvec out f arr = do 
    a <- G.freeze arr
    withFile out AppendMode $ \h ->
        forM_ a $ \x -> hPutStrLn h (f x)

print_Val_hex :: Kind -> Coq_eval_Kind -> String
print_Val_hex k v = print_Val2 k (fullFormatBinary k) v

print_SimReg :: String -> (FullKind, Coq_fullType Coq_eval_Kind) -> String
print_SimReg r (SyntaxKind k, v) = r ++ ": " ++ print_Val_hex k v
print_SimReg r (NativeKind _, _) = r ++ ": Native Value"

print_SimRegs :: SimRegs -> FilePath -> IO ()
print_SimRegs regs out = do
    let pairs = Map.toList regs
    withFile out AppendMode $ \h ->
        forM_ pairs $ \(r,v) -> hPutStrLn h (print_SimReg r v)

print_RegFile :: String -> RegFile -> IO ()
print_RegFile out file = do
    print_mvec out (print_Val_hex $ RegisterFile.kind file) (arr file)
    appendFile out "\n"

--Parsing

data Token = Regs | IntRegs | RegFiles | BoolT | BoolF | Word BV.BV | LBracketStruct | RBracketStruct | LBracketVec | RBracketVec | Semicolon | Name String deriving (Eq,Show)

read_BV :: String -> Maybe BV.BV
read_BV str = liftM (BV.bitVec $ length str) $ go $ reverse str

    where

        go [] = Just (0 :: Integer)
        go ('0':str') = do
            x <- go str'
            return (2 * x)
        go ('1':str') = do
            x <- go str'
            return (2 * x + 1)
        go _ = Nothing

read_tok :: String -> Token
read_tok "REGS" = Regs
read_tok "INT_REGS" = IntRegs
read_tok "REGFILES" = RegFiles
read_tok "tt" = BoolT
read_tok "ff" = BoolF
read_tok "{" = LBracketStruct
read_tok "}" = RBracketStruct
read_tok "[" = LBracketVec
read_tok "]" = RBracketVec
read_tok ";" = Semicolon
read_tok str = case read_BV str of
    Just bv -> Word bv
    _ -> Name str

data PreValue = BoolV Bool | BVV BV.BV | VectorV [PreValue] | StructV [PreValue] deriving (Show)

rm_last :: [a] -> [a]
rm_last [] = []
rm_last [x] = []
rm_last (x:xs) = x:rm_last xs

preVal_to_Val :: PreValue -> Any
preVal_to_Val (BoolV b) = unsafeCoerce b
preVal_to_Val (BVV v) = unsafeCoerce v
preVal_to_Val (VectorV vs) = unsafeCoerce $ V.fromList $ map preVal_to_Val vs
preVal_to_Val (StructV vs) = go (map preVal_to_Val vs)

    where

        go [] = unsafeCoerce ()
        go (x:xs) = unsafeCoerce (x, go xs)

parse_preVal :: [Token] -> (PreValue, [Token])
parse_preVal (BoolT:rest) =  (BoolV True, rest)
parse_preVal (BoolF:rest) = (BoolV False, rest)
parse_preVal ((Word bv):rest) = (BVV bv, rest)
parse_preVal (LBracketVec:rest) =
    let (vs,rest') = parse_preVals_until rest RBracketVec in (VectorV vs,rest')
parse_preVal (LBracketStruct:rest) =
    let (vs,rest') = parse_preVals_until rest RBracketStruct in (StructV vs, rest')
parse_preVal _ = error "parse error"

parse_preVals_until :: [Token] -> Token -> ([PreValue], [Token])
parse_preVals_until toks term_tok = go [] toks term_tok

    where

        go acc toks'@(t:rest) term_tok'
            | t == term_tok' = (reverse acc, rest)
            | t == Semicolon = go acc rest term_tok'
            | otherwise = let (v, rest') = parse_preVal toks' in go (v:acc) rest' term_tok'

parse_line :: [Token] -> PreValue
parse_line toks = let (v, rest) = parse_preVal toks in v

parse_tokss :: String -> [[Token]]
parse_tokss txt =
    let ls = filter (not . null) $ lines txt in
    let wss = map words ls in
    map (map read_tok) wss

parse_regpair :: [Token] -> (String, PreValue)
parse_regpair ((Name name):rest) =
    let (v, _) = parse_preVal rest in (rm_last name, v)
parse_regpair _ = error "parse error"

split_tokss :: [[Token]] -> ([[Token]] , [[Token]] , [[Token]])
split_tokss tokss =
    let (_,(_:a)) = break (== [Regs]) tokss in
    let (b,(_:c)) = break (== [IntRegs]) a in
    let (d,(_:e)) = break (== [RegFiles]) c in
        (b,d,e)


split_rfs :: [[Token]] -> [(String, Int, [PreValue])]
split_rfs ([Name name]:tokss) = reverse $ go name 0 [] [] tokss where

    go currFile len acc1 acc2 [] = (currFile , len, reverse acc2) : acc1
    go currFile len acc1 acc2 ([Name name]:rest) = go name 0 ((currFile, len, reverse acc2):acc1) [] rest
    go currFile len acc1 acc2 (line:rest) =
        let v = parse_line line in go currFile (len + 1) acc1 (v:acc2) rest

split_rfs _ = error "parse error"

init_array :: (String, Int, [PreValue]) -> IO (String, MV.MVector (PrimState IO) Any)
init_array (str,len,prevals) = do
    a <- MV.unsafeNew len
    go a 0 prevals 
    return (str,a)

        where

            go _ _ [] = return ()
            go a i (p:ps) = do
                MV.unsafeWrite a i (preVal_to_Val p)
                go a (i+1) ps

get_regpairs :: [[Token]] -> [(String, (Kind, Any))]
get_regpairs = map (\toks -> 
    let (str,p) = parse_regpair toks in
    (str, (undefined, preVal_to_Val p))) --undefined because this shouldn't be accessed by the simulator; otherwise the Kind will need to be reconstructed.

get_rfs :: [[Token]] -> IO [(String, MV.MVector (PrimState IO) Any)]
get_rfs tokss = mapM init_array (split_rfs tokss)

restart_RegFile :: (String, MV.MVector (PrimState IO) Any) -> RegFile -> RegFile
restart_RegFile (name, array) (Build_RegFile a b c d e f g _) =
    Build_RegFile a b c d e f g array

restart_FileState :: [(String, MV.MVector (PrimState IO) Any)] -> [(String, (Kind, Any))] -> FileState -> FileState
restart_FileState new_arrs new_int_regs (Build_FileState methods int_regs files) =
    Build_FileState methods (Map.fromList new_int_regs) (Prelude.foldr (\(name,a) -> Map.adjust (restart_RegFile (name,a)) name) files new_arrs)

read_checkpoint :: FilePath -> [(String,String)] -> [RegFileBase] -> IO KamiState
read_checkpoint path args rfbs = do
    txt <- readFile path
    let tokss = parse_tokss txt
    let (regs, int_regs, rfs) = split_tokss tokss
    state <- initialize_files args rfbs 
    fs <- get_rfs rfs
    return (Map.fromList $ map (\(s,(k,a)) -> (s, (SyntaxKind k, a))) (get_regpairs regs), restart_FileState fs (get_regpairs int_regs) state)
