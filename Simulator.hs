{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}

{-
  Haskell simulator for Kami modules.  Should be executed alongside extracted Haskell version of the Kami library.
-}

module Simulator where

import qualified Target as T

import qualified Data.Vector as V
import System.IO (isEOF)
import Numeric (showHex)
import System.Exit (exitSuccess)
import Data.List (intersperse)
import Data.Foldable (foldrM)
import Data.Maybe (isJust)
import Control.Monad (mapM, when)ß
import System.Random (mkStdGen, setStdGen, randomRIO)
import GHC.Base (unsafeCoerce#)

unsafeCoerce = unsafeCoerce#

space_pad :: Int -> String -> String
space_pad n str = replicate (n - length str) ' ' ++ str

dropLast :: Int -> [a] -> [a]
dropLast n = reverse . (drop n) . reverse

list_lshift :: Int -> a -> [a] -> [a]
list_lshift n x xs = replicate (min n (length xs)) x ++ dropLast n xs

list_rshift :: Int -> a -> [a] -> [a]
list_rshift n x xs = drop n xs ++ replicate (min n (length xs)) x

list_rshift_a :: Int -> [a] -> [a]
list_rshift_a _ [] = []
list_rshift_a n xs = drop n xs ++ replicate (min n (length xs)) (last xs)

list_of_word :: T.Coq_word -> [Bool]
list_of_word T.WO = []
list_of_word (T.WS b _ w) = b : (list_of_word w)

int_of_list :: [Bool] -> Int
int_of_list [] = 0
int_of_list (b:xs) = (if b then 1 else 0) + 2 * int_of_list xs

list_of_int :: Int {- length -} -> Int {- value -} -> [Bool]
list_of_int 0 _ = []
list_of_int n x = (not $ even x) : list_of_int (n-1) (x `div` 2)

update :: Eq a => (a,b) -> [(a,b)] -> Either a [(a,b)]
update (a,_) [] = Left a
update (a,b) ((a',b'):ps) = if a == a' then Right $ (a,b):ps else do
    ps' <- update (a,b) ps
    return $ (a',b'):ps'

updates :: Eq a => [(a,b)]  {- original pair list -} -> [(a,b)] {- list of updates -} -> Either a [(a,b)]
updates = foldrM update 

execIOs :: [IO ()] -> IO ()
execIOs = foldr (>>) (return ())

data Val = BoolVal Bool | BitvectorVal [Bool] | StructVal [(String,Val)] | ArrayVal (V.Vector Val) deriving (Eq)

boolCoerce :: Val -> Bool
boolCoerce (BoolVal b) = b
boolCoerce _ = error "Encountered a non-boolean value when a boolean was expected."

bvCoerce :: Val -> [Bool]
bvCoerce (BitvectorVal bs) = bs
bvCoerce _ = error "Encountered a non-bitvector value when a bitvector was expected."

structCoerce :: Val -> [(String,Val)]
structCoerce (StructVal fields) = fields
structCoerce _ = error "Encountered a non-struct value when a struct was expected."

arrayCoerce :: Val -> V.Vector Val
arrayCoerce (ArrayVal vs) = vs
arrayCoerce _ = error "Encountered a non-array value when an array was expected."

defVal :: T.Kind -> Val
defVal k = eval (T.getDefaultConst k)

-- defVal :: T.Kind -> Val
-- defVal T.Bool = BoolVal False
-- defVal (T.Bit n) = BitvectorVal $ replicate n False
-- defVal (T.Struct n kinds names) = StructVal $ map (\i -> (names $ of_nat_lt n i, defVal $ kinds $ of_nat_lt n i)) [0..(n-1)]
-- defVal (T.Array n k) = ArrayVal $ (replicate n $ defVal k)

defVal_FK :: T.FullKind -> Val
defVal_FK T.NativeKind = error "Encountered a NativeKind."
defVal_FK (T.SyntaxKind k) = defVal k 

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

printVal :: T.FullFormat -> Val -> String
printVal (T.FBool n bf) (BoolVal b) = space_pad n (if b then "1" else "0")
printVal (T.FBit n _ bf) (BitvectorVal bs) = space_pad n $ printNum bf bs
printVal (T.FStruct n _ names ffs) (StructVal fields) = "{" ++ (concat $ intersperse ";" $ 
    zipWith (\(name,val) ff -> name ++ ":" ++ (printVal ff val)) fields (map ffs (T.getFins n))
    ) ++ "}"
printVal ff (ArrayVal vals) = "[" ++ (concat $ intersperse ";" (zipWith (\i v -> show i ++ ": " ++ printVal ff v) [0..((length vals)-1)] (V.toList vals))) ++ "]"
printVal _ _ = "Cannot print expression, mismatch between FullFormat and Kami Type." --make an error?

printNum :: T.BitFormat -> [Bool] -> String
printNum T.Binary bs = "0b" ++ map (\b -> if b then '1' else '0') (reverse bs)
printNum T.Decimal bs = show $ int_of_list bs
printNum T.Hex bs = "0x" ++showHex (int_of_list bs) ""

sysIO :: T.SysT Val -> IO ()
sysIO T.Finish = do
    putStrLn "Exiting..."
    exitSuccess
sysIO (T.DispString msg) = putStrLn msg
sysIO (T.DispExpr _ e ff) = putStrLn $ printVal ff $ eval e

check_assertions :: T.ActionT Val -> [(String, Val)] -> Bool
check_assertions act regs = isJust $ tryEval act where

    tryEval :: T.ActionT Val -> Maybe Val
    tryEval (T.MCall _ (_,k) _ cont) = tryEval (cont $ defVal k)
    tryEval (T.LetExpr _ e cont) = tryEval (cont $ unsafeCoerce $ (eval e :: Val))
    tryEval (T.LetAction _ a cont) = do
        v <- tryEval a
        tryEval (cont v)
    tryEval (T.ReadNondet k cont) = tryEval $ cont $ unsafeCoerce $ defVal_FK k
    tryEval (T.ReadReg regName _ cont) = case lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> tryEval $ cont $ unsafeCoerce v
    tryEval (T.WriteReg regName _ e a) = tryEval a
    tryEval (T.IfElse e _ a1 a2 cont) = let a = if (boolCoerce $ eval e) then a1 else a2 in
        do
            v <- tryEval a
            tryEval (cont v)
    tryEval (T.Assertion e a) = if (boolCoerce $ eval e) then tryEval a else Nothing
    tryEval (T.Sys _ a) = tryEval a
    tryEval (T.Return e) = Just $ eval e

simulate_action :: [(String, Val -> IO Val)] -> T.ActionT Val -> [(String, Val)] -> IO ([(String, Val)] , Val)
simulate_action meths act regs = sim act where

    sim (T.MCall methName _ arg cont) = case lookup methName meths of
        Nothing -> error ("Method " ++ methName ++ " not found.")
        Just f -> do
            v <- f $ eval arg
            sim $ cont v 

    sim (T.LetExpr _ e cont) = sim (cont $ unsafeCoerce $ (eval e :: Val))

    sim (T.LetAction _ a cont) = do
        (upd, v) <- sim a
        (upd',v') <- sim $ cont v
        return (upd ++ upd', v')

    --using a default val for now
    sim (T.ReadNondet k cont) = sim $ cont $ unsafeCoerce $ defVal_FK k

    sim (T.ReadReg regName _ cont) = case lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> sim $ cont $ unsafeCoerce v 

    sim (T.WriteReg regName _ e a) = case lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just _ -> do
            (upd,v) <- sim a
            return ((regName,eval e):upd,v)

    sim (T.IfElse e _ a1 a2 cont) = let a = if (boolCoerce $ eval e) then a1 else a2 in
        do
            (upd,v) <- sim a
            (upd',v') <- sim $ cont v
            return (upd ++ upd', v')

    sim (T.Assertion e a) = if (boolCoerce $ eval e) then sim a else error "Assertion depends upon method return values."

    sim (T.Sys syss a) = do
        execIOs $ map sysIO syss
        sim a

    sim (T.Return e) = return ([], eval e)

data IOStr a = (:+) (IO a) (IOStr a)

exitStr :: String -> IOStr a
exitStr msg = exit :+ (exitStr msg) where
    exit = do
        putStrLn msg
        exitSuccess

rand_rules :: [T.RuleT] -> IOStr T.RuleT
rand_rules [] = exitStr "Empty rule list."
rand_rules rs = rule :+ rand_rules rs where

    rule = do
        i <- randomRIO (0,length rs - 1)
        return $ rs !! i

round_robin_rules :: [T.RuleT] -> IOStr T.RuleT
round_robin_rules [] = exitStr "Empty rule list."
round_robin_rules (r:rs) = (return r) :+ (round_robin_rules (rs ++ [r]))

user_rules :: [T.RuleT] -> IOStr T.RuleT
user_rules [] = exitStr "Empty rule list."
user_rules rs = rule :+ user_rules rs where

    rule = do
        putStrLn "Next rule:\n"
        b <- isEOF
        if not b then do
            ruleName <- getLine
            case lookup ruleName rs of
                Nothing -> do
                    putStrLn ("Rule " ++ ruleName ++ " not found.")
                    rule
                Just a -> return (ruleName,a)
        else exitSuccess

get_rules :: [String] -> [T.RuleT] -> Either String [T.RuleT]
get_rules [] _ = Right []
get_rules (x:xs) rules = case lookup x rules of
    Nothing -> Left x
    Just a -> do
        rest <- get_rules xs rules
        return ((x,a):rest)

randVal :: T.Kind -> IO Val
randVal T.Bool = do
    k <- (randomRIO (0,1) :: IO Int)
    return $ BoolVal $ k == 1
randVal (T.Bit n) = do
    k <- randomRIO (0, 2^n - 1)
    return $ BitvectorVal $ list_of_int n k
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

initialize :: T.RegInitT -> IO (String,Val)
initialize (_, (_, Just (T.NativeConst _))) = error "Encountered a NativeConst."
initialize (regName, (_, Just (T.SyntaxConst _ c))) = return (regName, eval c)
initialize (regName, (k, Nothing)) = do
    v <- randVal_FK k
    return (regName,v)

simulate_module :: Int -> ([T.RuleT] -> IOStr T.RuleT) -> [String] -> [(String, Val -> IO Val)] -> T.BaseModule -> IO ([(String, Val)])
simulate_module _ _ _ _ (T.BaseRegFile _) = error "BaseRegFile encountered."
simulate_module seed strategy rulenames meths (T.BaseMod init_regs rules defmeths) = 

    -- passes the seed to the global rng
    (setStdGen $ mkStdGen seed) >>

    (when (not $ null defmeths) $ putStrLn "Warning: Encountered internal methods.") >>
 
    case get_rules rulenames rules of
        Left regName -> error ("Register " ++ regName ++ " not found.")
        Right rules' -> do
            regs <- mapM initialize init_regs
            sim (strategy rules') regs where
                sim (r :+ rs) regs = do
                    (ruleName,a) <- r
                    let b = check_assertions (unsafeCoerce $ a ()) regs
                    if b then do
                        (upd,_) <- simulate_action meths (unsafeCoerce $ a ()) regs
                        case updates regs upd of
                            Left regName -> error ("Register " ++ regName ++ " not found.")
                            Right regs' -> sim rs regs'

                        else do
                            putStrLn $ "Guard for " ++ ruleName ++ " failed."
                            sim rs regs

