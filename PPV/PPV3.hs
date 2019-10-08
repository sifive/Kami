{-# OPTIONS_GHC -XStandaloneDeriving #-}

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric

log2_up :: Int -> Int
log2_up = ceiling . (logBase 2) . fromIntegral

intToFin :: Int -> Int -> (Int,Int)
intToFin = (,)

ppDealSize0 :: T.Kind -> String -> String -> String
ppDealSize0 ty def str = if T.size ty == 0 then def else str

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (n-1) ++ ":0]"

finToInt :: (Int,Int) -> Int
finToInt = snd

deformat :: String -> String
deformat = concatMap (\c -> if c == '\n' then "\\n" else c:[])

ppTypeVec :: T.Kind -> Int -> (T.Kind, [Int])
ppTypeVec k@(T.Array i' k') i =
  let (k'', is) = ppTypeVec k' i'
  in (k', i : is)
ppTypeVec k i = (k, i : [])

ppTypeName :: T.Kind -> String
ppTypeName k =
  case ppTypeVec k 0 of
    (T.Struct _ _ _, _) -> "struct packed"
    (_, _) -> "logic"

ppDeclType :: String -> T.Kind -> String
ppDeclType s k = ppTypeName k ++ ppType k ++ " " ++ s

ppName :: String -> String
ppName s = map (\x -> if isAlphaNum x || x == '_' then x else '$') s


ppType :: T.Kind -> String
ppType T.Bool = ""
ppType (T.Bit i) = "[" ++ show (i-1) ++ ":0]"
ppType v@(T.Array i k) =
  let (k', is) = ppTypeVec k i
  in case k' of
       T.Struct _ _ _ -> ppType k' ++ concatMap ppVecLen is
       _ -> concatMap ppVecLen is ++ ppType k'
ppType (T.Struct n fk fs) =
  "{" ++ concatMap (\i -> ppDealSize0 (fk i) "" (' ' : ppDeclType (ppName $ fs i) (fk i) ++ ";")) (T.getFins n) ++ "}"

ppPrintVar :: (String, Int) -> String
ppPrintVar (s, v) = ppName $ s ++ if v /= 0 then '#' : show v else []

{- make sure this is good -}
ppPrintVar' :: (String, Maybe Int) -> String
ppPrintVar' (s, Just v) = ppPrintVar (s,v)
ppPrintVar' (s, Nothing) = s

padwith :: a -> Int -> [a] -> [a]
padwith x n xs = let m = n - length xs in
  if m > 0 then replicate m x ++ xs else drop (-m) xs

ppWord :: (Int,Integer) -> String
ppWord (n,i) = padwith '0' n $ showIntAtBase 2 intToDigit i ""

ppConst :: T.ConstT -> String
ppConst (T.ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (T.ConstBit sz w) = show sz ++ "\'b" ++ ppWord w
ppConst (T.ConstArray n k fv) = '{' : intercalate ", " (Data.List.map ppConst (Data.List.map fv (reverse $ T.getFins n))) ++ "}"
ppConst (T.ConstStruct n fk fs fv) = '{' : intercalate ", " (snd (unzip (Data.List.filter (\(k,e) -> T.size k /= 0) (zip (Data.List.map fk (T.getFins n)) (Data.List.map ppConst (Data.List.map fv (T.getFins n))))))) ++ "}"

optionAddToTrunc :: String -> T.Kind -> T.RtlExpr' -> State (H.Map String (Int, T.Kind)) String
optionAddToTrunc who k e =
  case e of
    T.Var (T.SyntaxKind k') x -> let (s,o) = T.unsafeCoerce x in
      case o of
        Nothing -> case k' of
          T.Bit 0 -> return "0"
          _ -> return $ ppName s

        Just n -> case k' of
          T.Bit 0 -> return $ "0"
          _ -> return $ ppPrintVar (s,n)

    _ -> do
      x <- ppRtlExpr who e
      new <- addToTrunc who k x
      return new

createTrunc :: String -> T.Kind -> T.RtlExpr' -> Int -> Int -> State (H.Map String (Int, T.Kind)) String
createTrunc who k e msb lsb =
  if msb < lsb
  then return "0"
  else do
    new <- optionAddToTrunc who k e
    return $ new ++ '[' : show msb ++ ':' : show lsb ++ "]"

addToTrunc :: String -> T.Kind -> String -> State (H.Map String (Int, T.Kind)) String
addToTrunc who kind s =
  do
    x <- get
    case H.lookup s x of
      Just (pos, _) -> return $ "_trunc$" ++ who ++ "$" ++ show pos
      Nothing ->
        do
          put (H.insert s (H.size x, kind) x)
          return $ "_trunc$" ++ who ++ "$" ++ show (H.size x)

ppRtlExpr :: String -> T.RtlExpr' -> State (H.Map String (Int, T.Kind)) String
ppRtlExpr who e = 
  case e of
    --T.RtlReadReg k s -> return $ ppDealSize0 k "0" (ppName s)
    --T.RtlReadWire k var -> return $ ppDealSize0 k "0" (ppPrintVar var)
    T.Var (T.SyntaxKind k) x -> optionAddToTrunc who k e
    T.Var (T.NativeKind _) _ -> error "NativeKind encountered."
    T.Const k c -> return $ ppDealSize0 k "0" (ppConst c)
    T.UniBool T.Neg e -> uniExpr "~" e
    T.CABool T.And es -> listExpr "&" es "1'b1"
    T.CABool T.Or es -> listExpr "|" es "1'b0"
    T.CABool T.Xor es -> listExpr "^" es "1'b0"
    T.UniBit _ _ (T.Inv _) e -> uniExpr "~" e
    T.UniBit _ _ (T.UAnd _) e -> uniExpr "&" e
    T.UniBit _ _ (T.UOr _) e -> uniExpr "|" e
    T.UniBit _ _ (T.UXor _) e -> uniExpr "^" e
    T.UniBit sz retSz (T.TruncLsb lsb msb) e -> createTrunc who (T.Bit sz) e (retSz - 1) 0
    T.UniBit sz retSz (T.TruncMsb lsb msb) e -> createTrunc who (T.Bit sz) e (sz - 1) lsb
    T.CABit n T.Add es -> listExpr "+" es (show n ++ "'b0")
    T.CABit n T.Mul es -> listExpr "*" es (show n ++ "'b1")
    T.CABit n T.Band es -> listExpr "&" es (show n ++ "'b" ++ Data.List.replicate n '1')
    T.CABit n T.Bor es -> listExpr "|" es (show n ++ "'b0")
    T.CABit n T.Bxor es -> listExpr "^" es (show n ++ "'b0")
    T.BinBit _ _ _ (T.Sub _) e1 e2 -> binExpr e1 "-" e2
    T.BinBit _ _ _ (T.Div _) e1 e2 -> binExpr e1 "/" e2
    T.BinBit _ _ _ (T.Rem _) e1 e2 -> binExpr e1 "%" e2
    T.BinBit _ _ _ (T.Sll _ _) e1 e2 -> binExpr e1 "<<" e2
    T.BinBit _ _ _ (T.Srl _ _) e1 e2 -> binExpr e1 ">>" e2
    T.BinBit _ _ _ (T.Sra n m) e1 e2 ->
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        new <- addToTrunc who (T.Bit n) ("($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")")
        return $ new
        -- return $ "($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")"
    T.BinBit _ _ _ (T.Concat m n) e1 e2 ->
      case (m, n) of
        (0, 0)   -> return $ "0"
        (m', 0)  -> do
          x1 <- ppRtlExpr who e1
          return x1
        (0, n')  -> do
          x2 <- ppRtlExpr who e2
          return x2
        (m', n') -> do
          x1 <- ppRtlExpr who e1
          x2 <- ppRtlExpr who e2
          return $ '{' : x1 ++ ", " ++ x2 ++ "}"
    T.BinBitBool _ _ (_) e1 e2 -> binExpr e1 "<" e2
    T.ITE _ p e1 e2 -> triExpr p "?" e1 ":" e2
    T.Eq _ e1 e2 -> binExpr e1 "==" e2
    T.ReadStruct num fk fs e i ->
      do
        new <- optionAddToTrunc who (T.Struct num fk fs) e
        return $ ppDealSize0 (fk i) "0" (new ++ '.' : ppName (fs i))
    T.BuildStruct num fk fs es ->
      do
        strs <- mapM (ppRtlExpr who) (filterKind0 num fk es)  -- (Data.List.map es (getFins num))
        return $ ppDealSize0 (T.Struct num fk fs) "0" ('{': intercalate ", " strs ++ "}")
    T.ReadArray n m k vec idx ->
      do
        xidx <- ppRtlExpr who idx
        xvec <- ppRtlExpr who vec
        new <- optionAddToTrunc who (T.Array n k) vec
        return $ ppDealSize0 k "0" (new ++ '[' : xidx ++ "]")
    T.ReadArrayConst n k vec idx ->
      do
        let xidx = finToInt idx
        xvec <- ppRtlExpr who vec
        new <- optionAddToTrunc who (T.Array n k) vec
        return $ ppDealSize0 k "0" (new ++ '[' : show xidx ++ "]")
    T.BuildArray n k fv ->
      do
        strs <- mapM (ppRtlExpr who) (Data.List.map fv (reverse $ T.getFins n))
        return $ ppDealSize0 (T.Array n k) "0" ('{': intercalate ", " strs ++ "}")
  where
    filterKind0 num fk es = snd (unzip (Data.List.filter (\(k,e) -> T.size k /= 0) (zip (Data.List.map fk (T.getFins num)) (Data.List.map es (T.getFins num)))))
    uniExpr op e =
      do
        x <- ppRtlExpr who e
        return $ '(' : " " ++ op ++ " " ++ x ++ ")"
    listExpr' op es init =
      case es of
        e : es' -> do
                     x <- ppRtlExpr who e
                     xs <- listExpr' op es' init
                     return $ x ++ " " ++ op ++ " " ++ xs
        [] -> return init
    listExpr op es init =
      do
        xs <- listExpr' op es init
        return $ '(' : xs ++ ")"
    binExpr e1 op e2 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ '(' : x1 ++ " " ++ op ++ " " ++ x2 ++ ")"
    triExpr e1 op1 e2 op2 e3 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        x3 <- ppRtlExpr who e3
        return $ '(' : x1 ++ " " ++ op1 ++ " " ++ x2 ++ " " ++ op2 ++ " " ++ x3 ++ ")"

en_var :: String -> Int -> String
en_var f i = f ++ "__" ++ show i ++ "_enable"

arg_var :: String -> Int -> String
arg_var f i = f ++ "__" ++ show i ++ "_argument"

tmp_var :: Int -> String
tmp_var i = "tmp__" ++ show i

ret_var :: String -> String
ret_var f = f ++ "__return"

monad_concat :: Monad m => [m [a]] -> m [a]
monad_concat ms = fmap concat $ sequence ms

type ExprString = String
type Name = String

data RegMapTy = RegMapTy {
    reg_counters :: H.Map Name Int
  --, async_counters ::  H.Map (Name,Name) Int
  , async_read_counters :: H.Map Name Int
  , write_counters :: H.Map Name Int
  , isAddr_counters :: H.Map Name Int
  , not_isAddr_counters :: H.Map Name Int
  , isAddr_reg_counters :: H.Map Name Int
  , not_isAddr_reg_counters :: H.Map Name Int
}

data ExprState = ExprState {
    expr_map :: H.Map ExprString (Int, T.Kind)
  , regmap_counters :: RegMapTy
  , meth_counters :: H.Map Name Int
  , let_counter :: Int
  , all_regs :: [(Name,T.FullKind)]
  , all_asyncs :: [(Name,Name)]
  , all_isAddrs :: [(Name,Name)]
  , all_not_isAddrs :: [(Name,Name)]
}

data ReadPort = ReadPort {
    rd_pred :: T.RtlExpr'
  , rd_addr :: T.RtlExpr'
}

data WritePort = WritePort {
    wr_pred :: T.RtlExpr'
  , wr_addr :: T.RtlExpr'
  , wr_mask :: Maybe T.RtlExpr'
  , wr_data :: T.RtlExpr'
}

has_mask :: Name -> Bool
has_mask dataArray = undefined

var :: T.FullKind -> Name -> Int -> T.RtlExpr'
var k n i = T.Var k $ T.unsafeCoerce (n, Just i)

var' :: T.FullKind -> Name -> T.RtlExpr'
var' k n = T.Var k $ T.unsafeCoerce (n, Nothing)

writeMap_query_read :: T.FullKind -> Name -> RME -> ReadPort
writeMap_query_read k readPort m = case m of
  T.VarRME rmt -> let i = (async_read_counters rmt) H.! readPort in
    ReadPort {
        rd_pred = var k (readPort ++ "__pred__") i
      , rd_addr = var k (readPort ++ "__addr__") i
    }
  T.UpdReg _ _ _ _ m' -> writeMap_query_read k readPort m'
  T.UpdRegFile _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_read k readPort wm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_read k readPort wm
  T.AsyncRead idxNum num readPort' dataArray idx _ m' ->
    if readPort == readPort' then ReadPort {
          rd_pred = undefined
        , rd_addr = idx
      } else writeMap_query_read k readPort m'
  T.CompactRME m' -> writeMap_query_read k readPort m'

writeMap_query_write :: T.FullKind -> Name -> RME -> WriteMap
writeMap_query_write k dataArray m = case m of
  T.VarRME rmt -> let i = (write_counters rmt) H.! dataArray in
    WritePort {
        rd_pred = var k (dataArray ++ "__pred__") i
      , rd_addr = var k (dataArray ++ "__addr__") i
      , rd_mask = if has_mask dataArray then Just $ var k (dataArray ++ "__mask__") i else None
      , rd_data = var k (dataArray ++ "__data__") i
    }
  T.UpdReg _ _ _ _ m' -> writeMap_query_read k dataArray m'
  T.UpdRegFile idxNum num dataArray' idx k val mask pred wm rm _ ->
    if dataArray == dataArray' then WritePort {
        wr_pred = pred
      , wr_addr = idx
      , wr_mask = mask
      , wr_data = val
    } else writeMap_query_write k dataArray wm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_write k dataArray wm
  T.AsyncRead _ _ _ _ _ _ m' -> writeMap_query_write k dataArray m'
  T.CompactRME m' -> writeMap_query_write k dataArray m'

readMap_query_read :: T.FullKind -> Name -> RME -> ReadPort
readMap_query_read k readPort m = case m of
  T.VarRME rmt -> let i = (async_read_counters rmt) H.! readPort in
    ReadPort {
        rd_pred = var k (readPort ++ "__pred__") i
      , rd_addr = var k (readPort ++ "__addr__") i
    }
  T.UpdReg _ _ _ _ m' -> readMap_query_read k readPort m'
  T.UpdRegFile _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_read k readPort rm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_read k readPort rm
  T.AsyncRead idxNum num readPort' dataArray idx _ m' ->
    if readPort == readPort' then ReadPort {
          rd_pred = undefined
        , rd_addr = idx
      } else readMap_query_read k readPort m'
  T.CompactRME m' -> readMap_query_read k readPort m'

readMap_query_write :: T.FullKind -> Name -> RME -> WriteMap
readMap_query_write k dataArray m = case m of
  T.VarRME rmt -> let i = (write_counters rmt) H.! dataArray in
    WritePort {
        rd_pred = var k (dataArray ++ "__pred__") i
      , rd_addr = var k (dataArray ++ "__addr__") i
      , rd_mask = if has_mask dataArray then Just $ var k (dataArray ++ "__mask__") i else None
      , rd_data = var k (dataArray ++ "__data__") i
    }
  T.UpdReg _ _ _ _ m' -> readMap_query_read k dataArray m'
  T.UpdRegFile idxNum num dataArray' idx k val mask pred wm rm _ ->
    if dataArray == dataArray' then WritePort {
        wr_pred = pred
      , wr_addr = idx
      , wr_mask = mask
      , wr_data = val
    } else readMap_query_write k dataArray rm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_write k dataArray rm
  T.AsyncRead _ _ _ _ _ _ m' -> readMap_query_write k dataArray m'
  T.CompactRME m' -> readMap_query_write k dataArray m'

get_range_ptwise :: (T.RtlExpr' -> T.RtlExpr') -> T.RtlExpr' -> Int -> T.RtlExpr'
get_range_ptwise f idx num = undefined
  {- { f idx, f (idx+1), ..., f (idx+num-1) } -}

readmap_query_resp :: T.FullKind -> Int -> Name -> Name -> RME -> T.RtlExpr'
readmap_query_resp k num dataArray readPort m =
  let rd_idx = rd_addr $ readMap_query_read k readPort m in
  let wr_idx = wr_addr $ readMap_query_write k dataArray m in undefined


type RME = T.RME_simple T.Coq_rtl_ty RegMapTy

data VerilogExprs = VerilogExprs {
    assign_exprs :: [(Name, T.RtlExpr')]
  , if_begin_end_exprs :: [(T.RtlExpr', [T.SysT T.Coq_rtl_ty])]
  , return_expr :: T.RtlExpr'
  , return_maps :: RME
}

{- monadic accessors which both return the current count and increment it -}

get_regs :: State ExprState [(Name, T.FullKind)]
get_regs = do
  s <- get
  return $ all_regs s

get_asyncs :: State ExprState [(Name,Name)]
get_asyncs = do
  s <- get
  return $ all_asyncs s

get_isAddrs :: State ExprState [(Name,Name)]
get_isAddrs = do
  s <- get
  return $ all_isAddrs s

get_not_isAddrs :: State ExprState [(Name,Name)]
get_not_isAddrs = do
  s <- get
  return $ all_not_isAddrs s

let_count :: State ExprState Int
let_count = do
  s <- get
  let n = let_counter s
  put $ s { let_counter = n+1 }
  return n

meth_count :: Name -> State ExprState Int
meth_count f = do
  s <- get
  let n = meth_counters s H.! f
  put $ s { meth_counters = H.insert f (n+1) $ meth_counters s }
  return n

reg_count :: Name -> State ExprState Int
reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { reg_counters = H.insert r (n+1) rc } }
  return n

async_count :: (Name,Name) -> State ExprState Int
async_count p = do
  s <- get
  let rmc = regmap_counters s
  let arc = async_counters rmc
  let n = arc H.! p
  put $ s { regmap_counters = rmc { async_counters = H.insert p (n+1) arc } }
  return n

isAddr_count :: Name -> State ExprState Int
isAddr_count r = do
  s <- get
  let rmc = regmap_counters s
  let sic = isAddr_counters rmc
  let n = sic H.! r
  put $ s { regmap_counters = rmc { isAddr_counters = H.insert r (n+1) sic } }
  return n

not_isAddr_count :: Name -> State ExprState Int
not_isAddr_count r = do
  s <- get
  let rmc = regmap_counters s
  let snc = not_isAddr_counters rmc
  let n = snc H.! r
  put $ s { regmap_counters = rmc { not_isAddr_counters = H.insert r (n+1) snc} }
  return n

data MapType = ReadMap | WriteMap deriving (Eq)

{- normal registers -}

query_reg :: MapType -> T.FullKind -> Name -> RME -> T.RtlExpr'
query_reg x k reg (T.VarRME rmt) = T.Var k $ T.unsafeCoerce (reg, Just $ (reg_counters rmt) H.! reg)
query_reg x k reg (T.UpdReg r pred _ val m) = if reg == r then T.ITE k pred val (query_reg x k reg m) else query_reg x k reg m
query_reg ReadMap k reg (T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg ReadMap k reg readMap
query_reg WriteMap k reg (T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg WriteMap k reg writeMap
query_reg ReadMap k reg (T.UpdReadReq _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg ReadMap k reg readMap
query_reg WriteMap k reg (T.UpdReadReq _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg WriteMap k reg writeMap
query_reg x k reg (T.CompactRME m) = query_reg x k reg m

do_reg_upd :: RME -> T.FullKind -> Name -> State ExprState [(Name, T.RtlExpr')]
do_reg_upd m k r = case query_reg WriteMap k r m of
  T.Var _ _ -> return []
  e -> do
    i <- reg_count r
    return [(r ++ "__" ++ show i,e)]

get_reg_upds :: RME -> State ExprState [(Name, T.RtlExpr')]
get_reg_upds m = do
  rs <- get_regs
  monad_concat $ map (\(r,k) -> do_reg_upd m k r) rs

{- async regfiles -}

{-
write_query :: Name -> Name -> T.FullKind -> RME -> T.RtlExpr'
write_query dataArray readPort k m = case m of 
  T.VarRME rmt -> var k (dataArray ++ "__" ++ readPort) ((async_counters rmt) H.! (dataArray, readPort))
  T.UpdReg _ _ _ _ m' -> write_query dataArray readPort k m'
  T.UpdRegFile idxNum num dataArray idx k val mask pred writeMap readMap arr ->
-}

{-
query_async_rf_i :: MapType -> Name -> Int -> T.Expr Int -> Int -> T.RME_simple Int RegMapTy -> VExpr
query_async_rf_i x dataArray num idx i m = case m of
  T.VarRME rmt -> let n = async_counters rmt H.! dataArray in


      if n == 0 then {- ?? -} undefined else error "Trying to read from regfile that was written to."


  T.UpdReg _ _ _ _ m -> query_async_rf_i x dataArray idx i m 
  T.UpdRegFile idxNum num dataArray' idx' _ val Nothing pred writeMap readMap _ -> 
    let m' = if x == ReadMap then readMap else writeMap in
    if dataArray == dataArray' then
    VITE (VAnd (Between (KExpr idx') (VPlus (KExpr idx') (VInt i)) (VPlus (KExpr idx') (VInt (num-1)))) (KExpr pred)) (Access (KExpr val) (VInt i)) (query_async_rf_i x dataArray idx i m')
    else query_async_rf_i x dataArray idx i m'
  T.UpdRegFile idxNum num dataArray' idx' _ val (Just mask) pred writeMap readMap _ ->
    let m' = if x == ReadMap then readMap else writeMap in
   if dataArray == dataArray' then
    VITE (VAnd (Between (KExpr idx') (VPlus (KExpr idx') (VInt i)) (VPlus (KExpr idx') (VInt (num-1)))) (VAnd (Access (KExpr mask) (VInt i)) (KExpr pred))) (Access (KExpr val) (VInt i)) (query_async_rf_i x dataArray idx i m')
    else query_async_rf_i x dataArray idx i m'
  T.UpdReadReq _ _ _ _ _ _ _ _ writeMap readMap _ -> 
    let m' = if x == ReadMap then readMap else writeMap in
    query_async_rf_i x dataArray idx i m'
  T.CompactRME m' -> query_async_rf_i x dataArray idx i m'

query_async_rf :: MapType -> Name -> T.Expr Int -> Int -> T.RME_simple Int RegMapTy -> VExpr
query_async_rf x dataArray idx num m = ConcatVals $ do
  i <- [0..(num-1)]
  return $ query_async_rf_i x dataArray idx i m

do_async_rf_upd :: T.Expr Int -> Int -> T.RME_simple Int RegMapTy -> Name -> State ExprState [(Name,VExpr)]
do_async_rf_upd idx num m dataArray = case query_async_rf WriteMap dataArray idx num m of
  VVar _ -> return []
  e -> do
    i <- async_count dataArray
    return [(dataArray ++ "__" ++ show i,e)]

get_async_rf_upds :: Name -> T.Expr Int -> Int -> T.RME_simple Int RegMapTy -> State ExprState [(Name, VExpr)]
get_async_rf_upds dataArray idx num m = do
  rfs <- get_asyncs
  monad_concat $ map (do_async_rf_upd idx num m) (map fst rfs)

{- sync regfile regs; isAddr = true -}

query_isAddr_reg :: MapType -> Name -> Name -> T.RME_simple Int RegMapTy -> VExpr
query_isAddr_reg x dataArray regName m = case m of
  T.VarRME rmt -> VVar $ regName ++ "__" ++ (show $ (isAddr_reg_counters rmt) H.! regName)
  T.UpdReg _ _ _ _ m' -> query_isAddr_reg x dataArray regName m'
  T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _ ->
    let m' = if x == ReadMap then readMap else writeMap in query_isAddr_reg x dataArray regName m'
  T.UpdReadReq idxNum num regName' dataArray' idx _ isAddr pred writeMap readMap _ ->
    let m' = if x == ReadMap then readMap else writeMap in
    if regName == regName' && dataArray == dataArray' && isAddr then
      if x == ReadMap then error "Cannot read after an update."
      else VITE (KExpr pred) (KExpr idx) (query_isAddr_reg x dataArray regName m')
    else 
      query_isAddr_reg x dataArray regName m'
  T.CompactRME m' -> query_isAddr_reg x dataArray regName m'

do_isAddr_reg_upd :: T.RME_simple Int RegMapTy -> Name -> Name -> State ExprState [(Name,VExpr)]
do_isAddr_reg_upd m dataArray regName = case query_isAddr_reg WriteMap dataArray regName m of
  VVar _ -> return []
  e -> do
    isAddr_count regName
    return [(regName,e)]

get_isAddr_reg_upds :: T.RME_simple Int RegMapTy -> State ExprState [(Name, VExpr)]
get_isAddr_reg_upds m = do
  rfs <- get_isAddrs
  monad_concat $ map (\(dataArray,regName) -> do_isAddr_reg_upd m dataArray regName) rfs

{- sync regfile regs; isAddr = false -}

query_not_isAddr_reg :: MapType -> Name -> Name -> T.RME_simple Int RegMapTy -> VExpr
query_not_isAddr_reg x dataArray regName m = case m of
  T.VarRME rmt -> VVar $ regName ++ "__" ++ (show $ (not_isAddr_reg_counters rmt) H.! regName)
  T.UpdReg _ _ _ _ m' -> query_not_isAddr_reg x dataArray regName m'
  T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _ -> 
    let m' = if x == ReadMap then readMap else writeMap in query_not_isAddr_reg x dataArray regName m'
  T.UpdReadReq idxNum num regName' dataArray' idx _ isAddr pred writeMap readMap _ ->
    let m' = if x == ReadMap then readMap else writeMap in
    if regName == regName' && dataArray == dataArray' && not isAddr then
      if x == ReadMap then error "Cannot read after an update." else VITE (KExpr pred) (KExpr idx) (query_not_isAddr_reg x dataArray regName m')
      else
        query_not_isAddr_reg x dataArray regName m'
  T.CompactRME m' -> query_not_isAddr_reg x dataArray regName m'

do_not_isAddr_reg_upd :: T.RME_simple Int RegMapTy -> Name -> Name -> State ExprState [(Name,VExpr)]
do_not_isAddr_reg_upd m dataArray regName = case query_not_isAddr_reg WriteMap dataArray regName m of
  VVar _ -> return []
  e -> do
    not_isAddr_count regName
    return [(regName,e)]

get_not_isAddr_reg_upds :: T.RME_simple Int RegMapTy -> State ExprState [(Name, VExpr)]
get_not_isAddr_reg_upds m = do
  rfs <- get_asyncs
  monad_concat $ map (\(dataArray,regName) -> do_not_isAddr_reg_upd m dataArray regName) rfs

get_all_upds :: T.RME_simple Int RegMapTy -> State ExprState [(Name, VExpr)]
get_all_upds m = do
  reg_upds <- get_reg_upds m
  isAddr_upds <- get_isAddr_reg_upds m
  not_isAddr_upds <- get_not_isAddr_reg_upds m
  return $ reg_upds ++ isAddr_upds ++ not_isAddr_upds
-}

type CA_rtl = T.CA_simple T.Coq_rtl_ty RegMapTy

tmp :: Int -> (Name, Maybe Int)
tmp j = ("tmp", Just j)

ppCAS :: CA_rtl -> State ExprState VerilogExprs
ppCAS (T.CompCall_simple f (_,k) pred arg _ cont) = do
  i <- meth_count f
  j <- let_count
  y <- ppCAS (cont $ tmp j)
  return $ y {
    assign_exprs = (arg_var f i, arg) : (en_var f i, pred) : (tmp_var j, var' (T.SyntaxKind k) $ ret_var f) : assign_exprs y 
  }

ppCAS (T.CompLetExpr_simple (T.NativeKind _) _ _ _) = error "NativeKind encountered."
ppCAS (T.CompLetExpr_simple (T.SyntaxKind _) arg _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp j)
  return $ y {
    assign_exprs = (tmp_var j, arg) : assign_exprs y
  }

ppCAS (T.CompNondet_simple (T.NativeKind _) _ _) = error "NativeKind encountered."
ppCAS (T.CompNondet_simple (T.SyntaxKind k) _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const k $ T.getDefaultConst k) : assign_exprs y
  }

ppCAS (T.CompSys_simple pred xs _ a) = do
  y <- ppCAS a
  return $ y {
    if_begin_end_exprs = (pred,xs) : if_begin_end_exprs y
  }

ppCAS (T.CompReadReg_simple r k regmap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp j)
  return $ y {
    assign_exprs = (tmp_var j, query_reg ReadMap k r regmap) : assign_exprs y
  }

{-
ppCAS (T.CompRet_simple _ retval regmap) = do
  return $ VerilogExprs {
      assign_exprs = []
    , if_begin_end_exprs = []
    , return_expr = retval
    , return_maps = regmap
  }

ppCAS (T.CompLetFull_simple _  a _ cont) = do
  x <- ppCAS a
  j <- let_count
  let e = return_expr x
  let m = return_maps x
  assigns <- get_all_upds m
  s <- get
  y <- ppCAS (cont j $ regmap_counters s)
  return $ y {
    assign_exprs = (tmp_var j, KExpr e) : assigns ++ assign_exprs y 
  }

ppCAS (T.CompAsyncRead_simple idxNum num dataArray idx _ readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce j)
  return $ y {
    assign_exprs = (tmp_var j, query_async_rf ReadMap dataArray idx num readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readReg dataArray _ True readMap _ cont) = do
  let idx = query_isAddr_reg ReadMap dataArray readReg readMap
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce j)
  return $ y {
    assign_exprs = (tmp_var j, query_isAddr_rf dataArray idx) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readReg dataArray _ False readMap _ cont) = do
  let (b,x) = (query_not_isAddr_valid ReadMap readReg, query_not_isAddr_reg ReadMap dataArray readReg readMap)
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce j)
  return $ y {
    assign_exprs = (tmp_var j, VITE b x $ query_not_isAddr_resp dataArray {-just return dataArray__resp -}) : assign_exprs y
  }

ppCAS (T.CompWrite_simple idxNum _ dataArray readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont j)
  return $ y {
    assign_exprs = (tmp_var j, KExpr $ T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

ppCAS (T.CompSyncReadReq_simple idxNum num _ dataArray readReg isAddr readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont j)
  return $ y {
    assign_exprs = (tmp_var j, KExpr $ T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

query_not_isAddr_resp = undefined
query_not_isAddr_valid = undefined
--query_isAddr_reg = undefined
--get_all_upds = undefined
--do_isAddr_reg_upd = undefined
query_isAddr_rf = undefined {- is this the same as the async read query? -}

{-
query_RME_rf :: (RegMapTy -> H.Map Name Int) -> Name -> T.RME_simple Int RegMapTy -> VExpr
query_RME_rf getmap dataArray readMap = case readMap of
  T.VarRME rmt -> VVar $ dataArray ++ "__resp__" ++ (show $ (getmap rmt) H.! dataArray)
  T.UpdReg _ _ _ _ regMap -> query_RME_rf getmap dataArray regMap
  T.UpdRegFile _ _ _ _ _ _ _ _ _ readMap' _ -> query_RME_rf getmap dataArray readMap'
  T.UpdReadReq _ _ _ _ _ _ _ _ _ readMap' _ -> query_RME_rf getmap dataArray readMap'
  T.CompactRME m -> query_RME_rf getmap dataArray m
-}

main = return ()



ppCompActionT (T.CompRead r _ regmap _ cont) = do
  j <- let_count
  incr_let
  y <- ppCompActionT (cont $ T.unsafeCoerce j)
  m <- map_of_rme_reg regmap
  let x = case m H.! r of
            Left y -> y
            Right i -> r ++ "_" ++ show i
  return $ y {
    assign_exprs = (tmp_var j, Right x) : assign_exprs y
  }

--should not change rfs based on a, pass rf stuff to cont unchanged
ppCompActionT (T.CompLetFull _ a _ cont) = do
  x <- ppCompActionT a
  j <- let_count
  incr_let
  k <- reg_counters
  -- iterate over all registers, for each register r, check if RegMapExprDenotation is a Left (Int) or Right (ExprString);
  -- if Int, then leave k as is for that r, otherwise increment k for that r and add "assign r_(k ! r) = the ExprString"

  let e = return_expr x
  y <- ppCompActionT (cont j {- k' -}) --TODO
  return $ VerilogExprs {
    assign_exprs = (tmp_var j, Left e) : assign_exprs x ++ assign_exprs y
    , if_begin_end_exprs = if_begin_end_exprs x ++ if_begin_end_exprs y
    , return_expr = return_expr y
    , maps = let (a,b) = maps x in let (c,d) = maps y in (H.union c a, H.union d b)
  }

ppCompActionT (T.CompAsyncRead idxNum num dataArray idx _ readMap _ cont) = do
  j <- let_count
  incr_let
  x <- ppCompActionT (cont j)
  return $ x { 
    assign_exprs = (tmp_var j, Left {- etc. -})
   }
  -- if dataArray from readMap is False
  -- dataArray[idx+i] 
  -- otherwise dataArray__write__data[i]
  -- if pred is true and mask[i] is true and idx+i lies within dataArray__write__addr to dataArray__write_addr+num-1 then read what was written
  -- { a, b, c, d } a is the most significant (num-1) down to zero (d)

ppCompActionT (T.CompWrite idxNum num r idx _ val mask pred writeMap readMap _ cont) = undefined
  -- check ExprState (RegMapTy) if the regfile (r/dataArray) has been written to; if so throw error
  -- r__write__addr = idx; r__write__pred = pred; r__write__data = val; r__write__mask = mask (check Some/None)
  -- get a RegMapTy from writeMap, for registers follow CompLetFull stuff, for regfiles only change dataArray
  -- the RegMapTy for dataArray is set to True.
  -- Now pass new RegMapTy from 397+398 to cont.
  -- if(r__write__pred) begin
  --   if(r__write__mask[i]) begin
  --   rf[r__write__addr+i] <= r__write__data[i];
  --   end
  -- ...
  -- end

  --    rf[addr+i] <= pred ? 

ppCompActionT (T.CompSyncReadReq _ _ readReg dataArray idx _ isAddr pred writeMap readMap _ cont) = undefined
  -- analogous to CompLetFull
  -- write into readReg if isAddr == True then idx else val read from dataArray given by readMap
  -- add these new vals into the RegMapExpr denotation
  -- make assignment and pass fresh var to cont

ppCompActionT (T.CompSyncReadRes _ _ readReg dataArray _ isAddr readMap _ cont) = undefined
  -- if isAddr == False just read from readMap
  -- if isAddr == True then check if modified by readMap, do overlap checking and if overlapping return new val from readMap else old val
  -- from dataArray
-}

{-
ppRfInstance :: T.RtlRegFileBase -> String
ppRfInstance (rf@(T.Build_RtlRegFileBase isWrMask num name reads write idxNum dataType init)) =
  "  " ++ ppName name ++ " " ++
  ppName name ++ "$_inst(.CLK(CLK), .RESET(RESET), " ++
  (case reads of
     T.RtlAsync readLs ->
       concatMap (\(read, _) ->
                    ("." ++ ppName read ++ "$_enable(" ++ ppName read ++ "$_enable), ") ++
                    (ppDealSize0 (T.Bit (log2_up idxNum)) "" ("." ++ ppName read ++ "$_argument(" ++ ppName read ++ "$_argument), ")) ++
                    ppDealSize0 (T.Array num dataType) "" ("." ++ ppName read ++ "$_return(" ++ ppName read ++ "$_return), ")) readLs
     T.RtlSync isAddr readLs ->
       concatMap (\(T.Build_RtlSyncRead (T.Build_SyncRead readRq readRs _) _ _) ->
                    ("." ++ ppName readRq ++ "$_enable(" ++ ppName readRq ++ "$_enable), ") ++
                    (ppDealSize0 (T.Bit (log2_up idxNum)) "" ("." ++ ppName readRq ++ "$_argument(" ++ ppName readRq ++ "$_argument), ")) ++
                    ("." ++ ppName readRs ++ "$_enable(" ++ ppName readRs ++ "$_enable), ") ++
                    ppDealSize0 (T.Array num dataType) "" ("." ++ ppName readRs ++ "$_return(" ++ ppName readRs ++ "$_return), ")) readLs) ++
  ("." ++ ppName write ++ "$_enable(" ++ ppName write ++ "$_enable), ") ++
  ("." ++ ppName write ++ "$_argument(" ++ ppName write ++ "$_argument)") ++
  ");\n\n"

ppRfModule :: T.RtlRegFileBase -> String
ppRfModule (rf@(T.Build_RtlRegFileBase isWrMask num name reads write idxNum dataType init)) =
  let writeType = if isWrMask then T.coq_WriteRqMask idxNum num dataType else T.coq_WriteRq idxNum (T.Array num dataType) in
  "module " ++ ppName name ++ "(\n" ++
  (case reads of
     T.RtlAsync readLs ->
       concatMap (\(read, _) ->
                    ("  input " ++ ppDeclType (ppName read ++ "$_enable") T.Bool ++ ",\n") ++
                   (ppDealSize0 (T.Bit (log2_up idxNum)) "" ("  input " ++ ppDeclType (ppName read ++ "$_argument") (T.Bit (log2_up idxNum)) ++ ",\n")) ++
                   ppDealSize0 (T.Array num dataType) "" ("  output " ++ ppDeclType (ppName read ++ "$_return") (T.Array num dataType) ++ ",\n")) readLs
     T.RtlSync isAddr readLs ->
       concatMap (\(T.Build_RtlSyncRead (T.Build_SyncRead readRq readRs _) _ _) ->
                    ("  input " ++ ppDeclType (ppName readRq ++ "$_enable") T.Bool ++ ",\n") ++
                   (ppDealSize0 (T.Bit (log2_up idxNum)) "" ("  input " ++ ppDeclType (ppName readRq ++ "$_argument") (T.Bit (log2_up idxNum)) ++ ",\n")) ++
                    ("  input " ++ ppDeclType (ppName readRs ++ "$_enable") T.Bool ++ ",\n") ++
                   ppDealSize0 (T.Array num dataType) "" ("  output " ++ ppDeclType (ppName readRs ++ "$_return") (T.Array num dataType) ++ ",\n")) readLs) ++
   ("  input " ++ ppDeclType (ppName write ++ "$_enable") T.Bool ++ ",\n") ++
  ppDealSize0 writeType "" (("  input " ++ ppDeclType (ppName write ++ "$_argument") writeType ++ ",\n")) ++
  "  input logic CLK,\n" ++
  "  input logic RESET\n" ++
  ");\n" ++
  ppDealSize0 dataType "" ("  " ++ ppDeclType (ppName name ++ "$_data") dataType ++ "[" ++
                          (case init of
                             T.RFFile _ _ _ offset size _ -> show offset
                             _ -> "0")
                            ++ ":"
                            ++
                            (case init of
                               T.RFFile _ _ _ offset size _ ->
                                 show (offset + size - 1)
                               _ -> show (idxNum - 1))
                            -- ++ show (idxNum - 1)
                            ++ "] /* verilator public */;\n") ++
  (case reads of
     T.RtlSync isAddr readLs ->
       concatMap (\(T.Build_RtlSyncRead (T.Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                    if isAddr
                    then ppDealSize0 (T.Bit (log2_up idxNum)) "" ("  " ++ ppDeclType (ppName readReg) (T.Bit (log2_up idxNum)) ++ ";\n")
                    else ppDealSize0 (T.Array num dataType) "" ("  " ++ ppDeclType (ppName readReg) (T.Array num dataType)) ++
                         ppDealSize0 (T.Array num dataType) "" ("  " ++ ppDeclType (ppName (readReg ++ "$_temp")) (T.Array num dataType))
                 ) readLs
     _ -> "") ++
  "\n" ++
  (case init of
     T.RFFile isAscii isArg file offset size _ ->
       "  initial begin\n" ++
       (if isArg
        then "    string _fileName;\n" ++
             "    $value$plusargs(\"" ++ file ++ "=%s\", _fileName);\n"
        else "") ++
       "    $readmem" ++ (if isAscii then "h" else "b") ++ "(" ++ (if isArg then "_fileName" else "\"" ++ file ++ "\"") ++ ", " ++ ppName name ++ "$_data);\n" ++
       "  end\n\n"
     _ -> "") ++
  let writeByps readAddr i = 
        concatMap (\j -> "(" ++ 
                         "(" ++ ppName write ++ "$_enable && (" ++
                         "(" ++ ppDealSize0 (T.Bit (log2_up idxNum)) "0" (ppName write ++ "$_argument.addr + " ++ show j) ++ ") == " ++
                         "(" ++ ppDealSize0 (T.Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i) ++ "))" ++
                         (if isWrMask
                          then " && " ++ ppName write ++ "$_argument.mask[" ++ show j ++ "]"
                          else "") ++
                         ") ? " ++
                         ppDealSize0 dataType "0" (ppName write ++ "$_argument.data[" ++ show j ++ "]") ++ " : 0) | ")
        [0 .. (num-1)] in
    let readResponse readResp readAddr isByp =
          ppDealSize0 (T.Array num dataType) "" ("  assign " ++ ppName readResp ++ " = " ++ "{" ++
                                                intercalate ", " (map (\i ->
                                                                          ppDealSize0 (T.Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i ++ " < " ++ show idxNum) ++ " ? " ++
                                                                          (if isByp then writeByps readAddr i else "") ++ ppDealSize0 dataType "0" (ppName name ++ "$_data[" ++ (ppDealSize0 (T.Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i)) ++ "]") ++ ": " ++ show (T.size dataType) ++ "'b0")
                                                                  (reverse [0 .. (num-1)])) ++ "};\n") in
      (case reads of
         T.RtlAsync readLs -> concatMap (\(read, bypass) ->
                                         readResponse (read ++ "$_return") (ppName (read ++ "$_argument")) bypass) readLs
         T.RtlSync isAddr readLs ->
           concatMap (\(T.Build_RtlSyncRead (T.Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                        if isAddr
                        then readResponse (readRs ++ "$_return") (if bypRqRs then "(" ++ (ppName (readRq ++ "$_enable") ++ "? " ++ ppName (readRq ++ "$_argument") ++ ": " ++ ppName readReg) ++ ")" else ppName readReg) bypWrRd
                        else readResponse (readReg ++ "$_temp") readRq bypWrRd ++
                             ppDealSize0 (T.Array num dataType) "" ("  assign " ++ ppName readRs ++ " = " ++ if bypRqRs then "(" ++ ppName (readRq ++ "$_enable") ++ "? " ++ ppName (readReg ++ "$_temp") ++ ": " ++ ppName readReg ++ ")"  else ppName readReg)
                     ) readLs) ++
  "  always@(posedge CLK) begin\n" ++
  "    if(RESET) begin\n" ++
  (case init of
     T.RFNonFile (Just initVal) ->
       "      for(int _i = 0; _i < " ++ show idxNum ++ "; _i=_i+1) begin\n" ++
       ppDealSize0 dataType "" ("        " ++ ppName name ++ "$_data[_i] = " ++ ppConst initVal ++ ";\n") ++
       "      end\n"
     _ -> "") ++
  "    end else begin\n" ++
  "      if(" ++ ppName write ++ "$_enable) begin\n" ++
  concat (map (\i ->
                 (if isWrMask then "        if(" ++ ppName write ++ "$_argument.mask[" ++ show i ++ "])\n" else "") ++
                ppDealSize0 dataType "" ("          " ++ ppName name ++ "$_data[" ++ ppDealSize0 (T.Bit (log2_up idxNum)) "0" (ppName write ++ "$_argument.addr + " ++ show i) ++ "] <= " ++
                                         ppDealSize0 dataType "" (ppName write ++ "$_argument.data[" ++ show i ++ "]") ++ ";\n")) [0 .. (num-1)]) ++
  "      end\n" ++
  (case reads of
     T.RtlAsync readLs -> ""
     T.RtlSync isAddr readLs ->
       concatMap (\(T.Build_RtlSyncRead (T.Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                    if isAddr
                    then "      if(" ++ ppName (readRq ++ "$_enable") ++ ") begin\n" ++
                         "        " ++ ppName readReg ++ " <= " ++ ppName (readRq ++ "$_argument") ++ ";\n" ++
                         "      end\n"
                    else "      if(" ++ ppName (readRq ++ "$_enable") ++ ") begin\n" ++
                         "        " ++ ppName readReg ++ " <= " ++ ppName (readReg ++ "$_temp") ++ ";\n" ++
                         "      end\n"
                 ) readLs) ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"

removeDups :: Eq a => [(a, b)] -> [(a, b)]
removeDups = nubBy (\(a, _) (b, _) -> a == b)

getAllMethodsRegFileList :: [T.RtlRegFileBase] -> [(String, (T.Kind, T.Kind))]
getAllMethodsRegFileList ls = concat (map (\(T.Build_RtlRegFileBase isWrMask num dataArray readLs write idxNum d init) ->
                                              (write, (T.coq_WriteRq idxNum d, T.Bit 0)) :
                                              (map (\x -> (fst x, (T.Bit (log2_up idxNum), d)))
                                               (case readLs of
                                                  T.RtlAsync reads -> map (\(x, _) -> (x, (T.Bit (log2_up idxNum), d))) reads
                                                  T.RtlSync _ reads -> map (\(T.Build_RtlSyncRead (T.Build_SyncRead rq rs _) _ _) -> (rq, (T.Bit (log2_up idxNum), T.Bit 0))) reads ++
                                                                       map (\(T.Build_RtlSyncRead (T.Build_SyncRead rq rs _) _ _) -> (rs, (T.Bit 0, d))) reads
                                               ))) ls)


ppRtlInstance :: T.RtlModule -> String
ppRtlInstance m@(T.Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "  _design _designInst(.CLK(CLK), .RESET(RESET)" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" (", ." ++ ppPrintVar nm ++ "(" ++ ppPrintVar nm ++ ")")) (removeDups (ins' ++ outs')) ++ ");\n"
              
ppBitFormat :: T.BitFormat -> String
ppBitFormat T.Binary = "b"
ppBitFormat T.Decimal = "d"
ppBitFormat T.Hex = "x"

ppFullFormat :: T.FullFormat -> String
ppFullFormat (T.FBool sz bf) = "%" ++ show sz ++ ppBitFormat bf
ppFullFormat (T.FBit n sz bf) = "%" ++ show sz ++ ppBitFormat bf
ppFullFormat (T.FStruct n fk fs ff) = "{ " ++ concatMap (\i -> fs i ++ ":" ++ ppFullFormat (ff i) ++ "; ") (T.getFins n) ++ "}"
ppFullFormat (T.FArray n k f) = "[ " ++ concatMap (\i -> show i ++ "=" ++ ppFullFormat f ++ "; ") [0 .. (n-1)] ++ "]"

ppExprList :: T.Kind -> T.RtlExpr -> [T.RtlExpr]
ppExprList T.Bool e = [e]
ppExprList (T.Bit n) e = [e]
ppExprList (T.Struct n fk fs) e = concatMap (\i -> ppExprList (fk i) (T.RtlReadStruct n fk fs e i)) (T.getFins n)
ppExprList (T.Array n k) e = concatMap (\i -> ppExprList k (T.RtlReadArrayConst n k e i)) (T.getFins n)

ppRtlSys :: T.RtlSysT -> State (H.Map String (Int, T.Kind)) String
ppRtlSys (T.RtlDispString s) = return $ "        $write(\"" ++ deformat s ++ "\");\n"
ppRtlSys (T.RtlDispExpr k e f) = do
  printExprs <- mapM (\i -> ppExpr "sys" i) (ppExprList k e)
  return $ "        $write(\"" ++ ppFullFormat f ++ "\"" ++ concatMap (\x -> ", " ++ x) printExprs ++ ");\n"
ppRtlSys (T.RtlFinish) = return $ "        $finish();\n"

ppRtlModule :: T.RtlModule -> String
ppRtlModule m@(T.Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "module _design(\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) ins ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) outs ++ "\n" ++

  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, (T.SyntaxKind ty, init)) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppName nm) ty ++ ";\n")) regInits ++ "\n" ++

  concatMap (\(nm, (ty, expr)) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) assigns ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$sys$" ++ show pos) ty ++ ";\n")) sysTruncs ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$sys$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) sysTruncs ++ "\n" ++
  
  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("  assign " ++ ppPrintVar nm ++ " = " ++ sexpr ++ ";\n")) assignExprs ++ "\n" ++

  "  always @(posedge CLK) begin\n" ++
  "    if(RESET) begin\n" ++
  concatMap (\(nm, (T.SyntaxKind ty, init)) -> case init of
                                                 Just (T.SyntaxConst _ v) -> ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ ppConst v ++ ";\n")
                                                 _ -> "") regInits ++
  "    end\n" ++
  "    else begin\n" ++
  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ sexpr ++ ";\n")) regExprs ++
  concatMap (\(pred, sys) -> "      if(" ++ pred ++ ") begin\n" ++ sys ++ "      end\n") sys ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    regInits = removeDups regInits'
    regWrites = removeDups regWrites'
    assigns = removeDups assigns'
    convAssigns =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppExpr "wire" expr
                return (nm, (ty, s))) assigns
    convRegs =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppExpr "reg" expr
                return (nm, (ty, s))) regWrites
    (assignExprs, assignTruncs') = runState convAssigns H.empty
    (regExprs, regTruncs') = runState convRegs H.empty
    assignTruncs = H.toList assignTruncs'
    regTruncs = H.toList regTruncs'
    convSys = mapM(\(pred, listSys) ->
                      do
                        predExpr <- ppExpr "sys" pred
                        s <- mapM ppRtlSys listSys
                        return $ (predExpr, Data.List.concat s)) sys'
    (sys, sysTruncs') = runState convSys H.empty
    sysTruncs = H.toList sysTruncs'

ppGraph :: [(String, [String])] -> String
ppGraph x = case x of
              [] -> ""
              (a, b) : ys -> "(" ++ show a ++ ", " ++ show b ++ ", " ++ show (Data.List.length b) ++ "),\n" ++ ppGraph ys


maxOutEdge :: [(String, [String])] -> Int
maxOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Prelude.max (Data.List.length b) (maxOutEdge ys)

sumOutEdge :: [(String, [String])] -> Int
sumOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Data.List.length b + sumOutEdge ys


ppTopModule :: T.RtlModule -> String
ppTopModule m@(T.Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  concatMap ppRfModule regFs ++
  ppRtlModule m ++
  "module system(\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) insFiltered ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) outsFiltered ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) ins ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) outs ++ "\n" ++
  concatMap ppRfInstance regFs ++
  ppRtlInstance m ++
  "endmodule\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    isHidden (x, _) = not (elem x hiddenWires)
    insFiltered = Data.List.filter isHidden ins
    outsFiltered = Data.List.filter isHidden outs
              
printDiff :: [(String, [String])] -> [(String, [String])] -> IO ()
printDiff (x:xs) (y:ys) =
  do
    if x == y
    then printDiff xs ys
    else putStrLn $ (show x) ++ " " ++ (show y)
printDiff [] [] = return ()
printDiff _ _ = putStrLn "Wrong lengths"

ppConstMem :: T.ConstT -> String
ppConstMem (T.ConstBool b) = if b then "1" else "0"
ppConstMem (T.ConstBit sz w) = if sz == 0 then "0" else ppWord w
ppConstMem (T.ConstStruct num fk fs fv) = Data.List.concatMap ppConstMem (Data.List.map fv (T.getFins num))
ppConstMem (T.ConstArray num k fv) = Data.List.concatMap ppConstMem (Data.List.map fv (reverse $ T.getFins num))

ppRfFile :: (((String, [(String, Bool)]), String), ((Int, T.Kind), T.ConstT)) -> String
ppRfFile (((name, reads), write), ((idxType, dataType), T.ConstArray num k fv)) =
  concatMap (\v -> ppConstMem v ++ "\n") (Data.List.map fv (reverse $ T.getFins num)) ++ "\n"

ppRfName :: (((String, [(String, Bool)]), String), ((Int, T.Kind), T.ConstT)) -> String
ppRfName (((name, reads), write), ((idxType, dataType), T.ConstArray num k fv)) = ppName name ++ ".mem"

main = putStrLn $ ppTopModule T.rtlMod
-}

main = return ()