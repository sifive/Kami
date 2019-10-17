module CompAction where

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric

log2_up :: Int -> Int
log2_up = ceiling . (logBase 2) . fromIntegral

type RME = T.RmeSimple T.Coq_rtl_ty RegMapTy

data CommonInfo =
  CommonInfo
  { commonIsWrMask :: Bool
  , commonNum :: Int
  , commonDataArray :: String
  , commonWrite :: String
  , commonIdxNum :: Int
  , commonInit :: T.RegFileInitT }
  
data Async =
  Async
  { asyncCommon :: CommonInfo
  , asyncNames :: [String] }

data Sync =
  Sync
  { isAddrCommon :: CommonInfo
  , isAddrNames :: [T.SyncRead] }

data Register =
  Register
  { registerName :: String
  , registerKind :: T.FullKind }

data RegMapTy =
  RegMapTy
  { reg_counters :: H.Map String Int
  , write_counters :: H.Map String Int
  , async_read_counters :: H.Map String Int
  , isAddr_read_req_counters :: H.Map String Int
  , isAddr_read_reg_counters :: H.Map String Int
  , not_isAddr_read_req_counters :: H.Map String Int
  , not_isAddr_read_reg_counters :: H.Map String Int }

data ExprState = ExprState
  { let_counter :: Int
  , regmap_counters :: RegMapTy
  , meth_counters :: H.Map String Int
  , all_regs :: [Register]
  , all_asyncs :: [Async]
  , all_isAddrs :: [Sync]
  , all_not_isAddrs :: [Sync] }

data PredCall =
  PredCall
  { pred_val :: T.RtlExpr'
  , call_val :: T.RtlExpr' }

queryReg :: String -> T.FullKind -> Bool -> RME -> T.RtlExpr
queryReg name k isWrite regMap =
  query regMap
  where
    query (T.VarRME v) = T.Var k $ T.unsafeCoerce (name, Just $ reg_counters v H.! name)
    query (T.UpdRegRME r pred k val regMap') =
      let restVal = query regMap' in
        if r == name
        then T.ITE k pred val restVal
        else restVal
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryRfWrite :: String -> Int -> Int -> T.Kind -> Bool -> Bool -> RME -> PredCall
queryRfWrite name idxNum num k isMask isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.orKind writeType calls)
  where
    writeType = if isMask then T.coq_WriteRqMask (log2_up idxNum) num k else T.coq_WriteRq (log2_up idxNum) (T.Array num k)
    addrSize = log2_up idxNum
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind writeType) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      let (restPred, restCall) = query (if isWrite then writeMap else readMap) in
        if writePort == name
        then (pred : restPred, T.predPack (T.Bit $ T.size writeType) pred (case mask of
                                                                              Nothing -> T.createWriteRq idxNum num dataK idx val
                                                                              Just mask' -> T.createWriteRqMask idxNum num dataK idx val mask') : restCall)
        else (restPred, restCall)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryAsyncReadReq :: String -> Int -> Bool -> RME -> PredCall
queryAsyncReadReq name idxNum isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.orKind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      let (restPred, restAddr) = query readMap in
        if readPort == name
        then (pred : restPred, T.predPack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.CompactRME regMap) =
      query regMap

querySyncReadReq :: String -> Int -> Bool -> RME -> PredCall
querySyncReadReq name idxNum isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.orKind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      let (restPred, restAddr) = query (if isWrite then writeMap else readMap) in
        if readReq == name
        then (pred : restPred, T.predPack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryIsAddrRegWrite :: String -> Int -> RME -> T.RtlExpr'
queryIsAddrRegWrite name idxNum regMap = T.ITE (T.SyntaxKind (T.Bit (log2_up idxNum))) (pred_val readCall) (call_val readCall) regVal
  where
    readCall = querySyncReadReq name idxNum True regMap
    regVal = T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) (T.unsafeCoerce (name, Nothing))

queryNotIsAddrRegWrite :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryNotIsAddrRegWrite name writeName readReqName idxNum num k isMask regMap = pointwise
  where
    readCall = querySyncReadReq readReqName idxNum True regMap
    writeCall = queryRfWrite writeName idxNum num k isMask True regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (pred_val readCall) (call_val readCall) (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

queryAsyncReadResp :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryAsyncReadResp name writeName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = (T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing)))
    readCall = queryAsyncReadReq name idxNum False regMap
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (pred_val readCall) (call_val readCall) (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

queryIsAddrReadResp :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryIsAddrReadResp name writeName regName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing))
    readAddr = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (regName, Nothing))
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (T.Const T.Bool (T.ConstBool True)) readAddr (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

queryNotIsAddrReadResp :: String -> String -> Int -> T.Kind -> T.RtlExpr'
queryNotIsAddrReadResp name regName num k =
  T.pointwiseBypass num k bypass respVal
  where
    bypass = T.Var (T.SyntaxKind (T.Array num (T.coq_Maybe k))) (T.unsafeCoerce (regName, Nothing))
    respVal = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing))

type CA_rtl = T.CompActionSimple T.Coq_rtl_ty RegMapTy

data VerilogExprs = VerilogExprs {
    assign_exprs :: [(T.VarType, T.RtlExpr')]
  , if_begin_end_exprs :: [(T.RtlExpr', [T.SysT T.Coq_rtl_ty])]
  , return_expr :: T.RtlExpr'
  , return_maps :: RME
}

monad_concat :: Monad m => [m [a]] -> m [a]
monad_concat ms = fmap concat $ sequence ms

tmp_var :: Int -> T.VarType
tmp_var j = ("tmp", Just j)

arg_var :: String -> Int -> T.VarType
arg_var f i = (f ++ "#_argument", Just i)

let_count :: State ExprState Int
let_count = do
  s <- get
  let n = let_counter s
  put $ s { let_counter = n+1 }
  return n

meth_count :: String -> State ExprState Int
meth_count f = do
  s <- get
  let n = meth_counters s H.! f
  put $ s { meth_counters = H.insert f (n+1) $ meth_counters s }
  return n

reg_count :: String -> State ExprState Int
reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { reg_counters = H.insert r (n+1) rc } }
  return n

write_count :: String -> State ExprState Int
write_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = write_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { write_counters = H.insert r (n+1) rc } }
  return n

async_read_count :: String -> State ExprState Int
async_read_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = async_read_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { async_read_counters = H.insert r (n+1) rc } }
  return n

isAddr_read_req_count :: String -> State ExprState Int
isAddr_read_req_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = isAddr_read_req_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { isAddr_read_req_counters = H.insert r (n+1) rc } }
  return n

isAddr_read_reg_count :: String -> State ExprState Int
isAddr_read_reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = isAddr_read_reg_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { isAddr_read_reg_counters = H.insert r (n+1) rc } }
  return n
  
not_isAddr_read_req_count :: String -> State ExprState Int
not_isAddr_read_req_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = not_isAddr_read_req_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { not_isAddr_read_req_counters = H.insert r (n+1) rc } }
  return n

not_isAddr_read_reg_count :: String -> State ExprState Int
not_isAddr_read_reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = not_isAddr_read_reg_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { not_isAddr_read_reg_counters = H.insert r (n+1) rc } }
  return n

do_reg :: String -> T.FullKind -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_reg r k m = case queryReg r k True m of
  T.Var _ _ -> return []
  e -> do
    i <- reg_count r
    return [((r, Just i),e)]

do_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_regs m = do
  s <- get
  monad_concat $ map (\(Register r k) -> do_reg r k m) (all_regs s)

do_write :: String -> Int -> Int -> T.Kind -> Bool -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_write writeName idxNum num k isMask regMap = case queryRfWrite writeName idxNum num k isMask True regMap of
  PredCall (T.Var _ _) (T.Var _ _) -> return []
  PredCall e1 e2 -> do
    i <- write_count writeName
    return [((writeName ++ "#_enable", Just i), e1), ((writeName ++ "#_argument", Just i), e2)]

all_writes :: ExprState -> [(String, Int, Int, T.Kind, Bool)]
all_writes = undefined

do_writes :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_writes m = do
  s <- get
  monad_concat $ map (\(r, idxNum, num, k, isMask) -> do_write r idxNum num k isMask m)
    (all_writes s)

do_async_reads :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_async_reads m = undefined

do_isAddr_read_reqs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_reqs m = undefined

do_isAddr_read_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_regs m = undefined

do_not_isAddr_read_reqs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_reqs m = undefined

do_not_isAddr_read_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_regs m = undefined


get_all_upds :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
get_all_upds m = do
  assigns1 <- do_regs m
  assigns2 <- do_writes m
  assigns3 <- do_async_reads m
  assigns4 <- do_isAddr_read_reqs m
  assigns5 <- do_isAddr_read_regs m
  assigns6 <- do_not_isAddr_read_reqs m
  assigns7 <- do_not_isAddr_read_regs m
  return $ assigns1 ++ assigns2 ++ assigns3 ++ assigns4 ++ assigns5 ++ assigns6 ++ assigns7

-- Counters contain the next value to assign

ppCAS :: CA_rtl -> State ExprState VerilogExprs
ppCAS (T.CompCall_simple f (_,k) pred arg _ cont) = do
  i <- meth_count f
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = ((f ++ "#_argument", Just i), arg) :
                   ((f ++ "#_enable", Just i), pred) :
                   (tmp_var j, T.Var (T.SyntaxKind k) $ T.unsafeCoerce (f ++ "#_return", Nothing)) :
                   assign_exprs y 
  }

ppCAS (T.CompLetExpr_simple (T.NativeKind _) _ _ _) = error "NativeKind encountered."
ppCAS (T.CompLetExpr_simple (T.SyntaxKind _) expr _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, expr) : assign_exprs y
  }

ppCAS (T.CompNondet_simple (T.NativeKind _) _ _) = error "NativeKind encountered."
ppCAS (T.CompNondet_simple (T.SyntaxKind k) _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const k $ T.getDefaultConst k) : assign_exprs y
  }

ppCAS (T.CompSys_simple pred xs _ a) = do
  y <- ppCAS a
  return $ y {
    if_begin_end_exprs = (pred,xs) : if_begin_end_exprs y
  }

ppCAS (T.CompReadReg_simple r k regMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, queryReg r k False regMap) : assign_exprs y
  }

ppCAS (T.CompRet_simple _ retVal regMap) = do
  return $ VerilogExprs {
    assign_exprs = []
    , if_begin_end_exprs = []
    , return_expr = retVal
    , return_maps = regMap
  }

ppCAS (T.CompLetFull_simple _  a _ cont) = do
  (VerilogExprs assigns_a if_begin_ends_a ret_a map_a) <- ppCAS a
  j <- let_count
  assigns <- get_all_upds map_a
  s <- get
  y <- ppCAS (cont (tmp_var j) $ regmap_counters s)
  return $ y {
    assign_exprs = (tmp_var j, ret_a) : assigns ++ assigns_a ++ assign_exprs y
    , if_begin_end_exprs = if_begin_ends_a ++ if_begin_end_exprs y
  }

ppCAS (T.CompAsyncRead_simple idxNum num readPort dataArray idx pred k readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, queryAsyncReadResp readPort undefined idxNum num k undefined readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray k True readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, queryIsAddrReadResp readResp undefined readReg idxNum num k undefined readMap) : assign_exprs y
  }
ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray k False readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, queryNotIsAddrReadResp readResp readReg num k) : assign_exprs y
  }

ppCAS (T.CompWrite_simple idxNum k writePort dataArray readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

ppCAS (T.CompSyncReadReq_simple idxNum num k readReq readReg dataArray isAddr readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }
