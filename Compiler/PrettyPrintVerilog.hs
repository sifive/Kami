{-# OPTIONS_GHC -XStandaloneDeriving #-}
{-# LANGUAGE Strict #-}

module PrettyPrintVerilog where

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

ppPrintVar :: (String, Maybe Int) -> String
ppPrintVar (s, Just v) = ppName $ s ++ {- if v /= 0 then '#' : show v else [] -} '#' : show v
ppPrintVar (s, Nothing) = ppName $ s

padwith :: a -> Int -> [a] -> [a]
padwith x n xs = let m = n - length xs in
  if m > 0 then replicate m x ++ xs else drop (-m) xs

ppWord :: Int -> Integer -> String
ppWord n i = padwith '0' n $ showIntAtBase 2 intToDigit i ""

ppConst :: T.ConstT -> String
ppConst (T.ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (T.ConstBit sz w) = show sz ++ "\'b" ++ ppWord sz w
ppConst (T.ConstArray n k fv) = '{' : intercalate ", " (Data.List.map ppConst (Data.List.map fv (reverse $ T.getFins n))) ++ "}"
ppConst (T.ConstStruct n fk fs fv) = '{' : intercalate ", " (snd (unzip (Data.List.filter (\(k,e) -> T.size k /= 0) (zip (Data.List.map fk (T.getFins n)) (Data.List.map ppConst (Data.List.map fv (T.getFins n))))))) ++ "}"

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
ppExprList (T.Struct n fk fs) e = concatMap (\i -> ppExprList (fk i) (T.ReadStruct n fk fs e i)) (T.getFins n)
ppExprList (T.Array n k) e = concatMap (\i -> ppExprList k (T.ReadArrayConst n k e i)) (T.getFins n)

ppRtlSys :: T.SysT T.Coq_rtl_ty -> State (H.Map String (Int, T.Kind)) String
ppRtlSys (T.DispString s) = return $ "        $write(\"" ++ deformat s ++ "\");\n"
ppRtlSys (T.DispExpr k e f) = do
  printExprs <- mapM (\i -> ppRtlExpr "sys" i) (ppExprList k e)
  return $ "        $write(\"" ++ ppFullFormat f ++ "\"" ++ concatMap (\x -> ", " ++ x) printExprs ++ ");\n"
ppRtlSys (T.Finish) = return $ "        $finish();\n"

optionAddToTrunc :: String -> T.Kind -> T.RtlExpr -> State (H.Map String (Int, T.Kind)) String
optionAddToTrunc who k e =
  case e of
    T.Var (T.SyntaxKind k') x ->
      case k' of
        T.Bit 0 -> return "0"
        _ -> return $ ppPrintVar (T.unsafeCoerce x)
    _ -> do
      x <- ppRtlExpr who e
      new <- addToTrunc who k x
      return new

createTrunc :: String -> T.Kind -> T.RtlExpr -> Int -> Int -> State (H.Map String (Int, T.Kind)) String
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

ppRtlExpr :: String -> T.RtlExpr -> State (H.Map String (Int, T.Kind)) String
ppRtlExpr who e = 
  case e of
    T.Var (T.SyntaxKind k) x -> return $ ppDealSize0 k "0" (ppPrintVar (T.unsafeCoerce x))
    T.Var (T.NativeKind _) _ -> error "NativeKind encountered."
    T.Const k c -> return $ ppDealSize0 k "0" (ppConst c)
    T.UniBool T.Neg e -> uniExpr "~" e
    T.CABool T.And es -> listExpr "&" es "1'b1"
    --T.CABool T.Or es -> listExpr "|" es "1'b0"
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
    --T.CABit n T.Bor es -> listExpr "|" es (show n ++ "'b0")
    T.CABit n T.Bxor es -> listExpr "^" es (show n ++ "'b0")
    T.BinBit _ _ _ (T.Sub _) e1 e2 -> binExpr e1 "-" e2
    T.BinBit _ _ _ (T.Div _) e1 e2 -> binExpr e1 "/" e2
    T.BinBit _ _ _ (T.Rem _) e1 e2 -> binExpr e1 "%" e2
    T.BinBit _ _ _ (T.Sll _ _) e1 e2 -> binExpr e1 "<<" e2
    T.BinBit _ _ _ (T.Srl _ _) e1 e2 -> binExpr e1 ">>" e2
    T.Kor k es -> listExpr "|" es (ppConst (T.getDefaultConst k))
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

getRegFileNames :: T.RegFileBase -> [(Bool, T.Kind, String)]
getRegFileNames (rf@(T.Build_RegFileBase isWrMask num name reads write idxNum dataType init)) =
  (case reads of
     T.Async readLs ->
       concatMap (\(read) ->
                    [(True, T.Bool, read ++ "#_enable"),
                     (True, T.Bit (log2_up idxNum), read ++ "#_argument"),
                     (False, T.Array num dataType, read ++ "#_return")]) readLs
     T.Sync isAddr readLs ->
       concatMap (\(T.Build_SyncRead readRq readRs readReg) ->
                    [(True, T.Bool, readRq ++ "#_enable"),
                     (True, T.Bit (log2_up idxNum), readRq ++ "#_argument"),
                     (True, T.Bool, readRs ++ "#_enable"),
                     (False, T.Array num dataType, readRs ++ "#_return")]) readLs) ++
  [(True, T.Bool, write ++ "#_enable"),
   (True, writeType, write ++ "#_argument")]
  where writeType = if isWrMask then T.coq_WriteRqMask (log2_up idxNum) num dataType else T.coq_WriteRq (log2_up idxNum) (T.Array num dataType)
  

ppRfInstance :: T.RegFileBase -> String
ppRfInstance (rf@(T.Build_RegFileBase isWrMask num name reads write idxNum dataType init)) =
  "  " ++ ppName name ++ " " ++
  ppName name ++ "$_inst(.CLK(CLK), .RESET(RESET)" ++
  concatMap (\(_, k, name) -> ppDealSize0 k "" (", ." ++ ppName name ++ "(" ++ ppName name ++ ")")) (getRegFileNames rf) ++
  ");\n\n"

ppRfModule :: T.RegFileBase -> String
ppRfModule (rf@(T.Build_RegFileBase isWrMask num name reads write idxNum dataType init)) =
  let getInput isInput = if isInput then "  input " else "  output " in
    
  "module " ++ ppName name ++ "(\n" ++
  concatMap (\(isInput, k, name) -> ppDealSize0 k "" (getInput isInput ++ ppDeclType (ppName name) k) ++ ",\n") (getRegFileNames rf) ++
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
     T.Sync isAddr readLs ->
       concatMap (\(T.Build_SyncRead readRq readRs readReg) ->
                    if isAddr
                    then ppDealSize0 (T.Bit (log2_up idxNum)) "" ("  " ++ ppDeclType (ppName readReg) (T.Bit (log2_up idxNum)) ++ ";\n")
                    else ppDealSize0 (T.Array num dataType) "" ("  " ++ ppDeclType (ppName readReg) (T.Array num dataType) ++ ";\n") ++
                         ppDealSize0 (T.Array num dataType) "" ("  " ++ ppDeclType (ppName (readReg ++ "$_temp")) (T.Array num dataType) ++ ";\n")
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
    let readResponse readResp readAddr =
          ppDealSize0 (T.Array num dataType) "" ("  assign " ++ ppName readResp ++ " = " ++ "{" ++
                                                intercalate ", " (map (\i ->
                                                                          ppDealSize0 (T.Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i ++ " < " ++ show idxNum) ++ " ? " ++
                                                                          ppDealSize0 dataType "0" (ppName name ++ "$_data[" ++ (ppDealSize0 (T.Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i)) ++ "]") ++ ": " ++ show (T.size dataType) ++ "'b0")
                                                                  (reverse [0 .. (num-1)])) ++ "};\n") in
      (case reads of
         T.Async readLs -> concatMap (\(read) ->
                                         readResponse (read ++ "$_return") (ppName (read ++ "$_argument"))) readLs
         T.Sync isAddr readLs ->
           concatMap (\(T.Build_SyncRead readRq readRs readReg) -> 
                        if isAddr
                        then readResponse (readRs ++ "$_return") (ppName readReg)
                        else readResponse (readReg ++ "$_temp") (readRq ++ "$_argument") ++
                             ppDealSize0 (T.Array num dataType) "" ("  assign " ++ ppName readRs ++ "$_return = " ++ ppName readReg ++ ";\n")
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
     T.Async readLs -> ""
     T.Sync isAddr readLs ->
       concatMap (\(T.Build_SyncRead readRq readRs readReg) ->
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

kind_of_fullKind :: T.FullKind -> T.Kind
kind_of_fullKind (T.SyntaxKind k) = k
kind_of_fullKind (T.NativeKind _) = error "NativeKind encountered"

removeDups :: Eq a => [(a, b)] -> [(a, b)]
removeDups = nubBy (\(a, _) (b, _) -> a == b)

ppRtlInstance :: T.RtlModule -> String
ppRtlInstance m@(T.Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "  _design _designInst(.CLK(CLK), .RESET(RESET)" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" (", ." ++ ppPrintVar nm ++ "(" ++ ppPrintVar nm ++ ")")) (removeDups (ins' ++ outs' ++ (map (\(_,k,name) -> ((name,Nothing),k)) $ concatMap getRegFileNames regFs))) ++ ");\n"

ppRtlModule :: T.RtlModule -> String
ppRtlModule m@(T.Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "module _design(\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) ins ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) outs ++ "\n" ++

  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, (T.SyntaxKind ty, init)) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) regInits ++ "\n" ++

  concatMap (\(nm, (ty, expr)) ->
               if nm `elem` (map fst outs)
               then ""
               else ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) assigns ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$sys$" ++ show pos) ty ++ ";\n")) sysTruncs ++ "\n" ++

  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("  assign " ++ ppPrintVar nm ++ " = " ++ sexpr ++ ";\n")) assignExprs ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$sys$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) sysTruncs ++ "\n" ++
  
  "  always @(posedge CLK) begin\n" ++
  "    if(RESET) begin\n" ++
  concatMap (\(nm, (T.SyntaxKind ty, init)) ->
               case init of
                 Just (T.SyntaxConst _ v) -> ppDealSize0 ty "" ("      " ++ ppPrintVar nm ++ " <= " ++ ppConst v ++ ";\n")
                 _ -> "") regInits ++
  "    end\n" ++
  "    else begin\n" ++
  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("      " ++ ppPrintVar nm ++ " <= " ++ sexpr ++ ";\n")) (map (\(s1,(k,s2)) -> (s1,(kind_of_fullKind k,s2))) regExprs) ++
  concatMap (\(pred, sys) -> "      if(" ++ pred ++ ") begin\n" ++ sys ++ "      end\n") sys ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"
  where
    (regFsOuts,regFsIns) = partition (\(isInput,_,_) -> isInput) (concatMap getRegFileNames regFs)
    ins = removeDups (ins' ++ map (\(_,k,name) -> ((name,Nothing),k)) regFsIns)
    outs = removeDups (outs' ++ map (\(_,k,name) -> ((name,Nothing),k)) regFsOuts)
    regInits = regInits'
    regWrites = regWrites'
    assigns = map (\(p,(k,x)) -> (p,(kind_of_fullKind k,x))) assigns'
    convAssigns =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "wire" expr
                return (nm, (ty, s))) assigns
    convRegs =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "reg" expr
                return (nm, (ty, s))) regWrites
    (assignExprs, assignTruncs') = runState convAssigns H.empty
    (regExprs, regTruncs') = runState convRegs H.empty
    assignTruncs = H.toList assignTruncs'
    regTruncs = H.toList regTruncs'
    convSys = mapM(\(pred, listSys) ->
                      do
                        predExpr <- ppRtlExpr "sys" pred
                        s <- mapM ppRtlSys listSys
                        return $ (predExpr, Data.List.concat s)) sys'
    (sys, sysTruncs') = runState convSys H.empty
    sysTruncs = H.toList sysTruncs'

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
  concatMap (\rf -> concatMap (\(isInput, k, name) -> ppDealSize0 k "" ("  " ++ ppDeclType (ppName name) k) ++ ";\n") (getRegFileNames rf)) regFs ++
  concatMap ppRfInstance regFs ++
  ppRtlInstance m ++
  "endmodule\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    isHidden (x, _) = not (elem x hiddenWires)
    insFiltered = Data.List.filter isHidden ins
    outsFiltered = Data.List.filter isHidden outs

