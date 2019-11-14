Require Import Kami.Syntax Kami.Compiler.Compiler.
Require Import Kami.Notations.

Section Simple.

  Variable ty : Kind -> Type.
  Variable regMapTy : Type.

  Inductive RmeSimple :=
  | VarRME (v : regMapTy) : RmeSimple
  | UpdRegRME (r : string)(pred : Bool @# ty)(k : FullKind)(val : Expr ty k)(regMap : RmeSimple) : RmeSimple
  | WriteRME (idxNum num : nat) (writePort dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
             (val : Array num Data @# ty)
             (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RmeSimple)
             (arr : Array idxNum Data @# ty) : RmeSimple
  | ReadReqRME (idxNum num : nat) (readReq readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
               (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RmeSimple)
               (arr : Array idxNum Data @# ty) : RmeSimple
  | ReadRespRME (idxNum num : nat) (readResp readReg dataArray writePort : string) (isWriteMask: bool) (Data : Kind)
               (isAddr : bool) (writeMap readMap : RmeSimple) : RmeSimple
  | AsyncReadRME (idxNum num : nat) (readPort dataArray writePort : string) (isWriteMask: bool)
                 (idx : Bit (Nat.log2_up idxNum) @# ty) (pred : Bool @# ty)
                 (k : Kind)(writeMap readMap : RmeSimple) : RmeSimple
  | CompactRME (regMap: RmeSimple): RmeSimple.

  Fixpoint RmeSimple_of_RME(x : RegMapExpr ty regMapTy) : RmeSimple :=
    match x with
    | VarRegMap v => VarRME v
    | UpdRegMap r pred k val regMap => UpdRegRME r pred val (RmeSimple_of_RME regMap)
    | CompactRegMap x' => CompactRME (RmeSimple_of_RME x')
    end.

  Inductive CompActionSimple : Kind -> Type :=
  | CompCall_simple (f : string)(argRetK : Kind * Kind)(pred : Bool @# ty)(arg : fst argRetK @# ty)
                    lret (cont : fullType ty (SyntaxKind (snd argRetK)) -> CompActionSimple lret) : CompActionSimple lret
  | CompLetExpr_simple k (e : Expr ty k) lret (cont : fullType ty k -> CompActionSimple lret) : CompActionSimple lret
  | CompNondet_simple k lret (cont : fullType ty k -> CompActionSimple lret) : CompActionSimple lret
  | CompSys_simple (pred: Bool @# ty) (ls: list (SysT ty)) lret (cont: CompActionSimple lret): CompActionSimple lret
  | CompReadReg_simple (r: string) (k: FullKind) (readMap : RmeSimple) lret
                       (cont: fullType ty k -> CompActionSimple lret): CompActionSimple lret
  | CompRet_simple lret (e: lret @# ty) (newMap: RmeSimple) : CompActionSimple lret
  | CompLetFull_simple k (a: CompActionSimple k) lret (cont: fullType ty (SyntaxKind k) ->
                                                      regMapTy -> CompActionSimple lret): CompActionSimple lret
  | CompAsyncRead_simple (idxNum num : nat) (readPort dataArray writePort : string) (isWriteMask: bool) (idx : Bit (Nat.log2_up idxNum) @# ty)
                         (pred : Bool @# ty)
                         (k : Kind)
                         (readMap : RmeSimple) lret
                         (cont : fullType ty (SyntaxKind (Array num k)) -> CompActionSimple lret) : CompActionSimple lret
  | CompSyncReadRes_simple (idxNum num : nat) (readResp readReg dataArray writePort : string) (isWriteMask: bool) (Data : Kind) (isAddr : bool)
                           (readMap : RmeSimple) lret
                           (cont : fullType ty (SyntaxKind (Array num Data)) -> CompActionSimple lret) : CompActionSimple lret
  | CompWrite_simple (idxNum : nat) (Data : Kind) (writePort dataArray : string) (readMap : RmeSimple) lret
                     (cont : ty (Array idxNum Data) -> CompActionSimple lret) : CompActionSimple lret
  | CompSyncReadReq_simple (idxNum num : nat) (Data : Kind) (readReq readReg dataArray : string) (isAddr : bool)
                           (readMap : RmeSimple) lret
                           (cont : ty (Array idxNum Data) -> CompActionSimple lret) : CompActionSimple lret.

  Fixpoint CompActionSimple_of_CA{k}(a : CompActionT ty regMapTy k) : CompActionSimple k :=
    match a with
    | CompCall f argRetK pred arg lret cont => CompCall_simple f argRetK pred arg (fun x => CompActionSimple_of_CA (cont x))
    | CompLetExpr k e lret cont => CompLetExpr_simple e (fun x => CompActionSimple_of_CA (cont x))
    | CompNondet k lret cont => CompNondet_simple k (fun x => CompActionSimple_of_CA (cont x))
    | CompSys pred ls lret cont => CompSys_simple pred ls (CompActionSimple_of_CA cont)
    | CompRead r k readMap lret cont => CompReadReg_simple r k (RmeSimple_of_RME readMap)
                                                           (fun x => CompActionSimple_of_CA (cont x))
    | CompRet lret e newMap => CompRet_simple e (RmeSimple_of_RME newMap)
    | CompLetFull k a lret cont => CompLetFull_simple (CompActionSimple_of_CA a) (fun x y => CompActionSimple_of_CA (cont x y))
    | CompAsyncRead idxNum num readPort dataArray writePort isWriteMask idx pred k writeMap readMap lret cont =>
      CompAsyncRead_simple idxNum readPort dataArray writePort isWriteMask idx pred (RmeSimple_of_RME readMap)
                           (fun arr =>
                              CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
                                                     (AsyncReadRME idxNum num readPort dataArray
                                                                   writePort isWriteMask idx pred
                                                                   k (RmeSimple_of_RME writeMap)
                                                                   (RmeSimple_of_RME readMap)))
                              (fun _ x => CompActionSimple_of_CA (cont arr x)))
    | CompWrite idxNum num writePort dataArray idx Data val mask pred writeMap readMap lret cont =>
      @CompWrite_simple idxNum Data writePort dataArray (RmeSimple_of_RME readMap) lret
                        (fun arr => 
                           CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
                                                              (@WriteRME idxNum num writePort dataArray idx Data val mask pred
                                                                         (RmeSimple_of_RME writeMap)
                                                                         (RmeSimple_of_RME readMap) (#arr)%kami_expr))
                                              (fun _ y => CompActionSimple_of_CA (cont y)))
    | CompSyncReadReq idxNum num readReq readReg dataArray idx Data isAddr pred writeMap readMap lret cont =>
      @CompSyncReadReq_simple idxNum num Data readReq readReg dataArray isAddr (RmeSimple_of_RME readMap) lret
                              (fun x => CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
                                                                           (@ReadReqRME idxNum num readReq readReg dataArray
                                                                                        idx Data isAddr pred
                                                                                        (RmeSimple_of_RME writeMap)
                                                                                        (RmeSimple_of_RME readMap)
                                                                                        (#x)%kami_expr))
                                                           (fun _ y => CompActionSimple_of_CA (cont y)))
    | CompSyncReadRes idxNum num readResp readReg dataArray writePort isWriteMask Data isAddr writeMap readMap lret cont =>
      CompSyncReadRes_simple idxNum readResp readReg dataArray writePort isWriteMask isAddr
                             (@ReadRespRME idxNum num readResp readReg dataArray writePort
                                           isWriteMask Data isAddr (RmeSimple_of_RME writeMap)
                                           (RmeSimple_of_RME readMap))
                             (fun x => CompLetFull_simple (CompRet_simple (($$WO)%kami_expr : Void @# ty) (RmeSimple_of_RME writeMap))
                                (fun _ y => CompActionSimple_of_CA (cont x y)))
    end.

  Definition CAS_RulesRf(readMap : regMapTy) (rules : list RuleT) (lrf : list RegFileBase) :=
    CompActionSimple_of_CA (compileRulesRf ty readMap rules lrf).

End Simple.
