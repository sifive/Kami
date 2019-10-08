Require Import Kami.All.
Require Import Kami.Notations.

Section Simple.

  Variable ty : Kind -> Type.
  Variable regMapTy : Type.

  Inductive RME_simple :=
  | VarRME (v : regMapTy) : RME_simple
  | UpdReg (r : string)(pred : Bool @# ty)(k : FullKind)(val : Expr ty k)(regMap : RME_simple) : RME_simple
  | UpdRegFile (idxNum num : nat) (dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
               (val : Array num Data @# ty)
               (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RME_simple)
               (arr : Array idxNum Data @# ty) : RME_simple
  | UpdReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
               (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RME_simple)
               (arr : Array idxNum Data @# ty) : RME_simple
  | AsyncRead (idxNum num : nat) (readPort dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (pred : Bool @# ty)
              (k : Kind)(readMap : RME_simple) : RME_simple
  | CompactRME (regMap: RME_simple): RME_simple.

  Fixpoint RME_simple_of_RME(x : RegMapExpr ty regMapTy) : RME_simple :=
    match x with
    | VarRegMap v => VarRME v
    | UpdRegMap r pred k val regMap => UpdReg r pred val (RME_simple_of_RME regMap)
    | CompactRegMap x' => CompactRME (RME_simple_of_RME x')
    end.

  Inductive CA_simple : Kind -> Type :=
  | CompCall_simple (f : string)(argRetK : Kind * Kind)(pred : Bool @# ty)(arg : fst argRetK @# ty)
                    lret (cont : fullType ty (SyntaxKind (snd argRetK)) -> CA_simple lret) : CA_simple lret
  | CompLetExpr_simple k (e : Expr ty k) lret (cont : fullType ty k -> CA_simple lret) : CA_simple lret
  | CompNondet_simple k lret (cont : fullType ty k -> CA_simple lret) : CA_simple lret
  | CompSys_simple (pred: Bool @# ty) (ls: list (SysT ty)) lret (cont: CA_simple lret): CA_simple lret
  | CompReadReg_simple (r: string) (k: FullKind) (readMap : RME_simple) lret
                       (cont: fullType ty k -> CA_simple lret): CA_simple lret
  | CompRet_simple lret (e: lret @# ty) (newMap: RME_simple) : CA_simple lret
  | CompLetFull_simple k (a: CA_simple k) lret (cont: fullType ty (SyntaxKind k) ->
                                                      regMapTy -> CA_simple lret): CA_simple lret
  | CompAsyncRead_simple (idxNum num : nat) (readPort dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty)
                         (pred : Bool @# ty)
                         (k : Kind)
                         (readMap : RME_simple) lret
                         (cont : fullType ty (SyntaxKind (Array num k)) -> CA_simple lret) : CA_simple lret
  | CompSyncReadRes_simple (idxNum num : nat) (readReg dataArray : string) (Data : Kind) (isAddr : bool)
                           (readMap : RME_simple) lret
                           (cont : fullType ty (SyntaxKind (Array num Data)) -> CA_simple lret) : CA_simple lret
  | CompWrite_simple (idxNum : nat) (Data : Kind) (dataArray : string) (readMap : RME_simple) lret
                     (cont : ty (Array idxNum Data) -> CA_simple lret) : CA_simple lret
  | CompSyncReadReq_simple (idxNum num : nat) (Data : Kind) (dataArray readReg : string) (isAddr : bool)
                           (readMap : RME_simple) lret
                           (cont : ty (Array idxNum Data) -> CA_simple lret) : CA_simple lret.

  Fixpoint CA_simple_of_CA{k}(a : CompActionT ty regMapTy k) : CA_simple k :=
    match a with
    | CompCall f argRetK pred arg lret cont => CompCall_simple f argRetK pred arg (fun x => CA_simple_of_CA (cont x))
    | CompLetExpr k e lret cont => CompLetExpr_simple e (fun x => CA_simple_of_CA (cont x))
    | CompNondet k lret cont => CompNondet_simple k (fun x => CA_simple_of_CA (cont x))
    | CompSys pred ls lret cont => CompSys_simple pred ls (CA_simple_of_CA cont)
    | CompRead r k readMap lret cont => CompReadReg_simple r k (RME_simple_of_RME readMap)
                                                           (fun x => CA_simple_of_CA (cont x))
    | CompRet lret e newMap => CompRet_simple e (RME_simple_of_RME newMap)
    | CompLetFull k a lret cont => CompLetFull_simple (CA_simple_of_CA a) (fun x y => CA_simple_of_CA (cont x y))
    | CompAsyncRead idxNum num readPort dataArray idx pred k readMap lret cont =>
      CompLetFull_simple (CompRet_simple (($$WO)%kami_expr : Void @# ty)
                                         (AsyncRead idxNum num readPort dataArray idx pred k (RME_simple_of_RME readMap)))
                                         (fun _ y => CompAsyncRead_simple idxNum readPort dataArray idx pred (VarRME y)
                                                                          (fun arr => CA_simple_of_CA (cont arr)))
    | CompWrite idxNum num dataArray idx Data val mask pred writeMap readMap lret cont =>
      @CompWrite_simple idxNum Data dataArray (RME_simple_of_RME readMap) lret
                        (fun arr => 
                           CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
                                                              (@UpdRegFile idxNum num dataArray idx Data val mask pred
                                                                           (RME_simple_of_RME writeMap)
                                                                           (RME_simple_of_RME readMap) (#arr)%kami_expr))
                                              (fun _ y => CA_simple_of_CA (cont y)))
    | CompSyncReadReq idxNum num readReg dataArray idx Data isAddr pred writeMap readMap lret cont =>
      @CompSyncReadReq_simple idxNum num Data dataArray readReg isAddr (RME_simple_of_RME readMap) lret
                              (fun x => CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
                                                                           (@UpdReadReq idxNum num readReg dataArray
                                                                                        idx Data isAddr pred
                                                                                        (RME_simple_of_RME writeMap)
                                                                                        (RME_simple_of_RME readMap)
                                                                                        (#x)%kami_expr))
                                                           (fun _ y => CA_simple_of_CA (cont y)))
    | CompSyncReadRes idxNum num readReg dataArray Data isAddr readMap lret cont =>
      CompSyncReadRes_simple idxNum readReg dataArray isAddr (RME_simple_of_RME readMap)
                             (fun x => CA_simple_of_CA (cont x))
    end.

End Simple.

