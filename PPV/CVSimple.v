Require Import Kami.All.
Require Import Kami.Notations.

Section Simple.

Variable ty : Kind -> Type.
Variable regMapTy : Type.
(* 
| CompWrite (idxNum num : nat) (dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind) (val : Array num Data @# ty)
              (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RegMapExpr) lret
              (cont : regMapTy -> CompActionT lret) : CompActionT lret
  | CompSyncReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
                    (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RegMapExpr) lret
                    (cont : regMapTy -> CompActionT lret) : CompActionT lret
 
 *)

Inductive RME_simple :=
  | VarRME (v : regMapTy) : RME_simple
  | UpdReg (r : string)(pred : Bool @# ty)(k : FullKind)(val : Expr ty k)(regMap : RME_simple) : RME_simple
  | UpdRegFile (idxNum num : nat) (dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind) (val : Array num Data @# ty)
              (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RME_simple) (arr : Array idxNum Data @# ty) : RME_simple
  | UpdReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
               (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RME_simple)(arr : Array idxNum Data @# ty) : RME_simple
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
  | CompReadReg_simple (r: string) (k: FullKind) (readMap : RME_simple) lret (cont: fullType ty k -> CA_simple lret): CA_simple lret
  | CompRet_simple lret (e: lret @# ty) (newMap: RME_simple) : CA_simple lret
  | CompLetFull_simple k (a: CA_simple k) lret (cont: fullType ty (SyntaxKind k) -> regMapTy -> CA_simple lret): CA_simple lret
  | CompAsyncRead_simple (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (k : Kind) (readMap : RME_simple) lret (cont : ty k -> CA_simple lret) : CA_simple lret
  | CompSyncReadRes_simple (idxNum num : nat) (readReg dataArray : string) (Data : Kind) (isAddr : bool) (readMap : RME_simple) lret
                    (cont : fullType ty (SyntaxKind (Array num Data)) -> CA_simple lret) : CA_simple lret
  | CompWrite_simple (idxNum : nat) (Data : Kind) (dataArray : string) (readMap : RME_simple) lret (cont : ty (Array idxNum Data) -> CA_simple lret) : CA_simple lret
  | CompSyncReadReq_simple (idxNum num : nat) (Data : Kind) (dataArray readReg : string) (isAddr : bool) (readMap : RME_simple) lret
      (cont : ty (Array idxNum Data) -> CA_simple lret) : CA_simple lret.

Fixpoint CA_simple_of_CA{k}(a : CompActionT ty regMapTy k) : CA_simple k :=
  match a with
  | CompCall f argRetK pred arg lret cont => CompCall_simple f argRetK pred arg (fun x => CA_simple_of_CA (cont x))
  | CompLetExpr k e lret cont => CompLetExpr_simple e (fun x => CA_simple_of_CA (cont x))
  | CompNondet k lret cont => CompNondet_simple k (fun x => CA_simple_of_CA (cont x))
  | CompSys pred ls lret cont => CompSys_simple pred ls (CA_simple_of_CA cont)
  | CompRead r k readMap lret cont => CompReadReg_simple r k (RME_simple_of_RME readMap) (fun x => CA_simple_of_CA (cont x))
  | CompRet lret e newMap => CompRet_simple e (RME_simple_of_RME newMap)
  | CompLetFull k a lret cont => CompLetFull_simple (CA_simple_of_CA a) (fun x y => CA_simple_of_CA (cont x y))
  | CompAsyncRead idxNum num dataArray idx pred k readMap lret cont =>
      CompAsyncRead_simple idxNum num dataArray idx (RME_simple_of_RME readMap) (fun x => CA_simple_of_CA (cont x))
  | CompWrite idxNum num dataArray idx Data val mask pred writeMap readMap lret cont =>
      @CompWrite_simple idxNum Data dataArray (RME_simple_of_RME readMap) lret
      (fun arr => 
      CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
      (@UpdRegFile idxNum num dataArray idx Data val mask pred (RME_simple_of_RME writeMap) (RME_simple_of_RME readMap) (#arr)%kami_expr))
      (fun _ y => CA_simple_of_CA (cont y)))
  | CompSyncReadReq idxNum num readReg dataArray idx Data isAddr pred writeMap readMap lret cont =>
      @CompSyncReadReq_simple idxNum num Data dataArray readReg isAddr (RME_simple_of_RME readMap) lret
      (fun x => CompLetFull_simple (CompRet_simple (($$ WO)%kami_expr : Void @# ty)
      (@UpdReadReq idxNum num readReg dataArray idx Data isAddr pred (RME_simple_of_RME writeMap) (RME_simple_of_RME readMap) (#x)%kami_expr))
      (fun _ y => CA_simple_of_CA (cont y)))
  | CompSyncReadRes idxNum num readReg dataArray Data isAddr readMap lret cont =>
      CompSyncReadRes_simple idxNum readReg dataArray isAddr (RME_simple_of_RME readMap) (fun x => CA_simple_of_CA (cont x))
  end.

End Simple.

Section SemSimple.
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.
(*  
  | VarRME (v : regMapTy) : RME_simple
  | UpdReg (r : string)(pred : Bool @# ty)(k : FullKind)(val : Expr ty k)(regMap : RME_simple) : RME_simple
  | UpdRegFile (idxNum num : nat) (dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind) (val : Array num Data @# ty)
              (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RME_simple) (arr : Array idxNum Data @# ty) : RME_simple
  | UpdReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
               (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RME_simple)(arr : Array idxNum Data @# ty) : RME_simple.
  *)
  Inductive Sem_RME_simple: (RME_simple type RegMapType) -> RegMapType -> Prop :=
  | SemVarRME v:
      Sem_RME_simple (VarRME _ v) v
  | SemUpdRegTrue r (pred: Bool @# type) k val regMap
                  (HPredTrue: evalExpr pred = true)
                  old upds
                  (HSem_RME_simple : Sem_RME_simple regMap (old, upds))
                  upds'
                  (HEqual : upds' = (hd nil upds ++ ((r, existT _ k (evalExpr val)) :: nil)) :: tl upds):
      Sem_RME_simple (@UpdReg _ _ r pred k val regMap) (old, upds')
  | SemUpdRegFalse r (pred: Bool @# type) k val regMap
                   (HPredFalse: evalExpr pred = false)
                   old upds
                   (HSem_RME_simple: Sem_RME_simple regMap (old, upds)):
      Sem_RME_simple (@UpdReg _ _ r pred k val regMap) (old, upds)
  | SemUpdRegFileSome idxNum num dataArray idx Data val optMask mask pred writeMap readMap arr old upds
                      (HMask : optMask = Some mask)
                      (HUpdate : Sem_RME_simple
                                   (UpdReg dataArray pred
                                           (fold_left (fun newArr i =>
                                                         ITE
                                                           (ReadArrayConst mask i)
                                                           (UpdateArray newArr
                                                                        (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                        :: nil))
                                                                        (ReadArrayConst val i))
                                                           newArr
                                                      ) (getFins num)
                                                      arr)
                                           writeMap) (old, upds)):
                      Sem_RME_simple (@UpdRegFile _ _ idxNum num dataArray idx Data val optMask pred writeMap readMap arr) (old, upds)
  | SemUpdRegFileNone idxNum num dataArray idx Data val optMask pred writeMap readMap arr old upds
                      (HMask : optMask = None)
                      (HUpdate : Sem_RME_simple
                                   (UpdReg dataArray pred
                                              (fold_left (fun newArr i =>
                                                            (UpdateArray newArr
                                                                         (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                         :: nil))
                                                                         (ReadArrayConst val i))
                                                         ) (getFins num)
                                                         arr)
                                              writeMap) (old, upds)):
                      Sem_RME_simple (@UpdRegFile _ _ idxNum num dataArray idx Data val optMask pred writeMap readMap arr) (old, upds)
  | SemUpdReadReqTrue idxNum num readReg dataArray idx Data isAddr pred writeMap readMap arr old upds
                   (HisAddr : isAddr = true)
                   (HWriteMap : Sem_RME_simple (UpdReg readReg pred (Var type (SyntaxKind _) (evalExpr idx)) writeMap) (old, upds)):
                   Sem_RME_simple (@UpdReadReq _ _ idxNum num readReg dataArray idx Data isAddr pred writeMap readMap arr) (old, upds)
  | SemUpdReadReqFalse idxNum num readReg dataArray idx Data isAddr pred writeMap readMap arr old upds
                   (HisAddr : isAddr = false)
                   (HWriteMap : Sem_RME_simple
                                  (UpdReg readReg pred
                                             (BuildArray (fun i : Fin.t num =>
                                                            ReadArray
                                                              arr
                                                              (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                              Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                                             writeMap) (old, upds)):
      Sem_RME_simple (@UpdReadReq _ _ idxNum num readReg dataArray idx Data isAddr pred writeMap readMap arr) (old, upds)
  | SemCompactRME old upds regMap (HSemRegMap: Sem_RME_simple regMap (old, upds)):
      Sem_RME_simple (@CompactRME _ _ regMap) (old, nil::upds).
(*
  Definition WfRegMapExpr (regMapExpr : RegMapExpr type RegMapType) (regMap : RegMapType) :=
    SemRegMapExpr regMapExpr regMap /\
    let '(old, new) := regMap in
    forall u, In u new -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
  
  Inductive SemCompActionT: forall k, CompActionT type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCallTrue (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionT _ _ lret)
             (ret: fullType type (SyntaxKind (snd argRetK)))
             regMap calls val newCalls
             (HNewCalls : newCalls = (f, existT _ argRetK (evalExpr arg, ret)) :: calls)
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val)
             (HPred : evalExpr pred = true):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap newCalls val
  | SemCompCallFalse (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionT _ _ lret)
             (ret: fullType type (SyntaxKind (snd argRetK)))
             regMap calls val
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val)
             (HPred : evalExpr pred = false):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap calls val
  | SemCompLetExpr k e lret cont
                   regMap calls val
                   (HSemCompActionT: SemCompActionT (cont (evalExpr e)) regMap calls val):
      SemCompActionT (@CompLetExpr _ _ k e lret cont) regMap calls val
  | SemCompNondet k lret cont
                  ret regMap calls val
                  (HSemCompActionT: SemCompActionT (cont ret) regMap calls val):
      SemCompActionT (@CompNondet _ _ k lret cont) regMap calls val
  | SemCompSys pred ls lret cont
               regMap calls val
               (HSemCompActionT: SemCompActionT cont regMap calls val):
      SemCompActionT (@CompSys _ _ pred ls lret cont) regMap calls val
  | SemCompRead r k readMap lret cont
                regMap calls val regVal
                updatedRegs readMapValOld readMapValUpds
                (HReadMap: SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                (HUpdatedRegs: PriorityUpds readMapValOld readMapValUpds updatedRegs)
                (HIn: In (r, (existT _ k regVal)) updatedRegs)
                (HSemCompActionT: SemCompActionT (cont regVal) regMap calls val):
      SemCompActionT (@CompRead _ _ r k readMap lret cont) regMap calls val
  | SemCompRet lret e regMap regMapVal calls
               (HCallsNil : calls = nil)
               (HRegMapWf: WfRegMapExpr regMap regMapVal):
      SemCompActionT (@CompRet _ _ lret e regMap) regMapVal calls (evalExpr e)
  | SemCompLetFull k a lret cont
                   regMap_a calls_a val_a
                   (HSemCompActionT_a: SemCompActionT a regMap_a calls_a val_a)
                   regMap_cont calls_cont val_cont newCalls
                   (HNewCalls : newCalls = calls_a ++ calls_cont)
                   (HSemCompActionT_cont: SemCompActionT (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCompActionT (@CompLetFull _ _ k a lret cont) regMap_cont newCalls val_cont
  | SemCompAsyncRead num (dataArray : string) idxNum (idx : Bit (Nat.log2_up idxNum) @# type) pred Data readMap lret
                     updatedRegs readMapValOld readMapValUpds regVal regMap
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn :  In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     cont calls val contArray
                     (HContArray : contArray =
                                   BuildArray (fun i : Fin.t num =>
                                                 ReadArray
                                                   (Var type _ regVal)
                                                   (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                   Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                     (HSemCompActionT : SemCompActionT (cont (evalExpr contArray)) regMap calls val):
      SemCompActionT (@CompAsyncRead _ _  idxNum num dataArray idx pred Data readMap lret cont) regMap calls val
  | SemCompWriteSome num (dataArray : string) idxNum (idx  : Bit (Nat.log2_up idxNum) @# type) Data (array : Array num Data @# type)
                     (optMask : option (Array num Bool @# type)) (writeMap readMap : RegMapExpr type RegMapType) lret mask
                     (HMask : optMask = Some mask)
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     regMapVal pred
                     (HUpdate : WfRegMapExpr (UpdRegMap dataArray pred
                                                        (fold_left (fun newArr i =>
                                                                      ITE
                                                                        (ReadArrayConst mask i)
                                                                        (UpdateArray newArr
                                                                                     (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                     :: nil))
                                                                                     (ReadArrayConst array i))
                                                                        newArr
                                                                   ) (getFins num)
                                                                   (Var type (SyntaxKind (Array idxNum Data)) regVal))
                                                        writeMap) regMapVal)
                     cont regMap_cont calls val
                     (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompWrite _ _ idxNum num dataArray idx Data array optMask pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompWriteNone num (dataArray : string) idxNum (idx  : Bit (Nat.log2_up idxNum) @# type) Data (array : Array num Data @# type)
                     (optMask : option (Array num Bool @# type)) (writeMap readMap : RegMapExpr type RegMapType) lret
                     (HMask : optMask = None)
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     regMapVal pred
                     (HUpdate : WfRegMapExpr (UpdRegMap dataArray pred
                                                        (fold_left (fun newArr i =>
                                                                      (UpdateArray newArr
                                                                                   (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                   :: nil))
                                                                                   (ReadArrayConst array i))
                                                                   ) (getFins num)
                                                                   (Var type (SyntaxKind (Array idxNum Data)) regVal))
                                                        writeMap) regMapVal)
                     cont regMap_cont calls val
                     (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompWrite _ _ idxNum num dataArray idx Data array optMask pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReqTrue num idxNum readRegName dataArray (idx : Bit (Nat.log2_up idxNum) @# type) k (isAddr : bool)
                           (writeMap : RegMapExpr type RegMapType) readMap lret cont
                           regMapVal pred
                           (HisAddr : isAddr = true)
                           (HWriteMap : WfRegMapExpr (UpdRegMap readRegName pred (Var type (SyntaxKind _) (evalExpr idx)) writeMap) regMapVal)
                           regMap_cont calls val
                           (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompSyncReadReq _ _ idxNum num readRegName dataArray idx k isAddr pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReqFalse num idxNum readRegName dataArray (idx : Bit (Nat.log2_up idxNum) @# type) Data (isAddr : bool)
                            (writeMap : RegMapExpr type RegMapType) readMap lret cont
                            regMapVal pred
                            (HisAddr : isAddr = false)
                            updatedRegs readMapValOld readMapValUpds regV 
                            (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) updatedRegs)
                            (HWriteMap : WfRegMapExpr
                                           (UpdRegMap readRegName pred
                                                      (BuildArray (fun i : Fin.t num =>
                                                                     ReadArray
                                                                       (Var type _ regV)
                                                                       (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                                       Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil)))) writeMap) regMapVal)
                            regMap_cont calls val
                            (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompSyncReadReq _ _ idxNum num readRegName dataArray idx Data isAddr pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadResTrue num idxNum readRegName dataArray Data isAddr readMap lret cont
                           (HisAddr : isAddr = true)
                           updatedRegs readMapValOld readMapValUpds regVal idx
                           (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                           (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                           (HRegVal1 : In (readRegName, existT _ (SyntaxKind (Bit (Nat.log2_up idxNum))) idx) updatedRegs)
                           (HRegVal2 : In (dataArray, existT _ (SyntaxKind (Array idxNum Data)) regVal) updatedRegs)
                           (contArray : Expr type (SyntaxKind (Array num Data)))
                           (HContArray : contArray =
                                         BuildArray (fun i : Fin.t num =>
                                                       ReadArray
                                                         (Var type _ regVal)
                                                         (CABit Add (Var type (SyntaxKind _) idx ::
                                                                         Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                           regMap calls val
                           (HSemCompActionT : SemCompActionT (cont (evalExpr contArray)) regMap calls val):
      SemCompActionT (@CompSyncReadRes _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val
  | SemCompSyncReadResFalse num idxNum readRegName dataArray Data isAddr readMap lret cont
                            (HisAddr : isAddr = false)
                            updatedRegs readMapValOld readMapValUpds regVal
                            (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HIn1 : In (readRegName, (existT _ (SyntaxKind (Array num Data)) regVal)) updatedRegs)
                            regMap calls val
                            (HSemCompActionT : SemCompActionT (cont regVal) regMap calls val):
      SemCompActionT (@CompSyncReadRes _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val.

  Variable (k : Kind) (a : CompActionT type RegMapType k) (regInits : list RegInitT).
  
  Inductive SemCompTrace: RegsT -> list UpdRegsT -> list MethsT -> Prop :=
  | SemCompTraceInit (oInit : RegsT) (lupds : list UpdRegsT) (lcalls : list MethsT)
                     (HNoUpds : lupds = nil) (HNoCalls : lcalls = nil)
                     (HInitRegs : Forall2 regInit oInit regInits) :
      SemCompTrace oInit lupds lcalls
  | SemCompTraceCont (o o' : RegsT) (lupds lupds' : list UpdRegsT) (upds : UpdRegsT)
                     (lcalls lcalls' : list MethsT) (calls : MethsT) val
                     (HOldTrace : SemCompTrace o lupds lcalls)
                     (HSemAction : SemCompActionT a (o, upds) calls val)
                     (HNewUpds : lupds' = upds :: lupds)
                     (HNewCalls : lcalls' = calls :: lcalls)
                     (HPriorityUpds : PriorityUpds o upds o') :
      SemCompTrace o' lupds' lcalls'.
*)
End SemSimple.