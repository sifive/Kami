Require Import Kami.All Kami.Compiler.Compiler.
Require Import Kami.Notations.
Require Import Kami.Compiler.CompilerSimple.

Section SemSimple.
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.
  
  Inductive Sem_RmeSimple: (RmeSimple type RegMapType) -> RegMapType -> Prop :=
  | SemVarRME v:
      Sem_RmeSimple (VarRME _ v) v
  | SemUpdRegRMETrue r (pred: Bool @# type) k val regMap
                  (HPredTrue: evalExpr pred = true)
                  old upds
                  (HSem_RmeSimple : Sem_RmeSimple regMap (old, upds))
                  upds'
                  (HEqual : upds' = (hd nil upds ++ ((r, existT _ k (evalExpr val)) :: nil)) :: tl upds):
      Sem_RmeSimple (@UpdRegRME _ _ r pred k val regMap) (old, upds')
  | SemUpdRegRMEFalse r (pred: Bool @# type) k val regMap
                   (HPredFalse: evalExpr pred = false)
                   old upds
                   (HSem_RmeSimple: Sem_RmeSimple regMap (old, upds)):
      Sem_RmeSimple (@UpdRegRME _ _ r pred k val regMap) (old, upds)
  | SemWriteRMESome idxNum num writePort dataArray idx Data val optMask mask pred writeMap readMap arr old upds
                      (HMask : optMask = Some mask)
                      (HUpdate : Sem_RmeSimple
                                   (UpdRegRME dataArray pred
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
                      Sem_RmeSimple (@WriteRME _ _ idxNum num writePort dataArray idx Data val optMask pred writeMap readMap arr) (old, upds)
  | SemWriteRMENone idxNum num writePort dataArray idx Data val optMask pred writeMap readMap arr old upds
                      (HMask : optMask = None)
                      (HUpdate : Sem_RmeSimple
                                   (UpdRegRME dataArray pred
                                              (fold_left (fun newArr i =>
                                                            (UpdateArray newArr
                                                                         (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                         :: nil))
                                                                         (ReadArrayConst val i))
                                                         ) (getFins num)
                                                         arr)
                                              writeMap) (old, upds)):
                      Sem_RmeSimple (@WriteRME _ _ idxNum num writePort dataArray idx Data val optMask pred writeMap readMap arr) (old, upds)
  | SemReadReqRMETrue idxNum num readReq readReg dataArray idx Data isAddr pred writeMap readMap arr old upds
                   (HisAddr : isAddr = true)
                   (HWriteMap : Sem_RmeSimple (UpdRegRME readReg pred (Var type (SyntaxKind _) (evalExpr idx)) writeMap) (old, upds)):
                   Sem_RmeSimple (@ReadReqRME _ _ idxNum num readReq readReg dataArray idx Data isAddr pred writeMap readMap arr) (old, upds)
  | SemReadReqRMEFalse idxNum num readReq readReg dataArray idx Data isAddr pred writeMap readMap arr old upds
                   (HisAddr : isAddr = false)
                   (HWriteMap : Sem_RmeSimple
                                  (UpdRegRME readReg pred
                                             (BuildArray (fun i : Fin num =>
                                                            ReadArray
                                                              arr
                                                              (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                              Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                                             writeMap) (old, upds)):
      Sem_RmeSimple (@ReadReqRME _ _ idxNum num readReq readReg dataArray idx Data isAddr pred writeMap readMap arr) (old, upds)
  | SemReadRespRME idxNum num readResp readReg dataArray writePort isWriteMask Data isAddr writeMap readMap old upds
                       (HWriteMap : Sem_RmeSimple writeMap (old, upds)):
      Sem_RmeSimple (@ReadRespRME _ _ idxNum num readResp readReg dataArray writePort isWriteMask Data isAddr writeMap readMap) (old, upds)
  | SemAsyncReadRME (idxNum num : nat) (readPort dataArray : string) writePort isWriteMask (idx : Bit (Nat.log2_up idxNum) @# type) (pred : Bool @# type) (k : Kind) (writeMap readMap : RmeSimple type RegMapType)
                 old upds (HNoOp : Sem_RmeSimple writeMap (old, upds)):
      Sem_RmeSimple (@AsyncReadRME _ _ idxNum num readPort dataArray writePort isWriteMask idx pred k writeMap readMap) (old, upds)
  | SemCompactRME old upds regMap (HSemRegMap: Sem_RmeSimple regMap (old, upds)):
      Sem_RmeSimple (@CompactRME _ _ regMap) (old, nil::upds).

  Definition WfRmeSimple (regMapExpr : RmeSimple type RegMapType) (regMap : RegMapType) :=
    Sem_RmeSimple regMapExpr regMap /\
    let '(old, new) := regMap in
    forall u, In u new -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
  
  Inductive SemCompActionSimple: forall k, CompActionSimple type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCall_simple_True (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
                            (arg: fst argRetK @# type)
                            lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionSimple _ _ lret)
                            (ret: fullType type (SyntaxKind (snd argRetK)))
                            regMap calls val newCalls
                            (HNewCalls : newCalls = (f, existT _ argRetK (evalExpr arg, ret)) :: calls)
                            (HSemCompActionSimple: SemCompActionSimple (cont ret) regMap calls val)
                            (HPred : evalExpr pred = true):
      SemCompActionSimple (@CompCall_simple _ _ f argRetK pred arg lret cont) regMap newCalls val
  | SemCompCall_simple_False (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
                             (arg: fst argRetK @# type)
                             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionSimple _ _ lret)
                             (ret: fullType type (SyntaxKind (snd argRetK)))
                             regMap calls val
                             (HSemCompActionSimple: SemCompActionSimple (cont ret) regMap calls val)
                             (HPred : evalExpr pred = false):
      SemCompActionSimple (@CompCall_simple _ _ f argRetK pred arg lret cont) regMap calls val
  | SemCompLetExpr_simple k e lret cont
                          regMap calls val
                          (HSemCompActionSimple: SemCompActionSimple (cont (evalExpr e)) regMap calls val):
      SemCompActionSimple (@CompLetExpr_simple _ _ k e lret cont) regMap calls val
  | SemCompNondet_simple k lret cont
                         ret regMap calls val
                         (HSemCompActionSimple: SemCompActionSimple (cont ret) regMap calls val):
      SemCompActionSimple (@CompNondet_simple _ _ k lret cont) regMap calls val
  | SemCompSys_simple pred ls lret cont
               regMap calls val
               (HSemCompActionSimple: SemCompActionSimple cont regMap calls val):
      SemCompActionSimple (@CompSys_simple _ _ pred ls lret cont) regMap calls val
  | SemCompReadReg_simple r k readMap lret cont
                          regMap calls val regVal
                          updatedRegs readMapValOld readMapValUpds
                          (HReadMap: Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                          (HUpdatedRegs: PriorityUpds readMapValOld readMapValUpds updatedRegs)
                          (HIn: In (r, (existT _ k regVal)) updatedRegs)
                          (HSemCompActionT: SemCompActionSimple (cont regVal) regMap calls val):
      SemCompActionSimple (@CompReadReg_simple _ _ r k readMap lret cont) regMap calls val
  | SemCompRet_simple lret e regMap regMapVal calls
                      (HCallsNil : calls = nil)
                      (HRegMapWf: WfRmeSimple regMap regMapVal):
      SemCompActionSimple (@CompRet_simple _ _ lret e regMap) regMapVal calls (evalExpr e)
  | SemCompLetFull_simple k a lret cont
                          regMap_a calls_a val_a
                          (HSemCompActionSimple_a: SemCompActionSimple a regMap_a calls_a val_a)
                          regMap_cont calls_cont val_cont newCalls
                          (HNewCalls : newCalls = calls_a ++ calls_cont)
                          (HSemCompActionSimple_cont: SemCompActionSimple (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCompActionSimple (@CompLetFull_simple _ _ k a lret cont) regMap_cont newCalls val_cont
  | SemCompAsyncReadRmeSimple num (readPort dataArray : string) writePort isWriteMask idxNum (idx : Bit (Nat.log2_up idxNum) @# type) pred Data readMap lret
                            updatedRegs readMapValOld readMapValUpds regVal regMap
                            (HReadMap : Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HIn :  In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                            cont calls val contArray
                            (HContArray : contArray =
                                          BuildArray (fun i : Fin num =>
                                                        ReadArray
                                                          (Var type _ regVal)
                                                          (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                          Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                            (HSemCompActionSimple : SemCompActionSimple (cont (evalExpr contArray)) regMap calls val):
      SemCompActionSimple (@CompAsyncRead_simple _ _ idxNum num readPort dataArray writePort isWriteMask idx pred Data readMap lret cont) regMap calls val
  | SemCompWrite_simple (writePort dataArray : string) idxNum Data (readMap : RmeSimple type RegMapType) lret
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     cont regMap_cont calls val
                     (HSemCompActionSimple : SemCompActionSimple (cont regVal) regMap_cont calls val):
      SemCompActionSimple (@CompWrite_simple _ _ idxNum Data writePort dataArray readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReq_simple_True num idxNum readReq readReg dataArray k (isAddr : bool) readMap lret cont
                                   regMapVal
                                   (HisAddr : isAddr = true)
                                   regMap_cont calls val
                                   (HSemCompActionSimple : SemCompActionSimple (cont regMapVal) regMap_cont calls val):
      SemCompActionSimple (@CompSyncReadReq_simple _ _ idxNum num k readReq readReg dataArray isAddr readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReq_simple_False num idxNum readReq readReg dataArray (idx : Bit (Nat.log2_up idxNum) @# type) Data (isAddr : bool)
                                    (writeMap : RegMapExpr type RegMapType) readMap lret cont
                                    (HisAddr : isAddr = false)
                                    updatedRegs readMapValOld readMapValUpds regV 
                                    (HReadMap : Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                                    (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                                    (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) updatedRegs)
                                    regMap_cont calls val
                                    (HSemCompActionSimple : SemCompActionSimple (cont regV) regMap_cont calls val):
      SemCompActionSimple (@CompSyncReadReq_simple _ _ idxNum num Data readReq readReg dataArray isAddr readMap lret cont) regMap_cont calls val
  | SemCompSyncReadRes_simple_True num idxNum readResp readRegName dataArray writePort isWriteMask Data isAddr readMap lret cont
                                   (HisAddr : isAddr = true)
                                   updatedRegs readMapValOld readMapValUpds regVal idx
                                   (HReadMap : Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                                   (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                                   (HRegVal1 : In (readRegName, existT _ (SyntaxKind (Bit (Nat.log2_up idxNum))) idx) updatedRegs)
                                   (HRegVal2 : In (dataArray, existT _ (SyntaxKind (Array idxNum Data)) regVal) updatedRegs)
                                   (contArray : Expr type (SyntaxKind (Array num Data)))
                                   (HContArray : contArray =
                                                 BuildArray (fun i : Fin num =>
                                                               ReadArray
                                                                 (Var type _ regVal)
                                                                 (CABit Add (Var type (SyntaxKind _) idx ::
                                                                                 Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                                   regMap calls val
                                   (HSemCompActionSimple : SemCompActionSimple (cont (evalExpr contArray)) regMap calls val):
      SemCompActionSimple (@CompSyncReadRes_simple _ _ idxNum num readResp readRegName dataArray writePort isWriteMask Data isAddr readMap lret cont) regMap calls val
  | SemCompSyncReadRes_simple_False num idxNum readResp readRegName dataArray writePort isWriteMask Data isAddr readMap lret cont
                                    (HisAddr : isAddr = false)
                                    updatedRegs readMapValOld readMapValUpds regVal
                                    (HReadMap : Sem_RmeSimple readMap (readMapValOld, readMapValUpds))
                                    (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                                    (HIn1 : In (readRegName, (existT _ (SyntaxKind (Array num Data)) regVal)) updatedRegs)
                                    regMap calls val
                                    (HSemCompActionSimple : SemCompActionSimple (cont regVal) regMap calls val):
      SemCompActionSimple (@CompSyncReadRes_simple _ _ idxNum num readResp readRegName dataArray writePort isWriteMask Data isAddr readMap lret cont) regMap calls val.
  Variable (k : Kind) (a : CompActionSimple type RegMapType k) (regInits : list RegInitT).
  

  Section Loop.
    Variable f: RegsT -> CompActionSimple type RegMapType Void.

    Inductive SemCompActionSimple_Trace: RegsT -> list UpdRegsT -> list MethsT -> Prop :=
    | SemCompActionSimple_TraceInit (oInit : RegsT) (lupds : list UpdRegsT) (lcalls : list MethsT)
                             (HNoUpds : lupds = nil) (HNoCalls : lcalls = nil)
                             (HInitRegs : Forall2 regInit oInit regInits) :
        SemCompActionSimple_Trace oInit lupds lcalls
    | SemCompActionSimple_TraceCont (o o' : RegsT) (lupds lupds' : list UpdRegsT) (upds : UpdRegsT)
                             (lcalls lcalls' : list MethsT) (calls : MethsT) val
                             (HOldTrace : SemCompActionSimple_Trace o lupds lcalls)
                             (HSemAction : SemCompActionSimple (f o) (o, upds) calls val)
                             (HNewUpds : lupds' = upds :: lupds)
                             (HNewCalls : lcalls' = calls :: lcalls)
                             (HPriorityUpds : PriorityUpds o upds o') :
        SemCompActionSimple_Trace o' lupds' lcalls'.
  End Loop.
End SemSimple.
