Require Import Kami.All.
Require Import Kami.Notations.
Require Import Kami.PPV.CVSimple.

Section SemSimple.
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.
  
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

  Definition WfRME_simple (regMapExpr : RME_simple type RegMapType) (regMap : RegMapType) :=
    Sem_RME_simple regMapExpr regMap /\
    let '(old, new) := regMap in
    forall u, In u new -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
  
  Inductive SemCA_simple: forall k, CA_simple type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCall_simple_True (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
                            (arg: fst argRetK @# type)
                            lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CA_simple _ _ lret)
                            (ret: fullType type (SyntaxKind (snd argRetK)))
                            regMap calls val newCalls
                            (HNewCalls : newCalls = (f, existT _ argRetK (evalExpr arg, ret)) :: calls)
                            (HSemCA_simple: SemCA_simple (cont ret) regMap calls val)
                            (HPred : evalExpr pred = true):
      SemCA_simple (@CompCall_simple _ _ f argRetK pred arg lret cont) regMap newCalls val
  | SemCompCall_simple_False (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
                             (arg: fst argRetK @# type)
                             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CA_simple _ _ lret)
                             (ret: fullType type (SyntaxKind (snd argRetK)))
                             regMap calls val
                             (HSemCA_simple: SemCA_simple (cont ret) regMap calls val)
                             (HPred : evalExpr pred = false):
      SemCA_simple (@CompCall_simple _ _ f argRetK pred arg lret cont) regMap calls val
  | SemCompLetExpr_simple k e lret cont
                          regMap calls val
                          (HSemCA_simple: SemCA_simple (cont (evalExpr e)) regMap calls val):
      SemCA_simple (@CompLetExpr_simple _ _ k e lret cont) regMap calls val
  | SemCompNondet_simple k lret cont
                         ret regMap calls val
                         (HSemCA_simple: SemCA_simple (cont ret) regMap calls val):
      SemCA_simple (@CompNondet_simple _ _ k lret cont) regMap calls val
  | SemCompSys_simple pred ls lret cont
               regMap calls val
               (HSemCA_simple: SemCA_simple cont regMap calls val):
      SemCA_simple (@CompSys_simple _ _ pred ls lret cont) regMap calls val
  | SemCompReadReg_simple r k readMap lret cont
                          regMap calls val regVal
                          updatedRegs readMapValOld readMapValUpds
                          (HReadMap: Sem_RME_simple readMap (readMapValOld, readMapValUpds))
                          (HUpdatedRegs: PriorityUpds readMapValOld readMapValUpds updatedRegs)
                          (HIn: In (r, (existT _ k regVal)) updatedRegs)
                          (HSemCompActionT: SemCA_simple (cont regVal) regMap calls val):
      SemCA_simple (@CompReadReg_simple _ _ r k readMap lret cont) regMap calls val
  | SemCompRet_simple lret e regMap regMapVal calls
                      (HCallsNil : calls = nil)
                      (HRegMapWf: WfRME_simple regMap regMapVal):
      SemCA_simple (@CompRet_simple _ _ lret e regMap) regMapVal calls (evalExpr e)
  | SemCompLetFull_simple k a lret cont
                          regMap_a calls_a val_a
                          (HSemCA_simple_a: SemCA_simple a regMap_a calls_a val_a)
                          regMap_cont calls_cont val_cont newCalls
                          (HNewCalls : newCalls = calls_a ++ calls_cont)
                          (HSemCA_simple_cont: SemCA_simple (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCA_simple (@CompLetFull_simple _ _ k a lret cont) regMap_cont newCalls val_cont
  | SemCompAsyncRead_simple num (dataArray : string) idxNum (idx : Bit (Nat.log2_up idxNum) @# type) Data readMap lret
                            updatedRegs readMapValOld readMapValUpds regVal regMap
                            (HReadMap : Sem_RME_simple readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HIn :  In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                            cont calls val contArray
                            (HContArray : contArray =
                                          BuildArray (fun i : Fin.t num =>
                                                        ReadArray
                                                          (Var type _ regVal)
                                                          (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                          Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                            (HSemCA_simple : SemCA_simple (cont (evalExpr contArray)) regMap calls val):
      SemCA_simple (@CompAsyncRead_simple _ _ idxNum num dataArray idx Data readMap lret cont) regMap calls val
  | SemCompWrite_simple (dataArray : string) idxNum Data (readMap : RME_simple type RegMapType) lret
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : Sem_RME_simple readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     cont regMap_cont calls val
                     (HSemCA_simple : SemCA_simple (cont regVal) regMap_cont calls val):
      SemCA_simple (@CompWrite_simple _ _ idxNum Data dataArray readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReq_simple_True num idxNum readReg dataArray k (isAddr : bool) readMap lret cont
                                   regMapVal
                                   (HisAddr : isAddr = true)
                                   regMap_cont calls val
                                   (HSemCA_simple : SemCA_simple (cont regMapVal) regMap_cont calls val):
      SemCA_simple (@CompSyncReadReq_simple _ _ idxNum num k dataArray readReg isAddr readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReq_simple_False num idxNum readReg dataArray (idx : Bit (Nat.log2_up idxNum) @# type) Data (isAddr : bool)
                                    (writeMap : RegMapExpr type RegMapType) readMap lret cont
                                    (HisAddr : isAddr = false)
                                    updatedRegs readMapValOld readMapValUpds regV 
                                    (HReadMap : Sem_RME_simple readMap (readMapValOld, readMapValUpds))
                                    (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                                    (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) updatedRegs)
                                    regMap_cont calls val
                                    (HSemCA_simple : SemCA_simple (cont regV) regMap_cont calls val):
      SemCA_simple (@CompSyncReadReq_simple _ _ idxNum num Data dataArray readReg isAddr readMap lret cont) regMap_cont calls val
  | SemCompSyncReadRes_simple_True num idxNum readRegName dataArray Data isAddr readMap lret cont
                                   (HisAddr : isAddr = true)
                                   updatedRegs readMapValOld readMapValUpds regVal idx
                                   (HReadMap : Sem_RME_simple readMap (readMapValOld, readMapValUpds))
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
                                   (HSemCA_simple : SemCA_simple (cont (evalExpr contArray)) regMap calls val):
      SemCA_simple (@CompSyncReadRes_simple _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val
  | SemCompSyncReadRes_simple_False num idxNum readRegName dataArray Data isAddr readMap lret cont
                                    (HisAddr : isAddr = false)
                                    updatedRegs readMapValOld readMapValUpds regVal
                                    (HReadMap : Sem_RME_simple readMap (readMapValOld, readMapValUpds))
                                    (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                                    (HIn1 : In (readRegName, (existT _ (SyntaxKind (Array num Data)) regVal)) updatedRegs)
                                    regMap calls val
                                    (HSemCA_simple : SemCA_simple (cont regVal) regMap calls val):
      SemCA_simple (@CompSyncReadRes_simple _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val.

End SemSimple.
