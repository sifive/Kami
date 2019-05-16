Require Import Syntax StateMonad.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Notation NameVal := (string * {k: FullKind & Expr ty k})%type.
  
  Definition RegUpd := ((Bool @# ty) * NameVal)%type.
  Notation RegUpds := (list RegUpd).

  Definition RegState := (list NameVal).

  Definition RegMapTy := (RegState * RegUpds)%type.
  
  Inductive RegMapExpr: Type :=
  | VarRegMap (v: regMapTy): RegMapExpr
  | UpdRegMap (r: string) (pred: Bool @# ty) (k: FullKind) (val: Expr ty k) (regMap: RegMapExpr): RegMapExpr
  | CompactRegMap (regMap: RegMapExpr): RegMapExpr.

  Inductive CompActionT: Kind -> Type :=
  | CompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# ty)
             (arg: fst argRetK @# ty)
             lret (cont: ty (snd argRetK) -> CompActionT lret): CompActionT lret
  | CompLetExpr k (e: Expr ty k) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompNondet k lret (Cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompSys (ls: list (SysT ty)) lret (cont: CompActionT lret): CompActionT lret
  | CompRead (r: string) (k: FullKind) (readMap: RegMapExpr) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompRet lret (e: lret @# ty) (newMap: RegMapExpr): CompActionT lret
  | CompLetFull k (a: CompActionT k) lret (cont: ty k -> regMapTy -> CompActionT lret): CompActionT lret.

  Axiom cheat: forall t, t.

  Section ReadMap.
    Variable readMap: regMapTy.
    Fixpoint compileAction k (a: ActionT ty k) (pred: Bool @# ty)
             (writeMap: RegMapExpr)
             {struct a}:
      CompActionT k :=
      match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        CompCall meth k pred argExpr (fun ret => @compileAction _ (cont ret) pred writeMap)
      | Return x =>
        CompRet x writeMap
      | LetExpr k' expr cont => CompLetExpr expr (fun ret => @compileAction _ (cont ret) pred writeMap)
      | ReadNondet k' cont => CompNondet k' (fun ret => @compileAction _ (cont ret) pred writeMap)
      | Assertion pred' cont =>
        compileAction cont (pred && pred')%kami_expr writeMap
      | Sys ls cont => CompSys ls (compileAction cont pred writeMap)
      | ReadReg r k' cont =>
        @CompRead r k' (VarRegMap readMap) _ (fun v => @compileAction _ (cont v) pred writeMap)
      | WriteReg r k' expr cont =>
        let writeMap' := UpdRegMap r pred expr writeMap in
        @compileAction _ cont pred writeMap'
      | LetAction k' a' cont =>
        CompLetFull (@compileAction k' a' pred writeMap)
                    (fun retval writeMap' => @compileAction k (cont retval) pred (VarRegMap writeMap'))
      | IfElse pred' k' aT aF cont =>
        CompLetFull (@compileAction k' aT (pred && pred')%kami_expr writeMap)
                    (fun valT writesT =>
                       CompLetFull (@compileAction k' aF (pred && !pred')%kami_expr (VarRegMap writesT))
                                   (fun valF writesF =>
                                      CompLetExpr (IF pred' then #valT else #valF)%kami_expr
                                                  (fun val => (@compileAction k (cont val) pred (VarRegMap writesF)))
                    ))
      end.

    Definition compileActions (acts: list (ActionT ty Void)) :=
      fold_left (fun acc a =>
                   CompLetFull acc (fun _ writeMap => compileAction a ($$ true)%kami_expr (CompactRegMap (VarRegMap writeMap)))) acts
                (CompRet ($$ WO)%kami_expr (VarRegMap readMap)).

    Definition compileRules (rules: list RuleT) :=
      compileActions (map (fun a => snd a ty) rules).
  End ReadMap.
End Compile.

Section Semantics.
  Local Notation UpdRegsT := RegsT.

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.

  Inductive SemRegMapExpr: (RegMapExpr type RegMapType) -> RegMapType -> Prop :=
  | SemVarRegMap v:
      SemRegMapExpr (VarRegMap _ v) (fst v, snd v)
  | SemUpdRegMapTrue r (pred: Bool @# type) k val regMap
                     (PredTrue: evalExpr pred = true)
                     old upds
                     (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, (r, existT _ k (evalExpr val)) :: upds)
  | SemUpdRegMapFalse r (pred: Bool @# type) k val regMap
                      (PredTrue: evalExpr pred = false)
                      old upds
                      (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, upds)
  | SemCompactRegMap old upds regMap (HSemRegMap: SemRegMapExpr regMap (old, upds)) newMap
                     (HUpdRegs: UpdRegs (upds :: nil) old newMap):
      SemRegMapExpr (@CompactRegMap _ _ regMap) (newMap, nil).
  
  Inductive SemCompActionT: forall k, CompActionT type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: type (snd argRetK) -> CompActionT _ _ lret)
             (ret: type (snd argRetK))
             regMap calls val
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap
                     ((f, existT _ argRetK (evalExpr arg, ret)) :: calls) val
  | SemCompLetExpr k e lret cont
                   regMap calls val
                   (HSemCompActionT: SemCompActionT (cont (evalExpr e)) regMap calls val):
      SemCompActionT (@CompLetExpr _ _ k e lret cont) regMap calls val
  | SemCompNondet k lret cont
                  ret regMap calls val
                  (HSemCompActionT: SemCompActionT (cont ret) regMap calls val):
      SemCompActionT (@CompNondet _ _ k lret cont) regMap calls val
  | SemCompSys ls lret cont
               regMap calls val
               (HSemCompActionT: SemCompActionT cont regMap calls val):
      SemCompActionT (@CompSys _ _ ls lret cont) regMap calls val
  | SemCompRead r k readMap lret cont
                regMap calls val regVal
                updatedRegs
                (HUpdatedRegs: UpdRegs (snd regMap :: nil) (fst regMap) updatedRegs)
                (HIn: In (r, (existT _ k regVal)) updatedRegs)
                (HSemCompActionT: SemCompActionT (cont regVal) regMap calls val):
      SemCompActionT (@CompRead _ _ r k readMap lret cont) regMap calls val
  | SemCompRet lret e regMap regMapVal
               (HRegMap: SemRegMapExpr regMap regMapVal):
      SemCompActionT (@CompRet _ _ lret e regMap) regMapVal nil (evalExpr e)
  | SemCompLetFull k a lret cont
                   regMap_a calls_a val_a
                   (HSemCompActionT_a: SemCompActionT a regMap_a calls_a val_a)
                   regMap_cont calls_cont val_cont
                   (HSemCompActionT_cont: SemCompActionT (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCompActionT (@CompLetFull _ _ k a lret cont) regMap_cont (calls_a ++ calls_cont) val_cont.
End Semantics.

Fixpoint actions_to_rules (acts : list (Action Void)) (n : string) : list RuleT :=
  match acts with
  | nil => nil
  | a :: al => (n, a) :: actions_to_rules al (n++n)
  end.

Definition actions_to_module (o : list RegInitT) (acts : list (Action Void)) (n : string): BaseModule :=
  BaseMod o (actions_to_rules acts n) nil.

Fixpoint getMethsFullLabel (l : list FullLabel) : MethsT :=
  match l with
  | nil => nil
  | a :: a' => (snd (snd a) ++ getMethsFullLabel a')%list
 end.

Fixpoint getMeths (ll : list (list FullLabel)) :  MethsT :=
  match ll with
  | nil => nil
  | l :: lt => (getMethsFullLabel l ++ getMeths lt)%list
  end.

Fixpoint getExecsFullLabel (l : list FullLabel) : list RuleOrMeth :=
  match l with
  | nil => nil
  | l :: lt => fst (snd l) :: getExecsFullLabel lt
  end.

Fixpoint getExecs (ll : list (list FullLabel)) : list RuleOrMeth :=
  match ll with
  | nil => nil
  | l :: lt => (getExecsFullLabel l ++ getExecs lt)%list
  end.

Notation createBaseMod regs actions := (BaseMod regs (rules nil).


(*
Lemma TraceEquivOneAction k (a : ActionT type k) (o : RegsT) (newRegs: RegsT) (retl : type k):
  forall calls readRegs, 
  SemAction o a readRegs newRegs calls retl ->
  SemCompActionT (compileAction o a (Const type true) (doUpdRegs newRegs o)) (doUpdRegs newRegs o) calls retl.
Proof.
  induction a; intros; simpl.
  - inv H0.
    EqDep_subst; simpl.
    econstructor 1; eauto.
  - inv H0; EqDep_subst; simpl.
    econstructor 2; eauto.
  - inv H0; EqDep_subst; simpl.
    admit.
  - admit.
  - inv H0; EqDep_subst; simpl.
    econstructor 5; eauto.
  - inv H; EqDep_subst; simpl.
    rewrite in_map_iff in HRegVal; inv HRegVal; destruct H; inv H.
    destruct x, s0; simpl in *.
    econstructor 5; eauto.
    econstructor 7; eauto.
    simpl.
    assert (forall r ls ls', (doUpdRegs (r::nil) (doUpdRegs (r::ls) ls') = doUpdRegs (r::ls) ls')).
    {
      intros. simpl.
      admit.
    }
Admitted.
*)