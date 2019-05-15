Require Import Syntax StateMonad.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope string.

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Inductive CompActionT: Kind -> Type :=
  | CompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# ty)
             (arg: fst argRetK @# ty)
             lret (cont: ty (snd argRetK) -> CompActionT lret): CompActionT lret
  | CompLetExpr k (e: Expr ty k) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompNondet k lret (Cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompSys (ls: list (SysT ty)) lret (cont: CompActionT lret): CompActionT lret
  | CompRead (r: string) (k: FullKind) (readMap: regMapTy) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompUpd (r: string) (k: FullKind) (v: Expr ty k) (writeMap: regMapTy) lret (cont: regMapTy -> CompActionT lret): CompActionT lret
  | CompRet lret (e: lret @# ty) (newMap: regMapTy): CompActionT lret
  | CompLetFull k (a: CompActionT k) lret (cont: ty k -> regMapTy -> CompActionT lret): CompActionT lret.

  Axiom cheat: forall t, t.

  Section ReadMap.
    Variable readMap: regMapTy.
    Fixpoint compileAction k (a: ActionT ty k) (pred: Bool @# ty)
             (writeMap: regMapTy)
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
        @CompRead r k' readMap _ (fun v => @compileAction _ (cont v) pred writeMap)
      | WriteReg r k' expr cont =>
        @CompRead r k' readMap _
                  (fun v => CompUpd r (IF pred then expr else (Var ty k' v))%kami_expr writeMap
                                    (fun writeMap' => @compileAction _ cont pred writeMap'))
      | LetAction k' a' cont =>
        CompLetFull (@compileAction k' a' pred writeMap)
                    (fun retval writeMap' => @compileAction k (cont retval) pred writeMap')
      | IfElse pred' k' aT aF cont =>
        CompLetFull (@compileAction k' aT (pred && pred')%kami_expr writeMap)
                    (fun valT writesT =>
                       CompLetFull (@compileAction k' aF (pred && !pred')%kami_expr writesT)
                                   (fun valF writesF =>
                                      CompLetExpr (IF pred' then #valT else #valF)%kami_expr
                                                  (fun val => (@compileAction k (cont val) pred writesF))
                    ))
      end.

    Definition compileActions (acts: list (ActionT ty Void)) :=
      fold_left (fun acc a =>
                   CompLetFull acc
                   (fun _ writeMap => compileAction a ($$ true)%kami_expr writeMap)) acts (CompRet ($$ WO)%kami_expr readMap).
  End ReadMap.
End Compile.

Section Semantics.
  Variable readMap: RegsT.
  Inductive SemCompActionT: forall k, CompActionT type RegsT k -> RegsT -> MethsT -> type k -> Prop :=
  | SemCompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: type (snd argRetK) -> CompActionT type RegsT lret)
             (ret: type (snd argRetK))
             writeMap calls val
             (sem_a: SemCompActionT (cont ret) writeMap calls val)
    : SemCompActionT (@CompCall type RegsT f argRetK pred arg lret cont) writeMap ((f, existT _ argRetK (evalExpr arg, ret)) :: calls) val
  | SemCompLetExpr k (e: Expr type k) lret (cont: fullType type k -> CompActionT type RegsT lret)
                   writeMap calls val
                   (sem_a: SemCompActionT (cont (evalExpr e)) writeMap calls val)
    : SemCompActionT (@CompLetExpr type RegsT k e lret cont) writeMap calls val
  | SemCompNondet k (v: fullType type k) lret (cont: fullType type k -> CompActionT type RegsT lret)
                   writeMap calls val
                   (sem_a: SemCompActionT (cont v) writeMap calls val)
    : SemCompActionT (@CompNondet type RegsT k lret cont) writeMap calls val
  | SemCompSys (ls: list (SysT type)) lret (cont: CompActionT type RegsT lret)
               writeMap calls val
               (sem_a: SemCompActionT cont writeMap calls val)
    : SemCompActionT (CompSys ls cont) writeMap calls val
  | SemCompRead (r: string) k (readMap: RegsT) lret (cont: fullType type k -> CompActionT type RegsT lret)
                regV (HIn: In (r, existT _ k regV) readMap)
                writeMap calls val
                (sem_a: SemCompActionT (cont regV) writeMap calls val)
    : SemCompActionT (@CompRead type RegsT r k readMap lret cont) writeMap calls val
  | SemCompRet lret (e: lret @# type) (newMap: RegsT)
    : SemCompActionT (@CompRet type RegsT lret e newMap) newMap nil (evalExpr e)
  | SemCompUpd (r: string) k (v: Expr type k) (writeMap: RegsT) lret (cont: RegsT -> CompActionT type RegsT lret)
               writeMap calls val writeMap'
               (sem_a: SemCompActionT (cont (doUpdRegs ((r, existT _ k (evalExpr v)) :: nil) writeMap)) writeMap' calls val)
    : SemCompActionT (@CompUpd type RegsT r k v writeMap lret cont) writeMap' calls val
  | SemCompLetFull k (a: CompActionT type RegsT k) lret (cont: type k -> RegsT -> CompActionT type RegsT lret)
                   writeMapA callsA valA
                   (sem_a: SemCompActionT a writeMapA callsA valA)
                   writeMapCont callsCont valCont
                   (sem_cont: SemCompActionT (cont valA writeMapA) writeMapCont callsCont valCont)
    : SemCompActionT (@CompLetFull type RegsT k a lret cont) writeMapCont callsCont valCont.
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
