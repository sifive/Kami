Require Import Syntax StateMonad Properties All.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Notation NameVal := (string * {k: FullKind & Expr ty k})%type.
  
  Inductive RegMapExpr: Type :=
  | VarRegMap (v: regMapTy): RegMapExpr
  | UpdRegMap (r: string) (pred: Bool @# ty) (k: FullKind) (val: Expr ty k)
              (regMap: RegMapExpr): RegMapExpr
  | CompactRegMap (regMap: RegMapExpr): RegMapExpr.

  Inductive CompActionT: Kind -> Type :=
  | CompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# ty)
             (arg: fst argRetK @# ty)
             lret (cont: ty (snd argRetK) -> CompActionT lret): CompActionT lret
  | CompLetExpr k (e: Expr ty k) lret (cont: fullType ty k -> CompActionT lret):
      CompActionT lret
  | CompNondet k lret (Cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompSys (ls: list (SysT ty)) lret (cont: CompActionT lret): CompActionT lret
  | CompRead (r: string) (k: FullKind) (readMap: RegMapExpr) lret
             (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompRet lret (e: lret @# ty) (newMap: RegMapExpr): CompActionT lret
  | CompLetFull k (a: CompActionT k) lret
                (cont: ty k -> regMapTy -> CompActionT lret): CompActionT lret.

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
      | Sys ls cont => CompSys ls (compileAction cont pred writeMap)
      | ReadReg r k' cont =>
        @CompRead r k' (VarRegMap readMap) _ (fun v => @compileAction _ (cont v) pred writeMap)
      | WriteReg r k' expr cont =>
        CompLetFull (CompRet ($$ WO)%kami_expr
                             (UpdRegMap r pred expr writeMap)) (fun _ v => @compileAction _ cont pred (VarRegMap v))
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
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.

  Section PriorityUpds.
    Variable o: RegsT.
    Inductive PriorityUpds: UpdRegsT -> RegsT -> Prop :=
    | NoUpds: PriorityUpds nil o
    | ConsUpds (upds: UpdRegsT) (prevUpds: UpdRegsT) (prevRegs: RegsT)
               (prevCorrect: PriorityUpds prevUpds prevRegs)
               (u: UpdRegT)
               (curr: RegsT)
               (currRegsTCurr: getKindAttr o = getKindAttr curr)
               (Hcurr: forall s v, In (s, v) curr -> In (s, v) u \/ ((~ In s (map fst u)) /\ In (s, v) prevRegs))
               fullU
               (HFullU: fullU = u :: prevUpds):
        PriorityUpds fullU curr.

    Lemma prevPrevRegsTrue u prevUpds curr (currPriority: PriorityUpds (u :: prevUpds) curr):
      forall prev, PriorityUpds prevUpds prev -> getKindAttr o = getKindAttr prev.
    Proof.
      induction currPriority; simpl; auto; intros.
      inversion H; auto.
    Qed.
  End PriorityUpds.
    
  Inductive SemRegMapExpr: (RegMapExpr type RegMapType) -> RegMapType -> Prop :=
  | SemVarRegMap v:
      SemRegMapExpr (VarRegMap _ v) v
  | SemUpdRegMapTrue r (pred: Bool @# type) k val regMap
                     (PredTrue: evalExpr pred = true)
                     old upds
                     (HSemRegMap: SemRegMapExpr regMap (old, upds))
                     upds'
                     (HEqual : upds' = (hd nil upds ++ ((r, existT _ k (evalExpr val)) :: nil)) :: tl upds):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, upds')
  | SemUpdRegMapFalse r (pred: Bool @# type) k val regMap
                      (PredTrue: evalExpr pred = false)
                      old upds
                      (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, upds)
  | SemCompactRegMap old upds regMap (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@CompactRegMap _ _ regMap) (old, nil::upds).

  Definition WfRegMapExpr (regMapExpr : RegMapExpr type RegMapType) (regMap : RegMapType) :=
    SemRegMapExpr regMapExpr regMap /\
    let '(old, new) := regMap in
    forall u, In u new -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
  
  Inductive SemCompActionT: forall k, CompActionT type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCallTrue (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: type (snd argRetK) -> CompActionT _ _ lret)
             (ret: type (snd argRetK))
             regMap calls val
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val)
             (HPred : evalExpr pred = true):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap
                     ((f, existT _ argRetK (evalExpr arg, ret)) :: calls) val
  | SemCompCallFalse (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: type (snd argRetK) -> CompActionT _ _ lret)
             (ret: type (snd argRetK))
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
  | SemCompSys ls lret cont
               regMap calls val
               (HSemCompActionT: SemCompActionT cont regMap calls val):
      SemCompActionT (@CompSys _ _ ls lret cont) regMap calls val
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
               (HRegMapWf: WfRegMapExpr regMap regMapVal) :
      SemCompActionT (@CompRet _ _ lret e regMap) regMapVal calls (evalExpr e)
  | SemCompLetFull k a lret cont
                   regMap_a calls_a val_a
                   (HSemCompActionT_a: SemCompActionT a regMap_a calls_a val_a)
                   regMap_cont calls_cont val_cont
                   (HSemCompActionT_cont: SemCompActionT (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCompActionT (@CompLetFull _ _ k a lret cont) regMap_cont (calls_a ++ calls_cont) val_cont.
End Semantics.

Lemma getKindAttr_fst {A B : Type} {P : B -> Type}  {Q : B -> Type} (l1 : list (A * {x : B & P x})):
  forall  (l2 : list (A * {x : B & Q x})),
    getKindAttr l1 = getKindAttr l2 ->
    (map fst l1) = (map fst l2).
Proof.
  induction l1, l2; intros; auto; simpl in *; inv H.
  erewrite IHl1; eauto.
Qed.

Lemma SemRegExprVals expr :
  forall o1 o2,
  SemRegMapExpr expr o1 ->
  SemRegMapExpr expr o2 ->
  o1 = o2.
Proof.
  induction expr; intros; inv H; inv H0; EqDep_subst; auto;
    try congruence; specialize (IHexpr _ _ HSemRegMap HSemRegMap0); inv IHexpr; auto.
Qed.

Lemma SemCompActionEquivBexpr (k : Kind) (a : ActionT type k):
  forall o calls retl expr v' (bexpr1 bexpr2 : Bool @# type),
    evalExpr bexpr1  = evalExpr bexpr2  ->
    SemCompActionT (compileAction o a bexpr1 expr) v' calls retl ->
    SemCompActionT (compileAction o a bexpr2 expr) v' calls retl.
Proof.
  induction a; intros; simpl in *; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    assert (val_a = evalExpr (Const type WO)) as TMP.
    {rewrite (shatter_word_0 val_a); auto. }
    econstructor; eauto.
    rewrite TMP in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    econstructor; eauto.
    inv HRegMapWf; destruct regMap_a.
    split; auto.
    destruct (bool_dec (evalExpr bexpr2) true).
    inv H0; EqDep_subst.
    + econstructor 2; eauto.
    + congruence.
    + inv H0; EqDep_subst.
      * congruence.
      * econstructor 3; eauto.
  - inv H1; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H5; subst; simpl in *.
    econstructor.
    + eapply IHa1 with (bexpr1 := (bexpr1 && e)%kami_expr); eauto.
      simpl; rewrite H0; auto.
    + econstructor.
      * eapply IHa2 with (bexpr1 := (bexpr1 && !e)%kami_expr);eauto.
        simpl; rewrite H0; auto.
      * econstructor; simpl.
        eapply H; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
Qed.

Lemma predFalse_UpdsNil k a:
  forall (bexpr: Bool @# type) old regMap1 regMap2 calls val (HNbexpr : evalExpr bexpr = false) rexpr (HRegMap : SemRegMapExpr rexpr regMap1),
    @SemCompActionT k (compileAction (old, nil) a bexpr rexpr) regMap2 calls val ->
    regMap1 = regMap2 /\ calls = nil.
Proof.
  induction a; intros.
  - inv H0; EqDep_subst;[congruence|eauto].
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
    specialize (IHa _ _ _ _ _ _ HNbexpr _ HRegMap HSemCompActionT_a); dest.
    rewrite H0 in HRegMap.
    assert (SemRegMapExpr (VarRegMap type regMap_a) regMap_a);[constructor|].
    specialize (H _ _ _ _ _ _ _ HNbexpr _ H2 HSemCompActionT_cont); dest.
    split; subst; auto.
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
  - inv H; simpl in *; EqDep_subst; eauto.
    assert (val_a = evalExpr (Const type WO)) as TMP.
    {rewrite (shatter_word_0 val_a); auto. }
    rewrite TMP in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    inv HRegMapWf; inv H; EqDep_subst;[congruence|].
    assert (SemRegMapExpr (VarRegMap type (old0, upds)) (old0, upds));[constructor|].
    specialize (IHa _ _ _ _ _ _ HNbexpr _ H HSemCompActionT_cont); dest.
    rewrite (SemRegExprVals HRegMap HSemRegMap); auto.
  - simpl in *; inv H0; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
    assert (forall b, (evalExpr (bexpr && b)%kami_expr = false)).
    { intros; simpl; rewrite HNbexpr; auto. }
    specialize (IHa1 _ _ _ _ _ _ (H0 e) _ HRegMap HSemCompActionT_a); dest.
    assert (SemRegMapExpr (VarRegMap type regMap_a) regMap1) as P0.
    { rewrite H1; constructor. }
    specialize (IHa2 _ _ _ _ _ _ (H0 (!e)%kami_expr) _ P0 HSemCompActionT_a0); dest.
    assert (SemRegMapExpr (VarRegMap type regMap_a0) regMap1) as P1.
    { rewrite <- H3. constructor. }
    specialize (H _ _ _ _ _ _ _ HNbexpr _ P1 HSemCompActionT); dest.
    subst; auto.
  - inv H; EqDep_subst; eauto.
  - inv H; EqDep_subst.
    inv HRegMapWf.
    specialize (SemRegExprVals HRegMap H) as P0; auto.
Qed.

Lemma UpdRegs_same_nil o :
  UpdRegs (nil::nil) o o.
Proof.
  unfold UpdRegs.
  repeat split; auto.
  intros.
  right; unfold not; split; intros; dest; auto.
  destruct H0; subst; auto.
Qed.

Lemma NoDup_app_split {A : Type} (l l' : list A) :
  NoDup (l++l') ->
  forall a,
    In a l ->
    ~ In a l'.
Proof.
  induction l'; repeat intro;[inv H1|].
  specialize (NoDup_remove _ _ _ H) as P0; dest.
  inv H1; apply H3; rewrite in_app_iff; auto.
  exfalso; eapply IHl'; eauto.
Qed.

Lemma EquivActions k a:
  forall
    writeMap old upds
    (WfMap : WfRegMapExpr writeMap (old, upds)),
  forall calls retl upds',
    @SemCompActionT k (compileAction (old, nil) a (Const type true) writeMap) upds' calls retl ->
    (forall u, In u (snd upds') -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old)) /\
    exists newRegs readRegs,
      upds' = (old, match newRegs with
                    |nil => upds
                    |_ :: _ => (hd nil upds ++ newRegs) :: tl upds
                    end) /\
      SemAction old a readRegs newRegs calls retl.
Proof.
  induction a; subst; intros; simpl in *.
  - inv H0; EqDep_subst;[|discriminate].
    specialize (H _ _ _ _ WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (IHa _ _ _ WfMap _ _ _ HSemCompActionT_a); dest.
    assert (WfRegMapExpr (VarRegMap type regMap_a) regMap_a) as WfMap0.
    { unfold WfRegMapExpr; split;[econstructor|].
      destruct regMap_a; inv H1; intros.
      apply (H0 _ H1).
    }
    rewrite H1 in *.
    specialize (H _ _ _ _ WfMap0 _ _ _ HSemCompActionT_cont); dest.
    split; auto.
    exists (x++x1), (x0++x2); split.
    + destruct x1; simpl in *; auto.
      * rewrite app_nil_r; assumption.
      * destruct x; simpl in *; auto.
        rewrite app_comm_cons, app_assoc; assumption.
    + econstructor; eauto.
      rewrite H3 in H; simpl in *.
      clear - H.
      destruct x, x1; eauto using DisjKey_nil_r, DisjKey_nil_l; simpl in *.
      specialize (H _ (or_introl _ eq_refl)); simpl in *; dest.
      repeat rewrite map_app in H.
      intro k.
      destruct (In_dec string_dec k (map fst (p0::x1))); auto.
      left; intro.
      destruct (NoDup_app_Disj string_dec _ _ H k); auto.
      apply H2; rewrite in_app_iff; right; auto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, ((r, existT _ k regVal) :: x0).
    split; auto.
    econstructor; eauto.
    inv HReadMap; inv HUpdatedRegs; auto.
    discriminate.
  - inv H; simpl in *; EqDep_subst.
    assert (val_a = evalExpr (Const type WO)) as TMP.
    {rewrite (shatter_word_0 val_a); auto. }
    rewrite TMP in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    destruct HRegMapWf, WfMap, regMap_a.
    inv H;[|discriminate]; EqDep_subst.
    specialize (SemRegExprVals H1 HSemRegMap) as P0; inv P0.
    assert (WfRegMapExpr (VarRegMap type (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0))
                         (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as WfMap0.
    { split; auto. constructor. }
    specialize (IHa _ _ _ WfMap0 _ _ _ HSemCompActionT_cont); dest; simpl in *; split; auto.
    exists ((r, existT (fullType type) k (evalExpr e)) :: nil ++ x), x0; split.
    + destruct x; simpl in *; auto.
      rewrite <- app_assoc in H3. rewrite <-app_comm_cons in H3.
      simpl in H3; auto.
    + rewrite H3 in H; simpl in *; destruct x; econstructor; eauto; simpl in *; specialize (H _ (or_introl _ eq_refl)); dest.
      * rewrite map_app in H6; simpl in *.
        apply (H6 (r, k)).
        rewrite in_app_iff; right; left; reflexivity.
      * repeat intro; inv H7.
      * rewrite map_app in H6; simpl in *.
        apply (H6 (r, k)).
        rewrite map_app; repeat rewrite in_app_iff; simpl; auto.
      * repeat intro.
        repeat rewrite map_app in H; simpl in *.
        destruct H7; subst; destruct (NoDup_app_Disj string_dec _ _ H r) as [P0|P0]; apply P0.
        -- rewrite in_app_iff; simpl; auto.
        -- simpl; auto.
        -- rewrite in_app_iff; simpl; auto.
        -- simpl; right; rewrite in_map_iff.
           exists (r, v); simpl; auto.
  - inv H0; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    remember (evalExpr e) as P0.
    apply Eqdep.EqdepTheory.inj_pair2 in H4.
    rewrite H4 in *.
    clear H4; simpl in *.
    assert (forall bexpr, (evalExpr (Const type true && bexpr)%kami_expr = evalExpr bexpr)) as P1.
    { intro; simpl; auto. }
    specialize (SemCompActionEquivBexpr _ _ _ _ _ (P1 e) HSemCompActionT_a) as P2.
    specialize (SemCompActionEquivBexpr _ _ _ _ _ (P1 (!e)%kami_expr) HSemCompActionT_a0) as P3.
    destruct P0; simpl in *.
    + assert (evalExpr e = evalExpr (Const type true)) as P4; simpl; auto.
      assert (evalExpr (!e)%kami_expr = false) as P5.
      { simpl; rewrite <- HeqP0; auto. }
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 P2) as P6.
      specialize (IHa1 _ _ _ WfMap _ _ _ P6); dest.
      rewrite <- HeqP0 in HSemCompActionT.
      destruct (predFalse_UpdsNil _ _ _ P5 (SemVarRegMap regMap_a) P3).
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite <- H3 in P7 at 2.
      rewrite H1 in P7.
      specialize (H _ _ _ _ P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x++x1), (x0++x2).
      destruct x; simpl; split; auto.
      * rewrite H4.
        econstructor; eauto.
        apply DisjKey_nil_l.
      * destruct x1;[rewrite app_nil_r|]; simpl in *; auto.
        rewrite <-app_assoc, <-app_comm_cons in H5; assumption.
      * rewrite H4; simpl.
        econstructor; eauto.
        rewrite H5 in H; simpl in *.
        clear - H.
        destruct x1; simpl in *; [apply DisjKey_nil_r|].
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        intro.
        destruct (NoDup_app_Disj string_dec _ _ H k); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
    + assert (evalExpr (!e)%kami_expr = evalExpr (Const type true)) as P4.
      { simpl; rewrite <- HeqP0; auto. }
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 P3) as P6.
      remember WfMap as WfMap0.
      inv WfMap0.
      destruct (predFalse_UpdsNil _ _ _ (eq_sym HeqP0) H0 P2).
      assert (WfRegMapExpr (VarRegMap type regMap_a) (old, upds)) as WfMap0.
      { rewrite <- H2.
        clear - WfMap.
        unfold WfRegMapExpr in *; dest; repeat split;[constructor| |]; eapply H0; eauto.
      }
      specialize (IHa2 _ _ _ WfMap0 _ _ _ P6); dest.
      rewrite <- HeqP0 in HSemCompActionT.
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite  H5 in P7 at 2.
      specialize (H _ _ _ _ P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x++x1), (x0++x2).
      destruct x; simpl; split; auto.
      * rewrite H3; simpl.
        econstructor 8; eauto.
        apply DisjKey_nil_l.
      * destruct x1;[rewrite app_nil_r|]; simpl in *; auto.
        rewrite <-app_assoc, <-app_comm_cons in H7; assumption.
      * rewrite H3; simpl.
        econstructor 8; eauto.
        rewrite H7 in H; simpl in *.
        clear - H.
        destruct x1; simpl in *; [apply DisjKey_nil_r|].
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        intro.
        destruct (NoDup_app_Disj string_dec _ _ H k); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
  - inv H; EqDep_subst.
    specialize (IHa _ _ _ WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0.
    split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    inv WfMap; inv HRegMapWf.
    specialize (SemRegExprVals H H1) as TMP; subst; simpl in *.
    split; auto.
    exists nil, nil.
    split; auto.
    constructor; auto.
Qed.
