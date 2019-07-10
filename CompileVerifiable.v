Require Import Syntax StateMonad Properties All.
Import Word.Notations.

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

  End ReadMap.
    Definition compileActions (readMap : regMapTy) (acts: list (ActionT ty Void)) :=
      fold_left (fun acc a =>
                   CompLetFull acc (fun _ writeMap =>
                                      (CompLetFull (CompRet ($$ WO)%kami_expr (CompactRegMap (VarRegMap writeMap)))
                                      (fun _ v => @compileAction v _ a ($$ true)%kami_expr (VarRegMap v))))) acts
                (CompRet ($$ WO)%kami_expr (VarRegMap readMap)).

    Definition compileRules (readMap : regMapTy) (rules: list RuleT) :=
      compileActions readMap (map (fun a => snd a ty) rules).
End Compile.

Section Semantics.
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.

  Section PriorityUpds.
    Variable o: RegsT.
    Inductive PriorityUpds: UpdRegsT -> RegsT -> Prop :=
    | NoUpds: PriorityUpds nil o
    | ConsUpds (prevUpds: UpdRegsT) (prevRegs: RegsT)
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
    
    Lemma prevPrevRegsTrue' prevUpds:
      forall prev, PriorityUpds prevUpds prev -> getKindAttr o = getKindAttr prev.
    Proof.
      induction 1; eauto.
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

Section Properties.

  Lemma unifyWO (x : word 0):
    x = (evalExpr (Const type WO)).
  Proof.
    simpl.
    rewrite (shatter_word_0 x).
    reflexivity.
  Qed.

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
      econstructor; eauto.
      rewrite (unifyWO val_a) in HSemCompActionT_a.
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
      inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
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
    forall (bexpr: Bool @# type) o u regMap1 regMap2 calls val
           (HNbexpr : evalExpr bexpr = false) rexpr (HRegMap : SemRegMapExpr rexpr regMap1),
      @SemCompActionT k (compileAction (o, u) a bexpr rexpr) regMap2 calls val ->
      regMap1 = regMap2 /\ calls = nil.
  Proof.
    induction a; intros.
    - inv H0; EqDep_subst;[congruence|eauto].
    - inv H0; EqDep_subst; eauto.
    - inv H0; EqDep_subst; eauto.
      specialize (IHa _ _ _ _ _ _ _ HNbexpr _ HRegMap HSemCompActionT_a); dest.
      rewrite H0 in HRegMap.
      assert (SemRegMapExpr (VarRegMap type regMap_a) regMap_a);[constructor|].
      specialize (H _ _ _ _ _ _ _ _ HNbexpr _ H2 HSemCompActionT_cont); dest.
      split; subst; auto.
    - inv H0; EqDep_subst; eauto.
    - inv H0; EqDep_subst; eauto.
    - inv H; simpl in *; EqDep_subst; eauto.
      rewrite (unifyWO val_a) in HSemCompActionT_a.
      inv HSemCompActionT_a; EqDep_subst.
      inv HRegMapWf; inv H; EqDep_subst;[congruence|].
      assert (SemRegMapExpr (VarRegMap type (old, upds)) (old, upds));[constructor|].
      specialize (IHa _ _ _ _ _ _ _ HNbexpr _ H HSemCompActionT_cont); dest.
      rewrite (SemRegExprVals HRegMap HSemRegMap); auto.
    - simpl in *; inv H0; EqDep_subst.
      inv HSemCompActionT_cont; EqDep_subst.
      inv HSemCompActionT_cont0; EqDep_subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
      assert (forall b, (evalExpr (bexpr && b)%kami_expr = false)).
      { intros; simpl; rewrite HNbexpr; auto. }
      specialize (IHa1 _ _ _ _ _ _ _ (H0 e) _ HRegMap HSemCompActionT_a); dest.
      assert (SemRegMapExpr (VarRegMap type regMap_a) regMap1) as P0.
      { rewrite H1; constructor. }
      specialize (IHa2 _ _ _ _ _ _ _ (H0 (!e)%kami_expr) _ P0 HSemCompActionT_a0); dest.
      assert (SemRegMapExpr (VarRegMap type regMap_a0) regMap1) as P1.
      { rewrite <- H3. constructor. }
      specialize (H _ _ _ _ _ _ _ _ HNbexpr _ P1 HSemCompActionT); dest.
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

  Lemma PriorityUpds_Equiv old upds new
        (HNoDupOld : NoDup (map fst old))
        (HNoDupUpds : forall u, In u upds -> NoDup (map fst u)) :
    PriorityUpds old upds new ->
    forall new',
      PriorityUpds old upds new' ->
      SubList new new'.
  Proof.
    induction 1; intros.
    - inv H.
      + apply SubList_refl.
      + discriminate.
    - subst.
      inv H0; inv HFullU.
      repeat intro.
      destruct x.
      specialize (Hcurr _ _ H0).
      specialize (getKindAttr_map_fst _ _ currRegsTCurr0) as P0.
      specialize (getKindAttr_map_fst _ _ currRegsTCurr) as P1.
      assert (In s (map fst new')).
      { rewrite <- P0, P1, in_map_iff. exists (s, s0); split; auto. }
      rewrite in_map_iff in H1; dest.
      destruct x; simpl in *; subst.
      specialize (Hcurr0 _ _ H2).
      specialize (HNoDupUpds _ (or_introl _ (eq_refl))) as P3.
      destruct Hcurr, Hcurr0; dest.
      + rewrite <-(KeyMatching3 _ _ _ P3 H3 H1 eq_refl).
        assumption.
      + exfalso; apply H3.
        rewrite in_map_iff.
        exists (s, s0); split; auto.
      + exfalso; apply H1.
        rewrite in_map_iff.
        exists (s, s2); split; auto.
      + assert (forall u,  In u prevUpds0 -> NoDup (map fst u)) as P4; eauto.
        specialize (IHPriorityUpds P4 _ prevCorrect _ H5).
        rewrite (getKindAttr_map_fst _ _ (prevPrevRegsTrue' prevCorrect)) in HNoDupOld.
        rewrite (KeyMatching3 _ _ _ HNoDupOld H4 IHPriorityUpds eq_refl) in *.
        assumption.
  Qed.

  Lemma EquivActions k a:
    forall
      writeMap o old upds oInit uInit
      (HoInitNoDups : NoDup (map fst oInit))
      (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
      (HPriorityUpds : PriorityUpds oInit uInit o)
      (HConsistent : getKindAttr o = getKindAttr old)
      (WfMap : WfRegMapExpr writeMap (old, upds)),
    forall calls retl upds',
      @SemCompActionT k (compileAction (oInit, uInit) a (Const type true) writeMap) upds' calls retl ->
      (forall u, In u (snd upds') -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old)) /\
      exists newRegs readRegs,
        upds' = (old, match newRegs with
                      |nil => upds
                      |_ :: _ => (hd nil upds ++ newRegs) :: tl upds
                      end) /\
        SemAction o a readRegs newRegs calls retl.
  Proof.
    induction a; subst; intros; simpl in *.
    - inv H0; EqDep_subst;[|discriminate].
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
      exists x, x0; split; auto.
      econstructor; eauto.
    - inv H0; EqDep_subst.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
      exists x, x0; split; auto.
      econstructor; eauto.
    - inv H0; EqDep_subst.
      specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT_a); dest.
      assert (WfRegMapExpr (VarRegMap type regMap_a) regMap_a) as WfMap0.
      { unfold WfRegMapExpr; split;[econstructor|].
        destruct regMap_a; inv H1; intros.
        apply (H0 _ H1).
      }
      rewrite H1 in *.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont); dest.
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
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
      exists x, x0; split; auto.
      econstructor; eauto.
    - inv H0; EqDep_subst.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
      exists x, ((r, existT _ k regVal) :: x0).
      split; auto.
      econstructor; eauto.
      inv HReadMap.
      apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
    - inv H; simpl in *; EqDep_subst.
      rewrite (unifyWO val_a) in HSemCompActionT_a.
      inv HSemCompActionT_a; EqDep_subst.
      destruct HRegMapWf, WfMap, regMap_a.
      inv H;[|discriminate]; EqDep_subst.
      specialize (SemRegExprVals H1 HSemRegMap) as P0; inv P0.
      assert (WfRegMapExpr (VarRegMap type (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0))
                           (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as WfMap0.
      { split; auto. constructor. }
      specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont);
        dest; simpl in *; split; auto.
      exists ((r, existT (fullType type) k (evalExpr e)) :: nil ++ x), x0; split.
      + destruct x; simpl in *; auto.
        rewrite <- app_assoc in H3. rewrite <-app_comm_cons in H3.
        simpl in H3; auto.
      + rewrite H3 in H; simpl in *; destruct x; econstructor; eauto; simpl in *; specialize (H _ (or_introl _ eq_refl)); dest.
        * rewrite map_app, <-HConsistent in H6; simpl in *.
          apply (H6 (r, k)).
          rewrite in_app_iff; right; left; reflexivity.
        * repeat intro; inv H7.
        * rewrite map_app, <-HConsistent in H6; simpl in *.
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
        specialize (IHa1 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ P6); dest.
        rewrite <- HeqP0 in HSemCompActionT.
        destruct (predFalse_UpdsNil _ _ _ _ P5 (SemVarRegMap regMap_a) P3).
        assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
        { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
        rewrite <- H3 in P7 at 2.
        rewrite H1 in P7.
        specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
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
        destruct (predFalse_UpdsNil _ _ _ _ (eq_sym HeqP0) H0 P2).
        assert (WfRegMapExpr (VarRegMap type regMap_a) (old, upds)) as WfMap0.
        { rewrite <- H2.
          clear - WfMap.
          unfold WfRegMapExpr in *; dest; repeat split;[constructor| |]; eapply H0; eauto.
        }
        specialize (IHa2 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ P6); dest.
        rewrite <- HeqP0 in HSemCompActionT.
        assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
        { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
        rewrite  H5 in P7 at 2.
        specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
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
      specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
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


  Lemma SameOldAction (k : Kind) (a : ActionT type k) :
    forall oInit uInit writeMap old upds wOld wUpds calls retl bexpr
           (HSemRegMap : SemRegMapExpr writeMap (wOld, wUpds)),
      @SemCompActionT k (compileAction (oInit, uInit) a bexpr writeMap) (old, upds) calls retl ->
      wOld = old.
  Proof.
    induction a; intros; simpl in *.
    - inv H0; EqDep_subst; simpl in *; eapply H; eauto.
    - inv H0; EqDep_subst; simpl in *.
      eapply H; eauto.
    - inv H0; EqDep_subst; simpl in *.
      assert (SemRegMapExpr (VarRegMap type regMap_a) regMap_a) as P0.
      { constructor. }
      destruct regMap_a.
      specialize (H _ _ _ _ _ _ _ _ _ _ _ P0 HSemCompActionT_cont); subst.
      specialize (IHa _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a); assumption.
    - inv H0; EqDep_subst; simpl in *.
      eapply H; eauto.
    - inv H0; EqDep_subst; simpl in *.
      eapply H; eauto.
    - inv H; simpl in *; EqDep_subst.
      rewrite (unifyWO val_a) in HSemCompActionT_a.
      inv HSemCompActionT_a; EqDep_subst.
      destruct regMap_a; unfold WfRegMapExpr in *; dest.
      inv H; EqDep_subst.
      + assert (SemRegMapExpr (VarRegMap type (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0))
                              (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as P0.
        { constructor. }
        specialize (IHa _ _ _ _ _ _ _ _ _ _ P0 HSemCompActionT_cont).
        specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
        reflexivity.
      + specialize (IHa _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont).
        specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
        reflexivity.
    - inv H0; EqDep_subst; simpl in *.
      inv HSemCompActionT_cont; EqDep_subst.
      inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
      destruct regMap_a, regMap_a0.
      specialize (H _ _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT).
      simpl in *.
      specialize (IHa1 _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a).
      specialize (IHa2 _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_a0).
      subst; reflexivity.
    - inv H; EqDep_subst; simpl in *.
      eapply IHa; eauto.
    - inv H; EqDep_subst.
      unfold WfRegMapExpr in *; dest.
      specialize (SemRegExprVals H HSemRegMap) as TMP; inv TMP.
      reflexivity.
  Qed.

  Lemma SameOldActions o:
    forall la old upds calls retl,
      @SemCompActionT Void (compileActions (o, nil) (rev la)) (old, upds) calls retl ->
      o = old.
  Proof.
    induction la; simpl in *; intros.
    rewrite (unifyWO retl) in H.
    inv H; EqDep_subst.
    inv HRegMapWf.
    inv H.
    reflexivity.
    - unfold compileActions in *; simpl in *.
      rewrite <- fold_left_rev_right in *.
      rewrite rev_app_distr, rev_involutive in *; simpl in *.
      rewrite (unifyWO retl) in H.
      inv H; simpl in *; EqDep_subst.
      rewrite (unifyWO WO) in HSemCompActionT_cont.
      inv HSemCompActionT_cont; simpl in *; EqDep_subst.
      rewrite (unifyWO val_a0) in HSemCompActionT_a0.
      inv HSemCompActionT_a0; EqDep_subst.
      destruct regMap_a.
      specialize (IHla _ _ _ _ HSemCompActionT_a); subst.
      destruct regMap_a0.
      inv HRegMapWf; inv H; inv HSemRegMap.
      apply (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0).
  Qed.

  Lemma SameOldLoop (m : BaseModule) o:
    forall rules old upds calls retl,
      @SemCompActionT Void (compileRules type (o, nil) (rev rules)) (old, upds) calls retl ->
      o = old.
  Proof.
    induction rules; simpl in *; intros.
    - rewrite (unifyWO retl) in H.
      inv H; EqDep_subst.
      inv HRegMapWf.
      inv H.
      reflexivity.
    - unfold compileRules, compileActions in *; simpl in *.
      rewrite map_app, <- fold_left_rev_right, map_rev in *.
      simpl in *.
      rewrite rev_app_distr, rev_involutive in *; simpl in *.
      rewrite (unifyWO retl) in H.
      inv H; EqDep_subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
      destruct regMap_a.
      specialize (IHrules _ _ _ _ HSemCompActionT_a); subst.
      rewrite (unifyWO WO) in HSemCompActionT_cont.
      inv HSemCompActionT_cont; simpl in *; EqDep_subst.
      rewrite (unifyWO val_a0) in HSemCompActionT_a0.
      inv HSemCompActionT_a0; simpl in *; EqDep_subst.
      destruct regMap_a; inv HRegMapWf; inv H; inv HSemRegMap.
      apply (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0).
  Qed.

  Lemma PriorityUpdsCompact upds:
    forall old new,
      PriorityUpds old upds new -> PriorityUpds old (nil::upds) new.
  Proof.
    induction upds.
    - econstructor 2 with (u := nil) (prevUpds := nil); eauto; repeat constructor.
      inv H; eauto.
    - intros.
      econstructor 2 with (u := nil) (prevUpds := a :: upds); eauto.
      inv H; auto.
  Qed.

  Lemma KeyMatch (l1 : RegsT) :
    NoDup (map fst l1) ->
    forall l2,
      map fst l1 = map fst l2 ->
      (forall s v, In (s, v) l1 -> In (s, v) l2) ->
      l1 = l2.
  Proof.
    induction l1; intros.
    - destruct l2; inv H0; auto.
    - destruct a; simpl in *.
      destruct l2; inv H0.
      destruct p; simpl in *.
      inv H.
      specialize (H1 _ _ (or_introl (eq_refl))) as TMP; destruct TMP.
      + rewrite H in *.
        assert (forall s v, In (s, v) l1 -> In (s, v) l2).
        { intros.
          destruct (H1 _ _ (or_intror H0)); auto.
          exfalso.
          inv H2.
          apply H3.
          rewrite in_map_iff.
          exists (s2, v); auto.
        }
        rewrite (IHl1 H5 _ H4 H0).
        reflexivity.
      + exfalso.
        apply H3.
        rewrite H4, in_map_iff.
        exists (s, s0); auto.
  Qed.
  
  Lemma CompactPriorityUpds upds:
    forall old,
      NoDup (map fst old) ->
      forall new, 
        PriorityUpds old (nil::upds) new -> PriorityUpds old upds new.
  Proof.
    induction upds; intros.
    - enough (old = new).
      { subst; constructor. }
      inv H0; inv HFullU; inv prevCorrect;[|discriminate]; simpl in *.
      apply getKindAttr_map_fst in currRegsTCurr.
      assert (forall s v, In (s, v) new -> In (s, v) prevRegs).
      { intros.
        destruct (Hcurr _ _ H0);[contradiction|dest]; auto.
      }
      symmetry.
      apply KeyMatch; auto.
      rewrite currRegsTCurr in H; assumption.
    - inv H0; inv HFullU.
      enough ( new = prevRegs).
      { rewrite H0; auto. }
      apply getKindAttr_map_fst in currRegsTCurr.
      specialize (getKindAttr_map_fst _ _ (prevPrevRegsTrue' prevCorrect)) as P0.
      rewrite currRegsTCurr in H.
      eapply KeyMatch; eauto.
      + rewrite <- currRegsTCurr; assumption.
      + intros.
        destruct (Hcurr _ _ H0);[contradiction| dest; auto].
  Qed.

  Lemma CompactPriorityUpds_iff {old} (NoDupsOld : NoDup (map fst old)) upds new:
    PriorityUpds old (nil::upds) new <-> PriorityUpds old upds new.
  Proof.
    split; eauto using CompactPriorityUpds, PriorityUpdsCompact.
  Qed.
  
  Lemma EquivLoop (m : BaseModule) o:
    forall rules upds calls retl ls
           (HoInitNoDups : NoDup (map fst o))
           (HTrace : Trace m o ls)
           (HNoMeths : (getMethods m) = nil),
      SubList rules (getRules m) ->
      @SemCompActionT Void (compileRules type (o, nil) (rev rules)) (o, upds) calls retl ->
      (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
      exists o' (ls' : list (list FullLabel)),
        PriorityUpds o upds o' /\
        upds = (map getLabelUpds ls') /\
        calls = concat (map getLabelCalls (rev ls')) /\
        Trace m o' (ls' ++ ls).
  Proof.
    induction rules; simpl in *; intros.
    - rewrite (unifyWO retl) in H0.
      inv H0; EqDep_subst.
      unfold WfRegMapExpr in *; dest.
      inv H0; split; auto.
      exists o, nil; repeat split; auto.
      constructor.
    - unfold compileRules, compileActions in *; simpl in *.
      rewrite map_app in *.
      rewrite <- fold_left_rev_right in *.
      rewrite map_rev in *.
      simpl in *.
      rewrite rev_app_distr in H0.
      rewrite rev_involutive in *.
      simpl in *.
      rewrite (unifyWO retl) in H0.
      inv H0; simpl in *; EqDep_subst.
      assert (SubList rules (getRules m)) as P0.
      { repeat intro; apply H; right; auto. }
      destruct regMap_a.
      rewrite (unifyWO WO) in HSemCompActionT_cont.
      inv HSemCompActionT_cont; simpl in *; EqDep_subst.
      rewrite (unifyWO val_a0) in HSemCompActionT_a0.
      inv HSemCompActionT_a0; simpl in *; EqDep_subst.
      destruct regMap_a.
      specialize HRegMapWf as HRegMapWf0.
      inv HRegMapWf; inv H0; inv HSemRegMap.
      specialize (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0) as TMP; subst.
      specialize (IHrules _ _ _ _ HoInitNoDups HTrace HNoMeths P0 HSemCompActionT_a); dest.
      rewrite <-CompactPriorityUpds_iff in H2; auto.
      assert (forall u, In u (nil :: upds0) -> NoDup (map fst u)) as P1.
      { intros.
        destruct (H1 _ H7); auto.
      }
      assert (WfRegMapExpr (VarRegMap type (o, nil :: upds0)) (o, nil::upds0)) as P2.
      { clear - HRegMapWf0.
        unfold WfRegMapExpr in *; dest; split; auto.
        constructor.
      }
      specialize (EquivActions _ HoInitNoDups P1 H2 (eq_sym (prevPrevRegsTrue' H2))
                               P2 HSemCompActionT_cont0) as TMP; dest.
      split; auto; simpl in *.
      assert (upds = (x1::upds0)) as P4.
      { inv H8.
        destruct x1; auto.
      }
      clear H8; subst.
      exists (doUpdRegs x1 x), (((x1, (Rle (fst a), calls_cont0))::nil)::x0).
      unfold getLabelCalls, getLabelUpds in *; simpl in *.
      rewrite app_nil_r.
      repeat split; auto.
      + econstructor 2 with (u := x1); auto.
        * rewrite CompactPriorityUpds_iff in H2; auto.
          apply H2.
        * specialize (H7 _ (or_introl eq_refl)); dest.
          rewrite (prevPrevRegsTrue' H2).
          apply getKindAttr_doUpdRegs; eauto.
          -- rewrite <- (getKindAttr_map_fst _ _ (prevPrevRegsTrue' H2)).
             assumption.
          -- intros.
             rewrite <- (prevPrevRegsTrue' H2).
             apply H4.
             rewrite in_map_iff.
             exists (s, v); simpl; split; auto.
        * repeat intro.
          rewrite (getKindAttr_map_fst _ _ (prevPrevRegsTrue' H2)) in HoInitNoDups.
          specialize (H7 _ (or_introl eq_refl)); dest.
          rewrite (prevPrevRegsTrue' H2) in H7.
          specialize (doUpdRegs_UpdRegs _ (HoInitNoDups) _ H4 H7) as P4.
          unfold UpdRegs in P4; dest.
          specialize (H10 _ _ H3); dest.
          destruct H10; dest.
          -- inv H10; auto.
             inv H12.
          -- right; split; auto.
             intro; apply H10.
             exists x1; split; simpl; auto.
      + repeat rewrite map_app; simpl.
        repeat rewrite concat_app; simpl.
        repeat rewrite app_nil_r.
        reflexivity.
      + destruct a; simpl in *.
        econstructor 2.
        * apply H5.
        * assert (Step m x ((x1, (Rle s, calls_cont0))::nil)) as P3.
          { econstructor.
            - econstructor 2; eauto; specialize (Trace_sameRegs HTrace) as TMP; simpl in *.
              + rewrite <- TMP, (prevPrevRegsTrue' H2); reflexivity.
              + apply H; left; simpl; reflexivity.
              + rewrite <- TMP, (prevPrevRegsTrue' H2).
                apply SubList_map, (SemActionReadsSub H9).
              + specialize (H7 _ (or_introl eq_refl)); dest.
                rewrite <- TMP, (prevPrevRegsTrue' H2).
                apply (SemActionUpdSub H9).
              + intros; inv H3.
              + intros; inv H3.
              + econstructor.
                rewrite <- TMP.
                apply (eq_sym (prevPrevRegsTrue' H2)).
            - unfold MatchingExecCalls_Base; intros.
              rewrite HNoMeths in H3.
              inv H3.
          }
          apply P3.
        * simpl.
          apply doUpdRegs_enuf; auto.
          -- specialize (H7 _ (or_introl (eq_refl))); dest; auto.
          -- apply getKindAttr_doUpdRegs; auto.
             ++ rewrite <-(getKindAttr_map_fst _ _ (prevPrevRegsTrue' H2)); assumption.
             ++ specialize (H7 _ (or_introl (eq_refl))); dest; assumption.
             ++ intros.
                specialize (H7 _ (or_introl (eq_refl))); dest.
                rewrite <-(prevPrevRegsTrue' H2).
                apply H7.
                rewrite in_map_iff.
                exists (s0, v); auto.
        * reflexivity.
  Qed.

  Corollary EquivLoop' {m : BaseModule} {o ls rules upds calls retl}
            (HTrace : Trace m o ls) (HoInitNoDups : NoDup (map fst o))
            (HNoMeths : (getMethods m) = nil) (HValidSch : SubList rules (getRules m)):
    @SemCompActionT Void (compileRules type (o, nil) rules) (o, upds) calls retl ->
    (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists o' (ls' : list (list FullLabel)),
      PriorityUpds o upds o' /\
      upds = (map getLabelUpds ls') /\
      calls = concat (map getLabelCalls (rev ls')) /\
      Trace m o' (ls' ++ ls).
  Proof.
    rewrite <- (rev_involutive rules).
    assert (SubList (rev rules) (getRules m)) as P0.
    { repeat intro; apply HValidSch; rewrite in_rev; assumption. }
    eapply EquivLoop; eauto.
  Qed.
      
End Properties.
