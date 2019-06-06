Require Import SyntaxDoubleWrites Syntax CompileVerifiable StateMonad Properties All.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section DoubleWritesProof.

 Lemma NoDupAppSplit {A : Type} (l l' : list A) :
  NoDup (l++l') ->
  forall a,
    In a l ->
    ~ In a l'.
 Proof.
   induction l'.
   - intros.
     unfold not.
     intros.
     inversion H1.
   - intros.
     unfold not.
     intros.
     specialize (NoDup_remove _ _ _ H) as P0.
     destruct P0.
     inv H1.
     apply H3.
     rewrite in_app_iff.
     left.
     assumption.
     specialize (NoDup_remove _ _ _ H) as P0.
     destruct P0.
     eapply IHl'.
     assumption.
     apply H0.
     apply H4.
 Qed.

Lemma getKindAttr_consistent (k : Kind) (a : ActionT type k) (o : RegsT):
  forall newRegs readRegs calls retl,
    SemActionDoubleWrites o a readRegs newRegs calls retl ->
    SubList (getKindAttr newRegs) (getKindAttr o).
Proof.
  induction a; simpl in *; intros.
  - inv H0; EqDep_subst; eapply H; eauto.
  - inv H0; EqDep_subst; eapply H; eauto.
  - inv H0; EqDep_subst.
    rewrite map_app, SubList_app_l_iff; split.
    + eapply IHa; eauto.
    + eapply H; eauto.
  - inv H0; EqDep_subst; eapply H; eauto.
  - inv H0; EqDep_subst; eapply H; eauto.
  - inv H; EqDep_subst.
    repeat intro.
    simpl in *.
    destruct H; subst; auto.
    eapply IHa; eauto.
  - inv H0; EqDep_subst.
    + rewrite map_app,  SubList_app_l_iff.
      split.
      * eapply IHa1; eauto.
      * eapply H; eauto.
    + rewrite map_app, SubList_app_l_iff.
      split.
      * eapply IHa2; eauto.
      * eapply H; eauto.
  - inv H; EqDep_subst.
    eapply IHa; eauto.
  - inv H; EqDep_subst.
    simpl in *.
    unfold SubList. intros. inversion H.
Qed.


Lemma CheckOnNewUpds (k : Kind) (a : ActionT type k) (o : RegsT):
  forall writeMap upds' calls retl upds old,
    SemRegMapExpr writeMap (old, upds) ->
    SemCompActionT (compileAction (o,nil) a (Const type true) writeMap) (old, upds') calls retl ->
    forall u, In u upds' -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
Proof.
  induction a; intros; simpl in *; eauto.
  (* Meth Call *)
  - inv H1; EqDep_subst.
    * eapply H. apply H0. apply HSemCompActionT. assumption.
    * eapply H. apply H0. apply HSemCompActionT. assumption.
  (* Let Expr *)
  - inv H1; EqDep_subst.
     eapply H. apply H0. apply HSemCompActionT. assumption.
  (* Let Action *)
  - inv H1; EqDep_subst.
    destruct regMap_a.
     assert (old = r).
      { eapply SameOldAction.
        apply H0.
        apply HSemCompActionT_a.
      }
    rewrite <- H1 in HSemCompActionT_a.
    specialize (IHa _ _ _ _ _ _ H0 HSemCompActionT_a).
        assert (SemRegMapExpr (VarRegMap type (old, l)) (old,l)) as P0.
    {
      econstructor.
    }
    rewrite <- H1 in HSemCompActionT_cont.
    specialize (H _ _ _ _ _ _ _ P0 HSemCompActionT_cont).
    split.
    * apply H. assumption.
    * apply H. assumption.
    (* Non Det *)
  - inv H1; EqDep_subst.
    eapply H. apply H0. apply HSemCompActionT. apply H2.
    (* Read *)
  - inv H1; EqDep_subst.
    eapply H. apply H0. apply HSemCompActionT. apply H2.
    (* Write *)
  - inv H0; simpl in *; EqDep_subst.
     assert (val_a = evalExpr (Const type WO)) as P0.
     {rewrite (shatter_word_0 val_a); auto. }
     subst.
     inversion HSemCompActionT_a; EqDep_subst.
     destruct regMap_a.
     assert (r0 = old).
     {
       - inv HRegMapWf.
         inv H0. EqDep_subst.
         *  specialize (SemVarRegMap
                       (r0, (hd nil upds0 ++
                                (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as P0.
         eapply SameOldAction.
         apply P0.
         apply HSemCompActionT_cont.
         * discriminate.
     }
     assert (SemRegMapExpr (VarRegMap type (r0, l)) (r0, l)) as P1.
     { econstructor. }
     rewrite <- H0 in HSemCompActionT_cont.
     specialize (IHa _ _ _ _ _ _ P1 HSemCompActionT_cont).
     rewrite -> H0 in IHa. apply IHa. assumption.
  (* If-else *)
  - inv H1; simpl in *; EqDep_subst.
    inversion HSemCompActionT_cont; simpl in *; EqDep_subst.
      inversion HSemCompActionT_cont0; simpl in *; EqDep_subst.
     remember (evalExpr e) as P0.
          assert (forall bexpr, (evalExpr (Const type true && bexpr)%kami_expr = evalExpr bexpr)) as P1.
          { intro; simpl; auto. }
          specialize (SemCompActionEquivBexpr _ _ _ _ _ (P1 e) HSemCompActionT_a) as P2.
          specialize (SemCompActionEquivBexpr _ _ _ _ _ (P1 (!e)%kami_expr) HSemCompActionT_a0) as P3.
          destruct P0; simpl in *.
     *  assert (evalExpr e = evalExpr (Const type true)) as P4.
      simpl in *. rewrite <- HeqP0. reflexivity.
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 P2) as P6.
      simpl in *. rewrite -> P4 in HSemCompActionT.
      destruct regMap_a0.
      assert (r = old).
      {
        * specialize (SemVarRegMap (r, l)) as P0.
          eapply SameOldAction.
          apply P0.
          apply HSemCompActionT.
      }
       assert (SemRegMapExpr (VarRegMap type (r, l)) (r, l)) as P5.
      { econstructor. }
      rewrite <- H1 in HSemCompActionT.
      specialize (H _ _ _ _ _ _ _ P5 HSemCompActionT).
      rewrite -> H1 in H.
      apply H. assumption.
    * assert (evalExpr (!e)%kami_expr = evalExpr (Const type true)) as P4.
      { simpl; rewrite <- HeqP0; auto. }
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 P3) as P6.
       destruct regMap_a0.
      assert (r = old).
      {
        * specialize (SemVarRegMap (r, l)) as P0.
          eapply SameOldAction.
          apply P0.
          apply HSemCompActionT.
      }
       assert (SemRegMapExpr (VarRegMap type (r, l)) (r, l)) as P5.
      { econstructor. }
      rewrite <- H1 in HSemCompActionT.
      specialize (H _ _ _ _ _ _ _ P5 HSemCompActionT).
      rewrite -> H1 in H.
      apply H. assumption.
    (* Sys *)
  - inv H0; EqDep_subst.
    eapply IHa. apply H. apply HSemCompActionT. assumption.
    (* Ret *)
  - inv H0; EqDep_subst.
    unfold WfRegMapExpr in HRegMapWf.
    destruct HRegMapWf.
    apply H2. assumption.
Qed.


Lemma FalseSemCompAction_rev (k : Kind) (a : ActionT type k) (o : RegsT) :
  forall regMap regMapExpr (bexpr : Bool @# type) (WfRegMap : WfRegMapExpr regMapExpr regMap),
    evalExpr bexpr = false ->
    exists retl,
      SemCompActionT (compileAction (o,nil) a bexpr regMapExpr) regMap nil retl.
Proof.
  induction a; simpl in *; subst.
  - (* Meth Call *)
    intros.
    specialize (H (evalConstT (getDefaultConst (snd s))) _ _ _ WfRegMap H0).
    destruct H.
    exists x.
    econstructor. eapply H. assumption.
  - (* Let expr *)
    intros.
    specialize (H (evalExpr e) _ _ _ WfRegMap H0).
    destruct H.
    exists x.
    econstructor. assumption.
  - (* Let Action *)
    intros.
    specialize (IHa _ _ _ WfRegMap H0).
    destruct IHa.
    assert (WfRegMapExpr (VarRegMap type regMap) regMap).
    {
      unfold WfRegMapExpr in *; split; eauto.
      constructor.
      destruct WfRegMap. assumption.
    }
    specialize (H x _ _ _ H2 H0).
    destruct H. exists x0.
    rewrite <- (app_nil_r (nil : MethsT)).
    econstructor.
    eapply H1. apply H.
  - (* Non Det *)
    intros.
    eexists.
    econstructor.
    admit.
  -(* Read *)
    intros.
    eexists. econstructor.
    constructor. apply NoUpds. simpl.
    admit.
    admit.
  -(* Write *)
    intros.
     assert (WfRegMapExpr (VarRegMap type regMap) regMap).
    {
      unfold WfRegMapExpr in *; split; eauto.
      constructor.
      destruct WfRegMap. assumption.
    }
    specialize (IHa _ _ _ H0 H).
    destruct IHa.
    exists x. simpl in *.
    rewrite <- (app_nil_r (nil : MethsT)).
    econstructor. econstructor. reflexivity.
    unfold WfRegMapExpr in *; dest; repeat split; eauto.
    destruct regMap.
    econstructor 3; eauto.
    assumption.
  -(* If-else *)
    intros. 
    remember (evalExpr e) as P0.
    assert ((evalExpr (bexpr && !e)%kami_expr = evalExpr bexpr)) as P1.
    { simpl. rewrite -> H0. simpl. destruct (evalExpr e). simpl. reflexivity.
      reflexivity. }
    assert ((evalExpr (bexpr && e)%kami_expr = false)) as P2.
    { simpl. rewrite -> H0. simpl. reflexivity. }
    specialize (IHa1 _ _ _ WfRegMap P2).
    destruct IHa1.
    assert (WfRegMapExpr (VarRegMap type regMap) regMap).
    {
      unfold WfRegMapExpr in *; split; eauto.
      constructor.
      destruct WfRegMap. assumption.
    }
    rewrite -> H0 in P1.
    specialize (IHa2 _ _ _ H2 P1).
    destruct IHa2.
    destruct P0.
    * specialize (H x _ _ _ H2 H0).
      destruct H.
      exists x1.  rewrite <- (app_nil_r (nil : MethsT)).
      econstructor. simpl in *.
      apply  SemCompActionEquivBexpr with (bexpr1 := bexpr).
      simpl. rewrite -> H0. simpl. reflexivity.
      apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && e)%kami_expr).
      simpl. rewrite -> H0. simpl. reflexivity.
      apply H1.
      rewrite <- (app_nil_r (nil : MethsT)).
      econstructor.
      apply SemCompActionEquivBexpr with (bexpr1 := bexpr).
      simpl. rewrite -> H0. simpl. reflexivity.
      simpl.
      apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && !e)%kami_expr).
      simpl. rewrite -> H0. simpl. reflexivity.
      apply H3.
      simpl. econstructor. simpl in *.
      rewrite <- HeqP0. apply H.
    * specialize (H x0 _ _ _ H2 H0).
      destruct H.
      exists x1.  rewrite <- (app_nil_r (nil : MethsT)).
      econstructor. simpl in *.
      apply H1.
      rewrite <- (app_nil_r (nil : MethsT)).
      econstructor.
      apply H3.
      econstructor. simpl in *.
      rewrite <- HeqP0.
      apply H.
  - (* Sys *)
    intros. 
    specialize (IHa _ _ _ WfRegMap H).
    destruct IHa.
    exists x. econstructor. apply H0.
  - (* Ret *)
    intros.
    exists (evalExpr e).
    econstructor. reflexivity.
    assumption.
Admitted.

Lemma WfSemAction (k : Kind) (a : ActionT type k) (o : RegsT) :
  forall readRegs calls retl newRegs,
    SemActionDoubleWrites o a readRegs newRegs calls retl ->
  SubList (getKindAttr newRegs) (getKindAttr o).
Proof.
 intros. induction H; eauto.
  + rewrite HNewRegs, map_app, SubList_app_l_iff; split; auto. 
  + rewrite HANewRegs. simpl in *. unfold SubList. intros.
    simpl in *. destruct H0. subst. assumption. eapply IHSemActionDoubleWrites. 
    assumption.
  + rewrite HUNewRegs, map_app, SubList_app_l_iff; split; auto.
  + rewrite HUNewRegs, map_app, SubList_app_l_iff; split; auto.
  + rewrite HNewRegs; simpl; repeat intro; inv H.
Qed.


Lemma EquivActionNoDupWritesNew (k : Kind) (a : ActionT type k) (o : RegsT):
  forall newRegs readRegs calls retl,
    SemActionDoubleWrites o a readRegs newRegs calls retl ->
    NoDup (map fst newRegs) ->
    forall old writeMap upds
           (HConsistent: getKindAttr o = getKindAttr old)
           (HCheck : forall s, In s (map fst newRegs) -> ~ In s (map fst (hd nil upds))),
      SemRegMapExpr writeMap (old, upds) ->
      (forall u, In u upds ->  NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old)) ->
      exists upds',
        (upds' = (old, match newRegs with
                    |nil => upds
                    |_ :: _ => (hd nil upds ++ newRegs) :: tl upds
                     end)) /\
        SemCompActionT (compileAction (o,nil) a (Const type true) writeMap) upds' calls retl.
Proof.
  induction a; subst; intros; simpl in *.
  - (* Meth Call *)
    inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent HCheck H2 H3); dest.
    exists x. split.
    * assumption.
    * econstructor; eauto.
  - (* Let expr *)
    inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent HCheck H2 H3); dest.
    exists x. split.
    * assumption.
    * econstructor; eauto.
  - (* Let Action *)
    inv H0; EqDep_subst.
    rewrite map_app, NoDup_app_iff in H1; dest.
    assert ( forall s, In s (map fst (newRegs0)) -> ~ In s (map fst (hd nil upds))) as P0.
    {
      intros.
      apply HCheck.
      rewrite map_app. apply in_or_app.
      left. assumption. }
    specialize (IHa _ _ _ _ HSemAction H0 _ _ _  HConsistent P0 H2 H3); dest.
    destruct x.
    assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
    apply SemVarRegMap.
    assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P1.
    {
      split. inv H6; simpl in *; subst.
      destruct newRegs0; auto.
      simpl in *. apply H3. assumption.
      simpl in *. destruct H9; auto. subst.
      rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
      * destruct upds; simpl in *. constructor.
        eapply H3. left. reflexivity.
      * assumption.
      * intros;subst.
        unfold not. intro. destruct H9.
        subst. eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H9.
        assumption.
      * intros; subst.
        unfold not. intro. destruct H6; subst.
        eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H6.
        assumption.
      * eapply H3. simpl in *.
        destruct upds. inversion H6.
        simpl in H6. simpl in *. right. assumption.
      * inv H6; subst.
        destruct newRegs0. apply H3. assumption.
        destruct upds. simpl in *.
        destruct H9; [|contradiction]; subst.
        specialize WfSemAction as P1.
        rewrite <- HConsistent.
        specialize (P1 _ a o readRegs0 calls0 v (p :: newRegs0) HSemAction).
        assumption.
        simpl in *.
        destruct H9; subst.
        rewrite map_app. rewrite SubList_app_l_iff; split; auto.
        apply H3. left. reflexivity.
         specialize WfSemAction as P1.
        rewrite <- HConsistent.
        specialize (P1 _ a o readRegs0 calls0 v (p :: newRegs0) HSemAction).
        assumption.
        apply H3. right. assumption. }
    inversion H6; subst; simpl in *.
    assert (forall s, In s (map fst (newRegsCont)) -> ~ In s (map fst (hd nil  match newRegs0 with
               | nil => upds
               | _ :: _ => (hd nil upds ++ newRegs0) :: tl upds
               end))) as P2.
    {
      intros. simpl in *. destruct newRegs0.
      * unfold not; intros. eapply HCheck.
        simpl in *. apply H9. assumption.
      * unfold not. intros. eapply H5. apply H9. simpl in H10. rewrite map_app in H10.
        apply in_app_or in H10. destruct H10.
      + exfalso.
        eapply H5.
        apply H9. exfalso.
        eapply HCheck. rewrite map_app.
        apply in_or_app. right.
        apply H9. assumption.
      + assumption.
    }
    inversion H6; subst. simpl in *.
    specialize (H _ _ _ _ _ HSemActionCont H1 _ _ _ HConsistent P2 H8 P1).
    dest.
    exists x; split.
    * inversion H6; subst.
      destruct newRegs0. destruct newRegsCont; simpl in *; reflexivity.
      simpl in *. destruct newRegsCont. simpl in *. rewrite app_nil_r. reflexivity.
      rewrite app_comm_cons. rewrite app_assoc. reflexivity.
    * econstructor; eauto.
  - (* Non Det *)
    inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent HCheck H2 H3); dest.
    exists x. split.
    * assumption.
    * econstructor; eauto.
  - (* Read *)
    inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent HCheck H2 H3); dest.
    exists x. split.
    * assumption.
    * econstructor; eauto.
      apply SemVarRegMap.
      apply NoUpds.
  - (* Write *)
    inv H; EqDep_subst.
    inv H0.
    assert (SemRegMapExpr
              (VarRegMap type
                (old, (hd nil upds ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds))
              (old, (hd nil upds ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds)) as P0.
    { econstructor; eauto. }

    assert ((forall u : RegsT,
                 hd nil upds ++ (r, existT (fullType type) k (evalExpr e)) :: nil = u \/
                 In u (tl upds) -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old))) as P1.
    {
      intros.
      destruct H; subst.
      - repeat rewrite map_app; simpl.
        split.
        + rewrite NoDup_app_iff; simpl in *; repeat split.
          * clear - H2.
            destruct upds; simpl in *;[constructor|].
            eapply H2.
            left; reflexivity.
          * constructor;[|constructor].
            intro; inv H.
          * repeat intro.
            destruct H0; auto; subst.
            eapply HCheck. left; reflexivity.
            assumption.
          * intros; subst.
            destruct H; auto; subst.
        + simpl in *. apply SubList_app_l_iff.
          split. simpl in *.
          destruct upds; simpl in *; auto.
          repeat intro; simpl in *.
          contradiction.
          apply H2. left. reflexivity.
          rewrite <- HConsistent.
          unfold SubList. intros.
          simpl in *. destruct H; subst; auto. contradiction.
      - apply H2. simpl in *.
        destruct upds. inversion H.
        simpl in H. simpl in *. right. assumption.
    }
    assert (forall s, In s (map fst newRegs0) ->
            ~ In s (map fst (hd nil
                        ((hd nil upds ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds)))) as P2.
    {
      repeat intro.
      simpl in *.
      rewrite map_app in H0.
      simpl in *. apply in_app_iff in H0.
      destruct H0.
      destruct upds; subst. inversion H0.
      simpl in *.
      eapply HCheck. right. apply H.
      assumption.
      simpl in *. destruct H0.
      subst. apply H4. assumption.
      assumption.
     }
     specialize (IHa _ _ _ _ HSemAction H5 _ _ _ HConsistent P2 P0 P1); dest; simpl in *.
    exists x; repeat split; auto.
    * destruct newRegs0. assumption.
      rewrite -> H. simpl in *.
      rewrite <- app_assoc. reflexivity.
    * simpl in *.  rewrite <- (app_nil_l calls).
      econstructor; eauto.
      econstructor; eauto.
      unfold WfRegMapExpr; repeat split.
      ++ econstructor. simpl in *.
         reflexivity.
         apply H1. reflexivity.
      ++ destruct P1 with u.
         simpl in *. assumption. assumption.
      ++ simpl in *.
         destruct H3.
         subst.
         repeat intro.
         rewrite map_app in H; simpl in *.
         rewrite in_app_iff in H.
         destruct H.
         destruct upds.
         inv H.
         simpl in *.
         eapply H2.
         left.
         reflexivity.
         assumption.
         inv H.
         rewrite <- HConsistent.
         assumption.
         inv H3.
         destruct upds.
         simpl in *.
         inv H3.
         simpl in *.
         eapply H2; eauto.
  - (* if-else *)
    inv H0; EqDep_subst.
    * rewrite map_app, NoDup_app_iff in H1; dest.
      assert (forall s : string, In s (map fst newRegs1) -> ~ In s (map fst (hd nil upds))) as P3.
      {
        intros.
        eapply HCheck.
        rewrite map_app. apply in_or_app. left. assumption.
      }
      specialize (IHa1 _ _ _ _ HAction H0 _ _  _ HConsistent P3 H2 H3); dest.
      destruct x.
      assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
      apply SemVarRegMap.
      assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P4.
        {
          split. inv H6; simpl in *; subst.
      destruct newRegs1; auto.
      simpl in *. apply H3. assumption.
      simpl in *. destruct H9; auto. subst.
      rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
      * destruct upds; simpl in *. constructor.
        eapply H3. left. reflexivity.
      * assumption.
      * intros;subst.
        unfold not. intro. destruct H9.
        subst. eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H9.
        assumption.
      * intros; subst.
        unfold not. intro. destruct H6; subst.
        eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H6.
        assumption.
      * eapply H3. simpl in *.
        destruct upds. inversion H6.
        simpl in H6. simpl in *. right. assumption.
      * inv H6; subst.
        destruct newRegs1. apply H3. assumption.
        destruct upds. simpl in *.
        destruct H9; [|contradiction]; subst.
        specialize WfSemAction as P0.
        rewrite <- HConsistent.
        specialize (P0 _ a1 o readRegs1 calls1 r1 (p :: newRegs1) HAction).
        assumption.
        simpl in *.
        destruct H9; subst.
        rewrite map_app. rewrite SubList_app_l_iff; split; auto.
        apply H3. left. reflexivity.
         specialize WfSemAction as P0.
        rewrite <- HConsistent.
        specialize (P0 _ a1 o readRegs1 calls1 r1 (p :: newRegs1) HAction).
        assumption.
        apply H3. right. assumption. }
    inversion H6; subst; simpl in *.
    assert (forall s, In s (map fst (newRegs2)) -> ~ In s (map fst (hd nil  (match newRegs1 with
               | nil => upds
               | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
               end)))) as P5.
    {
      intros. simpl in *. destruct newRegs1.
      * unfold not; intros. eapply HCheck.
        simpl in *. apply H9. assumption.

      * unfold not. intros. eapply H5. apply H9. simpl in H10. rewrite map_app in H10.
        apply in_app_or in H10. destruct H10.
      + exfalso.
        eapply H5.
        apply H9. exfalso.
        eapply HCheck. rewrite map_app.
        apply in_or_app. right.
        apply H9. assumption.
      + assumption. }
    inversion H6; subst. simpl in *.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent P5 H8 P4).
    dest.
    exists x; split.
    **  destruct newRegs1. simpl in *. assumption.
    simpl in *. destruct newRegs2.
    simpl in *. rewrite app_nil_r.
    assumption.
    rewrite <- app_assoc in H. assumption.
    **  remember (evalExpr e) as P0.
     assert (forall bexpr, (evalExpr (Const type true && bexpr)%kami_expr = evalExpr bexpr)) as P1.
     { intro; simpl; auto. }
     assert (evalExpr e = evalExpr (Const type true)) as P2.
     { rewrite <- HeqP0. apply HTrue. }
    simpl.
    econstructor. simpl.
    apply SemCompActionEquivBexpr with (bexpr1 := (Const type true)).
    simpl in *. rewrite -> HeqP0 in HTrue. rewrite -> HTrue.
    reflexivity. apply H7.
    assert (evalExpr (!e)%kami_expr = false) as PF.
    { simpl; auto. simpl. rewrite -> P2. simpl; auto. }
    rewrite <- (app_nil_l calls2).  
    econstructor 8 with (regMap_a := (old, match newRegs1 with
                                         | nil => upds
                                         | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                           end)) (val_a := r1).
        *** specialize (FalseSemCompAction_rev) as P12.
            specialize (P1 (!e)%kami_expr). rewrite -> PF in P1.
             assert (WfRegMapExpr (VarRegMap type (old, match newRegs1 with
                             | nil => upds
                             | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                             end)) (old, match newRegs1 with
                                          | nil => upds
                                          | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                         end)).
            {
              unfold WfRegMapExpr in *; auto. }
            specialize (P12 _ a2 o _ _ _ H10 P1).
            assert (WfRegMapExpr (VarRegMap type (old, match newRegs1 with
                             | nil => upds
                             | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                             end)) (old, match newRegs1 with
                                          | nil => upds
                                          | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                         end)).
            {
              unfold WfRegMapExpr in *; auto. }
            admit.
       *** simpl in *. econstructor. simpl in *.
           rewrite -> P2. apply H9.
    * rewrite map_app, NoDup_app_iff in H1; dest.
    assert (forall s : string, In s (map fst newRegs1) -> ~ In s (map fst (hd nil upds))) as P3.
    {
      intros.
      eapply HCheck.
      rewrite map_app. apply in_or_app. left. assumption.
    }
    assert (SemRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as HF.
    { constructor. }
     specialize (IHa2 _ _ _ _ HAction H0 _ _  _ HConsistent P3 HF H3); dest.
      destruct x.
      assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
      apply SemVarRegMap.
      assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P4.
        {
          split. inv H6; simpl in *; subst.
      destruct newRegs1; auto.
      simpl in *. apply H3. assumption.
      simpl in *. destruct H9; auto. subst.
      rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
      * destruct upds; simpl in *. constructor.
        eapply H3. left. reflexivity.
      * assumption.
      * intros;subst.
        unfold not. intro. destruct H9.
        subst. eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H9.
        assumption.
      * intros; subst.
        unfold not. intro. destruct H6; subst.
        eapply HCheck. left. reflexivity.
        assumption.
        eapply HCheck. right. rewrite map_app.
        eapply in_or_app. left. apply H6.
        assumption.
      * eapply H3. simpl in *.
        destruct upds. inversion H6.
        simpl in H6. simpl in *. right. assumption.
      * inv H6; subst.
        destruct newRegs1. apply H3. assumption.
        destruct upds. simpl in *.
        destruct H9; [|contradiction]; subst.
        specialize WfSemAction as P0.
        rewrite <- HConsistent.
        specialize (P0 _ a2 o readRegs1 calls1 r1 (p :: newRegs1) HAction).
        assumption.
        simpl in *.
        destruct H9; subst.
        rewrite map_app. rewrite SubList_app_l_iff; split; auto.
        apply H3. left. reflexivity.
         specialize WfSemAction as P0.
        rewrite <- HConsistent.
        specialize (P0 _ a2 o readRegs1 calls1 r1 (p :: newRegs1) HAction).
        assumption.
        apply H3. right. assumption. }
    inversion H6; subst; simpl in *.
    assert (forall s, In s (map fst (newRegs2)) -> ~ In s (map fst (hd nil  (match newRegs1 with
               | nil => upds
               | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
               end)))) as P5.
    {
      intros. simpl in *. destruct newRegs1.
      * unfold not; intros. eapply HCheck.
        simpl in *. apply H9. assumption.
      * unfold not. intros. eapply H5. apply H9. simpl in H10. rewrite map_app in H10.
        apply in_app_or in H10. destruct H10.
      + exfalso.
        eapply H5.
        apply H9. exfalso.
        eapply HCheck. rewrite map_app.
        apply in_or_app. right.
        apply H9. assumption.
      + assumption.
    }
    inversion H6; subst. simpl in *.
    specialize (H _ _ _ _ _ HSemAction H1 _ _ _ HConsistent P5 H8 P4).
    dest.
    exists x; split.
    **  destruct newRegs1. simpl in *. assumption.
    simpl in *. destruct newRegs2.
    simpl in *. rewrite app_nil_r.
    assumption.
    rewrite <- app_assoc in H. assumption.
    **  remember (evalExpr e) as P0.
     assert (forall bexpr, (evalExpr (Const type true && bexpr)%kami_expr = evalExpr bexpr)) as P1.
     { intro; simpl; auto. }
     assert (evalExpr (!e)%kami_expr = evalExpr (Const type true)) as P2.
     {simpl.  rewrite -> HeqP0 in HFalse. rewrite -> HFalse. auto. }
     rewrite <-(app_nil_l (calls1++calls2)).
     econstructor 8 with (regMap_a := (old, upds)).
        *** (*apply FalseSemCompAction_rev.
            unfold WfRegMapExpr in *; auto. simpl in *.
            split; subst. destruct newRegs1. assumption.*)
            admit.
        *** simpl in *. econstructor 8 with (regMap_a :=  (old, match newRegs1 with
                                                    | nil => upds
                                                    | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                             end)) (val_a := r1) . simpl in *.
            apply SemCompActionEquivBexpr with (bexpr1 := (Const type true)).
            simpl in *. rewrite -> P2. reflexivity. apply H7.
            simpl in *. econstructor. simpl in *.
            rewrite -> HFalse in HeqP0. rewrite <- HeqP0. apply H9.
 - (* Sys *)
    inv H; EqDep_subst.
    specialize (IHa _ _ _ _ HSemAction H0 _ _ _ HConsistent HCheck H1 H2); dest.
    exists x. split.
    * assumption.
    * econstructor; eauto.
  - (* Return *)
    inv H; EqDep_subst.
    exists (old, upds).
    split. reflexivity.
    destruct upds.
    simpl in *. constructor. reflexivity.
    unfold WfRegMapExpr. split; auto.
    econstructor. reflexivity.
    unfold WfRegMapExpr. split; eauto.
Admitted.

      
End DoubleWritesProof.      


 
