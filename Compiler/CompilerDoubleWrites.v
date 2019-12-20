Require Import Kami.SyntaxDoubleWrites Kami.Compiler.Compiler Kami.Compiler.CompilerProps Kami.Syntax Kami.Properties Kami.PProperties Kami.PPlusProperties Kami.Lib.EclecticLib Kami.Notations.

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
      assert (val_a = evalExpr (Const type (ZToWord 0 0))) as P0.
      {specialize (unique_word_0 val_a). intros. auto. }
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
      inv HSemCompActionT; simpl in *; EqDep_subst.
      inv HSemCompActionT0; simpl in *; EqDep_subst.
      inversion HSemCompActionT_cont; simpl in *; EqDep_subst.
      inversion HSemCompActionT_cont0; simpl in *; EqDep_subst.
      remember (evalExpr e) as P0.
      destruct P0; simpl in *.
      * assert (forall b, (evalExpr (Var type (SyntaxKind Bool) b)) = evalExpr (Const type b)) as P4; auto.
         specialize (SemCompActionEquivBexpr _ _ _ _ _ (P4 true) HSemCompActionT_a) as P6.
         rewrite <- HeqP0 in *; simpl in HSemCompActionT.
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
      * assert (forall b, (evalExpr (Var type (SyntaxKind Bool) b)) = evalExpr (Const type b)) as P4; auto.
        specialize (SemCompActionEquivBexpr _ _ _ _ _ (P4 true) HSemCompActionT_a0) as P6.
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

  Lemma getRegisterValue (k : FullKind) (o : RegsT):
    forall r,
      In (r, k) (getKindAttr o) ->
      exists v,
        In (r, existT (fullType type) k v) o.
  Proof.
    intros. simpl in *.
    rewrite in_map_iff in H.
    dest. inv H.
    destruct x; subst.
    destruct s0; subst. simpl in *.
    exists f; auto.
  Qed.


  Lemma FalseSemCompAction (k : Kind) (a : ActionT type k) (o oInit : RegsT) uInit (m : BaseModule):
    forall regMap regMapExpr (bexpr : Bool @# type) (WfRegMap : WfRegMapExpr regMapExpr regMap) (HPriorityUpds : PriorityUpds oInit uInit o) ,
      getKindAttr o = getKindAttr (getRegisters m) ->
      getKindAttr oInit = getKindAttr (getRegisters m) ->
      WfActionT m a -> 
      evalExpr bexpr = false ->
      exists retl,
        SemCompActionT (compileAction (oInit,uInit) a bexpr regMapExpr) regMap nil retl.
  Proof.
    induction a; simpl in *; subst.
    - (* Meth Call *)
      intros.
      inversion H2; EqDep_subst.
      specialize (H6 (evalConstT (getDefaultConst (snd s)))).
      specialize (H (evalConstT (getDefaultConst (snd s))) _ _ _ WfRegMap HPriorityUpds H0 H1 H6 H3).
      destruct H.
      exists x.
      econstructor 2. eapply H. assumption.
    - (* Let expr *)
      intros.
      inversion H2; EqDep_subst.
      specialize (H6 (evalExpr e)).
      specialize (H (evalExpr e) _ _ _ WfRegMap HPriorityUpds H0 H1 H6 H3).
      destruct H.
      exists x.
      econstructor. assumption.
    - (* Let Action *)
      intros.
      inversion H2; EqDep_subst.
      specialize (IHa _ _ _ WfRegMap HPriorityUpds H0 H1 H7 H3).
      destruct IHa.
      assert (WfRegMapExpr (VarRegMap type regMap) regMap).
      {
        unfold WfRegMapExpr in *; split; eauto.
        constructor.
        destruct WfRegMap. assumption.
      }
      specialize (H9 x).
      specialize (H x _ _ _ H5 HPriorityUpds H0 H1 H9 H3).
      destruct H. exists x0.
      rewrite <- (app_nil_r (nil : MethsT)).
      econstructor; eauto.
    - (* Non Det *)
      intros.
      inversion H2; EqDep_subst.
      specialize (H6 (evalConstFullT (getDefaultConstFullKind k))).
      specialize (H (evalConstFullT (getDefaultConstFullKind k)) _ _ _ WfRegMap HPriorityUpds H0 H1 H6 H3).
      destruct H.
      exists x.
      econstructor.
      apply H.
    -(* Read *)
      intros.
      inversion H2; EqDep_subst.
      specialize (getRegisterValue); intros.
      rewrite <- H0 in H9.
      specialize (H4 _ _ _ H9).
      destruct H4.
      specialize (H7 x).
      specialize (H x _ _ _ WfRegMap HPriorityUpds H0 H1 H7 H3).
      destruct H. exists x0.
      econstructor; eauto.
      constructor. 
    -(* Write *)
      intros.
      assert (WfRegMapExpr (VarRegMap type regMap) regMap).
      {
        unfold WfRegMapExpr in *; split; eauto.
        constructor.
        destruct WfRegMap. assumption.
      }
      inversion H1; EqDep_subst.
      specialize (IHa _ _ _ H3 HPriorityUpds H H0 H7 H2).
      destruct IHa.
      exists x. simpl in *.
      rewrite <- (app_nil_r (nil : MethsT)).
      econstructor. econstructor. reflexivity.
      unfold WfRegMapExpr in *; dest; repeat split; eauto.
      destruct regMap.
      econstructor 3; eauto.
      reflexivity.
      assumption.
    -(* If-else *)
      intros. 
      assert ((evalExpr (bexpr && !e)%kami_expr = evalExpr bexpr)) as P1.
      { simpl. rewrite -> H3. simpl. destruct (evalExpr e). simpl. reflexivity.
        reflexivity. }
      assert ((evalExpr (bexpr && e)%kami_expr = false)) as P2.
      { simpl. rewrite -> H3. simpl. reflexivity. }
      inversion H2; EqDep_subst.
      specialize (IHa1 _ _ _ WfRegMap HPriorityUpds H0 H1 H11 H3).
      destruct IHa1.
      assert (WfRegMapExpr (VarRegMap type regMap) regMap).
      {
        unfold WfRegMapExpr in *; split; eauto.
        constructor.
        destruct WfRegMap. assumption.
      }
      rewrite -> H3 in P1.
      specialize (IHa2 _ _ _ H5 HPriorityUpds H0 H1 H12 P2).
      remember (evalExpr e) as P0.
      destruct IHa2.
      destruct P0.
      * specialize (H8 x).
        specialize (H x _ _ _ H5 HPriorityUpds H0 H1 H8 P2).
        destruct H.
        exists x1.  rewrite <- (app_nil_r (nil : MethsT)).
        do 3 econstructor. simpl in *.
        apply  SemCompActionEquivBexpr with (bexpr1 := bexpr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H4.
        reflexivity.
        rewrite <- (app_nil_r (nil : MethsT)).
        econstructor.
        apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && e)%kami_expr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H6.
        reflexivity.
        simpl. econstructor. simpl.
        rewrite <- HeqP0.
        apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && e)%kami_expr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H.
      * specialize (H8 x0).
        specialize (H x0 _ _ _ H5 HPriorityUpds H0 H1 H8 P2).
        destruct H.
        exists x1.  rewrite <- (app_nil_r (nil : MethsT)).
        do 3 econstructor. simpl in *.
        apply  SemCompActionEquivBexpr with (bexpr1 := bexpr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H4.
        reflexivity.
        rewrite <- (app_nil_r (nil : MethsT)).
        econstructor.
        apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && e)%kami_expr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H6.
        reflexivity.
        simpl. econstructor. simpl.
        rewrite <- HeqP0.
        apply SemCompActionEquivBexpr with (bexpr1 := (bexpr && e)%kami_expr).
        simpl. rewrite -> H3. simpl. reflexivity.
        apply H.
    - (* Sys *)
      intros.
      inversion H1; EqDep_subst.
      specialize (IHa _ _ _ WfRegMap HPriorityUpds H H0 H5 H2).
      destruct IHa.
      exists x. econstructor. apply H3.
    - (* Ret *)
      intros.
      inversion H1; EqDep_subst.
      exists (evalExpr e).
      econstructor. reflexivity.
      assumption.
  Qed.


  Lemma EquivActionNoDupWritesNew (k : Kind) (a : ActionT type k) (o oInit: RegsT) uInit  (m : BaseModule)
        (HoInitNoDups : NoDup (map fst oInit))
        (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
        (HPriorityUpds : PriorityUpds oInit uInit o)
        (HOgetReg : getKindAttr o = getKindAttr (getRegisters m)) :
    forall newRegs readRegs calls retl,
      SemActionDoubleWrites o a readRegs newRegs calls retl ->
      NoDup (map fst newRegs) ->
      getKindAttr oInit = getKindAttr (getRegisters m) ->
      WfActionT m a -> 
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
          SemCompActionT (compileAction (oInit, uInit) a (Const type true) writeMap) upds' calls retl.
  Proof.
    induction a; subst; intros; simpl in *.
    - (* Meth Call *)
      inv H0; EqDep_subst.
      inv H3; EqDep_subst.
      specialize (H7 mret).
      specialize (H _ _ _ _ _ HSemAction H1 H2 H7 _ _ _ HConsistent HCheck H4 H5); dest.
      exists x. split.
      * assumption.
      * econstructor; eauto.
    - (* Let expr *)
      inv H0; EqDep_subst.
      inv H3; EqDep_subst.
      specialize (H7 (evalExpr e)).
      specialize (H _ _ _ _ _ HSemAction H1 H2 H7 _ _ _ HConsistent HCheck H4 H5); dest.
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
      inv H3; EqDep_subst.
      specialize (H13 v).
      specialize (IHa _ _ _ _ HSemAction H0 H2 H11 _ _ _  HConsistent P0 H4 H5); dest.
      destruct x.
      assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
      apply SemVarRegMap.
      assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P1.
      {
        split. inv H3; simpl in *; subst.
        destruct newRegs0; auto.
        simpl in *. apply H5. assumption.
        simpl in *. destruct H10; auto. subst.
        rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
        * destruct upds; simpl in *. constructor.
          eapply H5. left. reflexivity.
        * assumption.
        * intros;subst.
          unfold not. intro. destruct H10.
          subst. eapply HCheck. left. reflexivity.
          assumption.
          eapply HCheck. right. rewrite map_app.
          eapply in_or_app. left. apply H10.
          assumption.
        * intros; subst.
          unfold not. intro. destruct H3; subst.
          eapply HCheck. left. reflexivity.
          assumption.
          eapply HCheck. right. rewrite map_app.
          eapply in_or_app. left. apply H3.
          assumption.
        * eapply H5. simpl in *.
          destruct upds. inversion H3.
          simpl in H6. simpl in *. right. assumption.
        * inv H3; subst.
          destruct newRegs0. apply H5. assumption.
          destruct upds. simpl in *.
          destruct H10; [|contradiction]; subst.
          specialize getKindAttr_consistent as P1.
          rewrite <- HConsistent.
          specialize (P1 _ a o  (p :: newRegs0) readRegs0 calls0 v HSemAction).
          assumption.
          simpl in *.
          destruct H10; subst.
          rewrite map_app. rewrite SubList_app_l_iff; split; auto.
          apply H5. left. reflexivity.
          specialize getKindAttr_consistent as P1.
          rewrite <- HConsistent.
          specialize (P1 _ a o  (p :: newRegs0) readRegs0 calls0 v HSemAction).
          assumption.
          apply H5. right. assumption. }
      inversion H3; subst; simpl in *.
      assert (forall s, In s (map fst (newRegsCont)) -> ~ In s (map fst (hd nil  match newRegs0 with
                                                                                 | nil => upds
                                                                                 | _ :: _ => (hd nil upds ++ newRegs0) :: tl upds
                                                                                 end))) as P2.
      {
        intros. simpl in *. destruct newRegs0.
        * unfold not; intros. eapply HCheck.
          simpl in *. apply H10. assumption.
        * unfold not. intros. eapply H7. apply H10. simpl in H12. rewrite map_app in H12.
          apply in_app_or in H12. destruct H12.
        + exfalso.
          eapply H7.
          apply H10. exfalso.
          eapply HCheck. rewrite map_app.
          apply in_or_app. right.
          apply H10. assumption.
        + assumption.
      }
      inversion H3; subst. simpl in *.
      specialize (H _ _ _ _ _ HSemActionCont H1 H2 H13 _ _ _ HConsistent P2 H9 P1).
      dest.
      exists x; split.
      * inversion H3; subst.
        destruct newRegs0. destruct newRegsCont; simpl in *; reflexivity.
        simpl in *. destruct newRegsCont. simpl in *. rewrite app_nil_r. reflexivity.
        rewrite app_comm_cons. rewrite app_assoc. reflexivity.
      * econstructor; eauto.
    - (* Non Det *)
      inv H0; EqDep_subst.
      inv H3; EqDep_subst.
      specialize (H7 valueV).
      specialize (H _ _ _ _ _ HSemAction H1 H2 H7 _ _ _ HConsistent HCheck H4 H5); dest.
      exists x. split.
      * assumption.
      * econstructor; eauto.
    - (* Read *)
      inv H0; EqDep_subst.
      inv H3; EqDep_subst.
      specialize (H8 regV).
      specialize (H _ _ _ _ _ HSemAction H1 H2 H8 _ _ _ HConsistent HCheck H4 H5); dest.
      exists x. split.
      * assumption.
      * econstructor; eauto.
        apply SemVarRegMap.
    - (* Write *)
      inv H; EqDep_subst.
      inv H0.
      inv H2; EqDep_subst.
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
            * clear - H4.
              destruct upds; simpl in *;[constructor|].
              eapply H4.
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
            apply H4. left. reflexivity.
            rewrite <- HConsistent.
            unfold SubList. intros.
            simpl in *. destruct H; subst; auto. contradiction.
        - apply H4. simpl in *.
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
        subst. apply H6. assumption.
        assumption.
      }
      specialize (IHa _ _ _ _ HSemAction H7 H1 H8 _ _ _ HConsistent P2 P0 P1); dest; simpl in *.
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
           apply H3. reflexivity.
        ++ destruct P1 with u.
           simpl in *. assumption. assumption.
        ++ simpl in *.
           destruct H2.
           subst.
           repeat intro.
           rewrite map_app in H; simpl in *.
           rewrite in_app_iff in H.
           destruct H.
           destruct upds.
           inv H.
           simpl in *.
           eapply H4.
           left.
           reflexivity.
           assumption.
           inv H.
           rewrite <- HConsistent.
           assumption.
           inv H2.
           destruct upds.
           simpl in *.
           inv H2.
           simpl in *.
           eapply H4; eauto.
    - (* if-else *)
      inv H0; EqDep_subst.
      inv H3; EqDep_subst.
      * rewrite map_app, NoDup_app_iff in H1; dest.
        assert (forall s : string, In s (map fst newRegs1) -> ~ In s (map fst (hd nil upds))) as P3.
        {
          intros.
          eapply HCheck.
          rewrite map_app. apply in_or_app. left. assumption.
        }
        specialize (IHa1 _ _ _ _ HAction H0 H2 H12 _ _  _ HConsistent P3 H4 H5); dest.
        destruct x.
        assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
        apply SemVarRegMap.
        assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P4.
        {
          split. inv H7; simpl in *; subst.
          destruct newRegs1; auto.
          simpl in *. apply H5. assumption.
          simpl in *. destruct H11; auto. subst.
          rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
          * destruct upds; simpl in *. constructor.
            eapply H5. left. reflexivity.
          * assumption.
          * intros;subst.
            unfold not. intro. destruct H11.
            subst. eapply HCheck. left. reflexivity.
            assumption.
            eapply HCheck. right. rewrite map_app.
            eapply in_or_app. left. apply H11.
            assumption.
          * intros; subst.
            unfold not. intro. destruct H7; subst.
            eapply HCheck. left. reflexivity.
            assumption.
            eapply HCheck. right. rewrite map_app.
            eapply in_or_app. left. apply H7.
            assumption.
          * eapply H5. simpl in *.
            destruct upds. inversion H7.
            simpl in H7. simpl in *. right. assumption.
          * inv H7; subst.
            destruct newRegs1. apply H5. assumption.
            destruct upds. simpl in *.
            destruct H11; [|contradiction]; subst.
            specialize getKindAttr_consistent as P0.
            rewrite <- HConsistent.
            specialize (P0 _ a1 o  (p :: newRegs1) readRegs1 calls1 r1 HAction).
            assumption.
            simpl in *.
            destruct H11; subst.
            rewrite map_app. rewrite SubList_app_l_iff; split; auto.
            apply H5. left. reflexivity.
            specialize getKindAttr_consistent as P0.
            rewrite <- HConsistent.
            specialize (P0 _ a1 o  (p :: newRegs1) readRegs1 calls1 r1 HAction).
            assumption.
            apply H5. right. assumption. }
        inversion H7; subst; simpl in *.
        assert (forall s, In s (map fst (newRegs2)) -> ~ In s (map fst (hd nil  (match newRegs1 with
                                                                                 | nil => upds
                                                                                 | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                                                                 end)))) as P5.
        {
          intros. simpl in *. destruct newRegs1.
          * unfold not; intros. eapply HCheck.
            simpl in *. apply H11. assumption.
          * unfold not. intros. eapply H6. apply H11. simpl in H14. rewrite map_app in H14.
            apply in_app_or in H14. destruct H14.
          + exfalso.
            eapply H6.
            apply H11. exfalso.
            eapply HCheck. rewrite map_app.
            apply in_or_app. right.
            apply H11. assumption.
          + assumption. }
        inversion H7; subst. simpl in *.
        specialize (H9 r1).
        specialize (H _ _ _ _ _ HSemAction H1 H2 H9 _ _ _ HConsistent P5 H10 P4).
        dest.
        exists x; split.
        **  destruct newRegs1. simpl in *. assumption.
            simpl in *. destruct newRegs2.
            simpl in *. rewrite app_nil_r.
            assumption.
            rewrite <- app_assoc in H. assumption.
        ** remember (evalExpr e) as P0.
           assert (forall bexpr, (evalExpr (Const type true && bexpr)%kami_expr = evalExpr bexpr)) as P1.
           { intro; simpl; auto. }
           assert (evalExpr e = evalExpr (Const type true)) as P2.
           { rewrite <- HeqP0. apply HTrue. }
           simpl.
           specialize (FalseSemCompAction) as P12.
           assert (evalExpr (!e)%kami_expr = false) as PF.
           { simpl; auto. simpl. rewrite -> P2. simpl; auto. }
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
           do 3 econstructor.
           apply SemCompActionEquivBexpr with (bexpr1 := (Const type true)).
           simpl in *. rewrite -> HeqP0 in HTrue. rewrite -> HTrue.
           reflexivity. apply H8. reflexivity.
           specialize (P12 _ a2 o oInit uInit _ _ _ _ H14 HPriorityUpds HOgetReg H2 H13 P1).
           destruct P12.
           rewrite <- (app_nil_l calls2).
           econstructor 8 with (regMap_a := (old, match newRegs1 with
                                                  | nil => upds
                                                  | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                                  end)) (val_a := x0).
           eapply SemCompActionEquivBexpr with (bexpr1 := (Const type true && ! e)%kami_expr); eauto.
           reflexivity.
           simpl in *. econstructor. simpl in *.
           rewrite -> P2. apply H11.
      * rewrite map_app, NoDup_app_iff in H1; dest.
        assert (forall s : string, In s (map fst newRegs1) -> ~ In s (map fst (hd nil upds))) as P3.
        {
          intros.
          eapply HCheck.
          rewrite map_app. apply in_or_app. left. assumption.
        }
        assert (SemRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as HF.
        { constructor. }
        inv H3; EqDep_subst.
        specialize (IHa2 _ _ _ _ HAction H0 H2 H16 _ _  _ HConsistent P3 HF H5); dest.
        destruct x.
        assert (SemRegMapExpr (VarRegMap type (l, l0)) (l, l0)).
        apply SemVarRegMap.
        assert (forall u, In u l0 -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old) ) as P4.
        {
          split. inv H3; simpl in *; subst.
          destruct newRegs1; auto.
          simpl in *. apply H5. assumption.
          simpl in *. destruct H10; auto. subst.
          rewrite map_app. rewrite NoDup_app_iff; simpl in *; repeat split.
          * destruct upds; simpl in *. constructor.
            eapply H5. left. reflexivity.
          * assumption.
          * intros;subst.
            unfold not. intro. destruct H10.
            subst. eapply HCheck. left. reflexivity.
            assumption.
            eapply HCheck. right. rewrite map_app.
            eapply in_or_app. left. apply H10.
            assumption.
          * intros; subst.
            unfold not. intro. destruct H3; subst.
            eapply HCheck. left. reflexivity.
            assumption.
            eapply HCheck. right. rewrite map_app.
            eapply in_or_app. left. apply H3.
            assumption.
          * eapply H5. simpl in *.
            destruct upds. inversion H3.
            simpl in H7. simpl in *. right. assumption.
          * inv H3; subst.
            destruct newRegs1. apply H5. assumption.
            destruct upds. simpl in *.
            destruct H10; [|contradiction]; subst.
            specialize getKindAttr_consistent as P0.
            rewrite <- HConsistent.
            specialize (P0 _ a2 o  (p :: newRegs1) readRegs1 calls1 r1 HAction).
            assumption.
            simpl in *.
            destruct H10; subst.
            rewrite map_app. rewrite SubList_app_l_iff; split; auto.
            apply H5. left. reflexivity.
            specialize getKindAttr_consistent as P0.
            rewrite <- HConsistent.
            specialize (P0 _ a2 o  (p :: newRegs1) readRegs1 calls1 r1 HAction).
            assumption.
            apply H5. right. assumption. }
        inversion H3; subst; simpl in *.
        assert (forall s, In s (map fst (newRegs2)) -> ~ In s (map fst (hd nil  (match newRegs1 with
                                                                                 | nil => upds
                                                                                 | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                                                                 end)))) as P5.
        {
          intros. simpl in *. destruct newRegs1.
          * unfold not; intros. eapply HCheck.
            simpl in *. apply H10. assumption.
          * unfold not. intros. eapply H7. apply H10. simpl in H11. rewrite map_app in H11.
            apply in_app_or in H11. destruct H11.
          + exfalso.
            eapply H7.
            apply H10. exfalso.
            eapply HCheck. rewrite map_app.
            apply in_or_app. right.
            apply H10. assumption.
          + assumption.
        }
        inversion H3; subst. simpl in *.
        specialize (H12 r1).
        specialize (H _ _ _ _ _ HSemAction H1 H2 H12 _ _ _ HConsistent P5 H9 P4).
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
            specialize (FalseSemCompAction) as P12.
            assert (evalExpr (!e)%kami_expr = true) as PF.
            { simpl; auto. }
            specialize (P1 (!e)%kami_expr). rewrite -> PF in P1.
            assert (WfRegMapExpr writeMap (old, upds)).
            { 
              unfold WfRegMapExpr in *; auto. }
            rewrite <-(app_nil_l (calls1++calls2)).
            assert (evalExpr (Const type true && e)%kami_expr = false).
            {
              simpl. rewrite -> HFalse in HeqP0; auto. }
            specialize (P12 _ a1 o oInit uInit _ _ _ _ H11 HPriorityUpds HOgetReg H2 H15 H13).
            destruct P12.
            do 2 econstructor; econstructor 8 with (regMap_a := (old, upds)) (val_a := x0).
            eapply SemCompActionEquivBexpr with (bexpr1 := (Const type true && e)%kami_expr); eauto.
            reflexivity.
            simpl in *. econstructor 8 with (regMap_a :=  (old, match newRegs1 with
                                                                | nil => upds
                                                                | _ :: _ => (hd nil upds ++ newRegs1) :: tl upds
                                                                end)) (val_a := r1) . simpl in *.
            apply SemCompActionEquivBexpr with (bexpr1 := (Const type true)).
            simpl in *. rewrite -> P2. reflexivity. apply H8.
            simpl in *. reflexivity. econstructor. simpl in *.
            rewrite -> HFalse in HeqP0. rewrite <- HeqP0. apply H10.
    - (* Sys *)
      inv H; EqDep_subst.
      inv H2; EqDep_subst.
      specialize (IHa _ _ _ _ HSemAction H0 H1 H6  _ _ _ HConsistent HCheck H3 H4); dest.
      exists x. split.
      * assumption.
      * econstructor; eauto.
    - (* Return *)
      inv H; EqDep_subst.
      inv H2; EqDep_subst.
      exists (old, upds).
      split. reflexivity.
      destruct upds.
      simpl in *. constructor. reflexivity.
      unfold WfRegMapExpr. split; auto.
      econstructor. reflexivity.
      unfold WfRegMapExpr. split; auto.
  Qed.

End DoubleWritesProof.      
