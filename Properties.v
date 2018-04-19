Require Import Kami.Syntax.

Import ListNotations.

Section evalExpr.
  
  Lemma castBits_same ty ni no (pf: ni = no) (e: Expr ty (SyntaxKind (Bit ni))): castBits pf e = match pf in _ = Y return Expr ty (SyntaxKind (Bit Y)) with
                                                                                                 | eq_refl => e
                                                                                                 end.
  Proof.
    unfold castBits.
    destruct pf.
    rewrite nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_castBits: forall ni no (pf: ni = no) (e: Bit ni @# type), evalExpr (castBits pf e) =
                                                                           nat_cast (fun n => word n) pf (evalExpr e).
  Proof.
    intros.
    unfold castBits.
    destruct pf.
    rewrite ?nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_BinBit: forall kl kr k (op: BinBitOp kl kr k)
                                (l1 l2: Bit kl @# type)
                                (r1 r2: Bit kr @# type),
    evalExpr l1 = evalExpr l2 ->
    evalExpr r1 = evalExpr r2 ->
    evalExpr (BinBit op l1 r1) = evalExpr (BinBit op l2 r2).
  Proof.
    intros.
    induction op; simpl; try congruence.
  Qed.

  Lemma evalExpr_ZeroExtend: forall lsb msb (e1 e2: Bit lsb @# type), evalExpr e1 = evalExpr e2 ->
                                                                      evalExpr (ZeroExtend msb e1) = evalExpr (ZeroExtend msb e2).
  Proof.
    intros.
    unfold ZeroExtend.
    erewrite evalExpr_BinBit; eauto.
  Qed.

  Lemma evalExpr_pack_Bool: forall (e1 e2: Bool @# type),
      evalExpr e1 = evalExpr e2 ->
      evalExpr (pack e1) = evalExpr (pack e2).
  Proof.
    intros.
    simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma evalExpr_Void (e: Expr type (SyntaxKind (Bit 0))):
    evalExpr e = WO.
  Proof.
    inversion e; auto.
  Qed.

  Lemma evalExpr_countLeadingZeros ni: forall no (e: Expr type (SyntaxKind (Bit ni))),
      evalExpr (countLeadingZeros no e) = countLeadingZerosWord no (evalExpr e).
  Proof.
    induction ni; simpl; intros; auto.
    rewrite evalExpr_castBits.
    simpl.
    unfold wzero at 2.
    rewrite wzero_wplus.
    match goal with
    | |- (if getBool ?P then _ else _) = (if ?P then _ else _) => destruct P; auto
    end.
    repeat f_equal.
    rewrite IHni.
    simpl.
    rewrite evalExpr_castBits.
    repeat f_equal.
  Qed.




  Lemma evalExpr_pack: forall k (e1 e2: k @# type),
      evalExpr e1 = evalExpr e2 ->
      evalExpr (pack e1) = evalExpr (pack e2).
  Proof.
    intros.
    induction k; simpl; rewrite ?H; try auto.
    admit.
    admit.
  Admitted.
End evalExpr.



Lemma UpdRegs_same: forall u o o', UpdRegs u o o' -> UpdRegs' u o o'.
Proof.
  unfold UpdRegs, UpdRegs'.
  intros; dest.
  apply (f_equal (map fst)) in H.
  rewrite ?map_map in H; simpl in *.
  setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; tauto.
Qed.


Lemma SignT_dec: forall k1 k2 (s1 s2: SignT (k1, k2)), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  simpl in *.
  apply prod_dec; simpl; auto; apply isEq.
Qed.

Lemma sigT_SignT_dec: forall s1 s2: (sigT SignT), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  destruct (Signature_dec x x0); subst.
  - destruct (SignT_dec s s0); subst.
    + left; reflexivity.
    + right; intro.
      apply EqdepFacts.eq_sigT_eq_dep in H.
      apply (Eqdep_dec.eq_dep_eq_dec (Signature_dec)) in H.
      tauto.
  - right; intro.
    inversion H.
    tauto.
Qed.

Lemma MethT_dec: forall s1 s2: MethT, {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  apply prod_dec.
  - apply string_dec.
  - apply sigT_SignT_dec.
Qed.

Lemma getKindAttr_map_fst A (P Q: A -> Type)
  : forall (l2: list (Attribute (sigT P))) (l1: list (Attribute (sigT Q))),
    getKindAttr l1 = getKindAttr l2 ->
    map fst l1 = map fst l2.
Proof.
  induction l2; simpl; auto; intros.
  - apply map_eq_nil in H; subst; auto.
  - destruct l1; simpl in *.
    + discriminate.
    + inv H; f_equal.
      apply IHl2; auto.
Qed.

Lemma Step_getAllRegisters m o l:
  Step m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; auto; simpl.
  - inv HSubsteps; auto.
  - rewrite map_app.
    rewrite <- IHStep1, <- IHStep2, HRegs.
    rewrite map_app.
    auto.
Qed.

Lemma Step_getAllRegisters_fst m o l:
  Step m o l ->
  map fst o = map fst (getAllRegisters m).
Proof.
  intros.
  apply Step_getAllRegisters in H.
  eapply getKindAttr_map_fst; eauto.
Qed.

Lemma DisjRegs_1_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_1_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.

Lemma Substeps_rm_In m o l:
  Substeps m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getMethods m)))
             end = true.
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getRules m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInRules)).
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getMethods m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInMeths)).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_In m o l:
  Step m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m)))
             end = true.
Proof.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_In; eauto.
  - subst.
    specialize (IHStep1 fv).
    specialize (IHStep2 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite in_app_iff in *.
    + destruct (in_dec string_dec b (map fst (getAllRules m1))),
      (in_dec string_dec b (map fst (getAllRules m2))); simpl in *; tauto.
    + destruct (in_dec string_dec s (map fst (getAllMethods m1))),
      (in_dec string_dec s (map fst (getAllMethods m2))); simpl in *; tauto.
Qed.

Lemma Substeps_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getRules m2) ->
  DisjKey (getAllMethods m1) (getMethods m2) ->
  Substeps m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros; subst; try tauto.
  - destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getAllRules m1))); simpl; auto.
      apply (in_map fst) in HInRules.
      clear - DisjRules DisjMeths HInRules i; firstorder.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getAllMethods m1))); simpl; auto.
      apply (in_map fst) in HInMeths.
      clear - DisjRules DisjMeths HInMeths i; firstorder.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_not_In; eauto.
  - subst.
    assert (sth1: DisjKey (getAllRules m1) (getAllRules m0)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth2: DisjKey (getAllMethods m1) (getAllMethods m0)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    assert (sth3: DisjKey (getAllRules m1) (getAllRules m2)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth4: DisjKey (getAllMethods m1) (getAllMethods m2)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    specialize (IHStep1 sth1 sth2 fv).
    specialize (IHStep2 sth3 sth4 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite ?in_app_iff in *; simpl in *; firstorder fail.
Qed.
  
Lemma DisjMeths_1_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m1 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_not_In; eauto.
  - eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m2 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_In; eauto.
  - eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.
  
Lemma DisjMeths_1_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m1 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_true_iff.
      eapply Step_rm_not_In; eauto.
  - setoid_rewrite negb_false_iff.
    eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m2 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_false_iff.
      eapply Step_rm_In; eauto.
  - setoid_rewrite negb_true_iff.
    eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.

Lemma Substeps_upd_SubList_key m o l:
  Substeps m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - simpl in *; tauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Substeps_upd_In m o l:
  Substeps m o l ->
  forall x, In x (map fst l) ->
            forall s: string, In s (map fst x) ->
                              In s (map fst (getRegisters m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest; subst.
  destruct x0; simpl.
  eapply Substeps_upd_SubList_key; eauto.
Qed.

Lemma Substeps_read m o l:
  Substeps m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
Qed.
  
Lemma Step_upd_SubList_key m o l:
  Step m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_upd_SubList_key; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 x s v).
    specialize (IHStep2 x s v).
    tauto.
Qed.

Lemma Step_read m o l:
  Step m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_read; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 s v).
    specialize (IHStep2 s v).
    tauto.
Qed.
 
Section SplitJoin.
  Variable m1 m2: Mod.

  Variable DisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2).
  Variable DisjRules: DisjKey (getAllRules m1) (getAllRules m2).
  Variable DisjMethods: DisjKey (getAllMethods m1) (getAllMethods m2).

  Lemma SplitStep o l:
    Step (ConcatMod m1 m2) o l ->
    Step m1 (filterRegs id m1 o) (filterExecs id m1 l) /\
    Step m2 (filterRegs id m2 o) (filterExecs id m2 l) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    MatchingExecCalls (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
    MatchingExecCalls (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
    (forall x y : FullLabel,
        In x (filterExecs id m1 l) ->
        In y (filterExecs id m2 l) ->
        match fst (snd x) with
        | Rle _ => match fst (snd y) with
                   | Rle _ => False
                   | Meth _ => True
                   end
        | Meth _ => True
        end) /\
    (forall x : MethT, InCall x (filterExecs id m1 l) -> InCall x (filterExecs id m2 l) -> False) /\
    l = filterExecs id m1 l ++ filterExecs id m2 l.
  Proof.
    intros H.
    inv H; intros.
    pose proof (Step_getAllRegisters_fst HStep1) as HRegs1.
    pose proof (Step_getAllRegisters_fst HStep2) as HRegs2.
    unfold filterRegs.
    rewrite DisjRegs_1_id with (l2 := getAllRegisters m2) (o1 := o1),
                               DisjRegs_2_id with (l1 := getAllRegisters m1) (o2 := o2); auto.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2), DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    Opaque MatchingExecCalls.
    repeat split; auto.
  Qed.

  Lemma Step_upd_1 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m1)) ->
      In x (map fst (filterExecs id m1 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H0 _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.
    
  Lemma Step_upd_2 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m2)) ->
      In x (map fst (filterExecs id m2 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.
  
  Lemma SplitTrace o ls:
    Trace (ConcatMod m1 m2) o ls ->
    Trace m1 (filterRegs id m1 o) (map (filterExecs id m1) ls) /\
    Trace m2 (filterRegs id m2 o) (map (filterExecs id m2) ls) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    mapProp
      (fun l =>
         MatchingExecCalls (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
         MatchingExecCalls (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
         (forall x y : FullLabel,
             In x (filterExecs id m1 l) ->
             In y (filterExecs id m2 l) ->
             match fst (snd x) with
             | Rle _ => match fst (snd y) with
                        | Rle _ => False
                        | Meth _ => True
                        end
             | Meth _ => True
             end) /\
         (forall x : MethT, InCall x (filterExecs id m1 l) -> InCall x (filterExecs id m2 l) -> False) /\
         l = filterExecs id m1 l ++ filterExecs id m2 l) ls /\
  map fst o = map fst (getAllRegisters (ConcatMod m1 m2)).
  Proof.
    Opaque MatchingExecCalls.
    induction 1; subst; simpl.
    - unfold filterRegs, filterExecs; simpl.
      rewrite ?map_app, ?filter_app.
      unfold id in *.
      pose proof (filter_In_map_same string_dec
                                     (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                     (getAllRegisters m1)) as sth1.
      pose proof (filter_DisjKeys string_dec
                                  (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                  DisjRegs) as sth2.
      pose proof (filter_In_map_same string_dec
                                     (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                     (getAllRegisters m2)) as sth3.
      assert (DisjRegs': DisjKey (getAllRegisters m2) (getAllRegisters m1)) by
          (clear - DisjRegs; firstorder).
      pose proof (filter_DisjKeys string_dec
                                  (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                  DisjRegs') as sth4.
      simpl in *.
      rewrite ?sth1, ?sth2, ?sth3, ?sth4, ?app_nil_r.
      simpl.
      repeat split; try constructor; auto.
      rewrite ?map_map, ?map_app.
      simpl.
      rewrite ?sth5; auto.
    - pose proof HStep as HStep'.
      apply SplitStep in HStep.
      dest.
      repeat split; try econstructor 2; eauto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H13; auto.
        * unfold filterRegs, id in H15.
          rewrite filter_In in H15; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m1))); [simpl in *| discriminate].
          specialize (H14 _ _ H15).
          destruct H14; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_1; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H17.
                rewrite in_map_iff in H17; dest.
                rewrite filter_In in H20; dest.
                setoid_rewrite in_map_iff at 1 in H14.
                clear - H14 H17 H20 H19.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m1))); simpl; auto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H13; auto.
        * unfold filterRegs, id in H15.
          rewrite filter_In in H15; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m2))); [simpl in *| discriminate].
          specialize (H14 _ _ H15).
          destruct H14; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_2; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H17.
                rewrite in_map_iff in H17; dest.
                rewrite filter_In in H20; dest.
                setoid_rewrite in_map_iff at 1 in H14.
                clear - H14 H17 H20 H19.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m2))); simpl; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H13 in H4.
        simpl in H4.
        rewrite map_app in H4.
        unfold filterRegs, id.
        apply filter_map_app_sameKey; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H13 in H4.
        simpl in H4.
        auto.
  Qed.

  Lemma JoinStep o1 o2 l1 l2:
    Step m1 o1 l1 ->
    Step m2 o2 l2 ->
    (MatchingExecCalls l1 l2 m2) ->
    (MatchingExecCalls l2 l1 m1) ->
    (forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                           | Rle _, Rle _ => False
                                           | _, _ => True
                                           end) ->
    (forall x, InCall x l1 -> InCall x l2 -> False) ->
    Step (ConcatMod m1 m2) (o1 ++ o2) (l1 ++ l2).
  Proof.
    intros.
    econstructor 3; eauto.
  Qed.

  Lemma JoinTrace_basic l:
    forall o1 o2,
    Trace m1 o1 (map fst l) ->
    Trace m2 o2 (map snd l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls l1 l2 m2) l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls l2 l1 m1) l) ->
    (mapProp2 (fun l1 l2 =>
                 (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                     In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                             | Rle _ => match fst (snd x2) with
                                                        | Rle _ => False
                                                        | Meth _ => True
                                                        end
                                             | Meth _ => True
                                             end)) l) ->
    (mapProp2 (fun l1 l2 =>
                 (forall x, InCall x l1 ->
                            InCall x l2 -> False)) l) ->
    Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) l).
  Proof.
    induction l; simpl; intros.
    - inversion H; inversion H0; subst; try discriminate.
      constructor; auto.
      simpl.
      rewrite map_app.
      reflexivity.
    - destruct a; simpl in *; dest.
      inv H; [discriminate| ]; inv H0; [discriminate|].
      inv HTrace; inv HTrace0.
      specialize (IHl _ _ HOldTrace HOldTrace0 H8 H7 H6).
      econstructor 2 with (o := o ++ o0); eauto.
      eapply JoinStep; eauto.
      unfold UpdRegs in *; dest.
      split.
      + rewrite ?map_app.
        congruence.
      + intros.
        rewrite in_app_iff in H11.
        destruct H11.
        * specialize (H10 _ _ H11).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H10; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H13; [firstorder fail|].
             rewrite in_map_iff in H14; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep0 _ _ _ H13 H15).
             pose proof (Step_read HStep _ _ H12).
             firstorder fail.
        * specialize (H0 _ _ H11).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H0; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H13; [|firstorder fail].
             rewrite in_map_iff in H14; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep _ _ _ H13 H15).
             pose proof (Step_read HStep0 _ _ H12).
             firstorder fail.
  Qed.

  Lemma JoinTrace_len l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls l1 l2 m2) l1 l2) ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls l2 l1 m1) l1 l2) ->
      (mapProp_len (fun l1 l2 =>
                      (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                          In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                  | Rle _ => match fst (snd x2) with
                                                             | Rle _ => False
                                                             | Meth _ => True
                                                             end
                                                  | Meth _ => True
                                                  end)) l1 l2) ->
      (mapProp_len (fun l1 l2 =>
                      (forall x, InCall x l1 -> InCall x l2 -> False)) l1 l2) ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (zip l1 l2)).
  Proof.
    intros.
    eapply JoinTrace_basic; rewrite ?fst_zip, ?snd_zip; eauto;
      eapply mapProp2_len_same; eauto.
  Qed.

  Lemma JoinTrace l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      nthProp2 (fun l1 l2 => MatchingExecCalls l1 l2 m2 /\
                             MatchingExecCalls l2 l1 m1 /\
                             (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                                 In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                         | Rle _ => match fst (snd x2) with
                                                                    | Rle _ => False
                                                                    | Meth _ => True
                                                                    end
                                                         | Meth _ => True
                                                         end) /\
                             (forall x, InCall x l1 -> InCall x l2 -> False)) l1 l2 ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (zip l1 l2)).
  Proof.
    intros ? ? ? ?.
    setoid_rewrite <- mapProp_len_nthProp2; auto.
    repeat rewrite mapProp_len_conj; auto.
    pose proof (@JoinTrace_len l1 l2 o1 o2 H).
    intros; dest.
    firstorder fail.
  Qed.
End SplitJoin.

Lemma InExec_dec: forall x l, {InExec x l} + {~ InExec x l}.
Proof.
  unfold InExec; intros.
  apply in_dec; intros.
  decide equality.
  - apply string_dec.
  - apply MethT_dec.
Qed.

Lemma Substeps_meth_In m o l:
  Substeps m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      apply (in_map fst _ _ HInMeths).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_meth_In m o l:
  Step m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - eapply Substeps_meth_In; eauto.
  - eauto.
  - rewrite map_app, in_app_iff in *.
    clear - IHStep1 IHStep2 H1;
      firstorder fail.
Qed.

Lemma Step_meth_InExec m o l:
  Step m o l ->
  forall f, InExec f l ->
            In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  unfold InExec in *.
  rewrite in_map_iff in H0.
  dest.
  destruct x; simpl in *.
  destruct p; simpl in *; subst.
  eapply Step_meth_In; eauto.
Qed.

Lemma Trace_meth_In m o ls:
  Trace m o ls ->
  forall u f cs i l, nth_error ls i = Some l ->
                     In (u, (Meth f, cs)) l ->
                     In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; auto; destruct i; simpl in *.
  - subst; simpl in *; congruence.
  - subst; simpl in *; congruence.
  - subst.
    eapply Step_meth_In with (o := o) (u := u) (f := f) (cs := cs) in H1; eauto.
    inv H0; auto.
  - subst; simpl in *.
    eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_In_map m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                In (Meth f) (map (fun x => fst (snd x)) l) ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest.
  destruct x.
  destruct p.
  simpl in *; subst.
  eapply Trace_meth_In; eauto.
Qed.
  
Lemma Trace_meth_InExec m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                InExec f l ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  apply Trace_meth_In_map.
Qed.

Lemma InExec_app_iff: forall x l1 l2, InExec x (l1 ++ l2) <-> InExec x l1 \/ InExec x l2.
Proof.
  unfold InExec in *; intros.
  rewrite map_app.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma InCall_app_iff: forall x l1 l2, InCall x (l1 ++ l2) <-> InCall x l1 \/ InCall x l2.
Proof.
  unfold InCall in *; intros.
  setoid_rewrite in_app_iff.
  firstorder fail.
Qed.

Lemma Step_meth_InCall_InDef_InExec m o ls:
  Step m o ls ->
  forall (f : MethT),
    InCall f ls ->
    In (fst f) (map fst (getAllMethods m)) -> InExec f ls.
Proof.
  induction 1.
  - unfold MatchingExecCalls in *.
    firstorder fail.
  - assumption.
  - subst.
    simpl.
    rewrite map_app.
    setoid_rewrite in_app_iff.
    setoid_rewrite InExec_app_iff.
    intros.
    rewrite InCall_app_iff in H1.
    unfold MatchingExecCalls in *.
    repeat match goal with
           | H: forall (x: MethT), _ |- _ => specialize (H f)
           end.
    tauto.
Qed.

Lemma Trace_meth_InCall_InDef_InExec m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l -> InCall f l ->
    In (fst f) (map fst (getAllMethods m)) -> InExec f l.
Proof.
  induction 1; subst; auto; simpl; intros.
  - destruct i; simpl in *; try congruence.
  - destruct i; simpl in *.
    + inv H0.
      eapply Step_meth_InCall_InDef_InExec; eauto.
    + eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_InCall_not_InExec_not_InDef m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l ->
    InCall f l ->
    ~ InExec f l ->
    ~ In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  intro.
  eapply Trace_meth_InCall_InDef_InExec in H3; eauto.
Qed.

Lemma InCall_dec: forall x l, InCall x l \/ ~ InCall x l.
Proof.
  unfold InCall; intros.
  induction l; simpl.
  - right.
    intro.
    dest; auto.
  - destruct IHl; dest.
    + left.
      exists x0.
      split; tauto.
    + pose proof (in_dec MethT_dec x (snd (snd a))).
      destruct H0.
      * left; exists a; tauto.
      * right; intro.
        dest.
        destruct H0; subst.
        -- auto.
        -- firstorder fail.
Qed.

Section ModularSubstition.
  Variable a b a' b': Mod.
  Variable DisjRegs: DisjKey (getAllRegisters a) (getAllRegisters b).
  Variable DisjRules: DisjKey (getAllRules a) (getAllRules b).
  Variable DisjMeths: DisjKey (getAllMethods a) (getAllMethods b).
  Variable DisjRegs': DisjKey (getAllRegisters a') (getAllRegisters b').
  Variable DisjMeths': DisjKey (getAllMethods a') (getAllMethods b').
  Variable SameList_a: forall x, (In x (map fst (getAllMethods a)) /\
                                  ~ In x (getHidden a)) <->
                                 (In x (map fst (getAllMethods a')) /\
                                  ~ In x (getHidden a')).
  Variable Subset_a: forall x, In x (map fst (getAllMethods a')) ->
                               In x (map fst (getAllMethods a)).
  Variable SameList_b: forall x, (In x (map fst (getAllMethods b)) /\
                                  ~ In x (getHidden b)) <->
                                 (In x (map fst (getAllMethods b')) /\
                                  ~ In x (getHidden b')).
  Variable Subset_b: forall x, In x (map fst (getAllMethods b')) ->
                               In x (map fst (getAllMethods b)).

  Lemma ModularSubstition: TraceInclusion a a' ->
                           TraceInclusion b b' ->
                           TraceInclusion (ConcatMod a b) (ConcatMod a' b').
  Proof.
    unfold TraceInclusion in *; intros.
    pose proof (SplitTrace DisjRegs DisjRules DisjMeths H1); dest.
    specialize (@H _ _ H2).
    specialize (@H0 _ _ H3).
    dest.
    exists (x1 ++ x).
    exists (map (fun x => fst x ++ snd x) (zip x2 x0)).
    pose proof H9 as sth1.
    pose proof H7 as sth2.
    rewrite map_length in H9, H7.
    rewrite H9 in H7.
    rewrite mapProp_nthProp in H5.
    repeat split.
    - apply JoinTrace; auto; unfold nthProp, nthProp2 in *; intros; auto.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in H10, H8;
        case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        case_eq (nth_error ls1 i);
        intros;
        try congruence; auto;
          [rewrite H11, H12, H13 in *; dest|
           solve [exfalso; apply (nth_error_len _ _ _ H11 H13 H9)]].
      Opaque MatchingExecCalls.
      repeat split; intros.
      Transparent MatchingExecCalls.
      + unfold MatchingExecCalls in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (DisjMeths (fst f));
          try specialize (DisjMeths' (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (Subset_b H25).
        destruct (InExec_dec f l1); [pose proof (Trace_meth_InExec H _ _ H13 i0) as sth; clear - DisjMeths' sth H25; firstorder fail|].
        pose proof (proj2 H21 (conj n H24)); dest.
        specialize (H5 H27 Subset_b); dest.
        clear - H28 H27 H16 H8 SameList_b H5 Subset_b; firstorder fail.
      + unfold MatchingExecCalls in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (DisjMeths (fst f));
          try specialize (DisjMeths' (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (Subset_a H25).
        destruct (InExec_dec f l0); [pose proof (Trace_meth_InExec H0 _ _ H12 i0) as sth; clear - DisjMeths' sth H25; firstorder fail|].
        pose proof (proj2 H18 (conj n H24)); dest.
        specialize (H14 H27 Subset_a); dest.
        clear - H28 H27 H16 H10 SameList_a H14 Subset_a; firstorder fail.
      + destruct x3, x4, p, p0, r1, r2; simpl; auto.
        pose proof (in_map (fun x => fst (snd x)) _ _ H24) as sth3.
        pose proof (in_map (fun x => fst (snd x)) _ _ H25) as sth4.
        simpl in *.
        assert (sth5: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id a l))) by
            (clear - H23 sth3; firstorder fail).
        assert (sth6: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id b l))) by
            (clear - H20 sth4; firstorder fail).
        dest.
        rewrite in_map_iff in *; dest.
        specialize (H15 _ _ H29 H28).
        rewrite H27, H26 in *.
        assumption.
      + destruct (InExec_dec x3 l1), (InExec_dec x3 l0).
        * pose proof (Trace_meth_InExec H _ _ H13 i0) as sth3.
          pose proof (Trace_meth_InExec H0 _ _ H12 i1) as sth4.
          clear - DisjMeths' sth3 sth4.
          firstorder fail.
        * pose proof (Trace_meth_InExec H _ _ H13 i0) as i0'.
          pose proof (Trace_meth_InCall_not_InExec_not_InDef H0 _ H12 H25 n) as n'.
          pose proof (proj2 (H18 _) (conj n H25)); dest.
          unfold MatchingExecCalls in *.
          pose proof (proj2 (H22 _) (or_introl (conj i0 H24))).
          destruct H28; dest.
          -- eapply H16; eauto.
          -- specialize (Subset_a _ i0').
             specialize (H14 _ H27 Subset_a); tauto.
        * pose proof (Trace_meth_InExec H0 _ _ H12 i0) as i0'.
          pose proof (Trace_meth_InCall_not_InExec_not_InDef H _ H13 H24 n) as n'.
          pose proof (proj2 (H21 _) (conj n H24)); dest.
          unfold MatchingExecCalls in *.
          pose proof (proj2 (H19 _) (or_introl (conj i0 H25))).
          destruct H28; dest.
          -- eapply H16; eauto.
          -- specialize (Subset_b _ i0').
             specialize (H5 _ H27 Subset_b); tauto.
        * pose proof (proj2 (H21 _) (conj n H24)); dest.
          pose proof (proj2 (H18 _) (conj n0 H25)); dest.
          clear - H27 H29 H16. specialize (H16 x3); tauto.
    - rewrite map_length.
      rewrite length_zip; congruence.
    - unfold nthProp, nthProp2 in *; intros.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in *.
      simpl in *.
      case_eq (nth_error ls1 i); intros; rewrite H11 in *; auto.
      setoid_rewrite (nth_error_zip (fun x3 => fst x3 ++ snd x3) _ i x2 x0); auto.
      case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        intros; auto; rewrite H12, H13 in *; simpl in *; intros.
      split; intros.
      + rewrite ?InExec_app_iff in *.
        rewrite ?InCall_app_iff in *.
        rewrite ?Demorgans in *.
        split; intros; dest.
        * rewrite H19 in H14, H15; clear H19.
          rewrite InExec_app_iff, InCall_app_iff in *.
          assert (~ InCall f (filterExecs id a l) /\
                  ~ InCall f (filterExecs id b l)) by (clear - H15; tauto).
          clear H15; dest.
          specialize (H10 f); specialize (H8 f).
          split; [tauto|].
          intro.
          destruct H14, H26; try tauto.
          -- destruct (InExec_dec f l0).
             ++ pose proof (Trace_meth_InExec H0 _ _ H12 i0) as sth.
                pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H14)
                  as sth3.
                specialize (Subset_b _ sth).
                clear - sth3 Subset_b DisjMeths; firstorder fail.
             ++ pose proof (proj2 (H20 _ ) (conj n H26)); dest.
                tauto.
          -- destruct (InExec_dec f l1).
             ++ pose proof (Trace_meth_InExec H _ _ H13 i0) as sth.
                pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H14)
                  as sth3.
                specialize (Subset_a _ sth).
                clear - sth3 Subset_a DisjMeths; firstorder fail.
             ++ pose proof (proj2 (H23 _ ) (conj n H26)); dest.
                tauto.
        * assert (~ InCall f l1 /\ ~ InCall f l0) by (clear - H15; tauto).
          clear H15; dest.
          rewrite H19.
          rewrite InExec_app_iff.
          rewrite InCall_app_iff.
          specialize (H10 f); specialize (H8 f).
          split; [tauto|].
          intro.
          destruct H14, H27; try tauto.
          -- destruct (InExec_dec f (filterExecs id b l)).
             ++ pose proof (Trace_meth_InExec H _ _ H13 H14) as sth.
                pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) i0)
                  as sth3.
                specialize (Subset_a _ sth).
                clear - sth3 Subset_a DisjMeths; firstorder fail.
             ++ pose proof (proj1 (H20 _) (conj n H27)); dest.
                tauto.
          -- destruct (InExec_dec f (filterExecs id a l)).
             ++ pose proof (Trace_meth_InExec H0 _ _ H12 H14) as sth.
                pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) i0)
                  as sth3.
                specialize (Subset_b _ sth).
                clear - sth3 Subset_b DisjMeths; firstorder fail.
             ++ pose proof (proj1 (H23 _) (conj n H27)); dest.
                tauto.
      + split; intros.
        * rewrite ?InExec_app_iff in *.
          rewrite ?InCall_app_iff in *.
          rewrite ?Demorgans in *.
          split; intros; dest.
          -- rewrite H19 in H14, H15; rewrite ?InExec_app_iff, ?InCall_app_iff,
                                      ?Demorgans in *.
             assert (~ InExec f (filterExecs id a l) /\
                     ~ InExec f (filterExecs id b l)) by (clear - H14; firstorder fail).
             clear H14; dest.
             specialize (H20 f); specialize (H23 f).
             split; [|tauto].
             intro.
             destruct H15, H27; try tauto.
             ++ unfold MatchingExecCalls in *.
                pose proof (Trace_meth_InExec H0 _ _ H12 H27) as sth.
                specialize (Subset_b _ sth).
                specialize (H5 f).
                tauto.
             ++ unfold MatchingExecCalls in *.
                pose proof (Trace_meth_InExec H _ _ H13 H27) as sth.
                specialize (Subset_a _ sth).
                specialize (H16 f).
                tauto.
          -- assert (~ InExec f l1 /\ ~ InExec f l0) by (clear - H14; firstorder fail).
             clear H14; dest.
             rewrite H19 .
             rewrite InExec_app_iff, InCall_app_iff.
             specialize (H20 f); specialize (H23 f).
             split; [|tauto].
             intro.
             destruct H15, H27; try tauto.
             ++ unfold MatchingExecCalls in *.
                destruct (InCall_dec f (filterExecs id b l)).
                ** pose proof (proj2 H23 (conj H14 H15)); dest.
                   eapply H18; eauto.
                ** pose proof (proj1 (H8 _) (conj H27 H28)).
                   tauto.
             ++ unfold MatchingExecCalls in *.
                destruct (InCall_dec f (filterExecs id a l)).
                ** pose proof (proj2 H20 (conj H26 H15)); dest.
                   eapply H18; eauto.
                ** pose proof (proj1 (H10 _) (conj H27 H28)).
                   tauto.
        * split; intros;
            unfold MatchingExecCalls in *; dest;
              repeat match goal with
                     | H: forall x: MethT, _ |- _ => specialize (H f)
                     end; try (specialize (DisjMeths (fst f)); specialize (SameList_a (fst f)); specialize (Subset_a (fst f));
                specialize (SameList_b (fst f)); specialize (Subset_b (fst f))).
          -- split; intros; dest.
             ++ rewrite H17 in H24.
                rewrite InExec_app_iff, InCall_app_iff in *.
                dest.
                destruct H24; dest.
                ** destruct H24, H25.
                   --- assert (~ InCall f (filterExecs id b l)) by tauto.
                       assert (~ InExec f (filterExecs id b l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H24).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H27).
                         tauto.
                       }
                       pose proof (proj1 H19 (or_intror (conj H27 H26))).
                       destruct H28; [left; clear - H28; tauto| dest].
                       pose proof (proj1 H22 (or_introl (conj H24 H25))).
                       destruct H30; [left; clear - H30; tauto| dest].
                       clear - H28 H29 H30 H31; tauto.
                   --- assert (~ InCall f (filterExecs id a l)) by tauto.
                       assert (~ InExec f (filterExecs id b l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H24).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H27).
                         tauto.
                       }
                       clear - H24 H25 H26 H27 H10 H21 H8 H18; tauto.
                   --- assert (~ InCall f (filterExecs id b l)) by tauto.
                       assert (~ InExec f (filterExecs id a l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H27).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H24).
                         tauto.
                       }
                       clear - H24 H25 H26 H27 H10 H21 H8 H18; tauto.
                   --- assert (~ InCall f (filterExecs id a l)) by tauto.
                       assert (~ InExec f (filterExecs id a l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H27).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H24).
                         tauto.
                       }
                       pose proof (proj1 H22 (or_intror (conj H27 H26))).
                       destruct H28; [left; clear - H28; tauto| dest].
                       pose proof (proj1 H19 (or_introl (conj H24 H25))).
                       destruct H30; [left; clear - H30; tauto| dest].
                       clear - H28 H29 H30 H31; tauto.
                ** assert (~ InExec f (filterExecs id a l) /\ ~ InExec f (filterExecs id b l)) by (clear - H24; tauto); clear H24.
                   assert (~ InCall f (filterExecs id a l) /\ ~ InCall f (filterExecs id b l)) by (clear - H25; tauto); clear H25.
                   dest.
                   pose proof (proj1 H22 (or_intror (conj H26 H24))).
                   pose proof (proj1 H19 (or_intror (conj H27 H25))).
                   destruct H28, H29; clear - H28 H29; try tauto.
             ++ rewrite H17.
                rewrite InExec_app_iff, InCall_app_iff in *.
                dest.
                specialize (DisjMeths' (fst f)).
                destruct H24; dest.
                ** destruct H24, H25.
                   --- pose proof (proj2 H22 (or_introl (conj H24 H25))).
                       destruct H26; [clear - H26; tauto| dest].
                       pose proof (Trace_meth_InExec H _ _ H13 H24).
                       specialize (Subset_a H28).
                       assert (~ In (fst f) (map fst (getAllMethods b))) by (clear - Subset_a DisjMeths; tauto).
                       assert (~ InExec f (filterExecs id b l)).
                       { intro Help.
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) Help).
                         tauto.
                       }
                       destruct (InCall_dec f (filterExecs id b l)); [| clear - H26 H27 H30 H31; tauto].
                       specialize (H14 H31 Subset_a); dest; tauto.
                   --- destruct (InCall_dec f l1), (InExec_dec f l0).
                       +++ pose proof (Trace_meth_InExec H _ _ H13 H24).
                           pose proof (Trace_meth_InExec H0 _ _ H12 i0).
                           clear - DisjMeths' H27 H28; tauto.
                       +++ pose proof (proj2 H18 (conj n H25)); dest.
                           pose proof (proj2 H22 (or_introl (conj H24 H26))).
                           destruct H29; [clear - H16 H29; tauto| dest].
                           pose proof (Trace_meth_InExec H _ _ H13 H24).
                           specialize (Subset_a H31).
                           specialize (H14 H28 Subset_a); clear - H14 H29; tauto.
                       +++ pose proof (Trace_meth_InExec H0 _ _ H12 i0).
                           specialize (Subset_b H27).
                           pose proof (Trace_meth_InExec H _ _ H13 H24).
                           specialize (Subset_a H28).
                           clear - Subset_a Subset_b DisjMeths; tauto.
                       +++ pose proof (proj2 H10 (conj H24 H26)); dest.
                           pose proof (proj2 H18 (conj n H25)); dest.
                           clear - H27 H30; tauto.
                   --- destruct (InCall_dec f l0), (InExec_dec f l1).
                       +++ pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           pose proof (Trace_meth_InExec H _ _ H13 i0).
                           clear - DisjMeths' H27 H28; tauto.
                       +++ pose proof (proj2 H21 (conj n H25)); dest.
                           pose proof (proj2 H19 (or_introl (conj H24 H26))).
                           destruct H29; [clear - H16 H29; tauto| dest].
                           pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           specialize (Subset_b H31).
                           specialize (H5 H28 Subset_b); clear - H5 H29; tauto.
                       +++ pose proof (Trace_meth_InExec H _ _ H13 i0).
                           specialize (Subset_a H27).
                           pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           specialize (Subset_b H28).
                           clear - Subset_a Subset_b DisjMeths; tauto.
                       +++ pose proof (proj2 H8 (conj H24 H26)); dest.
                           pose proof (proj2 H21 (conj n H25)); dest.
                           clear - H27 H30; tauto.
                   --- pose proof (proj2 H19 (or_introl (conj H24 H25))).
                       destruct H26; [clear - H26; tauto| dest].
                       pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                       specialize (Subset_b H28).
                       assert (~ In (fst f) (map fst (getAllMethods a))) by (clear - Subset_b DisjMeths; tauto).
                       assert (~ InExec f (filterExecs id a l)).
                       { intro Help.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) Help).
                         tauto.
                       }
                       destruct (InCall_dec f (filterExecs id a l)); [| clear - H26 H27 H30 H31; tauto].
                       specialize (H5 H31 Subset_b); dest; tauto.
                ** assert (~ InExec f l1 /\ ~ InExec f l0) by (clear - H24; tauto); dest.
                   assert (~ InCall f l1 /\ ~ InCall f l0) by (clear - H25; tauto); dest.
                   clear - H22 H19 H26 H27 H28 H29.
                   pose proof (proj2 H22 (or_intror (conj H26 H28))).
                   pose proof (proj2 H19 (or_intror (conj H27 H29))).
                   clear H22 H19; tauto.
          -- intros; dest; rewrite ?map_app, ?in_app_iff in *.
             rewrite H18.
             rewrite map_app.
             setoid_rewrite in_app_iff.
             clear - H14 H21 H24.
             firstorder fail.
  Qed.
End ModularSubstition.


Lemma TraceInclusion_refl: forall m, TraceInclusion m m.
Proof.
  unfold TraceInclusion; intros.
  exists o1, ls1.
  repeat split; auto.
  unfold nthProp2; intros.
  destruct (nth_error ls1 i); auto.
  repeat split; intros; tauto.
Qed.

Lemma TraceInclusion_trans: forall m1 m2 m3, TraceInclusion m1 m2 ->
                                             TraceInclusion m2 m3 ->
                                             TraceInclusion m1 m3.
Proof.
  unfold TraceInclusion; intros.
  specialize (H _ _ H1); dest.
  specialize (H0 _ _ H); dest.
  exists x1, x2.
  repeat split; auto.
  - congruence.
  - unfold nthProp2 in *; intros.
    specialize (H3 i); specialize (H5 i).
    case_eq (nth_error ls1 i);
      case_eq (nth_error x0 i);
      case_eq (nth_error x2 i);
      intros; auto.
    + rewrite H6, H7, H8 in *.
      dest.
      split; [|split; [|split]]; intros;
        repeat match goal with
               | H: forall x: MethT, _ |- _ => specialize (H f)
               end.
      * tauto.
      * tauto.
      * rewrite <- H13 in H10.
        assumption.
      * tauto.
    + pose proof (nth_error_len _ _ _ H7 H6 H4); tauto.
Qed.








Lemma UpdRegs_nil_upd: forall o, NoDup (map fst o) -> forall o', UpdRegs [] o o' -> o = o'.
Proof.
  unfold UpdRegs.
  intros.
  dest.
  simpl in *.
  assert (sth: forall s v, In (s, v) o' -> In (s, v) o).
  { intros.
    specialize (H1 s v H2).
    destruct H1; dest; try auto.
    tauto.
  }
  clear H1.
  generalize o' H H0 sth.
  clear o' H H0 sth.
  induction o; destruct o'; simpl; auto; intros.
  - discriminate.
  - discriminate.
  - inv H0.
    inv H.
    specialize (IHo _ H6 H4).
    destruct p, a; simpl in *; subst; auto; repeat f_equal; auto.
    + specialize (sth s s0 (or_introl eq_refl)).
      destruct sth.
      * inv H; subst; auto.
      * apply (in_map fst) in H; simpl in *; tauto.
    + eapply IHo; intros.
      specialize (sth _ _ (or_intror H)).
      destruct sth; [|auto].
      inv H0; subst.
      apply (f_equal (map fst)) in H4.
      rewrite ?map_map in *; simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H4; try tauto.
      apply (in_map fst) in H; simpl in *; congruence.
Qed.

Lemma Trace_NoDup m o l:
  Trace m o l ->
  NoDup (map fst (getAllRegisters m)) ->
  NoDup (map fst o).
Proof.
  induction 1; subst.
  - rewrite map_map; simpl.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst); intros; tauto.
  - unfold UpdRegs in *; intros; dest.
    apply (f_equal (map fst)) in H1.
    rewrite ?map_map in *; simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H1; try tauto.
    rewrite H1 in *; eapply IHTrace; eauto.
Qed.

Lemma Trace_sameRegs m o l:
  Trace m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; subst; auto.
  - rewrite map_map; simpl; auto.
  - unfold UpdRegs in *; dest. congruence.
Qed.

Lemma Step_empty m:
  forall o,
    getKindAttr o = getKindAttr (getAllRegisters m) ->
    Step m o [].
Proof.
  induction m; simpl; intros; auto.
  - constructor; auto.
    + constructor; auto.
    + unfold MatchingExecCalls; firstorder fail.
  - constructor 2.
    + eapply IHm; eauto.
    + intros.
      unfold InExec in *; simpl in *.
      tauto.
  - rewrite map_app in H.
    pose proof (list_split _ _ _ _ _ H).
    dest.
    specialize (IHm1 _ H1).
    specialize (IHm2 _ H2).
    eapply ConcatModStep with (o1 := x) (o2 := x0) (l1 := []) (l2 := []); eauto.
    + unfold MatchingExecCalls; intros.
      unfold InCall in *; simpl in *; dest; tauto.
    + unfold MatchingExecCalls; intros.
      unfold InCall in *; simpl in *; dest; tauto.
    + intros.
      simpl in *; tauto.
    + intros.
      unfold InCall in *; simpl in *; dest; tauto.
Qed.

Lemma Trace_Step_empty m o l:
  Trace m o l ->
  Step m o [].
Proof.
  intros.
  apply Trace_sameRegs in H.
  apply Step_empty in H.
  auto.
Qed.

Section StepSimulation.
  Variable imp spec: Mod.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: simRel (map regInit (getAllRegisters imp)) (map regInit (getAllRegisters spec)).
  Variable NoDupRegs: NoDup (map fst (getAllRegisters imp)).
  
  Variable stepSimulationNonZero:
    forall oImp lImp oImp',
      Step imp oImp lImp ->
      lImp <> nil ->
      UpdRegs (map fst lImp) oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        exists lSpec oSpec',
          Step spec oSpec lSpec /\
          UpdRegs (map fst lSpec) oSpec oSpec' /\
          simRel oImp' oSpec' /\
          (forall f : MethT, InExec f lImp /\ ~ InCall f lImp <-> InExec f lSpec /\ ~ InCall f lSpec) /\
          (forall f : MethT, ~ InExec f lImp /\ InCall f lImp <-> ~ InExec f lSpec /\ InCall f lSpec) /\
          (forall f : MethT, InExec f lImp /\ InCall f lImp \/ ~ InExec f lImp /\ ~ InCall f lImp <->
                             InExec f lSpec /\ InCall f lSpec \/ ~ InExec f lSpec /\ ~ InCall f lSpec) /\
          ((exists rle : string, In (Rle rle) (map getRleOrMeth lSpec)) -> (exists rle : string, In (Rle rle) (map getRleOrMeth lImp))).

  Lemma StepDecomposition':
    forall (oImp : RegsT) (lsImp : list (list FullLabel)),
      Trace imp oImp lsImp ->
      exists (oSpec : RegsT) (lsSpec : list (list FullLabel)),
        Trace spec oSpec lsSpec /\
        Datatypes.length lsImp = Datatypes.length lsSpec /\
        nthProp2
          (fun l1 l2 : list FullLabel =>
             (forall f : MethT, InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ ~ InCall f l2) /\
             (forall f : MethT, ~ InExec f l1 /\ InCall f l1 <-> ~ InExec f l2 /\ InCall f l2) /\
             (forall f : MethT, InExec f l1 /\ InCall f l1 \/ ~ InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ InCall f l2 \/ ~ InExec f l2 /\ ~ InCall f l2) /\
             ((exists rle : string, In (Rle rle) (map getRleOrMeth l2)) -> (exists rle : string, In (Rle rle) (map getRleOrMeth l1)))
          ) lsImp lsSpec /\
        simRel oImp oSpec.
  Proof.
    induction 1; subst; simpl; auto; intros.
    - exists (map regInit (getAllRegisters spec)), []; repeat split; auto.
      + econstructor 1; eauto.
      + unfold nthProp2; intros.
        destruct (nth_error [] i); auto.
        repeat split; intros; tauto.
    - dest.
      destruct l.
      + simpl in *.
        exists x, ([] :: x0); repeat split; simpl in *; auto.
        * constructor 2 with (o := x) (ls := x0) (l := []); simpl; auto.
          -- eapply Trace_Step_empty; eauto.
          -- clear.
             unfold UpdRegs; split; intros; try tauto.
             right; split; try intro; dest; auto.
        * rewrite nthProp2_cons; split; simpl; auto; repeat split; dest; simpl in *; try tauto.
          constructor.
        * pose proof (Trace_NoDup H NoDupRegs) as sth.
          pose proof (UpdRegs_nil_upd sth HUpdRegs); subst; auto.
      + specialize (stepSimulationNonZero HStep ltac:(intro; discriminate) HUpdRegs H3).
        destruct stepSimulationNonZero as [lSpec [oSpec' [stepSpec [updSpec [sim lSpecProp]]]]].
        exists oSpec', (lSpec :: x0); repeat split; simpl in *; auto.
        * econstructor 2; eauto.
        * simpl.
          rewrite nthProp2_cons; split; auto.
  Qed.

  Lemma StepDecomposition:
    TraceInclusion imp spec.
  Proof.
    unfold TraceInclusion; intros.
    eapply StepDecomposition' in H.
    dest.
    exists x, x0.
    repeat split; auto.
  Qed.
End StepSimulation.

Lemma NoMeths_Substeps m o ls:
  getMethods m = [] ->
  Substeps m o ls ->
  ls = nil \/ exists u rl cs, ls = (u, (Rle rl, cs)) :: nil.
Proof.
  intros nilMeths substeps.
  induction substeps; intros; auto; subst.
  - destruct IHsubsteps; subst.
    + right.
      repeat eexists; eauto.
    + dest; subst.
      specialize (HNoRle _ (or_introl eq_refl)); simpl in *.
      tauto.
  - rewrite nilMeths in *.
    simpl in *.
    tauto.
Qed.
    







Section DecompositionZero.
  Variable imp spec: BaseModule.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: simRel (map regInit (getRegisters imp)) (map regInit (getRegisters spec)).
  Variable NoDupRegs: NoDup (map fst (getRegisters imp)).

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp uImp rleImp csImp oImp',
      Substeps imp oImp [(uImp, (Rle rleImp, csImp))] ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((getKindAttr oSpec = getKindAttr (getRegisters spec) /\ simRel oImp' oSpec /\ csImp = []) \/
         (exists uSpec rleSpec oSpec',
             Substeps spec oSpec [(uSpec, (Rle rleSpec, csImp))] /\
             UpdRegs [uSpec] oSpec oSpec' /\
             simRel oImp' oSpec')).

  Lemma decompositionZero:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    apply StepDecomposition with (simRel := simRel); auto; intros.
    inv H.
    pose proof HSubsteps as sth.
    inv HSubsteps; simpl in *.
    - tauto.
    - pose proof (NoMeths_Substeps NoMeths HSubstep).
      destruct H; [subst | dest; subst].
      + simpl in *.
        specialize (@simulation _ _ _ _ oImp' sth H1 _ H2).
        destruct simulation; dest; subst.
        * exists nil, oSpec.
          repeat split; auto.
          constructor; auto.
          -- constructor; auto.
          -- clear; firstorder fail.
          -- intros.
             right; split; try intro; dest; simpl in *; try tauto.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *.
             destruct H4; congruence.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *.
             destruct H4; congruence.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *; tauto.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- intros.
             destruct H4; dest.
             ++ unfold InExec in H4; simpl in *.
                destruct H4; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec, InCall in *; simpl in *; tauto.
                ** unfold InExec, InCall in *; simpl in *; dest; tauto.
          -- intros.
             destruct H4; dest.
             ++ unfold InExec in H4; simpl in *; tauto.
             ++ right.
                split; intro.
                ** unfold InExec, InCall in *; simpl in *. destruct H6; [discriminate | tauto].
                ** unfold InExec, InCall in *; simpl in *; dest; destruct H6; subst; simpl in *; tauto.
          -- intros.
             dest.
             simpl in *.
             tauto.
        * exists [(x, (Rle x0, cs))], x1.
          repeat split; auto.
          -- constructor; auto.
             unfold MatchingExecCalls; intros.
             simpl in *.
             rewrite NoMethsSpec in *; simpl in *; tauto.
          -- unfold UpdRegs in *; dest.
             auto.
          -- intros.
             unfold UpdRegs in *; dest.
             simpl in *.
             eapply H6; eauto.
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- intro.
             dest.
             unfold InExec in *; simpl in *; destruct H6; [discriminate | tauto].
          -- dest.
             unfold InCall in *; simpl in *; destruct H6; dest.
             eexists.
             split; [apply (or_introl eq_refl)|].
             simpl.
             destruct H6; subst; simpl in *; auto.
             tauto.
          -- intro.
             dest.
             unfold InExec in *; simpl in *; destruct H6; [discriminate | tauto].
          -- dest.
             unfold InCall in *; simpl in *; destruct H6; dest.
             eexists.
             split; [apply (or_introl eq_refl)|].
             simpl.
             destruct H6; subst; simpl in *; auto.
             tauto.
          -- intros; dest.
             destruct H5; dest.
             ++ dest.
                unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec in *; simpl in *; destruct H7; [discriminate | tauto].
                ** unfold InCall in *; dest; simpl in *.
                   assert (sth2: exists x, ((u, (Rle rn, cs)) = x \/ False) /\ In f (snd (snd x))).
                   { eexists.
                     split.
                     - left; reflexivity.
                     - simpl.
                       destruct H7; [|tauto].
                       subst; simpl in *; auto.
                   }
                   tauto.
          -- intros; dest.
             destruct H5; dest.
             ++ dest.
                unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec in *; simpl in *; destruct H7; [discriminate | tauto].
                ** unfold InCall in *; dest; simpl in *.
                   assert (sth2: exists x1, ((x, (Rle x0, cs)) = x1 \/ False) /\ In f (snd (snd x1))).
                   { eexists.
                     split.
                     - left; reflexivity.
                     - simpl.
                       destruct H7; [|tauto].
                       subst; simpl in *; auto.
                   }
                   tauto.
          -- intros.
             simpl in *.
             dest.
             destruct H5; [|tauto].
             exists rn.
             left; auto.
      + specialize (HNoRle _ (or_introl eq_refl)); simpl in *; tauto.
    - rewrite NoMeths in *.
      simpl in *; tauto.
  Qed.
End DecompositionZero.


Lemma createHide_hides: forall hides m, getHidden (createHide m hides) = hides.
Proof.
  induction hides; simpl; auto; intros; f_equal; auto.
Qed.

Lemma createHide_Regs: forall m l, getAllRegisters (createHide m l) = getRegisters m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Rules: forall m l, getAllRules (createHide m l) = getRules m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Meths: forall m l, getAllMethods (createHide m l) = getMethods m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma getFlat_Hide m s:
  getFlat (HideMeth m s) = getFlat m.
Proof.
  unfold getFlat; auto.
Qed.

Lemma WfMod_Hidden m:
  WfMod m ->
  forall s, In s (getHidden m) -> In s (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; auto; intros.
  - tauto.
  - destruct H0; subst; auto.
  - rewrite map_app, in_app_iff in *.
    specialize (IHWfMod1 s); specialize (IHWfMod2 s); tauto.
Qed.

Lemma SemActionUpdSub o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  SubList (getKindAttr upds) (getKindAttr o).
Proof.
  induction 1; auto;
    unfold SubList in *; intros;
      rewrite ?in_app_iff in *.
  - rewrite map_app, in_app_iff in *.
    destruct H1; firstorder fail.
  - subst; firstorder; simpl in *.
    subst.
    assumption.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst; simpl in *; intuition.
Qed.

Lemma SemActionExpandRegs o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  forall o', SubList reads o' ->
             SubList (getKindAttr upds) (getKindAttr o') ->
             @SemAction o' k a reads upds calls ret.
Proof.
  intros.
  induction H; try solve [econstructor; auto].
  - subst.
    specialize (IHSemAction H0).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_cons in H0; dest.
    specialize (IHSemAction H2 H1).
    econstructor; eauto.
  - subst.
    simpl in *.
    apply SubList_cons in H1; dest.
    specialize (IHSemAction H0 H2).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor 8; eauto.
Qed.

Lemma Substeps_combine m1 o1 l1:
  Substeps m1 o1 l1 ->
  forall m2 o2 l2  (DisjRegs: DisjKey (getRegisters m1) (getRegisters m2)) (DisjMeths: DisjKey (getMethods m1) (getMethods m2))
         (HOneRle: forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                         | Rle _, Rle _ => False
                                                         | _, _ => True
                                                         end)
         (HNoCall: forall x, InCall x l1 -> InCall x l2 -> False),
    Substeps m2 o2 l2 ->
    Substeps (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) (o1 ++ o2) (l1 ++ l2).
Proof.
  induction 1; intros.
  - induction H; simpl in *.
    + constructor 1; auto; simpl.
      rewrite ?map_app; congruence.
    + econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
    + econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False) by (clear - HNoCall0; firstorder fail).
    specialize (IHSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HNoRle; eauto| ].
      unfold SubList in *.
      specialize (HOneRle _ x (or_introl eq_refl) H1); simpl in *; assumption.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      unfold InCall.
      eexists; split; simpl; eauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False) by (clear - HNoCall0; firstorder fail).
    specialize (IHSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      unfold InCall.
      eexists; split; simpl; eauto.
Qed.

Lemma Substeps_flatten m o l:
  Substeps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l ->
  Substeps m o l.
Proof.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma Step_substitute' m o l:
  Step m o l -> forall (HWfMod: WfMod m), StepSubstitute m o l.
Proof.
  unfold StepSubstitute.
  induction 1; auto; simpl; intros; dest; unfold MatchingExecCalls in *; simpl in *.
  - repeat split.
    clear HMatching.
    induction HSubsteps.
    + econstructor 1; eauto.
    + econstructor 2; eauto.
    + econstructor 3; eauto.
    + simpl; tauto.
    + specialize (HMatching f); tauto.
    + intros; tauto.
  - inv HWfMod.
    specialize (IHStep HWf); dest.
    repeat split; auto.
    + specialize (H1 f); tauto.
    + intros.
      destruct H4; simpl in *; subst.
      -- apply HHidden; auto.
      -- apply H2; auto.
  - inv HWfMod.
    specialize (IHStep1 HWf1).
    specialize (IHStep2 HWf2).
    dest.
    subst; repeat split; auto.
    + pose proof (Substeps_combine H4 HDisjRegs HDisjMeths HNoRle HNoCall H1 (m2 := BaseMod (getAllRegisters m2) _ _)).
      simpl in *.
      assumption.
    + rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: MethT, _ |- _ => specialize (H f)
             end; tauto.
    + intros.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: string, _ |- _ => specialize (H s)
             | H: forall x: MethT, _ |- _ => specialize (H (s, v))
             end.
      specialize (H6 v); specialize (H3 v).
      destruct H7, H8, H9; try tauto.
      * pose proof (Step_meth_InExec H0 _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (Step_meth_InExec H _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
Qed.

Lemma StepSubstitute_flatten m o l (HWfMod: WfMod m):
  Step (flatten m) o l <-> StepSubstitute m o l.
Proof.
  unfold flatten, getFlat, StepSubstitute.
  split; intros.
  - induction (getHidden m).
    + simpl in *.
      inv H.
      split; [auto| split; [auto| intros; tauto]].
    + simpl in *.
      inv H.
      specialize (IHl0 HStep); dest.
      split; [auto| split; [auto| intros]].
      rewrite createHide_Meths in *; simpl in *.
      destruct H3; [subst |clear - H1 H2 H3 H4; firstorder fail].
      firstorder fail.
  - induction (getHidden m); simpl; auto; dest.
    + constructor; auto.
    + assert (sth: Step (createHide (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) l0) o l) by firstorder fail.
      assert (sth2: forall v, In a (map fst (getAllMethods m)) -> InExec (a, v) l -> InCall (a, v) l) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths.
      auto.
Qed.
    
Lemma Step_substitute m o l (HWfMod: WfMod m):
  Step m o l -> Step (flatten m) o l.
Proof.
  intros Stp.
  apply Step_substitute' in Stp; auto.
  rewrite StepSubstitute_flatten in *; auto.
Qed.

Definition concatFlat m1 m2 := BaseMod (getRegisters m1 ++ getRegisters m2)
                                       (getRules m1 ++ getRules m2)
                                       (getMethods m1 ++ getMethods m2).

Lemma splitRegs o m1 m2 (DisjRegisters: DisjKey (getRegisters m1) (getRegisters m2)):
  getKindAttr o = getKindAttr (getRegisters m1 ++ getRegisters m2) ->
  getKindAttr (filter (fun x : string * {x : FullKind & fullType type x} => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) = getKindAttr (getRegisters m1).
Proof.
  intros HRegs.
  rewrite map_app in *.
  pose proof (filter_map_simple (fun x: string * {x: FullKind & fullType type x} => (fst x, projT1 (snd x)))
                                (fun x => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) as sth.
  simpl in sth.
  setoid_rewrite <- sth.
  setoid_rewrite HRegs.
  rewrite filter_app.
  setoid_rewrite filter_false_list at 2.
  - rewrite filter_true_list at 1.
    + rewrite app_nil_r; auto.
    + intros.
      apply (in_map fst) in H.
      rewrite map_map in H.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
      destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
  - intros.
    apply (in_map fst) in H.
    rewrite map_map in H.
    simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
    destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
    specialize (DisjRegisters (fst a)).
    tauto.
Qed.


Section SplitSubsteps.
  Variable m1 m2: BaseModule.
  Variable DisjRegs: DisjKey (getRegisters m1) (getRegisters m2).
  Variable DisjRules: DisjKey (getRules m1) (getRules m2).
  Variable DisjMeths: DisjKey (getMethods m1) (getMethods m2).

  Variable WfMod1: WfBaseMod m1.
  Variable WfMod2: WfBaseMod m2.
  
  Lemma split_Substeps o l:
    Substeps (concatFlat m1 m2) o l ->
    MatchingExecCalls l l (Base (concatFlat m1 m2)) ->
    exists o1 o2 l1 l2,
      o = o1 ++ o2 /\
      l = l1 ++ l2 /\
      Substeps m1 o1 l1 /\
      Substeps m2 o2 l2 /\
      MatchingExecCalls l1 l1 (Base m1) /\
      MatchingExecCalls l2 l2 (Base m2) /\
      MatchingExecCalls l1 l2 (Base m2) /\
      MatchingExecCalls l2 l1 (Base m1) /\
      (forall x y : FullLabel,
          In x l1 -> In y l2 -> match fst (snd x) with
                                | Rle _ => match fst (snd y) with
                                           | Rle _ => False
                                           | Meth _ => True
                                           end
                                | Meth _ => True
                                end) /\
      (forall x : MethT, InCall x l1 -> InCall x l2 -> False).
  Proof.
    induction 1; simpl in *.
    - rewrite map_app in *.
      pose proof (list_split _ _ _ _ _ HRegs); dest.
      intros.
      exists x, x0, [], [].
      split; [auto|].
      split; [auto|].
      split; [constructor; auto|].
      split; [constructor; auto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto.
    - subst; intros.
      destruct WfMod1 as [r1 df1].
      destruct WfMod2 as [r2 df2].
      unfold WfBaseMod in *.
      destruct WfMod1 as [Rules1 Meths1].
      destruct WfMod2 as [Rules2 Meths2].
      admit.
    - admit.
  Admitted.
End SplitSubsteps.

Lemma substitute_Step' m (HWfMod: WfMod m):
  forall o l,
    StepSubstitute m o l -> Step m o l.
Proof.
  unfold StepSubstitute.
  induction m; simpl in *; intros; dest.
  - constructor; auto.
    eapply Substeps_flatten; eauto.
  - constructor 2.
    + apply IHm; inv HWfMod; firstorder fail.
    + clear - H1; firstorder fail.
  - inv HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    (* pose proof (@split_Substeps (getFlat m1) (getFlat m2) HDisjRegs HDisjRules HDisjMeths _ _ H H0); dest. *)
    (* (* apply split_Substeps in H; eauto. *) *)
    (* econstructor; eauto. *)
    admit.
Admitted.

Lemma substitute_Step m o l (HWfMod: WfMod m):
  Step (flatten m) o l -> Step m o l.
Proof.
  rewrite StepSubstitute_flatten in *; auto.
  apply substitute_Step'; auto.
Qed.

Section TraceSubstitute.
  Variable m: Mod.
  Variable WfMod_m: WfMod m.

  Lemma Trace_flatten_same: forall o l, Trace m o l <-> Trace (flatten m) o l.
  Proof.
    intros.
    split; induction 1; subst.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply Step_substitute in HStep; auto.
      econstructor 2; eauto.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply substitute_Step in HStep; auto.
      econstructor 2; eauto.
  Qed.

  Lemma Trace_Inclusion_flatten_r: TraceInclusion m (flatten m).
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same; auto.
  Qed.

  Lemma Trace_Inclusion_flatten_l: TraceInclusion (flatten m) m.
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same; auto.
  Qed.
End TraceSubstitute.
    
Lemma SameTrace m1 m2:
  (forall o1 l, Trace m1 o1 l -> exists o2, Trace m2 o2 l) ->
  TraceInclusion m1 m2.
Proof.
  unfold TraceInclusion; intros.
  pose proof (H _ _ H0); dest.
  exists x, ls1; auto.
  repeat split; auto.
  - unfold nthProp2; intros.
    destruct (nth_error ls1 i); auto.
    repeat split; tauto.
Qed.

Lemma WfMod_createHide l: forall m, WfMod (createHide m l) <-> SubList l (map fst (getMethods m)).
Proof.
  split.
  - induction l; simpl; auto; intros; unfold SubList; simpl; intros; try tauto.
    inv H.
    destruct H0; subst; rewrite createHide_Meths in *; firstorder fail.
  - unfold SubList; induction l; simpl; intros; try tauto.
    + constructor.
      admit.
    + assert (WfMod (createHide m l)) by firstorder fail.
      assert (In a (map fst (getMethods m))) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths.
      auto.
Admitted.

Lemma flatten_WfMod m: WfMod m -> WfMod (flatten m).
Proof.
  unfold flatten.
  induction 1; simpl; auto; intros.
  - constructor; auto.
    admit.
  - constructor; auto.
    rewrite createHide_Meths.
    auto.
  - unfold getFlat in *; simpl.
    rewrite WfMod_createHide in *; simpl in *.
    rewrite map_app.
    unfold SubList in *; intros.
    rewrite in_app_iff in *.
    specialize (IHWfMod1 x).
    specialize (IHWfMod2 x).
    tauto.
Admitted.




