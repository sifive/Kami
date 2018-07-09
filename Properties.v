Require Import Kami.Syntax.

Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.

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




  (* Lemma evalExpr_pack: forall k (e1 e2: k @# type), *)
  (*     evalExpr e1 = evalExpr e2 -> *)
  (*     evalExpr (pack e1) = evalExpr (pack e2). *)
  (* Proof. *)
  (*   intros. *)
  (*   induction k; simpl; rewrite ?H; try auto. *)
  (*   admit. *)
  (*   admit. *)
  (* Admitted. *)
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
 
Lemma Forall2_impl A B (P Q: A -> B -> Prop):
  (forall a b, P a b -> Q a b) ->
  forall la lb,
    Forall2 P la lb ->
    Forall2 Q la lb.
Proof.
  induction la; destruct lb; simpl; auto; intros.
  - inv H0; tauto.
  - inv H0; tauto.
  - inv H0; constructor; firstorder fail.
Qed.

Lemma Forall2_map_eq A B C (f: A -> C) (g: B -> C):
  forall la lb,
    Forall2 (fun a b => f a = g b) la lb ->
    map f la = map g lb.
Proof.
  induction la; destruct lb; simpl; auto; intros.
  - inv H.
  - inv H.
  - inv H.
    f_equal; firstorder fail.
Qed.

Lemma Forall2_app_eq_length A B (P: A -> B -> Prop) :
  forall l1a l2a l1b l2b,
    Forall2 P (l1a ++ l2a) (l1b ++ l2b) ->
    length l1a = length l1b ->
    Forall2 P l1a l1b /\
    Forall2 P l2a l2b.
Proof.
  induction l1a; simpl; auto; intros.
  - apply eq_sym in H0.
    rewrite length_zero_iff_nil in H0.
    subst; simpl in *.
    split; auto.
  - destruct l1b; simpl in *; [discriminate|].
    split; inv H; [| eapply IHl1a; eauto].
    constructor; auto.
    specialize (IHl1a _ _ _ H6).
    destruct IHl1a; auto.
Qed.

Lemma same_length_map_DisjKey A B (o: list (Attribute A)):
  forall (l1 l2: list (Attribute B)),
    map fst o = map fst l1 ++ map fst l2 ->
    DisjKey l1 l2 ->
    o = filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o ++
               filter (fun x => getBool (in_dec string_dec (fst x) (map fst l2))) o ->
    length (map fst l1) = length (filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o).
Proof.
  induction o; simpl; auto; intros.
  - apply eq_sym in H.
    apply app_eq_nil in H; subst; dest; subst.
    rewrite H; auto.
  - destruct l1; simpl; rewrite ?filter_false; auto; simpl in *.
    inv H; subst.
    rewrite H3 in *.
    destruct (string_dec (fst p) (fst p)); [simpl in *| exfalso; clear - n; tauto].
    inv H1.
    assert (sth: DisjKey l1 l2) by (clear - H0; firstorder fail).
    specialize (IHo _ _ H4 sth).
    destruct (in_dec string_dec (fst p) (map fst l2)); simpl in *.
    + unfold DisjKey in *.
      specialize (H0 (fst p)); simpl in *.
      destruct H0; tauto.
    + rewrite <- H2.
      simpl in *.
      assert (sth2:
                (fun x : string * A =>
                   getBool
                     match string_dec (fst p) (fst x) with
                     | left e => left (or_introl e)
                     | right n =>
                       match in_dec string_dec (fst x) (map fst l1) with
                       | left i => left (or_intror i)
                       | right n0 => right (fun H0 : fst p = fst x \/ In (fst x) (map fst l1) => match H0 with
                                                                                                 | or_introl Hc1 => n Hc1
                                                                                                 | or_intror Hc2 => n0 Hc2
                                                                                                 end)
                       end
                     end) = (fun x : string * A =>
                               match string_dec (fst p) (fst x) with
                               | left _ => true
                               | right _ =>
                                 getBool (in_dec string_dec (fst x) (map fst l1))
                               end)). {
        extensionality x.
        destruct (string_dec (fst p) (fst x)); auto.
        destruct (in_dec string_dec (fst x) (map fst l1)); auto.
      }
      setoid_rewrite sth2 in H2.
      setoid_rewrite sth2.
      clear sth2.
      destruct (in_dec string_dec (fst p) (map fst l1)).
      * assert (sth3: (fun x: string * A => if string_dec (fst p) (fst x) then true else getBool (in_dec string_dec (fst x) (map fst l1))) =
                      fun x => getBool (in_dec string_dec (fst x) (map fst l1))). {
          extensionality x.
          destruct (string_dec (fst p) (fst x)); auto.
          rewrite <- e0.
          destruct (in_dec string_dec (fst p) (map fst l1)); auto.
          exfalso; tauto.
        }
        rewrite sth3 in *.
        specialize (IHo H2).
        auto.
      * assert (sth2: ~ In (fst p) (map fst o)). {
          rewrite H4.
          rewrite in_app_iff.
          intro.
          tauto.
        }
        assert (sth3: filter (fun x: string * A => if string_dec (fst p) (fst x) then true else getBool (in_dec string_dec (fst x) (map fst l1))) o =
                      filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o). {
          clear - sth2.
          generalize p sth2; clear p sth2.
          induction o; simpl; auto; intros.
          assert (sth4: ~ In (fst p) (map fst o)) by tauto.
          assert (sth5: fst a <> fst p) by tauto.
          specialize (IHo _ sth4).
          rewrite IHo.
          destruct (string_dec (fst p) (fst a)); try tauto.
          rewrite e in *; tauto.
        }
        rewrite sth3 in *.
        specialize (IHo H2).
        auto.
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

  Local Notation optFullType := (fun fk => option (fullType type fk)).
  
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
      assert (sth: Forall2 (fun o' r => fst o' = fst r) o' (getAllRegisters (ConcatMod m1 m2))) by
          (eapply Forall2_impl; eauto; intros; simpl in *; tauto).
      apply Forall2_map_eq in sth.
      simpl in sth.
      rewrite map_app in sth.
      assert (DisjRegs': DisjKey (getAllRegisters m2) (getAllRegisters m1)) by
          (clear - DisjRegs; firstorder).
      match goal with
      | |- _ /\ _ /\ ?P /\ _ /\ _ => assert P by (eapply filter_map_app_sameKey; eauto)
      end.
      simpl in *.
      pose proof (same_length_map_DisjKey sth DisjRegs H) as sth2.
      rewrite H in HUpdRegs.
      apply Forall2_app_eq_length in HUpdRegs; auto; dest.
      repeat split; auto; constructor; auto; subst; rewrite ?filter_app in *.
      rewrite map_length in *.
      congruence.
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
      eapply Forall2_app in HUpdRegs0; eauto.
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
  - intros.
    assert (sth: Forall2 (fun o' r => fst o' = fst r) o' (getAllRegisters m)) by
        (eapply Forall2_impl; eauto; intros; simpl in *; tauto).
    clear HUpdRegs.
    apply Forall2_map_eq in sth.
    congruence.
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
  - assert (sth: Forall2 (fun o' r => (fun x => (fst x, projT1 (snd x))) o' = (fun x => (fst x, projT1 (snd x))) r) o' (getAllRegisters m)). {
      eapply Forall2_impl; eauto; intro; simpl in *.
      intros; dest.
      f_equal; auto.
    }
    clear HUpdRegs.
    apply Forall2_map_eq in sth.
    congruence.
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
  Variable initRel: forall rimp, Forall2 regInit rimp (getAllRegisters imp) -> exists rspec, Forall2 regInit rspec (getAllRegisters spec) /\ simRel rimp rspec.
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
    - pose proof (initRel HUpdRegs) as [rspec rspecProp].
      exists rspec, []; repeat split; dest; auto.
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
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) -> exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.
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

Lemma getAllRegisters_flatten: forall m, getAllRegisters (flatten m) = getAllRegisters m.
Proof.
  unfold flatten, getFlat; intros.
  rewrite createHide_Regs.
  auto.
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
      * pose proof (SemActionReadsSub m2 HAction).
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
      * pose proof (SemActionReadsSub m2 HAction).
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
    + pose proof (SemActionReadsSub m1 HAction).
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
    + pose proof (SemActionReadsSub m1 HAction).
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

Lemma flatten_Substeps m o l:
  Substeps m o l -> Substeps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l.
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

Definition strcmp (s1 s2 : string) : bool := if (string_dec s1 s2) then true else false.
Definition BaseModuleFilter (m : BaseModule)(fl : FullLabel) : bool :=
  match getRleOrMeth fl with
  | Rle rn => existsb (strcmp rn) (map fst (getRules m))
  | Meth f => existsb (strcmp (fst f)) (map fst (getMethods m))
  end.
Definition ModuleFilterLabels (m : BaseModule)(l : list FullLabel) : list FullLabel := filter (BaseModuleFilter m) l.

Lemma InRules_Filter : forall (u : RegsT)(rn : string)(rb : Action Void)(l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    In (rn, rb) (getRules m1) -> ModuleFilterLabels m1 ((u, (Rle rn, cs))::l) = ((u, (Rle rn, cs))::ModuleFilterLabels m1 l).
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp rn) (map fst (getRules m1))).
  destruct (existsb (strcmp rn) (map fst (getRules m1))); intro;[reflexivity | destruct H0; clear H0].
  assert (false=true);[apply H1; exists rn; split| discriminate].
  - apply in_map_iff; exists (rn, rb); auto.
  - unfold strcmp;destruct (string_dec rn rn);[reflexivity|contradiction].
Qed.

Lemma NotInRules_Filter : forall (u : RegsT)(rn : string)(l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    ~In rn (map fst (getRules m1)) ->  ModuleFilterLabels m1 ((u, (Rle rn, cs))::l) = ModuleFilterLabels m1 l.
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp rn) (map fst (getRules m1))).
  destruct (existsb (strcmp rn) (map fst (getRules m1))); intro H0; destruct H0;[|reflexivity].
  apply False_ind; apply H.
  assert (true=true) as TMP;[reflexivity|specialize (H0 TMP); dest].
  unfold strcmp in H2; destruct (string_dec rn x); subst;[assumption|discriminate].
Qed.

Lemma InMethods_Filter : forall (u : RegsT)(fn : string)(fb : {x : Signature & MethodT x})
                                (argV : type (fst (projT1 fb)))(retV : type (snd (projT1 fb)))
                                (l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    In (fn, fb) (getMethods m1) ->
    ModuleFilterLabels m1 ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::l) = ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)):: ModuleFilterLabels m1 l).
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp fn) (map fst (getMethods m1))).
  destruct (existsb (strcmp fn) (map fst (getMethods m1))); intro;[reflexivity | destruct H0; clear H0].
  assert (false=true);[apply H1; exists fn; split| discriminate].
  - apply in_map_iff; exists (fn, fb); auto.
  - unfold strcmp;destruct (string_dec fn fn);[reflexivity|contradiction].
Qed.

Lemma NotInMethods_Filter : forall  (u : RegsT)(fn : string)(fb : {x : Signature & MethodT x})
                                  (argV : type (fst (projT1 fb)))(retV : type (snd (projT1 fb)))
                                  (l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    ~In fn (map fst (getMethods m1)) -> ModuleFilterLabels m1 ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::l) = ModuleFilterLabels m1 l.
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp fn) (map fst (getMethods m1))).
  destruct (existsb (strcmp fn) (map fst (getMethods m1))); intro H0; destruct H0;[|reflexivity].
  apply False_ind; apply H.
  assert (true=true) as TMP;[reflexivity|specialize (H0 TMP); dest].
  unfold strcmp in H2; destruct (string_dec fn x); subst;[assumption|discriminate].
Qed.

Lemma InCall_split_InCall f l m1 :
  InCall f (ModuleFilterLabels m1 l) -> InCall f l.
Proof.
  unfold InCall, ModuleFilterLabels.
  intros; dest.
  generalize (filter_In (BaseModuleFilter m1) x l) as TMP; intro; destruct TMP as [L R];clear R; apply L in H; destruct H.
  exists x; split; assumption.
Qed.

Lemma InExec_split_InExec f l m1 :
  InExec f (ModuleFilterLabels m1 l) -> InExec f l.
Proof.
  unfold InExec, ModuleFilterLabels.
  intros.
  apply in_map_iff; apply in_map_iff in H;dest.
  exists x; split;[assumption|].
  generalize (filter_In (BaseModuleFilter m1) x l) as TMP; intro; destruct TMP as [L R]; clear R; apply L in H0; destruct H0.
  assumption.
Qed.

Lemma InCall_perm l l' f :
  InCall f l -> Permutation l l' -> InCall f l'.
  induction 2. assumption.
  - apply (InCall_app_iff f (x::nil) l').
    apply (InCall_app_iff f (x::nil) l) in H.
    destruct H;[left|right; apply IHPermutation];assumption.
  - apply (InCall_app_iff f (x::y::nil) l).
    apply (InCall_app_iff f (y::x::nil) l) in H.
    destruct H;[left;apply (InCall_app_iff f (x::nil) (y::nil)) | right];[apply (InCall_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
  - apply (IHPermutation2 (IHPermutation1 H)).
Qed.

Lemma InExec_perm l l' f :
  InExec f l -> Permutation l l' -> InExec f l'.
  induction 2. assumption.
  - apply (InExec_app_iff f (x::nil) l').
    apply (InExec_app_iff f (x::nil) l) in H.
    destruct H;[left|right; apply IHPermutation];assumption.
  - apply (InExec_app_iff f (x::y::nil) l).
    apply (InExec_app_iff f (y::x::nil) l) in H.
    destruct H;[left;apply (InExec_app_iff f (x::nil) (y::nil)) | right];[apply (InExec_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
  - apply (IHPermutation2 (IHPermutation1 H)).
Qed.

Lemma MatchingExecCalls_perm1 l1 l2 l3 m1 :
  MatchingExecCalls l1 l2 (Base m1) -> Permutation l1 l3 -> MatchingExecCalls l3 l2 (Base m1).
Proof.
  repeat intro.
  specialize (H f).
  apply H; auto.
  apply (InCall_perm H1 (Permutation_sym H0)).
Qed.


Lemma MatchingExecCalls_perm2 l1 l2 l3 m1 :
  MatchingExecCalls l1 l2 (Base m1) -> Permutation l2 l3 -> MatchingExecCalls l1 l3 (Base m1).
Proof.
  repeat intro.
  destruct (H f H1 H2);split;[assumption|].
  apply (InExec_perm _ H4 H0).
Qed.

Lemma MatchingExecCalls_perm l l' m1 :
  MatchingExecCalls l l (Base m1) -> Permutation l l' -> MatchingExecCalls l' l' (Base m1).
  repeat intro.
  specialize (H f).
  split; auto.
  apply (InExec_perm f (l := l) (l' := l')).
  - apply (Permutation_sym) in H0; specialize (H (InCall_perm (l := l') (l' := l) H1 H0) H2). destruct H. assumption.
  - assumption.
Qed.

Lemma InExec_ModuleFilterLabels : forall (f : MethT)(m : BaseModule)(l : list FullLabel),
    InExec f l ->
    In (fst f) (map fst (getMethods m)) ->
    InExec f (ModuleFilterLabels m l).
Proof.
  unfold InExec;intros.
  assert (existsb (strcmp (fst f)) (map fst (getMethods m)) = true);[apply (existsb_exists (strcmp (fst f))(map fst (getMethods m)));exists (fst f);split;
                                                                     [assumption|unfold strcmp; destruct (string_dec(fst f)(fst f));[reflexivity|contradiction]]|].
  induction l;[inversion H|].
  destruct H.
  - unfold ModuleFilterLabels, BaseModuleFilter.
    simpl; rewrite H. rewrite H1. fold ModuleFilterLabels.
    rewrite map_cons.
    left. assumption.
  - specialize (IHl H); unfold ModuleFilterLabels, BaseModuleFilter.
    simpl. destruct (fst (snd a)).
    + destruct (existsb (strcmp rn) (map fst (getRules m)));[|assumption].
      rewrite map_cons;simpl;right;assumption.
    + destruct (existsb (strcmp (fst f0)) (map fst (getMethods m)));[|assumption].
      rewrite map_cons;simpl;right;assumption.
Qed.

Lemma MatchingExecCalls_Split : forall (l : list FullLabel) (m1 m2 : BaseModule),
    MatchingExecCalls l l (Base (concatFlat m1 m2)) ->
    MatchingExecCalls (ModuleFilterLabels m1 l) (ModuleFilterLabels m1 l) (Base m1).
Proof.
  repeat intro. split;[auto|].
  specialize (H f (InCall_split_InCall _ _ H0)).
  unfold concatFlat in H; simpl in H, H1; rewrite (map_app) in H.
  specialize (in_app_iff (map fst (getMethods m1)) (map fst (getMethods m2)) (fst f)) as TMP; destruct TMP as [L R]; clear L.
  destruct (H (R (or_introl _ H1))).
  apply InExec_ModuleFilterLabels; assumption.
Qed.

Lemma MatchingExecCalls_Mix : forall (l : list FullLabel) (m1 m2 : BaseModule),
    MatchingExecCalls l l (Base (concatFlat m1 m2)) ->
    MatchingExecCalls (ModuleFilterLabels m1 l) (ModuleFilterLabels m2 l) (Base m2).
Proof.
  repeat intro. split;[auto|].
  specialize (H f (InCall_split_InCall _ _ H0)).
  unfold concatFlat in H; simpl in H, H1; rewrite map_app in H.
  specialize (in_app_iff (map fst (getMethods m1)) (map fst (getMethods m2)) (fst f)) as TMP; destruct TMP as [L R]; clear L.
  destruct (H (R (or_intror _ H1))).
  apply InExec_ModuleFilterLabels; assumption.
Qed.

Lemma MatchingExecCalls_Concat_comm : forall (l l' : list FullLabel) (m1 m2 : BaseModule),
    MatchingExecCalls l l' (Base (concatFlat m1 m2)) -> MatchingExecCalls l l' (Base (concatFlat m2 m1)).
Proof.
  repeat intro.
  specialize (H f H0).
  simpl in *. apply H.
  rewrite (map_app) in *; apply in_app_iff; apply in_app_iff in H1.
  destruct H1;[right|left];assumption.
Qed.

Ltac EqDep_subst :=
  repeat match goal with
         |[H : existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _] => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         end.

Lemma WfActionT_ReadsWellDefined : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                          (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    SemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr readRegs) (getKindAttr (getRegisters m1)).
Proof.
  induction 2; intros; subst; inversion H; EqDep_subst; auto.
  - rewrite map_app. repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H3 _ H0).
    + apply (IHSemAction2 (H5 v) _ H0).
  - inversion H; EqDep_subst. repeat intro. destruct H1;[subst;assumption|apply IHSemAction; auto].
  - rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H7 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - inversion H; EqDep_subst. rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H8 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - repeat intro; auto. contradiction.
Qed.

Lemma WfActionT_WritesWellDefined : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                           (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    SemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr newRegs) (getKindAttr (getRegisters m1)).
Proof.
  induction 2; intros; subst; inversion H; EqDep_subst; auto.
  - rewrite map_app. repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H3 _ H0).
    + apply (IHSemAction2 (H5 v) _ H0).
  - inversion H; EqDep_subst. repeat intro. destruct H1;[subst;assumption|apply IHSemAction; auto].
  - rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H7 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - inversion H; EqDep_subst. rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H8 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - repeat intro; auto. contradiction.
Qed.

Lemma KeyMatching : forall (l : RegsT) (a b : string * {x : FullKind & fullType type x}),
    NoDup (map fst l) -> In a l -> In b l -> fst a = fst b -> a = b.
Proof.
  induction l; intros.
  - inversion H0.
  - destruct H0; destruct H1.
    + symmetry; rewrite <- H1; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l b) in H1.
      apply False_ind. apply H5.
      destruct a0; destruct b; simpl in *.
      rewrite H2; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l a0) in H0.
      apply False_ind; apply H5.
      destruct a0, b; simpl in *.
      rewrite <- H2; assumption.
    + inversion H; subst.
      apply IHl; auto.
Qed.

Lemma KeyRefinement : forall (l l' : RegsT) (a : string * {x: FullKind & fullType type x}),
    NoDup (map fst l) -> SubList l' l -> In a l -> In (fst a) (map fst l') -> In a l'.
Proof.
  induction l'; intros; inversion H2; subst.
  - assert (In a (a::l')) as TMP;[left; reflexivity|specialize (H0 _ TMP); rewrite (KeyMatching _ _ _ H H0 H1 H3); left; reflexivity].
  - right; apply IHl'; auto.
    repeat intro.
    apply (H0 x (or_intror _ H4)).
Qed.

Lemma GKA_fst : forall (A B : Type)(P : B -> Type)(o : list (A * {x : B & P x})),
    (map fst o) = (map fst (getKindAttr o)).
Proof.
  induction o; simpl.
  - reflexivity.
  - rewrite IHo.
    reflexivity.
Qed.

Lemma NoDupKey_Expand : forall (A B : Type)(l1 l2 : list (A * B)),
    NoDup (map fst l1) ->
    NoDup (map fst l2) ->
    DisjKey l1 l2 ->
    NoDup (map fst (l1++l2)).
Proof.
  intros; rewrite (map_app fst).
  induction l1; auto.
  inversion_clear H.
  destruct (H1 (fst a)).
  - apply False_ind. apply H; left; reflexivity.
  - assert (~(In (fst a) ((map fst l1)++(map fst l2)))).
    + intro in_app12; apply in_app_iff in in_app12; destruct in_app12;[apply H2|apply H]; assumption.
    + assert (DisjKey l1 l2); repeat intro.
      * destruct (H1 k);[left|right];intro; apply H5;simpl;auto.
      * apply (NoDup_cons (fst a) (l:=(map fst l1 ++ map fst l2)) H4 (IHl1 H3 H5)).
Qed.

Lemma WfActionT_SemAction : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                   (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    NoDup (map fst o) ->
    SemAction o a readRegs newRegs calls retl ->
    (forall (o1 : RegsT),
        SubList o1 o ->
        getKindAttr o1 = getKindAttr (getRegisters m1) ->
        SemAction o1 a readRegs newRegs calls retl).
  induction 3; intro; subst; inversion H; EqDep_subst.
  - intros TMP1 TMP2; specialize (IHSemAction (H4 mret) o1 TMP1 TMP2).
    econstructor 1; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction H4 o1 TMP1 TMP2).
    econstructor 2; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction1 (H4) o1 TMP1 TMP2); specialize (IHSemAction2 (H6 v) o1 TMP1 TMP2).
    econstructor 3; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction (H4 valueV) o1 TMP1 TMP2).
    econstructor 4; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction (H5 regV) o1 TMP1 TMP2).
    econstructor 5; eauto.
    apply (KeyRefinement (r, existT (fullType type) regT regV) H0 TMP1 HRegVal).
    rewrite <- TMP2 in H7; apply (in_map fst) in H7; specialize (GKA_fst (A:=string)(fullType type) o1); intro.
    simpl in *.
    setoid_rewrite H2; assumption.
  - intros TMP1 TMP2; specialize (IHSemAction H5 o1 TMP1 TMP2).
    econstructor 6; eauto.
    rewrite TMP2; assumption.
  - intros TMP1 TMP2; specialize (IHSemAction1 H8 o1 TMP1 TMP2); specialize (IHSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 7; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction1 H9 o1 TMP1 TMP2); specialize (IHSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 8; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction H4 o1 TMP1 TMP2).
    econstructor 9; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction H4 o1 TMP1 TMP2).
    econstructor 10; eauto.
  - intros; econstructor 11; eauto.
Qed.

Lemma app_sublist_l : forall {A : Type} (l1 l2 l : list A),
    l = l1++l2 -> SubList l1 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); left; assumption.
Qed.

Lemma app_sublist_r : forall {A : Type} (l1 l2 l : list A),
    l = l1++l2 -> SubList l2 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); right; assumption.
Qed.

Section SplitSubsteps.
  Variable m1 m2: BaseModule.
  Variable DisjRegs: DisjKey (getRegisters m1) (getRegisters m2).
  Variable DisjRules: DisjKey (getRules m1) (getRules m2).
  Variable DisjMeths: DisjKey (getMethods m1) (getMethods m2).

  Variable WfMod1: WfBaseMod m1.
  Variable WfMod2: WfBaseMod m2.
  
  Lemma filter_perm o l :
    Substeps (concatFlat m1 m2) o l ->
    Permutation l ((ModuleFilterLabels m1 l)++(ModuleFilterLabels m2 l)).
    induction 1; subst.
    - simpl; apply Permutation_refl.
    - apply in_app_iff in HInRules.
      destruct HInRules as [HInRules | HInRules]; rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
      + destruct (DisjRules rn).
        * generalize (in_map_iff fst (getRules m1) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m1));[exists (rn, rb); auto| specialize (R H1); contradiction].
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjRules rn).
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHSubsteps).
        * generalize (in_map_iff fst (getRules m2) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m2));[exists (rn, rb); auto | specialize (R H1); contradiction].
    - apply in_app_iff in HInMeths.
      destruct HInMeths as [HInMeths | HInMeths]; rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
      + destruct (DisjMeths fn).
        * generalize (in_map_iff fst (getMethods m1) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m1)); [exists (fn, fb); auto| specialize (R H1); contradiction].
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjMeths fn).
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHSubsteps).
        * generalize (in_map_iff fst (getMethods m2) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m2)); [exists (fn, fb); auto| specialize (R H1); contradiction].
  Qed.

  Lemma split_Substeps1 o l:
    NoDup (map fst (getRegisters m1)) ->
    NoDup (map fst (getRegisters m2)) ->
    Substeps (concatFlat m1 m2) o l ->
    (exists o1 o2, getKindAttr o1 = getKindAttr (getRegisters m1) /\
                   getKindAttr o2 = getKindAttr (getRegisters m2) /\
                   o = o1++o2 /\
                   Substeps m1 o1 (ModuleFilterLabels m1 l) /\
                   Substeps m2 o2 (ModuleFilterLabels m2 l)).
  Proof.
    unfold concatFlat; induction 3; simpl in *.
    - rewrite map_app in *; apply list_split in HRegs; dest.
      exists x, x0;split;[|split;[|split;[|split;[constructor|constructor]]]];assumption.
    - rewrite map_app in *;apply in_app_iff in HInRules; specialize (DisjRules rn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInRules as [HInRules|HInRules];generalize (in_map fst _ _ HInRules);destruct DisjRules;try contradiction.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
        destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined (WfMod_Rle1 _ HInRules) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Rle1 _ HInRules) HAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m1 ls)); auto.
        * specialize (app_sublist_l _ _ H6) as SL_o_x.
          specialize (WfMod_Rle1 (rn, rb) HInRules); specialize (WfActionT_SemAction WfMod_Rle1 H2 HAction SL_o_x H4).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
          destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
        * rewrite (NotInRules_Filter _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0; split;[|split;[|split;[|split]]];auto.
        rewrite (NotInRules_Filter _ _ _ _ _ H3); assumption.
        rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
        destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined (WfMod_Rle2 _ HInRules) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Rle2 _ HInRules) HAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m2 ls)); auto.
        * specialize (app_sublist_r _ _ H6) as SL_o_x.
          specialize (WfMod_Rle2 (rn, rb) HInRules); specialize (WfActionT_SemAction WfMod_Rle2 H2 HAction SL_o_x H5).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
          destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
    - rewrite map_app in *;apply in_app_iff in HInMeths; specialize (DisjMeths fn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInMeths as [HInMeths|HInMeths];generalize (in_map fst _ _ HInMeths);destruct DisjMeths;try contradiction;intros.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        * rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined (WfMod_Meth1 (fn, fb) HInMeths argV) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Meth1 (fn, fb) HInMeths argV) HAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m1 ls)); auto.
          -- specialize (app_sublist_l _ _ H7) as SL_o_x.
             specialize (WfMod_Meth1 (fn, fb) HInMeths argV); specialize (WfActionT_SemAction WfMod_Meth1 H2 HAction SL_o_x H5).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
               destruct (L H10); assumption.
          -- intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
             destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]]; auto.
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
        * rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined (WfMod_Meth2 (fn, fb) HInMeths argV) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Meth2 (fn, fb) HInMeths argV) HAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m2 ls)); auto.
          -- specialize (app_sublist_r _ _ H7) as SL_o_x.
             specialize (WfMod_Meth2 (fn, fb) HInMeths argV); specialize (WfActionT_SemAction WfMod_Meth2 H2 HAction SL_o_x H6).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
               destruct (L H10); assumption.
          -- intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
             destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
  Qed.
  
  Lemma split_Substeps2 o l:
    Substeps (concatFlat m1 m2) o l ->
      (forall x y : FullLabel,
          In x (ModuleFilterLabels m1 l) ->
          In y (ModuleFilterLabels m2 l) ->
          match fst (snd x) with
          | Rle _ => match fst (snd y) with
                     | Rle _ => False
                     | Meth _ => True
                     end
          | Meth _ => True
          end) /\
      (forall x : MethT, InCall x (ModuleFilterLabels m1 l) -> InCall x (ModuleFilterLabels m2 l)
                         -> False).
    induction 1; intros; split; auto; subst.
    - intros; contradiction.
    - unfold InCall; intros; dest; contradiction.
    - simpl in HInRules.
      destruct (in_app_or _ _ _ HInRules) as [Rle_in | Rle_in]; specialize (in_map fst _ _ Rle_in) as map_Rle_in; destruct (DisjRules rn); try contradiction; rewrite (InRules_Filter u _ _ ls cs _ Rle_in);rewrite (NotInRules_Filter u _ ls cs _ H0); intros.
      + destruct H1.
        * rewrite <- H1; simpl.
          apply HNoRle.
          unfold ModuleFilterLabels in H2; apply filter_In in H2; destruct H2; assumption.
        * eapply IHSubsteps; eauto.
      + destruct H2.
        * rewrite <- H2; simpl.
          apply HNoRle.
          unfold ModuleFilterLabels in H1; apply filter_In in H1; destruct H1; assumption.
        * eapply IHSubsteps; eauto.
    - destruct (in_app_or _ _ _ HInRules) as [Rle_in | Rle_in]; specialize (in_map fst _ _ Rle_in) as map_Rle_in; destruct (DisjRules rn); try contradiction; rewrite (InRules_Filter u _ _ ls cs _ Rle_in);rewrite (NotInRules_Filter u _ ls cs _ H0); intros.
      + destruct (InCall_app_iff x (((u, (Rle rn, cs)))::nil) (ModuleFilterLabels m1 ls)) as [L R]; clear R.
        destruct (L H1); clear L.
        * unfold InCall in H3. dest.
          destruct H3;[subst|contradiction].
          apply InCall_split_InCall in H2.
          apply (HNoCall x); auto.
        * eapply IHSubsteps; eauto.
      + destruct (InCall_app_iff x (((u, (Rle rn, cs)))::nil) (ModuleFilterLabels m2 ls)) as [L R]; clear R.
        destruct (L H2); clear L.
        * unfold InCall in H3. dest.
          destruct H3;[subst|contradiction].
          apply InCall_split_InCall in H1.
          apply (HNoCall x); auto.
        * eapply IHSubsteps; eauto.
    - intros.
      unfold ModuleFilterLabels in *.
      specialize (filter_app (BaseModuleFilter m1) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H0; clear TMP.
      specialize (filter_app (BaseModuleFilter m2) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H1; clear TMP.
      destruct (in_app_or _ _ _ H0); destruct (in_app_or _ _ _ H1).
      + apply filter_In in H3; apply filter_In in H2. dest.
        destruct H2, H3; try contradiction.
        subst; simpl; auto.
      + apply filter_In in H2; destruct H2.
        destruct H2;[|contradiction].
        subst; simpl; auto.
      + apply filter_In in H3; destruct H3.
        destruct H3;[|contradiction].
        subst; simpl; auto.
        destruct (fst (snd x)); auto.
      + eapply IHSubsteps; eauto.
    - intros.
      destruct (DisjMeths fn).
      + setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H2) in H0.
        unfold ModuleFilterLabels in *.
        specialize (filter_app (BaseModuleFilter m2) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H1; clear TMP.
        destruct (InCall_app_iff x (filter (BaseModuleFilter m2) [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))]) (filter (BaseModuleFilter m2) ls)) as [L R]; clear R; destruct (L H1); clear L.
        * unfold InCall in H3; dest; apply filter_In in H3; destruct H3.
          destruct H3;[subst|contradiction].
          simpl in H6.
          apply InCall_split_InCall in H0.
          eapply HNoCall; eauto.
        * eapply IHSubsteps; eauto.
      + setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H2) in H1.
        unfold ModuleFilterLabels in *.
        specialize (filter_app (BaseModuleFilter m1) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H0; clear TMP.
        destruct (InCall_app_iff x (filter (BaseModuleFilter m1) [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))]) (filter (BaseModuleFilter m1) ls)) as [L R]; clear R; destruct (L H0); clear L.
        * unfold InCall in H3; dest; apply filter_In in H3; destruct H3.
          destruct H3;[subst|contradiction].
          simpl in H6.
          apply InCall_split_InCall in H1.
          eapply HNoCall; eauto.
        * eapply IHSubsteps; eauto.
  Qed.

End SplitSubsteps.

Definition WeakInclusion (l1 l2 : list FullLabel) : Prop := 
     (forall f : MethT, InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ ~ InCall f l2) /\
     (forall f : MethT, ~ InExec f l1 /\ InCall f l1 <-> ~ InExec f l2 /\ InCall f l2) /\
     (forall f : MethT, InExec f l1 /\ InCall f l1 \/ ~ InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ InCall f l2 \/ ~ InExec f l2 /\ ~ InCall f l2)
     /\ ((exists rle : string, In (Rle rle) (map getRleOrMeth l2)) -> exists rle : string, In (Rle rle) (map getRleOrMeth l1)).


Lemma InExec_app_comm : forall l1 l2 e, InExec e (l1++l2) -> InExec e (l2++l1).
Proof.
  intros.
  apply InExec_app_iff.
  apply InExec_app_iff in H.
  firstorder.
Qed.

Lemma InCall_app_comm : forall l1 l2 e, InCall e (l1++l2) -> InCall e (l2++l1).
Proof.
  intros.
  apply InCall_app_iff.
  apply InCall_app_iff in H.
  firstorder.
Qed.

Lemma WeakInclusion_app_comm : forall l1 l2, WeakInclusion (l1++l2)(l2++l1).
Proof.
  intros.
  unfold WeakInclusion.
  repeat try split; try destruct H; try intro; try apply H0; try apply H; try apply InCall_app_comm; try apply InExec_app_comm; try assumption.
  - destruct H; destruct H;[left; split;[apply InExec_app_comm|apply InCall_app_comm]; assumption|
                            right; split; intro TMP;[apply InExec_app_comm in TMP|apply InCall_app_comm in TMP];contradiction].
  - destruct H; destruct H;[left; split;[apply InExec_app_comm|apply InCall_app_comm]; assumption|
                            right; split; intro TMP;[apply InExec_app_comm in TMP|apply InCall_app_comm in TMP];contradiction].
  -dest; exists x.
   rewrite map_app in *; apply in_app_iff; apply in_app_iff in H; firstorder.
Qed.

Definition WeakEquality (l1 l2 : list FullLabel) : Prop :=
  WeakInclusion l1 l2 /\ WeakInclusion l2 l1.

Lemma commutative_Concat : forall m1 m2 o l,
    Step (ConcatMod m1 m2) o l ->
    exists l' o',
      Step (ConcatMod m2 m1) o' l' /\
      WeakEquality l l'.
Proof.
  intros.
  inversion_clear H.
  exists (l2++l1).
  exists (o2++o1).
  split.
  econstructor; try eassumption.
  intros.
  generalize (HNoRle y x H0 H).
  intros.
  destruct x. subst.
  destruct y. simpl in *.
  destruct p. destruct p0.
  simpl in *.
  destruct r2. assumption. destruct r1. assumption. assumption.
  intros. apply (HNoCall x); assumption.
  reflexivity.
  reflexivity.
  subst.
  split.
  apply WeakInclusion_app_comm.
  apply WeakInclusion_app_comm.
Qed.

Lemma WeakInclusionRefl : forall l, WeakInclusion l l.
  intros.
  unfold WeakInclusion.
  repeat try split; dest; try assumption.
  intros. assumption. intros. assumption. intros. assumption.
Qed.

Corollary WeakEqualityRefl : forall l, WeakEquality l l.
  intros.
  unfold WeakEquality.
  split; apply WeakInclusionRefl.
Qed.

Lemma WeakInclusionTrans : forall l1 l2 l3, WeakInclusion l1 l2 -> WeakInclusion l2 l3 -> WeakInclusion l1 l3.
  intros.
  unfold WeakInclusion in *.
  dest.
  split.
  intros.
  split. intros.
  apply H0. apply H. assumption.
  intros. apply H. apply H0. assumption.
  split. intros.
  split. intros. apply H1. apply H4. assumption.
  intros. apply H4; apply H1; assumption.
  split.
  intros. split. intros.
  apply H2. apply H5. assumption.
  intros.
  apply H5; apply H2; assumption.
  intros.
  apply H6. apply H3. assumption.
Qed.

Corollary WeakEqualityTrans : forall l1 l2 l3, WeakEquality l1 l2 -> WeakEquality l2 l3 -> WeakEquality l1 l3.
  intros.
  unfold WeakEquality in *. dest.
  split. apply (WeakInclusionTrans H H0).
  apply (WeakInclusionTrans H1 H2).
Qed.

Lemma WeakEqualitySym : forall l1 l2, WeakEquality l1 l2 -> WeakEquality l2 l1.
  intros.
  firstorder.
Qed.

Lemma WfNoDups m (HWfMod : WfMod m) :
    NoDup (map fst (getAllRegisters m)) /\
    NoDup (map fst (getAllMethods m))   /\
    NoDup (map fst (getAllRules m)).
Proof.
  induction m.
  - split;[|split];inversion HWfMod; assumption.
  - inversion HWfMod; subst; apply IHm in HWf.
    assumption.
  - inversion HWfMod;subst;destruct (IHm1 HWf1) as [ND_Regs1 [ND_Meths1 ND_Rles1]];destruct (IHm2 HWf2) as [ND_Regs2 [ND_Meths2 ND_Rles2]];split;[|split].
    + simpl;rewrite map_app.
      induction (getAllRegisters m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjRegs (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Regs1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Regs1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjRegs k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Regs1; assumption.
    + simpl;rewrite map_app.
      induction (getAllMethods m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjMeths (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Meths1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Meths1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjMeths k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Meths1; assumption.
    + simpl;rewrite map_app.
      induction (getAllRules m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjRules (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Rles1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Rles1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjRules k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Rles1; assumption.
Qed.

Lemma WfMod_WfBaseMod_flat m (HWfMod : WfMod m):
  WfBaseMod (getFlat m).
Proof.
  unfold getFlat;induction m.
  - simpl; inversion HWfMod; subst; destruct WfBaseModule.
    unfold WfBaseMod in *; split; intros.
    + specialize (H rule H1).
      induction H; econstructor; eauto.
    + specialize (H0 meth H1 v).
      induction H0; econstructor; eauto.
  - inversion_clear HWfMod.
    specialize (IHm HWf).
    assumption.
  - inversion_clear HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    simpl in *.
    constructor;simpl; intros; destruct (in_app_or _ _ _ H) as [In1 | In1].
    + destruct IHm1 as [Rle Meth]; clear Meth; specialize (Rle _ In1).
      induction Rle; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;left; assumption.
    + destruct IHm2 as [Rle Meth]; clear Meth; specialize (Rle _ In1).
      induction Rle; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;right; assumption.
    + destruct IHm1 as [Rle Meth]; clear Rle; specialize (Meth _ In1 v).
      induction Meth; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;left; assumption.
    + destruct IHm2 as [Rle Meth]; clear Rle; specialize (Meth _ In1 v).
      induction Meth; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;right;assumption.
Qed.

Lemma WfConcatNotInCalls : forall (m : Mod)(o : RegsT)(k : Kind)(a : ActionT type k)
                                  (readRegs newRegs : RegsT)(cs : MethsT)(fret : type k)
                                  (f : MethT),
    WfConcatActionT a m ->
    SemAction o a readRegs newRegs cs fret ->
    In (fst f) (getHidden m) ->
    ~In f cs.
Proof.
  intros.
  induction H0; subst; eauto; inversion H; EqDep_subst; eauto.
  - specialize (IHSemAction (H8 mret)).
    intro TMP; destruct TMP;[subst; contradiction|contradiction].
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
Qed.

Lemma WfConcats : forall (m1 m2 : Mod) (o : RegsT)(l : list FullLabel),
    WfConcat m2 m1 ->
    Substeps (getFlat m2) o l ->
    (forall (s: string)(v : {x : Kind*Kind & SignT x}), In s (getHidden m1) -> ~InCall (s, v) l).
Proof.
  intros.
  induction H0; subst.
  - intro; unfold InCall in H0. dest; contradiction.
  - inversion H; simpl in HInRules;specialize (H2 _ HInRules).
    intro T1. destruct (InCall_app_iff (s, v) ((u, (Rle rn, cs))::nil) ls) as [L R]; clear R; apply L in T1; clear L.
    destruct T1;[unfold InCall in H4;dest|contradiction].
    destruct H4;[subst|contradiction].
    eapply WfConcatNotInCalls; eauto.
    simpl; assumption.
  - inversion H; simpl in HInMeths;specialize (H3 _ HInMeths argV).
    intro T1. destruct (InCall_app_iff (s, v) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as [L R]; clear R; apply L in T1; clear L.
    destruct T1;[unfold InCall in H4; dest|contradiction].
    destruct H4;[subst|contradiction].
    eapply WfConcatNotInCalls; eauto.
    simpl; assumption.
Qed.

Lemma substitute_Step' m (HWfMod: WfMod m):
  forall o l,
    StepSubstitute m o l ->
    exists l', Permutation l l' /\
               Step m o l'.
Proof.
  unfold StepSubstitute.
  induction m; simpl in *; intros; dest.
  - exists l; split;[apply Permutation_refl|constructor; auto].
    eapply Substeps_flatten; eauto.
  - assert ((forall (s : string) (v : {x : Kind * Kind & SignT x}), In s (map fst (getAllMethods m)) -> In s (getHidden m) -> InExec (s, v) l -> InCall (s, v) l)).
    intros.
    apply (H1 s); auto.
    inv HWfMod; specialize (IHm HWf o l (conj H (conj H0 H2))).
    dest; exists x; split;[assumption|constructor; auto];intros.
    eapply (InCall_perm).
    + eapply H1; auto.
      eapply (InExec_perm);[|apply Permutation_sym];eauto;assumption.
    + assumption.
  - inv HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    destruct (WfNoDups HWf1) as [ND_Regs1 [ND_Meths1 ND_Rules1]].
    destruct (WfNoDups HWf2) as [ND_Regs2 [ND_Meths2 ND_Rules2]].
    specialize (WfMod_WfBaseMod_flat HWf1) as WfBaseMod1.
    specialize (WfMod_WfBaseMod_flat HWf2) as WfBaseMod2.
    pose proof (@split_Substeps1 (getFlat m1) (getFlat m2) HDisjRegs HDisjRules HDisjMeths WfBaseMod1 WfBaseMod2 _ _  ND_Regs1 ND_Regs2 H);dest.
    assert (Substeps (BaseMod (getAllRegisters m1) (getAllRules m1) (getAllMethods m1)) x (ModuleFilterLabels (getFlat m1) l) /\
            MatchingExecCalls (ModuleFilterLabels (getFlat m1) l) (ModuleFilterLabels (getFlat m1) l) (Base (getFlat m1)) /\
            (forall (s : string) (v : {x : Kind * Kind & SignT x}), In s (map fst (getAllMethods m1)) ->
                                                                    In s (getHidden m1) ->
                                                                    InExec (s, v) (ModuleFilterLabels (getFlat m1) l) ->
                                                                    InCall (s, v) (ModuleFilterLabels (getFlat m1) l))).
    + split;unfold getFlat at 1 in H5. assumption.
      split.
      * unfold getFlat in H0. simpl in H0.
        unfold getFlat; simpl.
        assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2))));[unfold concatFlat, getFlat;simpl; assumption|].
        apply (MatchingExecCalls_Split H7).
      * intros; specialize (WfConcats WfConcat2 H6 H8 (v:=v));intro.
        rewrite map_app in H1.
        specialize (H1 s v (in_or_app _ _ s (or_introl H7)) (in_or_app _ _ s (or_introl H8)) (InExec_split_InExec _ _ _ H9)).
        assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2)));[repeat intro; apply HDisjRules|].
        assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2)));[repeat intro;apply HDisjMeths|].
        specialize (filter_perm H11 H12 H) as P1.
        specialize (InCall_perm H1 P1) as InCall_filter.
        apply InCall_app_iff in InCall_filter.
        destruct InCall_filter;[assumption|contradiction].
    + assert (Substeps (BaseMod (getAllRegisters m2) (getAllRules m2) (getAllMethods m2)) x0 (ModuleFilterLabels (getFlat m2) l) /\
              MatchingExecCalls (ModuleFilterLabels (getFlat m2) l) (ModuleFilterLabels (getFlat m2) l) (Base (getFlat m2)) /\
              (forall (s : string) (v : {x : Kind * Kind & SignT x}), In s (map fst (getAllMethods m2)) ->
                                                                      In s (getHidden m2) ->
                                                                      InExec (s, v) (ModuleFilterLabels (getFlat m2) l) ->
                                                                      InCall (s, v) (ModuleFilterLabels (getFlat m2) l))).
      * split;unfold getFlat at 1 in H6. assumption.
        split.
        -- unfold getFlat in H0. simpl in H0.
           unfold getFlat; simpl.
           assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2))));[unfold concatFlat, getFlat;simpl; assumption|].
           apply MatchingExecCalls_Concat_comm in H8.
           apply (MatchingExecCalls_Split H8).
        --  intros; specialize (WfConcats WfConcat1 H5 H9 (v:=v));intro.
            rewrite map_app in H1.
            specialize (H1 s v (in_or_app _ _ s (or_intror H8)) (in_or_app _ _ s (or_intror H9)) (InExec_split_InExec _ _ _ H10)).
            assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2)));[repeat intro; apply HDisjRules|].
            assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2)));[repeat intro;apply HDisjMeths|].
            specialize (filter_perm H12 H13 H) as P1.
            specialize (InCall_perm H1 P1) as InCall_filter.
            apply InCall_app_iff in InCall_filter.
            destruct InCall_filter;[contradiction|assumption].
      * specialize (IHm1 x (ModuleFilterLabels (getFlat m1) l) H7).
        specialize (IHm2 x0 (ModuleFilterLabels (getFlat m2) l) H8). dest.
        exists (x2++x1).
        split.
        -- specialize (filter_perm (m1:=(getFlat m1)) (m2:=(getFlat m2)) HDisjRules HDisjMeths H).
           intro.
           specialize (Permutation_app H15 H13).
           intro.
           apply (Permutation_trans H17 H18).
        -- econstructor; eauto; specialize (split_Substeps2 (m1:=(getFlat m1)) (m2:=(getFlat m2)) HDisjRules HDisjMeths (o:=o)(l:=l) H); intros.
           ++ repeat intro.
              split.
              ** intro;specialize (WfConcats WfConcat1 H5 H20 (v:=(snd f)));intro;specialize (InCall_perm H18 (Permutation_sym H15)).
                 destruct f; simpl in *; intro; contradiction.
              ** assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2)))).
                 apply H0.
                 specialize (MatchingExecCalls_Mix H20).
                 intro.
                 destruct (MatchingExecCalls_perm2 (MatchingExecCalls_perm1 H21 H15) H13 H18 H19); assumption.
           ++ repeat intro.
              split.
              ** intro;specialize (WfConcats WfConcat2 H6 H20 (v:=(snd f)));intro;specialize (InCall_perm H18 (Permutation_sym H13)).
                 destruct f; simpl in *; intro; contradiction.
              ** assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2)))).
                 apply H0.
                 apply MatchingExecCalls_Concat_comm in H20.
                 specialize (MatchingExecCalls_Mix H20).
                 intro.
                 destruct (MatchingExecCalls_perm2 (MatchingExecCalls_perm1 H21 H13) H15 H18 H19); assumption.
           ++ repeat intro.
              specialize (Permutation_in x3 (Permutation_sym H15) H18); intro.
              specialize (Permutation_in y (Permutation_sym H13) H19); intro.
              eapply H17; eauto.
           ++ specialize (InCall_perm H18 (Permutation_sym H15)); intro.
              specialize (InCall_perm H19 (Permutation_sym H13)); intro.
              eapply H17; eauto.
Qed.

Inductive WeakInclusions : list (list FullLabel) -> list (list (FullLabel)) -> Prop :=
| WI_Nil : WeakInclusions nil nil
| WI_Cons : forall (ls ls' : list (list FullLabel)) (l l' : list FullLabel), WeakInclusions ls ls' -> WeakInclusion l l' -> WeakInclusions (l::ls)(l'::ls').

Definition WeakEqualities ls ls' := WeakInclusions ls ls' /\ WeakInclusions ls' ls.

Lemma WeakInclusionsRefl l : WeakInclusions l l.
Proof.
  induction l; constructor.
  - assumption.
  - apply WeakInclusionRefl.
Qed.

Corollary WeakEqualitiesRefl l : WeakEqualities l l.
Proof.
  unfold WeakEqualities; split; apply WeakInclusionsRefl.
Qed.

Lemma WeakInclusionsTrans : forall (l1 l2 l3 : list (list FullLabel)), WeakInclusions l1 l2 -> WeakInclusions l2 l3 -> WeakInclusions l1 l3.
Proof.
  induction l1, l2, l3; intros; auto; try inversion H; try inversion H0; subst.
  constructor.
  - apply (IHl1 _ _ H4 H10).
  - apply (WeakInclusionTrans H6 H12).
Qed.

Corollary WeakEqualitesTrans ls1 ls2 ls3 : WeakEqualities ls1 ls2 -> WeakEqualities ls2 ls3 -> WeakEqualities ls1 ls3.
Proof.
  unfold WeakEqualities; intros; dest; split; eapply WeakInclusionsTrans; eauto.
Qed.

Lemma WeakEqualitiesSymm ls1 ls2 : WeakEqualities ls1 ls2 -> WeakEqualities ls2 ls1.
Proof.
  firstorder.
Qed.

Lemma WeakInclusionsLen_consistent ls1 ls2 : WeakInclusions ls1 ls2 -> length ls1 = length ls2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma WeakInclusions_WeakInclusion : forall (ls1 ls2 : list (list FullLabel)),  WeakInclusions ls1 ls2 -> nthProp2 WeakInclusion ls1 ls2.
Proof.
  induction ls1, ls2; unfold nthProp2; intros; try destruct (nth_error nil i); auto; try inversion H; subst.
  -  apply WeakInclusionRefl.
  - destruct i; simpl;[|apply IHls1];assumption.
Qed.

Lemma WeakInclusion_WeakInclusions : forall (ls1 ls2 : list (list FullLabel)),
    length ls1 = length ls2 -> nthProp2 WeakInclusion ls1 ls2 -> WeakInclusions ls1 ls2.
Proof.
  induction ls1, ls2; intros; try constructor; try inversion H; try  apply nthProp2_cons in H0; try destruct H0;[apply (IHls1 _ H2 H0)|assumption].
Qed.

Definition TraceList (m : Mod) (ls : list (list FullLabel)) :=
  (exists (o : RegsT), Trace m o ls).

Definition TraceInclusion' (m m' : Mod) :=
  forall (o : RegsT)(ls : list (list FullLabel)), Trace m o ls -> exists (ls': list (list FullLabel)), TraceList m' ls' /\ WeakInclusions ls ls'.

Lemma TraceInclusion'_TraceInclusion : forall (m m' : Mod), TraceInclusion' m m' -> TraceInclusion m m'.
Proof.
  unfold TraceInclusion', TraceInclusion; intros; generalize (H o1 ls1 H0); unfold TraceList; intros; dest;exists x0, x.
  repeat split.
  - assumption.
  - apply (WeakInclusionsLen_consistent H2).
  - apply WeakInclusions_WeakInclusion;assumption.
Qed.

Lemma TraceInclusion_TraceInclusion' : forall (m m' : Mod), TraceInclusion m m' -> TraceInclusion' m m'.
Proof.
  unfold TraceInclusion'; intros; generalize (H _ _ H0); intros; dest; unfold TraceList; exists x0.
  split.
  - exists x; assumption.
  - apply (WeakInclusion_WeakInclusions H2 H3).
Qed.


Lemma PermutationInCall : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), InCall f l <-> InCall f l').
Proof.
  induction 1.
  - firstorder.
  - intro; split; intros; try assumption.
    + apply (InCall_app_iff f (x::nil) l'); apply (InCall_app_iff f (x::nil) l) in H0.
      destruct H0;[left|right;apply IHPermutation];assumption.
    + apply (InCall_app_iff f (x::nil) l); apply (InCall_app_iff f (x::nil) l') in H0.
      destruct H0;[left|right;apply IHPermutation];assumption.
  - split; intros.
    + apply (InCall_app_iff f (x::y::nil) l); apply (InCall_app_iff f (y::x::nil) l) in H.
      destruct H;[left;simpl|right];firstorder.
    +  apply (InCall_app_iff f (y::x::nil) l); apply (InCall_app_iff f (x::y::nil) l) in H;firstorder.
  - intros; split;intros.
    + apply IHPermutation2; apply IHPermutation1; assumption.
    + apply IHPermutation1; apply IHPermutation2; assumption.
Qed.

Corollary neg_PermutationInCall : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), ~InCall f l <-> ~InCall f l').
Proof.
  intros; split; repeat intro; apply H0;specialize (Permutation_sym H) as TMP;  eapply PermutationInCall; eauto.
Qed.

Lemma PermutationInExec : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), InExec f l <-> InExec f l').
Proof.
  induction 1; firstorder.
Qed.

Corollary neg_PermutationInExec : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), ~InExec f l <-> ~InExec f l').
Proof.
  intros; split; repeat intro; apply H0; specialize (Permutation_sym H) as TMP; eapply PermutationInExec; eauto.
Qed.

Ltac Permutation_replace :=
  match goal with
  |[H : InExec ?f ?l |- InExec ?f ?l'] =>
   match goal with
   |[H1 : Permutation ?l ?l' |- _] => apply (PermutationInExec H1); assumption
   |[H1 : Permutation ?l' ?l |- _] => apply (PermutationInExec (Permutation_sym H1)); assumption
   end
  |[H : InCall ?f ?l |- InCall ?f ?l'] =>
   match goal with
   |[H1 : Permutation ?l ?l' |- _] => apply (PermutationInCall H1); assumption
   |[H1 : Permutation ?l' ?l |- _] => apply (PermutationInCall (Permutation_sym H1)); assumption
   end
  |[H : ~InCall ?f ?l |- ~InCall ?f ?l'] =>
   match goal with
   |[H1 : Permutation ?l ?l' |- _] => apply (neg_PermutationInCall H1); assumption
   |[H1 : Permutation ?l' ?l |- _] => apply (neg_PermutationInCall (Permutation_sym H1)); assumption
   end
  |[H : ~InExec ?f ?l |- ~InExec ?f ?l'] =>
   match goal with
   |[H1 : Permutation ?l ?l' |- _] => apply (neg_PermutationInExec H1); assumption
   |[H1 : Permutation ?l' ?l |- _] => apply (neg_PermutationInExec (Permutation_sym H1)); assumption
   end
  end.

Lemma PermutationWI : forall (l l' : list FullLabel), Permutation l l' -> WeakInclusion l l'.
Proof.
  intros; unfold WeakInclusion.
  repeat split; dest; intros;[| | | | | | | |destruct H0;dest;[left|right];split|destruct H0;dest;[left|right];split|dest; exists x; induction H; auto; destruct H0;firstorder];Permutation_replace.
Qed.

Corollary PermutationWE : forall (l l' : list FullLabel), Permutation l l' -> WeakEquality l l'.
Proof.
  intros;unfold WeakEquality; split;[apply PermutationWI|apply PermutationWI;apply Permutation_sym];assumption.
Qed.

Lemma substitute_Step m o l (HWfMod: WfMod m):
  Step (flatten m) o l ->
  exists l',
    Permutation l l' /\
    Step m o l'.
Proof.
  rewrite StepSubstitute_flatten in *; auto.
  apply substitute_Step'; auto.
Qed.

Inductive PermutationEquivLists : (list (list FullLabel)) -> (list (list FullLabel)) -> Prop :=
|PermutationEquiv_nil : PermutationEquivLists nil nil
|PermutationEquiv_cons ls ls' l l' : PermutationEquivLists ls ls' -> Permutation l l' -> PermutationEquivLists (l::ls) (l'::ls').

Lemma PermutationEquivLists_WeakInclusions : forall (ls ls' : list (list FullLabel)),
    PermutationEquivLists ls ls' -> WeakInclusions ls ls'.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
    apply PermutationWI; assumption.
Qed.

Lemma UpdRegs_perm u u' o o' : UpdRegs u o o' -> Permutation u u' -> UpdRegs u' o o'.
Proof.
  unfold UpdRegs; intros; dest.
  split; auto.
  intros.
  specialize (H1 s v H2).
  destruct H1;[left|right].
  - dest; exists x;split;auto.
    eapply Permutation_in; eauto.
  - destruct H1; split;[intro; apply H1|assumption].
    dest; exists x; split;[|assumption].
    apply Permutation_sym in H0.
    eapply Permutation_in; eauto.
Qed.

Section TraceSubstitute.
  Variable m: Mod.
  Variable WfMod_m: WfMod m.

  Lemma Trace_flatten_same1: forall o l,  Trace m o l -> Trace (flatten m) o l.
  Proof.
    induction 1; subst.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply Step_substitute in HStep; auto.
      econstructor 2; eauto.
  Qed.

  Lemma Trace_flatten_same2: forall o l, Trace (flatten m) o l -> (exists l', (PermutationEquivLists l l') /\ Trace m o l').
  Proof.
    induction 1; subst.
    - rewrite getAllRegisters_flatten in *.
      exists nil;split;constructor 1; auto.
    - apply substitute_Step in HStep;auto; dest.
      exists (x0::x);split.
      + constructor; auto.
      + econstructor 2; eauto.
        apply (Permutation_map fst) in H2.
        eapply UpdRegs_perm; eauto.
  Qed.

  Lemma TraceInclusion_flatten_r: TraceInclusion m (flatten m).
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same1; auto.
  Qed.

  Lemma TraceInclusion_flatten_l: TraceInclusion (flatten m) m.
  Proof.
    apply TraceInclusion'_TraceInclusion.
    unfold TraceInclusion'; intros.
    apply Trace_flatten_same2 in H.
    dest.
    exists x.
    split.
    - unfold TraceList; exists o; auto.
    - apply PermutationEquivLists_WeakInclusions.
      assumption.
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

Lemma WfMod_createHide l: forall m, WfMod (createHide m l) <-> (SubList l (map fst (getMethods m)) /\ WfMod (Base m)).
Proof.
  split.
  - induction l; simpl; intros; split; unfold SubList; simpl; intros; try tauto.
    + inv H.
      destruct H0; subst; rewrite createHide_Meths in *; firstorder fail.
    + inv H.
      destruct (IHl HWf); assumption.
  - unfold SubList; induction l; simpl; intros; try tauto; dest; constructor.
    + rewrite createHide_Meths; apply (H a); left; reflexivity.
    + apply IHl; intros; split;auto.
Qed.

Lemma WfActionT_flatten m k :
  forall (a : ActionT type k),
    WfActionT m a <-> WfActionT (getFlat (Base m)) a.
Proof.
  split; induction 1; econstructor; eauto.
Qed.

Lemma flatten_WfMod m: WfMod m -> WfMod (flatten m).
Proof.
  unfold flatten.
  induction 1; simpl; auto; intros.
  - constructor; auto.
    unfold getFlat.
    induction WfBaseModule.
    constructor; intros.
    + specialize (H rule H1).
      apply WfActionT_flatten in H.
      assumption.
    + specialize (H0 meth H1 v).
      apply WfActionT_flatten in H0.
      assumption.
  - constructor; auto.
    rewrite createHide_Meths.
    auto.
  - unfold getFlat in *; simpl.
    rewrite WfMod_createHide in *; dest; simpl in *.
    split.
    + rewrite map_app.
      unfold SubList in *; intros.
      rewrite in_app_iff in *.
      specialize (H3 x).
      specialize (H1 x).
      tauto.
    + constructor;inversion H4; inversion H2; inversion WfBaseModule; inversion WfBaseModule0; subst.
      * split; intros.
        -- destruct (in_app_or _ _ _ H6).
           ++ specialize (H5 _ H7).
              induction H5; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; left; assumption.
           ++ specialize (H9 _ H7).
              induction H9; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; right; assumption.
        -- destruct (in_app_or _ _ _ H6).
           ++ specialize (H8 _ H7 v).
              induction H8; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; left; assumption.
           ++ specialize (H10 _ H7 v).
              induction H10; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; right; assumption.
      * apply (NoDupKey_Expand NoDupMeths NoDupMeths0 HDisjMeths).
      * apply (NoDupKey_Expand NoDupRegs NoDupRegs0 HDisjRegs).
      * apply (NoDupKey_Expand NoDupRle NoDupRle0 HDisjRules).
Qed.

Lemma word0_neq: forall w : word 1, w <> WO~0 -> w = WO~1.
Proof.
  intros.
  shatter_word w.
  destruct x; auto.
  tauto.
Qed.

Section test.
  Variable ty: Kind -> Type.
  Definition Slt2 n (e1 e2: Expr ty (SyntaxKind (Bit (n + 1)))) :=
    ITE (Eq (UniBit (TruncMsb n 1) e1) (Const ty WO~0))
        (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const ty WO~0)) (BinBitBool (LessThan _) e1 e2) (Const ty false))
        (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const ty WO~1)) (BinBitBool (LessThan _) e1 e2) (Const ty true)).
End test.

Lemma Slt_same n e1 e2: evalExpr (Slt2 n e1 e2) = evalExpr (Slt n e1 e2).
Proof.
  unfold Slt2, Slt.
  simpl.
  destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
  - rewrite e.
    destruct (weq (split2 n 1 (evalExpr e2)) WO~0); simpl; auto.
    + rewrite e0.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
    + destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
      * destruct (weq WO~0 (split2 n 1 (evalExpr e2))); simpl; auto.
      * destruct (weq WO~0 (split2 n 1 (evalExpr e2))); simpl; auto.
        apply word0_neq in n0.
        pre_word_omega.
        rewrite wordToNat_split2 in *.
        pose proof (pow2_zero n) as sth0.
        rewrite Nat.div_small_iff in e by lia.
        assert (sth: 0 < #(evalExpr e2) / pow2 n) by lia.
        rewrite Nat.div_str_pos_iff in sth; lia.
  - destruct (weq (split2 n 1 (evalExpr e2)) WO~0); simpl; auto.
    + rewrite e.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
      * destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
        apply word0_neq in n1.
        pre_word_omega.
        rewrite wordToNat_split2 in *.
        pose proof (pow2_zero n) as sth0.
        rewrite Nat.div_small_iff in e by lia.
        assert (sth: 0 < #(evalExpr e1) / pow2 n) by lia.
        rewrite Nat.div_str_pos_iff in sth; lia.
      * destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
        tauto.
    + apply word0_neq in n0.
      apply word0_neq in n1.
      rewrite ?n0, ?n1.
      simpl.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
Qed.

Lemma WfActionT_inlinesingle_f (k : Kind) (a : ActionT type k) (f : DefMethT) m :
  WfActionT m a ->
  WfActionT (inlinesingle_BaseModule m f) a.
Proof.
  intros.
  induction H; econstructor; auto.
Qed.

Lemma inline_preserves_key_Meth (f : DefMethT) (meth : DefMethT):
  fst (inlinesingle_Meth f meth) = fst meth.
Proof.
  destruct meth; auto.
Qed.

Corollary inline_preserves_keys_Meth (f : DefMethT) (l : list DefMethT) :
  (map fst (map (inlinesingle_Meth f) l)) = (map fst l).
Proof.
  induction l; auto.
  simpl;rewrite inline_preserves_key_Meth; rewrite IHl; reflexivity.
Qed.

Lemma inline_preserves_key_Rule (f : DefMethT) (rle : RuleT) :
  fst (inlinesingle_Rule f rle) = fst rle.
Proof.
  destruct rle; auto.
Qed.

Corollary inline_preserves_keys_Rule (f : DefMethT) (l : list RuleT) :
  (map fst (map (inlinesingle_Rule f) l)) = (map fst l).
Proof.
  induction l; auto.
  simpl; rewrite inline_preserves_key_Rule; rewrite IHl; reflexivity.
Qed.

Lemma inline_preserves_Regs_BaseMod m f:
  getRegisters m = getRegisters (inlinesingle_BaseModule m f).
Proof.
  unfold inlinesingle_BaseModule;eauto.
Qed.

Lemma inline_preserves_Regs_Mod m f:
  (getAllRegisters m) = getAllRegisters (inlinesingle_Mod m f).
Proof.
  intros.
  induction m; simpl;eauto using inline_preserves_Regs_BaseMod.
  rewrite IHm1, IHm2; reflexivity.
Qed.

Lemma WfActionT_inlinesingle (k :Kind) (a : ActionT type k) (f : DefMethT) m:
  WfActionT m a ->
  (forall v, WfActionT m (projT2 (snd f) type v)) ->
  WfActionT (inlinesingle_BaseModule m f) (inlineSingle f a).
  induction 1; try econstructor;eauto.
  simpl.
  destruct (string_dec (fst f) meth),(Signature_dec s (projT1 (snd f))); subst; econstructor; eauto.
  econstructor.
  specialize (H1 (evalExpr e)).
  apply (WfActionT_inlinesingle_f);eauto.
Qed.

Lemma DefMethT_body_Wf m f (Wfm : WfMod m):
  In f (getAllMethods m) ->
  (forall v, WfActionT (getFlat m) (projT2 (snd f) type v)).
Proof.
  induction m; intros.
  - inversion Wfm; subst.
    destruct (WfBaseModule) as [WfRule WfMeth]; clear WfRule; specialize (WfMeth _ H v).
    apply WfActionT_flatten in WfMeth; assumption.
  - inversion Wfm; subst.
    unfold getFlat in *; simpl in *.
    eapply IHm; eauto.
  - simpl in H; apply in_app_or in H.
    unfold getFlat in *; simpl in *.
    destruct H; inversion Wfm; subst; [specialize (IHm1 HWf1 H v) as TMP|specialize (IHm2 HWf2 H v) as TMP];
      induction (projT2 (snd f) type v); inv TMP; EqDep_subst; econstructor; eauto;
        simpl in *; rewrite map_app; apply in_or_app;[left|left|right|right]; assumption.
Qed.

Lemma inline_createHide_push f m l:
  inlinesingle_Mod (createHide m l) f = createHide (inlinesingle_BaseModule m f) l.
Proof.
  induction l; auto.
  unfold createHide; simpl; fold (createHide).
  rewrite IHl; reflexivity.
Qed.

Lemma inline_flattening_AllRegs f m :
  getAllRegisters (inlinesingle_Mod (flatten m) f) = getAllRegisters m.
Proof.
  unfold flatten.
  induction getHidden; simpl; auto.
Qed.

Lemma inline_flattening_Meths f m :
  getAllMethods (inlinesingle_Mod m f) = (map (inlinesingle_Meth f) (getAllMethods m)).
Proof.
  induction m; simpl; auto.
  rewrite map_app; rewrite IHm1, IHm2; reflexivity.
Qed.

Lemma inline_flattening_Rules f m :
  getAllRules (inlinesingle_Mod m f) = (map (inlinesingle_Rule f) (getAllRules m)).
Proof.
  induction m; simpl; auto.
  rewrite map_app; rewrite IHm1, IHm2; reflexivity.
Qed.

Lemma inline_getHidden f m :
  getHidden (inlinesingle_Mod m f) = getHidden m.
Proof.
  induction m; simpl; eauto.
  - rewrite IHm; reflexivity.
  - rewrite IHm1, IHm2; reflexivity.
Qed.

Corollary inline_flattening_Hidden f m :
  getHidden (inlinesingle_Mod (flatten m) f) = getHidden (inlinesingle_Mod m f).
Proof.
  repeat rewrite inline_getHidden.
  unfold flatten; rewrite createHide_hides; reflexivity.
Qed.

Lemma inline_flattening_flattens_inline f m:
  (flatten (inlinesingle_Mod m f)) = (inlinesingle_Mod (flatten m) f).
Proof.
  unfold flatten, getFlat.
  rewrite inline_getHidden.
  rewrite inline_flattening_Rules.
  rewrite inline_flattening_Meths.
  rewrite <- inline_preserves_Regs_Mod.
  rewrite inline_createHide_push.
  unfold inlinesingle_BaseModule; simpl.
  reflexivity.
Qed.

Lemma ActionT_rules rule f:
  (snd (inlinesingle_Rule f rule) type) = (inlineSingle f (snd rule type)).
Proof.
  destruct rule; simpl.
  reflexivity.
Qed.

Lemma ActionT_meths f m1 m2 m:
  inlinesingle_Meth f m1 = m2 ->
  (forall (v : type (fst (projT1 (snd f)))), WfActionT m (projT2 (snd f) type v)) ->
  (forall (v : type (fst (projT1 (snd m1)))), WfActionT m (projT2 (snd m1) type v)) ->
  (forall (v : type (fst (projT1 (snd m2)))), WfActionT (inlinesingle_BaseModule m f) (projT2 (snd m2) type v)).
Proof.
  intros.
  destruct m1, m2, s0; simpl in *.
  inversion H; subst; simpl in *.
  specialize (H1 v).
  eapply WfActionT_inlinesingle; eauto.
Qed.

Lemma WfMod_inline_WfMod m f :
  WfMod (Base m) ->
  In f (getMethods m) ->
  WfMod (Base (inlinesingle_BaseModule m f)).
Proof.
  intros; inv H; econstructor; eauto.
  - split; intros; simpl in *;inv WfBaseModule; eauto; pose proof (H2 _ H0); rewrite in_map_iff in H; dest.
    + specialize (H1 _ H4).
      specialize (WfActionT_inlinesingle _ H1 H3); intro; rewrite <- H.
      rewrite ActionT_rules; apply WfActionT_inlinesingle; eauto.
    + specialize (H2 _ H4).
      eapply ActionT_meths; eauto.
  - rewrite <- (inline_preserves_keys_Meth f (getMethods m)) in NoDupMeths; assumption.
  - rewrite <- (inline_preserves_keys_Rule f (getRules m)) in NoDupRle; assumption.
Qed.
      

Lemma inline_preserves_keys_Meth_Mod s m f:
  In s (map fst (getAllMethods m)) <-> In s (map fst (getAllMethods (inlinesingle_Mod m f))).
Proof.
  induction m; simpl; split; intros; eauto.
  - rewrite inline_preserves_keys_Meth; assumption.
  - rewrite inline_preserves_keys_Meth in H; assumption.
  - rewrite <- IHm; assumption.
  - rewrite IHm; assumption.
  - rewrite map_app in *; rewrite in_app_iff in *.
    destruct H;[left;rewrite <- IHm1|right;rewrite <- IHm2]; assumption.
  - rewrite map_app in *; rewrite in_app_iff in *.
    destruct H;[left;rewrite IHm1|right; rewrite IHm2]; assumption.
Qed.

Lemma inline_preserves_keys_Rules_Mod s m f :
  In s (map fst (getAllRules m)) <-> In s (map fst (getAllRules (inlinesingle_Mod m f))).
Proof.
  induction m; simpl;split; intros; eauto.
  - rewrite inline_preserves_keys_Rule; assumption.
  - rewrite inline_preserves_keys_Rule in H; assumption.
  - rewrite <- IHm; assumption.
  - rewrite IHm; assumption.
  - rewrite map_app in *; rewrite in_app_iff in *.
    destruct H;[left;rewrite <- IHm1|right;rewrite <- IHm2]; assumption.
  - rewrite map_app in *; rewrite in_app_iff in *.
    destruct H;[left;rewrite IHm1|right; rewrite IHm2]; assumption.
Qed.

Fixpoint updGatherMeth (s : string) (ls : list FullLabel) : RegsT :=
  match ls with
  | a::ls' => match getRleOrMeth a with
              | Rle _ => updGatherMeth s ls'
              | Meth f => match string_dec s (fst f) with
                           | left _ => (fst a)++(updGatherMeth s ls')
                           | right _ => updGatherMeth s ls'
                           end
              end
  | nil => nil
  end.

Fixpoint elimMethExec (s : string) (ls : list FullLabel) : list FullLabel :=
  match ls with
  | a::ls' => match getRleOrMeth a with
              |Rle _ => a::(elimMethExec s ls')
              |Meth f => match string_dec s (fst f) with
                         | left _ => elimMethExec s ls'
                         | right _ => a::(elimMethExec s ls')
                         end
              end
  | nil => nil
  end.

Fixpoint inlineCall (f : MethT)(fcalls : MethsT)(fcalled : MethsT) : MethsT :=
  match fcalled with
  | g::fcalled' => match MethT_dec f g with
             | left _ => fcalls++(inlineCall f fcalls fcalled')
             | right _ => g::(inlineCall f fcalls fcalled')
             end
  | nil => nil
  end.

Fixpoint mergeSeparatedBaseMod (bl : list BaseModule) : Mod :=
  match bl with
  | b::bl' => ConcatMod (Base b) (mergeSeparatedBaseMod bl')
  | nil => Base (BaseMod nil nil nil)
  end.

Fixpoint mergeSeparatedBaseFile (rfl : list RegFileBase) : Mod :=
  match rfl with
  | rf::rfl' => ConcatMod (Base (BaseRegFile rf))(mergeSeparatedBaseFile rfl')
  | nil => Base (BaseMod nil nil nil)
  end.

Fixpoint createHide' (m : Mod) (hides : list string) : Mod :=
  match hides with
  | nil => m
  | h::hides' => HideMeth (createHide' m hides') h
  end.

Definition mergeSeparatedMod (hl : list string)(rfl : list RegFileBase) (bl : list BaseModule) :=
  createHide' (ConcatMod (mergeSeparatedBaseFile rfl) (mergeSeparatedBaseMod bl)) hl.
 
Lemma mergeSeparatedBaseFile_noHides (rfl : list RegFileBase) :
  getHidden (mergeSeparatedBaseFile rfl) = nil.
Proof.
  induction rfl; auto.
Qed.

Lemma mergeSeparatedBaseMod_noHides (bl : list BaseModule) :
  getHidden (mergeSeparatedBaseMod bl) = nil.
Proof.
  induction bl; auto.
Qed.

Lemma getHidden_createHide' (m : Mod) (hides : list string) :
  getHidden (createHide' m hides) = hides++(getHidden m).
Proof.
  induction hides; auto.
  - simpl; rewrite IHhides; reflexivity.
Qed.

Lemma getAllRegisters_createHide' (m : Mod) (hides : list string) :
  getAllRegisters (createHide' m hides) = getAllRegisters m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllRegisters_mergeBaseFile (rfl : list RegFileBase) :
  getAllRegisters (mergeSeparatedBaseFile rfl) = (concat (map getRegFileRegisters rfl)).
Proof.
  induction rfl;auto.
  simpl; rewrite IHrfl; reflexivity.
Qed.

Lemma getAllRegisters_mergeBaseMod (bl : list BaseModule) :
  getAllRegisters (mergeSeparatedBaseMod bl) = (concat (map getRegisters bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.

Lemma getAllMethods_createHide' (m : Mod) (hides : list string) :
  getAllMethods (createHide' m hides) = getAllMethods m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllMethods_mergeBaseFile (rfl : list RegFileBase) :
  getAllMethods (mergeSeparatedBaseFile rfl) = (concat (map getRegFileMethods rfl)).
Proof.
  induction rfl;auto.
  simpl; rewrite IHrfl; reflexivity.
Qed.

Lemma getAllMethods_mergeBaseMod (bl : list BaseModule) :
  getAllMethods (mergeSeparatedBaseMod bl) = (concat (map getMethods bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.

Lemma getAllRules_createHide' (m : Mod) (hides : list string) :
  getAllRules (createHide' m hides) = getAllRules m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllRules_mergeBaseFile (rfl : list RegFileBase) :
  getAllRules (mergeSeparatedBaseFile rfl) = nil.
Proof.
  induction rfl;auto.
Qed.

Lemma getAllRules_mergeBaseMod (bl : list BaseModule) :
  getAllRules (mergeSeparatedBaseMod bl) = (concat (map getRules bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.

Lemma separateBaseMod_flatten (m : Mod) :
  getAllRegisters m [=] getAllRegisters (mergeSeparatedMod (fst (separateMod m)) (fst (snd (separateMod m))) (snd (snd (separateMod m)))).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllRegisters_createHide'.
  unfold separateMod; simpl.
  rewrite getAllRegisters_mergeBaseFile, getAllRegisters_mergeBaseMod.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    repeat rewrite <- app_assoc; apply Permutation_app_head.
    repeat rewrite app_assoc; apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.

Lemma separateBaseModule_flatten_Methods (m : Mod) :
  getAllMethods m [=] getAllMethods (mergeSeparatedMod (fst (separateMod m)) (fst (snd (separateMod m))) (snd (snd (separateMod m)))).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllMethods_createHide'.
  unfold separateMod; simpl.
  rewrite getAllMethods_mergeBaseFile, getAllMethods_mergeBaseMod.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    repeat rewrite <- app_assoc; apply Permutation_app_head.
    repeat rewrite app_assoc; apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.

Lemma separateBaseModule_flatten_Rules (m : Mod) :
  getAllRules m [=] getAllRules (mergeSeparatedMod (fst (separateMod m)) (fst (snd (separateMod m))) (snd (snd (separateMod m)))).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllRules_createHide'.
  unfold separateMod; simpl.
  rewrite getAllRules_mergeBaseFile, getAllRules_mergeBaseMod; simpl.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    reflexivity.
Qed.

Lemma separateBaseModule_flatten_Hides (m : Mod) :
  getHidden m [=] getHidden (mergeSeparatedMod (fst (separateMod m)) (fst (snd (separateMod m))) (snd (snd (separateMod m)))).
  unfold mergeSeparatedMod.
  rewrite getHidden_createHide';simpl.
  rewrite mergeSeparatedBaseFile_noHides.
  rewrite mergeSeparatedBaseMod_noHides.
  repeat rewrite app_nil_r.
  reflexivity.
Qed.