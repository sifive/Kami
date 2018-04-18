Require Import bbv.Word Psatz PeanoNat Lib.EclecticLib Bool.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope word.
Open Scope nat.

Lemma wzero_wones: forall sz, sz >= 1 ->
                              natToWord sz 0 <> wones sz.
Proof.
  intros.
  unfold not.
  intros.
  pose proof (f_equal (@wordToNat sz) H0) as sth.
  unfold wzero in *.
  rewrite roundTrip_0 in *.
  rewrite wones_pow2_minus_one in sth.
  destruct sz; [lia | ].
  pose proof (NatLib.one_lt_pow2 sz).
  lia.
Qed.

Lemma wzero_wplus: forall sz w, wzero sz ^+ w = w.
Proof.
  intros.
  unfold wzero.
  apply wplus_unit.
Qed.

Lemma wordToNat_nonZero sz (w: word sz):
  w <> wzero sz -> wordToNat w > 0.
Proof.
  induction w; simpl; unfold wzero; simpl; intros.
  - tauto.
  - destruct b.
    + lia.
    + assert (sth: w <> (natToWord n 0)).
      { intro.
        subst.
        tauto.
      }
      assert (sth2: wordToNat w <> 0).
      { intro sth3.
        specialize (IHw sth).
        lia.
      }
      lia.
Qed.

Lemma split2_pow2: forall sz n,
    2 ^ sz <= n < 2 ^ S sz ->
    wordToNat (split2 sz 1 (natToWord (sz + 1) n)) = 1.
Proof.
  intros.
  rewrite wordToNat_split2.
  simpl in *.
  rewrite Nat.add_0_r in *.
  (* pose proof (wordToNat_natToWord sz n). *)
  rewrite wordToNat_natToWord_bound with (bound := wones _).
  - destruct H.
    assert (sth: pow2 sz <> 0) by lia.
    pose proof (Nat.div_le_mono _ _ (pow2 sz) sth H) as sth2.
    rewrite Nat.div_same in sth2 by auto.
    apply Nat.lt_le_pred in H0.
    pose proof (Nat.div_le_mono _ _ (pow2 sz) sth H0) as sth3.
    rewrite <- Nat.sub_1_r in sth3.
    assert (sth4: pow2 sz = 1 * pow2 sz) by lia.
    rewrite sth4 in sth3 at 2.
    assert (sth5: 1 * pow2 sz + pow2 sz - 1 = 1 * pow2 sz + (pow2 sz - 1)) by lia.
    rewrite sth5 in sth3.
    rewrite Nat.div_add_l in sth3 by lia.
    rewrite Nat.div_small with (a := pow2 sz - 1) in sth3 by lia.
    lia.
  - rewrite wones_pow2_minus_one.
    assert (sth: sz + 1 = S sz) by lia.
    rewrite sth.
    simpl.
    lia.
Qed.

Lemma combine_wones_WO sz:
  forall w, w <> wzero sz -> split2 sz 1 (combine (wones sz) ($ 0) ^+ combine w ($ 0)) = WO~1.
Proof.
  intros.
  match goal with
  | |- split2 _ _ (?a ^+ ?b) = _ =>
    rewrite <- (@natToWord_wordToNat _ a);
      rewrite <- (@natToWord_wordToNat _ b)
  end.
  rewrite <- natToWord_plus.
  rewrite ?wordToNat_combine.
  simpl.
  rewrite wones_pow2_minus_one.
  pose proof (wordToNat_bound w) as sth.
  pose proof (wordToNat_nonZero H).
  assert (sth2: 2^sz <= 2 ^ sz - 1 + wordToNat w < 2 ^ (S sz)). {
    pose proof (pow2_zero sz) as sth3.
    split; simpl; lia.
  }
  apply split2_pow2 in sth2.
  rewrite Nat.mul_0_r.
  rewrite ?Nat.add_0_r.
  apply (f_equal (natToWord 1)) in sth2.
  rewrite natToWord_wordToNat in sth2.
  assumption.
Qed.

Lemma wordToNat_plus sz (w1 w2: word sz):
  natToWord sz (wordToNat w1 + wordToNat w2) = w1 ^+ w2.
Proof.
  rewrite natToWord_plus.
  rewrite ?natToWord_wordToNat.
  auto.
Qed.

(*
  Lemma split1_wplus sz1 sz2 (w1 w2: word (sz1 + sz2)):
    split1 _ _ (w1 ^+ w2) = split1 sz1 _ w1 ^+ split1 _ _ w2.
  Proof.
    rewrite <- natToWord_wordToNat at 1.
    rewrite wordToNat_split1.
    
    (w12 w22: word sz2):
    split1 _ _ (combine w11 w12 ^+ combine w21 w22) = w11 ^+ w21.
  Proof.
 *)

Lemma wordToNat_natToWord_eqn sz:
  forall n,
    wordToNat (natToWord sz n) = n mod (pow2 sz).
Proof.
  intros.
  pose proof (wordToNat_natToWord sz n).
  destruct H as [? [? ?]].
  rewrite H.
  assert (sth: pow2 sz * x = x * pow2 sz) by lia.
  rewrite <- sth in *.
  clear sth.
  pose proof (wordToNat_bound (natToWord sz n)).
  apply (Nat.mod_unique n (pow2 sz) x (n - pow2 sz * x)); try lia.
Qed.

Lemma mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros.
  pose proof (Nat.mod_mul_r a _ _ H H0).
  rewrite H1.
  rewrite Nat.add_mod_idemp_l by auto.
  rewrite Nat.add_mod by auto.
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by nia.
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma split1_combine_wplus sz1 sz2 (w11 w21: word sz1) (w12 w22: word sz2):
  split1 _ _ (combine w11 w12 ^+ combine w21 w22) = w11 ^+ w21.
Proof.
  rewrite <- natToWord_wordToNat at 1.
  rewrite wordToNat_split1.
  rewrite <- wordToNat_plus.
  rewrite ?wordToNat_combine.
  assert (sth: #w11 + pow2 sz1 * #w12 + (#w21 + pow2 sz1 * #w22) = #w11 + #w21 + pow2 sz1 * (#w12 + #w22)) by lia.
  rewrite wordToNat_natToWord_eqn.
  rewrite sth.
  rewrite Nat.pow_add_r.
  assert (pow2 sz1 <> 0) by (pose proof (pow2_zero sz1); intro; lia).
  assert (pow2 sz2 <> 0) by (pose proof (pow2_zero sz2); intro; lia).
  rewrite mod_factor by auto.
  rewrite Nat.add_mod by auto.
  assert (sth2: pow2 sz1 * (# w12 + #w22) = (#w12 + #w22) * pow2 sz1) by nia.
  rewrite sth2.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  rewrite <- wordToNat_natToWord_eqn.
  rewrite natToWord_wordToNat.
  rewrite natToWord_plus.
  rewrite ?natToWord_wordToNat.
  auto.
Qed.

Lemma div_2 a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a / b = 1.
Proof.
  intros.
  assert (sth: b * 1 <= a) by lia.
  pose proof (Nat.div_le_lower_bound a b 1 H sth).
  pose proof (Nat.div_lt_upper_bound a b 2 H H0).
  lia.
Qed.

Lemma mod_sub a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a mod b = a - b.
Proof.
  intros.
  rewrite Nat.mod_eq; auto.
  repeat f_equal.
  rewrite div_2 by auto.
  rewrite Nat.mul_1_r; auto.
Qed.

Lemma wordToNat_wneg_non_0 sz: forall (a: word sz),
    a <> natToWord _ 0 ->
    # (wneg a) = pow2 sz - #a.
Proof.
  intros.
  unfold wneg.
  rewrite pow2_N.
  rewrite NToWord_nat.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite wordToN_to_nat.
  rewrite Nnat.Nat2N.id.
  simpl.
  rewrite wordToNat_natToWord_idempotent'; auto.
  assert (#a <> 0) by word_omega.
  pose proof (pow2_zero sz).
  lia.
Qed.

Lemma wordToNat_wnot sz: forall (a: word sz),
    # (wnot a) = pow2 sz - #a - 1.
Proof.
  intros.
  rewrite wnot_def.
  rewrite pow2_N.
  rewrite NToWord_nat.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite Nnat.N2Nat.inj_sub.
  rewrite wordToN_to_nat.
  rewrite Nnat.Nat2N.id.
  simpl.
  rewrite wordToNat_natToWord_idempotent'; auto.
  pose proof (pow2_zero sz).
  lia.
Qed.

Lemma wzero_wor: forall sz w, w ^| wzero sz = w.
Proof.
  intros.
  rewrite wor_comm.
  rewrite wor_wzero.
  auto.
Qed.

Lemma bool_prop1: forall a b, a && negb (a && b) = a && negb b.
Proof.
  destruct a, b; simpl; auto.
Qed.

Lemma wordToNat_wplus sz (w1 w2: word sz):
  #(w1 ^+ w2) = (#w1 + #w2) mod (pow2 sz).
Proof.
  rewrite <- (natToWord_wordToNat w1) at 1.
  rewrite <- (natToWord_wordToNat w2) at 1.
  rewrite <- natToWord_plus.
  rewrite wordToNat_natToWord_eqn.
  auto.
Qed.

Lemma wor_r_wzero_1 sz:
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w2 = natToWord sz 0.
Proof.
  induction w1; simpl; auto; intros.
  pose proof (shatter_word w2) as sth.
  simpl in sth.
  rewrite sth in *.
  unfold wor in H.
  simpl in H.
  unfold natToWord in H.
  unfold natToWord.
  fold (natToWord n (Nat.div2 0)) in *.
  unfold Nat.div2, mod2 in *.
  inversion H.
  destruct_existT.
  rewrite (IHw1 _ H2).
  f_equal.
  destruct b, (whd w2); auto.
Qed.

Lemma wor_r_wzero_2 sz:
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w1 = natToWord sz 0.
Proof.
  induction w1; simpl; auto; intros.
  pose proof (shatter_word w2) as sth.
  simpl in sth.
  rewrite sth in *.
  unfold wor in H.
  simpl in H.
  unfold natToWord in H.
  unfold natToWord.
  fold (natToWord n (Nat.div2 0)) in *.
  unfold Nat.div2, mod2 in *.
  inversion H.
  destruct_existT.
  rewrite (IHw1 _ H2).
  f_equal.
  destruct b, (whd w2); auto.
Qed.
Fixpoint nat_cast (P : nat -> Type) {n m} : n = m -> P n -> P m.
      refine match n, m return n = m -> P n -> P m with
             | O, O => fun _ => id
             | S n, S m => fun pf => @nat_cast (fun n => P (S n)) n m (f_equal pred pf)
             | _, _ => fun pf => match _ pf : False with end
             end;
        clear; abstract congruence.
    Defined.


Fixpoint countLeadingZerosWord ni no: word ni -> word no :=
  match ni return word ni -> word no with
  | 0 => fun _ => $ 0
  | S m => fun e =>
             if getBool (weq (split2 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) WO~0)
             then $ 1 ^+ @countLeadingZerosWord m no (split1 m 1 (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))
             else $ 0
  end.


Lemma countLeadingZerosWord_le_len no ni:
  ni < pow2 no ->
  forall w: word ni, (countLeadingZerosWord no w <= natToWord _ ni)%word.
Proof.
  induction ni; simpl; auto; intros.
  - word_omega.
  - match goal with
    | |- ((if getBool ?P then _ else _) <= _)%word => destruct P; simpl; auto
    end; [| word_omega].
    assert (sth: ni < pow2 no) by lia.
    specialize (IHni sth).
    assert (sth1: natToWord no (S ni) = natToWord no (1 + ni)) by auto.
    rewrite sth1.
    rewrite natToWord_plus.
    match goal with
    | |- ((_ ^+ countLeadingZerosWord no ?P) <= _)%word => specialize (IHni P)
    end.
    match goal with
    | |- (?a ^+ ?b <= ?c ^+ ?d)%word =>
      rewrite (wplus_comm a b); rewrite (wplus_comm c d)
    end.
    pre_word_omega.
    assert (sth2: no > 0). {
      destruct no; [|lia].
      destruct ni; simpl in *; try lia.
    }
    rewrite <- ?(@natplus1_wordplus1_eq _ _ (wones no)); auto.
    + lia.
    + pre_word_omega.
      rewrite wordToNat_natToWord_eqn.
      rewrite Nat.mod_small; auto.
      lia.
    + pre_word_omega.
      rewrite wordToNat_natToWord_eqn in IHni.
      rewrite Nat.mod_small in IHni; auto.
      lia.
Qed.



Close Scope nat.
Close Scope word.
