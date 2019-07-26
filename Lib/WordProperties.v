Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv Eqdep.
Require Import Lib.Word.
Require Import Lia.
Require Import Omega.

Lemma eq_wordVal {sz} {x y : word sz} : wordVal _ x = wordVal _ y -> x = y.
Proof.
  intros.
  destruct x as [x px].
  destruct y as [y py].
  intros.
  simpl in *; subst; auto.
  apply f_equal, Eqdep_dec.UIP_dec. eapply Z.eq_dec.
Qed.


Lemma weqb_true: forall sz (a b: word sz), weqb _ a b = true -> a = b.
Proof.
  intros.
  unfold weqb in H.
  rewrite Z.eqb_eq in H.
  apply eq_wordVal.
  assumption.
Qed.


Lemma weqb_false: forall sz (a b: word sz), weqb _ a b = false -> a <> b.
Proof.
  intros.
  unfold weqb in H.
  rewrite Z.eqb_neq in H. congruence.
Qed.


Definition wlt_dec : forall sz (l r : word sz), {(wltu _ l r) = true} +  {(wltu _ l r) = false}.
Proof.
  intros.
  destruct (wltu sz l r).
  left. reflexivity.
  right.
  reflexivity.
Qed.

Lemma weq : forall sz (x y : word sz), {x = y} + {x <> y}.
Proof.
  intros.
  destruct (weqb _ x y) eqn:H.
  apply weqb_true in H.
  left. assumption.
  right.
  apply weqb_false in H.
  assumption.
Qed.

Fixpoint nat_cast (P : nat -> Type) {n m} : n = m -> P n -> P m.
  refine match n, m return n = m -> P n -> P m with
         | O, O => fun _ => id
         | S n, S m => fun pf => @nat_cast (fun n => P (S n)) n m (f_equal pred pf)
         | _, _ => fun pf => match _ pf : False with end
         end;
    clear; abstract congruence.
Defined.

Lemma nat_cast_eq_rect: forall (P : nat -> Type),
    forall (n m : nat)  (e: n = m) (pn: P n),
      nat_cast P e pn = eq_rect n P pn m e.
Proof.
  destruct e.
  revert dependent P; induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma nat_cast_same: forall (P: nat -> Type) (s: nat) (n: P s),
    nat_cast P eq_refl n = n.
Proof.
  intros. rewrite nat_cast_eq_rect. reflexivity.
Qed.


Fixpoint countLeadingZerosWord ni no: word ni -> word no :=
  match ni return word ni -> word no with
  | 0 => fun _ => (zToWord _ 0)
  | S m => fun e =>
             if (weq _ (@truncMsb 1 (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) (zToWord 1 0))
             then (wadd _ (zToWord _ 1) (@countLeadingZerosWord m no (@truncLsb m (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))))
             else (zToWord _ 0)
  end.


Lemma neq_wordVal sz w1 w2:
  w1 <> w2 ->
  wordVal sz w1 <> wordVal _ w2.
Proof.
  intros.
  intro.
  apply eq_wordVal in H0.
  contradiction.
Qed.

Lemma boundProof sz w:
  w mod 2^sz = w -> w < 2^sz.
Proof.
  intros sth0.
  simpl.
  pose proof (Nat.mod_upper_bound w (2 ^ sz) (@Nat.pow_nonzero 2 sz ltac:(intro; discriminate))) as sth.
  rewrite sth0 in sth.
  auto.
Qed.

Ltac discharge_pow_nonzero :=
  (apply Z.pow_nonzero;
   unfold not; intros; discriminate).

Hint Rewrite
     Z.lor_spec
     Z.lxor_spec
     Z.testbit_0_l
  : Z_bitwise_no_hyps.

Ltac rewrite_bitwise := repeat (autorewrite with Z_bitwise_no_hyps).

Ltac bitblast := repeat f_equal; eapply Z.bits_inj_iff; unfold Z.eqf; intros; rewrite_bitwise.

Lemma boundProofZ (sz : nat) (w : Z):
  (w mod (2^ Z.of_nat sz))%Z = w -> (0 <= w < (2^ Z.of_nat sz))%Z.
Proof.
  intros sth0.
  assert (forall sz', 0 < (2 ^ Z.of_nat sz'))%Z. {
    induction sz'.
    simpl. lia.
    rewrite Nat2Z.inj_succ.
    rewrite <- Z.add_1_l.
    rewrite Z.pow_add_r.
    lia.
    lia.
    lia. }
  specialize (Z.mod_pos_bound w _ (H sz)) as TMP; destruct TMP.
  rewrite sth0 in *; split; assumption.
Qed.

Ltac discharge_gt_0 :=
  (destruct wordVal;
   lia;
   lia).

Tactic Notation "unique" "pose" "proof" constr(defn) "as" ident(H) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn as H
  end.

Ltac arithmetizeWord :=
  repeat match goal with
         | w: word _ |- _ => destruct w
         end;
  unfold wordVal, wordBound in *;
  repeat match goal with
         | H: ?w1 <> ?w2 |- _ => match type of w1 with
                                 | word ?sz => apply neq_wordVal in H
                                 end; simpl in H
         | |- ?w1 = ?w2 => match type of w1 with
                           | word ?sz => apply eq_wordVal
                           end; simpl
         | H: (?w mod (2^(Z.of_nat ?sz)))%Z = ?w |- _ =>
           let sth := fresh in
           unique pose proof (boundProofZ sz _ H) as sth
         end;
  cbn [Z.modulo Z.pow_pos] in *.


Lemma word0_neq: forall w : word 1, w <> (zToWord 1 0) -> w = (zToWord 1 1).
Proof.
  intros.
  arithmetizeWord.
  unfold Z.modulo in *; simpl in *.
  unfold Z.pow_pos in *; simpl in *.
  lia.
Qed.


Lemma wor_wzero : forall sz w, wor _ (zToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wzero_wor: forall sz w, wor _  w (zToWord sz 0) = w.
Proof.
  intros.
  arithmetizeWord.
  rewrite Z.lor_0_r.
  assumption.
Qed.

Lemma unique_word_0 : forall a : word 0,
    a = zToWord 0 0.
Proof.
  intros.
  arithmetizeWord.
  simpl in *.
  unfold Z.modulo in *; simpl in *.
  lia.
Qed.

Lemma wzero_wplus: forall sz w, wadd _ (zToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wor_idemp :  forall (n : nat) (x0 : word n), wor _ x0 x0 = x0.
Proof.
  intros.
  induction x0.
  unfold wor.
  arithmetizeWord.
  rewrite Z.lor_diag.
  auto.
Qed.

Lemma Z_lt_div: forall (a b c : Z), (c > 0)%Z -> (a/c < b/c)%Z -> (a < b)%Z.
Proof.
  intros.
  destruct (Z_ge_lt_dec a b); auto.
  apply (Z_div_ge _ _ _ H) in g.
  exfalso; lia.
Qed.



Lemma truncMsbLtTrue : forall (n x : nat) (w1 w2 : word n),
    (wordVal _ (@truncMsb x _ w1) < wordVal _ (@truncMsb x _ w2))%Z ->
    wltu _ w1 w2 = true.
Proof.
  intros.
  arithmetizeWord.
  simpl in *.
  unfold wltu.
  
  destruct (zerop (n - x)).
  simpl in *.
  rewrite e in *; simpl in *.
  repeat rewrite Z.div_1_r in *.
  rewrite Nat.sub_0_le in e.
  specialize (Z.pow_le_mono_r_iff 2 (Z.of_nat n) (Z.of_nat x)) as P0.
  assert (1 < 2)%Z as TMP1; [lia|].
  specialize (Nat2Z.is_nonneg x) as TMP2.
  rewrite Nat2Z.inj_le in e.
  destruct P0; auto.
  specialize (H2 e).
  rewrite Z.ltb_lt.
  do 2 (rewrite Zmod_small in H); try lia.
  
  assert (2^(Z.of_nat (n - x)) > 0)%Z as P1.
  { apply Z.lt_gt, Z.pow_pos_nonneg;[lia|].
    apply Nat2Z.is_nonneg. }
  
  assert (Z.of_nat n = Z.of_nat x + Z.of_nat (n - x))%Z.
  { rewrite <- Nat2Z.inj_add.
    apply inj_eq.
    apply le_plus_minus.
    apply Z.gt_lt in P1.
    lia. }
  
  specialize (Z.pow_nonneg 2 (Z.of_nat (n - x))); intros.
  assert (0 <= 2)%Z.
  {
    lia.
  }
  specialize (H3 H4).
  assert (2 ^ (Z.of_nat n) = ((2 ^ (Z.of_nat x)) * (2 ^ Z.of_nat (n- x))))%Z.
  { rewrite <- Z.pow_add_r.
    rewrite <- H2.
    reflexivity.
    lia.
    lia. }
  assert (0 <= wordVal0 / 2 ^ Z.of_nat (n - x) < 2 ^ Z.of_nat x)%Z.
  { rewrite H5 in H1.
    destruct H1.
    apply Zdiv_lt_upper_bound in H6.
    split.
    apply Z.div_pos.
    auto.
    lia.
    auto.
    apply Z.pow_pos_nonneg.
    lia.
    lia. }
  assert (0 <= wordVal / 2 ^ Z.of_nat (n - x) < 2 ^ Z.of_nat x)%Z.
  {
    rewrite H5 in H0.
    destruct H0.
    apply Zdiv_lt_upper_bound in H7.
    split.
    apply Z.div_pos.
    auto.

    lia.
    auto.
    apply Z.pow_pos_nonneg.
    lia.
    lia. }
  apply Z.mod_small in H6.
  rewrite H6 in H.
  apply Z.mod_small in H7.
  rewrite H7 in H.
  rewrite Z.ltb_lt.
  apply(Z_lt_div _ _ _ P1 H).
Qed.


Lemma truncMsbLtFalse : forall (n x : nat) (w1 w2 : word n),
    (wordVal _ (@truncMsb x _ w1) < wordVal _ (@truncMsb x _ w2))%Z ->
    wltu _ w2 w1 = false.
Proof.
  intros.
  specialize (truncMsbLtTrue _ _ _ _ H).
  intros.
  unfold wltu in *.
  rewrite Z.ltb_lt in *.
  rewrite Z.ltb_nlt.
  lia.
Qed.
