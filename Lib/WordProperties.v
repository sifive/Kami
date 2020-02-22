Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv Eqdep.
Require Import Kami.Lib.Word.
Require Import Kami.Lib.EclecticLib.
Require Import Lia.
Require Import Omega.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.NArith.NArith.
Require Import Arith_base.
Require Import Arith Coq.ZArith.Znat Psatz.

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

Definition weq sz (x y: word sz): {x = y} + {x <> y} :=
  match weqb _ x y as sth return weqb _ x y = sth -> {x = y} + {x <> y} with
  | true => fun s => left (weqb_true _ _ _ s)
  | false => fun s => right (weqb_false _ _ _ s)
  end eq_refl.

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
  | 0 => fun _ => (ZToWord _ 0)
  | S m => fun e =>
             if (weq _ (@truncMsb 1 (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) (ZToWord 1 0))
             then (wadd _ (ZToWord _ 1) (@countLeadingZerosWord m no (@truncLsb m (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))))
             else (ZToWord _ 0)
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
         | H: ?w1 = ?w2 |- _ => match type of w1 with
                                | word ?sz => let H1 := fresh in
                                              let H2 := fresh in
                                              unique pose proof (f_equal (@wordVal sz) H) as H1
                                end; 
                                cbn [Z.modulo Z.pow_pos] in *
         end.


Lemma word0_neq: forall w : word 1, w <> (ZToWord 1 0) -> w = (ZToWord 1 1).
Proof.
  intros.
  arithmetizeWord.
  unfold Z.modulo in *; simpl in *.
  unfold Z.pow_pos in *; simpl in *.
  lia.
Qed.


Lemma wor_wzero : forall sz w, wor _ (ZToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wzero_wor: forall sz w, wor _  w (ZToWord sz 0) = w.
Proof.
  intros.
  arithmetizeWord.
  rewrite Z.lor_0_r.
  assumption.
Qed.

Lemma unique_word_0 : forall a : word 0,
    a = ZToWord 0 0.
Proof.
  intros.
  arithmetizeWord.
  simpl in *.
  unfold Z.modulo in *; simpl in *.
  lia.
Qed.

Lemma wzero_wplus: forall sz w, wadd _ (ZToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wplus_wzero : forall sz w, wadd _ w (ZToWord sz 0) = w.
Proof.
  intros.
  arithmetizeWord.
  rewrite Zmod_0_l.
  rewrite Z.add_0_r.
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

Lemma Z_lt_div2: forall (a b c : Z), (c > 0)%Z -> (a < b)%Z -> (b mod c = 0)%Z -> (a/c < b/c)%Z.
Proof.
  intros.
  pose proof (Z.div_le_mono a b c ltac:(lia) ltac:(lia)) as sth.
  apply Z_le_lt_eq_dec in sth.
  destruct sth; auto.
  pose proof (Z.mod_eq b c ltac:(lia)) as sth2.
  assert (sth3: (b = c * (b / c))%Z) by lia.
  rewrite sth3 in H0.
  assert (sth4: (c * (a/c) = c * (b/c))%Z) by nia.
  rewrite <- sth4 in *.
  pose proof (Z_mult_div_ge a c H).
  lia.
Qed.

Lemma Z_pow_2_gt_0: forall n, (n >= 0)%Z -> (2 ^ n > 0)%Z.
Proof.
  intros.
  apply Z.lt_gt, Z.pow_pos_nonneg;[lia|].
  lia.
Qed.

Lemma Z_of_nat_pow_2_gt_0: forall n, (2 ^ (Z.of_nat n) > 0)%Z.
Proof.
  intros.
  apply Z.lt_gt, Z.pow_pos_nonneg;[lia|].
  apply Nat2Z.is_nonneg.
Qed.

(*Lemma Z_of_nat_add_sub: forall a b, Z.of_nat a = (Z.of_nat b + Z.of_nat (a - b))%Z.
Proof.
  intros.
  rewrite <- Nat2Z.inj_add.
  apply inj_eq.
  apply le_plus_minus.
  specialize (Z_of_nat_pow_2_gt_0 (a - b)).
  intro.
  apply Z.gt_lt in H.
  apply Z.pow_0_l in H.
    lia.
  

Lemma Z_pow_mul : forall a b, (2 ^ a)%Z = ((2 ^ b) * (2 ^ (a-b)))%Z.
Proof.
  intros.
  rewrite <- Z.pow_add_r.
  reflexivity.*)


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

Theorem wplus_unit : forall sz (x : word sz), wadd _ (ZToWord sz 0) x = x.
Proof.
  intros.
  arithmetizeWord.
  lia.
Qed.

Lemma boundProofZIff : forall (sz : nat) (w : Z), (w mod 2 ^ Z.of_nat sz)%Z = w <-> (0 <= w < 2 ^ Z.of_nat sz)%Z.
Proof.
  split; intros.
  - apply boundProofZ; auto.
  - apply Z.mod_small; auto.
Qed.

Lemma Zpow_1_0 : forall b, (Z.pow 2 b = 1)%Z -> b = 0%Z.
Proof.
  repeat intro.
  destruct (Z_lt_le_dec 0 b).
  - specialize (Z.pow_gt_1 2 b) as TMP; destruct TMP; try lia.
  - rewrite Z.le_lteq in l; destruct l; try lia.
    exfalso.
    rewrite (Z.pow_neg_r 2 _ H0) in H; lia.
Qed.


Lemma wones_wzero : forall sz, (sz > 0) -> wones sz <> ZToWord sz 0.
Proof.
  repeat intro.
  eapply (f_equal (wordVal _)) in H0.
  arithmetizeWord.
  simpl in *.
  assert (2 ^ Z.of_nat sz > 1)%Z.
  { pose proof (Z.pow_gt_1 2 (Z.of_nat sz)).
    lia.
  }
  rewrite 2 Z.mod_small in H0; lia.
Qed.


Lemma wordToZ_ZToWord: forall (sz : nat) (w : Z),
    (0 <= w < Z.pow 2 (Z.of_nat sz))%Z -> wordVal _ (ZToWord sz w) = w.
Proof.
  intros.
  arithmetizeWord.
  simpl in *.
  apply Z.mod_small.
  auto.
Qed.

Lemma pow2_of_nat (n : nat) : (2 ^ Z.of_nat n)%Z = Z.of_nat (2 ^ n)%nat.
Proof.
  induction n.
  + simpl. auto.
  + rewrite Nat2Z.inj_succ.
    simpl.
    rewrite Z.pow_succ_r; try lia.
Qed.

Lemma wordToNat_natToWord : forall (sz : nat) (w : nat),
    (w < 2 ^ sz)%nat -> wordToNat _ (natToWord sz w) = w.
Proof.
  intros.
  unfold wordToNat. unfold natToWord.
  arithmetizeWord.
  simpl.
  rewrite Z.mod_small.
  rewrite Nat2Z.id. auto.
  split; try lia.
  rewrite pow2_of_nat.
  apply Nat2Z.inj_lt. auto.
Qed.
  
Lemma Zpow_of_nat : forall n, Z.of_nat (2 ^ n) = (2 ^ Z.of_nat n)%Z.
Proof.
  induction n; auto.
  rewrite Nat2Z.inj_succ, <- Z.add_1_l.
  rewrite Z.pow_add_r; try lia.
  rewrite <-IHn.
  rewrite Nat.pow_succ_r', Nat2Z.inj_mul; auto.
Qed.


Lemma Zpow_1_le (a b : Z) :
  (1 <= a)%Z ->
  (0 <= b)%Z ->
  (1 <= a ^b)%Z.
Proof.
  intros.
  apply Zle_lt_or_eq in H.
  destruct H.
  - specialize (Z.pow_gt_lin_r _ _ H H0) as P0.
    lia.
  - rewrite <- H.
    rewrite Z.pow_1_l.
    lia.
    auto.
Qed.

Lemma Zpow_mul_le (a b : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (2 ^ a <= 2 ^ b * 2 ^ a)%Z.
Proof.
  intros.
  rewrite <-(Z.mul_1_l (2^a)) at 1. 
  assert (1 <= 2)%Z. { lia. }
                     specialize (Zpow_1_le _ _ H1 H0).
  intros.
  apply Zmult_lt_0_le_compat_r.
  apply Z.pow_pos_nonneg.
  lia. auto. auto.
Qed.

Lemma Zpow_add_sub (a b : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (2 ^ (a + b) = (2 ^ a * 2 ^ b - 2 ^ b) + 2 ^ b)%Z.
Proof.
  intros.
  rewrite Z.pow_add_r; lia.
Qed.

Lemma Zmul_sub (a b c : Z) :
  (0 <= b)%Z ->
  (0 <= c)%Z ->
  (0 <= a < 2 ^ b)%Z ->
  (a * 2 ^ c <= (2 ^ b * (2 ^ c) -  1 * (2 ^ c)))%Z.
Proof.
  intros.
  rewrite <-Z.mul_sub_distr_r. apply Z.mul_le_mono_nonneg_r.
  apply Z.pow_nonneg; lia.
  lia.
Qed.

Lemma Zpow_lt_add (a b c : Z) :
  (0 <= c)%Z ->
  (0 <= b)%Z ->
  (0 <=  a < 2 ^ c)%Z ->
  (0 <= a < 2 ^ (b + c))%Z.
Proof.
  intros.
  split.
  destruct H1.
  auto.
  rewrite Z.pow_add_r; auto.
  assert (1 <= 2)%Z. {
    lia. }
  specialize (Zpow_1_le _ _ H2 H0) as P0.
  destruct H1.
  specialize (Zpow_mul_le c b H H0) as P1.
  lia.
Qed.

Lemma Zmul_add_0_lt (a a' b c : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (0 <= c)%Z ->
  (0 <= a')%Z ->
  (0 <= a < 2 ^ b)%Z ->
  (0 <= a' < 2 ^ c)%Z ->
  (0 <= a' < 2 ^ (b + c))%Z ->
  (0 <= (a * 2 ^ c + a') < 2 ^ (b + c))%Z.
Proof.
  intros.
  split.
  apply Z.add_nonneg_nonneg; auto.
  specialize (Z.pow_nonneg 2 (c)) as P0.
  assert (0 <= 2)%Z; [lia|].
  specialize (P0 H6).
  apply Z.mul_nonneg_nonneg; auto.
  specialize(Zpow_lt_add _ _ _ H1 H0 H4); intros.
  specialize(Zmul_sub _ _ _ H0 H1 H3); intros.
  rewrite Z.mul_1_l in H7.
  specialize (Zmul_sub _ _ _ H0 H1 H3); intros.
  specialize (Zpow_add_sub _ _ H0 H1); intros.
  rewrite H9.
  lia.
Qed.


Lemma truncLsb_concat : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
    @truncLsb sz2 (sz1 + sz2) (wconcat w1 w2) = w2.
Proof.
  repeat intro.
  arithmetizeWord.
  specialize (Zpow_lt_add wordVal (Z.of_nat sz1) (Z.of_nat sz2) (Zle_0_nat sz2) (Zle_0_nat sz1) H); intros.
  assert (0 <= wordVal0)%Z. {
    lia.
  }
  assert (0 <= wordVal)%Z. {
    lia.
  }
  specialize (Zmul_add_0_lt
                wordVal0 wordVal (Z.of_nat sz1) (Z.of_nat sz2) H2 (Zle_0_nat sz1) (Zle_0_nat sz2) H3 H0 H H1); intros.
  specialize (Zmod_small _ _ H4); intros.
  rewrite Nat2Z.inj_add.
  rewrite H5.
  rewrite <- Zplus_mod_idemp_l.
  rewrite Z_mod_mult.
  simpl; auto.
Qed.

Lemma truncMsb_concat : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
    @truncMsb sz1 (sz1 + sz2) (wconcat w1 w2) = w1.
Proof.
  repeat intro.
  arithmetizeWord.
  specialize (Zpow_lt_add wordVal0 (Z.of_nat sz2) (Z.of_nat sz1) (Zle_0_nat sz1) (Zle_0_nat sz2) H0); intros.
  assert (0 <= wordVal0)%Z. {
    lia.
  }
  assert (0 <= wordVal)%Z. {
    lia.
  }
  specialize (Zpow_lt_add wordVal (Z.of_nat sz1) (Z.of_nat sz2) (Zle_0_nat sz2) (Zle_0_nat sz1) H); intros.
  specialize (Zmul_add_0_lt
                wordVal0 wordVal (Z.of_nat sz1) (Z.of_nat sz2) H2 (Zle_0_nat sz1) (Zle_0_nat sz2) H3 H0 H H4); intros.
  specialize (Zmod_small _ _ H5); intros.
  rewrite Nat2Z.inj_add.
  rewrite H6.
  rewrite Z.add_comm.
  rewrite minus_plus.
  rewrite Z_div_plus.
  rewrite <- wordBound. 
  rewrite Zmod_div.
  simpl; auto.
  lia.
Qed.

Lemma word1_neq (w: word 1):
  w <> (ZToWord 1 0) ->
  w <> (ZToWord 1 1) ->
  False.
Proof.
  intros.
  apply word0_neq in H.
  contradiction.
Qed.

Lemma Nat_mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros.
  pose proof (Nat.mod_mul_r a _ _ H H0).
  rewrite H1.
  rewrite Nat.add_mod_idemp_l by auto.
  rewrite Nat.add_mod by auto.
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by (apply Nat.mul_comm).
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma Nat_mod_factor' a b c d:
  b <> 0 -> c <> 0 -> d = b * c -> (a mod d) mod b = a mod b.
Proof.
  pose proof (@Nat_mod_factor a b c).
  intros.
  subst.
  eapply H; eauto.
Qed.

Lemma mod_sub a b c:
  c > 0 ->
  a >= b * c ->
  (a - b * c) mod c = a mod c.
Proof.
  intros.
  assert (sth: a - b * c + b * c = a) by lia.
  rewrite <- sth at 2.
  rewrite Nat.mod_add by lia.
  auto.
Qed.

Lemma truncLsb_fits_ZToWord n sz:
  (0 <= n < Z.pow 2 (Z.of_nat sz))%Z -> 
  (@truncLsb sz (sz+1) (ZToWord (sz + 1) n) = ZToWord sz n).
Proof.
  intro.
  unfold truncLsb.
  simpl.
  rewrite Zmod_small; auto.
  destruct H.
  split; auto.
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  rewrite Z.pow_1_r; lia.
  lia.
  lia.
Qed.

Theorem concat_split : forall sz1 sz2 (w : word (sz1 + sz2)),
    @wconcat _ _ _ (@truncMsb sz1 (sz1 + sz2) w) (@truncLsb sz2 (sz1 + sz2) w) = w.
Proof.
  intros. 
  arithmetizeWord.
  erewrite minus_plus, Z.add_comm, Z.mul_comm, <- Z.rem_mul_r.
  - erewrite <- Z.pow_add_r, <- Nat2Z.inj_add,  Nat.add_comm; try apply Nat2Z.is_nonneg.
    repeat rewrite wordBound; auto.
  - intro.
    specialize (Z_of_nat_pow_2_gt_0 sz2) as P0; lia.
  - specialize (Z_of_nat_pow_2_gt_0 sz1) as P0; lia.
Qed.

Fixpoint mod2 (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n') => mod2 n'
  end.

Ltac rethink :=
  match goal with
  | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Theorem div2_double : forall n, Nat.div2 (2 * n) = n.
Proof.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.

Theorem div2_S_double : forall n, Nat.div2 (S (2 * n)) = n.
  induction n; simpl; intuition; f_equal; rethink.
Qed.

Fixpoint Npow2 (n : nat) : N :=
  match n with
  | O => 1
  | S n' => 2 * Npow2 n'
  end%N.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
  auto.
Qed.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; omega.
  Qed.

  Theorem strong : forall n, P n.
    intros; eapply strong'; eauto.
  Qed.
End strong.

Theorem div2_odd : forall n,
    mod2 n = true
    -> n = S (2 * Nat.div2 n).
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  discriminate.
  destruct n as [|n]; simpl in *; intuition.
  do 2 f_equal.
  replace (Nat.div2 n + S (Nat.div2 n + 0)) with (S (Nat.div2 n + (Nat.div2 n + 0))); auto.
Qed.

Theorem div2_even : forall n,
    mod2 n = false
    -> n = 2 * Nat.div2 n.
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  destruct n as [|n]; simpl in *; intuition.
  discriminate.
  f_equal.
  replace (Nat.div2 n + S (Nat.div2 n + 0)) with (S (Nat.div2 n + (Nat.div2 n + 0))); auto.
Qed.

Theorem drop_mod2 : forall n k,
    2 * k <= n
    -> mod2 (n - 2 * k) = mod2 n.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; omega.
Qed.

Theorem div2_minus_2 : forall n k,
    2 * k <= n
    -> Nat.div2 (n - 2 * k) = Nat.div2 n - k.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
        destruct k; simpl in *; intuition.

        destruct k; simpl in *; intuition.
        rewrite <- plus_n_Sm.
        apply H; omega.
        Qed.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= Nat.div2 n.
  intros ? n H; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  omega.

  rewrite (div2_even _ Heq) in H.
  omega.
  Qed.

Lemma two_times_div2_bound: forall n, 2 * Nat.div2 n <= n.
Proof.
  eapply strong. intros n IH.
  destruct n.
  - constructor.
  - destruct n.
    + simpl. constructor. constructor.
    + simpl (Nat.div2 (S (S n))).
      specialize (IH n). omega.
Qed.

Lemma div2_compat_lt_l: forall a b, b < 2 * a -> Nat.div2 b < a.
Proof.
  induction a; intros.
  - omega.
  - destruct b.
    + simpl. omega.
    + destruct b.
      * simpl. omega.
      * simpl. apply lt_n_S. apply IHa. omega.
Qed.

(* otherwise b is made implicit, while a isn't, which is weird *)
Arguments div2_compat_lt_l {_} {_} _.

Lemma pow2_add_mul: forall a b,
    Nat.pow 2 (a + b) = (Nat.pow 2 a) * (Nat.pow 2 b).
Proof.
  induction a; destruct b; firstorder; simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_1_r; auto.
  repeat rewrite Nat.add_0_r.
  rewrite IHa.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_add_distr_r; auto.
Qed.

Lemma mult_pow2_bound: forall a b x y,
    x < Nat.pow 2 a -> y < Nat.pow 2 b -> x * y < Nat.pow 2 (a + b).
Proof.
  intros.
  rewrite pow2_add_mul.
  apply Nat.mul_lt_mono_nonneg; omega.
Qed.

Lemma mult_pow2_bound_ex: forall a c x y,
    x < Nat.pow 2 a -> y < Nat.pow 2 (c - a) -> c >= a -> x * y < Nat.pow 2 c.
Proof.
  intros.
  replace c with (a + (c - a)) by omega.
  apply mult_pow2_bound; auto.
Qed.

Lemma lt_mul_mono' : forall c a b,
    a < b -> a < b * (S c).
Proof.
  induction c; intros.
  rewrite Nat.mul_1_r; auto.
  rewrite Nat.mul_succ_r.
  apply lt_plus_trans.
  apply IHc; auto.
Qed.

Lemma lt_mul_mono : forall a b c,
    c <> 0 -> a < b -> a < b * c.
Proof.
  intros.
  replace c with (S (c - 1)) by omega.
  apply lt_mul_mono'; auto.
Qed.

Lemma zero_lt_pow2 : forall sz, 0 < Nat.pow 2 sz.
Proof.
  induction sz; simpl; omega.
Qed.

Lemma one_lt_pow2:
  forall n,
    1 < Nat.pow 2 (S n).
Proof.
  intros.
  induction n.
  simpl; omega.
  remember (S n); simpl.
  omega.
Qed.

Lemma one_le_pow2 : forall sz, 1 <= Nat.pow 2 sz.
Proof.
  intros. pose proof (zero_lt_pow2 sz). omega.
Qed.

Lemma pow2_ne_zero: forall n, Nat.pow 2 n <> 0.
Proof.
  intros.
  pose proof (zero_lt_pow2 n).
  omega.
Qed.

Lemma mul2_add : forall n, n * 2 = n + n.
Proof.
  induction n; firstorder.
Qed.

Lemma pow2_le_S : forall sz, (Nat.pow 2 sz) + 1 <= Nat.pow 2 (sz + 1).
Proof.
  induction sz; simpl; auto.
  repeat rewrite Nat.add_0_r.
  rewrite pow2_add_mul.
  repeat rewrite mul2_add.
  pose proof (zero_lt_pow2 sz).
  omega.
Qed.

Lemma pow2_bound_mono: forall a b x,
    x < Nat.pow 2 a -> a <= b -> x < Nat.pow 2 b.
Proof.
  intros.
  replace b with (a + (b - a)) by omega.
  rewrite pow2_add_mul.
  apply lt_mul_mono; auto.
  pose proof (zero_lt_pow2 (b - a)).
  omega.
Qed.

Lemma pow2_inc : forall n m,
    0 < n -> n < m ->
    Nat.pow 2 n < Nat.pow 2 m.
Proof.
  intros.
  generalize dependent n; intros.
  induction m; simpl.
  intros. inversion H0.
  unfold lt in H0.
  rewrite Nat.add_0_r.
  inversion H0.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
  apply Nat.lt_trans with (Nat.pow 2 m).
  apply IHm.
  exact H2.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
Qed.

Lemma pow2_S: forall x, Nat.pow 2 (S x) = 2 * Nat.pow 2 x.
Proof. intros. reflexivity. Qed.

Lemma mod2_S_S : forall n,
    mod2 (S (S n)) = mod2 n.
Proof.
  intros.
  destruct n; auto; destruct n; auto.
Qed.

Lemma mod2_S_not : forall n,
    mod2 (S n) = if (mod2 n) then false else true.
Proof.
  intros.
  induction n; auto.
  rewrite mod2_S_S.
  destruct (mod2 n); replace (mod2 (S n)); auto.
Qed.

Lemma mod2_S_eq : forall n k,
    mod2 n = mod2 k ->
    mod2 (S n) = mod2 (S k).
Proof.
  intros.
  do 2 rewrite mod2_S_not.
  rewrite H.
  auto.
Qed.

Theorem drop_mod2_add : forall n k,
    mod2 (n + 2 * k) = mod2 n.
Proof.
  intros.
  induction n.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply mod2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  apply mod2_S_eq; auto.
Qed.

Lemma mod2sub: forall a b,
    b <= a ->
    mod2 (a - b) = xorb (mod2 a) (mod2 b).
Proof.
  intros. remember (a - b) as c. revert dependent b. revert a. revert c.
  change (forall c,
             (fun c => forall a b, b <= a -> c = a - b -> mod2 c = xorb (mod2 a) (mod2 b)) c).
  apply strong.
  intros c IH a b AB N.
  destruct c.
  - assert (a=b) by omega. subst. rewrite Bool.xorb_nilpotent. reflexivity.
  - destruct c.
    + assert (a = S b) by omega. subst a. simpl (mod2 1). rewrite mod2_S_not.
      destruct (mod2 b); reflexivity.
    + destruct a; [omega|].
      destruct a; [omega|].
      simpl.
      apply IH; omega.
Qed.

Theorem mod2_pow2_twice: forall n,
    mod2 (Nat.pow 2 n + (Nat.pow 2 n + 0)) = false.
Proof.
  intros.
  replace (Nat.pow 2 n + (Nat.pow 2 n + 0)) with (2 * Nat.pow 2 n) by omega.
  apply mod2_double.
Qed.

Theorem div2_plus_2 : forall n k,
    Nat.div2 (n + 2 * k) = Nat.div2 n + k.
Proof.
  induction n; intros.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply div2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  destruct (Even.even_or_odd n).
  - rewrite <- even_div2.
    rewrite <- even_div2 by auto.
    apply IHn.
    apply Even.even_even_plus; auto.
    apply Even.even_mult_l; repeat constructor.

  - rewrite <- odd_div2.
    rewrite <- odd_div2 by auto.
    rewrite IHn.
    omega.
    apply Even.odd_plus_l; auto.
    apply Even.even_mult_l; repeat constructor.
Qed.

Lemma pred_add:
  forall n, n <> 0 -> pred n + 1 = n.
Proof.
  intros; rewrite pred_of_minus; omega.
Qed.

Lemma pow2_zero: forall sz, (Nat.pow 2 sz > 0)%nat.
Proof.
  induction sz; simpl; auto; omega.
Qed.

Section omega_compat.

  Ltac omega ::= lia.

  Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = Nat.pow 2 n.
    induction n as [|n IHn]; simpl; intuition.
    rewrite <- IHn; clear IHn.
    case_eq (Npow2 n); intuition.
  Qed.

End omega_compat.

Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
     N_of_nat_of_N nat_of_N_of_nat
     nat_of_P_o_P_of_succ_nat_eq_succ nat_of_P_succ_morphism : N.


Theorem nat_of_N_eq : forall n m,
    nat_of_N n = nat_of_N m
    -> n = m.
  intros ? ? H; apply (f_equal N_of_nat) in H;
    autorewrite with N in *; assumption.
Qed.


Theorem pow2_N : forall n, Npow2 n = N.of_nat (Nat.pow 2 n).
Proof.
  intro n. apply nat_of_N_eq. rewrite Nat2N.id. apply Npow2_nat.
Qed.

Lemma Z_of_N_Npow2: forall n, Z.of_N (Npow2 n) = (2 ^ Z.of_nat n)%Z.
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  rewrite Zpow_of_nat.
  reflexivity.
Qed.

Lemma pow2_S_z:
  forall n, Z.of_nat (Nat.pow 2 (S n)) = (2 * Z.of_nat (Nat.pow 2 n))%Z.
Proof.
  intros.
  replace (2 * Z.of_nat (Nat.pow 2 n))%Z with
      (Z.of_nat (Nat.pow 2 n) + Z.of_nat (Nat.pow 2 n))%Z by omega.
  simpl.
  repeat rewrite Nat2Z.inj_add.
  ring.
Qed.

Lemma pow2_le:
  forall n m, (n <= m)%nat -> (Nat.pow 2 n <= Nat.pow 2 m)%nat.
Proof.
  intros.
  assert (exists s, n + s = m) by (exists (m - n); omega).
  destruct H0; subst.
  rewrite pow2_add_mul.
  pose proof (pow2_zero x).
  replace (Nat.pow 2 n) with (Nat.pow 2 n * 1) at 1 by omega.
  apply mult_le_compat_l.
  omega.
Qed.

Lemma Zabs_of_nat:
  forall n, Z.abs (Z.of_nat n) = Z.of_nat n.
Proof.
  unfold Z.of_nat; intros.
  destruct n; auto.
Qed.

Lemma Npow2_not_zero:
  forall n, Npow2 n <> 0%N.
Proof.
  induction n; simpl; intros; [discriminate|].
  destruct (Npow2 n); auto.
  discriminate.
Qed.

Lemma Npow2_S:
  forall n, Npow2 (S n) = (Npow2 n + Npow2 n)%N.
Proof.
  simpl; intros.
  destruct (Npow2 n); auto.
  rewrite <-Pos.add_diag.
  reflexivity.
Qed.

Lemma Npow2_pos: forall a,
    (0 < Npow2 a)%N.
Proof.
  intros.
  destruct (Npow2 a) eqn: E.
  - exfalso. apply (Npow2_not_zero a). assumption.
  - constructor.
Qed.

Lemma minus_minus: forall a b c,
    c <= b <= a ->
    a - (b - c) = a - b + c.
Proof. intros. omega. Qed.

Lemma even_odd_destruct: forall n,
    (exists a, n = 2 * a) \/ (exists a, n = 2 * a + 1).
Proof.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn as [[a E] | [a E]].
    + right. exists a. omega.
    + left. exists (S a). omega.
Qed.

Lemma mul_div_undo: forall i c,
    c <> 0 ->
    c * i / c = i.
Proof.
  intros.
  pose proof (Nat.div_mul_cancel_l i 1 c) as P.
  rewrite Nat.div_1_r in P.
  rewrite Nat.mul_1_r in P.
  apply P; auto.
Qed.

Lemma mod_add_r: forall a b,
    b <> 0 ->
    (a + b) mod b = a mod b.
Proof.
  intros. rewrite <- Nat.add_mod_idemp_r by omega.
  rewrite Nat.mod_same by omega.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma mod2_cases: forall (n: nat), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros.
  assert (n mod 2 < 2). {
    apply Nat.mod_upper_bound. congruence.
  }
  omega.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Nat.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by omega.
  rewrite Nat.div_1_r in A.
  rewrite mult_comm.
  rewrite <- Nat.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Nat.mod_divide; assumption.
Qed.

Lemma Smod2_1: forall k, S k mod 2 = 1 -> k mod 2 = 0.
Proof.
  intros k C.
  change (S k) with (1 + k) in C.
  rewrite Nat.add_mod in C by congruence.
  pose proof (Nat.mod_upper_bound k 2).
  assert (k mod 2 = 0 \/ k mod 2 = 1) as E by omega.
  destruct E as [E | E]; [assumption|].
  rewrite E in C. simpl in C. discriminate.
Qed.

Lemma mod_0_r: forall (m: nat),
    m mod 0 = 0.
Proof.
  intros. reflexivity.
Qed.

Lemma sub_mod_0: forall (a b m: nat),
    a mod m = 0 ->
    b mod m = 0 ->
    (a - b) mod m = 0.
Proof.
  intros. assert (m = 0 \/ m <> 0) as C by omega. destruct C as [C | C].
  - subst. apply mod_0_r.
  - assert (a - b = 0 \/ b < a) as D by omega. destruct D as [D | D].
    + rewrite D. apply Nat.mod_0_l. assumption.
    + apply Nat2Z.inj. simpl.
      rewrite Zdiv.mod_Zmod by assumption.
      rewrite Nat2Z.inj_sub by omega.
      rewrite Zdiv.Zminus_mod.
      rewrite <-! Zdiv.mod_Zmod by assumption.
      rewrite H. rewrite H0.
      apply Z.mod_0_l.
      omega.
Qed.

Lemma mul_div_exact: forall (a b: nat),
    b <> 0 ->
    a mod b = 0 ->
    b * (a / b) = a.
Proof.
  intros. edestruct Nat.div_exact as [_ P]; [eassumption|].
  specialize (P H0). symmetry. exact P.
Qed.

Import Word.Notations.

Open Scope word_scope.

Lemma Z_add_sub_distr : forall a b c,
    ((a - (b + c)) = a - b - c)%Z.
Proof.
  intros.
  lia.
Qed.

Hint Rewrite Zplus_mod_idemp_r Z_mod_plus_full Zplus_mod_idemp_l: distributeMod.
Hint Rewrite Zminus_mod_idemp_r Zminus_mod_idemp_l: distributeMod.
Hint Rewrite Z_mod_mult Zmult_mod_idemp_r Zmult_mod_idemp_l Zmult_mod_distr_l Zmult_mod_distr_r: distributeMod.
Hint Rewrite <- Zplus_mod Zminus_mod Zmult_mod: distributeMod.

Lemma wminus_plus_distr:
  forall {sz} (x y z: word sz), x ^- (y ^+ z) = x ^- y ^- z.
Proof.
  intros.
  arithmetizeWord;
    autorewrite with distributeMod.
  f_equal.
  lia.
Qed.

Lemma wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ _ y.
Proof.
  intros.
  arithmetizeWord.
  autorewrite with distributeMod.
  rewrite <- Zplus_mod_idemp_r.
  rewrite <- (Zminus_mod_idemp_l (2 ^ Z.of_nat sz) wordVal _).
  rewrite Z_mod_same_full.
  simpl in *.
  autorewrite with distributeMod.
  f_equal.
Qed.

Lemma wneg_wnot:
  forall sz (w : word sz), wnot _ w = wneg _ w ^- (ZToWord _ 1).
Proof.
  intros.
  arithmetizeWord.
  autorewrite with distributeMod.
  f_equal.
Qed.

Lemma wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  f_equal.
  lia.
Qed.

Lemma wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  f_equal.
  lia.
Qed.

Lemma wminus_diag : (forall sz (x : word sz), x ^- x = ZToWord sz 0).
Proof.
  intros.
  arithmetizeWord; f_equal; lia.
Qed.

Lemma move_wplus_wminus : (forall sz (x y z : word sz), x ^+ y = z -> x = z ^- y).
Proof.
  intros.
  arithmetizeWord. 
  simpl in *; subst.
  autorewrite with distributeMod.
  assert (wordVal1 + wordVal0 - wordVal0 = wordVal1)%Z by lia.
  rewrite H3.
  lia.
Qed.


Lemma word_cancel_l sz (a b c: word sz):
  a = b -> c ^+ a = c ^+ b.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  inversion H; subst.
  f_equal.
Qed.

Lemma word_cancel_r sz (a b c: word sz):
  a = b -> a ^+ c = b ^+ c.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  simpl in *.
  inversion H; subst.
  f_equal.
Qed.



Lemma word_cancel_m sz (a b c a' b': word sz):
  a ^+ a' = b ^+ b'-> a ^+ c ^+ a' = b ^+ c ^+ b'.
Proof.
  intros.
  assert (sth: a ^+ c ^+ a' = a ^+ a'^+ c ).
  rewrite <- wplus_assoc.
  rewrite wplus_comm with (y := a').
  rewrite wplus_assoc.
  reflexivity.
  rewrite sth.
  rewrite H.
  rewrite <- wplus_assoc.
  rewrite wplus_comm with (x := b').
  rewrite wplus_assoc.
  reflexivity.
Qed.


Lemma wconcat_1_0 :
  (@wconcat 1 0 1 (ZToWord 1 1) (ZToWord 0 0)) = (ZToWord 1 1).
Proof.
  arithmetizeWord.
  lia.
Qed.

Lemma wconcat_w_0 : forall sz (w : word sz),
    (@wconcat sz 0 sz w (ZToWord 0 0)) = w.
Proof.
  intros.
  arithmetizeWord.
  rewrite Zmod_0_l.
  rewrite <- Zred_factor0.
  rewrite Z.add_0_r.
  auto.
Qed.

Lemma wconcat_0_sz1_w : forall sz (w : word sz),
    (@wconcat 1 sz (sz+1) (ZToWord 1 0) w) = (ZToWord (sz+1) (wordVal _ w)).
Proof.
  intros.
  arithmetizeWord.
  f_equal.
Qed.

Lemma eq_word {sz} {x y : word sz} : x = y -> wordVal _ x = wordVal _ y.
Proof.
  intros.
  destruct x as [x px].
  destruct y as [y py].
  simpl in *; subst; auto.
  inversion H; auto.
Qed.

Lemma getWordVal : forall n x,
    (0 <= x < (2 ^ (Z.of_nat n)))%Z ->
    wordVal n (ZToWord n x) = x.
Proof.
  intros.
  arithmetizeWord. simpl.
  apply Zmod_small; auto.
Qed.

Lemma Zpow_successor : forall x (y : nat),
    (0 <= x < 2 ^ (Z.of_nat y))%Z ->
    (0 <= x < 2 ^ Z.of_nat(y + 1))%Z.
Proof.
  intros.
  inversion H.
  split.
  * auto.
  * rewrite Nat2Z.inj_add.
    rewrite Z.add_comm.
    apply Zpow_lt_add.
    lia.
    lia.
    lia.
Qed.

Lemma Zpow_successor_itself : forall  (y : nat),
    (0 <= 2 ^ (Z.of_nat y) < 2 ^ Z.of_nat(y + 1))%Z.
Proof.
  intros.
  split.
  * rewrite (Z.pow_nonneg 2 (Z.of_nat y)).
    lia.
    lia.
  * apply Z.pow_lt_mono_r.
    lia.
    lia.
    lia.
Qed.
  

Lemma concat_shiftl_plus_n n x:
  (0 <= x < 2 ^ (Z.of_nat n))%Z ->
  (@wconcat 1 n (n+1) (ZToWord 1 1) (ZToWord n x)) = (ZToWord (n + 1) (2 ^ (Z.of_nat n))) ^+ ZToWord (n + 1) x.
Proof.
  intros.
  apply eq_wordVal.
  apply eq_word.
  unfold wconcat.
  unfold wadd.
  f_equal.
  assert (wordVal 1 (ZToWord 1 1) = 1)%Z. {
    simpl. apply Z.mod_1_l.
    rewrite Z.pow_pos_fold. rewrite Z.pow_1_r. lia. }
  rewrite H0.
  repeat (rewrite getWordVal).
  lia.
  apply Zpow_successor; auto.
  apply Zpow_successor_itself.
  auto.
Qed.

Lemma concat_wplus sz (w1 w2: word sz):
  forall sz' (w': word sz'),
    (0 <= (wordVal _ w1) + (wordVal _ w2) < 2 ^ Z.of_nat sz)%Z ->
    wconcat w' (w1 ^+ w2) = @wconcat sz' sz (sz'+sz) w' w1 ^+ wconcat (ZToWord sz' 0) w2.
Proof.
  intros.
  arithmetizeWord.
  rewrite (Zmod_small (wordVal1 + wordVal0) _).
  rewrite <- Zplus_assoc_reverse.
  rewrite (Zplus_mod (wordVal * 2 ^ Z.of_nat sz + wordVal1) wordVal0 _).
  lia.
  auto.
Qed.

Lemma wminus_inv : forall sz (x : word sz), x ^+ ^~ _ x = ZToWord sz 0.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  rewrite Zplus_mod.
  rewrite Zminus_mod.
  rewrite Z_mod_same_full, Z.sub_0_l, Zplus_mod_idemp_r, Z.add_opp_r, Zminus_mod_idemp_r.
  rewrite (Zmod_small _ _ H); rewrite Z.sub_diag; reflexivity.
Qed.

Lemma wminus_cancel : forall sz (x y : word sz),
   (wordVal _ x + wordVal _ y < 2 ^ Z.of_nat sz)%Z -> x ^+ y ^- y = x.
Proof.
  intros.
  arithmetizeWord.
  simpl in *.
  rewrite Z.mod_small; try lia.
  rewrite Z.mod_small; try lia.
  split. rewrite Z.mod_small. lia.
  split; lia.
  rewrite Z.mod_small; lia.
Qed.
  
Lemma wadd_wzero_1:
  forall sz (w: word sz), w ^+ (ZToWord _ 0) = w.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  rewrite Z.add_0_r.
  auto.
Qed.

Lemma move_wadd_wminus sz (a b c: word sz):
  a ^+ b = c <-> a = c ^- b.
Proof.
  split; intro.
  + rewrite <- H.
    rewrite wminus_def.
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite wadd_wzero_1.
    reflexivity.
  + rewrite H.
    rewrite wminus_def.
    rewrite <- wplus_assoc.
    rewrite wplus_comm with (x:= ^~ _ b).
    rewrite wminus_inv.
    rewrite wadd_wzero_1.
    reflexivity.
Qed.

Lemma wneg_idempotent:
  forall {sz} (w: word sz), ^~ _ (^~ _ w) = w.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  rewrite <- Zminus_mod_idemp_l.
  rewrite Z_mod_same_full.
  rewrite Z.sub_0_l.
  rewrite Z.opp_sub_distr.
  rewrite Z.add_opp_l.
  rewrite <- Zminus_mod_idemp_r.
  rewrite Z_mod_same_full.
  rewrite Z.sub_0_r.
  auto.
Qed.

Lemma ZToWord_plus : forall sz n m,
    ZToWord sz (n + m) = ZToWord _ n ^+ ZToWord _ m.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  f_equal.
Qed.

(* The ring of size-0 words is the trivial ring, with 0 = 1 *)
Lemma ws_zero_trivial (w : word 0) : w = ZToWord 0 1.
Proof.
  arithmetizeWord.
  cbn in *.
  rewrite Z.mod_1_r in wordBound.
  auto.
Qed.

Lemma pow2_gt_1 n : (n > 0)%nat -> (2 ^ n > 1)%nat.
Proof.
  induction n.
  + lia.
  + intros ?.
    apply one_lt_pow2.
Qed.

Lemma wone_wmul : forall sz w, wmul _ (ZToWord sz 1) w = w.
Proof.
  intros.
  case (zerop sz) as [H_wz | H_wpos].
  + subst. rewrite ws_zero_trivial. auto.
  + arithmetizeWord.
    repeat rewrite Z.mod_small; try lia;
    split; intuition;
    apply Z2Nat.inj_lt; try lia; simpl;
    rewrite <- Zpow_of_nat;
    rewrite Nat2Z.id;
    apply pow2_gt_1; auto.
Qed.

Lemma wmul_comm : forall sz (x y : word sz), x ^* y = y ^* x.
Proof.
  intros.
  arithmetizeWord; autorewrite with distributeMod.
  f_equal.
  lia.
Qed.
  
Lemma split_concat : forall sz1 sz2 (w : word (sz1 + sz2)),
    wconcat (wsplitl sz1 sz2 w) (wsplitr sz1 sz2 w) = w.
Proof.
  intros.
  unfold wconcat. unfold wsplitl. unfold wsplitr.
  specialize Z_of_nat_pow_2_gt_0 with sz2 as Hp.
  simpl.
  arithmetizeWord.
  rewrite Zmod_mod.
  specialize Z.mod_small with (wordVal / 2 ^ Z.of_nat sz2)%Z (2 ^ Z.of_nat sz1)%Z as Hs.
  rewrite Hs.
  specialize Z_div_mod_eq with wordVal (2 ^ Z.of_nat sz2)%Z as Hmod.
  rewrite Z.mul_comm in Hmod.
  rewrite <- Hmod.
  rewrite Z.mod_small; try lia.
  auto.
  split; try apply Z.div_pos; intuition.
  apply Z.div_lt_upper_bound; intuition.
  rewrite <- Z.pow_add_r; try lia.
  rewrite <- Nat2Z.inj_add. rewrite Nat.add_comm.
  lia.
Qed.

(* Moved from FpuProperties.v *)

Lemma nat_mul_cancel_l :
  forall a b c, c <> 0 ->
                c * a = c * b ->
                a = b.
Proof.
  induction a; intros.
  - rewrite <- mult_n_O in H0.
    apply eq_sym, mult_is_O in H0.
    destruct H0; subst; tauto.
  - induction b.
    + exfalso; rewrite <- mult_n_O in H0.
      destruct (mult_is_O _ _ H0); lia.
    + repeat rewrite Nat.mul_succ_r in H0.
      rewrite Nat.add_cancel_r in H0.
      rewrite (IHa _ _ H H0); reflexivity.
Qed.

Definition wmsb sz (w : word sz) (b : bool) :=
  if (sz =? 0)%nat then b else (0 <? wordToNat _ w / 2 ^ (sz - 1)).

Definition wleu sz (x y : word sz) :=
  (wordVal _ x <=? wordVal _ y)%Z.

Lemma Zdiv_div (n m : Z) :
  (0 < m)%Z ->
  (0 <= n)%Z ->
  Z.to_nat (n / m) = (Z.to_nat n /Z.to_nat m).
Proof.
  intros.
  rewrite <- (Z2Nat.id n) at 1; auto.
  rewrite <- (Z2Nat.id m) at 1; [|lia].
  rewrite <- div_Zdiv.
  - rewrite Nat2Z.id; reflexivity.
  - rewrite <- Z2Nat.inj_0; intro.
    rewrite Z2Nat.inj_iff in H1; subst; lia.
Qed.

Lemma Zmod_mod' (n m : Z) :
  (0 < m)%Z ->
  (0 <= n)%Z ->
  (Z.to_nat (n mod m) = (Z.to_nat n) mod (Z.to_nat m)).
Proof.
  intros.
  rewrite <- (Z2Nat.id n) at 1; auto.
  rewrite <- (Z2Nat.id m) at 1; [|lia].
  rewrite <- mod_Zmod.
  - rewrite Nat2Z.id; reflexivity.
  - rewrite <- Z2Nat.inj_0; intro.
    rewrite Z2Nat.inj_iff in H1; subst; lia.
Qed.

Lemma pow_divide :
  forall sz1 sz2,
    (2 ^ Z.of_nat sz1 | 2 ^ Z.of_nat (sz1 + sz2))%Z
    /\ (2 ^ Z.of_nat sz2 | 2 ^ Z.of_nat (sz1 + sz2))%Z.
Proof.
  split; erewrite Nat2Z.inj_add, Z.pow_add_r; try apply Nat2Z.is_nonneg; eexists; [rewrite Z.mul_comm|]; reflexivity.
Qed.

Lemma wordToNat_split2 : forall sz1 sz2 (w : word (sz1 + sz2)), wordToNat _ (@truncMsb sz2 _ w) = wordToNat _ w / (2 ^ sz1).
Proof.
  intros.
  unfold natToWord, truncMsb, wordToNat.
  arithmetizeWord.
  simpl.
  rewrite Nat.add_sub, Z.mod_small.
  - rewrite Zdiv_div; try lia.
    + rewrite pow2_of_nat, Nat2Z.id; reflexivity.
    + apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
  - split.
    + apply Z.div_pos; try lia.
      apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
    + rewrite (Zdiv_unique (2 ^ Z.of_nat (sz1 + sz2)) (2 ^ Z.of_nat (sz1)) (2 ^ Z.of_nat (sz2)) 0%Z).
      * apply Z_lt_div2; try lia.
        -- apply (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _))).
        -- apply Znumtheory.Zdivide_mod, pow_divide.
      * split; try lia.
        apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
      * rewrite Nat2Z.inj_add, Z.pow_add_r; lia.
Qed.

Lemma split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2), @truncMsb sz2 (sz1 + sz2) (wconcat z w) = z.
Proof.
  intros.
  arithmetizeWord.
  rewrite Nat.add_sub, (Zmod_small _ (2 ^ Z.of_nat (_ + _))).
  - rewrite <- (Zdiv_unique _ _ wordVal wordVal0); lia.
  - split.
    + apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia.
    + apply (Z.lt_le_trans _ ((2 ^ Z.of_nat sz1) * (wordVal + 1)) _ ); [| rewrite Nat2Z.inj_add, Z.pow_add_r]; try lia.
      apply Z.mul_le_mono_nonneg_l; lia.
Qed.

Lemma countLeadingZerosWord_le_len :
  forall no ni, ni < 2 ^ no ->
                forall w : word ni,
                  @wleu _ (countLeadingZerosWord _ no w) (natToWord no ni) = true.
Proof.
  unfold wleu; setoid_rewrite Z.leb_le.
  induction ni; intros; [simpl; lia|].
  cbv [countLeadingZerosWord].
  destruct (weq _ _).
  - fold (countLeadingZerosWord ni no
          (truncLsb (nat_cast (fun n : nat => word n) (eq_sym (Nat.add_1_r ni)) w))).
    unfold natToWord.
    rewrite <- (Nat.add_1_l ni) at 3; rewrite Nat2Z.inj_add, ZToWord_plus.
    simpl; repeat rewrite Zplus_mod_idemp_r; repeat rewrite Zplus_mod_idemp_l.
    repeat rewrite Z.mod_small.
    + apply Zplus_le_compat_l.
      apply (Z.le_trans _ (wordVal no (natToWord no ni)) _).
      * apply IHni; lia.
      * simpl; rewrite Z.mod_small; [lia|].
        split; [apply Nat2Z.is_nonneg|].
        rewrite <- Zpow_of_nat; apply inj_lt; lia.
    + split; try lia.
      specialize (inj_lt _ _ H) as P0.
      rewrite Zpow_of_nat, <- Nat.add_1_l, Nat2Z.inj_add in P0; lia.
    + assert (forall no w, (0 <= wordVal no w < 2 ^ Z.of_nat no)%Z) as P0.
      { clear; intros.
        arithmetizeWord; assumption.
      }
      split.
      * apply Z.add_nonneg_nonneg; [lia | apply P0].
      * apply (Z.le_lt_trans _ (Z.of_nat (S ni)) _).
        -- rewrite <- (Nat.add_1_l ni) at 2.
           rewrite Nat2Z.inj_add, <- Z.add_le_mono_l.
           assert (Z.of_nat ni = wordVal no (natToWord no ni)) as P1.
           { simpl; symmetry.
             apply Z.mod_small; split; try lia.
             rewrite <- Zpow_of_nat.
             apply inj_lt; lia.
           }
           rewrite P1; apply IHni; lia.
        -- rewrite <- Zpow_of_nat.
           apply inj_lt; assumption.
  - arithmetizeWord.
    cbv [natToWord ZToWord].
    repeat rewrite (Zmod_small);[ |split |split ]; try lia.
    + rewrite <- Zpow_of_nat.
      apply inj_lt; assumption.
    + apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
Qed.

Lemma wneg_wplus_distr : forall sz (w1 w2 : word sz), ^~ _ (w1 ^+ w2) = ^~ _ w1 ^+ ^~ _ w2.
Proof.
  intros.
  arithmetizeWord.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
  assert ((2 ^ Z.of_nat sz - wordVal0 + (2 ^ Z.of_nat sz - wordVal))
          = (2 * 2 ^ Z.of_nat sz - (wordVal0 + wordVal)))%Z as P0.
  { lia. }
  rewrite P0.
  destruct (Z_lt_le_dec (wordVal0 + wordVal) (2 ^ Z.of_nat sz)).
  - rewrite (Zmod_small (_ + _) _); try lia.
    rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_l.
    rewrite Zminus_mod, (Znumtheory.Zdivide_mod (2*_)); auto.
    exists 2%Z; reflexivity.
  - rewrite (Zmod_eq_full (_ + _) _),
    <- (Zdiv_unique (wordVal0 + wordVal) (2 ^ Z.of_nat sz) 1 
                    ((wordVal0 + wordVal) - 2 ^ Z.of_nat sz)); try lia.
    f_equal; lia.
Qed.

Lemma wordToNat_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    wordToNat _ (@truncLsb sz1 _ w) = (wordToNat _ w) mod (2 ^ sz1).
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord.
  simpl.
  rewrite Zmod_mod'; try lia.
  - rewrite <- Zpow_of_nat, Nat2Z.id; reflexivity.
  - apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
Qed.

Lemma wordToNat_wplus :
  forall sz (w1 w2 : word sz),
    wordToNat _ (w1 ^+ w2) = (wordToNat _ w1 + wordToNat _ w2) mod (2 ^ sz).
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord. simpl.
  rewrite Zmod_mod'; try lia.
  rewrite <- Zpow_of_nat, Nat2Z.id, Z2Nat.inj_add; lia.
Qed.

Lemma wordToNat_wnot :
  forall sz (a : word sz), wordToNat _ (wnot _ a) = 2 ^ sz - wordToNat _ a - 1.
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord. simpl.
  rewrite Zminus_mod_idemp_l.
  rewrite (Z.mod_small); try lia.
  repeat rewrite Z2Nat.inj_sub; try lia.
  repeat f_equal; try lia.
  rewrite <- Zpow_of_nat, Nat2Z.id; reflexivity.
Qed.

Lemma diag :
  forall n, n - n = 0.
Proof. intros. lia. Qed.

Lemma countLeadingZerosWord_lt_len no ni :
  ni < 2 ^ no ->
  forall w : word ni, w <> wzero ni -> (wltu _ (countLeadingZerosWord _ no w) (natToWord no ni) = true).
Proof.
  unfold wltu.
  setoid_rewrite <- Zlt_is_lt_bool.
  induction ni; intros.
  - exfalso; apply H0.
    apply unique_word_0.
  - cbv [countLeadingZerosWord].
    destruct (weq _ _).
    + fold (countLeadingZerosWord ni no
             (truncLsb (nat_cast (fun n : nat => word n) (eq_sym (Nat.add_1_r ni)) w))).
      unfold natToWord.
      rewrite <- (Nat.add_1_l ni) at 3; rewrite Nat2Z.inj_add, ZToWord_plus.
      simpl; repeat rewrite Zplus_mod_idemp_r; repeat rewrite Zplus_mod_idemp_l.
      repeat rewrite Z.mod_small.
      * apply Zplus_lt_compat_l.
        apply (Z.lt_le_trans _ (wordVal no (natToWord no ni)) _).
        -- apply IHni; try lia.
           rewrite Nat.add_1_r.
           intro.
           specialize (concat_split 1 ni w) as P0.
           unfold truncMsb in *.
           simpl in *.
           rewrite Nat.add_1_r, Nat.sub_succ, Nat.sub_0_r in e.
           rewrite Nat.sub_0_r in P0.
           simpl in e.
           rewrite nat_cast_same in e, H1; rewrite e, H1 in P0.
           apply H0; rewrite <- P0.
           arithmetizeWord.
           repeat rewrite Z.mod_small; try split; try lia; apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
        -- arithmetizeWord; simpl.
           simpl; rewrite Z.mod_small; [lia| split; try lia].
           rewrite <- Zpow_of_nat; apply inj_lt; lia.
      * split; try lia.
        specialize (inj_lt _ _ H) as P0.
        rewrite Zpow_of_nat, <- Nat.add_1_l, Nat2Z.inj_add in P0; lia.
      * assert (forall no w, (0 <= wordVal no w < 2 ^ Z.of_nat no)%Z) as P0.
        { clear; intros.
          arithmetizeWord; assumption.
        }
        split.
        -- apply Z.add_nonneg_nonneg; [lia | apply P0].
        -- apply (Z.lt_trans _ (Z.of_nat (S ni)) _).
           ++ rewrite <- (Nat.add_1_l ni) at 2.
              rewrite Nat2Z.inj_add, <- Z.add_lt_mono_l.
              assert (Z.of_nat ni = wordVal no (natToWord no ni)) as P1.
              { simpl; symmetry.
                apply Z.mod_small; split; try lia.
                rewrite <- Zpow_of_nat.
                apply inj_lt; lia.
              }
              rewrite P1; apply IHni; try lia.
              rewrite Nat.add_1_r.
              intro.
              specialize (concat_split 1 ni w) as P2.
              unfold truncMsb in *.
              simpl in *.
              rewrite Nat.add_1_r, Nat.sub_succ, Nat.sub_0_r in e.
              rewrite Nat.sub_0_r in P2.
              simpl in e.
              rewrite nat_cast_same in e, H1; rewrite e, H1 in P2.
              apply H0; rewrite <- P2.
              arithmetizeWord.
              repeat rewrite Z.mod_small; try split; try lia; apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
           ++ rewrite <- Zpow_of_nat.
              apply inj_lt; assumption.
    + arithmetizeWord.
      cbv [natToWord ZToWord].
      repeat rewrite (Zmod_small);[ |split |split ]; try lia.
      * rewrite <- Zpow_of_nat.
        apply inj_lt; assumption.
      * apply (Z.gt_lt _ _ (Z_pow_2_gt_0 _ (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
Qed.

Lemma combine_shiftl_plus_n  n x :
  x < 2 ^ n ->
  wconcat (natToWord 1 1) (natToWord n x) = natToWord (n + 1) (2 ^ n) ^+ natToWord (n + 1) x.
Proof.
  intros.
  arithmetizeWord.
  destruct (2 ^ Z.of_nat n)%Z eqn:G; try(specialize (Z_of_nat_pow_2_gt_0 n) as P0; lia).
  rewrite (Z.mod_small _ (Z.pos _)).
  - rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    f_equal.
    rewrite <- G, pow2_of_nat; reflexivity.
  - rewrite <- G; split.
    + apply Nat2Z.is_nonneg.
    + rewrite pow2_of_nat.
      apply inj_lt; assumption.
Qed.

Lemma combine_wplus sz (w1 w2 : word sz) :
  wordToNat _ w1 + wordToNat _ w2 < 2 ^ sz ->
  forall sz' (w' : word sz'),
    @wconcat _ _ (sz + sz') w' (w1 ^+ w2) = wconcat w' w1 ^+ wconcat (natToWord sz' 0) w2.
Proof.
  unfold wordToNat; intros.
  arithmetizeWord.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, (Z.mod_small (wordVal1 + _) _), Z.add_assoc; try split; try lia.
  rewrite <- Z2Nat.inj_add in H; try lia.
  rewrite Z2Nat.inj_lt, <- Zpow_of_nat, Nat2Z.id; lia.
Qed.

Lemma pow2_wneg sz : wneg _ (natToWord (S sz) (2 ^ sz)) = natToWord (S sz) (2 ^ sz).
Proof.
  arithmetizeWord.
  rewrite Zminus_mod_idemp_r.
  f_equal.
  rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat, <- Nat2Z.inj_succ, <- Nat.add_1_l, Nat2Z.inj_add, Z.pow_add_r; try lia.
  repeat rewrite <- Zpow_of_nat.
  rewrite Nat.pow_1_r; lia.
Qed.

Lemma wmsb_true_split2_wones sz (w : word (sz + 1)) b :
  wmsb _ w b = true -> wones 1 = @truncMsb 1 _ w.
Proof.
  unfold wmsb.
  assert (sth : sz + 1 <> 0) by lia.
  apply Nat.eqb_neq in sth.
  rewrite sth.
  unfold wordToNat.
  intros.
  apply Nat.ltb_lt in H.
  arithmetizeWord.
  destruct H0.
  rewrite Z2Nat.inj_lt, <- Zpow_of_nat, Nat2Z.id in H1; try lia.
  rewrite Nat.div_str_pos_iff in H;[|specialize (pow2_zero (sz + 1 - 1))]; try lia.
  rewrite Nat.add_comm, minus_plus in H.
  rewrite Nat.add_comm, minus_plus, Z.mod_small; try lia.
  rewrite Z.mod_small.
  - apply (Zdiv_unique _ _ _ (wordVal - 2 ^ Z.of_nat sz)); try split; rewrite pow2_of_nat, <- (Z2Nat.id wordVal); try lia.
    rewrite <- Nat2Z.inj_sub, <- Nat2Z.inj_lt; try lia.
    rewrite Nat.pow_add_r in H1.
    simpl in H1; lia.
  - assert (Z.pow_pos 2 1 <> 0)%Z as P0.
    { lia. }
    assert ((wordVal / 2 ^ Z.of_nat sz)/(Z.pow_pos 2 1) = 0)%Z as P1.
    { replace (Z.pow_pos 2 1) with 2%Z; auto.
      rewrite Zdiv_Zdiv; try lia.
      - replace 2%Z with (2 ^ 1)%Z at 2; try lia.
        rewrite <- Z.pow_add_r; try lia.
        rewrite <- (Z2Nat.id 1); try lia.
        rewrite <- (Z2Nat.id wordVal); try lia.
        rewrite <- (Z2Nat.id 0); try lia.
        rewrite <- Nat2Z.inj_add, pow2_of_nat, <- div_Zdiv.
        + rewrite Nat2Z.inj_iff.
          replace (Z.to_nat 1) with 1; auto.
          replace (Z.to_nat 0) with 0; auto.
          rewrite Nat.div_small_iff; auto.
          specialize (pow2_zero (sz + 1)) as TMP; lia.
        + specialize (pow2_zero (sz + (Z.to_nat 1))) as TMP; lia.
      - apply Z.pow_nonneg; lia.
    }
    destruct (Z.div_small_iff (wordVal / 2 ^ Z.of_nat sz) _ P0) as [P2 P3]; clear P3.
    destruct (P2 P1); auto.
    exfalso; lia.
Qed.

Lemma neq0_wneq0 sz (n : word sz) : wordToNat _ n <> 0 <-> n <> natToWord sz 0.
Proof.
  unfold wordToNat, natToWord.
  split; repeat intro.
  + simpl in *.
    rewrite H0 in H.
    simpl in H.
    auto.
  + apply H.
    arithmetizeWord.
    rewrite Z.mod_small; try lia.
    rewrite <- Z2Nat.inj_iff; try lia; rewrite H0; auto.
Qed.

Lemma Natlt_0 :
  forall n,
    n <= 0 <-> n = 0.
Proof.
  induction n; intros; try lia.
Qed.

Lemma wmsb_1_natToWord sz n default :
  2 ^ sz <= n < 2 * 2 ^ sz ->
  wmsb _ (natToWord (S sz) n) default = true.
Proof.
  intros.
  unfold wmsb.
  destruct (Nat.eqb _ _) eqn:G.
  - exfalso.
    rewrite Nat.eqb_eq in G; discriminate.
  - rewrite Nat.ltb_lt.
    rewrite Nat.div_str_pos_iff.
    + unfold wordToNat, natToWord; simpl.
      rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat, <- Nat2Z.inj_succ, <- (Nat.add_1_l sz), Nat2Z.inj_add, Z.pow_add_r; try lia.
      destruct H.
      rewrite <- minus_n_O, Z.mod_small.
      * rewrite Nat2Z.id; assumption.
      * split; [apply Nat2Z.is_nonneg|].
        repeat rewrite <- Zpow_of_nat.
        rewrite <- Nat2Z.inj_mul.
        apply inj_lt.
        assumption.
    + intro.
      specialize (pow2_zero (S sz - 1)); lia.
Qed.


Lemma equal_expWidth_sigWidth:
  forall s, 2^s + 4 > s + 2.
Proof.
  induction s; simpl; auto.
  rewrite Nat.add_0_r.
  pose proof (pow2_zero s).
  Omega.omega.
Qed.

Unset Implicit Arguments.

Lemma natToWord_wordToNat sz (w : word sz) : natToWord sz (wordToNat _ w) = w.
Proof.
  unfold natToWord, wordToNat.
  rewrite Z2Nat.id; arithmetizeWord; intuition.
Qed.

Set Implicit Arguments.

Lemma one_lt_pow2' : forall n, n > 0 -> 1 < 2 ^ n.
Proof.
  intros; specialize (pow2_gt_1 _ H); auto.
Qed.

Lemma wzero_wones : forall sz, sz >= 1 -> natToWord sz 0 <> wones sz.
Proof.
  intros.
  unfold natToWord.
  simpl.
  apply weqb_false.
  unfold weqb.
  apply Z.eqb_neq.
  simpl.
  rewrite Z.mod_0_l, Z.mod_small; try split; try lia.
  rewrite <- Zpow_of_nat.
  assert (sth : (1 < Z.of_nat (2 ^ sz))%Z). {
    replace 1%Z with (Z.of_nat 1); auto.
    apply Nat2Z.inj_lt.
    apply one_lt_pow2'.
    lia.
  }
  lia.
  assert (sth : (1 <= Z.of_nat (2 ^ sz))%Z). {
    replace 1%Z with (Z.of_nat 1); auto.
    apply Nat2Z.inj_le.
    apply one_le_pow2.
  }
  rewrite <- Zpow_of_nat.
  lia.
  apply Z.pow_nonzero; lia.
Qed.

Lemma combine_wones_WO :
  forall (sz : nat) (w : word sz),
    w <> wzero sz ->
    @truncMsb 1 (sz + 1) (wconcat (natToWord 1 0) (wones sz) ^+ wconcat (natToWord 1 0) w) = natToWord 1 1.
Proof.
  intros.
  arithmetizeWord.
  simpl.
  assert (Z.pow_pos 2 1 = 2)%Z by auto; rewrite !H1; simpl; clear H1.
  assert (1 mod 2 = 1)%Z by auto; rewrite H1.
  rewrite Nat.add_sub.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l, (Zmod_small (_ - 1) _); [|lia].
  rewrite (Zmod_small (_ + wordVal)).
  - assert (0 <= wordVal - 1 < 2 ^ Z.of_nat sz)%Z as P0.
    {
      split; [|lia].
      apply Zlt_0_le_0_pred.
      destruct H0; destruct (Zle_lt_or_eq _ _ H0); auto.
      exfalso; apply H.
      rewrite <- H3, Zmod_0_l; reflexivity.
    }
    erewrite <- (Z.div_unique_pos _ _ 1 _ P0); [assumption|lia].
  - rewrite Nat2Z.inj_add, Z.pow_add_r; simpl; lia.
Qed.

Lemma wones_pow2_minus_one : forall sz, wordToNat _ (wones sz) = 2 ^ sz - 1.
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord.
  simpl.
  rewrite Z.mod_small; try split; try lia.
  rewrite Z2Nat.inj_sub; try lia.
  rewrite <- Zpow_of_nat, Nat2Z.id; auto.
  assert (H : (1 <= 2 ^ Z.of_nat sz)%Z) by (apply Zpow_1_le; lia).
  lia.
Qed.

Lemma split1_combine_wplus :
  forall sz1 sz2 (w11 w21 : word sz1) (w12 w22 : word sz2),
    @truncLsb sz1 (sz1 + sz2) (wconcat w12 w11 ^+ wconcat w22 w21) = w11 ^+ w21.
Proof.
  intros.
  unfold truncLsb.
  arithmetizeWord.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l,
  Nat2Z.inj_add, Z.pow_add_r, <- Znumtheory.Zmod_div_mod; try lia.
  - assert ((wordVal0 * 2 ^ Z.of_nat sz1 + wordVal2 + (wordVal * 2 ^ Z.of_nat sz1 + wordVal1))
            = (wordVal2 + wordVal1 + ((wordVal0 + wordVal) * 2 ^ Z.of_nat sz1)))%Z as P0 by lia.
    rewrite P0, Z_mod_plus_full.
    reflexivity.
  - apply Z.mul_pos_pos; try lia.
  - rewrite Z.mul_comm; eexists; reflexivity.
Qed.

Lemma wordToNat_combine :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) outSz,
    outSz = sz1 + sz2 ->
    wordToNat _ (@wconcat _ _ outSz w2 w1) = wordToNat _ w1 + 2 ^ sz1 * wordToNat _ w2.
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord; simpl.
  rewrite H, Zmod_small.
  - rewrite Z2Nat.inj_add, Z2Nat.inj_mul, pow2_of_nat, Nat2Z.id ; try lia.
    apply Z.mul_nonneg_nonneg; lia.
  - split.
    + apply Z.add_nonneg_nonneg; [|lia].
      apply Z.mul_nonneg_nonneg; lia.
    + rewrite Nat2Z.inj_add, Z.pow_add_r; try lia.
      apply (Z.lt_le_trans _ ( 2 ^ Z.of_nat sz1 * (wordVal  + 1)) _);[lia|].
      rewrite <- Z.mul_le_mono_pos_l; lia.
Qed.

Lemma wordToNat_natToWord_idempotent' : forall sz n , n < 2 ^ sz -> wordToNat _ (natToWord sz n) = n.
Proof.
  intros.
  unfold wordToNat, natToWord.
  simpl.
  rewrite <- Zpow_of_nat.
  rewrite <- mod_Zmod.
  rewrite Nat2Z.id.
  rewrite Nat.mod_small; auto.
  apply Nat.pow_nonzero; auto.
Qed.

Lemma wones_natToWord : forall sz, wones sz = natToWord sz (2 ^ sz - 1).
Proof.
  intros.
  unfold natToWord, wones.
  arithmetizeWord.
  rewrite Nat2Z.inj_sub, Zpow_of_nat.
  auto.
  apply one_le_pow2.
Qed.

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord sz n ^+ natToWord sz m.
Proof.
  intros.
  unfold natToWord.
  arithmetizeWord.
  rewrite Nat2Z.inj_add, Zplus_mod.
  auto.
Qed.

Lemma natToWord_pow2_add : forall sz n, natToWord sz (n + 2 ^ sz) = natToWord sz n.
Proof.
  intros. unfold natToWord.
  arithmetizeWord.
  rewrite Nat2Z.inj_add.
  rewrite Zpow_of_nat.
  rewrite Zplus_mod, Z_mod_same_full, Z.add_0_r.
  rewrite Zmod_mod.
  auto.
Qed.

Lemma split2_zero : forall sz1 sz2, @truncMsb sz2 (sz1 + sz2) (natToWord (sz1 + sz2) 0) = natToWord sz2 0.
Proof.
  intros.
  unfold natToWord.
  simpl.
  arithmetizeWord. 
  rewrite !Z.mod_0_l; auto; apply Z.pow_nonzero; lia.
Qed.

Lemma wordToNat_bound : forall sz (w : word sz), wordToNat _ w < 2 ^ sz.
Proof.
  intros. unfold wordToNat.
  arithmetizeWord. 
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id, Zpow_of_nat; intuition.
Qed.

Lemma wminus_minus :
  forall sz (a b : word sz), (wltu _ b a = true) ->
                             wordToNat _ (a ^- b) = wordToNat _ a - wordToNat _ b.
Proof.
  intros. unfold wordToNat, wltu in *.
  arithmetizeWord.
  simpl in *.
  rewrite Z.mod_small.
  rewrite Z2Nat.inj_sub; intuition.
  apply Z.ltb_lt in H. lia.
Qed.

Lemma lt_minus' :
  forall a b c : nat, b <= a -> b < c -> a < c -> a - b < c.
Proof. intros. lia. Qed.

Lemma Nat2Z_ZToWord :
  forall sz (n : nat), ZToWord sz (Z.of_nat n) = natToWord _ n.
Proof. intros; auto. Qed.

Lemma mod_sub' : forall a b, b <> 0 -> a < b * 2 -> a >= b -> a mod b = a - b.
Proof.
  intros.
  rewrite <- (@mod_sub _ 1 _); try lia.
  rewrite Nat.mod_small; lia.
Qed.

Lemma wordVal_pos : forall sz (w : word sz), (0 <= wordVal _ w)%Z.
Proof. intros. arithmetizeWord. lia. Qed.

Lemma wordToNat_lt1 sz (a b : word sz) : wltu _ a b = true -> wordToNat _ a < wordToNat _ b.
Proof.
  unfold wltu, wordToNat.
  intros.
  arithmetizeWord. 
  simpl in *.
  apply Z.ltb_lt in H.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma wordToNat_natToWord_eqn sz n : wordToNat _ (natToWord sz n) = n mod (2 ^ sz).
Proof.
  unfold wordToNat, natToWord.
  simpl.
  rewrite <- Zpow_of_nat.
  rewrite <- mod_Zmod.
  rewrite Nat2Z.id. auto.
  apply Nat.pow_nonzero; auto.
Qed.

Lemma move_wplus_wminus' sz (a b c : word sz) : a ^+ b = c <-> a = c ^- b. 
Proof.
  apply move_wadd_wminus.
Qed.


Lemma wltu_wordToNat sz (w w' : word sz) :
  wltu _ w w' = (wordToNat _ w <? wordToNat _ w').
Proof.
  unfold wordToNat, wltu.
  case_eq (wordVal _ w <? wordVal _ w')%Z; intros; [apply Z.ltb_lt in H | apply Z.ltb_nlt in H]; symmetry.
  + apply Nat.ltb_lt.
    apply Z2Nat.inj_lt; try apply wordVal_pos; auto.
  + apply Nat.ltb_nlt.
    intros H'.
    apply Z2Nat.inj_lt in H'; try apply wordVal_pos; auto.
Qed.

Lemma wleu_wordToNat sz (w w' : word sz) :
  wleu _ w w' = (wordToNat _ w <=? wordToNat _ w').
Proof.
  unfold wordToNat, wleu.
  case_eq (wordVal _ w <=? wordVal _ w')%Z; intros; [apply Z.leb_le in H | apply Z.leb_nle in H]; symmetry.
  + apply Nat.leb_le.
    apply Z2Nat.inj_le; try apply wordVal_pos; auto.
  + apply Nat.leb_nle.
    intros H'.
    apply Z2Nat.inj_le in H'; try apply wordVal_pos; auto.
Qed.

Lemma pow2_wzero sz : natToWord sz (2 ^ sz) = wzero sz.
Proof.
  arithmetizeWord.
  rewrite <- Zpow_of_nat.
  rewrite Z_mod_same_full.
  rewrite Z.mod_0_l.
  auto.
  rewrite Zpow_of_nat.
  apply Z.pow_nonzero; lia.
Qed.

Lemma concat_split' sz1 sz2 (w : word (sz2 + sz1)) :
  @wconcat sz1 sz2 (sz2 + sz1) (@truncMsb sz1 (sz2 + sz1) w) (@truncLsb sz2 (sz2 + sz1) w) = w.
Proof.
  intros. 
  arithmetizeWord. 
  erewrite Nat.add_sub, Z.add_comm, Z.mul_comm, <- Z.rem_mul_r.
  - erewrite <- Z.pow_add_r, <- Nat2Z.inj_add,  Nat.add_comm; try apply Nat2Z.is_nonneg.
    rewrite Nat.add_comm.
    repeat rewrite wordBound; auto.
  - intro.
    specialize (Z_of_nat_pow_2_gt_0 sz2) as P0; lia.
  - specialize (Z_of_nat_pow_2_gt_0 sz1) as P0; lia.
Qed.

Lemma combine_natToWord_wzero n x : 
  x < 2 ^ n -> wconcat (natToWord 1 0) (natToWord n x) = natToWord (n + 1) x.
Proof.
  intros.
  unfold natToWord.
  simpl.
  arithmetizeWord.
  simpl.
  assert (H' : (Z.of_nat x < 2 ^ Z.of_nat n)%Z).
  { rewrite <- Zpow_of_nat. apply Nat2Z.inj_lt. auto. }
  assert (sth : (Z.of_nat x mod 2 ^ Z.of_nat n = Z.of_nat x)%Z).
  { apply Z.mod_small; lia. }
  rewrite sth.
  auto.
Qed.

Lemma split1_combine sz1 sz2 (w : word sz1) (z : word sz2) :
  @truncLsb sz1 (sz1 + sz2) (wconcat z w) = w.
Proof.
  rewrite plus_comm.
  rewrite truncLsb_concat.
  auto.
Qed.

Lemma split1_fits_natToWord n sz:
  n < 2 ^ sz -> 
  (@truncLsb sz _ (natToWord (sz + 1) n) = natToWord sz n).
Proof.
  intro.
  rewrite <- combine_natToWord_wzero; auto.
  rewrite split1_combine; auto.
Qed.


Unset Implicit Arguments.

Lemma getBool_weq sz (w1 w2: word sz):
  getBool (weq _ w1 w2) = true -> w1 = w2.
Proof.
  intros.
  destruct (weq _ w1 w2); [auto | discriminate].
Qed.

Lemma if_same A (x: A) (p: bool): (if p then x else x) = x.
Proof.
  destruct p; auto.
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
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by (apply Nat.mul_comm).
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma mod_factor' a b c d:
  b <> 0 -> c <> 0 -> d = b * c -> (a mod d) mod b = a mod b.
Proof. 
  pose proof (@mod_factor a b c).
  intros.
  subst.
  eapply H; eauto.
Qed.

Lemma if_bool_2 A (x y: A) (p1 p2: bool):
  p1 = p2 ->
  (if p1 then x else y) = (if p2 then x else y).
Proof.
  intros sth.
  rewrite sth.
  auto.
Qed.

Lemma mod_cancel_l:
  forall a b x n,
    n <> 0 ->
    a mod n = b mod n ->
    (x + a) mod n = (x + b) mod n.
Proof.
  intros.
  rewrite <- Nat.add_mod_idemp_r; auto.
  rewrite H0.
  rewrite Nat.add_mod_idemp_r; auto.
Qed.

Lemma pow2_1_iff_0 n:
  2 ^ n = 1 <-> n = 0.
Proof.
  induction n; split; intro; try lia.
  simpl. reflexivity.
  destruct IHn.
  pose proof (one_lt_pow2 n) as sth1.
  rewrite H in sth1.
  apply False_ind.
  inversion sth1.
  inversion H3.
Qed.

Lemma pow2_lt_S n:
  n > 0 ->
  2 ^ n + 1 < 2 ^ (n + 1).
Proof.
  pose proof (pow2_le_S n) as sth.
  apply Nat.lt_eq_cases in sth.
  destruct sth; auto.
  intro sth.
  apply False_ind.
  apply Nat.add_sub_eq_l in H.
  pose proof (pow2_1_iff_0 n) as sth1.
  replace (2 ^ n) with (2 ^ n * 1) in H by lia.
  rewrite pow2_add_mul in H.
  rewrite <- Nat.mul_sub_distr_l in H.
  simpl in H.
  destruct sth1 as [sth2 sth3].
  rewrite sth2 in sth; lia.
Qed.

Lemma pow2_lt_2 n:
  1 < n -> 2 < 2 ^ n.
Proof.
  intro sth.
  induction n.
  inversion sth.
  simpl.
  assert (sth1: n = 1 \/ n > 1) by lia.
  destruct sth1.
  rewrite H.
  simpl.
  auto.
  simpl.
  apply Nat.lt_lt_add_l.
  rewrite Nat.add_0_r.
  lia.
Qed.

Lemma pow2_lt_pow2_S n : 2 ^ n < 2 ^ (n + 1).
Proof.
  rewrite Nat.add_1_r.
  simpl.
  assert (0 < 2 ^ n) by apply zero_lt_pow2.
  lia.
Qed.
