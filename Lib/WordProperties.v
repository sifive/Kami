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
             if (weq (@truncMsb 1 (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e)) (ZToWord 1 0))
             then (wadd (ZToWord _ 1) (@countLeadingZerosWord m no (@truncLsb m (m+1) (nat_cast (fun n => word n) (eq_sym (Nat.add_1_r m)) e))))
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

Lemma wor_wzero : forall sz w, wor (ZToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wzero_wor: forall sz w, wor w (ZToWord sz 0) = w.
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

Lemma wzero_wplus: forall sz w, wadd (ZToWord sz 0) w = w.
Proof.
  intros.
  arithmetizeWord.
  assumption.
Qed.

Lemma wplus_wzero : forall sz w, wadd w (ZToWord sz 0) = w.
Proof.
  intros.
  arithmetizeWord.
  rewrite Zmod_0_l.
  rewrite Z.add_0_r.
  assumption.
Qed.

Lemma wor_idemp :  forall (n : nat) (x0 : word n), wor x0 x0 = x0.
Proof.
  intros.
  induction x0.
  unfold wor.
  arithmetizeWord.
  rewrite Z.lor_diag.
  auto.
Qed.

Lemma truncMsbLtTrue : forall (n x : nat) (w1 w2 : word n),
    (wordVal _ (@truncMsb x _ w1) < wordVal _ (@truncMsb x _ w2))%Z ->
    wltu w1 w2 = true.
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
  apply(Z_lt_div' _ _ P1 H).
Qed.


Lemma truncMsbLtFalse : forall (n x : nat) (w1 w2 : word n),
    (wordVal _ (@truncMsb x _ w1) < wordVal _ (@truncMsb x _ w2))%Z ->
    wltu w2 w1 = false.
Proof.
  intros.
  specialize (truncMsbLtTrue _ _ _ _ H).
  intros.
  unfold wltu in *.
  rewrite Z.ltb_lt in *.
  rewrite Z.ltb_nlt.
  lia.
Qed.

Theorem wplus_unit : forall sz (x : word sz), wadd (ZToWord sz 0) x = x.
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

Lemma wordToNat_natToWord : forall (sz : nat) (w : nat),
    (w < 2 ^ sz)%nat -> wordToNat (natToWord sz w) = w.
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

Lemma truncLsb_concat : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
    @truncLsb sz2 (sz1 + sz2) (wconcat w1 w2) = w2.
Proof.
  repeat intro.
  arithmetizeWord.
  specialize (@Zpow_lt_add wordVal (Z.of_nat sz1) (Z.of_nat sz2) (Zle_0_nat sz2) (Zle_0_nat sz1) H); intros.
  assert (0 <= wordVal0)%Z. {
    lia.
  }
  assert (0 <= wordVal)%Z. {
    lia.
  }
  specialize (@Zmul_add_0_lt
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
  specialize (@Zpow_lt_add wordVal0 (Z.of_nat sz2) (Z.of_nat sz1) (Zle_0_nat sz1) (Zle_0_nat sz2) H0); intros.
  assert (0 <= wordVal0)%Z. {
    lia.
  }
  assert (0 <= wordVal)%Z. {
    lia.
  }
  specialize (@Zpow_lt_add wordVal (Z.of_nat sz1) (Z.of_nat sz2) (Zle_0_nat sz2) (Zle_0_nat sz1) H); intros.
  specialize (@Zmul_add_0_lt
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


Import Word.Notations.

Open Scope word_scope.

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

Lemma wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
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
  forall sz (w : word sz), wnot w = wneg w ^- (ZToWord _ 1).
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

Lemma wminus_wplus_undo : forall sz (a b : word sz),
    a ^- b ^+ b = a.
Proof.
  intros.
  arithmetizeWord.
  rewrite Zplus_mod_idemp_l, Z.mod_small; lia.
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

Lemma wminus_inv : forall sz (x : word sz), x ^+ ^~ x = ZToWord sz 0.
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
    rewrite wplus_comm with (x:= ^~ b).
    rewrite wminus_inv.
    rewrite wadd_wzero_1.
    reflexivity.
Qed.

Lemma wneg_idempotent:
  forall {sz} (w: word sz), ^~ (^~ w) = w.
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

Lemma wone_wmul : forall sz w, wmul (ZToWord sz 1) w = w.
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

Lemma wordToNat_split2 : forall sz1 sz2 (w : word (sz1 + sz2)), wordToNat (@truncMsb sz2 _ w) = wordToNat w / (2 ^ sz1).
Proof.
  intros.
  unfold natToWord, truncMsb, wordToNat.
  arithmetizeWord.
  simpl.
  rewrite Nat.add_sub, Z.mod_small.
  - rewrite Zdiv_div; try lia.
    + rewrite pow2_of_nat, Nat2Z.id; reflexivity.
    + apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
  - split.
    + apply Z.div_pos; try lia.
      apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
    + rewrite (Zdiv_unique (2 ^ Z.of_nat (sz1 + sz2)) (2 ^ Z.of_nat (sz1)) (2 ^ Z.of_nat (sz2)) 0%Z).
      * apply Z_lt_div2; try lia.
        -- apply (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _))).
        -- apply Znumtheory.Zdivide_mod, pow_divide.
      * split; try lia.
        apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
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
    + apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
Qed.

Lemma wneg_wplus_distr : forall sz (w1 w2 : word sz), ^~ (w1 ^+ w2) = ^~ w1 ^+ ^~ w2.
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
    wordToNat (@truncLsb sz1 _ w) = (wordToNat w) mod (2 ^ sz1).
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord.
  simpl.
  rewrite Zmod_mod'; try lia.
  - rewrite <- Zpow_of_nat, Nat2Z.id; reflexivity.
  - apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
Qed.

Lemma wordToNat_wplus :
  forall sz (w1 w2 : word sz),
    wordToNat (w1 ^+ w2) = (wordToNat w1 + wordToNat w2) mod (2 ^ sz).
Proof.
  intros.
  unfold wordToNat.
  arithmetizeWord. simpl.
  rewrite Zmod_mod'; try lia.
  rewrite <- Zpow_of_nat, Nat2Z.id, Z2Nat.inj_add; lia.
Qed.

Lemma wordToNat_wnot :
  forall sz (a : word sz), wordToNat (wnot a) = 2 ^ sz - wordToNat a - 1.
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

Lemma countLeadingZerosWord_lt_len no ni :
  ni < 2 ^ no ->
  forall w : word ni, w <> wzero ni -> (wltu (countLeadingZerosWord _ no w) (natToWord no ni) = true).
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
           repeat rewrite Z.mod_small; simpl in *; try split; try lia; try apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
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
              repeat rewrite Z.mod_small; simpl in *; try split; try lia; apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
           ++ rewrite <- Zpow_of_nat.
              apply inj_lt; assumption.
    + arithmetizeWord.
      cbv [natToWord ZToWord].
      repeat rewrite (Zmod_small);[ |split |split ]; try lia.
      * rewrite <- Zpow_of_nat.
        apply inj_lt; assumption.
      * apply (Z.gt_lt _ _ (Z_pow_2_gt_0 (Z.le_ge _ _ (Nat2Z.is_nonneg _)))).
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
  wordToNat w1 + wordToNat w2 < 2 ^ sz ->
  forall sz' (w' : word sz'),
    @wconcat _ _ (sz + sz') w' (w1 ^+ w2) = wconcat w' w1 ^+ wconcat (natToWord sz' 0) w2.
Proof.
  unfold wordToNat; intros.
  arithmetizeWord.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, (Z.mod_small (wordVal1 + _) _), Z.add_assoc; try split; try lia.
  rewrite <- Z2Nat.inj_add in H; try lia.
  rewrite Z2Nat.inj_lt, <- Zpow_of_nat, Nat2Z.id; lia.
Qed.

Lemma pow2_wneg sz : wneg (natToWord (S sz) (2 ^ sz)) = natToWord (S sz) (2 ^ sz).
Proof.
  arithmetizeWord.
  rewrite Zminus_mod_idemp_r.
  f_equal.
  rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat, <- Nat2Z.inj_succ, <- Nat.add_1_l, Nat2Z.inj_add, Z.pow_add_r; try lia.
  repeat rewrite <- Zpow_of_nat.
  rewrite Nat.pow_1_r; lia.
Qed.

Lemma wmsb_true_split2_wones sz (w : word (sz + 1)) b :
  wmsb _ w b = true -> wones _ = @truncMsb 1 _ w.
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
  rewrite Nat.add_comm, minus_plus, Z.mod_small; try rewrite Z.pow_pos_fold; try lia.
  rewrite Z.mod_small.
  - apply (Zdiv_unique _ _ _ (wordVal - 2 ^ Z.of_nat sz)); try split; rewrite pow2_of_nat, <- (Z2Nat.id wordVal); try lia.
    rewrite <- Nat2Z.inj_sub, <- Nat2Z.inj_lt; try lia.
    rewrite Nat.pow_add_r in H1.
    simpl in H1; lia.
  - assert (Z.pow_pos 2 1 <> 0)%Z as P0.
    { try rewrite Z.pow_pos_fold.
      lia. }
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
    exfalso; try rewrite Z.pow_pos_fold in *; lia.
Qed.

Lemma neq0_wneq0 sz (n : word sz) : wordToNat n <> 0 <-> n <> natToWord sz 0.
Proof.
  unfold wordToNat, natToWord.
  split; repeat intro.
  + simpl in *.
    rewrite H0 in H.
    simpl in H.
    auto.
  + apply H.
    arithmetizeWord.
    rewrite Z.mod_small; try lia; try (rewrite <- Z2Nat.inj_iff; try lia; rewrite H0; auto).
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

Unset Implicit Arguments.

Lemma natToWord_wordToNat sz (w : word sz) : natToWord sz (wordToNat w) = w.
Proof.
  unfold natToWord, wordToNat.
  rewrite Z2Nat.id; arithmetizeWord; intuition.
Qed.

Set Implicit Arguments.

Lemma wzero_wones : forall sz, sz >= 1 -> natToWord sz 0 <> wones _.
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
  - rewrite Nat2Z.inj_add, Z.pow_add_r; simpl; try rewrite Z.pow_pos_fold; lia.
Qed.

Lemma wones_pow2_minus_one : forall sz, wordToNat (wones sz) = 2 ^ sz - 1.
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
    wordToNat (@wconcat _ _ outSz w2 w1) = wordToNat w1 + 2 ^ sz1 * wordToNat w2.
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

Lemma wordToNat_natToWord_idempotent' : forall sz n , n < 2 ^ sz -> wordToNat (natToWord sz n) = n.
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

Lemma wordToNat_bound : forall sz (w : word sz), wordToNat w < 2 ^ sz.
Proof.
  intros. unfold wordToNat.
  arithmetizeWord. 
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id, Zpow_of_nat; intuition.
Qed.

Lemma wminus_minus :
  forall sz (a b : word sz), (wltu b a = true) ->
                             wordToNat (a ^- b) = wordToNat a - wordToNat b.
Proof.
  intros. unfold wordToNat, wltu in *.
  arithmetizeWord.
  simpl in *.
  rewrite Z.mod_small.
  rewrite Z2Nat.inj_sub; intuition.
  apply Z.ltb_lt in H. lia.
Qed.

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

Lemma wordToNat_lt1 sz (a b : word sz) : wltu a b = true -> wordToNat a < wordToNat b.
Proof.
  unfold wltu, wordToNat.
  intros.
  arithmetizeWord. 
  simpl in *.
  apply Z.ltb_lt in H.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma wordToNat_natToWord_eqn sz n : wordToNat (natToWord sz n) = n mod (2 ^ sz).
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
  wltu w w' = (wordToNat w <? wordToNat w').
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
  wleu w w' = (wordToNat w <=? wordToNat w').
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
  getBool (weq w1 w2) = true -> w1 = w2.
Proof.
  intros.
  destruct (weq w1 w2); [auto | discriminate].
Qed.

Lemma wor_comm width (x y : word width) :
  wor x y = wor y x.
Proof.
  arithmetizeWord.
  rewrite Z.lor_comm; reflexivity.
Qed.

Lemma wor_assoc n (x y z : word n):
  wor x (wor y z) = wor (wor x y) z.
Proof.
  arithmetizeWord.
  - rewrite (Zmod_small _ _ (Zlor_bounds _ H0 H)),
    (Zmod_small _ _ (Zlor_bounds _ H1 H0)),
    Z.lor_assoc; reflexivity.
Qed.
