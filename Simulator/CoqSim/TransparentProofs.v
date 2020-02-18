Require Import Kami.AllNotations.

Lemma Bool_eqb_refl2 : forall b, Bool.eqb b b = true.
Proof.
  destruct b; simpl; auto.
Defined.

Lemma Ascii_eqb_refl2 : forall c, (c =? c)%char = true.
Proof.
  intros []; simpl.
  repeat rewrite (Bool_eqb_refl2); auto.
Defined.

Lemma Ascii_eqb_eq2 : forall n m : ascii, (n =? m)%char = true <-> n = m.
Proof.
  intros.
  split; intro.
  apply Ascii.eqb_eq in H.
  exact (match ascii_dec n m with
         | left p => p
         | right ne => match (ne H) with end
         end).
  rewrite H.
  apply Ascii_eqb_refl2.
Defined.

Lemma Nat_eqb_refl2 : forall n, (n =? n)%nat = true.
Proof.
  induction n; auto.
Defined.

Lemma Nat_eqb_eq2 : forall n m : nat, (n =? m)%nat = true <-> n = m.
Proof.
  split; intro.
  apply Nat.eqb_eq in H.
  exact (match Nat.eq_dec n m with
         | left p => p
         | right ne => match (ne H) with end
         end).
  rewrite H.
  apply Nat_eqb_refl2.
Defined.

Lemma String_eqb_eq2 : forall s1 s2 : string, String.eqb s1 s2 = true <-> s1 = s2.
Proof.
  induction s1; destruct s2; simpl; split; intro; try reflexivity; try discriminate.
  - destruct (a =? a0)%char eqn:G.
    + apply Ascii_eqb_eq2 in G.
      apply IHs1 in H.
      congruence.
    + discriminate.
  - inversion H.
    rewrite Ascii.eqb_refl.
    rewrite <- H2.
    apply IHs1; reflexivity.
Defined.

Lemma Kind_decb_eq2 : forall k1 k2, Kind_decb k1 k2 = true <-> k1 = k2.
Proof.
  induction k1; intros; destruct k2; split; intro; try (reflexivity || discriminate).
  - simpl in H; apply Nat_eqb_eq2 in H; congruence.
  - inversion H; simpl; apply Nat_eqb_refl2.
  - destruct (n =? n0)%nat eqn:G.
    + simpl in H0.
      rewrite (@silly_lemma_true bool (n =? n0)%nat _ _ G) in H0 by auto.
      pose proof G.
      apply Nat_eqb_eq2 in H1.
      destruct H1.
      f_equal; extensionality i.
      apply H.
      apply andb_true_iff in H0; destruct H0.
      pose (proj1 (Fin_forallb_correct _) H0).
      rewrite (hedberg Nat.eq_dec _ eq_refl) in e.
      simpl in e.
      apply e.
      apply String_eqb_eq2.
      apply andb_true_iff in H0; destruct H0.
      pose (proj1 (Fin_forallb_correct _) H1).
      rewrite (hedberg Nat.eq_dec _ eq_refl) in e.
      simpl in e.
      apply e.
    + simpl in H0.
      rewrite (@silly_lemma_false) in H0 by auto; discriminate.
  - rewrite H0; apply Kind_decb_refl.
  - simpl in H; apply andb_true_iff in H.
    destruct H as [H1 H2]. apply Nat_eqb_eq2 in H1.
    destruct (IHk1 k2).
    pose (H H2); congruence.
  - simpl.
    apply andb_true_iff; inversion H; split.
    + apply Nat_eqb_refl2.
    + rewrite <- H2, IHk1; reflexivity.
Defined.

Definition string_dec2 : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct (String.eqb s1 s2) eqn:G.
  - left; apply String_eqb_eq2; auto.
  - right; abstract (intro;
    rewrite <- String_eqb_eq2 in H;
    rewrite H in G; discriminate).
Defined.

Definition Kind_dec2 : forall k1 k2 : Kind, {k1 = k2} + {k1 <> k2}.
Proof.
  intros.
  destruct (Kind_decb k1 k2) eqn: G.
  - left; apply Kind_decb_eq2 in G; congruence.
  - right.
    abstract (intro; subst;
    rewrite Kind_decb_refl in G; discriminate).
Defined.

Definition Signature_dec2 (s1 s2 : Signature) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct s1,s2.
  destruct (Kind_dec2 k k1).
  destruct (Kind_dec2 k0 k2).
  left; congruence.
  right; congruence.
  right; congruence.
Defined.

Definition string_sigb : forall x y : (string * Signature), {x = y} + {x <> y}.
Proof.
  intros [] [].
  destruct (string_dec2 s s1);
  destruct (Signature_dec2 s0 s2).
  - left; congruence.
  - right; congruence.
  - right; congruence.
  - right; congruence.
Defined.