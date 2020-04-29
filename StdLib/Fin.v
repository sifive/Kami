Require Import Bool String Ascii List Streams.
Require Import Lt.
Require Import Nat.
Require Import PeanoNat.
Require Import ProofIrrelevance.
Import ListNotations.

Fixpoint Fin (n : nat) :=
  match n with
  | 0 => Empty_set
  | S m => (unit + Fin m)%type
  end.

Definition F1 {n : nat} : Fin (S n) := inl tt.

Definition FS {n : nat} (i : Fin n) : Fin (S n) := @inr unit (Fin n) i.

Definition case0 (F : Fin 0 -> Type) (x : Fin 0) : F x := Empty_set_rect F x.

Lemma FS_inj : forall n (i j: Fin n) (H: FS i = FS j), i = j.
Proof.
  intro n.
  induction n.
    + exact (case0 (fun i => forall j : Fin 0, FS i = FS j -> i = j)).
    + intros i j H. injection H. trivial.
Qed.

Fixpoint to_nat {n : nat} : forall (i : Fin n), {m : nat | m < n} :=
  match n return forall i : Fin n, {m : nat | m < n} with
  | 0 => case0 (fun _ => {m : nat | m < 0})
  | S m =>
    fun i : Fin (S m) =>
      match i with
      | inl _ => exist _ 0 (Nat.lt_0_succ m)
      | inr j =>
        exist (fun o => o < S m)
              (S (proj1_sig (@to_nat m j)))
              (Nat.le_lt_trans
                 (S (proj1_sig (@to_nat m j))) m (S m)
                 (proj2_sig (@to_nat m j))
                 (Nat.lt_succ_diag_r m))
      end
  end.

Goal proj1_sig (@to_nat 1 F1) = 0. Proof. reflexivity. Qed.

Goal proj1_sig (@to_nat 4 F1) = 0. Proof. reflexivity. Qed.

Goal proj1_sig (@to_nat 4 (FS (FS (FS F1)))) = 3. Proof. reflexivity. Qed.

Fixpoint of_nat (x n : nat) : (Fin n) + {exists m, x = n + m}.
  refine
  match n with
  | 0 => inright (ex_intro (fun m => x = 0 + m) x (Nat.add_0_l x))
  | S n =>
    match x with
    | 0 => inleft F1
    | S x =>
      match of_nat x n with
      | inleft i => inleft (FS i)
      | inright H => 
        inright
          (ex_ind
            (fun m (Hm : x = n + m) =>
              ex_intro
                (fun o => S x = S n + o) m _
            )
            H)
      end
    end
  end.
Proof.
  abstract (rewrite Hm; rewrite <- (plus_Sn_m n m); reflexivity).
Defined.

Fixpoint of_nat_lt {x n : nat} : x < n -> Fin n :=
  match n with
  | 0 => fun H : x < 0 => False_rect _ (Nat.nlt_0_r x H)
  | S n =>
    match x with
    | 0 => fun _ => F1
    | S x => fun H : S x < S n => FS (@of_nat_lt x n (Lt.lt_S_n x n H))
    end
  end.

Lemma to_nat_of_nat_inv : forall (x n : nat) (H : x < n), proj1_sig (@to_nat n (@of_nat_lt x n H)) = x.
Proof.
  induction x.
  + induction n.
    - intro Hcontr; contradict Hcontr; exact (Nat.nlt_0_r 0).
    - intro H; simpl; reflexivity.
  + induction n.
    - intro Hcontr; contradict Hcontr; exact (Nat.nlt_0_r (S x)).
    - intro H.
      simpl.
      exact (f_equal S (IHx n (lt_S_n _ _ H))).
Qed.

Lemma of_nat_ext {n} {m} (H H0 : n < m) : of_nat_lt H = of_nat_lt H0.
Proof.
  rewrite (proof_irrelevance (n < m) H H0).
  reflexivity.
Qed.

Lemma to_nat_S : forall n (i : Fin n), S (proj1_sig (@to_nat n i)) = proj1_sig (@to_nat (S n) (inr i)).
Proof.
  induction n as [|m HInd].
  + exact (case0 (fun i => S (proj1_sig (to_nat i)) = (proj1_sig (@to_nat  (S 0) (inr i))))).
  + intro i; simpl; reflexivity.
Qed.

Lemma of_nat_to_nat_inv {n} : forall i : Fin n, of_nat_lt (proj2_sig (to_nat i)) = i.
Proof.
  induction n.
  + exact (case0 (fun i => of_nat_lt (proj2_sig (to_nat i)) = i)).
  + intro i.
    destruct i as [j|j].
    - destruct j; reflexivity.
    - simpl.
      apply (f_equal (@inr unit (Fin n))).
      rewrite <- (IHn j) at 5.
      apply (@of_nat_ext (proj1_sig (to_nat j)) n).
Qed.

Lemma of_nat_to_nat_FS {n} :
  forall (i : Fin n),
    of_nat_lt (proj2_sig (to_nat (FS i))) =
    FS (of_nat_lt (proj2_sig (to_nat i))).
Proof.
  induction n.
  + exact
      (case0 (fun i =>
               of_nat_lt (proj2_sig (to_nat (FS i))) =
               FS (of_nat_lt (proj2_sig (to_nat i))))).
  + intro i.
    destruct i as [i|i].
    - reflexivity.
    - simpl.
      apply (f_equal (fun j => @inr unit (Fin (S n)) (@inr unit (Fin n) j))).
      apply (@of_nat_ext (proj1_sig (to_nat i)) n).
Qed.

Lemma to_nat_of_nat {n} {m} (H : n < m) : to_nat (of_nat_lt H) = exist _ n H.
Proof.
  induction m.
    + exact (False_ind _ (Nat.nlt_0_r _ H)).
    + destruct n as [|n].
      - simpl; rewrite (proof_irrelevance (0 < S m) (Nat.lt_0_succ m) H); reflexivity.
      - simpl.
        apply (eq_sig_hprop (fun o H H0 => proof_irrelevance (o < S m) H H0) _ _).
        simpl.
        exact (f_equal S (to_nat_of_nat_inv n m (lt_S_n n m H))).
Qed.

Lemma to_nat_inj {n} (i j : Fin n) : proj1_sig (to_nat i) = proj1_sig (to_nat j) -> i = j.
Proof.
  induction n.
  + exact (case0 (fun _ => proj1_sig (to_nat i) = proj1_sig (to_nat j) -> i = j) i).
  + destruct i, j.
    - destruct u, u0. exact (fun _ => eq_refl).
    - exact (fun Hcontr : 0 = S _ => False_ind _ (O_S _ Hcontr)).
    - exact (fun Hcontr : S _ = 0 => False_ind _ (O_S _ (eq_sym Hcontr))).
    - exact (fun H => f_equal (@inr unit (Fin n)) (IHn f f0 (Nat.succ_inj _ _ H) )).
Qed.

Lemma eq_dec {n} (i j : Fin n): {i = j} + {i <> j}.
Proof.
  induction n.
  + exact (case0 (fun _ => {i = j}+{i <> j}) i).
  + destruct i, j.
    - destruct u, u0; exact (left _ (eq_refl)).
    - right; discriminate.
    - right; discriminate.
    - destruct (IHn f f0) as [Heq|Hneq].
      * exact (left _ (f_equal (@inr unit (Fin n)) Heq)).
      * right; intro Heq; injection Heq; exact (Hneq).
Qed.

Definition eqb {n m} (i : Fin n) (j : Fin m) : bool :=
  match Nat.eq_dec n m with
  | left Heq =>
    if eq_dec i (eq_rect_r Fin j Heq)
    then true
    else false
  | _ => false
  end.

Lemma eqb_nat_eq : forall n m (i : Fin n) (j : Fin m), eqb i j = true -> n = m.
Proof.
  intros n m i j H. 
  unfold eqb in H.
  destruct (Nat.eq_dec n m) as [Heq|Hneq] in H.
  + assumption.
  + contradict H; discriminate.
Qed.

Lemma eqb_eq : forall n (i j : Fin n), eqb i j = true <-> i = j.
Proof.
  intros n i j.
  unfold eqb.
  destruct (Nat.eq_dec n n) as [Heq|Hneq].
  + unfold eq_rect_r.
    rewrite <- (Eq_rect_eq.eq_rect_eq nat n (fun y : nat => Fin y) j (eq_sym Heq)).
    destruct (eq_dec i j) as [H|H].
    - exact (conj (fun _ => H) (fun _ => eq_refl)).
    - split.
      * discriminate.
      * contradiction.
  + contradiction.
Qed.

Definition cast {n} (i: Fin n) {m} (H : n = m) : Fin m := eq_rect n Fin i m H.
