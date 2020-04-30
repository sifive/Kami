Require Import Bool String Ascii List.
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

Local Fixpoint cast_aux {n} {m} : n = m -> Fin n -> Fin m :=
  match n, m with
  | 0, m     => fun _ => case0 (fun _ => Fin m)
  | S n, 0   => fun (H : S n = 0) _ => False_rect (Fin 0) (Nat.neq_succ_0 n H)
  | S n, S m =>
    fun (H : S n = S m) i =>
      match i with
      | inl _ => @F1 m
      | inr j => FS (cast_aux (Nat.succ_inj n m H) j)
      end
  end.

Definition cast {n} (i: Fin n) {m} (H : n = m) : Fin m := cast_aux H i.

Lemma cast_eq {n} : forall (i : Fin n) (H : n = n), i = cast i H.
Proof.
  induction n.
  + exact (case0 (fun i => forall H : 0 = 0, i = cast i H)).
  + induction i as [i|j].
    - intro H; simpl; destruct i; reflexivity.
    - intro H. 
      exact (f_equal (@inr unit (Fin n)) (IHn j (Nat.succ_inj n n H))).
Qed.

Fixpoint Fin_foldr {A : Type} (n : nat) (init : A) : forall (f : Fin n -> A -> A), A :=
  match n with
  | 0 => fun _ => init
  | S n => fun f => f F1 (Fin_foldr n init (fun i => f (FS i)))
  end.

Fixpoint nth_Fin {A : Type} (xs : list A) : Fin (length xs) -> A :=
  match xs with
  | [] => case0 (fun _ => A)
  | x :: xs =>
    fun i =>
      match i with
      | inl _ => x
      | inr j => nth_Fin xs j
      end
  end.

Definition nth_Fin' {A : Type} (xs : list A) {n : nat} (H : n = length xs) (i : Fin n) : A :=
  nth_Fin xs (cast i H).

Fixpoint nth_Fin'' {A : Type} (xs : list A) : forall n : nat, n <= length xs -> Fin n -> A :=
  match xs as ys return forall n, n <= length ys -> Fin n -> A with
  | [] =>
    fun n (H : n <= 0) (i : Fin n) =>
      let Heq : n = 0 := eq_sym (Le.le_n_0_eq n H) in
      case0 (fun _ => A) (cast i Heq)
  | y :: ys =>
    fun n =>
      match n as m return m <= length (y :: ys) -> Fin m -> A with
      | 0 => fun _ => case0 (fun _ => A)
      | S m =>
        fun (H : S m <= S (length ys)) (i : Fin (S m)) =>
          match i with
          | inl _ => y
          | inr j => nth_Fin'' ys m (le_S_n _ _ H) j
          end
      end
  end.

Lemma nth_Fin'_nth {A : Type} : forall (n : nat) (default : A) (i : Fin n) (xs : list A) (H : n = length xs), 
  nth_Fin' xs H i = nth (proj1_sig (to_nat i)) xs default.
Proof.
  induction n.
  + exact (fun default => case0 (fun i => forall xs (H : 0 = length xs), nth_Fin' xs H i = nth (proj1_sig (to_nat i)) xs default)).
  + intro default.
    destruct i as [i|j].
    - destruct i.
      destruct xs as [|x xs].
      * exact (fun Hcontr => False_ind _ (Nat.neq_succ_0 _ Hcontr)).
      * intro H.
        unfold nth_Fin'.
        simpl.
        reflexivity.
    - destruct xs as [|x xs].
      * intro H.
        contradict H.
        exact (Nat.neq_succ_0 n).
      * intro H.
        unfold nth_Fin'.
        simpl.
        unfold nth_Fin' in IHn.
        exact (IHn default j xs (Nat.succ_inj n (length xs) H)).
Qed.

Lemma nth_Fin_nth {A : Type} (default : A) : forall (xs : list A) (i : Fin (length xs)),
  nth_Fin xs i = nth (proj1_sig (to_nat i)) xs default.
Proof.
  induction xs.
  + exact (case0 (fun i => nth_Fin [] i = nth (proj1_sig (to_nat i)) [] default)).
  + destruct i as [i|j].
    - reflexivity.
    - exact (IHxs j).
Qed.

Definition fin_case (n : nat)
  (i : Fin (S n)) : forall
  (F : Fin (S n) -> Type)
  (f1 : F F1)
  (fs : forall j, F (FS j)), F i :=
  match i return
    forall F : Fin (S n) -> Type,
      F (@inl unit (Fin n) tt) ->
      (forall j : Fin n, F (@FS n j)) ->
      F i with
  | inl u => match u with tt => fun _ f1 _ => f1 end
  | inr j => fun _ _ fs => fs j
  end.

(* TODO: LLEE: replace the fin_dep_destruct tactic from EclecticLib. *)

Lemma Fin_cast_lemma : forall (n m : nat) (i : Fin n) (H H0 : n = m), cast i H = cast i H0.
Proof.
  intros n m i H H0.
  rewrite (proof_irrelevance (n = m) H H0).
  reflexivity.
Qed.

Lemma fin_to_nat_cast : forall (n : nat) (i: Fin n) (m : nat) (H: n = m),
  proj1_sig (to_nat (cast i H)) = proj1_sig (to_nat i).
Proof.
  induction n as [|n].
  + exact (case0 (fun i => forall m H, proj1_sig (to_nat (cast i H)) = proj1_sig (to_nat i))).
  + destruct i as [i|j].
    - destruct m as [|m].
      * intro H; contradict H; exact (Nat.neq_succ_0 n).
      * intro H; reflexivity.
    - destruct m as [|m].
      * intro H; contradict H; exact (Nat.neq_succ_0 n).
      * intro H.
        simpl.
        exact (f_equal S (IHn j m (Nat.succ_inj n m H))).
Qed.

Fixpoint map_length_red {A B : Type} (f : A -> B) (xs : list A) :=
  match xs return length (map f xs) = length xs with
  | [] => ltac:(reflexivity)
  | y :: ys =>
    f_equal_nat nat S
      (length (map f ys))
      (length ys)
      (map_length_red f ys)
  end.

Lemma nth_Fin_map2 (A B : Type) (f : A -> B) (F : B -> Type) :
  forall (xs : list A)
    (i : Fin (Datatypes.length (map f xs))),
  F (f (nth_Fin xs (cast i (map_length_red f xs)))) -> F (nth_Fin (map f xs) i).
Proof.
  induction xs as [|x xs IH].
  + exact (case0 (fun i => F (f (nth_Fin [] (cast i (map_length_red f [])))) -> F (nth_Fin (map f []) i))).
  + destruct i as [i|j].
    - exact (id).
    - simpl. 
      rewrite <- (Fin_cast_lemma (length (map f xs)) (length xs) j (map_length_red f xs)
        (Nat.succ_inj (length (map f xs))
          (length xs)
          (f_equal_nat nat S (Datatypes.length (map f xs))
            (Datatypes.length xs) (map_length_red f xs)))).
      exact (IH j).
Qed.

Fixpoint Fin_forallb {n} : (Fin n -> bool) -> bool :=
  match n with
  | 0   => fun _ => true
  | S n => fun f => f F1 && Fin_forallb (fun i => f (FS i))
  end.

Lemma Fin_forallb_correct {n} :
  forall f : Fin n -> bool,
    Fin_forallb f = true <-> forall i, f i = true.
Proof.
  induction n as [|n].
  + intro f; split; intro H.
    - exact (case0 (fun i => f i = true)).
    - unfold Fin_forallb; reflexivity.
  + intro f; split; intro H.
    destruct i as [u|j].
    - destruct u; simpl; unfold Fin_forallb in H; exact (proj1 (andb_prop (f F1) _ H)).
    - unfold Fin_forallb in H.
      fold (@Fin_forallb n (fun i : Fin n => f (FS i))) in H.
      exact (proj1 (IHn (fun i => f (FS i))) (proj2 (andb_prop _ _ H)) j).
    - simpl; apply (andb_true_intro); split.
      * exact (H F1).
      * exact (proj2 (IHn (fun i => f (FS i))) (fun i => H (FS i))).
Qed.

Fixpoint getFins (n : nat) : list (Fin n) := 
  match n with
  | 0 => []
  | S m => F1 :: map FS (getFins m)
  end.

Fixpoint getFinsBound n m : list (Fin m) :=
  match n with
  | 0 => []
  | S n =>
    match m with
    | 0 => []
    | S m => F1 :: map FS (getFinsBound n m)
    end
  end.

Definition mapOrFins {n : nat} (i : Fin n) := fold_left (fun acc x => i = x \/ acc) (getFins n) False.

Lemma getFins_length : forall n, length (getFins n) = n.
Proof.
  induction n as [|n IH].
  + reflexivity.
  + simpl; rewrite map_length; rewrite IH; reflexivity.
Qed.

Lemma getFins_all : forall n (i : Fin n), In i (getFins n).
Proof.
  induction n as [|n IH].
  + exact (case0 (fun i => In i (getFins 0))).
  + destruct i as [u|j].
    - destruct u; left; reflexivity.
    - simpl. right. exact (in_map FS (getFins n) j (IH j)).
Qed.

Lemma getFins_nth_error : forall {n} (i : Fin n),
  nth_error (getFins n) (proj1_sig (to_nat i)) = Some i.
Proof.
  induction n as [|n IH].
  + exact (case0 (fun i => nth_error (getFins 0) (proj1_sig (to_nat i)) = Some i)).
  + destruct i as [u|j].
    - destruct u; reflexivity.
    - simpl; exact (@map_nth_error _ _ FS (proj1_sig (to_nat j)) (getFins n) j (IH j)).
Qed.

Lemma getFins_nth {A : Type} : forall n (default : Fin n) (i : Fin n),
  nth (proj1_sig (to_nat i)) (getFins n) default = i.
Proof.
  intros.
  apply nth_error_nth.
  apply getFins_nth_error.
Qed.
