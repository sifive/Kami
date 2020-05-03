Require Import Kami.StdLib.Fin.
Require Import Arith_base.
Import EqNotations.
Local Open Scope nat_scope.

Fixpoint Vec X n : Type :=
  match n with
  | 0 => unit
  | S m => (X * Vec X m)%type
  end.

Definition nil : forall (A : Type), Vec A 0 := fun _  => tt.
Definition cons : forall (A : Type), A -> forall (n : nat), Vec A n -> Vec A (S n) :=
  fun (A : Type) (a : A) (n : nat) (v : Vec A n) => (a, v).


Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

  Definition rectS {A} (P : forall {n}, Vec A (S n) -> Type)
             (bas : forall (a : A), P (a :: []))
             (rect : forall a {n} (v : Vec A (S n)), P v -> P (a :: v)) :
    forall (n : nat) (v : Vec A (S n)), P v.
  Proof.
    induction n; intros.
    - repeat destruct v.
      apply (bas a).
    - destruct v; apply rect, IHn.
  Defined.
  
  Definition case0 {A} (P : Vec A 0 -> Type) (H : P []) (v : Vec A 0) :=
    match v as u return (P u) with
    | tt => H
    end.

  Definition caseS {A} (P : forall {n}, Vec A (S n) -> Type)
             (H : forall h {n} t, @P n (h :: t)) {n} (v : Vec A (S n)) : P v :=
    let (a, v0) as p return (P p) := v in H a v0.
  
  Definition caseS' {A} {n : nat} (v : Vec A (S n)) (P : Vec A (S n) -> Type)
             (H : forall h t, P (h :: t)) : P v :=
    let (a, v0) as p return (P p) := v in H a v0.

  Definition rect2 {A B} (P : forall {n}, Vec A n -> Vec B n -> Type)
             (bas : P [] []) (rect : forall {n v1 v2}, @P n v1 v2 ->
                                                       forall a b, P (a :: v1) (b :: v2)) :
    forall (n : nat) (v1 : Vec A n) (v2 : Vec B n), P v1 v2.
  Proof.
    induction n; intros; destruct v1, v2.
    - apply bas.
    - apply rect, IHn.
  Defined.

End SCHEMES.

Section BASES.
(** The first element of a non empty vector *)
Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

(** The last element of an non empty vector *)
Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

(** Build a vector of n{^ th} [a] *)
Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

(** The [p]{^ th} element of a vector of length [m]. *)
Fixpoint nth {n X} : Vec X n -> Fin n -> X :=
  match n with
  | 0 => fun _ => Fin.case0 _
  | S m => fun v i => fin_case i _ (fst v) (fun j => nth (snd v) j)
  end.

(** An equivalent definition of [nth]. *)
Definition nth_order {A} {n} (v: Vec A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

Definition replace {A n} (v : Vec A n) (p : Fin n) (a : A) : Vec A n.
Proof.
  induction n.
  - inversion p.
  - simpl in *.
    destruct p, v.
    + apply (a, v).
    + apply (a0, (IHn v f)).
Defined. 

(** Version of replace with [lt] *)
Definition replace_order {A n} (v: Vec A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

(** Remove the first element of a non empty vector *)
Definition tl {A} := @caseS _ (fun n v => Vec A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

(** Destruct a non empty vector *)
Definition uncons {A} {n : nat} (v : Vec A (S n)) : A * Vec A n := (hd v, tl v).

(** Remove last element of a non-empty vector *)
Definition shiftout {A} := @rectS _ (fun n _ => Vec A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

(** Add an element at the end of a vector *)
Fixpoint shiftin {A} {n : nat} (a : A) (v : Vec A n) : Vec A (S n) :=
  match n as n0 return (Vec A n0 -> Vec A (S n0)) with
  | O => (fun v' => (a, v'))
  | S m => (fun v' => (fst v', (shiftin a (snd v'))))
  end v.

(** Copy last element of a vector *)
Definition shiftrepeat {A} := @rectS _ (fun n _ => Vec A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

(** Take first [p] elements of a vector *)
Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:Vec A n) : Vec A p :=
  match p as p0 return p0 <= n -> Vec A n -> Vec A p0 with
  | O => fun _ _ => []
  | S p' => 
    match n as n0 return S p' <= n0 -> Vec A n0 -> Vec A (S p') with
    | O => fun le  => False_rect _ (Nat.nle_succ_0 p' le)
    | S n' => fun le v' => ((fst v'), take p' (le_S_n p' _ le) (snd v'))
    end
  end le v.

(** Remove [p] last elements of a vector *)
Lemma trunc : forall {A} {n} (p:nat), n > p -> Vec A n
  -> Vec A (n - p).
Proof.
  induction p as [| p f]; intros H v.
  rewrite <- minus_n_O.
  exact v.

  apply shiftout.

  rewrite minus_Sn_m.
  apply f.
  auto with *.
  exact v.
  auto with *.
Defined.

(** Concatenation of two vectors *)
Fixpoint append {A}{n}{p} (v : Vec A n) (w : Vec A p) : Vec A (n + p) :=
  match n as n0 return Vec A n0 -> Vec A (n0 + p) with
  | O => (fun _ => w)
  | S m => (fun v' => (fst v', (append (snd v') w)))
  end v.

Infix "++" := append.

(** Split a vector into two parts *)
Fixpoint splitat {A} (l : nat) {r : nat} :
  Vec A (l + r) -> Vec A l * Vec A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
              let (v1, v2) := splitat l' (tl v) in
              (hd v::v1, v2)
  end.

(** Two definitions of the tail recursive function that appends two lists but *)
(* reverses the first one *)

(** This one has the exact expected computational behavior *)
Fixpoint rev_append_tail {A n p} (v : Vec A n) (w: Vec A p)
  : Vec A (tail_plus n p) :=
  match n as n0 return Vec A n0 -> Vec A (tail_plus n0 p) with
  | O => (fun _ => w)
  | S m => (fun v' => rev_append_tail (snd v') ((fst v') :: w))
  end v.

Import EqdepFacts.

(** This one has a better type *)
Definition rev_append {A n p} (v: Vec A n) (w: Vec A p)
  :Vec A (n + p) :=
  rew <- (plus_tail_plus n p) in (rev_append_tail v w).

(** rev [a₁ ; a₂ ; .. ; an] is [an ; a{n-1} ; .. ; a₁] *)

(* Caution : There is a lot of rewrite garbage in this definition *)
Definition rev {A n} (v : Vec A n) : Vec A n :=
 rew <- (plus_n_O _) in (rev_append v []).

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.
(** * Here are special non dependent useful instantiation of induction schemes *)

(** Uniform application on the arguments of the vector *)
Definition map {A} {B} (f : A -> B) : forall {n} (v : Vec A n), Vec B n :=
  fix map_fix {n} (v : Vec A n) : Vec B n :=
    match n as n0 return Vec A n0 -> Vec B n0 with
    | O => (fun _ => [])
    | S m => (fun v' => (f (fst v'), (map_fix (snd v'))))
    end v.

(** map2 g [x1 .. xn] [y1 .. yn] = [(g x1 y1) .. (g xn yn)] *)
Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), Vec A n -> Vec B n -> Vec C n :=
@rect2 _ _ (fun n _ _ => Vec C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.

(** fold_left f b [x1 .. xn] = f .. (f (f b x1) x2) .. xn *)
Definition fold_left {A B:Type} (f : B -> A -> B) : forall (b : B) {n} (v : Vec A n), B :=
  fix fold_left_fix (b:B) {n} (v : Vec A n) : B :=
    match n as n0 return Vec A n0 -> B with
    | O => fun _ => b
    | S m => (fun v' => (fold_left_fix (f b (fst v')) (snd v')))
    end v.

(** fold_right f [x1 .. xn] b = f x1 (f x2 .. (f xn b) .. ) *)
Definition fold_right {A B : Type} (f : A -> B -> B) :=
  fix fold_right_fix {n} (v : Vec A n) (b : B) : B :=
    match n as n0 return Vec A n0 -> B with
    | O => fun _ => b
    | S m => (fun v' => f (fst v') (fold_right_fix (snd v') b))
    end v.

(** fold_right2 g c [x1 .. xn] [y1 .. yn] = g x1 y1 (g x2 y2 .. (g xn yn c) .. ) *)
(*     c is before the vectors to be compliant with "refolding". *)
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).


(** fold_left2 f b [x1 .. xn] [y1 .. yn] = g .. (g (g a x1 y1) x2 y2) .. xn yn *)
Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
  fix fold_left2_fix (a : A) {n} (v : Vec B n) : Vec C n -> A :=
    match n as n0 return Vec B n0 -> Vec C n0 -> A with
    | O => (fun v' w => case0 (fun _ => A) a w)
    | S m =>
      (fun v' w => caseS' w (fun _ => A)
                          (fun wh wt => fold_left2_fix (f a (fst v') wh) (snd v') wt))
    end v.

End ITERATORS.

Section SCANNING.
Inductive Forall {A} (P: A -> Prop): forall {n} (v: Vec A n), Prop :=
 |Forall_nil: Forall P []
 |Forall_cons {n} x (v: Vec A n): P x -> Forall P v -> Forall P (x::v).
Hint Constructors Forall : core.

Inductive Exists {A} (P:A->Prop): forall {n}, Vec A n -> Prop :=
 |Exists_cons_hd {m} x (v: Vec A m): P x -> Exists P (x::v)
 |Exists_cons_tl {m} x (v: Vec A m): Exists P v -> Exists P (x::v).
Hint Constructors Exists : core.

Inductive In {A} (a:A): forall {n}, Vec A n -> Prop :=
 |In_cons_hd {m} (v: Vec A m): In a (a::v)
 |In_cons_tl {m} x (v: Vec A m): In a v -> In a (x::v).
Hint Constructors In : core.

Inductive Forall2 {A B} (P:A->B->Prop): forall {n}, Vec A n -> Vec B n -> Prop :=
 |Forall2_nil: Forall2 P [] []
 |Forall2_cons {m} x1 x2 (v1:Vec A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
    Forall2 P (x1::v1) (x2::v2).
Hint Constructors Forall2 : core.

Inductive Exists2 {A B} (P:A->B->Prop): forall {n}, Vec A n -> Vec B n -> Prop :=
 |Exists2_cons_hd {m} x1 x2 (v1: Vec A m) (v2: Vec B m): P x1 x2 -> Exists2 P (x1::v1) (x2::v2)
 |Exists2_cons_tl {m} x1 x2 (v1:Vec A m) v2: Exists2 P v1 v2 -> Exists2 P (x1::v1) (x2::v2).
Hint Constructors Exists2 : core.

End SCANNING.

Section VECTORLIST.
(** * vector <=> list functions *)

Fixpoint of_list {A} (l : list A) : Vec A (length l) :=
match l as l' return Vec A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list tail))
end.

Definition to_list {A}{n} (v : Vec A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.
End VECTORLIST.

Module VectorNotations.
Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "[ ]" := [] (format "[ ]") : vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : vector_scope.
Notation "[ x ]" := (x :: []) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
Infix "++" := append : vector_scope.
Open Scope vector_scope.
End VectorNotations.
