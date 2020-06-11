Require Kami.StdLib.Vector.
Require Import Kami.StdLib.Fin.
Import VectorDef.
Import VectorNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition Vector_caseS'
           {A'} (Q : nat -> Type)
           (P : forall {n} (v : Vec A' (S n)), Q n -> Type)
           (H : forall h {n} t q, @P n (h :: t) q) {n} (v: Vec A' (S n))
           (q : Q n)
: P v q.
Proof.
  specialize (fun h t => H h _ t q).
  change n with (pred (S n)) in H, q |- *.
  set (Sn := S n) in *.
  pose (fun Sn (v : Vec A' Sn) (q : Q (pred Sn)) =>
          match Sn return Vec A' Sn -> Q (pred Sn) -> Type with
            | S n' => P n'
            | 0 => fun _ _ => True
          end v q) as P'.
  change (match Sn return Type with
            | 0 => True
            | _ => P' Sn v q
          end).
  change (forall h (t : match Sn with
                          | S n' => Vec A' n'
                          | 0 => Vec A' Sn
                        end),
            P' Sn (match Sn return match Sn with
                                     | S n' => Vec A' n'
                                     | 0 => Vec A' Sn
                                   end -> Vec A' Sn
                   with
                     | S _ => fun t => h :: t
                     | 0 => fun t => t
                   end t) q) in H.
  clearbody P'; clear P.
  clearbody Sn.
  destruct Sn.
  + constructor.
  + destruct v.
    apply H.
Defined.

Definition Vector_nth_map' A (f: A -> Type) (n: nat):
  forall v (p: Fin n),
    f (Vector.nth v p) ->
    Vector.nth (Vector.map f v) p.
Proof.
  induction n; intros v p.
  - contradiction.
  - destruct v as [v0 v].
    destruct p as [p|p].
    + destruct p; simpl; trivial.
    + exact (IHn v p).
Defined.

Definition Vector_nth_map A (f: A -> Type) n (v: Vec A n) p
           (m: f (Vector.nth v p)): Vector.nth (Vector.map f v) p := @Vector_nth_map' _ f n v p m.

Definition Vector_nth_map2_l' A B (g: A -> B) (f: B -> Type) n :
  forall (v: Vec A n) (p: Fin n),
    (forall p: Fin n, Vector.nth (Vector.map (fun x => f (g x)) v) p) ->
    f (Vector.nth (Vector.map g v) p).
Proof.
  induction n; intros v p.
  - contradiction.
  - destruct v as [v0 v]; destruct p as [p|p]; intro h.
    + destruct p; simpl; exact (h Fin.F1).
    + exact (IHn v p (fun q => h (inr q))).
Defined.

Definition Vector_nth_map2_l A B (g: A -> B) (f: B -> Type) n (v: Vec A n)
  (m: forall p: Fin n, Vector.nth (Vector.map (fun x => f (g x)) v) p)
  (p: Fin n): f (Vector.nth (Vector.map g v) p) := @Vector_nth_map2_l' _ _ g f n v p m.

Definition Vector_nth_map2_r' A B (g: A -> B) (f: B -> Type) n:
  forall (v: Vec A n) (p: Fin n),
    f (g (Vector.nth v p)) ->
    f (Vector.nth (Vector.map g v) p).
Proof.
  induction n; intros v p.
  - contradiction.
  - destruct v as [v0 v].
    destruct p as [p|p].
    + destruct p; simpl; trivial.
    + exact (IHn v p).
Defined.

Definition Vector_nth_map2_r A B (g: A -> B) (f: B -> Type) n (v: Vec A n)  (p: Fin n)
           (m: f (g (Vector.nth v p))):
  f (Vector.nth (Vector.map g v) p) := @Vector_nth_map2_r' _ _ g f n v p m.

Section find.
  Variable A: Type.
  Variable f: A -> bool.

  Fixpoint Vector_find_opt {n} : forall v : Vec A n, option (Fin n) :=
  match n with
  | 0 => fun _ => None
  | S m => fun v : Vec A (S m) =>
    if f (fst v)
    then Some Fin.F1
    else
      let acc : option (Fin m) := Vector_find_opt (snd v) in
      match acc with
      | None => None
      | Some p => Some (Fin.FS p)
      end
  end.
End find.

