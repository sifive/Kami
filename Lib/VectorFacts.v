Require Coq.Vectors.Vector.
Import Vectors.VectorDef.VectorNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition Vector_caseS'
           {A'} (Q : nat -> Type)
           (P : forall {n} (v : Vector.t A' (S n)), Q n -> Type)
           (H : forall h {n} t q, @P n (h :: t) q) {n} (v: Vector.t A' (S n))
           (q : Q n)
: P v q.
Proof.
  specialize (fun h t => H h _ t q).
  change n with (pred (S n)) in H, q |- *.
  set (Sn := S n) in *.
  pose (fun Sn (v : Vector.t A' Sn) (q : Q (pred Sn)) =>
          match Sn return Vector.t A' Sn -> Q (pred Sn) -> Type with
            | S n' => P n'
            | 0 => fun _ _ => True
          end v q) as P'.
  change (match Sn return Type with
            | 0 => True
            | _ => P' Sn v q
          end).
  change (forall h (t : match Sn with
                          | S n' => Vector.t A' n'
                          | 0 => Vector.t A' Sn
                        end),
            P' Sn (match Sn return match Sn with
                                     | S n' => Vector.t A' n'
                                     | 0 => Vector.t A' Sn
                                   end -> Vector.t A' Sn
                   with
                     | S _ => fun t => h :: t
                     | 0 => fun t => t
                   end t) q) in H.
  clearbody P'; clear P.
  clearbody Sn.
  destruct v as [|h ? t].
  { constructor. }
  { apply H. }
Defined.

Definition Vector_nth_map' A (f: A -> Type) (n: nat):
  forall v (p: Fin.t n),
    f (Vector.nth v p) ->
    Vector.nth (Vector.map f v) p.
Proof.
  induction p.
  - apply (Vector.caseS (fun n1 v1 => f (Vector.nth v1 Fin.F1) -> Vector.nth (Vector.map f v1) Fin.F1) (fun h n1 t => fun x => x) v).
  - apply (Vector.caseS (fun n1 v1 => forall p4, (forall v2, f (Vector.nth v2 p4) -> Vector.nth (Vector.map f v2) p4) ->
                                                 f (Vector.nth v1 (Fin.FS p4)) -> Vector.nth (Vector.map f v1) (Fin.FS p4))
                        (fun h n1 t p4 IHp2 =>
                           fun X => IHp2 t X)
                        v p IHp
          ).
Defined.

Definition Vector_nth_map A (f: A -> Type) n (v: Vector.t A n) p
           (m: f (Vector.nth v p)): Vector.nth (Vector.map f v) p := @Vector_nth_map' _ f n v p m.

Definition Vector_nth_map2_l' A B (g: A -> B) (f: B -> Type) n (v: Vector.t A n) (p: Fin.t n):
  (forall p: Fin.t n, Vector.nth (Vector.map (fun x => f (g x)) v) p) ->
  f (Vector.nth (Vector.map g v) p) :=
  Fin.t_rect
    (fun n0 p3 =>
       forall v0,
         (forall p, Vector.nth (Vector.map (fun x => f (g x)) v0) p) -> f (Vector.nth (Vector.map g v0) p3))
    (fun n0 v0 =>
       Vector.caseS
         (fun n1 v1 =>
            (forall p, Vector.nth (Vector.map (fun x => f (g x)) v1) p) -> f (Vector.nth (Vector.map g v1) Fin.F1))
         (fun h n1 t => fun x => x Fin.F1) v0)
    (fun n0 p3 IHp1 v0 =>
       Vector.caseS
         (fun n1 v1 =>
            forall p4,
              (forall v2,
                 (forall p, Vector.nth (Vector.map (fun x => f (g x)) v2) p) -> f (Vector.nth (Vector.map g v2) p4)) ->
              (forall p, Vector.nth (Vector.map (fun x => f (g x)) v1) p) -> f (Vector.nth (Vector.map g v1) (Fin.FS p4)))
         (fun h n1 t p4 IHp2 =>
            fun X => (IHp2 t (fun (p: Fin.t n1) => (X (Fin.FS p))))
         ) v0 p3 IHp1) n p v.

Definition Vector_nth_map2_l A B (g: A -> B) (f: B -> Type) n (v: Vector.t A n)
  (m: forall p: Fin.t n, Vector.nth (Vector.map (fun x => f (g x)) v) p)
  (p: Fin.t n): f (Vector.nth (Vector.map g v) p) := @Vector_nth_map2_l' _ _ g f n v p m.

Definition Vector_nth_map2_r' A B (g: A -> B) (f: B -> Type) n (v: Vector.t A n) (p: Fin.t n):
  f (g (Vector.nth v p)) ->
  f (Vector.nth (Vector.map g v) p).
Proof.
  induction p.
  - apply (Vector.caseS (fun n1 v1 => f (g (Vector.nth v1 Fin.F1)) ->
                                      f (Vector.nth (Vector.map g v1) Fin.F1)) (fun h n1 t => fun x => x) v).
  - apply (Vector.caseS (fun n1 v1 => forall p4, (forall v2, f (g (Vector.nth v2 p4)) -> f (Vector.nth (Vector.map g v2) p4)) ->
                                                 f (g (Vector.nth v1 (Fin.FS p4))) -> f (Vector.nth (Vector.map g v1) (Fin.FS p4)))
                        (fun h n1 t p4 IHp2 =>
                           fun X => IHp2 t X)
                        v p IHp
          ).
Defined.

Definition Vector_nth_map2_r A B (g: A -> B) (f: B -> Type) n (v: Vector.t A n)  (p: Fin.t n)
           (m: f (g (Vector.nth v p))):
  f (Vector.nth (Vector.map g v) p) := @Vector_nth_map2_r' _ _ g f n v p m.

Section find.
  Variable A: Type.
  Variable f: A -> bool.

  Fixpoint Vector_find' n (v: Vector.t A n): match n with
                                               | 0 => unit
                                               | S m => Fin.t (S m)
                                             end :=
  match v in Vector.t _ n0 return match n0 with
                                    | 0 => unit
                                    | S m0 => Fin.t (S m0)
                                  end with
    | Vector.nil => tt
    | Vector.cons h n1 t => if f h
                            then Fin.F1
                            else match n1 as n0 return (Vector.t _ n0 -> Fin.t (S n0)) with
                                   | 0 => fun _ => Fin.F1
                                   | S n2 => fun t0 => Fin.FS (Vector_find' t0)
                                 end t
  end.

  Definition Vector_find n (v: Vector.t A (S n)): Fin.t (S n) := Vector_find' v.


  Fixpoint Vector_find_opt n (v: Vector.t A n): option (Fin.t n) :=
    match v in Vector.t _ n0 return option (Fin.t n0) with
    | Vector.nil => None
    | Vector.cons h n1 t => if f h
                            then Some Fin.F1
                            else match n1 as n0 return (Vector.t _ n0 -> option (Fin.t (S n0)))
                                 with
                                   | 0 => fun _ => None
                                   | S n2 => fun t0 =>
                                               match Vector_find_opt t0 with
                                               | None => None
                                               | Some i => Some (Fin.FS i)
                                               end
                                 end t
  end.
End find.

