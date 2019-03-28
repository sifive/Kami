Require Import List.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition State (s a: Type) := s -> (a * s).

Definition get {s: Type} : State s s := fun i => (i, i).
Definition gets {s a: Type} f : State s a := fun s => (f s, s).
Definition put {s: Type} x : State s unit := fun _ => (tt, x).
Definition modify {s: Type} (f: s -> s): State s unit := fun i => (tt, f i).

Definition bind s a b (f: State s a) (g: a -> State s b) : State s b :=
  fun i =>
    let (x, y) := f i in g x y.

Definition ret s a (v: a) : State s a := fun i => (v, i).

Definition run s a (m: State s a) init : (a * s) := m init.

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

Section test.
  Let MyS := State (list nat) nat.

  Let ADef := 0.

  Let mon := (do test <- get ;
                do _ <- put (tail test) ;
                do test2 <- get ;
                ret (hd 0 test2)
             ).

  Let montest := eq_refl: (run mon (34 :: 673 :: 3 :: 84 :: nil) = (673, 673 :: 3 :: 84 :: nil)).
End test.
