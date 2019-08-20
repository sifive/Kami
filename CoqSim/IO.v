Require Import String Kami.All Kami.CoqSim.Misc.

(*
Parameter IO : Type -> Type.

Parameter ret : forall {X}, X -> IO X.
Parameter bind : forall {X Y}, IO X -> (X -> IO Y) -> IO Y.
*)

(* warning: do not pattern match on IO since there is no meaningful corresponding operation in Haskell *)
CoInductive IO : Type -> Type :=
  | print : string -> IO unit
  | ret : forall {X}, X -> IO X
  | bind : forall {X Y}, IO X -> (X -> IO Y) -> IO Y
  | error : forall {X}, string -> IO X
  | rand_bool : IO bool
  | rand_word : forall n, IO (word n)
  | exit : forall {X}, IO X.

CoFixpoint rr_aux(rem ios : list {X : Type & IO X}) : IO unit :=
  match rem with
  | [] => bind (ret tt) (fun _ => rr_aux ios ios)
  | io::rem' => bind (projT2 io) (fun _ => rr_aux rem' ios)
  end.

Definition rr(ios : list {X : Type & IO X}) : IO unit :=
  match ios with
  | [] => error "empty rule list"
  | _ => rr_aux ios ios
  end.




Notation "'io_do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

(*
Parameter print : string -> IO unit.
Parameter error : forall {X}, string -> IO X.
Parameter rand_bool : IO bool.
Parameter rand_word : forall n, IO (word n).
Parameter exit : forall {X}, IO X.
*)

Definition reg_not_found{X} : string -> IO X :=
  fun reg => error ("register " ++ reg ++ " not found.").

Fixpoint rand_vec{n X} : IO X -> IO (Vec X n) :=
  match n with
  | 0 => fun _ => ret tt
  | S m => fun mx => (
      io_do x <- mx;
      io_do v <- rand_vec mx;
      ret (x,v)
      )
  end.

Fixpoint rand_tuple{n} : forall ts : Fin.t n -> Type, (forall i, IO (ts i)) -> IO (Tuple ts) :=
  match n with
  | 0 => fun _ _ => ret tt
  | S m => fun ts mxs => (
      io_do x <- mxs Fin.F1;
      io_do xs <- rand_tuple (fun j => ts (Fin.FS j)) (fun j => mxs (Fin.FS j));
      ret (x,xs)
      )
  end.

