Require Import Bool Kami.Lib.EclecticLib String Ascii List Streams.
Require Import Kami.StdLib.Vector.
Require Import Kami.StdLib.Fin.
Import ListNotations.

Section Tuple.

Fixpoint Tuple{n} : (Fin n -> Type) -> Type :=
  match n with
  | 0 => fun _ => unit
  | S m => fun ts => ((ts Fin.F1) * (Tuple (fun j => ts (Fin.FS j))))%type
  end.

Fixpoint Tup_map{n} : forall (ts1 ts2 : Fin n -> Type)(fs : forall i, ts1 i -> ts2 i)(t : Tuple ts1), Tuple ts2 :=
  match n with
  | 0 => fun _ _ _ _ => tt
  | S m => fun ts1 ts2 fs t => (fs F1 (fst t), Tup_map (fun i => ts1 (FS i)) (fun i => ts2 (FS i)) (fun i => fs (FS i)) (snd t))
  end.

Fixpoint tup_index{n} : forall (i : Fin n) ts, Tuple ts -> ts i :=
  match n with
  | 0 => case0 (fun i => _)
  | S m => fun i ts t => fin_case i _ (fst t) (fun j => tup_index j (fun j => ts (Fin.FS j)) (snd t))
  end.

Fixpoint mkTup{n} : forall ts : Fin n -> Type, (forall i, ts i) -> Tuple ts :=
  match n with
  | 0 => fun _ _ => tt
  | S m => fun ts es => (es Fin.F1, mkTup (fun j => ts (Fin.FS j)) (fun j => es (Fin.FS j)))
  end.

Fixpoint TupEq{n} : forall ts : Fin n -> Type, (forall i, ts i -> ts i -> bool) -> Tuple ts -> Tuple ts -> bool :=
  match n with
  | 0 => fun _ _ _ _ => true
  | S m => fun ts eqs t1 t2 => eqs Fin.F1 (fst t1) (fst t2) && TupEq (fun j => ts (Fin.FS j)) (fun j => eqs (Fin.FS j)) (snd t1) (snd t2)
  end.

Fixpoint tup_to_vec{n X} : forall (ts : Fin n -> Type)(to_X : forall i, ts i -> X), Tuple ts -> Vec X n :=
  match n with
  | 0 => fun _ _ _ => tt
  | S m => fun ts to_X '(x,t) => (to_X Fin.F1 x, tup_to_vec (fun j => ts (Fin.FS j)) (fun j => to_X (Fin.FS j)) t)
  end.

End Tuple.

Section Lookup.

Fixpoint Fin_lookup{X}(pred : X -> bool){n} : (Fin n -> X) -> option (Fin n) :=
  match n return (Fin n -> X) -> option (Fin n) with
  | 0 => fun _ => None
  | S m => fun f => if pred (f F1) then Some F1 else
      match Fin_lookup pred (fun j => f (FS j)) with
      | None => None
      | Some i => Some (FS i)
      end
  end.

(* Check lookup.

Definition lookup{K X} : (K -> K -> bool) -> K -> list (K * X) -> option X :=
  fun eqbk key pairs => match List.find (fun p => eqbk key (fst p)) pairs with
                        | Some p => Some (snd p)
                        | None => None
                        end. *)

End Lookup.

Section PrintUtil.

Open Scope char_scope.

Fixpoint char_replicate(c : ascii)(n : nat) : string :=
  match n with
  | 0 => EmptyString
  | S m => String c (char_replicate c m)
  end.

Fixpoint string_drop(n : nat)(str : string) : string :=
  match n with
  | 0 => str
  | S m => match str with
           | EmptyString => EmptyString
           | String c str' => string_drop m str'
           end
  end.

Definition pad_with(c : ascii)(n : nat)(str : string) : string :=
  if Nat.ltb (String.length str) n then char_replicate c (n - String.length str) ++ str else string_drop (String.length str - n) str.

(* 
Fixpoint intersperse(x : string)(xs : list string) : list string :=
  match xs with
  | [] => []
  | y::ys => match ys with
             | [] => xs
             | z::zs => y::x::intersperse x ys
             end
  end.
 *)
End PrintUtil.

Section Streams.

CoFixpoint unwind_list_aux{X}(xs ys : list X) : ys <> [] -> Stream X :=
  match ys return ys <> [] -> Stream X with
  | [] => fun pf => match pf eq_refl with end
  | y::zs => fun pf => match xs with
                       | x::xs' => Cons x (unwind_list_aux xs' (y::zs) pf)
                       | [] => Cons y (unwind_list_aux zs (y::zs) pf)
                       end
  end.

Definition unwind_list{X}(xs : list X) : xs <> [] -> Stream X :=
  unwind_list_aux xs xs.

Fixpoint take{X}(n : nat)(xs : Stream X) : list X :=
  match n with
  | 0 => []
  | S m => match xs with
           | Cons x xs' => x :: take m xs'
           end
  end.

End Streams.

Section Option.

Definition o_bind{X Y}(o : option X)(cont : X -> option Y) : option Y :=
  match o with
  | Some x => cont x
  | None => None
  end.

Definition o_ret{X}(x : X) : option X := Some x.

End Option.

Notation "'o_do' x <- y ; cont" := (o_bind y (fun x => cont)) (at level 20).
