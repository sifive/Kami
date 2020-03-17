Require Import Fin Bool Kami.Lib.EclecticLib String Ascii List Streams.
Import ListNotations.

Fixpoint Fin n :=
  match n with
  | 0 => Empty_set
  | S m => (unit + Fin m)%type
  end.

Section Vector.

Fixpoint Vec X n : Type :=
  match n with
  | 0 => unit
  | S m => (X * Vec X m)%type
  end.

Fixpoint vec_index{n X} : Fin.t n -> Vec X n -> X :=
  match n with
  | 0 => case0 _
  | S m => fun i v => fin_case i _ (fst v) (fun j => vec_index j (snd v))
  end.

Fixpoint mkVec{n X} : (Fin.t n -> X) -> Vec X n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun f => (f Fin.F1, mkVec (fun j => f (Fin.FS j)))
  end.

Fixpoint VecEq{n X} : (X -> X -> bool) -> Vec X n -> Vec X n -> bool :=
  match n with
  | 0 => fun _ _ _ => true
  | S m => fun eq v1 v2 => eq (fst v1) (fst v2) && VecEq eq (snd v1) (snd v2)
  end.

Fixpoint vmap{n X Y}(f : X -> Y) : Vec X n -> Vec Y n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun '(x,xs) => (f x, vmap f xs)
  end.

Fixpoint v_to_list{n X} : Vec X n -> list X :=
  match n with
  | 0 => fun _ => []
  | S m => fun '(x,xs) => x::v_to_list xs
  end.

Fixpoint add_indices_aux{n X} : nat -> Vec X n -> Vec (nat * X) n :=
  match n return nat -> Vec X n -> Vec (nat * X) n with
  | 0 => fun _ _ => tt
  | S m => fun acc '(x,xs) => ((acc,x), add_indices_aux (S acc) xs)
  end.

Definition add_indices{n X} : Vec X n -> Vec (nat * X) n := add_indices_aux 0.

Fixpoint add_strings{n X} : (Fin.t n -> string) -> Vec X n -> Vec (string * X) n :=
  match n return (Fin.t n -> string) -> Vec X n -> Vec (string * X) n with
  | 0 => fun _ _ => tt
  | S m => fun strs '(x,xs) => ((strs Fin.F1,x),add_strings (fun j => strs (Fin.FS j)) xs)
  end.

End Vector.

Section Tuple.

Fixpoint Tuple{n} : (Fin.t n -> Type) -> Type :=
  match n with
  | 0 => fun _ => unit
  | S m => fun ts => ((ts Fin.F1) * (Tuple (fun j => ts (Fin.FS j))))%type
  end.

Fixpoint Tup_map{n} : forall (ts1 ts2 : Fin.t n -> Type)(fs : forall i, ts1 i -> ts2 i)(t : Tuple ts1), Tuple ts2 :=
  match n with
  | 0 => fun _ _ _ _ => tt
  | S m => fun ts1 ts2 fs t => (fs F1 (fst t), Tup_map (fun i => ts1 (FS i)) (fun i => ts2 (FS i)) (fun i => fs (FS i)) (snd t))
  end.

Fixpoint tup_index{n} : forall (i : Fin.t n) ts, Tuple ts -> ts i :=
  match n with
  | 0 => case0 _
  | S m => fun i ts t => fin_case i _ (fst t) (fun j => tup_index j (fun j => ts (Fin.FS j)) (snd t))
  end.

Fixpoint mkTup{n} : forall ts : Fin.t n -> Type, (forall i, ts i) -> Tuple ts :=
  match n with
  | 0 => fun _ _ => tt
  | S m => fun ts es => (es Fin.F1, mkTup (fun j => ts (Fin.FS j)) (fun j => es (Fin.FS j)))
  end.

Fixpoint TupEq{n} : forall ts : Fin.t n -> Type, (forall i, ts i -> ts i -> bool) -> Tuple ts -> Tuple ts -> bool :=
  match n with
  | 0 => fun _ _ _ _ => true
  | S m => fun ts eqs t1 t2 => eqs Fin.F1 (fst t1) (fst t2) && TupEq (fun j => ts (Fin.FS j)) (fun j => eqs (Fin.FS j)) (snd t1) (snd t2)
  end.

Fixpoint tup_to_vec{n X} : forall (ts : Fin.t n -> Type)(to_X : forall i, ts i -> X), Tuple ts -> Vec X n :=
  match n with
  | 0 => fun _ _ _ => tt
  | S m => fun ts to_X '(x,t) => (to_X Fin.F1 x, tup_to_vec (fun j => ts (Fin.FS j)) (fun j => to_X (Fin.FS j)) t)
  end.

End Tuple.

Section Lookup.

Fixpoint Fin_lookup{X}(pred : X -> bool){n} : (Fin.t n -> X) -> option (Fin.t n) :=
  match n return (Fin.t n -> X) -> option (Fin.t n) with
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

Definition space_pad(final_len : nat)(x : string) : string :=
  char_replicate " " (final_len - String.length x) ++ x.

Definition zero_pad(final_len : nat)(x : string) : string :=
  char_replicate "0" (final_len - String.length x) ++ x.

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
