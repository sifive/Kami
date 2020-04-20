Require Import Kami.All.
Require Import Kami.Lib.NatStr.
Require Import String.

Section TestNative.

Local Open Scope kami_expr.
Local Open Scope kami_action.

Inductive Foo := A | B | C.

Definition showFoo x :=
  match x with
  | A => "A"
  | B => "B"
  | C => "C"
  end.

Definition showListFoo xs :=
  ("[" ++ concat ";" (map showFoo xs) ++ "]")%string.

Definition int := NativeKind 0.
Definition listfoo := NativeKind ([] : list Foo).

Definition testNativeModule :=
  MODULE {
         RegisterN "list" : listfoo <- []
    with RegisterN "count" : int <- 0

    (* increments counter *)
    with Rule "incr" := (
      ReadN x : int <- "count";
      WriteN "count" : int <- Var _ int (S x);
      Retv)

    (* prints counter *)
    with Rule "count" := (
      ReadN x : int <- "count";
      System [DispString _ ("Count: " ++ (natToHexStr x) ++ "\n")%string];
      Retv)

    (* appends A if count is even, else B*)
    with Rule "app_count" := (
      ReadN x : int <- "count";
      ReadN xs : listfoo <- "list";
      WriteN "list" : listfoo <- Var _ listfoo ((if Nat.even x then A else B)::xs);
      Retv)

      (* appends C *)
     with Rule "app_c" := (
      ReadN xs : listfoo <- "list";
      WriteN "list" : listfoo <- Var _ listfoo (C::xs);
      Retv)

    (* prints list *)
    with Rule "list" := (
      ReadN xs : listfoo <- "list";
      System [DispString _ ("List: " ++ (showListFoo xs) ++ "\n")%string];
      Retv)

    }.

End TestNative.

Definition mkMod(bm : BaseModule)(rfs : list RegFileBase) :=
  let md := (fold_right ConcatMod bm (map (fun m => Base (BaseRegFile m)) rfs)) in
  createHideMod md (map fst (getAllMethods md)).

Definition testNative := mkMod testNativeModule [].

Extract Inductive nat => "Prelude.Int" [ "0" "(Prelude.succ :: Prelude.Int -> Prelude.Int)" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
