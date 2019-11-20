Require Import Kami.All.
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

Definition int := Anything 0.

Definition listfoo := Anything ([] : list Foo).

Definition testNative :=
  MODULE {
         RegisterN "list" : listfoo <- []
    with RegisterN "count" : Nat <- 100

    (* increments counter *)
    with Rule "incr" := (
      ReadN x : NativeKind int <- "count";
      WriteN "count" : NativeKind int <- Var _ (NativeKind int) (S x);
      Retv)

    (* prints counter *)
    with Rule "count" := (
      ReadN x : NativeKind int <- "count";
      System [DispString _ ("Count: " ++ (nat_decimal_string x) ++ "\n")%string];
      Retv)

    (* appends A if count is even, else B*)
    with Rule "app_count" := (
      ReadN x : NativeKind int <- "count";
      ReadN xs : NativeKind listfoo <- "list";
      WriteN "list" : NativeKind listfoo <- Var _ (NativeKind listfoo) ((if Nat.even x then A else B)::xs);
      Retv)

      (* appends C *)
     with Rule "app_c" := (
      ReadN xs : NativeKind listfoo <- "list";
      WriteN "list" : NativeKind listfoo <- Var _ (NativeKind listfoo) (C::xs);
      Retv)

    (* prints list *)
    with Rule "list" := (
      ReadN xs : NativeKind listfoo <- "list";
      System [DispString _ ("List: " ++ (showListFoo xs) ++ "\n")%string];
      Retv)

    }.

End TestNative.

Definition mkMod(bm : BaseModule)(rfs : list RegFileBase) :=
  let md := (fold_right ConcatMod bm (map (fun m => Base (BaseRegFile m)) rfs)) in
  createHideMod md (map fst (getAllMethods md)).

Definition testNativeMod := mkMod testNative [].

Extract Inductive nat => "Prelude.Int" [ "0" "(Prelude.succ :: Prelude.Int -> Prelude.Int)" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
