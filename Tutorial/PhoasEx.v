Require Import String List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* A simple language to write a sequence of let bindings and finally
return a value. The values are all of type bools. We define primitive
operations to and/or two booleans and negation operator *)
Section Lambda.
  Variable ty: Type.
  (* ty is parameterizing the below inductive type Expr *)

  Inductive Expr: Type :=
  | Const (n: bool)
  | Andb (a b: Expr)
  | Orb (a b: Expr)
  | Negb (a: Expr)
  | Var (v: ty)
  (* The above construct enables injecting a term of type ty (the parameter for Expr) into an Expr.
     Depending on how ty is instantiated, we can get the denotional
     semantics for Expr as well as compile it into a string using
     fresh names for each let binding. We will see the two use cases below *)
  | LetExpr (x: Expr) (cont: ty -> Expr)
  (* The above construct creates a let-binding followed by a continuation that uses the let-binding.
     This is essentially an "application" of an "abstraction" (cont) to an Expr *)
  | Ret (x: Expr).
  (* The above construct closes a term in the Expr language *)
End Lambda.


(* The following function gives the denotional semantics of Expr.
   Note first that ty is instantiated to Bool. So every variable
   that we inject into the Expr is a boolean. This makes sense, since
   we want values of this language to be booleans and hence the denotation
   of a variable must be a boolean *)
Fixpoint evalExpr (e: Expr bool) :=
  match e with
  | Const n => n
  | Andb a b => andb (evalExpr a) (evalExpr b)
  | Orb a b => orb (evalExpr a) (evalExpr b)
  | Negb a => negb (evalExpr a)
  | Var v => v
  (* Notice above that the denotation of a variable is simply its value *)
  | LetExpr x cont => evalExpr (cont (evalExpr x))
  (* In the above, we pass the expression used in the let-binding to its 
     continuation so that the bound variable is replaced by its binding everywhere it is used *)
  | Ret x => evalExpr x
  end.

Local Open Scope string.
Fixpoint natStr (n: nat) :=
  match n with
  | 0 => "O"
  | S m => "S" ++ natStr m
  end.

(* This is a compiler that translates the above AST into concrete strings, creating
   a new temporary name for each let-binding. The idea is to have a counter (curr)
   that keeps incrementing each time a new let-binding is made. The current value of the
   counter essentially creates a reference to the expression that is let-bound. Whenever
   a "Var" is used, it in turn emits the counter value that was passed to it.
   The counter state is being threaded (i.e. the current value of the counter is the input,
   and the updated value of the counter is the output, along with the string.
   Only let-bindings increment the counter. *)
Fixpoint toString (e: Expr nat) curr: (nat * string) :=
  match e with
  | Const n => (curr, if n then "true" else "false")
  | Andb a b =>
    let '(next, str) := toString a curr in
    let '(final, strF) := toString b curr in
    (final, "(" ++ str ++ " && " ++ strF ++ ")")
  | Orb a b =>
    let '(next, str) := toString a curr in
    let '(final, strF) := toString b curr in
    (final, "(" ++ str ++ " || " ++ strF ++ ")")
  | Negb a =>
    let '(final, str) := toString a curr in
    (final, "(!" ++ str ++ ")")
  | Var v => (curr, "x" ++ natStr v)
  (* The above uses the value of the counter that was passed to it *)
  | LetExpr x cont =>
    let '(next, str) := toString x curr in
    (* This evaluates the let-binding expression. If the let-binding expressiong in turn
       has other let-bindings, then the counter will be incremented by it. Finally, the last
       value of the counter is returned. *)
    let '(final, strF) := toString (cont next) (S next) in
    (* We assign the last value of the counter returned by the let-binding expression (next) as 
       the reference to that expression. We then construct the string for the continuation,
       instantiating cont with the let-binding reference (next), while incrementing the counter
       that is passed to it, so that it does not reuse "next" *)
    (final, "let x" ++ natStr next ++ " := " ++ str ++ " in " ++ strF)
    (* Finally, we pretty print all the collected string.
       We prepend "x" to the name of the references for aesthetic purposes *)
  | Ret x => toString x curr
  end.

(* This is just a helper function that initializes the counter to 0 and ignores the updated counter value *)
Definition pretty (e: Expr nat) := snd (toString e 0).

Definition expr ty :=
  LetExpr (Orb (Const ty true) (Const _ false))
          (fun x => LetExpr (Const _ true)
                            (fun y => Andb (Var x) (Var y))).

(* This shows how the expression is pretty printed *)
Compute pretty (expr _).
