Require Import Kami.All. Import Word.Notations.
Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv.


Section Ex.
  (* The usual boiler plate *)
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Variable name: string.

  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  (* The parametricity argument, as described in the README.
     See PhoasEx.v for understanding the underlying concepts *)
  Variable ty: Kind -> Type.

  (* "k @# ty" is a way to specify an expression of kami of type k
     (indexed by ty, the parametricity index).  "k ## ty" is a way to
     specify a let-expression of kami of type k (again indexed by ty).
     The following action takes an input expression of Bit 10 and a
     let-expression of Bit 5, and performs a few operations on
     registers and makes an explicit call.  Note that one can read any
     register and write any register.  This is possible because
     registers are simply accessed using names and there's no scope
     for accessing them.  There's an explicit check, called Wf, that
     ensures that a module never accesses a register that it does not
     define.  Nevertheless, having name-based access allows us to
     write actions that access these register outside the context of a
     module. *)
  Definition exampleAction (e: Bit 10 @# ty) (le: Bit 5 ## ty): ActionT ty (Bit 10) := (
    Read x: Bit 10 <- @^"reg1";
    (* Note that we need to use convertLetExprSyntax_ActionT to convert any let-expression into an action *)
    LETA y <- convertLetExprSyntax_ActionT le;
    Write @^"reg2" <- {<#x + e, #y>};
    Call "extCall"(#x: _);
    Ret (#x + #x + e)
    ).

  (* Example of an Expr; One cannot read/write registers or call methods. *)
  Definition exampleExpr (e: Bit 4 @# ty) (f: Bit 6 @# ty): Bit 10 @# ty := $3 + $4 + {< e, f >}.

  (* Example of a LetExprSyntax *)
  Definition exampleLetExpr (e: Bit 4 ## ty) (f: Bit 6 ## ty): Bit 10 ## ty :=
    (
      (* Note that we need to use LETE to bind a let-expression directly *)
      LETE e' <- e;
      LETE f' <- f;
      
      (* But we use a LETC to bind a normal expression into a let-binding of a let-expression *)
      LETC x <- {< #e', #f' >};
      RetE #x
      ).
    
End Ex.
