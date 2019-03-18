Require Import Syntax Thread RecordUpdate.RecordSet.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope string.

Local Definition SynExpr ty k := (Expr ty (SyntaxKind k)).

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Section lret.
    Variable lret: Kind.
    
    Inductive CompActionT: Prop :=
    | CompReadCtxt (r: string) (k: Kind) (regMap: regMapTy) (cont: ty k -> CompActionT): CompActionT
    | CompLetExpr k (e: SynExpr ty k) (cont: ty k -> CompActionT): CompActionT
    | CompLetCtxt (vals: forall sk: (string * Kind), SynExpr ty (snd sk)) (cont: regMapTy -> CompActionT):
        CompActionT
    | CompRet (vals: forall sk: (string * Kind), SynExpr ty (snd sk)) (e: SynExpr ty lret): CompActionT
    | CompCall (f: string) (argRetK: Kind * Kind) (pred: SynExpr ty Bool) (arg: SynExpr ty (fst argRetK))
               (cont: ty (snd argRetK) -> CompActionT): CompActionT.
  End lret.
End Compile.
