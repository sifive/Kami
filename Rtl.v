Require Import Kami.Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition VarType := (string * option nat)%type.
Definition rtl_ty := (fun (_ : Kind) => VarType).
Definition RtlExpr := (Expr rtl_ty).
Definition RtlSysT := (SysT rtl_ty).

Record RtlModule :=
  { hiddenWires: list (string * nat);
    regFiles: list RegFileBase;
    inputs: list (string * nat * Kind);
    outputs: list (string * nat * Kind);
    regInits: list (string * sigT RegInitValT);
    regWrites: list (string * sigT RtlExpr);
    wires: list (string * nat * sigT RtlExpr);
    sys: list (RtlExpr (SyntaxKind Bool) * list RtlSysT)
  }.
