Require Import Kami.Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition VarType := (string * option nat)%type.
Definition rtl_ty := (fun (_ : Kind) => VarType).
Definition RtlExpr := (Expr rtl_ty).
Definition RtlSysT := (SysT rtl_ty).

Record RtlModule :=
  { hiddenWires: list VarType;
    regFiles: list RegFileBase;
    inputs: list (VarType * Kind);
    outputs: list (VarType * Kind);
    regInits: list (VarType * sigT RegInitValT);
    regWrites: list (VarType * sigT RtlExpr);
    wires: list (VarType * sigT RtlExpr);
    sys: list (RtlExpr (SyntaxKind Bool) * list RtlSysT)
  }.
