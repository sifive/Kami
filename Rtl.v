Require Import Kami.Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition VarType := (string * option nat)%type.
Definition rtl_ty := (fun (_ : Kind) => VarType).
Definition RtlExpr := (Expr rtl_ty).
Definition RtlSysT := (SysT rtl_ty).

Record RtlModule :=
  { hiddenWires: list (string * VarType);
    regFiles: list RegFileBase;
    inputs: list (string * VarType * Kind);
    outputs: list (string * VarType * Kind);
    regInits: list (string * sigT RegInitValT);
    regWrites: list (string * sigT RtlExpr);
    wires: list (string * VarType * sigT RtlExpr);
    sys: list (RtlExpr (SyntaxKind Bool) * list RtlSysT)
  }.
