Require Import Kami.Syntax Kami.Lib.EclecticLib Kami.Tactics.
Require Import Kami.Lib.NatStr.
Require Import RecordUpdate.RecordSet.
Require Import Program.Wf.
Require Import Wf_nat.
Require Import BinNums.

Definition AddIndexToName name idx := (name ++ "_" ++ natToHexStr idx)%string.

Definition AddIndicesToNames name idxs := List.map (fun x => AddIndexToName name x) idxs.

(* Notation for normal mods *)
Inductive ModuleElt: Type :=
| MERegister (_ : RegInitT)
| MERule (_ : Attribute (Action Void))
| MEMeth (_ : DefMethT).

Fixpoint makeModule'  (xs: list ModuleElt) :=
  match xs with
  | e :: es =>
    let '(iregs, irules, imeths) := makeModule' es in
    match e with
    | MERegister mreg => (mreg :: iregs, irules, imeths)
    | MERule mrule => (iregs, mrule :: irules, imeths)
    | MEMeth mmeth => (iregs, irules, mmeth :: imeths)
    end
  | nil => (nil, nil, nil)
  end.

Fixpoint makeModule_regs  (xs: list ModuleElt) :=
  match xs with
  | e :: es =>
    let iregs := makeModule_regs es in
    match e with
    | MERegister mreg => mreg :: iregs
    | MERule mrule => iregs
    | MEMeth mmeth => iregs
    end
  | nil => nil
  end.

Fixpoint makeModule_rules  (xs: list ModuleElt) :=
  match xs with
  | e :: es =>
    let irules := makeModule_rules es in
    match e with
    | MERegister mreg => irules
    | MERule mrule => mrule :: irules
    | MEMeth mmeth => irules
    end
  | nil => nil
  end.

Fixpoint makeModule_meths  (xs: list ModuleElt) :=
  match xs with
  | e :: es =>
    let imeths := makeModule_meths es in
    match e with
    | MERegister mreg => imeths
    | MERule mrule => imeths
    | MEMeth mmeth => mmeth :: imeths
    end
  | nil => nil
  end.

Definition makeModule (im : list ModuleElt) :=
  BaseMod (makeModule_regs im) (makeModule_rules im) (makeModule_meths im).

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Fixpoint getOrder  (xs: list ModuleElt) :=
  match xs with
  | e :: es =>
    let names := getOrder es in
    match e with
    | MERegister _ => names
    | MERule mrule => fst mrule :: names
    | MEMeth mmeth => fst mmeth :: names
    end
  | nil => nil
  end.

(* Definition getOrder (im : Tree ModuleElt) := getOrder' (flattenTree im). *)

(** Notations for Struct **)

Declare Scope kami_expr_scope.
Delimit Scope kami_expr_scope with kami_expr.

Declare Scope kami_struct_scope.
Notation "name :: ty" := (name%string,  ty) (only parsing) : kami_struct_scope.
Delimit Scope kami_struct_scope with kami_struct.

(** Notations for expressions *)

Notation "k @# ty" := (Expr ty (SyntaxKind k)) (no associativity, at level 98, only parsing).
Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (no associativity, at level 0, only parsing) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (no associativity, at level 0): kami_expr_scope.
Notation "$$ e" := (Const ltac:(assumption) e) (at level 8, only parsing) : kami_expr_scope.

Notation "! v" := (UniBool Neg v) (at level 35): kami_expr_scope.
Notation "e1 && e2" := (CABool And (e1 :: e2 :: nil)) : kami_expr_scope.
Notation "e1 || e2" := ((@Kor _ Bool) (e1 :: e2 :: nil)) : kami_expr_scope.
Notation "e1 ^^ e2" := (CABool Xor (e1 :: e2 :: nil)) (at level 50): kami_expr_scope.
Notation "~ x" := (UniBit (Inv _) x) : kami_expr_scope.

Notation "a $[ i : j ]":=
  ltac:(let aTy := type of a in
        match aTy with
        | Expr _ (SyntaxKind ?bv) =>
          let bvSimpl := eval compute in bv in
              match bvSimpl with
              | Bit ?w =>
                let middle := eval simpl in (i + 1 - j)%nat in
                    let top := eval simpl in (w - 1 - i)%nat in
                        exact (ConstExtract j middle top a)
              end
        end) (at level 100, i at level 99, only parsing) : kami_expr_scope.

Notation "a $#[ i : j ]":=
  ltac:(let aTy := type of a in
        match aTy with
        | Expr _ (SyntaxKind ?bv) =>
          let bvSimpl := eval compute in bv in
              match bvSimpl with
              | Bit ?w =>
                let middle := eval simpl in (i + 1 - j)%nat in
                    let top := eval simpl in (w - 1 - i)%nat in
                        exact (ConstExtract j middle top (@castBits _ w (j + middle + top) ltac:(abstract (lia || nia)) a))
              end
        end) (at level 100, i at level 99, only parsing) : kami_expr_scope.

Notation "e1 + e2" := (CABit (Add) (e1 :: e2 :: nil)) : kami_expr_scope.
Notation "e1 * e2" := (CABit (Mul) (e1 :: e2 :: nil)) : kami_expr_scope.
Notation "e1 .& e2" := (CABit (Band) (e1 :: e2 :: nil)) (at level 201)
                       : kami_expr_scope.
Notation "e1 .| e2" := (Kor (e1 :: e2 :: nil)) (at level 201)
                       : kami_expr_scope.
Notation "e1 .^ e2" := (CABit (Bxor) (e1 :: e2 :: nil)) (at level 201) : kami_expr_scope.
Infix "-" := (BinBit (Sub _)) : kami_expr_scope.
Infix "/" := (BinBit (Div _)) : kami_expr_scope.
Infix "%%" := (BinBit (Rem _)) (at level 100): kami_expr_scope.
Infix "<<" := (BinBit (Sll _ _)) (at level 100) : kami_expr_scope.
Infix ">>" := (BinBit (Srl _ _)) (at level 100) : kami_expr_scope.
Infix ">>>" := (BinBit (Sra _ _)) (at level 100) : kami_expr_scope.
Notation "{< a , .. , b >}" :=
  ((BinBit (Concat _ _)) a .. (BinBit (Concat _ _) b (@Const _ (Bit 0) WO)) ..)
    (at level 100, a at level 99): kami_expr_scope.
Notation "{< a , .. , b >}" :=
  (wcombine b .. (wcombine a WO) ..)
    (at level 100, a at level 99): word_scope.

Infix "<" := (BinBitBool (LessThan _)) : kami_expr_scope.
Notation "x > y" := (BinBitBool (LessThan _) y x) : kami_expr_scope.
Notation "x >= y" := (UniBool Neg (BinBitBool (LessThan _) x y)) : kami_expr_scope.
Notation "x <= y" := (UniBool Neg (BinBitBool (LessThan _) y x)) : kami_expr_scope.
Infix "<s" := (Slt _) (at level 70): kami_expr_scope.
Notation "x >s y" := (Slt _ y x) (at level 70, y at next level): kami_expr_scope.
Notation "x >=s y" := (UniBool Neg (Slt _ x y)) (at level 100) : kami_expr_scope.
Notation "x <=s y" := (UniBool Neg (Slt _ y x)) (at level 100): kami_expr_scope.
Infix "==" := Eq (at level 39, no associativity) : kami_expr_scope.
Notation "x != y" := (UniBool Neg (Eq x y))
                       (at level 39, no associativity) : kami_expr_scope.
Notation "v @[ idx ] " := (ReadArray v idx) (at level 38) : kami_expr_scope.
Notation "v '@[' idx <- val ] " := (UpdateArray v idx val) (at level 38) : kami_expr_scope.

Notation "s @% f" := ltac:(struct_get_field_ltac s%kami_expr f%string)
                            (at level 38, only parsing): kami_expr_scope.

Declare Scope kami_struct_init_scope.
Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (snd a)))
          (name%string, _) value) (at level 50) : kami_struct_init_scope.
Delimit Scope kami_struct_init_scope with struct_init.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStructVal (cons s1%struct_init ..
                      (cons sN%struct_init nil) ..))
  : kami_expr_scope.

Declare Scope kami_switch_init_scope.
Notation "name ::= value" :=
  (name, value) (only parsing): kami_switch_init_scope.
Delimit Scope kami_switch_init_scope with switch_init.

Notation "s '@%[' f <- v ]" := ltac:(struct_set_field_ltac s f v)
                                      (at level 38, only parsing): kami_expr_scope.

Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) : kami_expr_scope.

Notation "nkind <[ def ]>" := (@NativeKind nkind def) (at level 100): kami_expr_scope.

(* One hot switches *)
Notation "'Switch' val 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (Kor (cons (IF val == fst s1%switch_init then pack (snd s1%switch_init) else $0)%kami_expr ..
                          (cons (IF val == fst sN%switch_init then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

Notation "'Switch' val 'Of' inK 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (Kor (cons (IF val == ((fst s1%switch_init): inK @# _) then pack (snd s1%switch_init) else $0)%kami_expr ..
                          (cons (IF val == ((fst sN%switch_init): inK @# _) then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

(* Notations for Let Expressions *)
Notation "'LETE' name <- expr ; cont " :=
  (LetE expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'LETE' name : t <- expr ; cont " :=
  (LetE (k' := t) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'RetE' expr" :=
  (NormExpr expr%kami_expr) (at level 13) : kami_expr_scope.
Notation "'LETC' name <- v ; c " :=
  (LETE name <- RetE v ; c)%kami_expr
                           (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'LETC' name : t <- v ; c " :=
  (LETE name : t <- RetE v ; c)%kami_expr
                               (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'SystemE' ls ; c " :=
  (SysE ls c)%kami_expr (at level 13, right associativity, ls at level 99): kami_expr_scope.
Notation "'IfE' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElseE cexpr%kami_expr tact fact (fun name => cont))
    (at level 14, right associativity) : kami_expr_scope.
Notation "'IfE' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElseE cexpr%kami_expr tact fact (fun _ => cont))
    (at level 14, right associativity) : kami_expr_scope.
Notation "'IfE' cexpr 'then' tact ; cont" :=
  (IfElseE cexpr%kami_expr tact (RetE (Const _ Default))%kami_expr (fun _ => cont))
    (at level 14, right associativity) : kami_expr_scope.



Notation "k ## ty" := (LetExprSyntax ty k) (no associativity, at level 98, only parsing).

(** Notations for action *)

Declare Scope kami_action_scope.
Notation "'Call' meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, Void) a%kami_expr (fun _ => cont))
    (at level 13, right associativity, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' name : retT <- meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, retT) a%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 0, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' meth () ; cont " :=
  (MCall meth%string (Void, Void) (Const _ Default) (fun _ => cont))
    (at level 13, right associativity, meth at level 0) : kami_action_scope.
Notation "'Call' name : retT <- meth () ; cont " :=
  (MCall meth%string (Void, retT) (Const _ Default) (fun name => cont))
    (at level 13, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'LETN' name : fullkind <- expr ; cont " :=
  (LetExpr (k := fullkind) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name <- expr ; cont " :=
  (LetExpr expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (LetExpr (k := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name <- act ; cont " :=
  (LetAction act (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name : t <- act ; cont " :=
  (LetAction (k := t) act (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'NondetN' name : fullkind ; cont" :=
  (ReadNondet fullkind (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Nondet' name : kind ; cont" :=
  (ReadNondet (SyntaxKind kind) (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'ReadN' name : fullkind <- reg ; cont " :=
  (ReadReg reg fullkind (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg reg _ (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg reg (SyntaxKind kind) (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'WriteN' reg : fullkind <- expr ; cont " :=
  (@WriteReg _ _ reg fullkind expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg reg expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@WriteReg _ _ reg (SyntaxKind kind) expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact ; cont" :=
  (IfElse cexpr%kami_expr tact (Return (Const _ Default)) (fun _ => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'System' sysexpr ; cont " :=
  (Sys sysexpr%kami_expr cont)
    (at level 13, right associativity) : kami_action_scope.
Notation "'Ret' expr" :=
  (Return expr%kami_expr)%kami_expr (at level 13) : kami_action_scope.
Notation "'Retv'" := (Return (Const _ (k := Void) Default)) : kami_action_scope.

Delimit Scope kami_action_scope with kami_action.

Notation "'ReadRf' val : k <- meth ( addr : idxT ) ; cont" :=
  (MCall meth (idxT, Array 1 k) addr
         (fun raw => LetExpr (ReadArrayConst (@Var _ (SyntaxKind (Array 1 k)) raw) Fin.F1) (fun val => cont)))%kami_action
  (at level 13, right associativity, meth at level 0, addr at level 99, val at level 0): kami_action_scope.
Notation "'ReadReqRf' meth ( addr : idxT ) ; cont" :=
  (MCall meth (idxT, Void) addr (fun _ => cont))%kami_action
  (at level 13, right associativity, meth at level 0, addr at level 99): kami_action_scope.
Notation "'ReadResRf' val : k <- meth () ; cont" :=
  (MCall meth (Void, Array 1 k) (@Const _ Void (getDefaultConst Void))
         (fun raw => LetExpr (ReadArrayConst (@Var _ (SyntaxKind (Array 1 k)) raw) Fin.F1) (fun val => cont)))%kami_action
  (at level 13, right associativity, meth at level 0, val at level 0): kami_action_scope.
Notation "'WriteRf' meth ( addr : lgIdxNum ; data : k ) ; cont" :=
  (MCall meth (WriteRq lgIdxNum (Array 1 k), Void) (STRUCT { "addr" ::= addr ; "data" ::= BuildArray (fun _ => data) })%kami_expr
         (fun _ => cont))%kami_action
  (at level 13, right associativity, meth at level 0, addr at level 99, data at level 99): kami_action_scope.

(* Complex List Actions *)
Fixpoint gatherActions (ty: Kind -> Type) k_in (acts: list (ActionT ty k_in)) k_out
         (cont: list (Expr ty (SyntaxKind k_in)) -> ActionT ty k_out): ActionT ty k_out :=
  match acts with
  | nil => cont nil
  | x :: xs =>
    (LetAction x (fun val =>
                    gatherActions xs (fun vals => cont ((Var ltac:(assumption) (SyntaxKind _) val) :: vals))))
  end.

Definition readNames (ty: Kind -> Type) k names := map (fun r => 
                                                          (ReadReg r (SyntaxKind k) 
                                                                   (fun tmp => 
                                                                      (Return (Var ltac:(assumption) (SyntaxKind _) tmp))))) names.

Definition callNames (ty: Kind -> Type) k names := map (fun r =>
                                                          (MCall r (Void, k) (Const _ Default) (fun tmp => (Return (Var ltac:(assumption) (SyntaxKind _) tmp))))) names.

Definition writeNames (ty: Kind -> Type) k namesVals :=
  map (fun r => 
         (@WriteReg _ _ (fst r) (SyntaxKind k) (snd r)
                    (Return (Const ty (ZToWord 0 0))))) namesVals.

(* Complex list action notations *)
Notation "'GatherActions' actionList 'as' val ; cont" :=
  (gatherActions actionList (fun val => cont))
    (at level 13, right associativity, val at level 99) : kami_action_scope.

Notation "'ReadToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (readNames _ k names) (fun val => cont))
    (at level 13, right associativity, val at level 99) : kami_action_scope.

Notation "'CallToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (callNames _ k names) (fun val => cont))
    (at level 13, right associativity, val at level 99): kami_action_scope.

Declare Scope kami_init_scope.
Notation "'WriteToList' names 'of' k 'using' vals ; cont" :=
  (gatherActions (@writeNames _ k (List.combine names vals)) (fun _ => cont))
    (at level 13, right associativity, vals at level 99) : kami_action_scope.
Delimit Scope kami_init_scope with kami_init.

Notation "'ARRAY' { x1 ; .. ; xn }" :=
  (BuildArray (nth_Fin (cons x1%kami_init .. (cons xn%kami_init nil) ..)))
  : kami_expr_scope.

Declare Scope kami_struct_initial_scope.
Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => ConstT (snd a))
          (name%string, _) value) (at level 50) : kami_struct_initial_scope.
Delimit Scope kami_struct_initial_scope with struct_initial.

Declare Scope kami_scope.
Delimit Scope kami_scope with kami.

Notation "'RegisterN' name : type <- init" :=
  (((MERegister (name%string, existT RegInitValT type (Some ((NativeConst init)%kami_init)%word))) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'RegisterNDef' name : type <- init" :=
  ((MERegister (name%string, existT RegInitValT (@NativeKind type init)%kami_init (Some ((NativeConst init)%kami_init))) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'Register' name : type <- init" :=
  (((MERegister (name%string, existT RegInitValT (SyntaxKind type) (Some (makeConst ((init)%kami_init)%word)))) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'RegisterU' name : type" :=
  (((MERegister (name%string, existT RegInitValT (SyntaxKind type) None)) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'Method' name () : retT := c" :=
  (((MEMeth (name%string, existT MethodT (Void, retT)
                                     (fun ty (_: ty Void) => c%kami_action : ActionT ty retT))) :: nil))
    (at level 13, name at level 9) : kami_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (((MEMeth (name%string, existT MethodT (dom, retT)
                                      (fun ty (param : ty dom) => c%kami_action : ActionT ty retT))) :: nil))
    (at level 13, name at level 9, param at level 99) : kami_scope.

Notation "'Rule' name := c" :=
  (((MERule (name%string, fun ty => (c)%kami_action : ActionT ty Void)) :: nil))
    (at level 13) : kami_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule ((app m1%kami .. (app mN%kami nil) ..)))
    (only parsing).

Notation "'MODULE_WF' { m1 'with' .. 'with' mN }" :=
  {| baseModuleWf := {| baseModule := (makeModule ((app m1%kami .. (app mN%kami nil) ..))) ;
                        wfBaseModule := ltac:(discharge_wf) |} ;
     baseModuleOrd := getOrder ((app m1%kami .. (app mN%kami nil) ..)) |}
    (only parsing).

Notation "'MOD_WF' { m1 'with' .. 'with' mN }" :=
  {| modWf := {| module := Base (makeModule ((app m1%kami .. (app mN%kami nil) ..))) ;
                    wfMod := ltac:(discharge_wf) |} ;
     modOrd := getOrder ((app m1%kami .. (app mN%kami nil) ..)) |}
    (only parsing).

Notation "'MODULE_WF_new' { m1 'with' .. 'with' mN }" :=
  {| baseModuleWf_new := {| baseModule_new := (makeModule ((app m1%kami .. (app mN%kami nil) ..))) ;
                        wfBaseModule_new := ltac:(discharge_wf_new) |} ;
     baseModuleOrd_new := getOrder ((app m1%kami .. (app mN%kami nil) ..)) |}
    (only parsing).

Notation "'MOD_WF_new' { m1 'with' .. 'with' mN }" :=
  {| modWf_new := {| module_new := Base (makeModule ((app m1%kami .. (app mN%kami nil) ..))) ;
                 wfMod_new := ltac:(discharge_wf_new) |} ;
     modOrd_new := getOrder ((app m1%kami .. (app mN%kami nil) ..)) |}
    (only parsing).

(* Notation "'RegisterVec' name 'using' nums : type <- init" := *)
(*   (MERegAry ( *)
(*        map (fun idx => *)
(*               (AddIndexToName name idx, existT RegInitValT (SyntaxKind type) (Some (makeConst (init)%kami_init))) *)
(*            ) nums *)
(*   )) *)
(*     (at level 13, name at level 9, nums at level 9) : kami_scope. *)



(* Gallina Record Notations *)
Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
                                    (at level 12, left associativity).
Notation "x <| proj  ::==  f |>" := (set proj f x)
                                      (at level 12, f at next level, left associativity).


Notation "'STRUCT_TYPE' { s1 ; .. ; sN }" :=
  (getStruct (cons s1%kami_struct .. (cons sN%kami_struct nil) ..)).

Notation "'ARRAY_CONST' { x1 ; .. ; xn }" :=
  (ConstArray (nth_Fin' (cons (x1%kami_init)%word .. (cons (xn%kami_init)%word nil) ..) eq_refl)).

Notation "'STRUCT_CONST' { s1 ; .. ; sN }" :=
  (getStructConst (cons (s1%struct_initial)%word ..
                        (cons (sN%struct_initial)%word nil) ..)).

Notation "i #: n" := (ltac:(let y := eval cbv in (@Fin.of_nat_lt (i)%nat (n)%nat ltac:(cbv; lia)) in exact y))
                       (at level 10, only parsing).

Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= x })%kami_expr
                                                                       (at level 100, only parsing) : kami_expr_scope.

Notation "'InvData' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= x })%kami_expr
                                                                          (at level 100, only parsing) : kami_expr_scope.

Section mod_test.
  Variable a: string.
  Local Notation "^ x" := (a ++ "." ++ x)%string (at level 0).

  Local Example test : ModWf type := MOD_WF{
                                         (concat [Register (^"x") : Bool <- true; Register (^"z") : Bool <- false])
                                           with Register (^"y") : Bool <- false
                                           with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                                Write (^"x"): Bool <- #y;
                                                                Retv)
                                       }.

  Local Example test1 : ModWf type := MODULE_WF{
                                        (concat [Register (^"x") : Bool <- true; Register (^"w"): Bool <- true;
                                                Register (^"t"): Bit 0 <- WO])
                                          with Register (^"y") : Bool <- false
                                          with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                               Write (^"x"): Bool <- #y;
                                                               Retv )
                                      }.

  Local Example test_new : ModWf_new type := MOD_WF_new {
                                                 (concat [Register (^"x") : Bool <- true; Register (^"z") : Bool <- false])
                                                   with Register (^"y") : Bool <- false
                                                   with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                                        Write (^"x"): Bool <- #y;
                                                                        Retv )
                                               }.

Local Example test1_new : BaseModuleWf_new type := MODULE_WF_new{
                                                       (concat [Register (^"x") : Bool <- true; Register (^"w"): Bool <- true;
                                                               Register (^"t"): Bit 0 <- WO])
                                                         with Register (^"y") : Bool <- false
                                                         with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                                              Write (^"x"): Bool <- #y;
                                                                              Retv )
                                                       }.

End mod_test.

Definition Registers := (map MERegister).

Definition Rules := (map MERule).

Definition Methods := (map MEMeth).
