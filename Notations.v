Require Import Kami.Syntax Kami.Lib.EclecticLib Kami.Tactics.
Require Import RecordUpdate.RecordSet.
Require Import Program.Wf.
Require Import Wf_nat.
Require Import BinNums.
(*
Definition natToHexStr (n : nat) : string :=
  match (BinNat.N.of_nat n) with
  | N0     => "0"
  | Npos p => of_pos p ""
  end.

Definition AddIndexToName name idx := (name ++ "_" ++ natToHexStr idx)%string.

Definition AddIndicesToNames name idxs := List.map (fun x => AddIndexToName name x) idxs.
*)
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

Require Import Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Section nat_string.
  Unset Implicit Arguments.

  (*
    Accepts two arguments: radix and ns; and returns: ns[0] + radix *
    ns[1] + radix^2 * ns[2] + ... radix^n * ns[n]

    Ex: nat_decomp_nat 2 [1; 0; 1; 1] = 13.
  *)
  Local Fixpoint nat_decomp_nat (radix : nat) (ns : list nat) : nat
    := match ns with
       | [] => 0
       | m :: ms => (radix * nat_decomp_nat radix ms) + m
       end.

  Local Fixpoint nat_decomp_prod (x : nat) (ns : list nat) : list nat
    := match ns with
       | [] => []
       | m :: ms => x * m :: nat_decomp_prod x ms
       end.

  (* 0 = Nat.div x y ==> x < y ==> x = x mod y *)
  Lemma div0_mod : forall x y : nat, y <> 0 -> 0 = Nat.div x y -> x = x mod y.
  Proof.
    exact
      (fun x y H H0
        => eq_sym (Nat.mod_small x y
             (proj1 (Nat.div_small_iff x y H)
               (eq_sym H0)))).
  Qed.

  Local Definition nat_decomp
    (radix : nat) (* radix minus 2 *)
    (n : nat)
    :  {ms : list nat |
         Forall (fun m => m < (S (S radix))) ms /\
         n = nat_decomp_nat (S (S radix)) ms}
    := Fix_F
         (fun n
           => {ms : list nat |
                Forall (fun m => m < (S (S radix))) ms /\
                n = nat_decomp_nat (S (S radix)) ms})
         (fun n (F : forall r, r < n -> {ms : list nat | Forall (fun m => m < (S (S radix))) ms /\ r = nat_decomp_nat (S (S radix)) ms})
           => nat_rec
                (fun q
                  => q = Nat.div n (S (S radix)) ->
                     {ms : list nat |
                       Forall (fun m => m < (S (S radix))) ms /\
                       n = nat_decomp_nat (S (S radix)) ms})
                (fun H : 0 = Nat.div n (S (S radix))
                  => let H0 : n = nat_decomp_nat (S (S radix)) [n mod (S (S radix))]
                       := ltac:(
                            lazy [nat_decomp_nat list_rec list_rect];
                            rewrite (Nat.mul_0_r (S (S radix)));
                            rewrite (Nat.add_0_l _);
                            apply (div0_mod n (S (S radix)) (Nat.neq_succ_0 (S radix)) H)) in
                     exist
                       (fun ms
                         => Forall (fun m => m < (S (S radix))) ms /\
                            n = nat_decomp_nat (S (S radix)) ms)
                       [n mod (S (S radix))]
                       (conj
                         (Forall_cons (n mod (S (S radix))) 
                           (Nat.mod_upper_bound n (S (S radix)) (Nat.neq_succ_0 (S radix)))
                           (Forall_nil (fun m => m < S (S radix))))
                         H0))
                (fun q _ (H : S q = Nat.div n (S (S radix)))
                  => let (ms, H0)
                       := F (S q)
                            (eq_ind_r
                              (fun x => x < n)
                              (Nat.div_lt n (S (S radix))
                                (or_ind
                                  (fun H0 : 0 < n => H0)
                                  (fun H0 : 0 = n
                                    => False_ind (0 < n)
                                         (let H2 : Nat.div n (S (S radix)) = 0
                                            := eq_ind
                                                 0
                                                 (fun x => Nat.div x (S (S radix)) = 0)
                                                 (Nat.div_0_l (S (S radix)) (Nat.neq_succ_0 (S radix)))
                                                 n
                                                 H0 in
                                          let H1 : S q = 0
                                            := eq_ind_r (fun x => x = 0) H2 H in
                                          Nat.neq_succ_0 q H1))
                                  ((proj1 (Nat.lt_eq_cases 0 n))
                                    (Nat.le_0_l n)))
                                (le_n_S 1 (S radix) (le_n_S 0 radix (Nat.le_0_l radix)))) 
                              H) in
                     let xs := n mod (S (S radix)) :: ms in
                     let H1 : n = nat_decomp_nat (S (S radix)) xs
                       := ltac:(
                            unfold xs;
                            lazy [nat_decomp_nat list_rec list_rect];
                            fold (nat_decomp_nat (S (S radix)));
                            rewrite <- (proj2 H0);
                            rewrite H;
                            rewrite <- (Nat.div_mod n (S (S radix)) (Nat.neq_succ_0 (S radix)));
                            reflexivity) in
                     let H2 : Forall (fun m => m < S (S radix)) xs
                       := Forall_cons (n mod S (S radix))
                           (Nat.mod_upper_bound n (S (S radix)) (Nat.neq_succ_0 (S radix)))
                           (proj1 H0) in
                     exist _ xs (conj H2 H1))
                (Nat.div n (S (S radix)))
                eq_refl)%nat
         (lt_wf n).

  (* Every function that has an inverse is injective. *)
  Local Theorem inv_inj
    : forall (A B : Type) (f : A -> B) (g : B -> A),
        (forall x : A, g (f x) = x) ->
        (forall x y : A, f x = f y -> x = y).
  Proof.
    exact
      (fun A B f g Hinv x
        => NNPP
             (forall y : A, f x = f y -> x = y)
             (fun H
               => let H0 := not_all_ex_not A (fun y => f x = f y -> x = y) H in
                  ex_ind
                    (fun y (H1 : ~ (f x = f y -> x = y))
                      => let (H2, H3)
                           := imply_to_and (f x = f y) (x = y) H1 in
                         let H4 : g (f x) = g (f y)
                           := f_equal g H2 in
                         ltac:(
                           rewrite (Hinv x) in H4;
                           rewrite (Hinv y) in H4;
                           contradiction))
                    H0)).
  Qed.

  Local Theorem nat_decomp_inj
    (radix : nat) (* radix minus 2 *)
    :  forall n m : nat, proj1_sig (nat_decomp radix n) = proj1_sig (nat_decomp radix m) -> n = m.
  Proof.
    exact
      (inv_inj _ _
        (fun x => proj1_sig (nat_decomp radix x))
        (nat_decomp_nat (S (S radix)))  
        (fun x => eq_sym (proj2 (proj2_sig (nat_decomp radix x))))).
  Qed.

  Local Open Scope char_scope.

  Local Fixpoint nat_decomp_chars
    (radix : nat) (* radix minus 2 *)
    (encoding : forall n, n < S (S radix) -> ascii)
    (ns : list nat)
    :  Forall (fun n => n < S (S radix)) ns -> list ascii
    := match ns with
       | [] => fun _ => []
       | m :: ms
         => fun H : Forall (fun n => n < S (S radix)) (m :: ms)
              => nat_decomp_chars radix encoding ms (Forall_inv_tail H) ++
                 [encoding m (Forall_inv H)]
       end.

  Local Theorem nat_decomp_chars_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    : forall 
         (ns : list nat)
         (ms : list nat)
         (Hns : Forall (fun n => n < S (S radix)) ns)
         (Hms : Forall (fun m => m < S (S radix)) ms),
         nat_decomp_chars radix encoding ns Hns =
         nat_decomp_chars radix encoding ms Hms ->
         ns = ms.
  Proof.
    exact
      (list_ind
        (fun ns
          => forall
               (ms : list nat)
               (Hns : Forall (fun n => n < S (S radix)) ns)
               (Hms : Forall (fun m => m < S (S radix)) ms),
               nat_decomp_chars radix encoding ns Hns =
               nat_decomp_chars radix encoding ms Hms ->
               ns = ms)
        (list_ind
          (fun ms
            => forall
                 (Hns : Forall (fun n => n < S (S radix)) [])
                 (Hms : Forall (fun m => m < S (S radix)) ms),
                 nat_decomp_chars radix encoding [] Hns =
                 nat_decomp_chars radix encoding ms Hms ->
                 [] = ms)
          (fun _ _ _ => ltac:(reflexivity))
          (fun _ _ _ _ _ H => False_ind _ (app_cons_not_nil _ _ _ H)))
        (fun n ns F
          => list_ind
               (fun ms
                 => forall
                      (Hns : Forall (fun n => n < S (S radix)) (n :: ns))
                      (Hms : Forall (fun m => m < S (S radix)) ms),
                      nat_decomp_chars radix encoding (n :: ns) Hns =
                      nat_decomp_chars radix encoding ms Hms ->
                      (n :: ns) = ms)
               (fun _ _ H => False_ind _ (app_cons_not_nil _ _ _ (eq_sym H)))
               (fun m ms G Hns Hms H
                 => let H0
                      :  ns = ms
                      := F ms
                           (Forall_inv_tail Hns)
                           (Forall_inv_tail Hms)
                           (proj1 (app_inj_tail 
                             (nat_decomp_chars radix encoding ns (Forall_inv_tail Hns))
                             (nat_decomp_chars radix encoding ms (Forall_inv_tail Hms))
                             (encoding n (Forall_inv Hns))
                             (encoding m (Forall_inv Hms))
                             H)) in
                    sumbool_ind
                      (fun _ => _)
                      (fun H1 : n = m
                        => ltac:(rewrite H0; rewrite H1; reflexivity) : (n :: ns) = (m :: ms))
                      (fun H1 : n <> m
                        => let H2
                             :  encoding n (Forall_inv Hns) = encoding m (Forall_inv Hms)
                             := proj2 (app_inj_tail
                                  (nat_decomp_chars radix encoding ns (Forall_inv_tail Hns))
                                  (nat_decomp_chars radix encoding ms (Forall_inv_tail Hms))
                                  (encoding n (Forall_inv Hns))
                                  (encoding m (Forall_inv Hms))
                                  H) in
                           False_ind _
                             (H1 (encoding_inj n m (Forall_inv Hns) (Forall_inv Hms) H2)))
                       (Nat.eq_dec n m)))).
  Qed.

  Local Definition nat_chars
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (n : nat)
    :  list ascii
    := nat_decomp_chars radix encoding
         (proj1_sig (nat_decomp radix n))
         (proj1 (proj2_sig (nat_decomp radix n))).

  Local Theorem nat_chars_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    :  forall n m : nat, nat_chars radix encoding n = nat_chars radix encoding m -> n = m.
  Proof.
    intros n m H.
    assert ((proj1_sig (nat_decomp radix n)) = (proj1_sig (nat_decomp radix m))).
    apply (nat_decomp_chars_inj radix encoding encoding_inj 
            (proj1_sig (nat_decomp radix n))
            (proj1_sig (nat_decomp radix m))
            (proj1 (proj2_sig (nat_decomp radix n)))
            (proj1 (proj2_sig (nat_decomp radix m)))
            H).
    apply (nat_decomp_inj radix n m H0).
  Qed.
    
  Local Definition nat_string
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (n : nat)
    :  string
    := string_of_list_ascii (nat_chars radix encoding n).

  Local Lemma string_of_list_ascii_inj
    : forall xs ys : list ascii, string_of_list_ascii xs = string_of_list_ascii ys -> xs = ys.
  Proof.
    exact
      (inv_inj _ _
        string_of_list_ascii
        list_ascii_of_string
        list_ascii_of_string_of_list_ascii).
  Qed.

  Local Theorem nat_string_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    :  forall n m : nat, nat_string radix encoding n = nat_string radix encoding m -> n = m.
  Proof.
    intros n m H.
    assert (nat_chars radix encoding n = nat_chars radix encoding m).
    apply (string_of_list_ascii_inj _ _ H).
    assert ((proj1_sig (nat_decomp radix n)) = (proj1_sig (nat_decomp radix m))).
    apply (nat_decomp_chars_inj radix encoding encoding_inj 
            (proj1_sig (nat_decomp radix n))
            (proj1_sig (nat_decomp radix m))
            (proj1 (proj2_sig (nat_decomp radix n)))
            (proj1 (proj2_sig (nat_decomp radix m)))
            H0).
    apply (nat_decomp_inj radix n m H1).
  Qed.

  Local Ltac notIn H (* In x xs *) := repeat (destruct H; repeat (discriminate; assumption)).

  Local Ltac encoding_NoDup xs
    := lazymatch xs with
       | nil => exact (NoDup_nil ascii)
       | (cons ?X ?XS)%list
         => exact
              (NoDup_cons X 
                (fun H : In X XS => ltac:(notIn H))
                (ltac:(encoding_NoDup XS)))
       end.

  Local Definition decode (encoding : list ascii) (n : nat) : ascii
    := List.nth n encoding " ".

  Local Definition decode_safe (encoding : list ascii) (n : nat) (_ : n < List.length encoding)
    := decode encoding n.

  Local Ltac digit_encoding_inj encoding
    := exact
         (proj1 (NoDup_nth encoding " ") 
            ltac:(encoding_NoDup encoding)
           : forall n m : nat,
               n < List.length encoding ->
               m < List.length encoding ->
               decode encoding n = decode encoding m ->
               n = m).

  Local Ltac encoding_inj radix encoding (* radix = encoding - 2 *)
    := exact
         (nat_string_inj
           radix
           (decode_safe encoding)
           (ltac:(digit_encoding_inj encoding))).

  Local Definition binary_encoding_list : list ascii := ["0"; "1"].

  Definition natToBinStr : nat -> string
    := nat_string 0 (decode_safe binary_encoding_list).

  Definition natToBinStr_inj
    :  forall n m, natToBinStr n = natToBinStr m -> n = m
    := ltac:(encoding_inj 0 ["0"; "1"]%list).

  Local Definition decimal_encoding_list : list ascii
    := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"].

  Definition natToDecStr : nat -> string
    := nat_string 8 (decode_safe decimal_encoding_list).

  Definition natToDecStr_inj
    :  forall n m, natToDecStr n = natToDecStr m -> n = m
    := ltac:(encoding_inj 8 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]%list).

  Local Definition hex_encoding_list : list ascii
    := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"].

  Definition natToHexStr : nat -> string
    := nat_string 14 (decode_safe hex_encoding_list).

  Definition natToHexStr_inj
    :  forall n m, natToHexStr n = natToHexStr m -> n = m
    := ltac:(encoding_inj 14 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"]%list).

  Local Close Scope char_scope.

  Local Open Scope string_scope.

  (* Goal (natToHexStr 179 = "B3"). Proof. reflexivity. Qed. *)
  Goal (natToDecStr 179 = "179"). Proof. reflexivity. Qed.
  Goal (natToBinStr 179 = "10110011"). Proof. reflexivity. Qed.

  Local Close Scope string_scope.

  Local Close Scope list.

  Set Implicit Arguments.

End nat_string.

(* The following definitions are DEPRECATED. *)
(*
Section Positive.
  Local Open Scope positive_scope.
  Fixpoint of_pos (p : positive) (rest : string) : string :=
    match p with
    | 1 => String "1" rest
    | 2 => String "2" rest
    | 3 => String "3" rest
    | 4 => String "4" rest
    | 5 => String "5" rest
    | 6 => String "6" rest
    | 7 => String "7" rest
    | 8 => String "8" rest
    | 9 => String "9" rest
    | 10 => String "A" rest
    | 11 => String "B" rest
    | 12 => String "C" rest
    | 13 => String "D" rest
    | 14 => String "E" rest
    | 15 => String "F" rest
    | p'~0~0~0~0 => of_pos p' (String "0" rest)
    | p'~0~0~0~1 => of_pos p' (String "1" rest)
    | p'~0~0~1~0 => of_pos p' (String "2" rest)
    | p'~0~0~1~1 => of_pos p' (String "3" rest)
    | p'~0~1~0~0 => of_pos p' (String "4" rest)
    | p'~0~1~0~1 => of_pos p' (String "5" rest)
    | p'~0~1~1~0 => of_pos p' (String "6" rest)
    | p'~0~1~1~1 => of_pos p' (String "7" rest)
    | p'~1~0~0~0 => of_pos p' (String "8" rest)
    | p'~1~0~0~1 => of_pos p' (String "9" rest)
    | p'~1~0~1~0 => of_pos p' (String "A" rest)
    | p'~1~0~1~1 => of_pos p' (String "B" rest)
    | p'~1~1~0~0 => of_pos p' (String "C" rest)
    | p'~1~1~0~1 => of_pos p' (String "D" rest)
    | p'~1~1~1~0 => of_pos p' (String "E" rest)
    | p'~1~1~1~1 => of_pos p' (String "F" rest)
    end.
  Local Close Scope positive_scope.
  Definition natToHexStr (n : nat) : string :=
    match (BinNat.N.of_nat n) with
    | N0     => "0"
    | Npos p => of_pos p ""
    end.
End Positive.

Definition AddIndexToName name idx := (name ++ "_" ++ natToHexStr idx)%string.

Definition AddIndicesToNames name idxs := List.map (fun x => AddIndexToName name x) idxs.

Fixpoint pos_length(x : positive) : nat :=
  match x with
  | xH => 0
  | xI y => S (pos_length y)
  | xO y => S (pos_length y)
  end.

Lemma string_lemma1 : forall str c d, (str <> "" -> str ++ (String c EmptyString) <> String d EmptyString)%string.
Proof.
  intros.
  destruct str.
  - elim H; reflexivity.
  - destruct str; discriminate.
Qed.

Lemma string_lemma2 : forall str c str', (str ++ String c str' = (str ++ (String c "")) ++ str')%string.
Proof.
  destruct str'.
  - rewrite append_nil; auto.
  - rewrite <- append_assoc; auto.
Qed.

Lemma string_lemma3 : forall str str' c c', (str ++ String c "" = str' ++ String c' "")%string ->
  c = c'.
Proof.
  induction str; intros.
  - destruct str'.
    + inversion H; auto.
    + inversion H.
      * destruct str'; discriminate.
  - destruct str'.
    + inversion H.
      destruct str; discriminate.
    + inversion H.
      eapply IHstr.
      exact H2.
Qed.

Lemma string_lemma4 : forall str1 str2 c c' str3, (str1 ++ (String c str3) = str2 ++ (String c' str3))%string
 -> c = c'.
Proof.
  intros.
  rewrite (string_lemma2 str1) in H.
  rewrite (string_lemma2 str2) in H.
  rewrite append_remove_suffix in H.
  eapply string_lemma3.
  exact H.
Qed.

Ltac pop_bits n x :=
  match n with
  | 0 => idtac
  | S ?m => let y := fresh "y" in
            let z := fresh "z" in
  destruct x as [ y | z | ]; [ pop_bits m y | pop_bits m z | idtac ]
  end.

Lemma of_pos_suff_aux : forall n x suff, pos_length x = n -> of_pos x suff = (of_pos x "" ++ suff)%string.
Proof.
  intro n.
  induction n using (well_founded_induction lt_wf).
  intros.
  pop_bits 4 x; simpl;
  match goal with
  | |- of_pos ?p (String ?c ?suff) = (of_pos ?p (String ?c EmptyString) ++ ?suff)%string =>
      assert (pos_length p < n) as pf by (simpl in H0; lia);
      rewrite (H _ pf _ (String c suff) eq_refl);
      rewrite (H _ pf _ (String c EmptyString) eq_refl);
      apply string_lemma2
  | _ => reflexivity
  end.
Qed.

Lemma of_pos_suff : forall x suff, of_pos x suff = (of_pos x "" ++ suff)%string.
Proof.
  intros; eapply of_pos_suff_aux.
  reflexivity.
Qed.

Lemma of_pos_ne : forall x, of_pos x "" <> "".
Proof.
  pop_bits 4 x;
  try discriminate;
  try (simpl;
       rewrite of_pos_suff;
       destruct (of_pos _ "");
       discriminate).
Qed.

Lemma of_pos_nz : forall x, of_pos x "" <> "0".
Proof.
  pop_bits 4 x;
  try discriminate;
  try (simpl; rewrite of_pos_suff; apply string_lemma1; apply of_pos_ne).
Qed.

Lemma of_pos_lemma1 : forall p q str c c', of_pos p (String c str) = of_pos q (String c' str) -> c = c'.
Proof.
  intros.
  rewrite (of_pos_suff p), (of_pos_suff q) in H.
  exact (string_lemma4 _ _ _ _ _ H).
Qed.

Lemma length_append : forall str str', (String.length (str ++ str') = String.length str + String.length str')%string.
Proof.
  induction str; intros.
  - auto.
  - simpl.
    rewrite IHstr; auto.
Qed.

Lemma of_pos_lemma2 : forall p str c d, of_pos p (String c str) <> String d str.
Proof.
  intros; rewrite of_pos_suff; intro.
  apply (f_equal String.length) in H.
  rewrite length_append in H.
  simpl in H.
  destruct (of_pos p "") eqn:G.
  - exact (of_pos_ne _ G).
  - simpl in H; lia.
Qed.

Lemma of_pos_inj_aux : forall n str x y, pos_length x = n -> of_pos x str = of_pos y str -> x = y.
Proof.
  intro n.
  induction n using (well_founded_induction lt_wf); intros str x y lenx of_pos_eq.
  pop_bits 4 x; pop_bits 4 y; simpl in *;
   match goal with
   | |- ?x = ?x => reflexivity
   | [ _ : of_pos ?p (String ?c ?str) = of_pos ?q (String ?c ?str) |- _ ]
      => assert (pos_length p < n) as pf by (simpl in lenx; lia);
         rewrite (H _ pf _ _ _ eq_refl of_pos_eq); reflexivity
   | [ H : of_pos ?p (String ?c str) = of_pos ?q (String ?d str) |- _ ] => discriminate (of_pos_lemma1 _ _ _ _ _ H)
   | [ H : of_pos ?p (String ?c ?str) = String ?d ?str |- _ ] => elim (of_pos_lemma2 _ _ H)
   | [ H : String ?d ?str = of_pos ?p (String ?c ?str) |- _ ] => symmetry in H; elim (of_pos_lemma2 _ _ H)
   | _ => discriminate
   end.
Qed.

Lemma of_pos_inj : forall str x y, of_pos x str = of_pos y str -> x = y.
Proof.
  intros.
  eapply of_pos_inj_aux.
  reflexivity.
  exact H.
Qed.

Lemma natToHexStr_inj :
  forall n m,
    natToHexStr n = natToHexStr m ->
    n = m.
Proof.
  intros n m Hnm.
  unfold natToHexStr in Hnm.
  destruct n,m; simpl in Hnm.
  - reflexivity.
  - symmetry in Hnm; elim (of_pos_nz _ Hnm).
  - elim (of_pos_nz _ Hnm).
  - f_equal.
    apply SuccNat2Pos.inj.
    eapply of_pos_inj; exact Hnm.
Qed.
*)
