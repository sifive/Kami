Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv Eqdep.
Require Import Kami.Syntax Kami.Lib.EclecticLib Kami.Tactics.
Require Import RecordUpdate.RecordSet.
Require Import Wf.
Require Import Wf_nat.
(* Require Import BinNums. *)

Definition natToHexStr (n : nat) : string :=
  match (BinNat.N.of_nat n) with
  | N0     => "0"
  | Npos p => of_pos p ""
  end.

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
Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (at level 0, only parsing) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (at level 9): kami_expr_scope.
Notation "$$ e" := (Const ltac:(assumption) e) (at level 8, only parsing) : kami_expr_scope.

Notation "! v" := (UniBool Neg v) (at level 35): kami_expr_scope.
Notation "e1 && e2" := (CABool And (e1 :: e2 :: nil)) : kami_expr_scope.
Notation "e1 || e2" := (CABool Or (e1 :: e2 :: nil)) : kami_expr_scope.
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
Notation "e1 & e2" := (CABit (Band) (e1 :: e2 :: nil)) (at level 201)
                      : kami_expr_scope.
Notation "e1 | e2" := (CABit (Bor) (e1 :: e2 :: nil)) (at level 201)
                      : kami_expr_scope.
Notation "e1 ^ e2" := (CABit (Bxor) (e1 :: e2 :: nil)) : kami_expr_scope.
Infix "-" := (BinBit (Sub _)) : kami_expr_scope.
Infix "/" := (BinBit (Div _)) : kami_expr_scope.
Infix "%%" := (BinBit (Rem _)) (at level 100): kami_expr_scope.
Infix "<<" := (BinBit (Sll _ _)) (at level 100) : kami_expr_scope.
Infix ">>" := (BinBit (Srl _ _)) (at level 100) : kami_expr_scope.
Infix ">>>" := (BinBit (Sra _ _)) (at level 100) : kami_expr_scope.
Notation "{< a , .. , b >}" :=
  ((BinBit (Concat _ _)) a .. (BinBit (Concat _ _) b (@Const _ (Bit 0) (zToWord 0 0))) ..)
    (at level 100, a at level 99): kami_expr_scope.
Notation "{< a , .. , b >}" :=
  (wconcat b .. (wconcat a (zToWord 0 0)) ..)
    (at level 100, a at level 99): word_scope.

Infix "<" := (BinBitBool (LessThan _)) : kami_expr_scope.
Notation "x > y" := (BinBitBool (LessThan _) y x) : kami_expr_scope.
Notation "x >= y" := (UniBool Neg (BinBitBool (LessThan _) x y)) : kami_expr_scope.
Notation "x <= y" := (UniBool Neg (BinBitBool (LessThan _) y x)) : kami_expr_scope.
Infix "<s" := (Slt _) (at level 70) : kami_expr_scope.
Notation "x >s y" := (Slt _ y x) (at level 70, y at next level) : kami_expr_scope.
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
  (unpack retK (CABit Bor (cons (IF val == fst s1%switch_init then pack (snd s1%switch_init) else $0)%kami_expr ..
                                (cons (IF val == fst sN%switch_init then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

Notation "'Switch' val 'Of' inK 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons (IF val == ((fst s1%switch_init): inK @# _) then pack (snd s1%switch_init) else $0)%kami_expr ..
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
                    (Return (Const ty (zToWord 0 0))))) namesVals.

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
  ((MERegister (name%string, existT RegInitValT type (Some ((NativeConst init)%kami_init))) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'RegisterNDef' name : type <- init" :=
  ((MERegister (name%string, existT RegInitValT (@NativeKind type init)%kami_init (Some ((NativeConst init)%kami_init))) :: nil))
    (at level 13, name at level 99) : kami_scope.

Notation "'Register' name : type <- init" :=
  (((MERegister (name%string, existT RegInitValT (SyntaxKind type) (Some (makeConst ((init)%kami_init))))) :: nil))
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
  (ConstArray (nth_Fin' (cons (x1%kami_init) .. (cons (xn%kami_init) nil) ..) eq_refl)).

Notation "'STRUCT_CONST' { s1 ; .. ; sN }" :=
  (getStructConst (cons (s1%struct_initial) ..
                        (cons (sN%struct_initial) nil) ..)).

Notation "i #: n" := (@Fin.of_nat_lt (i)%nat (n)%nat ltac:(lia)) (at level 10, only parsing).

Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= x })%kami_expr
                                                                       (at level 100, only parsing) : kami_expr_scope.

Notation "'InvData' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= x })%kami_expr
                                                                          (at level 100, only parsing) : kami_expr_scope.

Section mod_test.
  Variable a: string.
  Local Notation "^ x" := (a ++ "." ++ x)%string (at level 0).
  Local Example test := MOD_WF{
                              (concat [Register (^"x") : Bool <- true; Register (^"z") : Bool <- false])
                                with Register (^"y") : Bool <- false
                                with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                         Write (^"x"): Bool <- #y;
                                                         Retv )
                          }.

  Local Example test1 := MODULE_WF{
                             (concat [Register (^"x") : Bool <- true; Register (^"w"): Bool <- true;
                                        Register (^"t"): Bit 0 <- (zToWord 0 Z0)])
                               with Register (^"y") : Bool <- false
                               with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                        Write (^"x"): Bool <- #y;
                                                        Retv )
                           }.
End mod_test.

Definition Registers := (map MERegister).

Definition Rules := (map MERule).

Definition Methods := (map MEMeth).

Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Definition nat_string
  (radix : nat) (* radix minus 2 *)
  (encoding : Vector.t string (S (S radix)))
  (n : nat)
  :  string
  := Fix_F
       (fun n => string)
       (fun n (F : forall r, r < n -> string)
         => let digit_string
              := Vector.nth encoding
                   (of_nat_lt
                     (Nat.mod_upper_bound n (S (S radix)) (Nat.neq_succ_0 (S radix)))) in
            nat_rec
              (fun q => q = Nat.div n (S (S radix)) -> string)
              (fun _ => digit_string)
              (fun q _ (H : S q = Nat.div n (S (S radix)))
                => String.append
                     (F (S q)
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
                           (le_n_S 1 (S radix) (le_n_S 0 radix (Nat.le_0_l radix)))                           ) 
                         H))
                     digit_string)
              (Nat.div n (S (S radix)))
              eq_refl)%nat
       (lt_wf n).

Local Open Scope vector.
Local Open Scope string.

Local Definition binary_encoding
  :  Vector.t string 2
  := ["0"; "1"].

Local Definition decimal_encoding
  :  Vector.t string 10
  := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"].

Local Definition hex_encoding
  :  Vector.t string 16
  := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"].

Close Scope vector.

Definition nat_binary_string := nat_string binary_encoding.

Definition nat_decimal_string := nat_string decimal_encoding.

Definition nat_hex_string := nat_string hex_encoding.

Local Close Scope list.
