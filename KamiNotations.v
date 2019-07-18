Require Export Syntax.
Require Import RecordUpdate.RecordSet.

(* Notation for normal mods *)

  Inductive ModuleElt :=
  | MERegister (_ : RegInitT)
  | MERegAry (_ : list RegInitT)
  | MERule (_ : Attribute (Action Void))
  | MEMeth (_ : DefMethT).

  Inductive InModule :=
  | NilInModule
  | ConsInModule (_ : ModuleElt) (_ : InModule).

  Fixpoint makeModule' (im : InModule) :=
    match im with
    | NilInModule => (nil, nil, nil)
    | ConsInModule e i =>
      let '(iregs, irules, imeths) := makeModule' i in
      match e with
      | MERegister mreg => (mreg :: iregs, irules, imeths)
      | MERegAry mregs => (mregs ++ iregs, irules, imeths)
      | MERule mrule => (iregs, mrule :: irules, imeths)
      | MEMeth mmeth => (iregs, irules, mmeth :: imeths)
      end
    end.

  Definition makeModule (im : InModule) :=
    let '(regs, rules, meths) := makeModule' im in
    BaseMod regs rules meths.

  Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

  Fixpoint getOrder (im : InModule) :=
    match im with
    | NilInModule => nil
    | ConsInModule e i =>
      let rest := getOrder i in
      match e with
      | MERule mrule => fst mrule :: rest
      | MEMeth mmeth => fst mmeth :: rest
      | _ => rest
      end
    end.
  
  (** Notations for Struct **)

  Delimit Scope kami_expr_scope with kami_expr.

  Notation "name :: ty" := (name%string,  ty) (only parsing) : kami_struct_scope.
  Delimit Scope kami_struct_scope with kami_struct.

  (** Notations for expressions *)

  Notation "k @# ty" := (Expr ty (SyntaxKind k)) (no associativity, at level 98, only parsing).

  Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (at level 0, only parsing) : kami_expr_scope. 
  Notation "$ n" := (Const _ (of_nat _ n)) (at level 9) : kami_expr_scope.
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
    ((BinBit (Concat _ _)) a .. (BinBit (Concat _ _) b (@Const _ (Bit 0) (of_nat 0 0))) ..)
      (at level 100, a at level 99): kami_expr_scope.
  Notation "{< a , .. , b >}" :=
    (concat b .. (concat a (of_nat 0 0)) ..)
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

  Notation "name ::= value" :=
    (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (snd a)))
            (name%string, _) value) (at level 50) : kami_struct_init_scope.
  Delimit Scope kami_struct_init_scope with struct_init.

  Notation "'STRUCT' { s1 ; .. ; sN }" :=
    (getStructVal (cons s1%struct_init ..
                        (cons sN%struct_init nil) ..))
    : kami_expr_scope.

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
                      (Return (Const ty (of_nat 0 0))))) namesVals.

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

  Notation "'WriteToList' names 'of' k 'using' vals ; cont" :=
    (gatherActions (@writeNames _ k (List.combine names vals)) (fun _ => cont))
      (at level 13, right associativity, vals at level 99) : kami_action_scope.
  Delimit Scope kami_init_scope with kami_init.

  Notation "'ARRAY' { x1 ; .. ; xn }" :=
    (BuildArray (nth_Fin (cons x1%kami_init .. (cons xn%kami_init nil) ..)))
    : kami_expr_scope.

  Notation "name ::= value" :=
    (existT (fun a : Attribute Kind => ConstT (snd a))
            (name%string, _) value) (at level 50) : kami_struct_initial_scope.
  Delimit Scope kami_struct_initial_scope with struct_initial.

  Delimit Scope kami_scope with kami.

  Notation "'RegisterN' name : type <- init" :=
    (MERegister (name%string, existT RegInitValT type (Some ((NativeConst init)%kami_init))))
      (at level 13, name at level 99) : kami_scope.

  Notation "'Register' name : type <- init" :=
    (MERegister (name%string, existT RegInitValT (SyntaxKind type) (Some (makeConst ((init)%kami_init)))))
      (at level 13, name at level 99) : kami_scope.

  Notation "'RegisterU' name : type" :=
    (MERegister (name%string, existT RegInitValT (SyntaxKind type) None))
      (at level 13, name at level 99) : kami_scope.

  Notation "'Method' name () : retT := c" :=
    (MEMeth (name%string, existT MethodT (Void, retT)
                                 (fun ty (_: ty Void) => c%kami_action : ActionT ty retT)))
      (at level 13, name at level 9) : kami_scope.

  Notation "'Method' name ( param : dom ) : retT := c" :=
    (MEMeth (name%string, existT MethodT (dom, retT)
                                 (fun ty (param : ty dom) => c%kami_action : ActionT ty retT)))
      (at level 13, name at level 9, param at level 99) : kami_scope.

  Notation "'Rule' name := c" :=
    (MERule (name%string, fun ty => (c)%kami_action : ActionT ty Void))
      (at level 13) : kami_scope.

  Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
    (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..))
      (only parsing).


  Notation "'MODULE_WF' { m1 'with' .. 'with' mN }" :=
    {| baseModuleWf := {| baseModule := makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..) ;
                          wfBaseModule := ltac:(discharge_wf) |} ;
       baseModuleOrd := getOrder (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..) |}
      (only parsing).

  Notation "'MOD_WF' { m1 'with' .. 'with' mN }" :=
    {| modWf := {| module := Base (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..)) ;
                   wfMod := ltac:(discharge_wf) |} ;
       modOrd := getOrder (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..) |}
      (only parsing).

  Notation "'RegisterVec' name 'using' nums : type <- init" :=
    (MERegAry (
         map (fun idx =>
                (AddIndexToName name idx, existT RegInitValT (SyntaxKind type) (Some (makeConst (init)%kami_init)))
             ) nums
    ))
      (at level 13, name at level 9, nums at level 9) : kami_scope.



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
