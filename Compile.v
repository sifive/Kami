Require Import Syntax Rtl Thread RecordUpdate.RecordSet.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope string.

Local Notation VarType := (list nat).
Local Notation NoneVal := (nil: VarType).
Local Notation InitVal := (0 :: nil: VarType).

Definition getRegActionRead a s := (a ++ "#" ++ s ++ "#_read", NoneVal).
Definition getRegActionWrite a s := (a ++ "#" ++ s ++ "#_tempwrite", NoneVal).
Definition getRegActionFinalWrite a s := (a ++ "#" ++ s ++ "#_write", NoneVal).
Definition getRegActionEn a s := (a ++ "#" ++ s ++ "#_en", NoneVal).

Definition getRegRead s := (s ++ "#_read", NoneVal).
Definition getRegWrite s := (s ++ "#_write", NoneVal).

Definition getMethActionArg a f := (a ++ "#" ++ f ++ "#_argument", NoneVal).
Definition getMethActionEn a f := (a ++ "#" ++ f ++ "#_enable", NoneVal).

Definition getMethRet f := (f ++ "#_return", NoneVal).
Definition getMethArg f := (f ++ "#_argument", NoneVal).
Definition getMethEn f := (f ++ "#_enable", NoneVal).
Definition getMethGuard f := (f ++ "#_guard", NoneVal).

Definition getActionGuard r := (r ++ "#_guard", NoneVal).
Definition getActionEn r := (r ++ "#_enable", NoneVal).

Local Close Scope string.

Section Compile.
  Variable name: string.

  Fixpoint convertExprToRtl k (e: Expr (fun _ => VarType) (SyntaxKind k)) :=
    match e in Expr _ (SyntaxKind k) return RtlExpr k with
      | Var k' x' =>   match k' return
                             (forall x,
                                match k' return (Expr (fun _ => VarType) k' -> Set) with
                                  | SyntaxKind k => fun _ => RtlExpr k
                                  | NativeKind _ => fun _ => IDProp
                                end (Var (fun _ => VarType) k' x))
                       with
                         | SyntaxKind k => fun x => RtlReadWire k (name, x)
                         | NativeKind t => fun _ => idProp
                       end x'
      | Const k x => RtlConst x
      | UniBool x x0 => RtlUniBool x (@convertExprToRtl _ x0)
      | CABool x x0 => RtlCABool x (map (@convertExprToRtl _) x0)
      | UniBit n1 n2 x x0 => RtlUniBit x (@convertExprToRtl _ x0)
      | CABit n x x0 => RtlCABit x (map (@convertExprToRtl _) x0)
      | BinBit n1 n2 n3 x x0 x1 => RtlBinBit x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | BinBitBool n1 n2 x x0 x1 => RtlBinBitBool x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | Eq k e1 e2 => RtlEq (@convertExprToRtl _ e1) (@convertExprToRtl _ e2)
      | ReadStruct n fk fs e i => @RtlReadStruct n fk fs (@convertExprToRtl _ e) i
      | BuildStruct n fk fs fv => @RtlBuildStruct n fk fs (fun i => @convertExprToRtl _ (fv i))
      | ReadArray n k arr idx => @RtlReadArray n k (@convertExprToRtl _ arr) (@convertExprToRtl _ idx)
      | ReadArrayConst n k arr idx => @RtlReadArrayConst n k (@convertExprToRtl _ arr) idx
      | BuildArray n k farr => @RtlBuildArray n k (fun i => @convertExprToRtl _ (farr i))
      | ITE k' x x0' x1' =>
        match k' return
              (forall x0 x1,
                 match k' return (Expr (fun _ => VarType) k' -> Set) with
                   | SyntaxKind k => fun _ => RtlExpr k
                   | NativeKind _ => fun _ => IDProp
                 end (ITE x x0 x1))
        with
          | SyntaxKind k => fun x0 x1 => RtlITE (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
          | NativeKind t => fun _ _ => idProp
        end x0' x1'
    end.

  Definition getRtlDisp (d: SysT (fun _ => VarType)) :=
    match d with
    | DispString s => RtlDispString s
    | DispBool e f => RtlDispBool (@convertExprToRtl _ e) f
    | DispBit n e f => RtlDispBit (@convertExprToRtl _ e) f
    | DispStruct n fk fs e f => RtlDispStruct (@convertExprToRtl _ e) f
    | DispArray n k e f => RtlDispArray (@convertExprToRtl _ e) f
    | Finish => RtlFinish
    end.

  Local Definition inc ns := match ns with
                             | nil => nil
                             | x :: xs => S x :: xs
                             end.

  Axiom cheat: forall t, t.

  Record RtlExprs := { tempWires : list (string * VarType * sigT RtlExpr) ;
                       regsWrite : string -> forall k, option (RtlExpr Bool * RtlExpr k) ;
                       methCalls : string -> forall k, option (RtlExpr Bool * RtlExpr k) ;
                       systCalls : list (RtlExpr Bool * list RtlSysT) ;
                       guard : option (RtlExpr Bool) }.

  Definition defRtlExprs := {| tempWires := nil ;
                               regsWrite := fun _ k => None ;
                               methCalls := fun _ k => None ;
                               systCalls := nil ;
                               guard := None |}.

  Local Open Scope rtl_expr.

  Definition combineRtlExprPreds k p1 (e1: option (_ * RtlExpr k)) p2 e2 :=
    match e1, e2 with
    | None, None => None
    | None, Some (x, v) => Some (p2 && x, v)
    | Some (x, v), None => Some (p1 && x, v)
    | Some (x1, v1), Some (x2, v2) => Some (p1 && x1 || p2 && x2, RtlITE (p1 && x1) v1 v2)
    end.
  
  Definition combineRtlExpr k (e1: option (_ * RtlExpr k)) e2 :=
    match e1, e2 with
    | None, None => None
    | None, Some (x, v) => Some (x, v)
    | Some (x, v), None => Some (x, v)
    | Some (x1, v1), Some (x2, v2) => Some (x1 || x2, RtlITE x1 v1 v2)
    end.
  
  Definition combineRtlExprsPreds p1 e1 p2 e2 := {| tempWires := tempWires e1 ++ tempWires e2 ;
                                                    regsWrite := fun s k => combineRtlExprPreds p1 (regsWrite e1 s k) p2 (regsWrite e2 s k) ;
                                                    methCalls := fun s k => combineRtlExprPreds p1 (methCalls e1 s k) p2 (methCalls e2 s k) ;
                                                    systCalls := map (fun x => (p1 && fst x, snd x)) (systCalls e1) ++
                                                                     map (fun x => (p2 && fst x, snd x)) (systCalls e2) ;
                                                    guard := match guard e1, guard e2 with
                                                             | None, None => Some (p1 || p2)
                                                             | Some x, None => Some ((p1 && x) || p2)
                                                             | None, Some x => Some (x || (p2 && x))
                                                             | Some x1, Some x2 => Some ((p1 && x1) || (p2 && x2))
                                                             end |}.
  
  Definition combineRtlExprs e1 e2 := {| tempWires := tempWires e1 ++ tempWires e2 ;
                                         regsWrite := fun s k => combineRtlExpr (regsWrite e1 s k) (regsWrite e2 s k) ;
                                         methCalls := fun s k => combineRtlExpr (methCalls e1 s k) (methCalls e2 s k) ;
                                         systCalls := systCalls e1 ++ systCalls e2 ;
                                         guard := match guard e1, guard e2 with
                                                  | None, None => None
                                                  | Some x, None => Some x
                                                  | None, Some x => Some x
                                                  | Some x1, Some x2 => Some (x1 && x2)
                                                  end |}.

  Import ApplicativeNotations.
  Global Instance etaX_RtlExprs : Settable _ :=
    mkSettable
      (constructor Build_RtlExprs
                   <*> tempWires <*> regsWrite <*> methCalls <*> systCalls <*> guard)%set.

  Local Notation "x [ proj  :=  v ]" := (set proj (constructor v) x)
                                      (at level 14, left associativity).
  Local Notation "x [ proj  :==  f ]" := (set proj f x)
                                       (at level 14, f at next level, left associativity).

  Local Notation add proj rec val := (rec [ proj :== (cons val) ]).

  Fixpoint convertActionToRtl k (a: ActionT (fun _ => VarType) k) (retVar: VarType) : State VarType RtlExprs :=
    match a in ActionT _ _ with
    | MCall meth argRetK argExpr cont =>
      (do curr <- get ;
         do _ <- put (inc curr) ;
         do final <- convertActionToRtl (cont curr) retVar ;
         ret (final[ tempWires := (name, curr, existT _ _ (RtlReadWire (snd argRetK) (getMethRet meth))) :: tempWires final ]
                   [ methCalls := fun s k' => match string_dec meth s with
                                              | left _ => match Kind_dec (fst argRetK) k' with
                                                          | left pf_k => Some (RtlReadWire Bool (getActionGuard name),
                                                                               match pf_k in _ = Y return _ Y with
                                                                               | eq_refl => convertExprToRtl argExpr
                                                                               end)
                                                          | _ => methCalls final s k'
                                                          end
                                              | _ => methCalls final s k'
                                              end]))
    | Return x => ret (add tempWires defRtlExprs (name, retVar, existT _ k (convertExprToRtl x)))
    | LetExpr k' expr cont =>
      match k' return Expr (fun _ => VarType) k' ->
                      (fullType (fun _ => VarType) k' -> ActionT (fun _ => VarType) k) ->
                      State VarType RtlExprs with
      | SyntaxKind k => fun expr cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont curr) retVar ;
                             ret (add tempWires final (name, curr, existT _ _ (convertExprToRtl expr))))
      | _ => fun _ _ => ret defRtlExprs
      end expr cont
    | LetAction k' a' cont =>
      (do curr <- get ;
         do _ <- put (inc curr) ;
         do final1 <- convertActionToRtl a' curr ;
         do final2 <- convertActionToRtl (cont curr) retVar ;
         ret (combineRtlExprs final1 final2))
    | ReadNondet k' cont =>
      match k' return (fullType (fun _ => VarType) k' -> ActionT (fun _ => VarType) k) ->
                      State VarType RtlExprs with
      | SyntaxKind k => fun cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont curr) retVar ;
                             ret (add tempWires final (name, curr, existT _ _ (RtlConst (getDefaultConst k)))))
      | _ => fun _ => ret defRtlExprs
      end cont
    | ReadReg r k' cont =>
      match k' return (fullType (fun _ => VarType) k' -> ActionT (fun _ => VarType) k) ->
                      State VarType RtlExprs with
      | SyntaxKind k => fun cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont curr) retVar ;
                             ret (add tempWires final (name, curr, existT _ _ (RtlReadWire k (getRegActionRead name r)))))
      | _ => fun _ => ret defRtlExprs
      end cont
    | WriteReg r k' expr cont =>
      match k' return Expr (fun _ => VarType) k' -> State VarType RtlExprs with
      | SyntaxKind k =>
        fun expr =>
          (do final <- convertActionToRtl cont retVar ;
             ret (final[ regsWrite :=
                           fun s k'' =>
                             match string_dec r s with
                             | left _ => match Kind_dec k k'' with
                                         | left pf_k => Some (RtlReadWire Bool (getActionGuard name), match pf_k in _ = Y return _ Y with
                                                                                                      | eq_refl => convertExprToRtl expr
                                                                                                      end)
                                         | _ => regsWrite final s k''
                                         end
                             | _ => regsWrite final s k''
                             end]))
      | _ => fun _ => ret defRtlExprs
      end expr
    | Assertion pred cont =>
      (do final <- convertActionToRtl cont retVar ;
         let p := convertExprToRtl pred in
         ret (final[ guard := (match guard final with
                               | None => Some p
                               | Some v => Some (p && v)%rtl_expr
                               end)]))
    | Sys ls cont =>
      (do final <- convertActionToRtl cont retVar ;
         ret (add systCalls final (RtlReadWire Bool (getActionGuard name), map getRtlDisp ls)))
    | IfElse pred ktf t f cont =>
      (do init <- get ;
         let predWire := RtlReadWire Bool (name, init) in
         do _ <- put (inc init) ;
         do currT <- get ;
         do _ <- put (inc currT) ;
         do finalT <- convertActionToRtl t currT ;
         do currF <- get ;
         do _ <- put (inc currF) ;
         do finalF <- convertActionToRtl f currF ;
         do curr <- get ;
         do _ <- put (inc curr) ;
         do final <- convertActionToRtl (cont curr) retVar ;
         let combTF := combineRtlExprsPreds predWire finalT
                                            (RtlUniBool Neg predWire) finalF in
         let combCont := combineRtlExprs combTF final in
         let addCurr := add tempWires combCont (name, curr, existT _ _ (RtlITE predWire
                                                                               (RtlReadWire ktf (name, currT))
                                                                               (RtlReadWire ktf (name, currF)))) in
         ret (add tempWires addCurr (name, init, existT _ _ (convertExprToRtl pred))))
    end.
End Compile.

Section PerRule.
  Variable rule: Attribute (Action Void).

  Record RuleOutput :=
    { ruleTemps: list (string * VarType * sigT RtlExpr) ;
      ruleSysCs: list (RtlExpr Bool * list RtlSysT) }.
  
  Definition getRtlExprsForRule :=
    fst (run (convertActionToRtl (fst rule) (snd rule (fun _ => VarType)) InitVal)
             (inc InitVal)).

  Definition getTempWiresForRule (regs: list (Attribute Kind))
             (calls: list (Attribute (Kind * Kind))) :=
    let '(Build_RtlExprs tw rw mc sc g) := getRtlExprsForRule in
    {| ruleTemps := (getActionGuard (fst rule), existT _ Bool match g with
                                                              | Some g' => g'
                                                              | None => RtlConst true
                                                              end)
                      ::
                      tw ++ (map (fun sk => let '(s, k) := sk in
                                            (getRegActionEn (fst rule) s, existT _ Bool
                                                                                 match rw s k with
                                                                                 | Some (pred, val) => pred
                                                                                 | None => RtlConst false
                                                                                 end)) regs)
                      ++ (map (fun sk => let '(s, k) := sk in
                                         (getRegActionWrite (fst rule) s, existT _ k
                                                                                 match rw s k with
                                                                                 | Some (pred, val) => val
                                                                                 | None => RtlConst (getDefaultConst k)
                                                                                 end)) regs)
                      ++ (map (fun sk => let '(s, (argK, retK)) := sk in
                                         (getMethEn s, existT _ Bool
                                                              match mc s argK with
                                                              | Some (pred, val) => pred
                                                              | None => RtlConst false
                                                              end)) calls)
                      ++ (map (fun sk => let '(s, (argK, retK)) := sk in
                                         (getMethArg s, existT _ argK
                                                               match mc s argK with
                                                               | Some (pred, val) => val
                                                               | None => RtlConst (getDefaultConst argK)
                                                               end)) calls) ;
       ruleSysCs := map (fun v => let '(pred, val) := v in
                                  (pred, val)%rtl_expr) sc |}.
End PerRule.

Section AllRules.
  Variable rules: list (Attribute (Action Void)).
  Variable regs: list (Attribute Kind).
  Variable calls: list (Attribute (Kind * Kind)).

  Definition combineRules :=
    fold_left (fun acc rule => {| ruleTemps := ruleTemps acc ++ ruleTemps (getTempWiresForRule rule regs calls) ;
                                  ruleSysCs := ruleSysCs acc ++ ruleSysCs (getTempWiresForRule rule regs calls) |})
              rules {| ruleTemps := nil ;
                       ruleSysCs := nil |}.
End AllRules.

Section ThreadRules.
  Variable rules: list (Attribute (Action Void)).
  Variable regs: list (Attribute Kind).
  Variable calls: list (Attribute (Kind * Kind)).

  Definition getRuleWrite rule (x: Attribute Kind) :=
    existT _ (snd x) (RtlITE (RtlReadWire Bool (getRegActionEn rule (fst x)))
                             (RtlReadWire (snd x) (getRegActionWrite rule (fst x)))
                             (RtlReadWire (snd x) (getRegActionRead rule (fst x)))).
  
  Definition threadTogether curr next : list (string * VarType * sigT RtlExpr) :=
    map (fun x => (getRegActionRead next (fst x), getRuleWrite curr x)) regs.

  Fixpoint threadAllTemps (order: list string) {struct order} :=
    match order with
    | x :: xs => match xs with
                 | y :: ys => threadTogether x y
                 | nil => nil
                 end ++ threadAllTemps xs
    | _ => nil
    end.

  Definition finalWrite (order: list string) :=
    map (fun x => (fst x, getRuleWrite (last order ""%string) x)) regs.

  Definition initialRead (order: list string) :=
    map (fun x => (getRegActionRead (hd ""%string order) (fst x), existT _ _ (RtlReadReg (snd x) (fst x)))) regs.

  Definition allWires order :=
    ({| ruleTemps := threadAllTemps order ++ initialRead order ++ ruleTemps (combineRules rules regs calls) ;
        ruleSysCs := ruleSysCs (combineRules rules regs calls) |},
     finalWrite order).
End ThreadRules.

Definition getRegInit (y: sigT RegInitValT): {x: Kind & option (ConstT x)} :=
  existT _ _
         match projT2 y with
         | Uninit => None
         | Init y' => Some match y' in ConstFullT k return ConstT match k with
                                                                  | SyntaxKind k' => k'
                                                                  | _ => Void
                                                                  end with
                           | SyntaxConst k c => c
                           | _ => WO
                           end
         | RegFileUninit num k pf => None
         | RegFileInit num k pf val =>
           Some
             match eq_sym pf in _ = Y return ConstT match Y with
                                                    | SyntaxKind k' => k'
                                                    | NativeKind _ => Void
                                                    end with
             | eq_refl => ConstArray (fun _ => val)
             end
             
         | RegFileHex num k pf file => None
         | RegFileBin num k pf file => None
         end.

Definition rtlModCreate (bm: list string * (list RegFileBase * BaseModule))
           (order: list string) :=
  let '(hides, (rfs, m)) := bm in
  let rules := getRules m in
  let regs := map (fun x => let '(a, b) := x in
                            (a, match b with
                                | SyntaxKind k => k
                                | _ => Bit 0
                                end)) (getKindAttr (getRegisters m)) in
  let calls := getCallsWithSignPerMod m in
  let '(Build_RuleOutput temps syss, regWr) := allWires rules regs calls order in
  let ins := map (fun x => (getMethRet (fst x), (snd (snd x)))) calls in
  let outs := map (fun x => (getMethArg (fst x), (fst (snd x)))) calls ++ map (fun x => (getMethEn (fst x), Bool)) calls in
  {| hiddenWires := map (fun x => getMethArg x) hides ++
                        map (fun x => getMethEn x) hides ++
                        map (fun x => getMethRet x) hides ;
     regFiles := map (fun x => (false, x)) rfs ;
     inputs := ins ;
     outputs := outs ;
     regInits :=  map (fun x => (fst x, getRtlRegInit (snd x))) (getRegisters m) ;
     regWrites := regWr ;
     wires := temps ;
     sys := syss |}.

Definition getRtl (bm: (list string * (list RegFileBase * BaseModule))) :=
  rtlModCreate bm (map fst (getRules (snd (snd bm)))).

Definition rtlGet m :=
  getRtl (getHidden m, (fst (separateBaseMod m), inlineAll_All_mod (mergeSeparatedBaseMod (snd (separateBaseMod m))))).

Definition makeRtl (m: ModWfOrd) := rtlGet m.
