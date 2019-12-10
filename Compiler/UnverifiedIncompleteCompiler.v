Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv.
Require Import Kami.Syntax Kami.Notations RecordUpdate.RecordSet Kami.Compiler.Rtl Kami.StateMonad.


Set Implicit Arguments.
Set Asymmetric Patterns.

Local Notation NoneVal := (None: option nat).

Local Open Scope string.

Definition getRegActionRead a s := (a ++ "#" ++ s ++ "#_read", NoneVal).
Definition getRegActionWrite a s := (a ++ "#" ++ s ++ "#_tempwrite", NoneVal).
Definition getRegActionEn a s := (a ++ "#" ++ s ++ "#_en", NoneVal).

Definition getMethRet f := (f ++ "#_return", NoneVal).
Definition getMethArg f := (f ++ "#_argument", NoneVal).
Definition getMethEn f := (f ++ "#_enable", NoneVal).

Definition getActionGuard r := (r ++ "#_guard", NoneVal).

Local Close Scope string.
Definition RtlReadWire k s := @Var rtl_ty (SyntaxKind k) s.
Definition RtlReadReg k s := @Var rtl_ty (SyntaxKind k) (s, None).
Arguments RtlReadWire: clear implicits.
  

Section Compile.
  Variable name: string.

  Fixpoint convertExprToRtl k (e: RtlExpr (SyntaxKind k)) := e.

  Definition getRtlDisp (d: RtlSysT) := d.

  Local Notation inc ns := (S ns).

  Record RtlExprs := { tempWires : list (string * option nat * sigT RtlExpr') ;
                       regsWrite : string -> forall k, option (RtlExpr' Bool * RtlExpr' k) ;
                       methCalls : string -> forall k, option (RtlExpr' Bool * RtlExpr' k) ;
                       systCalls : list (RtlExpr' Bool * list RtlSysT) ;
                       guard : option (RtlExpr' Bool) }.

  Definition defRtlExprs := {| tempWires := nil ;
                               regsWrite := fun _ k => None ;
                               methCalls := fun _ k => None ;
                               systCalls := nil ;
                               guard := None |}.

  Local Open Scope kami_expr.

  Definition combineRtlExprPreds k p (e1: option (_ * RtlExpr k)) e2 :=
    match e1, e2 with
    | None, None => None
    | None, Some (x, v) => Some ((UniBool Neg p) && x, v)
    | Some (x, v), None => Some (p && x, v)
    | Some (x1, v1), Some (x2, v2) => Some (ITE p x1 x2, ITE (p && x1) v1 v2)
    end.
  
  Definition combineRtlExpr k (e1: option (_ * RtlExpr k)) e2 :=
    match e1, e2 with
    | None, None => None
    | None, Some (x, v) => Some (x, v)
    | Some (x, v), None => Some (x, v)
    | Some (x1, v1), Some (x2, v2) => Some (x1 || x2, ITE x1 v1 v2)
    end.
  
  Definition combineRtlExprsPreds p e1 e2 := {| tempWires := tempWires e1 ++ tempWires e2 ;
                                                regsWrite := fun s k => combineRtlExprPreds p (regsWrite e1 s k) (regsWrite e2 s k) ;
                                                methCalls := fun s k => combineRtlExprPreds p (methCalls e1 s k) (methCalls e2 s k) ;
                                                systCalls := map (fun x => (p && fst x, snd x)) (systCalls e1) ++
                                                                 map (fun x => ((UniBool Neg p) && fst x, snd x)) (systCalls e2) ;
                                                guard := match guard e1, guard e2 with
                                                         | None, None => None
                                                         | Some x, None => Some (x || (UniBool Neg p))
                                                         | None, Some x => Some (x || p)
                                                         | Some x1, Some x2 => Some (ITE p x1 x2)
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

  Global Instance etaX_RtlExprs : Settable _ :=
    settable!
      Build_RtlExprs
                   <tempWires ; regsWrite ; methCalls ; systCalls ; guard>.

  Local Notation add proj rec val := (rec <| proj ::== (cons val) |>).
  Definition getTemp num := (name, Some num : option nat).

  Fixpoint convertActionToRtl k (a: ActionT rtl_ty k) (retVar: nat) : State nat RtlExprs :=
    match a in ActionT _ _ with
    | MCall meth argRetK argExpr cont =>
      (do curr <- get ;
         do _ <- put (inc curr) ;
         do final <- convertActionToRtl (cont (getTemp curr)) retVar ;
         ret (final<| tempWires := (name, Some curr, existT _ _ (RtlReadWire (snd argRetK) (getMethRet meth))) :: tempWires final |>
                   <| methCalls := fun s k' => match string_dec meth s with
                                               | left _ => match Kind_dec (fst argRetK) k' with
                                                           | left pf_k => Some (RtlReadWire Bool (getActionGuard name),
                                                                                match pf_k in _ = Y return _ Y with
                                                                                | eq_refl => convertExprToRtl argExpr
                                                                                end)
                                                           | _ => methCalls final s k'
                                                           end
                                               | _ => methCalls final s k'
                                               end |>))
    | Return x => ret (add tempWires defRtlExprs (name, Some retVar, existT _ k (convertExprToRtl x)))
    | LetExpr k' expr cont =>
      match k' return Expr rtl_ty k' ->
                      (fullType rtl_ty k' -> ActionT rtl_ty k) ->
                      State nat RtlExprs with
      | SyntaxKind k => fun expr cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont (getTemp curr)) retVar ;
                             ret (add tempWires final (name, Some curr, existT _ k (convertExprToRtl expr))))
      | _ => fun _ _ => ret defRtlExprs
      end expr cont
    | LetAction k' a' cont =>
      (do curr <- get ;
         do _ <- put (inc curr) ;
         do final1 <- convertActionToRtl a' curr ;
         do final2 <- convertActionToRtl (cont (getTemp curr)) retVar ;
         ret (combineRtlExprs final1 final2))
    | ReadNondet k' cont =>
      match k' return (fullType rtl_ty k' -> ActionT rtl_ty k) ->
                      State nat RtlExprs with
      | SyntaxKind k => fun cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont (getTemp curr)) retVar ;
                             ret (add tempWires final (name, Some curr, existT _ k (Const _ (getDefaultConst k)))))
      | _ => fun _ => ret defRtlExprs
      end cont
    | ReadReg r k' cont =>
      match k' return (fullType rtl_ty k' -> ActionT rtl_ty k) ->
                      State nat RtlExprs with
      | SyntaxKind k => fun cont =>
                          (do curr <- get ;
                             do _ <- put (inc curr) ;
                             do final <- convertActionToRtl (cont (getTemp curr)) retVar ;
                             ret (add tempWires final (name, Some curr, existT _ _ (RtlReadWire k (getRegActionRead name r)))))
      | _ => fun _ => ret defRtlExprs
      end cont
    | WriteReg r k' expr cont =>
      match k' return Expr rtl_ty k' -> State nat RtlExprs with
      | SyntaxKind k =>
        fun expr =>
          (do final <- convertActionToRtl cont retVar ;
             ret (final<| regsWrite :=
                           fun s k'' =>
                             match string_dec r s with
                             | left _ => match Kind_dec k k'' with
                                         | left pf_k => Some (RtlReadWire Bool (getActionGuard name), match pf_k in _ = Y return _ Y with
                                                                                                      | eq_refl => convertExprToRtl expr
                                                                                                      end)
                                         | _ => regsWrite final s k''
                                         end
                             | _ => regsWrite final s k''
                             end |>))
      | _ => fun _ => ret defRtlExprs
      end expr
    | Sys ls cont =>
      (do final <- convertActionToRtl cont retVar ;
         ret (add systCalls final (RtlReadWire Bool (getActionGuard name), map getRtlDisp ls)))
    | IfElse pred ktf t f cont =>
      (do init <- get ;
         let predWire := RtlReadWire Bool (name, Some init) in
         do _ <- put (inc init) ;
         do currT <- get ;
         do _ <- put (inc currT) ;
         do finalT <- convertActionToRtl t currT ;
         do currF <- get ;
         do _ <- put (inc currF) ;
         do finalF <- convertActionToRtl f currF ;
         do curr <- get ;
         do _ <- put (inc curr) ;
         do final <- convertActionToRtl (cont (getTemp curr)) retVar ;
         let combTF := combineRtlExprsPreds predWire finalT finalF in
         let combCont := combineRtlExprs combTF final in
         let addCurr := add tempWires combCont (name, Some curr, existT _ _ (ITE predWire
                                                                               (RtlReadWire ktf (name, Some currT))
                                                                               (RtlReadWire ktf (name, Some currF)))) in
         ret (add tempWires addCurr (name, Some init, existT _ Bool (convertExprToRtl pred))))
    end.
End Compile.

Section PerRule.
  Variable rule: Attribute (Action Void).

  Local Definition calls := getCallsWithSignPerRule rule.

  Record RuleOutput :=
    { ruleTemps: list (string * option nat * sigT RtlExpr') ;
      ruleSysCs: list (RtlExpr' Bool * list RtlSysT) }.
  
  Definition getRtlExprsForRule :=
    fst (run (convertActionToRtl (fst rule) (snd rule rtl_ty) 0)
             1).

  Definition getTempWiresForRule (regs: list (Attribute Kind)) :=
    let '(Build_RtlExprs tw rw mc sc g) := getRtlExprsForRule in
    {| ruleTemps := (getActionGuard (fst rule), existT _ Bool match g with
                                                              | Some g' => g'
                                                              | None => Const _ true
                                                              end)
                      ::
                      tw ++ (map (fun sk => let '(s, k) := sk in
                                            (getRegActionEn (fst rule) s, existT _ Bool
                                                                                 match rw s k with
                                                                                 | Some (pred, val) => pred
                                                                                 | None => Const _ false
                                                                                 end)) regs)
                      ++ (map (fun sk => let '(s, k) := sk in
                                         (getRegActionWrite (fst rule) s, existT _ k
                                                                                 match rw s k with
                                                                                 | Some (pred, val) => val
                                                                                 | None => Const _ (getDefaultConst k)
                                                                                 end)) regs)
                      ++ (map (fun sk => let '(s, (argK, retK)) := sk in
                                         (getMethEn s, existT _ Bool
                                                              match mc s argK with
                                                              | Some (pred, val) => pred
                                                              | None => Const _ false
                                                              end)) calls)
                      ++ (map (fun sk => let '(s, (argK, retK)) := sk in
                                         (getMethArg s, existT _ argK
                                                               match mc s argK with
                                                               | Some (pred, val) => val
                                                               | None => Const _ (getDefaultConst argK)
                                                               end)) calls) ;
       ruleSysCs := map (fun v => let '(pred, val) := v in
                                  (pred, val)%kami_expr) sc |}.
End PerRule.

Section AllRules.
  Variable rules: list (Attribute (Action Void)).
  Variable regs: list (Attribute Kind).

  Definition combineRules :=
    fold_left (fun acc rule => {| ruleTemps := ruleTemps acc ++ ruleTemps (getTempWiresForRule rule regs) ;
                                  ruleSysCs := ruleSysCs acc ++ ruleSysCs (getTempWiresForRule rule regs) |})
              rules {| ruleTemps := nil ;
                       ruleSysCs := nil |}.
End AllRules.

Section ThreadRules.
  Variable rules: list (Attribute (Action Void)).
  Variable regs: list (Attribute Kind).

  Definition getRuleWrite rule (x: Attribute Kind) :=
    existT RtlExpr' (snd x) (ITE (RtlReadWire Bool (getRegActionEn rule (fst x)))
                             (RtlReadWire (snd x) (getRegActionWrite rule (fst x)))
                             (RtlReadWire (snd x) (getRegActionRead rule (fst x)))).
  
  Definition threadTogether curr next : list (string * option nat * sigT RtlExpr') :=
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
    map (fun x => (getRegActionRead (hd ""%string order) (fst x), existT RtlExpr' _ (RtlReadReg (snd x) (fst x)))) regs.

  Definition allWires order :=
    ({| ruleTemps := threadAllTemps order ++ initialRead order ++ ruleTemps (combineRules rules regs) ;
        ruleSysCs := ruleSysCs (combineRules rules regs) |},
     finalWrite order).
End ThreadRules.

Definition getRegInit (y: sigT RegInitValT): {x: Kind & option (ConstT x)} :=
  existT _ _
         match projT2 y with
         | None => None
         | Some y' =>
           Some match y' in ConstFullT k return ConstT match k with
                                                       | SyntaxKind k' => k'
                                                       | _ => Void
                                                       end with
                | SyntaxConst k c => c
                | _ => (zToWord 0 0)
                end
         end.

(* tagged database entry definitions *)
Fixpoint tag' val T (xs : list T) :=
  match xs with
  | nil => nil
  | y :: ys => (val, y) :: tag' (S val) ys
  end.

Definition tag := @tag' 0.

Section order.
  Variable rules: list RuleT.
  Variable order: list string.

  Definition callingRule m := find (fun calls => getBool (In_dec string_dec m (snd calls)))
                                   (map (fun x => (fst x, map fst (getCallsWithSignPerRule x))) rules).

  Definition getPosCallingRule m :=
    match callingRule m with
    | Some (x, _) =>
      match find (fun z => getBool (string_dec x (snd z))) (tag order) with
      | Some (pos, _) => Some pos
      | None => None
      end
    | None => None
    end.

  Definition isBeforeCall m1 m2 :=
    match getPosCallingRule m1, getPosCallingRule m2 with
    | Some x, Some y => getBool (Compare_dec.lt_dec x y)
    | _, _ => false
    end.

End order.

Definition convertRtl (e : {x : Kind & RtlExpr' x}) : {x : FullKind & RtlExpr x} :=
  match e with
  | existT x val => existT _ (SyntaxKind x) val
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
  let '(Build_RuleOutput temps syss, regWr) := allWires rules regs order in
  let ins := map (fun x => (getMethRet (fst x), (snd (snd x)))) calls in
  let outs := map (fun x => (getMethArg (fst x), (fst (snd x)))) calls ++
                  map (fun x => (getMethEn (fst x), Bool)) calls in
  {| hiddenWires := map (fun x => getMethArg x) hides ++
                        map (fun x => getMethEn x) hides ++
                        map (fun x => getMethRet x) hides ;
     regFiles := rfs ;
     inputs := ins ;
     outputs := outs;
     regInits := map (fun '(x,y) => (x, None, y)) (getRegisters m) ;
     regWrites := map (fun '(x,y) => (x, None, convertRtl y)) regWr ;
     wires := map (fun '(x,y,z) => (x, y, convertRtl z)) temps ;
     sys := syss |}.

Definition getRtl (bm: (list string * (list RegFileBase * BaseModule))) :=
  rtlModCreate bm (map fst (getRules (snd (snd bm)))).

Definition getRtlSafe
           (module : Mod)
  :  RtlModule
  := getRtl (separateModRemove module).

Definition rtlGet m :=
  getRtl (getHidden m, (fst (separateBaseMod m), inlineAll_All_mod (mergeSeparatedBaseMod (snd (separateBaseMod m))))).

Definition makeRtl (m: ModWfOrd) := rtlGet m.
