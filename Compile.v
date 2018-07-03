Require Import Syntax Rtl.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.

Local Notation nil_nat := (nil: list nat).

Definition getRegActionRead a s := (a ++ "#" ++ s ++ "#_read", nil_nat).
Definition getRegActionWrite a s := (a ++ "#" ++ s ++ "#_tempwrite", nil_nat).
Definition getRegActionFinalWrite a s := (a ++ "#" ++ s ++ "#_write", nil_nat).
Definition getRegActionEn a s := (a ++ "#" ++ s ++ "#_en", nil_nat).

Definition getRegRead s := (s ++ "#_read", nil_nat).
Definition getRegWrite s := (s ++ "#_write", nil_nat).

Definition getMethActionArg a f := (a ++ "#" ++ f ++ "#_argument", nil_nat).
Definition getMethActionEn a f := (a ++ "#" ++ f ++ "#_enable", nil_nat).

Definition getMethRet f := (f ++ "#_return", nil_nat).
Definition getMethArg f := (f ++ "#_argument", nil_nat).
Definition getMethEn f := (f ++ "#_enable", nil_nat).
Definition getMethGuard f := (f ++ "#_guard", nil_nat).

Definition getActionGuard r := (r ++ "#_guard", nil_nat).
Definition getActionEn r := (r ++ "#_enable", nil_nat).

Close Scope string.

Local Notation cast k' v := v.


Section Compile.
  Variable name: string.

  Fixpoint convertExprToRtl k (e: Expr (fun _ => list nat) (SyntaxKind k)) :=
    match e in Expr _ (SyntaxKind k) return RtlExpr k with
      | Var k' x' =>   match k' return
                             (forall x,
                                match k' return (Expr (fun _ => list nat) k' -> Set) with
                                  | SyntaxKind k => fun _ => RtlExpr k
                                  | NativeKind _ => fun _ => IDProp
                                end (Var (fun _ => list nat) k' x))
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
                 match k' return (Expr (fun _ => list nat) k' -> Set) with
                   | SyntaxKind k => fun _ => RtlExpr k
                   | NativeKind _ => fun _ => IDProp
                 end (ITE x x0 x1))
        with
          | SyntaxKind k => fun x0 x1 => RtlITE (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
          | NativeKind t => fun _ _ => idProp
        end x0' x1'
    end.

  Local Definition inc ns := match ns with
                             | nil => nil
                             | x :: xs => S x :: xs
                             end.

  Axiom cheat: forall t, t.

  Fixpoint convertActionToRtl_noGuard k (a: ActionT (fun _ => list nat) k) enable startList retList :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        (name, startList, existT _ (snd k) (RtlReadWire (snd k) (getMethRet meth))) ::
        convertActionToRtl_noGuard (cont startList) enable (inc startList) retList
      | Return x => (name, retList, existT _ k (convertExprToRtl x)) :: nil
      | LetExpr k' expr cont =>
        match k' return Expr (fun _ => list nat) k' ->
                        (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (string * list nat * sigT RtlExpr) with
        | SyntaxKind k => fun expr cont => (name, startList, existT _ k (convertExprToRtl expr))
                                             ::
                                             convertActionToRtl_noGuard (cont startList) enable (inc startList)
                                             retList
        | _ => fun _ _ => nil
        end expr cont
      | LetAction k' a' cont =>
        convertActionToRtl_noGuard a' enable (0 :: startList) startList ++
        convertActionToRtl_noGuard (cont startList) enable (inc startList) retList
      | ReadNondet k' cont =>
        match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (string * list nat * sigT RtlExpr) with
        | SyntaxKind k => fun cont => (name, startList, existT _ k (convertExprToRtl
                                                                      (Const _ (getDefaultConst _))))
                                        ::
                                        convertActionToRtl_noGuard (cont startList) enable (inc startList) retList
        | _ => fun _ => nil
        end cont
      | ReadReg r k' cont =>
        match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun cont => (name, startList,
                                         existT _ k (RtlReadWire k (getRegActionRead name r)))
                                          ::
                                          convertActionToRtl_noGuard (cont startList) enable
                                          (inc startList) retList
          | _ => fun _ => nil
        end cont
      | WriteReg r k' expr cont =>
        convertActionToRtl_noGuard cont enable startList retList
      | Assertion pred cont => convertActionToRtl_noGuard cont enable startList retList
      | Sys ls cont => convertActionToRtl_noGuard cont enable startList retList
      | IfElse pred ktf t f cont =>
        convertActionToRtl_noGuard t (RtlCABool And (enable :: (convertExprToRtl pred) :: nil)) (0 :: startList) (startList) ++
        convertActionToRtl_noGuard f
          (RtlCABool And (enable :: (RtlUniBool Neg (convertExprToRtl pred)) :: nil)) (0 :: inc startList) (inc startList) ++
          (name, inc (inc startList),
           existT _ ktf (RtlITE (convertExprToRtl pred) (RtlReadWire ktf (name, startList)) (RtlReadWire ktf (name, inc startList)))) ::
        convertActionToRtl_noGuard (cont (inc (inc startList))) enable (inc (inc (inc startList))) retList
        end.

  Fixpoint convertActionToRtl_guard k (a: ActionT (fun _ => list nat) k) startList:
    list (RtlExpr Bool) :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        RtlReadWire Bool (getActionGuard meth) ::
                    (convertActionToRtl_guard (cont startList) (inc startList))
      | LetExpr k' expr cont =>
        match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (RtlExpr Bool) with
        | SyntaxKind k => fun cont =>
                            convertActionToRtl_guard (cont startList) (inc startList)
        | _ => fun _ => nil
        end cont
      | ReadNondet k' cont =>
        match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (RtlExpr Bool) with
        | SyntaxKind k => fun cont =>
                            convertActionToRtl_guard (cont startList) (inc startList)
        | _ => fun _ => nil
        end cont
      | ReadReg r k' cont =>
        match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                        list (RtlExpr Bool) with
        | SyntaxKind k => fun cont =>
                            convertActionToRtl_guard (cont startList) (inc startList)
        | _ => fun _ => nil
        end cont
      | WriteReg r k' expr cont =>
        convertActionToRtl_guard cont startList
      | Assertion pred cont => convertExprToRtl pred ::
                                              (convertActionToRtl_guard cont startList)
      | Sys ls cont => convertActionToRtl_guard cont (inc startList)
      | Return x => RtlConst (ConstBool true) :: nil
      | IfElse pred ktf t f cont =>
        (RtlITE (convertExprToRtl pred) (RtlCABool And
                                                   (convertActionToRtl_guard t (0 :: startList)))
                (RtlCABool And (convertActionToRtl_guard f (0 :: inc startList))))
          ::
          (convertActionToRtl_guard (cont (inc (inc startList)))
                                    (inc (inc (inc startList))))
      | LetAction k' a' cont =>
        convertActionToRtl_guard a' (0 :: startList) ++
                                 convertActionToRtl_guard (cont startList) (inc startList)
    end.

  Definition convertActionToRtl_guardF k (a: ActionT (fun _ => list nat) k) startList :=
    RtlCABool And (convertActionToRtl_guard a startList).

  Definition invalidRtl (k: Kind) :=
    ((STRUCT {
          "valid" ::= RtlConst false ;
          "data" ::= RtlConst (getDefaultConst k)
     })%rtl_expr : RtlExpr (Maybe k)).


  Section MethReg.
    Open Scope string.
    Section GetRegisterWrites.
      Variable reg: RegInitT.
      
      Definition regKind := match projT1 (snd reg) with
                            | SyntaxKind k => k
                            | _ => Void
                            end.
      Fixpoint getRegisterWrites k (a: ActionT (fun _ => list nat) k) (startList: list nat) : RtlExpr (Maybe regKind) :=
        match a in ActionT _ _ with
        | MCall meth k argExpr cont =>
          @getRegisterWrites _ (cont startList) (inc startList)
        | Return x => invalidRtl _
        | LetExpr k' expr cont =>
          match k' return Expr (fun _ => list nat) k' ->
                          (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun expr cont => @getRegisterWrites _ (cont startList) (inc startList)
          | _ => fun _ _ => invalidRtl _
          end expr cont
        | LetAction k' a' cont =>
          let w1 := @getRegisterWrites _ a' (0 :: startList) in
          let w2 := @getRegisterWrites _ (cont startList) (inc startList) in
          (RtlITE (w2 @% "valid") w2 w1)%rtl_expr
        | ReadNondet k' cont =>
          match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun cont => @getRegisterWrites _ (cont startList) (inc startList)
          | _ => fun _ => invalidRtl _
          end cont
        | ReadReg r k' cont =>
          match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun cont => @getRegisterWrites _ (cont startList) (inc startList)
          | _ => fun _ => invalidRtl _
          end cont
        | Assertion pred cont => @getRegisterWrites _ cont startList
        | Sys ls cont => @getRegisterWrites _ cont startList
        | IfElse pred ktf t f cont =>
          let wt := @getRegisterWrites _ t (0 :: startList) in
          let wf := @getRegisterWrites _ f (0 :: inc startList) in
          let wc := @getRegisterWrites _ (cont (inc (inc startList))) (inc (inc (inc startList))) in
          (RtlITE (wc @% "valid") wc
                  (RtlITE (convertExprToRtl pred) wt wf))%rtl_expr
        | WriteReg r k' expr cont =>
          let wc := @getRegisterWrites _ cont startList in
          if string_dec r (fst reg)
          then
            match k' return Expr (fun _ => list nat) k' -> RtlExpr (Maybe regKind) with
            | SyntaxKind k => fun expr =>
                                match Kind_dec regKind k with
                                | left pf => match pf in _ = Y return Expr _ (SyntaxKind Y) -> RtlExpr (Maybe regKind) with
                                             | eq_refl => fun expr => (RtlITE (wc @% "valid") wc
                                                                              (STRUCT {
                                                                                   "valid" ::= RtlReadWire Bool (getActionGuard name) ;
                                                                                   "data" ::= convertExprToRtl expr
                                                                              })
                                                                      )%rtl_expr
                                             end expr
                                | right _ => wc
                                end
            | _ => fun _ => wc
            end expr
          else wc
        end.
    End GetRegisterWrites.

    Section GetMethEns.
      Variable meth: Attribute Signature.
      
      Definition argKind := fst (snd meth).

      Fixpoint getMethEns k (a: ActionT (fun _ => list nat) k) (startList: list nat) : RtlExpr (Maybe argKind) :=
        match a in ActionT _ _ with
        | MCall f k expr cont =>
          let wc := @getMethEns _ (cont startList) (inc startList) in
          if string_dec f (fst meth)
          then
            match Kind_dec argKind (fst k) with
            | left pf => match pf in _ = Y return Expr _ (SyntaxKind Y) -> RtlExpr (Maybe argKind) with
                         | eq_refl => fun expr => (RtlITE (wc @% "valid") wc
                                                          (STRUCT {
                                                               "valid" ::= RtlReadWire Bool (getActionGuard name) ;
                                                               "data" ::= convertExprToRtl expr
                                                          })
                                                  )%rtl_expr
                         end expr
            | right _ => wc
            end
          else wc
        | Return x => invalidRtl _
        | LetExpr k' expr cont =>
          match k' return Expr (fun _ => list nat) k' ->
                          (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun expr cont => @getMethEns _ (cont startList) (inc startList)
          | _ => fun _ _ => invalidRtl _
          end expr cont
        | LetAction k' a' cont =>
          let w1 := @getMethEns _ a' (0 :: startList) in
          let w2 := @getMethEns _ (cont startList) (inc startList) in
          (RtlITE (w2 @% "valid") w2 w1)%rtl_expr
        | ReadNondet k' cont =>
          match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun cont => @getMethEns _ (cont startList) (inc startList)
          | _ => fun _ => invalidRtl _
          end cont
        | ReadReg r k' cont =>
          match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) -> _ with
          | SyntaxKind k => fun cont => @getMethEns _ (cont startList) (inc startList)
          | _ => fun _ => invalidRtl _
          end cont
        | Assertion pred cont => @getMethEns _ cont startList
        | Sys ls cont => @getMethEns _ cont startList
        | IfElse pred ktf t f cont =>
          let wt := @getMethEns _ t (0 :: startList) in
          let wf := @getMethEns _ f (0 :: inc startList) in
          let wc := @getMethEns _ (cont (inc (inc startList))) (inc (inc (inc startList))) in
          (RtlITE (wc @% "valid") wc (RtlITE (convertExprToRtl pred) wt wf))%rtl_expr
        | WriteReg r k' expr cont =>
          @getMethEns _ cont startList
        end.

    End GetMethEns.
    Close Scope string.
  End MethReg.

  Definition convertRegsWrites regs k (a: ActionT (fun _ => list nat) k) startList :=
    map (fun reg =>
           let wc := getRegisterWrites reg a startList in
           (getRegActionFinalWrite name (fst reg), existT _ (regKind reg)
                                                          (RtlITE (wc @% "valid"%string)%rtl_expr (wc @% "data"%string)%rtl_expr
                                                                  (RtlReadWire _ (getRegActionRead name (fst reg)))))) regs.

  
  Definition getRtlDisp (d: SysT (fun _ => list nat)) :=
    match d with
    | DispString s => RtlDispString s
    | DispBool e f => RtlDispBool (@convertExprToRtl _ e) f
    | DispBit n e f => RtlDispBit (@convertExprToRtl _ e) f
    | DispStruct n fk fs e f => RtlDispStruct (@convertExprToRtl _ e) f
    | DispArray n k e f => RtlDispArray (@convertExprToRtl _ e) f
    end.

  Fixpoint getRtlSys k (a: ActionT (fun _ => list nat) k) enable startList : list (RtlExpr Bool * list RtlSysT) :=
    match a in ActionT _ _ with
    | MCall meth k argExpr cont =>
      getRtlSys (cont startList) enable (inc startList)
    | LetExpr k' expr cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (RtlExpr Bool * list RtlSysT) with
      | SyntaxKind k => fun cont =>
                          getRtlSys (cont startList) enable (inc startList)
      | _ => fun _ => nil
      end cont
    | LetAction k' a' cont =>
      getRtlSys a' enable (0 :: startList) ++
                getRtlSys (cont startList) enable (inc startList)
    | ReadNondet k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (RtlExpr Bool * list RtlSysT) with
      | SyntaxKind k => fun cont =>
                          getRtlSys (cont startList) enable (inc startList)
      | _ => fun _ => nil
      end cont
    | ReadReg r k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (RtlExpr Bool * list RtlSysT) with
      | SyntaxKind k => fun cont =>
                          getRtlSys (cont startList) enable (inc startList)
      | _ => fun _ => nil
      end cont
    | WriteReg r k' expr cont =>
      getRtlSys cont enable startList
    | Assertion pred cont => getRtlSys cont (RtlCABool And
                                                       (convertExprToRtl pred :: enable :: nil))
                                       startList
    | Sys ls cont => (enable, map getRtlDisp ls) :: getRtlSys cont enable (inc startList)
    | Return x => nil
    | IfElse pred ktf t f cont =>
      getRtlSys t (RtlCABool And (convertExprToRtl pred :: enable :: nil)) (0 :: startList) ++
                getRtlSys f (RtlCABool And (convertExprToRtl (UniBool Neg pred) :: enable :: nil)) (0 :: inc startList) ++
                getRtlSys (cont (inc (inc startList))) enable (inc (inc (inc startList)))
    end.

  Fixpoint getCallsSign k (a: ActionT (fun _ => list nat) k) startList :=
    match a in ActionT _ _ with
    | MCall meth k argExpr cont =>
      (meth, k) :: getCallsSign (cont startList) (inc startList) 
    | Return x => nil
    | LetExpr k' expr cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (string * (Kind * Kind)) with
      | SyntaxKind k => fun cont =>
                          getCallsSign (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | LetAction k' a' cont =>
      getCallsSign a' (0 :: startList) ++
                   getCallsSign (cont startList) (inc startList)
    | ReadNondet k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (string * (Kind * Kind)) with
      | SyntaxKind k => fun cont =>
                          getCallsSign (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | ReadReg r k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list (string * (Kind * Kind)) with
      | SyntaxKind k => fun cont =>
                          getCallsSign (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | WriteReg r k' expr cont =>
      getCallsSign cont startList
    | Assertion pred cont => getCallsSign cont startList
    | Sys ls cont => getCallsSign cont startList
    | IfElse pred ktf t f cont =>
      getCallsSign t (0 :: startList) ++ getCallsSign f (0 :: inc startList) ++ getCallsSign (cont (inc (inc startList))) (inc (inc (inc startList)))
    end.

  Fixpoint getWrites k (a: ActionT (fun _ => list nat) k) startList :=
    match a in ActionT _ _ with
    | MCall meth k argExpr cont =>
      getWrites (cont startList) (inc startList) 
    | Return x => nil
    | LetExpr k' expr cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list string with
      | SyntaxKind k => fun cont =>
                          getWrites (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | LetAction k' a' cont =>
      getWrites a' (0 :: startList) ++
                   getWrites (cont startList) (inc startList)
    | ReadNondet k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list string with
      | SyntaxKind k => fun cont =>
                          getWrites (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | ReadReg r k' cont =>
      match k' return (fullType (fun _ => list nat) k' -> ActionT (fun _ => list nat) k) ->
                      list string with
      | SyntaxKind k => fun cont =>
                          getWrites (cont startList) (inc startList)
      | _ => fun _ => nil
      end cont
    | WriteReg r k' expr cont =>
      r :: getWrites cont startList
    | Assertion pred cont => getWrites cont startList
    | Sys ls cont => getWrites cont startList
    | IfElse pred ktf t f cont =>
      getWrites t (0 :: startList) ++ getWrites f (0 :: inc startList) ++ getWrites (cont (inc (inc startList))) (inc (inc (inc startList)))
    end.
End Compile.

Definition getCallsSignPerRule (rule: Attribute (Action Void)) :=
  getCallsSign (snd rule (fun _ => list nat)) (1 :: nil).

Definition getCallsPerBaseMod rules := concat (map getCallsSignPerRule rules).

Section ForMeth.
  Variable meth: Attribute Signature.
  Open Scope string.
  Fixpoint getMethEnsRules (rules: list (Attribute (Action Void))) :=
    match rules with
    | r :: rules' => let wc' := getMethEnsRules rules' in
                     (RtlITE (wc' @% "valid") wc' (getMethEns (fst r) meth (snd r _) (1 :: nil)))%rtl_expr
    | nil => invalidRtl _
    end.

  Definition getMethEnsRulesEn rules :=
    (getMethEn (fst meth), existT _ Bool (getMethEnsRules rules @% "valid"))%rtl_expr.

  Definition getMethEnsRulesArg rules :=
    (getMethArg (fst meth), existT _ _ (getMethEnsRules rules @% "data"))%rtl_expr.
  Close Scope string.
End ForMeth.


Definition getMethEnsRulesEnBaseMod rules := map (fun meth => getMethEnsRulesEn meth rules) (getCallsPerBaseMod rules).
Definition getMethEnsRulesArgBaseMod rules := map (fun meth => getMethEnsRulesArg meth rules) (getCallsPerBaseMod rules).

Definition getSysPerRule (rule: Attribute (Action Void)) :=
  getRtlSys (fst rule) (snd rule (fun _ => list nat)) (RtlReadWire Bool (getActionGuard (fst rule))) (1 :: nil).

Definition getSysPerBaseMod rules := concat (map getSysPerRule rules).

(* Set the enables correctly in the following two functions *)

Definition computeRuleAssigns (r: Attribute (Action Void)) :=
  (getActionGuard (fst r),
   existT _ Bool (convertActionToRtl_guardF (fst r) (snd r (fun _ => list nat)) (1 :: nil)))
    ::
    convertActionToRtl_noGuard (fst r) (snd r (fun _ => list nat)) (RtlReadWire Bool (getActionGuard (fst r)))
    (1 :: nil) (0 :: nil).

Definition computeRuleAssignsRegs regs (r: Attribute (Action Void)) :=
  convertRegsWrites (fst r) regs (snd r (fun _ => list nat)) (1 :: nil).

Definition getInputs (calls: list (Attribute (Kind * Kind))) := map (fun x => (getMethRet (fst x), snd (snd x))) calls.
                                                                    (* ++ map (fun x => (getMethGuard (fst x), Bool)) calls. *)

Definition getOutputs (calls: list (Attribute (Kind * Kind))) := map (fun x => (getMethArg (fst x), fst (snd x))) calls ++
                                                                     map (fun x => (getMethEn (fst x), Bool)) calls.

Definition getRegInit (y: {x : FullKind & option (ConstFullT x)}): {x: Kind & option (ConstT x)} :=
  existT _ _
         match projT2 y with
         | None => None
         | Some y' => Some match y' in ConstFullT k return ConstT match k with
                                                                  | SyntaxKind k' => k'
                                                                  | _ => Void
                                                                  end with
                           | SyntaxConst k c => c
                           | _ => WO
                           end
         end.

(* Fixpoint finalWrites (regs: list RegInitT) (a: Attribute (Action Void)): list (string * list nat * {x : Kind & RtlExpr x}) := *)
(*   match regs with *)
(*   | nil => nil *)
(*   | s :: ss => (getRegActionFinalWrite (fst a) (fst s), *)
(*                 existT _ _ (if in_dec string_dec (fst s) (getWrites (snd a (fun _ => list nat)) (1 :: nil)) *)
(*                             then RtlITE (RtlReadWire _ (getRegActionEn (fst a) (fst s))) *)
(*                                         (RtlReadWire _ (getRegActionWrite (fst a) (fst s))) *)
(*                                         (RtlReadWire _ (getRegActionRead (fst a) (fst s))) *)
(*                             else RtlReadWire (projT1 (getRegInit (snd s))) (getRegActionRead (fst a) (fst s)))) *)
(*                  :: finalWrites ss a *)
(*   end. *)

Fixpoint getAllWriteReadConnections' (regs: list RegInitT) (order: list string) {struct order} :=
  match order with
  | penult :: xs =>
    match xs with
    | ult :: ys =>
      map (fun r => (getRegActionRead ult (fst r), existT _ _ (RtlReadWire (projT1 (getRegInit (snd r))) (getRegActionFinalWrite penult (fst r))))) regs
          ++ getAllWriteReadConnections' regs ys
    | nil => map (fun r => (getRegWrite (fst r), existT _ _ (RtlReadWire (projT1 (getRegInit (snd r))) (getRegActionFinalWrite penult (fst r))))) regs
    end
  | nil => nil
  end.

Definition getAllWriteReadConnections (regs: list RegInitT) (order: list string) :=
  match order with
  | beg :: xs =>
    map (fun r => (getRegActionRead beg (fst r), existT _ _ (RtlReadWire (projT1 (getRegInit (snd r))) (getRegRead (fst r))))) regs
        ++ getAllWriteReadConnections' regs order
  | nil => nil
  end.

Definition getWires regs (rules: list (Attribute (Action Void))) (order: list string) :=
  concat (map computeRuleAssigns rules) ++ getAllWriteReadConnections regs order ++ concat (map (computeRuleAssignsRegs regs) rules) ++
         getMethEnsRulesEnBaseMod rules ++ getMethEnsRulesArgBaseMod rules.
      
Definition getWriteRegs (regs: list RegInitT) :=
  map (fun r => (fst r, existT _ (projT1 (getRegInit (snd r))) (RtlReadWire _ (getRegWrite (fst r))))) regs.

Definition getReadRegs (regs: list RegInitT) :=
  map (fun r => (getRegRead (fst r), existT _ (projT1 (getRegInit (snd r))) (RtlReadReg _ (fst r)))) regs.

Definition setMethodGuards (rules: list (Attribute (Action Void))) :=
  map (fun m => (getMethGuard (fst m), existT _ Bool (RtlConst (ConstBool true)))) (getCallsPerBaseMod rules).

Definition getRtl (bm: (list string * list RegFileBase * BaseModule)) :=
  match snd bm with
  | BaseMod regs rules dms =>
    {| hiddenWires := fst (fst bm);
       regFiles := snd (fst bm);
       inputs := getInputs (getCallsPerBaseMod rules);
       outputs := getOutputs (getCallsPerBaseMod rules);
       regInits := map (fun x => (fst x, getRegInit (snd x))) regs;
       regWrites := getWriteRegs regs;
       wires := getReadRegs regs ++ getWires regs rules (map fst rules) ++ setMethodGuards rules;
       sys := getSysPerBaseMod rules |}
  | _ => {| hiddenWires := fst (fst bm);
            regFiles := snd (fst bm);
            inputs := nil;
            outputs := nil;
            regInits := nil;
            regWrites := nil;
            wires := nil;
            sys := nil|}
  end.
