Require Import Kami.Syntax Kami.Notations.
Set Asymmetric Patterns.
Set Implicit Arguments.

Section ty.
  Variable ty: Kind -> Type.
  Definition boolTy (k: Kind) := bool.
  
  Fixpoint goodDfExpr k (e: Expr boolTy k) {struct e}: bool.
    refine
      match e with
      | Var k v => match k return fullType boolTy k -> bool with
                   | SyntaxKind k' => fun v => v
                   | _ => fun _ => true
                   end v
      | Const k c => true
      | UniBool op e => @goodDfExpr _ e
      | CABool op es => forallb (@goodDfExpr _) es
      | UniBit n1 n2 op e => @goodDfExpr _ e
      | CABit n op es => forallb (@goodDfExpr _) es
      | BinBit n1 n2 n3 op e1 e2 => (@goodDfExpr _ e1) && (@goodDfExpr _ e2)
      | BinBitBool n1 n2 op e1 e2 => (@goodDfExpr _ e1) && (@goodDfExpr _ e2)
      | ITE k p e1 e2 => (@goodDfExpr _ p) && (@goodDfExpr _ e1) && (@goodDfExpr _ e2)
      | Eq k e1 e2 => (@goodDfExpr _ e1) && (@goodDfExpr _ e2)
      | ReadStruct n m k e i => (@goodDfExpr _ e)
      | ReadArray n m k e i => (@goodDfExpr _ e) && (@goodDfExpr _ i)
      | ReadArrayConst n k e i => (@goodDfExpr _ e)
      | BuildArray n k fv => forallb (fun i => @goodDfExpr _ (fv i)) (getFins n)
      | BuildStruct n fk fs fv => forallb (fun i => @goodDfExpr _ (fv i)) (getFins n)
      end.
  Defined.

  
  Fixpoint goodDfAction lret (a: ActionT boolTy lret) :=
    match a with
    | MCall name sig arg cont => goodDfAction (cont true)
    | LetExpr k e cont =>
      match k return Expr boolTy k -> (fullType boolTy k -> ActionT boolTy lret) -> bool with
      | SyntaxKind k' => fun e cont => goodDfAction (cont (goodDfExpr e))
      | _ => fun e cont => false
      end e cont
    | LetAction k a cont => 
      goodDfAction a && (goodDfAction (cont true))
    | ReadNondet k cont =>
      match k return (fullType boolTy k -> ActionT boolTy lret) -> bool with
      | SyntaxKind k' => fun cont => goodDfAction (cont false)
      | _ => fun cont => false
      end cont
    | ReadReg name k cont =>
      match k return (fullType boolTy k -> ActionT boolTy lret) -> bool with
      | SyntaxKind k' => fun cont => goodDfAction (cont true)
      | _ => fun cont => false
      end cont
    | WriteReg name k e cont =>
      goodDfAction cont
    | IfElse p k a1 a2 cont =>
      goodDfExpr p && goodDfAction a1 && goodDfAction a2 &&
                 goodDfAction (cont true)
    | Sys _ cont => goodDfAction cont
    | Return e => (* goodDfExpr e *) true
    end.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Section aggressive.
    Variable isAgg: bool.
    Fixpoint getGuard lret (a: ActionT ty lret): ActionT ty Bool :=
      match a with
      | MCall name sig arg cont =>
        Call gmeth: Bool <- (name ++ ".guard")(arg: _) ;
          LET dummy <- Const _ (getDefaultConst _);
          LETA grest <- getGuard (cont dummy);
          Ret (#gmeth && #grest)
      | LetExpr k e cont =>
        LetExpr e (fun x => getGuard (cont x))
      | LetAction k a cont =>
        LETA ga <- getGuard a;
          LET dummy <- Const _ (getDefaultConst _);
          LETA grest <- getGuard (cont dummy);
          Ret (#ga && #grest)
      | ReadNondet k cont =>
        ReadNondet k (fun x => getGuard (cont x))
      | ReadReg name k cont =>
        ReadReg name k (fun x => getGuard (cont x))
      | WriteReg name k e cont =>
        getGuard cont
      | IfElse p k a1 a2 cont =>
        LETA g1 <- getGuard a1;
          LETA g2 <- getGuard a2;
          LET dummy <- Const _ (getDefaultConst _);
          LETA grest <- getGuard (cont dummy);
          Ret (if isAgg then (IF p then #g1 else #g2) && #grest else #g1 && #g2 && #grest)
      | Sys _ cont => getGuard cont
      | Return e => Ret ($$ true)
      end.

    Definition addGuardGen lret (a: ActionT ty lret) :=
      LETA g <- getGuard a;
        If #g then a else Ret ($$ (getDefaultConst lret)) as sth;
        Ret #sth.
  End aggressive.
End ty.

Definition addGuardMeth (f: DefMethT) :=
  (fst f, existT MethodT (projT1 (snd f))
                 (fun ty x =>
                    addGuardGen (goodDfAction (projT2 (snd f) boolTy true))
                                (projT2 (snd f) ty x))).


Definition MethodGuardT (sig: Signature) :=
  forall ty : Kind -> Type, (ty (fst sig) -> ActionT ty (snd sig)) *
                            (ty (fst sig) -> ActionT ty Bool).

Definition DefMethGuardT := Attribute (sigT MethodGuardT).

Definition addGuardRule (ra: Attribute (Action Void)) :=
  (fst ra, fun ty => addGuardGen (goodDfAction (snd ra boolTy)) (snd ra ty)).

Definition addGuardMethWithGuard (f: DefMethGuardT): (DefMethT * DefMethT) :=
  (addGuardMeth (fst f, existT MethodT
                               (projT1 (snd f))
                               (fun ty => fst (projT2 (snd f) ty))),
   addGuardMeth ((fst f ++ ".guard")%string,
                 existT MethodT
                        (fst (projT1 (snd f)), Bool)
                        (fun ty => snd (projT2 (snd f) ty)))).
  

(* IGNORE THE REST *)

(* Section ty. *)
(*   Variable ty: Kind -> Type. *)
(*   Definition optTy := (fun k => option (ty k)). *)

(*   Definition liftSome A B (f: A -> B) (e: option A) := match e with *)
(*                                                        | Some x => Some (f x) *)
(*                                                        | None => None *)
(*                                                        end. *)

(*   Fixpoint liftSomes A (ls: list (option A)) := *)
(*     match ls with *)
(*     | Some x :: xs => liftSome (cons x) (liftSomes xs) *)
(*     | None :: xs => None *)
(*     | nil => Some nil *)
(*     end. *)

(*   Definition liftSome2 A B C (f: A -> B -> C) (e1: option A) (e2: option B) *)
(*     := match e1, e2 with *)
(*        | Some x, Some y => Some (f x y) *)
(*        | _, _ => None *)
(*        end. *)

(*   Definition liftSome3 A B C D (f: A -> B -> C -> D) (e1: option A) (e2: option B) (e3: option C) *)
(*     := match e1, e2, e3 with *)
(*        | Some x, Some y, Some z => Some (f x y z) *)
(*        | _, _, _ => None *)
(*        end. *)

(*   Fixpoint exprForGuard k (e: Expr optTy k) {struct e}: option (Expr ty k). *)
(*     refine *)
(*       match e with *)
(*       | Var k v => match k return fullType optTy k -> option (Expr ty k) with *)
(*                    | SyntaxKind k' => fun v => match v with *)
(*                                                | None => None *)
(*                                                | Some x => Some (Var _ (SyntaxKind k') x) *)
(*                                                end *)
(*                    | NativeKind sk => fun v => Some (Var ty (NativeKind sk) v) *)
(*                    end v *)
(*       | Const k c => Some (Const _ c) *)
(*       | UniBool op e => liftSome (UniBool op) (@exprForGuard _ e) *)
(*       | CABool op es => liftSome (CABool op) (liftSomes (map (@exprForGuard _) es)) *)
(*       | UniBit n1 n2 op e => liftSome (UniBit op) (@exprForGuard _ e) *)
(*       | CABit n op es => liftSome (CABit op) (liftSomes (map (@exprForGuard _) es)) *)
(*       | BinBit n1 n2 n3 op e1 e2 => liftSome2 (BinBit op) (@exprForGuard _ e1) *)
(*                                               (@exprForGuard _ e2) *)
(*       | BinBitBool n1 n2 op e1 e2 => liftSome2 (BinBitBool op) (@exprForGuard _ e1) *)
(*                                                (@exprForGuard _ e2) *)
(*       | ITE k p e1 e2 =>  liftSome3 (@ITE _ k) (@exprForGuard _ p) *)
(*                                     (@exprForGuard _ e1) (@exprForGuard _ e2) *)
(*       | Eq k e1 e2 => liftSome2 (@Eq _ k) (@exprForGuard _ e1) (@exprForGuard _ e2) *)
(*       | ReadStruct n fk fs e i => liftSome (fun e => ReadStruct e i) (@exprForGuard _ e) *)
(*       | ReadArray n m k e i => liftSome2 (@ReadArray ty n m k) *)
(*                                          (@exprForGuard _ e) (@exprForGuard _ i) *)
(*       | ReadArrayConst n k e i => liftSome (fun e => @ReadArrayConst ty n k e i) *)
(*                                            (@exprForGuard _ e) *)
(*       | BuildArray n k fv => _ *)
(*       | BuildStruct n fk fs fv => _ *)
(*       end. *)
(*     - refine (match _ with *)
(*               | None => None *)
(*               | Some fv' => Some (BuildStruct fk fs fv') *)
(*               end). *)
(*       pose proof (fun i => @exprForGuard _ (fv i)) as sth. *)
(*       induction n. *)
(*       + exact (Some (fun i => Fin.case0 (fun i => Expr ty (SyntaxKind (fk i))) i)). *)
(*       + refine (match sth Fin.F1, IHn (fun i => fk (Fin.FS i)) *)
(*                                       (fun i => fs (Fin.FS i)) *)
(*                                       (fun i => fv (Fin.FS i)) *)
(*                                       (fun i => sth (Fin.FS i))with *)
(*                 | Some x, Some y => Some (fun i => fin_case *)
(*                                                      i *)
(*                                                      (fun i => Expr ty (SyntaxKind (fk i))) x y) *)
(*                 | _, _ => None *)
(*                 end). *)
(*     - refine (match _ with *)
(*               | None => None *)
(*               | Some fv' => Some (BuildArray fv') *)
(*               end). *)
(*       pose proof (fun i => @exprForGuard _ (fv i)) as sth. *)
(*       induction n. *)
(*       + exact (Some (fun i => Fin.case0 (fun i => Expr ty (SyntaxKind k)) i)). *)
(*       + refine (match sth Fin.F1, IHn (fun i => fv (Fin.FS i)) (fun i => sth (Fin.FS i)) with *)
(*                 | Some x, Some y => Some (fun i => fin_case *)
(*                                                      i *)
(*                                                      (fun i => Expr ty (SyntaxKind k)) x y) *)
(*                 | _, _ => None *)
(*                 end). *)
(*   Defined. *)

(* End ty. *)
