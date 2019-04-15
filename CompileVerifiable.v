Require Import Syntax StateMonad.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope string.

Local Definition SynExpr ty k := (Expr ty (SyntaxKind k)).

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Section lret.
    Variable lret: Kind.
    
    Inductive CompActionT: Type :=
    | CompReadCtxt (r: string) (k: Kind) (regMap: regMapTy)
                   (cont: ty k -> CompActionT): CompActionT
    | CompLetExpr k (e: SynExpr ty k) (cont: ty k -> CompActionT): CompActionT
    | CompLetCtxt (vals: forall sk: (string * Kind), SynExpr ty (snd sk))
                  (cont: regMapTy -> CompActionT):
        CompActionT
    | CompRet (vals: forall sk: (string * Kind), SynExpr ty (snd sk))
              (e: SynExpr ty lret): CompActionT
    | CompCall (f: string) (argRetK: Kind * Kind) (pred: SynExpr ty Bool)
               (arg: SynExpr ty (fst argRetK))
               (cont: ty (snd argRetK) -> CompActionT): CompActionT.
  End lret.

  Axiom cheat: forall t, t.

  Fixpoint compile k (a: ActionT ty k) (pred: SynExpr ty Bool)
           (writes: forall sk: (string * Kind), SynExpr ty (snd sk))
           (regMap: regMapTy)
           {struct a}:
    CompActionT k :=
    match a in ActionT _ _ with
    | MCall meth k argExpr cont =>
      CompCall meth k pred argExpr (fun ret => @compile _ (cont ret) pred writes regMap)
    | Return x =>
      CompRet writes x
    | WriteReg r k' expr cont =>
      match k' return Expr ty k' -> CompActionT k with
      | NativeKind _ => fun _ => CompRet writes (@Const _ _ (getDefaultConst k))
      | SyntaxKind k' =>
        fun expr =>
        @compile _ cont pred (fun rk =>
                                match string_dec (fst rk) r, Kind_dec k' (snd rk) with
                                | left _, left pf => ITE pred
                                                         match pf in _ = Y return
                                                               Expr _ (_ Y) with
                                                         | eq_refl => expr
                                                         end
                                                         (writes rk)
                                | _, _ => writes rk
                                end) regMap
      end expr
    | _ => cheat _
    end.
    (* | LetExpr k' expr cont => *)
    (*   match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> *)
    (*                   list (string * (Kind * Kind)) with *)
    (*   | SyntaxKind k => fun cont => getCallsWithSign (cont tt) *)
    (*   | _ => fun _ => nil *)
    (*   end cont *)
    (* | LetAction k' a' cont => *)
    (*   getCallsWithSign a' ++ getCallsWithSign (cont tt) *)
    (* | ReadNondet k' cont => *)
    (*   match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> *)
    (*                   list (string * (Kind * Kind)) with *)
    (*   | SyntaxKind k => fun cont => *)
    (*                       getCallsWithSign (cont tt) *)
    (*   | _ => fun _ => nil *)
    (*   end cont *)
    (* | ReadReg r k' cont => *)
    (*   match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> *)
    (*                   list (string * (Kind * Kind)) with *)
    (*   | SyntaxKind k => fun cont => *)
    (*                       getCallsWithSign (cont tt) *)
    (*   | _ => fun _ => nil *)
    (*   end cont *)
    (* | Assertion pred cont => getCallsWithSign cont *)
    (* | Sys ls cont => getCallsWithSign cont *)
    (* | IfElse predNew ktf t f cont => *)
    (*   getCallsWithSign t ++ getCallsWithSign f ++ getCallsWithSign (cont tt) *)
End Compile.
