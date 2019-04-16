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
    CompActionT k. refine
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
    | LetExpr k' expr cont =>
      match k' return (Expr ty k' -> (fullType ty k' -> ActionT ty k) -> CompActionT k) with
      | NativeKind _ => fun _ _ => CompRet writes (@Const _ _ (getDefaultConst k))
      | SyntaxKind k0 =>
        (fun (e0 : Expr ty (SyntaxKind k0))
            (cont0 : fullType ty (SyntaxKind k0) -> ActionT ty k) =>
          (match Kind_dec k k0 with
           | left e1 =>
             match e1 in _ = Y return (Expr ty (SyntaxKind Y) ->
                                       (fullType ty (SyntaxKind Y) -> ActionT ty k) ->
                                       CompActionT k) with
             | eq_refl =>
               (fun (e2 : Expr ty (SyntaxKind k))
                    (cont1 : fullType ty (SyntaxKind k) -> ActionT ty k) =>
                  CompLetExpr e2 (fun ret => @compile _ (cont1 ret) pred writes regMap)
               ) end e0 cont0
           | right _ => CompRet writes (@Const _ _ (getDefaultConst k))
           end))
      end expr cont
    | LetAction k' a' cont =>
      cheat _ 
    | ReadNondet k' cont => CompRet writes (@Const _ _ (getDefaultConst k))
    | ReadReg r k' cont =>
      match k' return ((fullType ty k' -> ActionT ty k)-> CompActionT k) with
      | NativeKind _ => fun _ => CompRet writes (@Const _ _ (getDefaultConst k))
      | SyntaxKind k0 =>
        (fun (cont0 : fullType ty (SyntaxKind k0) -> ActionT ty k) =>
           (match Kind_dec k k0 with
            | left e1 =>
              match e1 in _ = Y return ((fullType ty (SyntaxKind Y) -> ActionT ty k) ->
                                        CompActionT k) with
              | eq_refl =>
                (fun (cont1 : fullType ty (SyntaxKind k) -> ActionT ty k) =>
                   CompReadCtxt r regMap (fun ret => @compile _ (cont1 ret) pred writes regMap)
                ) end cont0
            | right _ => CompRet writes (@Const _ _ (getDefaultConst k))
            end))
      end cont
    | Assertion pred' cont =>
      compile _ cont (pred && pred')%kami_expr writes regMap
    | Sys ls cont => compile _ cont pred writes regMap
    | IfElse pred' k' aT aF cont => cheat _
    end.
  Defined.
End Compile.
