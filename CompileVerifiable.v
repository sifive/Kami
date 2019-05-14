Require Import Syntax StateMonad.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope string.

Local Definition SynExpr ty k := (Expr ty (SyntaxKind k)).

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Inductive CompActionT: Kind -> Type :=
  | CompCall (f: string) (argRetK: Kind * Kind) (pred: SynExpr ty Bool)
             (arg: SynExpr ty (fst argRetK))
             lret (cont: ty (snd argRetK) -> CompActionT lret): CompActionT lret
  | CompLetExpr k (e: SynExpr ty k) lret (cont: ty k -> CompActionT lret): CompActionT lret
  | CompSys (ls: list (SysT ty)) lret (cont: CompActionT lret): CompActionT lret
  | CompRead (r: string) (k: Kind) (readMap: regMapTy) lret (cont: ty k -> CompActionT lret): CompActionT lret
  | CompUpd (r: string) (k: Kind) (v: SynExpr ty k) (writeMap: regMapTy) lret (cont: regMapTy -> CompActionT lret): CompActionT lret
  | CompRet lret (e: SynExpr ty lret) (newMap: regMapTy): CompActionT lret
  | CompLetFull k (a: CompActionT k) lret (cont: ty k -> regMapTy -> CompActionT lret): CompActionT lret.

  Axiom cheat: forall t, t.

  Section ReadMap.
    Variable readMap: regMapTy.
    Fixpoint compileAction k (a: ActionT ty k) (pred: SynExpr ty Bool)
             (writeMap: regMapTy)
             {struct a}:
      CompActionT k :=
      match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        CompCall meth k pred argExpr (fun ret => @compileAction _ (cont ret) pred writeMap)
      | Return x =>
        CompRet x writeMap
      | LetExpr k' expr cont =>
        match k' return (Expr ty k' -> (fullType ty k' -> ActionT ty k) -> CompActionT k) with
        | NativeKind _ => fun _ _ => CompRet (@Const _ _ (getDefaultConst k)) writeMap
        | SyntaxKind k => fun expr cont => CompLetExpr expr (fun ret => @compileAction _ (cont ret) pred writeMap)
        end expr cont
      | ReadNondet k' cont => CompRet (@Const _ _ (getDefaultConst k)) writeMap
      | Assertion pred' cont =>
        compileAction cont (pred && pred')%kami_expr writeMap
      | Sys ls cont => CompSys ls (compileAction cont pred writeMap)
      | ReadReg r k' cont =>
        match k' return ((fullType ty k' -> ActionT ty k)-> CompActionT k) with
        | NativeKind _ => fun _ => CompRet (@Const _ _ (getDefaultConst k)) writeMap
        | SyntaxKind k => fun cont =>
                            @CompRead r k readMap _
                                      (fun v => @compileAction _ (cont v) pred writeMap)
        end cont
      | WriteReg r k' expr cont =>
        match k' return Expr ty k' -> CompActionT k with
        | NativeKind _ => fun _ => CompRet (@Const _ _ (getDefaultConst k)) writeMap
        | SyntaxKind k => fun expr =>
                            @CompRead r k readMap _
                                      (fun v => CompUpd r (IF pred then expr else #v)%kami_expr writeMap
                                                        (fun writeMap' => @compileAction _ cont pred writeMap'))
        end expr
      | LetAction k' a' cont =>
        CompLetFull (@compileAction k' a' pred writeMap)
                    (fun retval writeMap' => @compileAction k (cont retval) pred writeMap')
      | IfElse pred' k' aT aF cont =>
        CompLetFull (@compileAction k' aT (pred && pred')%kami_expr writeMap)
                    (fun valT writesT =>
                       CompLetFull (@compileAction k' aF (pred && !pred')%kami_expr writesT)
                                   (fun valF writesF =>
                                      CompLetExpr (IF pred' then #valT else #valF)%kami_expr
                                                  (fun val => (@compileAction k (cont val) pred writesF))
                    ))
      end.

    Definition compileActions (acts: list (ActionT ty Void)) :=
      fold_left (fun acc a =>
                   CompLetFull acc
                   (fun _ writeMap => compileAction a ($$ true)%kami_expr writeMap)) acts (CompRet ($$ WO)%kami_expr readMap).
  End ReadMap.
End Compile.

Section Semantics.
  Variable readMap: RegsT.
  Inductive SemCompActionT: forall k, CompActionT type RegsT k -> RegsT -> MethsT -> type k -> Prop :=
  | SemCompCall (f: string) (argRetK: Kind * Kind) (pred: SynExpr type Bool)
             (arg: SynExpr type (fst argRetK))
             lret (cont: type (snd argRetK) -> CompActionT type RegsT lret)
             (ret: type (snd argRetK))
             writeMap calls val
             (sem_a: SemCompActionT (cont ret) writeMap calls val)
    : SemCompActionT (@CompCall type RegsT f argRetK pred arg lret cont) writeMap ((f, existT _ argRetK (evalExpr arg, ret)) :: calls) val
  | SemCompLetExpr k (e: SynExpr type k) lret (cont: type k -> CompActionT type RegsT lret)
                   writeMap calls val
                   (sem_a: SemCompActionT (cont (evalExpr e)) writeMap calls val)
    : SemCompActionT (@CompLetExpr type RegsT k e lret cont) writeMap calls val
  | SemCompSys (ls: list (SysT type)) lret (cont: CompActionT type RegsT lret)
               writeMap calls val
               (sem_a: SemCompActionT cont writeMap calls val)
    : SemCompActionT (CompSys ls cont) writeMap calls val
  | SemCompRead (r: string) (k: Kind) (readMap: RegsT) lret (cont: type k -> CompActionT type RegsT lret)
                regV (HIn: In (r, existT _ (SyntaxKind k) regV) readMap)
                writeMap calls val
                (sem_a: SemCompActionT (cont regV) writeMap calls val)
    : SemCompActionT (@CompRead type RegsT r k readMap lret cont) writeMap calls val
  | SemCompRet lret (e: SynExpr type lret) (newMap: RegsT)
    : SemCompActionT (@CompRet type RegsT lret e newMap) newMap nil (evalExpr e)
  | SemCompUpd (r: string) (k: Kind) (v: SynExpr type k) (writeMap: RegsT) lret (cont: RegsT -> CompActionT type RegsT lret)
               writeMap calls val writeMap'
               (sem_a: SemCompActionT (cont (doUpdRegs ((r, existT _ (SyntaxKind k) (evalExpr v)) :: nil) writeMap)) writeMap' calls val)
    : SemCompActionT (@CompUpd type RegsT r k v writeMap lret cont) writeMap' calls val
  | SemCompLetFull k (a: CompActionT type RegsT k) lret (cont: type k -> RegsT -> CompActionT type RegsT lret)
                   writeMapA callsA valA
                   (sem_a: SemCompActionT a writeMapA callsA valA)
                   writeMapCont callsCont valCont
                   (sem_cont: SemCompActionT (cont valA writeMapA) writeMapCont callsCont valCont)
    : SemCompActionT (@CompLetFull type RegsT k a lret cont) writeMapCont callsCont valCont.
End Semantics.
