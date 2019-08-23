Require Import Kami.StateMonad Kami.Syntax Kami.Properties Kami.PProperties Kami.PPlusProperties Kami.Notations Kami.Lib.EclecticLib.
Import Word.Notations.

Require Import ZArith.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Compile.
  Variable ty: Kind -> Type.
  Variable regMapTy: Type.

  Inductive RegMapExpr: Type :=
  | VarRegMap (v: regMapTy): RegMapExpr
  | UpdRegMap (r: string) (pred: Bool @# ty) (k: FullKind) (val: Expr ty k)
              (regMap: RegMapExpr): RegMapExpr
  | CompactRegMap (regMap: RegMapExpr): RegMapExpr.

  Inductive CompActionT: Kind -> Type :=
  | CompCall (f: string) (argRetK: Kind * Kind) (pred: Bool @# ty)
             (arg: fst argRetK @# ty)
             lret (cont: fullType ty (SyntaxKind (snd argRetK)) -> CompActionT lret): CompActionT lret
  | CompLetExpr k (e: Expr ty k) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompNondet k lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompSys (ls: list (SysT ty)) lret (cont: CompActionT lret): CompActionT lret
  | CompRead (r: string) (k: FullKind) (readMap: RegMapExpr) lret (cont: fullType ty k -> CompActionT lret): CompActionT lret
  | CompRet lret (e: lret @# ty) (newMap: RegMapExpr) : CompActionT lret
  | CompLetFull k (a: CompActionT k) lret (cont: fullType ty (SyntaxKind k) -> regMapTy -> CompActionT lret): CompActionT lret
  | CompAsyncRead (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (k : Kind) (readMap : RegMapExpr) lret
                  (cont : fullType ty (SyntaxKind (Array num k)) -> CompActionT lret) : CompActionT lret
  | CompWrite (idxNum num : nat) (dataArray : string) (idx  : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind) (val : Array num Data @# ty)
              (mask : option (Array num Bool @# ty)) (pred : Bool @# ty) (writeMap readMap : RegMapExpr) lret
              (cont : regMapTy -> CompActionT lret) : CompActionT lret
  | CompSyncReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty) (Data : Kind)
                    (isAddr : bool) (pred : Bool @# ty) (writeMap readMap : RegMapExpr) lret
                    (cont : regMapTy -> CompActionT lret) : CompActionT lret
  | CompSyncReadRes (idxNum num : nat) (readReg dataArray : string) (Data : Kind) (isAddr : bool) (readMap : RegMapExpr) lret
                    (cont : fullType ty (SyntaxKind (Array num Data)) -> CompActionT lret) : CompActionT lret.

  Inductive EActionT (lretT : Kind) : Type :=
  | EMCall (meth : string) s (e : Expr ty (SyntaxKind (fst s)))
           (cont : (fullType ty (SyntaxKind (snd s))) -> EActionT lretT) : EActionT lretT
  | ELetExpr (k : FullKind) (e : Expr ty k) (cont : fullType ty k  -> EActionT lretT) : EActionT lretT
  | ELetAction (k : Kind) (a : EActionT k) (cont : fullType ty (SyntaxKind k) -> EActionT lretT) : EActionT lretT
  | EReadNondet (k : FullKind) (cont : fullType ty k -> EActionT lretT) : EActionT lretT
  | EReadReg (r : string) (k : FullKind) (cont : fullType ty k -> EActionT lretT) : EActionT lretT
  | EWriteReg (r : string) (k : FullKind) (e :  Expr ty k) (cont : EActionT lretT) : EActionT lretT
  | EIfElse : Expr ty (SyntaxKind Bool) -> forall k, EActionT k -> EActionT k -> (fullType ty (SyntaxKind k) -> EActionT lretT) -> EActionT lretT
  | ESys (ls : list (SysT ty)) (cont : EActionT lretT) : EActionT lretT
  | EReturn (e : Expr ty (SyntaxKind lretT)) : EActionT lretT
  | EAsyncRead (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty)
                      (k : Kind) (cont : fullType ty (SyntaxKind (Array num k)) -> EActionT lretT) : EActionT lretT
  | EWrite (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty)
                  (Data : Kind) (val : Array num Data @# ty) (mask : option (Array num Bool @# ty))
                  (cont : EActionT lretT) : EActionT lretT
  | ESyncReadReq (idxNum num : nat) (readReg dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# ty)
                        (Data : Kind) (isAddr : bool) (cont : EActionT lretT) : EActionT lretT
  | ESyncReadRes (idxNum num : nat) (readReg dataArray : string) (Data : Kind) (isAddr : bool)
                        (cont : fullType ty (SyntaxKind (Array num Data)) -> EActionT lretT) : EActionT lretT.
  
  Fixpoint Action_EAction (lretT : Kind) (a : ActionT ty lretT) :  EActionT lretT :=
    match a in ActionT _ _ with
    | MCall meth k argExpr cont =>
      EMCall meth k argExpr (fun v => Action_EAction (cont v))
    | Return x =>
      EReturn x
    | LetExpr k' expr cont => ELetExpr expr (fun v => Action_EAction (cont v))
    | ReadNondet k' cont => EReadNondet k' (fun ret => Action_EAction (cont ret))
    | Sys ls cont => ESys ls (Action_EAction cont)
    | ReadReg r k' cont => EReadReg r k' (fun v => Action_EAction (cont v))
    | WriteReg r k' expr cont => EWriteReg r expr (Action_EAction cont)
    | LetAction k' a' cont => ELetAction (Action_EAction a') (fun v => Action_EAction (cont v))
    | IfElse pred' k' aT aF cont => EIfElse pred' (Action_EAction aT) (Action_EAction aF) (fun v => Action_EAction (cont v))
    end.
  
  Section ReadMap.
    Variable readMap: regMapTy.

    
    Fixpoint compileAction k (a: ActionT ty k) (pred: Bool @# ty)
             (writeMap: RegMapExpr) {struct a}:
      CompActionT k :=
      match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        CompCall meth k pred argExpr (fun ret => @compileAction _ (cont ret) pred writeMap)
      | Return x =>
        CompRet x writeMap
      | LetExpr k' expr cont => CompLetExpr expr (fun ret => @compileAction _ (cont ret) pred writeMap)
      | ReadNondet k' cont => CompNondet k' (fun ret => @compileAction _ (cont ret) pred writeMap)
      | Sys ls cont => CompSys ls (compileAction cont pred writeMap)
      | ReadReg r k' cont =>
        @CompRead r k' (VarRegMap readMap) _ (fun v => @compileAction _ (cont v) pred writeMap)
      | WriteReg r k' expr cont =>
        CompLetFull (CompRet ($$ WO)%kami_expr
                             (UpdRegMap r pred expr writeMap)) (fun _ v => @compileAction _ cont pred (VarRegMap v))
      | LetAction k' a' cont =>
        CompLetFull (@compileAction k' a' pred writeMap)
                    (fun retval writeMap' => @compileAction k (cont retval) pred (VarRegMap writeMap'))
      | IfElse pred' k' aT aF cont =>
        CompLetFull (@compileAction k' aT (pred && pred')%kami_expr writeMap)
                    (fun valT writesT =>
                       CompLetFull (@compileAction k' aF (pred && !pred')%kami_expr (VarRegMap writesT))
                                   (fun valF writesF =>
                                      CompLetExpr (IF pred' then #valT else #valF)%kami_expr
                                                  (fun val => (@compileAction k (cont val) pred (VarRegMap writesF)))
                    ))
      end.

    Fixpoint EcompileAction k (a : EActionT k) (pred : Bool @# ty)
             (writeMap : RegMapExpr) {struct a} :
      CompActionT k :=
      match a in EActionT _ with
      | EMCall meth k argExpr cont =>
        CompCall meth k pred argExpr (fun ret => @EcompileAction _ (cont ret) pred writeMap)
      | EReturn x =>
        CompRet x writeMap
      | ELetExpr k' expr cont => CompLetExpr expr (fun ret => @EcompileAction _ (cont ret) pred writeMap)
      | EReadNondet k' cont => CompNondet k' (fun ret => @EcompileAction _ (cont ret) pred writeMap)
      | ESys ls cont => CompSys ls (EcompileAction cont pred writeMap)
      | EReadReg r k' cont =>
        @CompRead r k' (VarRegMap readMap) _ (fun v => @EcompileAction _ (cont v) pred writeMap)
      | EWriteReg r k' expr cont =>
        CompLetFull (CompRet ($$ WO)%kami_expr
                             (UpdRegMap r pred expr writeMap)) (fun _ v => @EcompileAction _ cont pred (VarRegMap v))
      | ELetAction k' a' cont =>
        CompLetFull (@EcompileAction k' a' pred writeMap)
                    (fun retval writeMap' => @EcompileAction k (cont retval) pred (VarRegMap writeMap'))
      | EIfElse pred' k' aT aF cont =>
        CompLetFull (@EcompileAction k' aT (pred && pred')%kami_expr writeMap)
                    (fun valT writesT =>
                       CompLetFull (@EcompileAction k' aF (pred && !pred')%kami_expr (VarRegMap writesT))
                                   (fun valF writesF =>
                                      CompLetExpr (IF pred' then #valT else #valF)%kami_expr
                                                  (fun val => (@EcompileAction k (cont val) pred (VarRegMap writesF)))
                    ))
      | EAsyncRead idxNum num dataArray idx k cont =>
        CompAsyncRead idxNum dataArray idx (VarRegMap readMap)
                      (fun array => @EcompileAction _ (cont array) pred writeMap)
      | EWrite idxNum num dataArray idx Data val mask cont =>
        CompWrite idxNum dataArray idx val mask pred writeMap (VarRegMap readMap)
                  (fun writeMap' => @EcompileAction _ cont pred (VarRegMap writeMap'))
      | ESyncReadReq idxNum num readReg dataArray idx Data isAddr cont =>
        CompSyncReadReq idxNum num readReg dataArray idx Data isAddr pred writeMap (VarRegMap readMap)
                        (fun writeMap' => @EcompileAction _ cont pred (VarRegMap writeMap'))
      | ESyncReadRes idxNum num readReg dataArray Data isAddr cont =>
        CompSyncReadRes idxNum readReg dataArray isAddr (VarRegMap readMap)
                        (fun array => @EcompileAction _ (cont array) pred writeMap)
      end.

    Fixpoint inlineWriteFile k (rf : RegFileBase) (a : EActionT k) : EActionT k :=
      match rf with
      | @Build_RegFileBase _isWrMask _num _dataArray _readers _write _idxNum _Data _init =>
        match a with
        | EMCall g sign arg cont =>
          match String.eqb _write g with
          | true =>
            if _isWrMask then
              match Signature_dec sign (WriteRqMask (Nat.log2_up _idxNum) _num _Data, Void) with
              | left isEq =>
                let inValue := (match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with | eq_refl => arg end) in
                ELetExpr ($$ WO)%kami_expr
                         (fun v => EWrite _idxNum _dataArray (inValue @% "addr")%kami_expr (inValue @% "data")%kami_expr
                                          (Some (inValue @% "mask")%kami_expr) (inlineWriteFile rf (match isEq in _ = Y return fullType ty (SyntaxKind (snd Y)) -> EActionT k with
                                                                                                    | eq_refl => cont
                                                                                                    end v)))
              | right _ => EMCall g sign arg (fun ret => inlineWriteFile rf (cont ret))
              end
            else
              match Signature_dec sign (WriteRq (Nat.log2_up _idxNum) (Array _num _Data), Void) with
              | left isEq =>
                let inValue := (match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with | eq_refl => arg end) in
                ELetExpr ($$ WO)%kami_expr
                         (fun v => EWrite _idxNum _dataArray (inValue @% "addr")%kami_expr (inValue @% "data")%kami_expr
                                          None (inlineWriteFile rf (match isEq in _ = Y return fullType ty (SyntaxKind (snd Y)) -> EActionT k with
                                                                    | eq_refl => cont
                                                                    end v)))
              | right _ => EMCall g sign arg (fun ret => inlineWriteFile rf (cont ret))
              end
          | false => EMCall g sign arg (fun ret => inlineWriteFile rf (cont ret))
          end
        | ELetExpr _ e cont => ELetExpr e (fun ret => inlineWriteFile rf (cont ret))
        | ELetAction _ a cont => ELetAction (inlineWriteFile rf a) (fun ret => inlineWriteFile rf (cont ret))
        | EReadNondet k c => EReadNondet k (fun ret => inlineWriteFile rf (c ret))
        | EReadReg r k c => EReadReg r k (fun ret => inlineWriteFile rf (c ret))
        | EWriteReg r k e a => EWriteReg r e (inlineWriteFile rf a)
        | EIfElse p _ aT aF c => EIfElse p (inlineWriteFile rf aT) (inlineWriteFile rf aF) (fun ret => inlineWriteFile rf (c ret))
        | ESys ls c => ESys ls (inlineWriteFile rf c)
        | EReturn e => EReturn e
        | EAsyncRead idxNum num dataArray idx k cont =>
          EAsyncRead idxNum dataArray idx (fun ret => inlineWriteFile rf (cont ret))
        | EWrite idxNum num dataArray idx Data val mask cont =>
          EWrite idxNum dataArray idx val mask (inlineWriteFile rf cont)
        | ESyncReadReq idxNum num readReg dataArray idx Data isAddr cont =>
          ESyncReadReq idxNum num readReg dataArray idx Data isAddr (inlineWriteFile rf cont)
        | ESyncReadRes idxNum num readReg dataArray Data isAddr cont =>
          ESyncReadRes idxNum readReg dataArray isAddr (fun v => inlineWriteFile rf (cont v))
        end
      end.
    
    Fixpoint inlineAsyncReadFile (read : string) (rf : RegFileBase) k (a : EActionT k) : EActionT k :=
      match rf with
      | @Build_RegFileBase _isWrMask _num _dataArray _readers _write _idxNum _Data _init =>
        match _readers with
        | Async reads =>
          match (existsb (String.eqb read) reads) with
          | true =>
            match a with
            | EMCall g sign arg cont =>
              match String.eqb read g with
              | true =>
                match Signature_dec sign (Bit (Nat.log2_up _idxNum), Array _num _Data) with
                | left isEq =>
                  let inValue := (match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with | eq_refl => arg end) in
                  EAsyncRead _idxNum _dataArray inValue (fun array => inlineAsyncReadFile  read rf (match isEq in _ = Y return fullType ty (SyntaxKind (snd Y)) -> EActionT k with
                                                                                                      | eq_refl => cont
                                                                                                      end array))
                | right _ => EMCall g sign arg (fun ret => inlineAsyncReadFile read rf (cont ret))
                end
              | false => EMCall g sign arg (fun ret => inlineAsyncReadFile read rf (cont ret))
              end
            | ELetExpr _ e cont => ELetExpr e (fun ret => inlineAsyncReadFile read rf (cont ret))
            | ELetAction _ a cont => ELetAction (inlineAsyncReadFile read rf a) (fun ret => inlineAsyncReadFile read rf (cont ret))
            | EReadNondet k c => EReadNondet k (fun ret => inlineAsyncReadFile read rf (c ret))
            | EReadReg r k c => EReadReg r k (fun ret => inlineAsyncReadFile read rf (c ret))
            | EWriteReg r k e a => EWriteReg r e (inlineAsyncReadFile read rf a)
            | EIfElse p _ aT aF c => EIfElse p (inlineAsyncReadFile read rf aT) (inlineAsyncReadFile read rf aF) (fun ret => inlineAsyncReadFile read rf (c ret))
            | ESys ls c => ESys ls (inlineAsyncReadFile read rf c)
            | EReturn e => EReturn e
            | EAsyncRead idxNum num dataArray idx k cont =>
              EAsyncRead idxNum dataArray idx (fun ret => inlineAsyncReadFile read rf (cont ret))
            | EWrite idxNum num dataArray idx Data val mask cont =>
              EWrite idxNum dataArray idx val mask (inlineAsyncReadFile read rf cont)
            | ESyncReadReq idxNum num readReg dataArray idx Data isAddr cont =>
              ESyncReadReq idxNum num readReg dataArray idx Data isAddr (inlineAsyncReadFile read rf cont)
            | ESyncReadRes idxNum num readReg dataArray Data isAddr cont =>
              ESyncReadRes idxNum readReg dataArray isAddr (fun v => inlineAsyncReadFile read rf (cont v))
            end
          | false => a
          end
        | Sync _ _ => a
        end
      end.

  Lemma SyncRead_eq_dec (r r' : SyncRead) :
    {r = r'} + {r <> r'}.
  Proof.
    destruct (string_dec (readReqName r) (readReqName r')),
    (string_dec (readResName r) (readResName r')),
    (string_dec (readRegName r) (readRegName r')), r, r';
      simpl in *; subst; auto; right; intro; inv H; auto.
  Qed.

  Definition SyncRead_eqb (r r' : SyncRead) : bool :=
    (String.eqb (readReqName r) (readReqName r'))
      && (String.eqb (readResName r) (readResName r'))
      && (String.eqb (readRegName r) (readRegName r')).

  Lemma SyncRead_eqb_eq (r r' : SyncRead) :
    SyncRead_eqb r r' = true <-> r = r'.
  Proof.
    split; intros.
    - unfold SyncRead_eqb in H.
      repeat (apply andb_prop in H; dest; rewrite String.eqb_eq in *).
      destruct r, r'; simpl in *; subst; auto.
    - rewrite H.
      unfold SyncRead_eqb; repeat rewrite eqb_refl; auto.
  Qed.
              
  Fixpoint inlineSyncResFile (read : SyncRead) (rf : RegFileBase) k (a : EActionT k) : EActionT k :=
    match rf with
    | @Build_RegFileBase _isWrMask _num _dataArray _readers _write _idxNum _Data _init =>
      match read with
      | @Build_SyncRead _readReqName _readResName _readRegName => 
        match _readers with
        | Async _ => a
        | Sync isAddr reads =>
          match (existsb (SyncRead_eqb read) reads) with
          | true =>
            match a with
            | EMCall g sign arg cont =>
              match String.eqb _readResName g with
              | true =>
                match Signature_dec sign (Void, Array _num _Data) with
                | left isEq =>
                  ESyncReadRes _idxNum _readRegName _dataArray isAddr (fun array => inlineSyncResFile read rf (match isEq in _ = Y return fullType ty (SyntaxKind (snd Y)) -> EActionT k with | eq_refl => cont end array))
                | right _ => EMCall g sign arg (fun ret => inlineSyncResFile read rf (cont ret))
                end 
              | false => EMCall g sign arg (fun ret => inlineSyncResFile read rf (cont ret))
              end
            | ELetExpr _ e cont => ELetExpr e (fun ret => inlineSyncResFile read rf (cont ret))
            | ELetAction _ a cont => ELetAction (inlineSyncResFile read rf a) (fun ret => inlineSyncResFile read rf (cont ret))
            | EReadNondet k c => EReadNondet k (fun ret => inlineSyncResFile read rf (c ret))
            | EReadReg r k c => EReadReg r k (fun ret => inlineSyncResFile read rf (c ret))
            | EWriteReg r k e a => EWriteReg r e (inlineSyncResFile read rf a)
            | EIfElse p _ aT aF c => EIfElse p (inlineSyncResFile read rf aT) (inlineSyncResFile read rf aF) (fun ret => inlineSyncResFile read rf (c ret))
            | ESys ls c => ESys ls (inlineSyncResFile read rf c)
            | EReturn e => EReturn e
            | EAsyncRead idxNum num dataArray idx k cont =>
              EAsyncRead idxNum dataArray idx (fun ret => inlineSyncResFile read rf (cont ret))
            | EWrite idxNum num dataArray idx Data val mask cont =>
              EWrite idxNum dataArray idx val mask (inlineSyncResFile read rf cont)
            | ESyncReadReq idxNum num readReg dataArray idx Data isAddr cont =>
              ESyncReadReq idxNum num readReg dataArray idx Data isAddr (inlineSyncResFile read rf cont)
            | ESyncReadRes idxNum num readReg dataArray Data isAddr cont =>
              ESyncReadRes idxNum readReg dataArray isAddr (fun v => inlineSyncResFile read rf (cont v))
            end
          | false => a
          end
        end
      end
    end.

  Fixpoint inlineSyncReqFile (read : SyncRead) (rf : RegFileBase) k (a : EActionT k) : EActionT k :=
    match rf with
    | @Build_RegFileBase _isWrMask _num _dataArray _readers _write _idxNum _Data _init =>
      match read with
      | @Build_SyncRead _readReqName _readResName _readRegName => 
        match _readers with
        | Async _ => a
        | Sync isAddr reads =>
          match (existsb (SyncRead_eqb read) reads) with
          | true =>
            match a with
            | EMCall g sign arg cont =>
              match String.eqb _readReqName g with
              | true =>
                match Signature_dec sign (Bit (Nat.log2_up _idxNum), Void) with
                | left isEq =>
                  let inValue := (match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with | eq_refl => arg end) in
                  ELetExpr ($$ WO)%kami_expr
                           (fun v => ESyncReadReq _idxNum _num _readRegName _dataArray inValue _Data isAddr (inlineSyncReqFile read rf (match isEq in _ = Y return fullType ty (SyntaxKind (snd Y)) -> EActionT k with
                                                                                                       | eq_refl => cont
                                                                                                       end v)))
                | right _ => EMCall g sign arg (fun ret => inlineSyncReqFile read rf (cont ret))
                end 
              | false => EMCall g sign arg (fun ret => inlineSyncReqFile read rf (cont ret))
              end
            | ELetExpr _ e cont => ELetExpr e (fun ret => inlineSyncReqFile read rf (cont ret))
            | ELetAction _ a cont => ELetAction (inlineSyncReqFile read rf a) (fun ret => inlineSyncReqFile read rf (cont ret))
            | EReadNondet k c => EReadNondet k (fun ret => inlineSyncReqFile read rf (c ret))
            | EReadReg r k c => EReadReg r k (fun ret => inlineSyncReqFile read rf (c ret))
            | EWriteReg r k e a => EWriteReg r e (inlineSyncReqFile read rf a)
            | EIfElse p _ aT aF c => EIfElse p (inlineSyncReqFile read rf aT) (inlineSyncReqFile read rf aF) (fun ret => inlineSyncReqFile read rf (c ret))
            | ESys ls c => ESys ls (inlineSyncReqFile read rf c)
            | EReturn e => EReturn e
            | EAsyncRead idxNum num dataArray idx k cont =>
              EAsyncRead idxNum dataArray idx (fun ret => inlineSyncReqFile read rf (cont ret))
            | EWrite idxNum num dataArray idx Data val mask cont =>
              EWrite idxNum dataArray idx val mask (inlineSyncReqFile read rf cont)
            | ESyncReadReq idxNum num readReg dataArray idx Data isAddr cont =>
              ESyncReadReq idxNum num readReg dataArray idx Data isAddr (inlineSyncReqFile read rf cont)
            | ESyncReadRes idxNum num readReg dataArray Data isAddr cont =>
              ESyncReadRes idxNum readReg dataArray isAddr (fun v => inlineSyncReqFile read rf (cont v))
            end
          | false => a
          end
        end
      end
    end.
  
  End ReadMap.

    
    Definition getRegFileWrite (rf : RegFileBase) : DefMethT :=
      match rf with
      | @Build_RegFileBase isWrMask num dataArray _ write idxNum Data _ =>
        writeRegFileFn isWrMask num dataArray write idxNum Data
      end.

    Definition getAsyncReads (rf : RegFileBase) (read : string) : DefMethT :=
      (read,
       existT MethodT (Bit (Nat.log2_up (rfIdxNum rf)), Array (rfNum rf) (rfData rf))
              (buildNumDataArray (rfNum rf) (rfDataArray rf) (rfIdxNum rf) (rfData rf))).
    
    Definition getSyncReq (rf : RegFileBase) (isAddr : bool) (read : SyncRead) : DefMethT :=
      if isAddr
      then
        (readReqName read,
         existT MethodT (Bit (Nat.log2_up (rfIdxNum rf)), Void)
                (fun (ty : Kind -> Type) (idx : fullType ty (SyntaxKind (fst (Bit (Nat.log2_up (rfIdxNum rf)), Void)))) =>
                   (Write readRegName read : fst (Bit (Nat.log2_up (rfIdxNum rf)), Void) <-
                                                 Var ty (SyntaxKind (fst (Bit (Nat.log2_up (rfIdxNum rf)), Void))) idx; Ret 
                                                                                                                          Const ty WO)%kami_action))
      else
        (readReqName read,
         existT MethodT (Bit (Nat.log2_up (rfIdxNum rf)), Void)
                (fun (ty : Kind -> Type) (idx : fullType ty (SyntaxKind (fst (Bit (Nat.log2_up (rfIdxNum rf)), Void)))) =>
                   (LETA vals : Array (rfNum rf) (rfData rf) <- buildNumDataArray (rfNum rf) (rfDataArray rf) (rfIdxNum rf) (rfData rf) ty idx;
                      Write readRegName read : Array (rfNum rf) (rfData rf) <- Var ty (SyntaxKind (Array (rfNum rf) (rfData rf))) vals;
                      Ret Const ty WO)%kami_action)).

    Definition getSyncRes (rf : RegFileBase) (isAddr : bool) (read : SyncRead) : DefMethT :=
      if isAddr
      then
        (readResName read,
         existT MethodT (Void, Array (rfNum rf) (rfData rf))
                (fun (ty : Kind -> Type) (_ : fullType ty (SyntaxKind (fst (Void, Array (rfNum rf) (rfData rf))))) =>
                   (Read name : Bit (Nat.log2_up (rfIdxNum rf)) <- readRegName read;
                      buildNumDataArray (rfNum rf) (rfDataArray rf) (rfIdxNum rf) (rfData rf) ty name)%kami_action))
      else
        (readResName read,
         existT MethodT (Void, Array (rfNum rf) (rfData rf))
                (fun (ty : Kind -> Type) (_ : fullType ty (SyntaxKind (fst (Void, Array (rfNum rf) (rfData rf))))) =>
                   (Read data : Array (rfNum rf) (rfData rf) <- readRegName read;
                      Ret Var ty (SyntaxKind (Array (rfNum rf) (rfData rf))) data)%kami_action)).

    Definition inlineSingle_Flat_pos meths1 meths2 n :=
      match nth_error meths1 n with
      | Some f => map (inlineSingle_Meth f) meths2
      | None => meths2
      end.

    Definition inlineSingle_pos k meths (a : ActionT ty k) n :=
      match nth_error meths n with
      | Some f => inlineSingle f a
      | None => a
      end.
    
    Definition getEachRfMethod (rf : RegFileBase) : list DefMethT :=
      (getRegFileWrite rf :: match (rfRead rf) with
                             | Async read => map (getAsyncReads rf) read
                             | Sync isAddr read => map (getSyncReq rf isAddr) read
                                                       ++ map (getSyncRes rf isAddr) read
                             end).

    Definition EgetRegFileMapMethods k (rf : RegFileBase) : list (EActionT k -> EActionT k) :=
      (inlineWriteFile rf :: match (rfRead rf) with
                             | Async read => map (fun x => @inlineAsyncReadFile x rf k) read
                             | Sync isAddr read => map (fun x => @inlineSyncReqFile x rf k) read
                                                       ++ map (fun x => @inlineSyncResFile x rf k) read
                             end).
    
Definition EeachRfMethodInliners k (lrf : list RegFileBase) : list (EActionT k -> EActionT k) :=
      concat (map (fun rf => EgetRegFileMapMethods k rf) lrf).

    Definition eachRfMethodInliners k (lrf : list RegFileBase) : list (ActionT ty k -> ActionT ty k) :=
      (concat (map (fun rf => (map (fun f => @inlineSingle ty f k) (getRegFileMethods rf))) lrf)).
    
    Definition apply_nth {A : Type} (lf : list (A -> A)) (a : A) (n : nat) :=
      match nth_error lf n with
      | Some f => f a
      | None => a
      end.
    
    Definition preCompileRegFiles k (ea : EActionT k) (lrf : list RegFileBase) : EActionT k :=
      fold_left (apply_nth (EeachRfMethodInliners k lrf)) (seq 0 (length (EeachRfMethodInliners k lrf))) ea.
    
    Definition compileActions (readMap : regMapTy) (acts: list (ActionT ty Void)) :=
      fold_left (fun acc a =>
                   CompLetFull acc (fun _ writeMap =>
                                      (CompLetFull (CompRet ($$ WO)%kami_expr
                                                            (CompactRegMap (VarRegMap writeMap)))
                                      (fun _ v => @compileAction v _ a ($$ true)%kami_expr (VarRegMap v))))) acts
                (CompRet ($$ WO)%kami_expr (VarRegMap readMap)).

    Definition compileActionsRf (readMap : regMapTy) (acts : list (ActionT ty Void)) (lrf : list RegFileBase) :=
      fold_left (fun acc a =>
                   CompLetFull acc (fun _ writeMap =>
                                      (CompLetFull (CompRet ($$ WO)%kami_expr
                                                            (CompactRegMap (VarRegMap writeMap)))
                                                   (fun _ v => @EcompileAction v _ (preCompileRegFiles (Action_EAction a) lrf) ($$ true)%kami_expr (VarRegMap v))))) acts
                (CompRet ($$ WO)%kami_expr (VarRegMap readMap)).

    Definition compileRules (readMap : regMapTy) (rules: list RuleT) :=
      compileActions readMap (map (fun a => snd a ty) rules).

    Definition compileRulesRf (readMap : regMapTy) (rules : list RuleT) (lrf : list RegFileBase) :=
      compileActionsRf readMap (map (fun a => snd a ty) rules) lrf.
    
End Compile.
                                                    
Section Semantics.
  Local Notation UpdRegT := RegsT.
  Local Notation UpdRegsT := (list UpdRegT).

  Local Notation RegMapType := (RegsT * UpdRegsT)%type.

  Section PriorityUpds.
    
    Variable o: RegsT.
    Inductive PriorityUpds: UpdRegsT -> RegsT -> Prop :=
    | NoUpds: PriorityUpds nil o
    | ConsUpds (prevUpds: UpdRegsT) (prevRegs: RegsT)
               (prevCorrect: PriorityUpds prevUpds prevRegs)
               (u: UpdRegT)
               (curr: RegsT)
               (currRegsTCurr: getKindAttr o = getKindAttr curr)
               (Hcurr: forall s v, In (s, v) curr -> In (s, v) u \/ ((~ In s (map fst u)) /\ In (s, v) prevRegs))
               fullU
               (HFullU: fullU = u :: prevUpds):
        PriorityUpds fullU curr.

    Lemma prevPrevRegsTrue prevUpds:
      forall prev, PriorityUpds prevUpds prev -> getKindAttr o = getKindAttr prev.
    Proof.
      induction 1; eauto.
    Qed.
    
  End PriorityUpds.
    
  Inductive SemRegMapExpr: (RegMapExpr type RegMapType) -> RegMapType -> Prop :=
  | SemVarRegMap v:
      SemRegMapExpr (VarRegMap _ v) v
  | SemUpdRegMapTrue r (pred: Bool @# type) k val regMap
                     (PredTrue: evalExpr pred = true)
                     old upds
                     (HSemRegMap: SemRegMapExpr regMap (old, upds))
                     upds'
                     (HEqual : upds' = (hd nil upds ++ ((r, existT _ k (evalExpr val)) :: nil)) :: tl upds):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, upds')
  | SemUpdRegMapFalse r (pred: Bool @# type) k val regMap
                      (PredTrue: evalExpr pred = false)
                      old upds
                      (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@UpdRegMap _ _ r pred k val regMap) (old, upds)
  | SemCompactRegMap old upds regMap (HSemRegMap: SemRegMapExpr regMap (old, upds)):
      SemRegMapExpr (@CompactRegMap _ _ regMap) (old, nil::upds).
  
  Definition WfRegMapExpr (regMapExpr : RegMapExpr type RegMapType) (regMap : RegMapType) :=
    SemRegMapExpr regMapExpr regMap /\
    let '(old, new) := regMap in
    forall u, In u new -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old).
  
  Inductive SemCompActionT: forall k, CompActionT type RegMapType k -> RegMapType ->  MethsT -> type k -> Prop :=
  | SemCompCallTrue (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionT _ _ lret)
             (ret: fullType type (SyntaxKind (snd argRetK)))
             regMap calls val newCalls
             (HNewCalls : newCalls = (f, existT _ argRetK (evalExpr arg, ret)) :: calls)
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val)
             (HPred : evalExpr pred = true):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap newCalls val
  | SemCompCallFalse (f: string) (argRetK: Kind * Kind) (pred: Bool @# type)
             (arg: fst argRetK @# type)
             lret (cont: fullType type (SyntaxKind (snd argRetK)) -> CompActionT _ _ lret)
             (ret: fullType type (SyntaxKind (snd argRetK)))
             regMap calls val
             (HSemCompActionT: SemCompActionT (cont ret) regMap calls val)
             (HPred : evalExpr pred = false):
      SemCompActionT (@CompCall _ _ f argRetK pred arg lret cont) regMap calls val
  | SemCompLetExpr k e lret cont
                   regMap calls val
                   (HSemCompActionT: SemCompActionT (cont (evalExpr e)) regMap calls val):
      SemCompActionT (@CompLetExpr _ _ k e lret cont) regMap calls val
  | SemCompNondet k lret cont
                  ret regMap calls val
                  (HSemCompActionT: SemCompActionT (cont ret) regMap calls val):
      SemCompActionT (@CompNondet _ _ k lret cont) regMap calls val
  | SemCompSys ls lret cont
               regMap calls val
               (HSemCompActionT: SemCompActionT cont regMap calls val):
      SemCompActionT (@CompSys _ _ ls lret cont) regMap calls val
  | SemCompRead r k readMap lret cont
                regMap calls val regVal
                updatedRegs readMapValOld readMapValUpds
                (HReadMap: SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                (HUpdatedRegs: PriorityUpds readMapValOld readMapValUpds updatedRegs)
                (HIn: In (r, (existT _ k regVal)) updatedRegs)
                (HSemCompActionT: SemCompActionT (cont regVal) regMap calls val):
      SemCompActionT (@CompRead _ _ r k readMap lret cont) regMap calls val
  | SemCompRet lret e regMap regMapVal calls
               (HCallsNil : calls = nil)
               (HRegMapWf: WfRegMapExpr regMap regMapVal):
      SemCompActionT (@CompRet _ _ lret e regMap) regMapVal calls (evalExpr e)
  | SemCompLetFull k a lret cont
                   regMap_a calls_a val_a
                   (HSemCompActionT_a: SemCompActionT a regMap_a calls_a val_a)
                   regMap_cont calls_cont val_cont newCalls
                   (HNewCalls : newCalls = calls_a ++ calls_cont)
                   (HSemCompActionT_cont: SemCompActionT (cont val_a regMap_a) regMap_cont calls_cont val_cont):
      SemCompActionT (@CompLetFull _ _ k a lret cont) regMap_cont newCalls val_cont
  | SemCompAsyncRead num (dataArray : string) idxNum (idx : Bit (Nat.log2_up idxNum) @# type) Data readMap lret
                     updatedRegs readMapValOld readMapValUpds regVal regMap
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn :  In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     cont calls val contArray
                     (HContArray : contArray =
                                   BuildArray (fun i : Fin.t num =>
                                                 ReadArray
                                                   (Var type _ regVal)
                                                   (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                   Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                     (HSemCompActionT : SemCompActionT (cont (evalExpr contArray)) regMap calls val):
      SemCompActionT (@CompAsyncRead _ _  idxNum num dataArray idx Data readMap lret cont) regMap calls val
  | SemCompWriteSome num (dataArray : string) idxNum (idx  : Bit (Nat.log2_up idxNum) @# type) Data (array : Array num Data @# type)
                     (optMask : option (Array num Bool @# type)) (writeMap readMap : RegMapExpr type RegMapType) lret mask
                     (HMask : optMask = Some mask)
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     regMapVal pred
                     (HUpdate : WfRegMapExpr (UpdRegMap dataArray pred
                                                        (fold_left (fun newArr i =>
                                                                      ITE
                                                                        (ReadArrayConst mask i)
                                                                        (UpdateArray newArr
                                                                                     (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                     :: nil))
                                                                                     (ReadArrayConst array i))
                                                                        newArr
                                                                   ) (getFins num)
                                                                   (Var type (SyntaxKind (Array idxNum Data)) regVal))
                                                        writeMap) regMapVal)
                     cont regMap_cont calls val
                     (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompWrite _ _ idxNum num dataArray idx Data array optMask pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompWriteNone num (dataArray : string) idxNum (idx  : Bit (Nat.log2_up idxNum) @# type) Data (array : Array num Data @# type)
                     (optMask : option (Array num Bool @# type)) (writeMap readMap : RegMapExpr type RegMapType) lret
                     (HMask : optMask = None)
                     updatedRegs readMapValOld readMapValUpds regVal
                     (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                     (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                     (HIn : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regVal)) updatedRegs)
                     regMapVal pred
                     (HUpdate : WfRegMapExpr (UpdRegMap dataArray pred
                                                        (fold_left (fun newArr i =>
                                                                      (UpdateArray newArr
                                                                                   (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                   :: nil))
                                                                                   (ReadArrayConst array i))
                                                                   ) (getFins num)
                                                                   (Var type (SyntaxKind (Array idxNum Data)) regVal))
                                                        writeMap) regMapVal)
                     cont regMap_cont calls val
                     (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompWrite _ _ idxNum num dataArray idx Data array optMask pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReqTrue num idxNum readRegName dataArray (idx : Bit (Nat.log2_up idxNum) @# type) k (isAddr : bool)
                           (writeMap : RegMapExpr type RegMapType) readMap lret cont
                           regMapVal pred
                           (HisAddr : isAddr = true)
                           (HWriteMap : WfRegMapExpr (UpdRegMap readRegName pred (Var type (SyntaxKind _) (evalExpr idx)) writeMap) regMapVal)
                           regMap_cont calls val
                           (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompSyncReadReq _ _ idxNum num readRegName dataArray idx k isAddr pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadReqFalse num idxNum readRegName dataArray (idx : Bit (Nat.log2_up idxNum) @# type) Data (isAddr : bool)
                            (writeMap : RegMapExpr type RegMapType) readMap lret cont
                            regMapVal pred
                            (HisAddr : isAddr = false)
                            updatedRegs readMapValOld readMapValUpds regV 
                            (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) updatedRegs)
                            (HWriteMap : WfRegMapExpr
                                           (UpdRegMap readRegName pred
                                                      (BuildArray (fun i : Fin.t num =>
                                                                     ReadArray
                                                                       (Var type _ regV)
                                                                       (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                                       Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil)))) writeMap) regMapVal)
                            regMap_cont calls val
                            (HSemCompActionT : SemCompActionT (cont regMapVal) regMap_cont calls val):
      SemCompActionT (@CompSyncReadReq _ _ idxNum num readRegName dataArray idx Data isAddr pred writeMap readMap lret cont) regMap_cont calls val
  | SemCompSyncReadResTrue num idxNum readRegName dataArray Data isAddr readMap lret cont
                           (HisAddr : isAddr = true)
                           updatedRegs readMapValOld readMapValUpds regVal idx
                           (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                           (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                           (HRegVal1 : In (readRegName, existT _ (SyntaxKind (Bit (Nat.log2_up idxNum))) idx) updatedRegs)
                           (HRegVal2 : In (dataArray, existT _ (SyntaxKind (Array idxNum Data)) regVal) updatedRegs)
                           (contArray : Expr type (SyntaxKind (Array num Data)))
                           (HContArray : contArray =
                                         BuildArray (fun i : Fin.t num =>
                                                       ReadArray
                                                         (Var type _ regVal)
                                                         (CABit Add (Var type (SyntaxKind _) idx ::
                                                                         Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                           regMap calls val
                           (HSemCompActionT : SemCompActionT (cont (evalExpr contArray)) regMap calls val):
      SemCompActionT (@CompSyncReadRes _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val
  | SemCompSyncReadResFalse num idxNum readRegName dataArray Data isAddr readMap lret cont
                            (HisAddr : isAddr = false)
                            updatedRegs readMapValOld readMapValUpds regVal
                            (HReadMap : SemRegMapExpr readMap (readMapValOld, readMapValUpds))
                            (HUpdatedRegs : PriorityUpds readMapValOld readMapValUpds updatedRegs)
                            (HIn1 : In (readRegName, (existT _ (SyntaxKind (Array num Data)) regVal)) updatedRegs)
                            regMap calls val
                            (HSemCompActionT : SemCompActionT (cont regVal) regMap calls val):
      SemCompActionT (@CompSyncReadRes _ _ idxNum num readRegName dataArray Data isAddr readMap lret cont) regMap calls val.

  Variable (k : Kind) (a : CompActionT type RegMapType k) (regInits : list RegInitT).
  
  Inductive SemCompTrace: RegsT -> list UpdRegsT -> list MethsT -> Prop :=
  | SemCompTraceInit (oInit : RegsT) (lupds : list UpdRegsT) (lcalls : list MethsT)
                     (HNoUpds : lupds = nil) (HNoCalls : lcalls = nil)
                     (HInitRegs : Forall2 regInit oInit regInits) :
      SemCompTrace oInit lupds lcalls
  | SemCompTraceCont (o o' : RegsT) (lupds lupds' : list UpdRegsT) (upds : UpdRegsT)
                     (lcalls lcalls' : list MethsT) (calls : MethsT) val
                     (HOldTrace : SemCompTrace o lupds lcalls)
                     (HSemAction : SemCompActionT a (o, upds) calls val)
                     (HNewUpds : lupds' = upds :: lupds)
                     (HNewCalls : lcalls' = calls :: lcalls)
                     (HPriorityUpds : PriorityUpds o upds o') :
      SemCompTrace o' lupds' lcalls'.
  
    
End Semantics.

Section EActionT_Semantics.
  Variable o : RegsT.

  Inductive UpdOrMeth : Type :=
  | Upd : RegT -> UpdOrMeth
  | Meth : MethT -> UpdOrMeth.

  Definition UpdOrMeths := list UpdOrMeth.

  Fixpoint UpdOrMeths_RegsT (uml : UpdOrMeths) : RegsT :=
    match uml with
    | um :: uml' =>
      match um with
      | Upd u => u :: (UpdOrMeths_RegsT uml')
      | Meth _ => (UpdOrMeths_RegsT uml')
      end
    | nil => nil
    end.

  Fixpoint UpdOrMeths_MethsT (uml : UpdOrMeths) : MethsT :=
    match uml with
    | um :: uml' =>
      match um with 
      | Upd _ => (UpdOrMeths_MethsT uml')
      | Meth m => m :: (UpdOrMeths_MethsT uml')
      end
    | nil => nil
    end.
  
  Inductive ESemAction :
    forall k, EActionT type k -> UpdOrMeths -> type k -> Prop :=
  | ESemCall (meth : string) (s : Kind * Kind) (marg : Expr type (SyntaxKind (fst s))) (mret : type (snd s)) (retK : Kind)
             (fret : type retK) (cont : type (snd s) -> EActionT type retK) (uml : UpdOrMeths) (auml : list UpdOrMeth)
             (HNewList : auml = (Meth (meth, existT SignT s (evalExpr marg, mret)) :: uml))
             (HESemAction : ESemAction (cont mret) uml fret) :
      ESemAction (EMCall meth s marg cont) auml fret
  | ESemLetExpr (k : FullKind) (e : Expr type k) (retK : Kind) (fret : type retK) (cont : fullType type k -> EActionT type retK)
                (uml : UpdOrMeths) (HESemAction : ESemAction (cont (evalExpr e)) uml fret) :
      ESemAction (ELetExpr e cont) uml fret
  | ESemLetAction (k : Kind) (ea : EActionT type k) (v : type k) (retK : Kind) (fret : type retK) (cont : type k -> EActionT type retK)
                  (newUml : list UpdOrMeth) (newUmlCont : list UpdOrMeth)
                  (HDisjRegs : DisjKey (UpdOrMeths_RegsT newUml) (UpdOrMeths_RegsT newUmlCont)) (HESemAction : ESemAction ea newUml v)
                  (HESemActionCont : ESemAction (cont v) newUmlCont fret)
                  (uNewUml : UpdOrMeths)
                  (HNewUml : uNewUml = newUml ++ newUmlCont) :
      ESemAction (ELetAction ea cont) uNewUml fret
  | ESemReadNondet (valueT : FullKind) (valueV : fullType type valueT) (retK : Kind) (fret : type retK)
                   (cont : fullType type valueT -> EActionT type retK) (newUml : UpdOrMeths)
                   (HESemAction : ESemAction (cont valueV) newUml fret):
      ESemAction (EReadNondet _ cont) newUml fret
  | ESemReadReg (r : string) (regT : FullKind) (regV : fullType type regT) (retK : Kind) (fret : type retK) (cont : fullType type regT -> EActionT type retK)
                (newUml : UpdOrMeths) (HRegVal : In (r, existT _ regT regV) o)
                (HESemAction : ESemAction (cont regV) newUml fret) :
      ESemAction (EReadReg r _ cont) newUml fret
  | ESemWriteReg (r : string) (k : FullKind) (e : Expr type k) (retK : Kind) (fret : type retK) (cont : EActionT type retK)
                 (newUml : list UpdOrMeth) (anewUml : list UpdOrMeth)
                 (HRegVal : In (r, k) (getKindAttr o))
                 (HDisjRegs : key_not_In r (UpdOrMeths_RegsT newUml))
                 (HANewUml : anewUml = (Upd (r, existT _ _ (evalExpr e))) :: newUml)
                 (HESemAction : ESemAction cont newUml fret):
      ESemAction (EWriteReg r e cont) anewUml fret
  | ESemIfElseTrue (p : Expr type (SyntaxKind Bool)) (k1 : Kind) (ea ea' : EActionT type k1) (r1 : type k1) (k2 : Kind) (cont : type k1 -> EActionT type k2)
                   (newUml1 newUml2 : list UpdOrMeth) (r2 : type k2)
                   (HDisjRegs : DisjKey (UpdOrMeths_RegsT newUml1) (UpdOrMeths_RegsT newUml2))
                   (HTrue : evalExpr p = true)
                   (HEAction : ESemAction ea  newUml1 r1)
                   (HESemAction : ESemAction (cont r1) newUml2 r2)
                   (unewUml : UpdOrMeths)
                   (HUNewUml : unewUml = newUml1 ++ newUml2) :
      ESemAction (EIfElse p ea ea' cont) unewUml r2
  | ESemIfElseFalse (p : Expr type (SyntaxKind Bool)) (k1 : Kind) (ea ea' : EActionT type k1) (r1 : type k1) (k2 : Kind) (cont : type k1 -> EActionT type k2)
                    (newUml1 newUml2 : list UpdOrMeth) (r2 : type k2)
                    (HDisjRegs : DisjKey (UpdOrMeths_RegsT newUml1) (UpdOrMeths_RegsT newUml2))
                    (HFalse : evalExpr p = false)
                    (HEAction : ESemAction ea' newUml1 r1)
                    (HESemAction : ESemAction (cont r1) newUml2 r2)
                    (unewUml : UpdOrMeths)
                    (HUNewUml : unewUml = newUml1 ++ newUml2) :
      ESemAction (EIfElse p ea ea' cont) unewUml r2
  | ESemSys (ls : list (SysT type)) (k : Kind) (cont : EActionT type k) (r : type k) (newUml : UpdOrMeths)
            (HESemAction : ESemAction cont newUml r) :
      ESemAction (ESys ls cont) newUml r
  | ESemReturn (k : Kind) (e : Expr type (SyntaxKind k)) (evale : fullType type (SyntaxKind k))
               (HEvalE : evale = evalExpr e)
               (newUml : UpdOrMeths)
               (HNewUml : newUml = nil) :
      ESemAction (EReturn e) newUml evale
  | ESemAsyncRead (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# type) (Data : Kind) (retK : Kind) (fret : type retK)
                  (newUml : UpdOrMeths) (regV : fullType type (SyntaxKind (Array idxNum Data)))
                  (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) o)
                  (cont : type (Array num Data) -> EActionT type retK)
                  (contArray : Expr type (SyntaxKind (Array num Data)))
                  (HContArray : contArray =
                                BuildArray (fun i : Fin.t num =>
                                              ReadArray
                                                (Var type _ regV)
                                                (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                  (HESemAction : ESemAction (cont (evalExpr contArray)) newUml fret):
      ESemAction (EAsyncRead idxNum num dataArray idx Data cont) newUml fret
  | ESemWriteSome (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# type) (Data : Kind) (array : Array num Data @# type)
                  (optMask : option (Array num Bool @# type)) (retK : Kind) (fret : type retK) (cont : EActionT type retK) (newUml : UpdOrMeths)
                  (anewUml : list UpdOrMeth) (regV : fullType type (SyntaxKind (Array idxNum Data))) (mask : Array num Bool @# type)
                  (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) o)
                  (HMask : optMask = Some mask)
                  (HANewUml : anewUml =
                              (Upd (dataArray, existT _ _
                                                      (evalExpr (fold_left (fun newArr i =>
                                                                      ITE
                                                                        (ReadArrayConst mask i)
                                                                        (UpdateArray newArr
                                                                                     (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                     :: nil))
                                                                                     (ReadArrayConst array i))
                                                                        newArr
                                                                           ) (getFins num)
                                                                           (Var type (SyntaxKind (Array idxNum Data)) regV))))) :: newUml)
                  (HDisjRegs : key_not_In dataArray (UpdOrMeths_RegsT newUml))
                  (HESemAction : ESemAction cont newUml fret) :
      ESemAction (EWrite idxNum dataArray idx array optMask cont) anewUml fret
  | ESemWriteNone (idxNum num : nat) (dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# type) (Data : Kind) (array : Array num Data @# type)
                  (optMask : option (Array num Bool @# type)) (retK : Kind) (fret : type retK) (cont : EActionT type retK) (newUml : UpdOrMeths)
                  (anewUml : list UpdOrMeth) (regV : fullType type (SyntaxKind (Array idxNum Data)))
                  (HRegVal : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) o)
                  (HMask : optMask = None)
                  (HANewUml : anewUml =
                              (Upd (dataArray, existT _ _
                                                      (evalExpr (fold_left (fun newArr i =>
                                                                      (UpdateArray newArr
                                                                                   (CABit Add (idx :: Const type (natToWord _ (proj1_sig (Fin.to_nat i)))
                                                                                                   :: nil))
                                                                                   (ReadArrayConst array i))
                                                                   ) (getFins num)
                                                                           (Var type (SyntaxKind (Array idxNum Data)) regV))))) :: newUml)
                  (HDisjRegs : key_not_In dataArray (UpdOrMeths_RegsT newUml))
                  (HESemAction : ESemAction cont newUml fret) :
      ESemAction (EWrite idxNum dataArray idx array optMask cont) anewUml fret
  | ESemSyncReadReqTrue (idxNum num : nat) (readRegName dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# type) (Data : Kind) (isAddr : bool)
                        (retK : Kind) (fret : type retK) (cont : EActionT type retK) (newUml : UpdOrMeths) (anewUml : list UpdOrMeth)
                        (HisAddr : isAddr = true)
                        (HRegVal : In (readRegName, (SyntaxKind (Bit (Nat.log2_up idxNum)))) (getKindAttr o))
                        (HDisjRegs : key_not_In readRegName (UpdOrMeths_RegsT newUml))
                        (HANewUml : anewUml = (Upd (readRegName, existT _ _ (evalExpr idx))) :: newUml)
                        (HESemAction : ESemAction cont newUml fret):
      ESemAction (ESyncReadReq idxNum num readRegName dataArray idx Data isAddr cont) anewUml fret
  | ESemSyncReadReqFalse (idxNum num : nat) (readRegName dataArray : string) (idx : Bit (Nat.log2_up idxNum) @# type) (Data : Kind) (isAddr : bool)
                         (retK : Kind) (fret : type retK) (cont : EActionT type retK) (newUml : UpdOrMeths) (anewUml : list UpdOrMeth)
                         (regV : fullType type (SyntaxKind (Array idxNum Data)))
                         (HisAddr : isAddr = false)
                         (HRegVal1 : In (readRegName, (SyntaxKind (Array num Data))) (getKindAttr o))
                         (HRegVal2 : In (dataArray, (existT _ (SyntaxKind (Array idxNum Data)) regV)) o)
                         (HDisjRegs : key_not_In readRegName (UpdOrMeths_RegsT newUml))
                         (HANewUml : anewUml =
                                     (Upd (readRegName, existT _ _
                                                               (evalExpr
                                                                  (BuildArray (fun i : Fin.t num =>
                                                     ReadArray
                                                       (Var type _ regV)
                                                       (CABit Add (Var type (SyntaxKind _) (evalExpr idx) ::
                                                                       Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))))) :: newUml)
                         (HESemAction : ESemAction cont newUml fret):
      ESemAction (ESyncReadReq idxNum num readRegName dataArray idx Data isAddr cont) anewUml fret
  | ESemSyncReadResTrue (idxNum num : nat) (readRegName dataArray : string) (Data : Kind) (isAddr : bool) (retK : Kind) (fret : type retK)
                        (regVal : fullType type (SyntaxKind (Array idxNum Data))) (idx : fullType type (SyntaxKind (Bit (Nat.log2_up idxNum))))
                        (cont : type (Array num Data) -> EActionT type retK)
                        (HisAddr : isAddr = true)
                        (HRegVal1 : In (readRegName, existT _ (SyntaxKind (Bit (Nat.log2_up idxNum))) idx) o)
                        (HRegVal2 : In (dataArray, existT _ (SyntaxKind (Array idxNum Data)) regVal) o)
                        (contArray : Expr type (SyntaxKind (Array num Data)))
                        (HContArray : contArray =
                                      BuildArray (fun i : Fin.t num =>
                                                       ReadArray
                                                         (Var type _ regVal)
                                                         (CABit Add (Var type (SyntaxKind _) idx ::
                                                                         Const type (natToWord _ (proj1_sig (Fin.to_nat i)))::nil))))
                        (newUml : UpdOrMeths) 
                        (HESemAction : ESemAction (cont (evalExpr contArray)) newUml fret):
      ESemAction (ESyncReadRes idxNum num readRegName dataArray Data isAddr cont)  newUml fret
  | ESemSyncReadResFalse (idxNum num : nat) (readRegName dataArray : string) (Data : Kind) (isAddr : bool) (retK : Kind) (fret : type retK)
                         (regVal : fullType type (SyntaxKind (Array num Data))) (cont : type (Array num Data) -> EActionT type retK)
                         (HisAddr : isAddr = false)
                         (HRegVal : In (readRegName, existT _ (SyntaxKind (Array num Data)) regVal) o)
                         (newUml : UpdOrMeths) 
                         (HESemAction : ESemAction (cont regVal) newUml fret):
      ESemAction (ESyncReadRes idxNum num readRegName dataArray Data isAddr cont) newUml fret.
                      
End EActionT_Semantics.


