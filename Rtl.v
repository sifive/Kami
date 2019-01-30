Require Import Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* TODO
 * System Calls
 * Dealing with Register Files
 *)

Inductive RtlExpr: Kind -> Type :=
| RtlReadReg k: string -> RtlExpr k
| RtlReadWire k: (string * list nat) -> RtlExpr k
| RtlConst k: ConstT k -> RtlExpr k
| RtlUniBool: UniBoolOp -> RtlExpr Bool -> RtlExpr Bool
| RtlCABool: CABoolOp -> list (RtlExpr Bool) -> RtlExpr Bool
| RtlUniBit n1 n2: UniBitOp n1 n2 -> RtlExpr (Bit n1) -> RtlExpr (Bit n2)
| RtlCABit n: CABitOp -> list (RtlExpr (Bit n)) -> RtlExpr (Bit n)
| RtlBinBit n1 n2 n3: BinBitOp n1 n2 n3 ->
                      RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                      RtlExpr (Bit n3)
| RtlBinBitBool n1 n2: BinBitBoolOp n1 n2 ->
                       RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                       RtlExpr Bool
| RtlITE k: RtlExpr Bool -> RtlExpr k -> RtlExpr k -> RtlExpr k
| RtlEq k: RtlExpr (k) -> RtlExpr (k) -> RtlExpr (Bool)
| RtlReadStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
                (e: RtlExpr (Struct fk fs)) i:
    RtlExpr (fk i)
| RtlBuildStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
                 (fv: forall i, RtlExpr (fk i)):
    RtlExpr (Struct fk fs)
| RtlReadArray n k: RtlExpr (Array n k) ->
                    RtlExpr (Bit (Nat.log2_up n)) ->
                    RtlExpr k
| RtlReadArrayConst n k: RtlExpr (Array n k) ->
                         Fin.t n ->
                         RtlExpr k
| RtlBuildArray n k: (Fin.t n -> RtlExpr k) -> RtlExpr (Array n k).

Inductive RtlSysT : Type :=
| RtlDispString : string -> RtlSysT
| RtlDispBool : RtlExpr Bool -> FullBitFormat -> RtlSysT
| RtlDispBit : forall n, RtlExpr (Bit n) -> FullBitFormat -> RtlSysT
| RtlDispStruct : forall n (fk : Fin.t n -> Kind) (fs : Fin.t n -> string),
    RtlExpr (Struct fk fs) -> (Fin.t n -> FullBitFormat) -> RtlSysT
| RtlDispArray : forall n k,
    RtlExpr (Array n k) -> FullBitFormat -> RtlSysT
| RtlFinish: RtlSysT.


Inductive RtlRegConst (x: Kind) :=
| NotInit
| SimpleInit (v: ConstT x)
| ArrayNotInit num k (pf: x = Array num k)
| ArrayInit num k (pf: x = Array num k) (val: ConstT k)
| ArrayHex num k (pf: x = Array num k) (file: string)
| ArrayBin num k (pf: x = Array num k) (file: string).

Definition getRtlRegInit (x: sigT optConstFullT): sigT RtlRegConst.
  refine (
      existT _ match projT1 x with
               | SyntaxKind k => k
               | NativeKind _ => Void
               end
             match projT2 x with
             | Uninit => NotInit _
             | Init y' => SimpleInit match y' in ConstFullT k return ConstT match k with
                                                                            | SyntaxKind k' => k'
                                                                            | _ => Void
                                                                            end with
                                     | SyntaxConst k c => c
                                     | _ => WO
                                     end
             | RegFileUninit num k pf => NotInit _
             | RegFileInit num k pf val =>
               @ArrayInit _ num k _ val
             | RegFileHex num k pf file =>
               @ArrayHex _ num k _ file
             | RegFileBin num k pf file =>
               @ArrayBin _ num k _ file
             end); rewrite pf; reflexivity.
Defined.

Record RtlModule :=
  { hiddenWires: list (string * list nat);
    regFiles: list (bool * RegFileBase);
    inputs: list (string * list nat * Kind);
    outputs: list (string * list nat * Kind);
    regInits: list (string * sigT RtlRegConst);
    regWrites: list (string * sigT RtlExpr);
    wires: list (string * list nat * sigT RtlExpr);
    sys: list (RtlExpr Bool * list RtlSysT)
  }.

Section BitOps.
  Local Fixpoint sumSizes n: (Fin.t n -> nat) -> nat :=
    match n return (Fin.t n -> nat) -> nat with
    | 0 => fun _ => 0
    | S m => fun sizes => sumSizes (fun x => sizes (Fin.FS x)) + sizes Fin.F1
    end.

  Local Fixpoint size (k: Kind) {struct k} :=
    match k with
    | Bool => 1
    | Bit n => n
    | Struct n fk fs =>
      sumSizes (fun i => size (fk i))
    | Array n k => n * size k
    end.

  (* ConstExtract: LSB, MIDDLE, MSB *)
  (* Concat: MSB, LSB *)

  Local Fixpoint concatStructExpr n {struct n}:
    forall (sizes: Fin.t n -> nat)
           (f: forall i, RtlExpr (Bit (sizes i))),
      RtlExpr (Bit (sumSizes sizes)) :=
    match n return forall
        (sizes: Fin.t n -> nat)
        (f: forall i, RtlExpr (Bit (sizes i))),
        RtlExpr (Bit (sumSizes sizes)) with
    | 0 => fun _ _ => RtlConst WO
    | S m => fun sizes f =>
               RtlBinBit
                 (Concat _ _) (f Fin.F1)
                 (@concatStructExpr m (fun x => (sizes (Fin.FS x))) (fun x => f (Fin.FS x)))
    end.

  Fixpoint rtlPack (k: Kind): RtlExpr k -> RtlExpr (Bit (size k)) :=
    match k return RtlExpr k -> RtlExpr (Bit (size k)) with
    | Bool => fun e => (RtlITE e (RtlConst (WO~1)%word) (RtlConst (WO~0)%word))
    | Bit n => fun e => e
    | Struct n fk fs =>
      fun e =>
        concatStructExpr (fun i => size (fk i))
                         (fun i => @rtlPack (fk i) (RtlReadStruct e i))
    | Array n k =>
      fun e =>
        (fix help i :=
           match i return RtlExpr (Bit (i * size k)) with
           | 0 => RtlConst WO
           | S m =>
             RtlBinBit
               (Concat (m * size k) (size k)) (help m)
               (@rtlPack k (RtlReadArray e (RtlConst (natToWord (Nat.log2_up n) m))))
           end) n
    end.

  Local Fixpoint sumSizesMsbs n (i: Fin.t n) {struct i}: (Fin.t n -> nat) -> nat :=
    match i in Fin.t n return (Fin.t n -> nat) -> nat with
    | Fin.F1 _ => fun _ => 0
    | Fin.FS m f => fun sizes => sumSizesMsbs f (fun j => sizes (Fin.FS j)) + sizes Fin.F1
    end.

  Local Lemma helper_sumSizes n (i: Fin.t n):
    forall (sizes: Fin.t n -> nat), sumSizes sizes = (sumSizes sizes - (sumSizesMsbs i sizes + sizes i)) + sizes i + sumSizesMsbs i sizes.
  Proof.
    induction i; simpl; intros; auto.
    - lia.
    - specialize (IHi (fun x => sizes (Fin.FS x))).
      lia.
  Qed.
  Local Lemma helper_array n (i: Fin.t n):
    forall size_k,
      n * size_k = (n * size_k - ((proj1_sig (Fin.to_nat i) * size_k) + size_k)) + size_k + (proj1_sig (Fin.to_nat i) * size_k).
  Proof.
    induction i; simpl; intros; auto.
    - lia.
    - case_eq (Fin.to_nat i); simpl; intros.
      rewrite H in *; simpl in *.
      rewrite IHi at 1.
      lia.
  Qed.
  
  Local Definition castBits ni no (pf: ni = no) (e: RtlExpr (Bit ni)) :=
    nat_cast (fun n => RtlExpr (Bit n)) pf e.

  Local Definition ConstExtract lsb n msb (e: RtlExpr (Bit (lsb + n + msb))): RtlExpr (Bit n) :=
      RtlUniBit (TruncMsb lsb n) (RtlUniBit (TruncLsb (lsb + n) msb) e).


  Fixpoint rtlUnpack (k: Kind): RtlExpr (Bit (size k)) -> RtlExpr k :=
    match k return RtlExpr (Bit (size k)) -> RtlExpr k with
    | Bool => fun e => RtlEq e (RtlConst (WO~1)%word)
    | Bit _ => fun e => e
    | Struct n fk fs =>
      fun e => RtlBuildStruct
                 _ _
                 (fun i =>
                    rtlUnpack
                      _
                      (ConstExtract
                         _ _ (sumSizesMsbs i (fun j => size (fk j)))
                         (@castBits _ _ (helper_sumSizes i (fun j => size (fk j))) e)))
    | Array n k =>
      fun e =>
        RtlBuildArray
          (fun i => rtlUnpack _ (ConstExtract _ _ (proj1_sig (Fin.to_nat i) * size k)
                                           (@castBits _ _ (helper_array _ _) e)))
    end.
End BitOps.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => RtlExpr (snd a))
          (name%string, _) value) (at level 50, only parsing) : rtl_struct_init_scope.
Delimit Scope rtl_struct_init_scope with rtl_init.

Notation getStructVal ls :=
  (RtlBuildStruct (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
                  (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j))
                  (fun k => Vector_nth_map2_r (@projT1 _ _) (fun x => RtlExpr (snd x)) ls k (projT2 (Vector.nth ls k)))).

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStructVal (Vector.cons _ s1%rtl_init _ ..
                             (Vector.cons _ sN%rtl_init _ (Vector.nil _)) ..))
  : rtl_expr_scope.

Delimit Scope rtl_expr_scope with rtl_expr.

Local Definition testStruct :=
  (STRUCT {
       "hello" :: Bit 10 ;
       "a" :: Bit 3 ;
       "b" :: Bit 5 ;
       "test" :: Bool }).

Local Definition testStructVal: RtlExpr testStruct :=
  (STRUCT {
       "hello" ::= RtlConst (natToWord _ 4) ;
       "a" ::= RtlConst (natToWord _ 23) ;
       "b" ::= RtlConst (natToWord _ 5) ;
       "test" ::= RtlConst true })%rtl_expr.

Local Ltac findStructIdx v f :=
  let idx := eval cbv in (Vector_find (fun x => getBool (string_dec (fst x) f%string)) v) in
      exact idx.

Local Ltac getStructList fs f := match fs with
                                 | (fun i: Fin.t _ =>
                                      fst (Vector.nth ?v i)) =>
                                   findStructIdx v f
                                 | _ => let y := eval hnf in fs in
                                            getStructList y f
                                 end.

Local Ltac getStructStringFn v f := match v with
                                    | Struct ?fk ?fs => getStructList fs f
                                    | _ => let y := eval hnf in v in
                                               getStructStringFn y f
                                    end.

Local Ltac getStructFull v f := match v with
                                | RtlExpr ?y => getStructStringFn y f
                                | _ => let y := eval hnf in v in
                                           getStructFull y f
                                end.



Notation "s @% f" := (RtlReadStruct s ltac:(let typeS := type of s in
                                            getStructFull typeS f)) (only parsing)
                     : rtl_expr_scope.

Local Definition testFieldAccess := 
  (testStructVal @% "hello")%rtl_expr.
