Require Export Bool String List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word Lib.VectorFacts Lib.EclecticLib.

Export Word.Notations.

Require Import Permutation.
Require Import ZArith.
Import ListNotations.

Global Set Implicit Arguments.
Global Set Asymmetric Patterns.

Global Open Scope word_scope.
Global Open Scope nat_scope.
Global Open Scope string_scope.
Global Open Scope vector_scope.
Global Open Scope list_scope.

Inductive Kind :=
| Bool    : Kind
| Bit     : nat -> Kind
| Struct  : forall n, (Fin.t n -> Kind) -> (Fin.t n -> string) -> Kind
| Array   : nat -> Kind -> Kind.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type): FullKind.

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstStruct n fk fs (fv: forall i, ConstT (fk i)): ConstT (@Struct n fk fs)
| ConstArray n k (fk: Fin.t n -> ConstT k): ConstT (Array n k).

Inductive ConstFullT: FullKind -> Type :=
| SyntaxConst k: ConstT k -> ConstFullT (SyntaxKind k)
| NativeConst t (c': t): ConstFullT (NativeKind t).

Coercion ConstBool : bool >-> ConstT.
Coercion ConstBit : word >-> ConstT.

Fixpoint getDefaultConst (k: Kind): ConstT k :=
  match k with
    | Bool => ConstBool false
    | Bit n => ConstBit (wzero n)
    | Struct n fk fs =>
      ConstStruct fk fs (fun i => getDefaultConst (fk i))
    | Array n k => ConstArray (fun _ => getDefaultConst k)
  end.

Inductive UniBoolOp: Set :=
| Neg: UniBoolOp.

Inductive CABoolOp: Set :=
| And: CABoolOp
| Or: CABoolOp
| Xor: CABoolOp.

Inductive UniBitOp: nat -> nat -> Set :=
| Inv n: UniBitOp n n
| TruncLsb lsb msb: UniBitOp (lsb + msb) lsb
| TruncMsb lsb msb: UniBitOp (lsb + msb) msb
| UAnd n: UniBitOp n 1
| UOr n: UniBitOp n 1
| UXor n: UniBitOp n 1.

Inductive BinSign := SignSS | SignSU | SignUU.

Inductive BinBitOp: nat -> nat -> nat -> Set :=
| Sub n: BinBitOp n n n
| Div n: BinBitOp n n n
| Rem n: BinBitOp n n n
| Sll n m: BinBitOp n m n
| Srl n m: BinBitOp n m n
| Sra n m: BinBitOp n m n
| Concat msb lsb: BinBitOp msb lsb (lsb + msb) (* MSB : n1, LSB : n2 *).

Inductive CABitOp: Set :=
| Add: CABitOp
| Mul: CABitOp
| Band: CABitOp
| Bor: CABitOp
| Bxor: CABitOp.

Inductive BinBitBoolOp: nat -> nat -> Set :=
| LessThan n: BinBitBoolOp n n.

Section Phoas.
  Variable ty: Kind -> Type.
  Definition fullType k := match k with
                             | SyntaxKind k' => ty k'
                             | NativeKind k' => k'
                           end.

  Inductive Expr: FullKind -> Type :=
  | Var k: fullType k -> Expr k
  | Const k: ConstT k -> Expr (SyntaxKind k)
  | UniBool: UniBoolOp -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool)
  | CABool: CABoolOp -> list (Expr (SyntaxKind Bool)) -> Expr (SyntaxKind Bool)
  | UniBit n1 n2: UniBitOp n1 n2 -> Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2))
  | CABit n: CABitOp -> list (Expr (SyntaxKind (Bit n))) -> Expr (SyntaxKind (Bit n))
  | BinBit n1 n2 n3: BinBitOp n1 n2 n3 ->
                     Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                     Expr (SyntaxKind (Bit n3))
  | BinBitBool n1 n2: BinBitBoolOp n1 n2 ->
                      Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                      Expr (SyntaxKind Bool)
  | ITE k: Expr (SyntaxKind Bool) -> Expr k -> Expr k -> Expr k
  | Eq k: Expr (SyntaxKind k) -> Expr (SyntaxKind k) -> Expr (SyntaxKind Bool)
  | ReadStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
               (e: Expr (SyntaxKind (Struct fk fs))) i:
      Expr (SyntaxKind (fk i))
  | BuildStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
                (fv: forall i, Expr (SyntaxKind (fk i))):
      Expr (SyntaxKind (Struct fk fs))
  | ReadArray n k: Expr (SyntaxKind (Array n k)) ->
                   Expr (SyntaxKind (Bit (Nat.log2_up n))) ->
                   Expr (SyntaxKind k)
  | ReadArrayConst n k: Expr (SyntaxKind (Array n k)) ->
                        Fin.t n ->
                        Expr (SyntaxKind k)
  | BuildArray n k: (Fin.t n -> Expr (SyntaxKind k)) -> Expr (SyntaxKind (Array n k)).

  Definition UpdateArray n k (e: Expr (SyntaxKind (Array n k)))
             (i: Expr (SyntaxKind (Bit (Nat.log2_up n))))
             (v: Expr (SyntaxKind k)) :=
    BuildArray (fun i' : Fin.t n =>
                  ITE (Eq i (Const (natToWord _ (proj1_sig (Fin.to_nat i'))))) v
                      (ReadArrayConst e i')).

  Definition UpdateArrayConst n k (e: Expr (SyntaxKind (Array n k)))
             (i: Fin.t n)
             (v: Expr (SyntaxKind k)) :=
    BuildArray (fun i' : Fin.t n =>
                  match Fin.eq_dec i i' with
                  | left _ => v
                  | right _ => ReadArrayConst e i'
                  end).

  Definition UpdateStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
             (e: Expr (SyntaxKind (Struct fk fs))) i (v: Expr (SyntaxKind (fk i))) :=
    BuildStruct fk fs (fun i' => match Fin.eq_dec i i' with
                                 | left pf => match pf in _ = Y return
                                                    Expr (SyntaxKind (fk Y)) with
                                              | eq_refl => v
                                              end
                                 | right _ => ReadStruct e i'
                                 end).

  Inductive LetExprSyntax k :=
  | NormExpr (e: Expr (SyntaxKind k)): LetExprSyntax k
  | LetE k' (e: LetExprSyntax k') (cont: ty k' -> LetExprSyntax k): LetExprSyntax k.

  Section BitOps.
    Definition castBits ni no (pf: ni = no) (e: Expr (SyntaxKind (Bit ni))) :=
      nat_cast (fun n => Expr (SyntaxKind (Bit n))) pf e.

    Definition Slt n (e1 e2: Expr (SyntaxKind (Bit (n + 1)))) :=
      Eq (Eq (UniBit (TruncMsb n 1) e1) (UniBit (TruncMsb n 1) e2)) (BinBitBool (LessThan _) e1 e2).

    Definition ConstExtract lsb n msb (e: Expr (SyntaxKind (Bit (lsb + n + msb)))): Expr (SyntaxKind (Bit n)) :=
      UniBit (TruncMsb lsb n) (UniBit (TruncLsb (lsb + n) msb) e).

    Definition ZeroExtend msb lsb (e: Expr (SyntaxKind (Bit lsb))): Expr (SyntaxKind (Bit (lsb + msb))) :=
      (BinBit (Concat msb lsb) (Const (wzero msb))) e.

    Definition SignExtend lsb msb: Expr (SyntaxKind (Bit lsb)) -> Expr (SyntaxKind (Bit (lsb + msb))).
      refine
        match lsb return Expr (SyntaxKind (Bit lsb)) -> Expr (SyntaxKind (Bit (lsb + msb))) with
        | 0 => fun _ => Const (wzero msb)
        | S m => fun e => BinBit (Concat msb (S m)) (ITE (Eq (UniBit (TruncMsb m 1)
                                                                     (castBits _ e))
                                                             (Const (WO~0)%word))
                                                         (Const (wzero msb))
                                                         (Const (wones msb))) e
        end; abstract lia.
    Defined.

    Fixpoint replicate sz (e: Expr (SyntaxKind (Bit sz))) n : Expr (SyntaxKind (Bit (n * sz))) :=
      match n with
      | 0 => Const WO
      | S m => BinBit (Concat (m * sz) sz) (replicate e m) e
      end.
    
    Definition ZeroExtendTruncLsb ni no (e: Expr (SyntaxKind (Bit ni))):
      Expr (SyntaxKind (Bit no)).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => UniBit (TruncLsb no (ni - no)) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition SignExtendTruncLsb ni no (e: Expr (SyntaxKind (Bit ni))):
      Expr (SyntaxKind (Bit no)).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend ni (no - ni) e)
        | right isGe => UniBit (TruncLsb no (ni - no)) (castBits _ e)
        end; abstract Omega.omega.
    Defined.

    Definition ZeroExtendTruncMsb ni no (e: Expr (SyntaxKind (Bit ni))):
      Expr (SyntaxKind (Bit no)).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => UniBit (TruncMsb (ni - no) no) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition SignExtendTruncMsb ni no (e: Expr (SyntaxKind (Bit ni))):
      Expr (SyntaxKind (Bit no)).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend ni (no - ni) e)
        | right isGe => UniBit (TruncMsb (ni - no) no) (castBits _ e)
        end; abstract Omega.omega.
    Defined.

    Fixpoint countLeadingZeros ni no: Expr (SyntaxKind (Bit ni)) -> Expr (SyntaxKind (Bit no)).
    refine
      match ni return Expr (SyntaxKind (Bit ni)) -> Expr (SyntaxKind (Bit no)) with
      | 0 => fun _ => Const (wzero _)
      | S m => fun e =>
                 ITE (Eq (UniBit (TruncMsb m 1) (castBits (eq_sym (Nat.add_1_r m)) e)) (Const WO~0))
                     (CABit Add [Const (natToWord _ 1);
                                     countLeadingZeros m _ (UniBit (TruncLsb m 1) (castBits (eq_sym (Nat.add_1_r m)) e))])
                     (Const (wzero _))
      end.
    Defined.

    Fixpoint sumSizes n: (Fin.t n -> nat) -> nat :=
      match n return (Fin.t n -> nat) -> nat with
      | 0 => fun _ => 0
      | S m => fun sizes => sumSizes (fun x => sizes (Fin.FS x)) + sizes Fin.F1
      end.

    Fixpoint size (k: Kind) {struct k} :=
      match k with
      | Bool => 1
      | Bit n => n
      | Struct n fk fs =>
        sumSizes (fun i => size (fk i))
      | Array n k => n * size k
      end.

    (* ConstExtract: LSB, MIDDLE, MSB *)
    (* Concat: MSB, LSB *)

    Fixpoint concatStructExpr n {struct n}:
      forall (sizes: Fin.t n -> nat)
             (f: forall i, Expr (SyntaxKind (Bit (sizes i)))),
        Expr (SyntaxKind (Bit (sumSizes sizes))) :=
      match n return forall
          (sizes: Fin.t n -> nat)
          (f: forall i, Expr (SyntaxKind (Bit (sizes i)))),
          Expr (SyntaxKind (Bit (sumSizes sizes))) with
      | 0 => fun _ _ => Const WO
      | S m => fun sizes f =>
                 BinBit
                   (Concat _ _) (f Fin.F1)
                   (@concatStructExpr m (fun x => (sizes (Fin.FS x))) (fun x => f (Fin.FS x)))
      end.

    Fixpoint pack (k: Kind): Expr (SyntaxKind k) -> Expr (SyntaxKind (Bit (size k))).
      refine
      match k return Expr (SyntaxKind k) -> Expr (SyntaxKind (Bit (size k))) with
      | Bool => fun e => (ITE e (Const (WO~1)%word) (Const (WO~0)%word))
      | Bit n => fun e => e
      | Struct n fk fs =>
        fun e =>
          concatStructExpr (fun i => size (fk i))
                           (fun i => @pack (fk i) (ReadStruct e i))
      | Array n k =>
        fun e =>
          (fix help i :=
             match i return Expr (SyntaxKind (Bit (i * size k))) with
             | 0 => Const WO
             | S m =>
               castBits _ (BinBit
                             (Concat (size k) (m * size k))
                             (@pack k (ReadArray e (Const (natToWord (Nat.log2_up n) m))))
                             (help m))
             end) n
      end; abstract lia.
    Defined.

    Fixpoint sumSizesMsbs n (i: Fin.t n) {struct i}: (Fin.t n -> nat) -> nat :=
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
        n * size_k = (proj1_sig (Fin.to_nat i) * size_k) + size_k + (n * size_k - ((proj1_sig (Fin.to_nat i) * size_k) + size_k)) .
    Proof.
      induction i; simpl; intros; auto.
      - lia.
      - case_eq (Fin.to_nat i); simpl; intros.
        rewrite H in *; simpl in *.
        rewrite IHi at 1.
        lia.
    Qed.

    Fixpoint unpack (k: Kind): Expr (SyntaxKind (Bit (size k))) -> Expr (SyntaxKind k) :=
      match k return Expr (SyntaxKind (Bit (size k))) -> Expr (SyntaxKind k) with
      | Bool => fun e => Eq e (Const (WO~1)%word)
      | Bit _ => fun e => e
      | Struct n fk fs =>
        fun e => BuildStruct
                   _ _
                   (fun i =>
                      unpack
                        _
                        (ConstExtract
                           _ _ (sumSizesMsbs i (fun j => size (fk j)))
                           (@castBits _ _ (helper_sumSizes i (fun j => size (fk j))) e)))
      | Array n k =>
        fun e =>
          BuildArray
            (fun i => unpack _ (ConstExtract (proj1_sig (Fin.to_nat i) * size k) _ _
                                             (@castBits _ _ (helper_array _ _) e)))
      end.
  End BitOps.
  
  Inductive BitFormat :=
  | Binary
  | Decimal
  | Hex.

  Definition FullBitFormat := (nat * BitFormat)%type.

  Inductive SysT: Type :=
  | DispString: string -> SysT
  | DispBool: Expr (SyntaxKind Bool) -> FullBitFormat -> SysT
  | DispBit: forall n, Expr (SyntaxKind (Bit n)) -> FullBitFormat -> SysT
  | DispStruct: forall n fk fs, Expr (SyntaxKind (@Struct n fk fs)) ->
                                  (Fin.t n -> FullBitFormat)
                                  -> SysT
  | DispArray: forall n k, Expr (SyntaxKind (Array n k)) -> FullBitFormat -> SysT
  | Finish: SysT.
  
  Inductive ActionT (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (SyntaxKind (fst s)) ->
      (ty (snd s) -> ActionT lretT) ->
      ActionT lretT
  | LetExpr k: Expr k -> (fullType k -> ActionT lretT) -> ActionT lretT
  | LetAction k: ActionT k -> (ty k -> ActionT lretT) -> ActionT lretT
  | ReadNondet k: (fullType k -> ActionT lretT) -> ActionT lretT
  | ReadReg (r: string) k: (fullType k -> ActionT lretT) -> ActionT lretT
  | WriteReg (r: string) k:
      Expr k -> ActionT lretT -> ActionT lretT
  | IfElse: Expr (SyntaxKind Bool) -> forall k,
                                        ActionT k ->
                                        ActionT k ->
                                        (ty k -> ActionT lretT) ->
                                        ActionT lretT
  | Assertion: Expr (SyntaxKind Bool) -> ActionT lretT -> ActionT lretT
  | Sys: list SysT -> ActionT lretT -> ActionT lretT
  | Return: Expr (SyntaxKind lretT) -> ActionT lretT.

  Fixpoint convertLetExprSyntax_ActionT k (e: LetExprSyntax k) :=
    match e in LetExprSyntax _ return ActionT k with
    | NormExpr e' => Return e'
    | LetE _ e' cont => LetAction (convertLetExprSyntax_ActionT e') (fun v => convertLetExprSyntax_ActionT (cont v))
    end.
End Phoas.


Definition Action (retTy : Kind) := forall ty, ActionT ty retTy.

Definition Signature := (Kind * Kind)%type.
Definition MethodT (sig : Signature) := forall ty, ty (fst sig) -> ActionT ty (snd sig).

Notation Void := (Bit 0).

Notation Attribute A := (string * A)%type (only parsing).
Notation optConstFullT := (fun x => option (ConstFullT x)).
Definition RegInitT := Attribute (sigT optConstFullT).
Definition DefMethT := Attribute (sigT MethodT).
Definition RuleT := Attribute (Action Void).

Inductive RegFileBase: Type :=
| RegFile (dataArray: string) (read: list string) (write: string) (IdxNum: nat) (Data: Kind)
          (init: option (ConstT Data))
| SyncRegFile (isAddr: bool)
              (dataArray: string) (read: list (string * string * string)) (write: string)
              (IdxNum: nat) (Data: Kind) (init: option (ConstT Data)).

Inductive BaseModule: Type :=
| BaseRegFile (rf: RegFileBase)
| BaseMod (regs: list RegInitT) (rules: list RuleT) (dms: list DefMethT).

Inductive Mod: Type :=
| Base (m: BaseModule): Mod
| HideMeth (m: Mod) (meth: string): Mod
| ConcatMod (m1 m2: Mod): Mod.

Coercion Base: BaseModule >-> Mod.

Notation getKindAttr ls := (map (fun x => (fst x, projT1 (snd x))) ls).

Notation "l '[=]' r" :=
  ((@Permutation _ (l) (r)))
    (at level 70, no associativity).

Definition getRegFileRegisters m :=
  match m with
  | RegFile dataArray read write IdxNum Data init =>
    (dataArray, existT optConstFullT (SyntaxKind (Array IdxNum Data))
                       match init with
                       | None => None
                       | Some init' => Some (SyntaxConst (ConstArray (fun _ => init')))
                       end) :: nil
  | SyncRegFile isAddr dataArray read write IdxNum Data init =>
    (dataArray, existT optConstFullT (SyntaxKind (Array IdxNum Data))
                       match init with
                       | None => None
                       | Some init' => Some (SyntaxConst (ConstArray (fun _ => init')))
                       end)
      ::
      map (fun x => (snd x, existT optConstFullT (SyntaxKind Data)
                                   match init with
                                   | None => None
                                   | Some init' => Some (SyntaxConst init')
                                   end)) read
  end.

Definition getRegisters m :=
  match m with
  | BaseRegFile rf => getRegFileRegisters rf
  | BaseMod regs rules dms => regs
  end.

Fixpoint getRules m :=
  match m with
  | BaseRegFile rf => nil
  | BaseMod regs rules dms => rules
  end.

(** Notations for Struct **)

Delimit Scope kami_expr_scope with kami_expr.

Notation "name :: ty" := (name%string,  ty) (only parsing) : kami_struct_scope.
Delimit Scope kami_struct_scope with kami_struct.

Notation getStruct ls :=
  (Struct (fun i => snd (Vector.nth ls i)) (fun j => fst (Vector.nth ls j))) (only parsing).

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStruct (Vector.cons _ s1%kami_struct _ .. (Vector.cons _ sN%kami_struct _ (Vector.nil _)) ..)).

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (snd a)))
          (name%string, _) value) (at level 50) : kami_struct_init_scope.
Delimit Scope kami_struct_init_scope with struct_init.

Notation getStructVal ls :=
  (BuildStruct (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
               (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j))
               (fun k => Vector_nth_map2_r (@projT1 _ _) (fun x => Expr _ (SyntaxKind (snd x))) ls k (projT2 (Vector.nth ls k)))).

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStructVal (Vector.cons _ s1%struct_init _ ..
                             (Vector.cons _ sN%struct_init _ (Vector.nil _)) ..))
  : kami_expr_scope.


Definition WriteRq IdxNum Data := STRUCT { "addr" :: Bit (Nat.log2_up IdxNum) ;
                                           "data" :: Data }.

Definition getRegFileMethods m :=
  match m with
  | RegFile dataArray read write IdxNum Data init =>
    (write, existT MethodT (WriteRq IdxNum Data, Void)
                   (fun ty x =>
                      ReadReg dataArray _
                              (fun val =>
                                 WriteReg dataArray
                                          (UpdateArray (Var ty _ val)
                                                       (ReadStruct (Var ty (SyntaxKind _) x)
                                                                   Fin.F1)
                                                       (ReadStruct (Var ty (SyntaxKind _) x)
                                                                   (Fin.FS Fin.F1)))
                                          (Return (Const _ WO)))))
      :: (map (fun x =>
                 (x,
                  existT MethodT (Bit (Nat.log2_up IdxNum), Data)
                         (fun ty x =>
                            ReadReg dataArray (SyntaxKind (Array IdxNum Data))
                                    (fun val =>
                                       ReadReg dataArray _
                                               (fun val =>
                                                  Return (ReadArray
                                                            (Var ty _ val)
                                                            (Var ty (SyntaxKind _) x)))))))
              read)
  | SyncRegFile isAddr dataArray read write IdxNum Data init =>
    (write, existT MethodT (WriteRq IdxNum Data, Void)
                   (fun ty x =>
                      ReadReg dataArray _
                              (fun val =>
                                 WriteReg dataArray
                                          (UpdateArray (Var ty _ val)
                                                       (ReadStruct (Var ty (SyntaxKind _) x)
                                                                   Fin.F1)
                                                       (ReadStruct (Var ty (SyntaxKind _) x)
                                                                   (Fin.FS Fin.F1)))
                                          (Return(Const _ WO)))))
      ::
      if isAddr
      then
      ((map (fun r =>
               (fst (fst r),
                existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                       (fun ty x =>
                          WriteReg (snd r) (Var ty (SyntaxKind _) x)
                                   (Return (Const _ WO)))))) read)
        ++
        (map (fun r =>
                (snd (fst r),
                 existT MethodT (Void, Data)
                        (fun ty x =>
                           ReadReg (snd r) (SyntaxKind (Bit (Nat.log2_up IdxNum)))
                                   (fun idx =>
                                      ReadReg dataArray (SyntaxKind (Array IdxNum Data))
                                              (fun val =>
                                                 Return (ReadArray
                                                           (Var ty _ val)
                                                           (Var ty (SyntaxKind _) idx)))))))
             read)
      else
        ((map (fun r =>
                 (fst (fst r),
                  existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                         (fun ty x =>
                            ReadReg (snd r) (SyntaxKind (Bit (Nat.log2_up IdxNum)))
                                    (fun data =>
                                       WriteReg (snd r) (Var ty (SyntaxKind _) data)
                                                (Return (Const _ WO)))))) read))
          ++
          (map (fun r =>
                  (snd (fst r),
                   existT MethodT (Void, Data)
                          (fun ty x =>
                             ReadReg (snd r) (SyntaxKind Data)
                                     (fun data =>
                                        Return (Var ty _ data)))))
               read)
  end.

Fixpoint getMethods m :=
  match m with
  | BaseRegFile rf => getRegFileMethods rf
  | BaseMod regs rules dms => dms
  end.

Fixpoint getAllRegisters m :=
  match m with
  | Base m' => getRegisters m'
  | HideMeth m' s => getAllRegisters m'
  | ConcatMod m1 m2 => getAllRegisters m1 ++ getAllRegisters m2
  end.

Fixpoint getAllRules m :=
  match m with
  | Base m' => getRules m'
  | HideMeth m' s => getAllRules m'
  | ConcatMod m1 m2 => getAllRules m1 ++ getAllRules m2
  end.

Fixpoint getAllMethods m :=
  match m with
  | Base m' => getMethods m'
  | HideMeth m' s => getAllMethods m'
  | ConcatMod m1 m2 => getAllMethods m1 ++ getAllMethods m2
  end.

Fixpoint getHidden m :=
  match m with
  | Base _ => []
  | ConcatMod m1 m2 => getHidden m1 ++ getHidden m2
  | HideMeth m' s => s :: getHidden m'
  end.

Fixpoint type (k: Kind): Type :=
  match k with
    | Bool => bool
    | Bit n => word n
    | Struct n fk fs => forall i, type (fk i)
    | Array n k' => Fin.t n -> type k'
  end.

Section WfBaseMod.
  Variable m: BaseModule.
  
  Inductive WfActionT: forall lretT, ActionT type lretT -> Prop :=
  | WfMCall meth s e lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (MCall meth s e c)
  | WfLetExpr k (e: Expr type k) lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (LetExpr e c)
  | WfLetAction k (a: ActionT type k) lretT c: WfActionT a -> (forall v, WfActionT (c v)) -> @WfActionT lretT (LetAction a c)
  | WfReadNondet k lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (ReadNondet k c)
  | WfReadReg r k lretT c: (forall v, WfActionT (c v)) -> In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (ReadReg r k c)
  | WfWriteReg r k (e: Expr type k) lretT c: WfActionT c  -> In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (WriteReg r e c)
  | WfIfElse p k (atrue: ActionT type k) afalse lretT c: (forall v, WfActionT (c v)) -> WfActionT atrue -> WfActionT afalse -> @WfActionT lretT (IfElse p atrue afalse c)
  | WfAssertion (e: Expr type (SyntaxKind Bool)) lretT c: WfActionT c -> @WfActionT lretT (Assertion e c)
  | WfSys ls lretT c: WfActionT c -> @WfActionT lretT (Sys ls c)
  | WfReturn lretT e: @WfActionT lretT (Return e).

  Definition WfBaseModule :=
    (forall rule, In rule (getRules m) -> WfActionT (snd rule type)) /\
    (forall meth, In meth (getMethods m) -> forall v, WfActionT (projT2 (snd meth) type v)) /\
    NoDup (map fst (getMethods m)) /\ NoDup (map fst (getRegisters m)) /\ NoDup (map fst (getRules m)).
  
  Lemma WfLetExprSyntax k (e: LetExprSyntax type k): WfActionT (convertLetExprSyntax_ActionT e).
  Proof.
    induction e; constructor; auto.
  Qed.
End WfBaseMod.

Inductive WfConcatActionT : forall lretT, ActionT type lretT -> Mod -> Prop :=
| WfConcatMCall meth s e lretT c m' :(forall v, WfConcatActionT (c v) m') -> ~In meth (getHidden m') -> @WfConcatActionT lretT (MCall meth s e c) m'
| WfConcatLetExpr k (e : Expr type k) lretT c m' : (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (LetExpr e c) m'
| WfConcatLetAction k (a : ActionT type k) lretT c m' : WfConcatActionT a m' -> (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (LetAction a c) m'
| WfConcatReadNondet k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (ReadNondet k c) m'
| WfConcatReadReg r k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (ReadReg r k c) m'
| WfConcatWriteReg r k (e: Expr type k) lretT c m': WfConcatActionT c m' -> @WfConcatActionT lretT (WriteReg r e c) m'
| WfConcatIfElse p k (atrue: ActionT type k) afalse lretT c m': (forall v, WfConcatActionT (c v) m') -> WfConcatActionT atrue m' -> WfConcatActionT afalse m' -> @WfConcatActionT lretT (IfElse p atrue afalse c) m'
| WfConcatAssertion (e: Expr type (SyntaxKind Bool)) lretT c m': WfConcatActionT c m' -> @WfConcatActionT lretT (Assertion e c) m'
| WfConcatSys ls lretT c m': WfConcatActionT c m' -> @WfConcatActionT lretT (Sys ls c) m'
| WfConcatReturn lretT e m': @WfConcatActionT lretT (Return e) m'.

Definition WfConcat m m' :=
  (forall rule, In rule (getAllRules m) -> WfConcatActionT (snd rule type) m') /\
  (forall meth, In meth (getAllMethods m) -> forall v, WfConcatActionT (projT2 (snd meth) type v) m').

Inductive WfMod: Mod -> Prop :=
| BaseWf m (HWfBaseModule: WfBaseModule m): WfMod (Base m)
| HideMethWf m s (HHideWf: In s (map fst (getAllMethods m))) (HWf: WfMod m): WfMod (HideMeth m s)
| ConcatModWf m1 m2 (HDisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2))
              (HDisjRules: DisjKey (getAllRules m1) (getAllRules m2))
              (HDisjMeths: DisjKey (getAllMethods m1) (getAllMethods m2))
              (HWf1: WfMod m1) (HWf2: WfMod m2)(WfConcat1: WfConcat m1 m2)
              (WfConcat2 : WfConcat m2 m1): WfMod (ConcatMod m1 m2).

Record ModWf : Type := { module :> Mod;
                         wfMod : WfMod module }.

Record ModWfOrd := { modWf :> ModWf ;
                     modOrd : list string }.

Record BaseModuleWf :=
  { baseModule :> BaseModule ;
    wfBaseModule : WfBaseModule baseModule }.

Record BaseModuleWfOrd :=
  { baseModuleWf :> BaseModuleWf ;
    baseModuleOrd : list string }.

Definition getModWf (m: BaseModuleWf) :=
  {| module := m;
     wfMod := BaseWf (wfBaseModule m) |}.

Definition getModWfOrd (m: BaseModuleWfOrd) :=
  {| modWf := getModWf m;
     modOrd := baseModuleOrd m |}.

Coercion getModWf: BaseModuleWf >-> ModWf.
Coercion getModWfOrd: BaseModuleWfOrd >-> ModWfOrd.


Ltac Struct_neq :=
  match goal with
  | |- Struct _ _ <> Struct _ _ =>
    let H := fresh in intro H;
                      injection H;
                      intros;
                      repeat (existT_destruct Nat.eq_dec)
  end.

Ltac discharge_wf :=
  repeat match goal with
         | |- @WfMod _ => constructor_simpl
         | |- @WfConcat _ _ => constructor_simpl
         | |- _ /\ _ => constructor_simpl
         | |- @WfConcatActionT _ _ _ => constructor_simpl
         | |- @WfBaseModule _ => constructor_simpl
         | |- @WfActionT _ _ (convertLetExprSyntax_ActionT ?e) => apply WfLetExprSyntax
         | |- @WfActionT _ _ _ => constructor_simpl
         | |- NoDup _ => constructor_simpl
         | H: _ \/ _ |- _ => destruct H; subst; simpl
         end; repeat (discharge_DisjKey || tauto || congruence);
  try (discharge_DisjKey || tauto || congruence).


Section NoCallActionT.
  Variable ls: list string.
  
  Inductive NoCallActionT: forall k, ActionT type k -> Prop :=
  | NoCallMCall meth s e lretT c: ~ In meth ls -> (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (MCall meth s e c)
  | NoCallLetExpr k (e: Expr type k) lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (LetExpr e c)
  | NoCallLetAction k (a: ActionT type k) lretT c: NoCallActionT a -> (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (LetAction a c)
  | NoCallReadNondet k lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (ReadNondet k c)
  | NoCallReadReg r k lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (ReadReg r k c)
  | NoCallWriteReg r k (e: Expr type k) lretT c: NoCallActionT c  -> @NoCallActionT lretT (WriteReg r e c)
  | NoCallIfElse p k (atrue: ActionT type k) afalse lretT c: (forall v, NoCallActionT (c v)) -> NoCallActionT atrue -> NoCallActionT afalse -> @NoCallActionT lretT (IfElse p atrue afalse c)
  | NoCallAssertion (e: Expr type (SyntaxKind Bool)) lretT c: NoCallActionT c -> @NoCallActionT lretT (Assertion e c)
  | NoCallSys ls lretT c: NoCallActionT c -> @NoCallActionT lretT (Sys ls c)
  | NoCallReturn lretT e: @NoCallActionT lretT (Return e).
End NoCallActionT.

Section NoSelfCallBaseModule.
  Variable m: BaseModule.
  
  Definition NoSelfCallRuleBaseModule (rule : Attribute (Action Void)) :=
    NoCallActionT (map fst (getMethods m)) (snd rule type).
  
  Definition NoSelfCallRulesBaseModule :=
    forall rule, In rule (getRules m) ->
                 NoCallActionT (map fst (getMethods m)) (snd rule type).
  
  Definition NoSelfCallMethsBaseModule :=
    forall meth, In meth (getMethods m) ->
                 forall (arg: type (fst (projT1 (snd meth)))), NoCallActionT (map fst (getMethods m)) (projT2 (snd meth) type arg).

  Definition NoSelfCallBaseModule :=
    NoSelfCallRulesBaseModule /\ NoSelfCallMethsBaseModule.
End NoSelfCallBaseModule.







(* Semantics *)

Definition Kind_dec (k1: Kind): forall k2, {k1 = k2} + {k1 <> k2}.
Proof.
  induction k1; intros; destruct k2; try (right; (abstract congruence)).
  - left; reflexivity.
  - destruct (Nat.eq_dec n n0); [left; subst; reflexivity | right; abstract congruence].
  - destruct (Nat.eq_dec n n0).
    + subst.
      induction n0.
      * left.
        f_equal; extensionality x; apply Fin.case0; exact x.
      * specialize (IHn0 (fun i => s (Fin.FS i)) (fun i => k (Fin.FS i))
                         (fun i => H (Fin.FS i)) (fun i => k0 (Fin.FS i))
                         (fun i => s0 (Fin.FS i))).
        destruct IHn0.
        -- injection e.
           intros.
           repeat (existT_destruct Nat.eq_dec).
           destruct (string_dec (s Fin.F1) (s0 Fin.F1)).
           ++ destruct (H Fin.F1 (k0 Fin.F1)).
              ** left; f_equal; extensionality x; apply (Fin.caseS' x); try assumption;
                   apply equal_f; assumption.
              ** right.
                 Struct_neq.
                 apply (n eq_refl).
           ++ right.
              Struct_neq.
              apply (n eq_refl).
        -- right.
           Struct_neq.
           apply (n eq_refl).
    + right.
      intro.
      injection H0 as H0.
      intros.
      apply (n1 H0).
  - destruct (Nat.eq_dec n n0).
    + subst; destruct (IHk1 k2).
      * left; subst; reflexivity.
      * right; intro.
        injection H as H.
        apply (n H).
    + right.
      intro.
      injection H as H.
      apply (n1 H).
Defined.

Lemma Signature_dec: forall (s1 s2: Signature), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality; apply Kind_dec.
Defined.

Lemma isEq k: forall (e1: type k) (e2: type k),
    {e1 = e2} + {e1 <> e2}.
Proof.
  induction k; intros.
  - apply bool_dec.
  - apply weq.
  - induction n.
    + left.
      extensionality x.
      apply Fin.case0.
      apply x.
    + destruct (IHn (fun i => k (Fin.FS i)) (fun i => X (Fin.FS i)) (fun i => s (Fin.FS i))
                    (fun i => e1 (Fin.FS i)) (fun i => e2 (Fin.FS i))).
      * destruct (X Fin.F1 (e1 Fin.F1) (e2 Fin.F1)).
        -- left.
           extensionality x.
           apply (Fin.caseS' x); try assumption; apply equal_f_dep; assumption.
        -- right; intro; subst.
           apply (n0 eq_refl).
      * right; intro; subst.
        apply (n0 eq_refl).
  - induction n.
    + left.
      extensionality x.
      apply Fin.case0.
      apply x.
    + simpl in *.
      destruct (IHn (fun i => e1 (Fin.FS i)) (fun i => e2 (Fin.FS i))).
      * destruct (IHk (e1 Fin.F1) (e2 Fin.F1)).
        -- left.
           extensionality x.
           apply (Fin.caseS' x); try assumption; apply equal_f; assumption.
        -- right; intro; subst.
           apply (n0 eq_refl).
      * right; intro; subst.
        apply (n0 eq_refl).
Defined.

Definition evalUniBool (op: UniBoolOp) : bool -> bool :=
  match op with
    | Neg => negb
  end.

Definition evalCABool (op: CABoolOp) (ws : list bool) : bool :=
  match op with
    | And => fold_left andb ws true
    | Or => fold_left orb ws false
    | Xor => fold_left xorb ws false
  end.

Fixpoint fold_left_word (f: bool -> bool -> bool) sz (w: word sz) init: bool :=
  match w with
  | WO => init
  | WS b _ rst => fold_left_word f rst (f init b)
  end.

Fixpoint fold_right_word (f: bool -> bool -> bool) init sz (w: word sz): bool :=
  match w with
  | WO => init
  | WS b _ rst => f b (fold_right_word f init rst)
  end.

Definition evalUniBit n1 n2 (op: UniBitOp n1 n2): word n1 -> word n2 :=
  match op with
  | Inv n => (@wnot n)
  | TruncLsb lsb msb => split1 lsb msb
  | TruncMsb lsb msb => split2 lsb msb
  | UAnd n => fun w => WS (fold_left_word andb w true) WO
  | UOr n => fun w => WS (fold_left_word orb w false) WO
  | UXor n => fun w => WS (fold_left_word xorb w false) WO
  end.

Definition wdivN := wordBinN Nat.div.
Definition wremN := wordBinN Nat.modulo.

Definition evalBinBit n1 n2 n3 (op: BinBitOp n1 n2 n3)
  : word n1 -> word n2 -> word n3 :=
  match op with
    | Sub n => @wminus n
    | Div n => @wdivN n
    | Rem n => @wremN n
    | Sll n m => (fun x y => wlshift x (wordToNat y))
    | Srl n m => (fun x y => wrshift x (wordToNat y))
    | Sra n m => (fun x y => wrshifta x (wordToNat y))
    | Concat n1 n2 => fun x y => (Word.combine y x)
  end.

Definition evalCABit n (op: CABitOp) (ls: list (word n)): word n :=
  match op with
    | Add => fold_left (@wplus n) ls (wzero n)
    | Mul => fold_left (@wmult n) ls (natToWord n 1)
    | Band => fold_left (@wand n) ls (wones n)
    | Bor => fold_left (@wor n) ls (wzero n)
    | Bxor => fold_left (@wxor n) ls (wzero n)
  end.

Definition evalBinBitBool n1 n2 (op: BinBitBoolOp n1 n2)
  : word n1 -> word n2 -> bool :=
  match op with
    | LessThan n => fun a b => getBool (@wlt_dec n a b)
  end.

Fixpoint evalConstT k (e: ConstT k): type k :=
  match e in ConstT k return type k with
    | ConstBool b => b
    | ConstBit n w => w
    | ConstStruct n fk fs fv => fun i => evalConstT (fv i)
    | ConstArray n k' fv => fun i => evalConstT (fv i)
  end.

Definition evalConstFullT k (e: ConstFullT k) :=
  match e in ConstFullT k return fullType type k with
    | SyntaxConst k' c' => evalConstT c'
    | NativeConst t c' => c'
  end.

(* maps register names to the values which they currently hold *)
Notation RegT := (Attribute (sigT (fullType type))).
Definition RegsT := (list RegT).

(* a pair of the value sent to a method call and the value it returned *)
Definition SignT k := (type (fst k) * type (snd k))%type.

(* a list of simulatenous method call actions made during a single step *)
Notation MethT := (Attribute (sigT SignT)).
Definition MethsT := (list MethT).


Section Semantics.
  Fixpoint natToFin n (i: nat): Fin.t (S n) :=
    match i with
    | 0 => Fin.F1
    | S i' => match n with
             | 0 => Fin.F1
             | S n' => Fin.FS (natToFin n' i')
             end
    end.


  Fixpoint evalExpr exprT (e: Expr type exprT): fullType type exprT :=
    match e in Expr _ exprT return fullType type exprT with
      | Var _ v => v
      | Const _ v => evalConstT v
      | UniBool op e1 => (evalUniBool op) (@evalExpr _ e1)
      | CABool op es => evalCABool op (map (@evalExpr _) es)
      | UniBit n1 n2 op e1 => (evalUniBit op) (@evalExpr _ e1)
      | BinBit n1 n2 n3 op e1 e2 => (evalBinBit op) (@evalExpr _ e1) (@evalExpr _ e2)
      | CABit n op es => evalCABit op (map (@evalExpr _) es)
      | BinBitBool n1 n2 op e1 e2 => (evalBinBitBool op) (@evalExpr _ e1) (@evalExpr _ e2)
      | ITE _ p e1 e2 => if @evalExpr _ p
                         then @evalExpr _ e1
                         else @evalExpr _ e2
      | Eq _ e1 e2 => getBool (isEq _ (@evalExpr _ e1) (@evalExpr _ e2))
      | ReadStruct n fk fs e i => (@evalExpr _ e) i
      | BuildStruct n fk fs fv => fun i => @evalExpr _ (fv i)
      | ReadArray n k fv i =>
        match n return (Fin.t n -> fullType type (SyntaxKind k)) ->
                       fullType type (SyntaxKind k) with
        | 0 => fun _ => evalConstT (getDefaultConst k)
        | S m => fun fv => fv (natToFin m (wordToNat (@evalExpr _ i)))
        end (@evalExpr _ fv)
      | ReadArrayConst n k fv i =>
        (@evalExpr _ fv) i
      | BuildArray n k fv => fun i => @evalExpr _ (fv i)
    end.
  
  Fixpoint evalLetExpr k (e: LetExprSyntax type k) :=
    match e in LetExprSyntax _ _ return type k with
    | NormExpr e' => evalExpr e'
    | LetE _ e' cont => evalLetExpr (cont (evalLetExpr e'))
    end.

  Variable o: RegsT.

  Inductive SemAction:
    forall k, ActionT type k -> RegsT -> RegsT -> MethsT -> type k -> Prop :=
  | SemMCall
      meth s (marg: Expr type (SyntaxKind (fst s)))
      (mret: type (snd s))
      retK (fret: type retK)
      (cont: type (snd s) -> ActionT type retK)
      readRegs newRegs (calls: MethsT) acalls
      (HAcalls: acalls = (meth, (existT _ _ (evalExpr marg, mret))) :: calls)
      (HSemAction: SemAction (cont mret) readRegs newRegs calls fret):
      SemAction (MCall meth s marg cont) readRegs newRegs acalls fret
  | SemLetExpr
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) readRegs newRegs calls
      (HSemAction: SemAction (cont (evalExpr e)) readRegs newRegs calls fret):
      SemAction (LetExpr e cont) readRegs newRegs calls fret
  | SemLetAction
      k (a: ActionT type k) (v: type k) retK (fret: type retK)
      (cont: type k -> ActionT type retK)
      readRegs newRegs readRegsCont newRegsCont calls callsCont
      (HDisjRegs: DisjKey newRegs newRegsCont)
      (HSemAction: SemAction a readRegs newRegs calls v)
      (HSemActionCont: SemAction (cont v) readRegsCont newRegsCont callsCont fret)
      uReadRegs uNewRegs uCalls
      (HReadRegs: uReadRegs = readRegs ++ readRegsCont)
      (HNewRegs: uNewRegs = newRegs ++ newRegsCont)
      (HCalls: uCalls = calls ++ callsCont):
      SemAction (LetAction a cont) uReadRegs uNewRegs uCalls fret
  | SemReadNondet
      valueT (valueV: fullType type valueT)
      retK (fret: type retK) (cont: fullType type valueT -> ActionT type retK)
      readRegs newRegs calls
      (HSemAction: SemAction (cont valueV) readRegs newRegs calls fret):
      SemAction (ReadNondet _ cont) readRegs newRegs calls fret
  | SemReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      readRegs newRegs calls areadRegs
      (HRegVal: In (r, existT _ regT regV) o)
      (HSemAction: SemAction (cont regV) readRegs newRegs calls fret)
      (HNewReads: areadRegs = (r, existT _ regT regV) :: readRegs):
      SemAction (ReadReg r _ cont) areadRegs newRegs calls fret
  | SemWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) readRegs newRegs calls anewRegs
      (HRegVal: In (r, k) (getKindAttr o))
      (HDisjRegs: key_not_In r newRegs)
      (HANewRegs: anewRegs = (r, (existT _ _ (evalExpr e))) :: newRegs)
      (HSemAction: SemAction cont readRegs newRegs calls fret):
      SemAction (WriteReg r e cont) readRegs anewRegs calls fret
  | SemIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2  newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HTrue: evalExpr p = true)
      (HAction: SemAction a readRegs1 newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs = readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs = newRegs1 ++ newRegs2)
      (HUCalls: ucalls = calls1 ++ calls2) :
      SemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | SemIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2 newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HFalse: evalExpr p = false)
      (HAction: SemAction a' readRegs1 newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs = readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs = newRegs1 ++ newRegs2)
      (HUCalls: ucalls = calls1 ++ calls2):
      SemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | SemAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2) readRegs2 newRegs2 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HSemAction: SemAction cont readRegs2 newRegs2 calls2 r2):
      SemAction (Assertion p cont) readRegs2 newRegs2 calls2 r2
  | SemDisplay
      (ls: list (SysT type)) k (cont: ActionT type k)
      r readRegs newRegs calls
      (HSemAction: SemAction cont readRegs newRegs calls r):
      SemAction (Sys ls cont) readRegs newRegs calls r
  | SemReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e)
      readRegs newRegs calls
      (HReadRegs: readRegs = nil)
      (HNewRegs: newRegs = nil)
      (HCalls: calls = nil) :
      SemAction (Return e) readRegs newRegs calls evale.


  Inductive PSemAction:
    forall k, ActionT type k -> RegsT -> RegsT -> MethsT -> type k -> Prop :=
  | PSemMCall
      meth s (marg: Expr type (SyntaxKind (fst s)))
      (mret: type (snd s))
      retK (fret: type retK)
      (cont: type (snd s) -> ActionT type retK)
      readRegs newRegs (calls: MethsT) acalls
      (HAcalls: acalls [=] (meth, (existT _ _ (evalExpr marg, mret))) :: calls)
      (HPSemAction: PSemAction (cont mret) readRegs newRegs calls fret):
      PSemAction (MCall meth s marg cont) readRegs newRegs acalls fret
  | PSemLetExpr
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) readRegs newRegs calls
      (HPSemAction: PSemAction (cont (evalExpr e)) readRegs newRegs calls fret):
      PSemAction (LetExpr e cont) readRegs newRegs calls fret
  | PSemLetAction
      k (a: ActionT type k) (v: type k) retK (fret: type retK)
      (cont: type k -> ActionT type retK)
      readRegs newRegs readRegsCont newRegsCont calls callsCont
      (HDisjRegs: DisjKey newRegs newRegsCont)
      (HPSemAction: PSemAction a readRegs newRegs calls v)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs ++ readRegsCont)
      (HUNewRegs: unewRegs [=] newRegs ++ newRegsCont)
      (HUCalls: ucalls [=] calls ++ callsCont)
      (HPSemActionCont: PSemAction (cont v) readRegsCont newRegsCont callsCont fret):
      PSemAction (LetAction a cont) (ureadRegs) (unewRegs)
                (ucalls) fret
  | PSemReadNondet
      valueT (valueV: fullType type valueT)
      retK (fret: type retK) (cont: fullType type valueT -> ActionT type retK)
      readRegs newRegs calls
      (HPSemAction: PSemAction (cont valueV) readRegs newRegs calls fret):
      PSemAction (ReadNondet _ cont) readRegs newRegs calls fret
  | PSemReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      readRegs newRegs calls areadRegs
      (HRegVal: In (r, existT _ regT regV) o)
      (HPSemAction: PSemAction (cont regV) readRegs newRegs calls fret)
      (HNewReads: areadRegs [=] (r, existT _ regT regV) :: readRegs):
      PSemAction (ReadReg r _ cont) areadRegs newRegs calls fret
  | PSemWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) readRegs newRegs calls anewRegs
      (HRegVal: In (r, k) (getKindAttr o))
      (HDisjRegs: key_not_In r newRegs)
      (HANewRegs: anewRegs [=] (r, (existT _ _ (evalExpr e))) :: newRegs)
      (HPSemAction: PSemAction cont readRegs newRegs calls fret):
      PSemAction (WriteReg r e cont) readRegs anewRegs calls fret
  | PSemIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2  newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HTrue: evalExpr p = true)
      (HAction: PSemAction a readRegs1 newRegs1 calls1 r1)
      (HPSemAction: PSemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs [=] newRegs1 ++ newRegs2)
      (HUCalls: ucalls [=] calls1 ++ calls2) :
      PSemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | PSemIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2 newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HFalse: evalExpr p = false)
      (HAction: PSemAction a' readRegs1 newRegs1 calls1 r1)
      (HPSemAction: PSemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs [=] newRegs1 ++ newRegs2)
      (HUCalls: ucalls [=] calls1 ++ calls2):
      PSemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | PSemAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2) readRegs2 newRegs2 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HPSemAction: PSemAction cont readRegs2 newRegs2 calls2 r2):
      PSemAction (Assertion p cont) readRegs2 newRegs2 calls2 r2
  | PSemDisplay
      (ls: list (SysT type)) k (cont: ActionT type k)
      r readRegs newRegs calls
      (HPSemAction: PSemAction cont readRegs newRegs calls r):
      PSemAction (Sys ls cont) readRegs newRegs calls r
  | PSemReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e)
      readRegs newRegs calls
      (HReadRegs: readRegs = nil)
      (HNewRegs: newRegs = nil)
      (HCalls: calls = nil) :
      PSemAction (Return e) readRegs newRegs calls evale.  
End Semantics.

Inductive RuleOrMeth :=
| Rle (rn: string)
| Meth (f: MethT).

Notation getRleOrMeth := (fun x => fst (snd x)).

Notation FullLabel := (RegsT * (RuleOrMeth * MethsT))%type.


Lemma SignT_dec: forall k1 k2 (s1 s2: SignT (k1, k2)), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  simpl in *.
  apply prod_dec; simpl; auto; apply isEq.
Defined.

(*
  Asserts that, if the values passed to, and
  returned by, a method are equal, the Gallina
  values passed to, and returned by, a method
  are also equal.
*)
Lemma method_values_eq
  :  forall (s : Signature) (x y : SignT s), existT SignT s x = existT SignT s y -> x = y.
Proof (Eqdep_dec.inj_pair2_eq_dec Signature Signature_dec SignT).
            
(*
  Asserts that the values passed two and returned
  by two method calls differ if their signatures
  differ.
*)
Lemma method_values_neq 
  :  forall (s r : Signature) (x : SignT s) (y : SignT r), s <> r -> existT SignT s x <> existT SignT r y.
Proof (fun s r x y H H0 => H (projT1_eq H0)).

(*
  Determines whether or not the Gallina terms
  passed to, and returned by, two method calls
  are equal.
*)
Definition method_denotation_values_dec
  :  forall (s : Signature) (x y : SignT s), {x = y} + {x <> y}
  := fun s => prod_dec (isEq (fst s)) (isEq (snd s)).

(*
  Determines whether or not the values passed to,
  and returned by, two method calls that have
  the same Kami signature are equal.
*)
Definition method_values_dec
  :  forall (s : Signature) (x y : SignT s), {existT SignT s x = existT SignT s y} + {existT SignT s x <> existT SignT s y}
  := fun s x y
       => sumbool_rec
            (fun _ => {existT SignT s x = existT SignT s y} + {existT SignT s x <> existT SignT s y})
            (fun H : x = y
              => left
                   (eq_ind x
                     (fun z => existT SignT s x = existT SignT s z)
                     (eq_refl (existT SignT s x))
                     y H))
            (fun H : x <> y
              => right
                   (fun H0 : existT SignT s x = existT SignT s y
                     => H (method_values_eq H0)))
            (method_denotation_values_dec x y).

(*
  Determines whether or not the values passed to,
  and returned by, two method calls are equal.
*)
Definition sigT_SignT_dec
  :  forall x y: (sigT SignT), {x = y} + {x <> y}
  := sigT_rect _
       (fun (s : Signature) (x : SignT s)
          => sigT_rect _
               (fun (r : Signature)
                 => sumbool_rect _
                      (fun H : s = r
                        => eq_rect s
                             (fun t => forall y : SignT t, {existT SignT s x = existT SignT t y} + {existT SignT s x <> existT SignT t y})
                             (fun y : SignT s => method_values_dec x y)
                             r H)
                      (fun (H : s <> r) (_ : SignT r)
                        => right (method_values_neq H))
                      (Signature_dec s r))).

Lemma MethT_dec: forall s1 s2: MethT, {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  apply prod_dec.
  - apply string_dec.
  - apply sigT_SignT_dec.
Defined.

Fixpoint getNumFromCalls (f : MethT) (l : MethsT) : Z :=
  match l with
  |g::l' => match MethT_dec f g with
            | left _ => 1%Z + (getNumFromCalls f l')
            | right _ => (getNumFromCalls f l')
            end
  |nil => 0
  end.

Definition getNumCalls (f : MethT) (l : list FullLabel) :=
  getNumFromCalls f (concat (map (fun x => (snd (snd x))) l)).

Fixpoint getNumFromExecs (f : MethT) (l : list RuleOrMeth) : Z :=
  match l with
  |rm::l' => match rm with
             |Rle _ => (getNumFromExecs f l')
             |Meth g => match MethT_dec f g with
                        |left _ => 1%Z + (getNumFromExecs f l')
                        |right _ => (getNumFromExecs f l')
                        end
             end
  |nil => 0
  end.

Definition getNumExecs (f : MethT) (l : list FullLabel) :=
  getNumFromExecs f (map (fun x => fst (snd x)) l).

Open Scope Z_scope.

Notation PPT_execs := (fun x => fst (snd x)).
Notation PPT_calls := (fun x => snd (snd x)).

(*
  Proves that the number of method calls returned
  by [getNumCalls] is always greater than or
  equal to 0.
*)
Lemma num_method_calls_positive
  : forall (method : MethT) (labels : list FullLabel),
      0 <= getNumCalls method labels.
Proof 
fun method
  => list_ind _
       (ltac:(discriminate) : 0 <= getNumCalls method [])
       (fun (label : FullLabel) (labels : list FullLabel)
         (H : 0 <= getNumFromCalls method (concat (map PPT_calls labels)))
         => list_ind _ H
              (fun (method0 : MethT) (methods : MethsT)
                (H0 : 0 <= getNumFromCalls method (methods ++ concat (map PPT_calls labels)))
                => sumbool_ind
                     (fun methods_eq
                       => 0 <=
                            if methods_eq
                              then 1 + getNumFromCalls method (methods ++ concat (map PPT_calls labels))
                              else getNumFromCalls method (methods ++ concat (map PPT_calls labels)))
                     (fun _ => Z.add_nonneg_nonneg 1 _ (Zle_0_pos 1) H0)
                     (fun _ => H0)
                     (MethT_dec method method0))
              (snd (snd label))).

(*
  Proves that the number of method executions
  counted by [getNumExecs] is always greater
  than or equal to 0.
*)
Lemma num_method_execs_positive
  : forall (method : MethT) (labels : list FullLabel),
      0 <= getNumExecs method labels.
Proof
fun method
  => list_ind _
       (ltac:(discriminate) : 0 <= getNumExecs method [])
       (fun (label : FullLabel) (labels : list FullLabel)
         (H : 0 <= getNumFromExecs method (map PPT_execs labels))
         => RuleOrMeth_ind
              (fun rule_method : RuleOrMeth
                => 0 <= match rule_method with
                        | Rle _ => _
                        | Meth _ => _
                        end)
              (fun _ => H)
              (fun method0 : MethT
                => sumbool_ind
                     (fun methods_eq
                       => 0 <=
                            if methods_eq
                              then 1 + getNumFromExecs method (map PPT_execs labels)
                              else getNumFromExecs method (map PPT_execs labels))
                     (fun _ => Z.add_nonneg_nonneg 1 _ (Zle_0_pos 1) H)
                     (fun _ => H)
                     (MethT_dec method method0))
              (fst (snd label))).

Close Scope Z_scope.

Definition getListFullLabel_diff (f : MethT) (l : list FullLabel) :=
  ((getNumExecs f l) - (getNumCalls f l))%Z.

Definition MatchingExecCalls_Base (l : list FullLabel) m :=
  forall f,
    In (fst f) (map fst (getMethods m)) ->
    (getNumCalls f l <= getNumExecs f l)%Z.

Definition MatchingExecCalls_Concat (lcall lexec : list FullLabel) mexec :=
  forall f,
    (getNumCalls f lcall <> 0%Z) ->
    In (fst f) (map fst (getAllMethods mexec)) ->
    ~In (fst f) (getHidden mexec) /\
    (getNumCalls f lcall + getNumCalls f lexec <= getNumExecs f lexec)%Z.

Section BaseModule.
  Variable m: BaseModule.

  Variable o: RegsT.

  Inductive Substeps: list FullLabel -> Prop :=
  | NilSubstep (HRegs: getKindAttr o = getKindAttr (getRegisters m)) : Substeps nil
  | AddRule (HRegs: getKindAttr o = getKindAttr (getRegisters m))
            rn rb
            (HInRules: In (rn, rb) (getRules m))
            reads u cs
            (HAction: SemAction o (rb type) reads u cs WO)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            l ls (HLabel: l = (u, (Rle rn, cs)) :: ls)
            (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
            (HNoRle: forall x, In x ls -> match fst (snd x) with
                                          | Rle _ => False
                                          | _ => True
                                          end)
            (HSubstep: Substeps ls):
      Substeps l
  | AddMeth (HRegs: getKindAttr o = getKindAttr (getRegisters m))
            fn fb
            (HInMeths: In (fn, fb) (getMethods m))
            reads u cs argV retV
            (HAction: SemAction o ((projT2 fb) type argV) reads u cs retV)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            l ls (HLabel: l = (u, (Meth (fn, existT _ _ (argV, retV)), cs)) :: ls )
            (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
            (HSubsteps: Substeps ls):
      Substeps l.

  Inductive PSubsteps: list FullLabel -> Prop :=
  | NilPSubstep (HRegs: getKindAttr o [=] getKindAttr (getRegisters m)) : PSubsteps nil
  | PAddRule (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
             rn rb
             (HInRules: In (rn, rb) (getRules m))
             reads u cs
             (HPAction: PSemAction o (rb type) reads u cs WO)
             (HReadsGood: SubList (getKindAttr reads)
                                  (getKindAttr (getRegisters m)))
             (HUpdGood: SubList (getKindAttr u)
                                (getKindAttr (getRegisters m)))
             l ls (HLabel: l [=] (u, (Rle rn, cs)) :: ls)
             (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
             (HNoRle: forall x, In x ls -> match fst (snd x) with
                                           | Rle _ => False
                                           | _ => True
                                           end)
             (HPSubstep: PSubsteps ls):
      PSubsteps l
  | PAddMeth (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
             fn fb
             (HInMeths: In (fn, fb) (getMethods m))
             reads u cs argV retV
             (HPAction: PSemAction o ((projT2 fb) type argV) reads u cs retV)
             (HReadsGood: SubList (getKindAttr reads)
                                  (getKindAttr (getRegisters m)))
             (HUpdGood: SubList (getKindAttr u)
                                (getKindAttr (getRegisters m)))
             l ls (HLabel: l [=] (u, (Meth (fn, existT _ _ (argV, retV)), cs)) :: ls )
             (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
             (HPSubsteps: PSubsteps ls):
      PSubsteps l.

  Inductive PPlusSubsteps: RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | NilPPlusSubstep (HRegs: getKindAttr o [=] getKindAttr (getRegisters m)) : PPlusSubsteps nil nil nil
  | PPlusAddRule (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            rn rb
            (HInRules: In (rn, rb) (getRules m))
            reads u cs
            (HPAction: PSemAction o (rb type) reads u cs WO)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Rle rn :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HNoRle: forall x, In x oldExecs -> match x with
                                                | Rle _ => False
                                                | _ => True
                                                end)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls
  | PPlusAddMeth (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            fn fb
            (HInMeths: In (fn, fb) (getMethods m))
            reads u cs argV retV
            (HPAction: PSemAction o ((projT2 fb) type argV) reads u cs retV)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Meth (fn, existT _ _ (argV, retV)) :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls.
End BaseModule.

Inductive Step: Mod -> RegsT -> list FullLabel -> Prop :=
| BaseStep m o l (HSubsteps: Substeps m o l) (HMatching: MatchingExecCalls_Base l  m):
    Step (Base m) o l
| HideMethStep m s o l (HStep: Step m o l)
               (HHidden : In s (map fst (getAllMethods m)) -> (forall v, (getListFullLabel_diff (s, v) l = 0%Z))):
    Step (HideMeth m s) o l
| ConcatModStep m1 m2 o1 o2 l1 l2
                (HStep1: Step m1 o1 l1)
                (HStep2: Step m2 o2 l2)
                (HMatching1: MatchingExecCalls_Concat l1 l2 m2)
                (HMatching2: MatchingExecCalls_Concat l2 l1 m1)
                (HNoRle: forall x y, In x l1 -> In y l2 -> match fst (snd x), fst (snd y) with
                                                           | Rle _, Rle _ => False
                                                           | _, _ => True
                                                           end)
                o l
                (HRegs: o = o1 ++ o2)
                (HLabels: l = l1 ++ l2):
    Step (ConcatMod m1 m2) o l.

Inductive PStep: Mod -> RegsT -> list FullLabel -> Prop :=
| PBaseStep m o l (HPSubsteps: PSubsteps m o l) (HMatching: MatchingExecCalls_Base l m):
    PStep (Base m) o l
| PHideMethStep m s o l (HPStep: PStep m o l)
               (HHidden : In s (map fst (getAllMethods m)) -> (forall v, (getListFullLabel_diff (s, v) l = 0%Z))):
    PStep (HideMeth m s) o l
| PConcatModStep m1 m2 o1 o2 l1 l2
                 (HPStep1: PStep m1 o1 l1)
                 (HPStep2: PStep m2 o2 l2)
                 (HMatching1: MatchingExecCalls_Concat l1 l2 m2)
                 (HMatching2: MatchingExecCalls_Concat l2 l1 m1)
                 (HNoRle: forall x y, In x l1 -> In y l2 -> match fst (snd x), fst (snd y) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end)
                 o l
                 (HRegs: o [=] o1 ++ o2)
                 (HLabels: l [=] l1 ++ l2):
    PStep (ConcatMod m1 m2) o l.

Section PPlusStep.
  Variable m: BaseModule.
  Variable o: RegsT.
  
  Definition MatchingExecCalls_flat (calls : MethsT) (execs : list RuleOrMeth) (m : BaseModule) :=
    forall (f : MethT),
      In (fst f) (map fst (getMethods m)) ->
      (getNumFromCalls f calls <= getNumFromExecs f execs)%Z.
  
  Inductive PPlusStep :  RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | BasePPlusStep upds execs calls:
      PPlusSubsteps m o upds execs calls ->
      MatchingExecCalls_flat calls execs m -> PPlusStep upds execs calls.
End PPlusStep.


Definition UpdRegs (u: list RegsT) (o o': RegsT)
  := getKindAttr o = getKindAttr o' /\
     (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                   ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

Notation regInit := (fun o' r => fst o' = fst r /\
                                 exists (pf: projT1 (snd o') = projT1 (snd r)),
                                   match projT2 (snd r) with
                                   | None => True
                                   | Some x =>
                                     match pf in _ = Y return _ Y with
                                     | eq_refl => projT2 (snd o')
                                     end = evalConstFullT x
                                   end).


Fixpoint findReg (s: string) (u: RegsT) :=
  match u with
  | x :: xs => if string_dec s (fst x)
               then Some (snd x)
               else findReg s xs
  | nil => None
  end.

Fixpoint doUpdRegs (u: RegsT) (o: RegsT) :=
  match o with
  | x :: o' => match findReg (fst x) u with
               | Some y => (fst x, y)
               | None => x
               end :: doUpdRegs u o'
  | nil => nil
  end.

Section Trace.
  Variable m: Mod.
  Inductive Trace: RegsT -> list (list FullLabel) -> Prop :=
  | InitTrace (o': RegsT) ls'
              (HUpdRegs: (Forall2 regInit o' (getAllRegisters m)))
              (HTrace: ls' = nil):
      Trace o' ls'
  | ContinueTrace o ls l o' ls'
                  (HOldTrace: Trace o ls)
                  (HStep: Step m o l)
                  (HUpdRegs: UpdRegs (map fst l) o o')
                  (HTrace: ls' = l :: ls):
      Trace o' ls'.

  Definition PUpdRegs (u: list RegsT) (o o': RegsT)
    := getKindAttr o [=] getKindAttr o' /\
       (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                     ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

  Inductive PTrace: RegsT -> list (list FullLabel) -> Prop :=
  | PInitTrace (o' o'' : RegsT) ls'
               (HPerm : o' [=] o'')
               (HUpdRegs : Forall2 regInit o'' (getAllRegisters m))
               (HTrace: ls' = nil):
      PTrace o' ls'
  | PContinueTrace o ls l o' ls'
                   (PHOldTrace: PTrace o ls)
                   (HPStep: PStep m o l)
                   (HPUpdRegs: PUpdRegs (map fst l) o o')
                   (HTrace: ls' = l :: ls):
      PTrace o' ls'.
End Trace.

Definition PPlusUpdRegs (u o o' : RegsT) :=
  getKindAttr o [=] getKindAttr o' /\
  (forall s v, In (s, v) o' -> In (s, v) u \/ (~ In s (map fst u) /\ In (s, v) o)).
  
Section PPlusTrace.
  Variable m: BaseModule.
  Inductive PPlusTrace : RegsT -> list (RegsT * ((list RuleOrMeth) * MethsT)) -> Prop :=
  | PPlusInitTrace (o' o'' : RegsT) ls'
                   (HPerm : o' [=] o'')
                   (HUpdRegs : Forall2 regInit o'' (getRegisters m))
                   (HTrace : ls' = nil):
      PPlusTrace o' ls'
  | PPlusContinueTrace (o o' : RegsT)
                       (upds : RegsT)
                       (execs : list RuleOrMeth)
                       (calls : MethsT)
                       (ls ls' : list (RegsT * ((list RuleOrMeth) * MethsT)))
                       (PPlusOldTrace : PPlusTrace o ls)
                       (HPPlusStep : PPlusStep m o upds execs calls)
                       (HUpdRegs : PPlusUpdRegs upds o o')
                       (HPPlusTrace : ls' = ((upds, (execs, calls))::ls)):
      PPlusTrace o' ls'.
End PPlusTrace.

Definition WeakInclusion (l1 : list FullLabel) (l2 : list FullLabel) : Prop :=
  (forall f, getListFullLabel_diff f l1 = getListFullLabel_diff f l2) /\
  ((exists rle, In (Rle rle) (map (fun x => fst (snd x)) l2)) ->
   (exists rle, In (Rle rle) (map (fun x => fst (snd x)) l1))).

Definition TraceInclusion m1 m2 :=
 forall o1 ls1,
   Trace m1 o1 ls1 ->
   exists o2 ls2,
     Trace m2 o2 ls2 /\
     length ls1 = length ls2 /\
     (nthProp2 WeakInclusion ls1 ls2).

Definition PTraceList (m : Mod) (ls : list (list FullLabel)) :=
  (exists (o : RegsT), PTrace m o ls).

Inductive WeakInclusions : list (list FullLabel) -> list (list (FullLabel)) -> Prop :=
| WI_Nil : WeakInclusions nil nil
| WI_Cons : forall (ls ls' : list (list FullLabel)) (l l' : list FullLabel), WeakInclusions ls ls' -> WeakInclusion l l' -> WeakInclusions (l::ls)(l'::ls').

Definition PTraceInclusion (m m' : Mod) :=
  forall (o : RegsT) (ls : list (list FullLabel)),
    PTrace m o ls -> exists (ls' : list (list FullLabel)), PTraceList m' ls' /\ WeakInclusions ls ls'.

Section PPlusTraceInclusion.

  Definition getListFullLabel_diff_flat f (t : (RegsT *((list RuleOrMeth)*MethsT))) : Z:=
    (getNumFromExecs f (PPT_execs t) - getNumFromCalls f (PPT_calls t))%Z. 
  
  Definition WeakInclusion_flat (t1 t2 : (RegsT *((list RuleOrMeth) * MethsT))) :=
    (forall (f : MethT), (getListFullLabel_diff_flat f t1 = getListFullLabel_diff_flat f t2)%Z) /\
    ((exists rle, In (Rle rle) (PPT_execs t2)) ->
     (exists rle, In (Rle rle) (PPT_execs t1))).


  Inductive WeakInclusions_flat : list (RegsT * ((list RuleOrMeth) * MethsT)) -> list (RegsT *((list RuleOrMeth) * MethsT)) -> Prop :=
  |WIf_Nil : WeakInclusions_flat nil nil
  |WIf_Cons : forall (lt1 lt2 : list (RegsT *((list RuleOrMeth) * MethsT))) (t1 t2 : RegsT *((list RuleOrMeth) * MethsT)),
      WeakInclusions_flat lt1 lt2 -> WeakInclusion_flat t1 t2 -> WeakInclusions_flat (t1::lt1) (t2::lt2).

  Definition PPlusTraceList (m : BaseModule)(lt : list (RegsT * ((list RuleOrMeth) * MethsT))) :=
    (exists (o : RegsT), PPlusTrace m o lt).

  Definition PPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))),  PPlusTraceList m' tl' /\ WeakInclusions_flat tl tl'.

  Definition StrongPPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))), PPlusTrace m' o tl' /\ WeakInclusions_flat tl tl'.
End PPlusTraceInclusion.













(* Useful functions *)

Fixpoint getCallsWithSign k (a: ActionT (fun _ => unit) k) :=
  match a in ActionT _ _ with
  | MCall meth k argExpr cont =>
    (meth, k) :: getCallsWithSign (cont tt)
  | Return x => nil
  | LetExpr k' expr cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * (Kind * Kind)) with
    | SyntaxKind k => fun cont => getCallsWithSign (cont tt)
    | _ => fun _ => nil
    end cont
  | LetAction k' a' cont =>
    getCallsWithSign a' ++ getCallsWithSign (cont tt)
  | ReadNondet k' cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * (Kind * Kind)) with
    | SyntaxKind k => fun cont =>
                        getCallsWithSign (cont tt)
    | _ => fun _ => nil
    end cont
  | ReadReg r k' cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * (Kind * Kind)) with
    | SyntaxKind k => fun cont =>
                        getCallsWithSign (cont tt)
    | _ => fun _ => nil
    end cont
  | WriteReg r k' expr cont =>
    getCallsWithSign cont
  | Assertion pred cont => getCallsWithSign cont
  | Sys ls cont => getCallsWithSign cont
  | IfElse pred ktf t f cont =>
    getCallsWithSign t ++ getCallsWithSign f ++ getCallsWithSign (cont tt)
  end.

Definition getCallsWithSignPerRule (rule: Attribute (Action Void)) :=
  getCallsWithSign (snd rule _).

Definition getCallsWithSignPerMeth (meth: DefMethT) :=
  getCallsWithSign (projT2 (snd meth) _ tt).

Definition getCallsWithSignPerMod (m: Mod) :=
  concat (map getCallsWithSignPerRule (getAllRules m)) ++ concat (map getCallsWithSignPerMeth (getAllMethods m)).

Definition getCallsPerMod (m: Mod) := map fst (getCallsWithSignPerMod m).


(* Utility functions *)

(* TODO: For each of these functions, get a well-formedness theorem and possibly trace inclusion theorem *)

Fixpoint createHide (m: BaseModule) (hides: list string) :=
  match hides with
  | nil => Base m
  | x :: xs => HideMeth (createHide m xs) x
  end.

Fixpoint createHideMod (m : Mod) (hides : list string) : Mod :=
  match hides with
  | nil => m
  | h::hides' => HideMeth (createHideMod m hides') h
  end.

Definition getFlat m := BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m).

Definition flatten m := createHide (getFlat m) (getHidden m).

Definition autoHide (m: Mod) := createHideMod m (filter (fun i => getBool (in_dec string_dec i (getCallsPerMod m)))
                                                        (map fst (getAllMethods m))).

Fixpoint separateBaseMod (m: Mod): (list RegFileBase * list BaseModule) :=
  match m with
  | Base m' =>
    match m' with
    | BaseMod regs rules meths => (nil, BaseMod regs rules meths :: nil)
    | BaseRegFile rf => (rf :: nil, nil)
    end
  | HideMeth m' meth => separateBaseMod m'
  | ConcatMod m1 m2 =>
    let '(rfs1, ms1) := separateBaseMod m1 in
    let '(rfs2, ms2) := separateBaseMod m2 in
    (rfs1 ++ rfs2, ms1 ++ ms2)
  end.

Definition separateMod (m: Mod) :=
  (getHidden m, separateBaseMod m).
    
Fixpoint mergeSeparatedBaseMod (bl : list BaseModule) : Mod :=
  match bl with
  | b::bl' => ConcatMod (Base b) (mergeSeparatedBaseMod bl')
  | nil => Base (BaseMod nil nil nil)
  end.

Fixpoint mergeSeparatedBaseFile (rfl : list RegFileBase) : Mod :=
  match rfl with
  | rf::rfl' => ConcatMod (Base (BaseRegFile rf))(mergeSeparatedBaseFile rfl')
  | nil => Base (BaseMod nil nil nil)
  end.

Definition mergeSeparatedMod (tup: list string * (list RegFileBase * list BaseModule)) :=
  createHideMod (ConcatMod (mergeSeparatedBaseFile (fst (snd tup))) (mergeSeparatedBaseMod (snd (snd tup)))) (fst tup).
 
Definition concatFlat m1 m2 := BaseMod (getRegisters m1 ++ getRegisters m2)
                                       (getRules m1 ++ getRules m2)
                                       (getMethods m1 ++ getMethods m2).

(* Inlining *)


Section inlineSingle.
  Variable ty: Kind -> Type.
  Variable f: DefMethT.

  (* not expressible as a module *)
  Fixpoint inlineSingle k (a: ActionT ty k): ActionT ty k :=
    match a with
    | MCall g sign arg cont =>
      match string_dec (fst f) g with
      | left _ =>
        match Signature_dec sign (projT1 (snd f)) with
        | left isEq =>
          LetAction (LetExpr match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with
                             | eq_refl => arg
                             end (projT2 (snd f) ty))
                    (fun ret => inlineSingle (match isEq in _ = Y return ty (snd Y) -> ActionT ty k with
                                              | eq_refl => cont
                                              end ret))
        | right _ => MCall g sign arg (fun ret => inlineSingle (cont ret))
        end
      | right _ => MCall g sign arg (fun ret => inlineSingle (cont ret))
      end
    | LetExpr _ e cont =>
      LetExpr e (fun ret => inlineSingle (cont ret))
    | LetAction _ a cont =>
      LetAction (inlineSingle a) (fun ret => inlineSingle (cont ret))
    | ReadNondet k c =>
      ReadNondet k (fun ret => inlineSingle (c ret))
    | ReadReg r k c =>
      ReadReg r k (fun ret => inlineSingle (c ret))
    | WriteReg r k e a =>
      WriteReg r e (inlineSingle a)
    | IfElse p _ aT aF c =>
      IfElse p (inlineSingle aT) (inlineSingle aF) (fun ret => inlineSingle (c ret))
    | Assertion e c =>
      Assertion e (inlineSingle c)
    | Sys ls c =>
      Sys ls (inlineSingle c)
    | Return e =>
      Return e
    end.
End inlineSingle.

Definition inlineSingle_Rule  (f : DefMethT) (rle : RuleT): RuleT.
Proof.
  unfold RuleT in *.
  destruct rle.
  constructor.
  - apply s.
  - unfold Action in *.
    intro.
    apply (inlineSingle f (a ty)).
Defined.

(* BaseModule version of inlineSingle_Rule done *)
Definition inlineSingle_Rule_map_BaseModule (f : DefMethT) (m : BaseModule) :=
  BaseMod (getRegisters m) (map (inlineSingle_Rule f) (getRules m)) (getMethods m).

Fixpoint inlineSingle_Rule_in_list (f : DefMethT) (rn : string) (lr : list RuleT) : list RuleT :=
  match lr with
  | rle'::lr' => match string_dec rn (fst rle') with
                 | right _ => rle'::(inlineSingle_Rule_in_list f rn lr')
                 | left _ => (inlineSingle_Rule f rle')::(inlineSingle_Rule_in_list f rn lr')
                 end
  | nil => nil
  end.

(* BaseModule version of inlineSingle_Rule_in_list done *)
Definition inlineSingle_Rule_BaseModule (f : DefMethT) (rn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (inlineSingle_Rule_in_list f rn (getRules m)) (getMethods m).

Definition inlineSingle_Meth (f : DefMethT) (meth : DefMethT): DefMethT.
Proof.
  unfold DefMethT in *.
  destruct meth.
  constructor.
  - apply s.
  - destruct (string_dec (fst f) s).
    + apply s0.
    + destruct s0.
      unfold MethodT; unfold MethodT in m.
      exists x.
      intros.
      apply (inlineSingle f (m ty X)).
Defined.

(* BaseModule version of inlineSingle_Meth done *)
Definition inlineSingle_Meth_map_BaseModule (f : DefMethT) (m : BaseModule) :=
  BaseMod (getRegisters m) (getRules m) (map (inlineSingle_Meth f) (getMethods m)).

Fixpoint inlineSingle_Meth_in_list (f : DefMethT) (gn : string) (lm : list DefMethT) : list DefMethT :=
  match lm with
  | meth'::lm' => match string_dec gn (fst meth') with
                  | right _ => meth'::(inlineSingle_Meth_in_list f gn lm')
                  | left _ => (inlineSingle_Meth f meth')::(inlineSingle_Meth_in_list f gn lm')
                  end
  | nil => nil
  end.

(* BaseModule version of inlineSingle_Meth_in_list done *)
Definition inlineSingle_Meth_BaseModule (f : DefMethT) (fn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (getRules m) (inlineSingle_Meth_in_list f fn (getMethods m)).

Section inlineSingle_nth.
  Variable (f : DefMethT).
  Variable (regs: list RegInitT) (rules: list RuleT) (meths: list DefMethT).

  (* BaseModule version of both inlineSingle_Rule and inlineSingle_Meth done *)
  Definition inlineSingle_BaseModule : BaseModule :=
    BaseMod regs (map (inlineSingle_Rule f) rules) (map (inlineSingle_Meth f) meths).

  (* Iterated BaseModule version of inlineSingle_Meth done *)
  Definition inlineSingle_BaseModule_nth_Meth xs : BaseModule :=
    BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs).

  (* Iterated BaseModule version of inlineSingle_Rule done *)
  Definition inlineSingle_BaseModule_nth_Rule xs : BaseModule :=
    BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths.
End inlineSingle_nth.

Definition inlineSingle_Rules_pos meths n rules :=
  match nth_error meths n with
  | Some f => map (inlineSingle_Rule f) rules
  | None => rules
  end.

Definition inlineAll_Rules meths rules := fold_left (fun newRules n => inlineSingle_Rules_pos meths n newRules) (0 upto (length meths)) rules.

(* BaseModule version of inlineAll_Rules done *)
Definition inlineAll_Rules_mod m :=
  (BaseMod (getRegisters m) (inlineAll_Rules (getMethods m) (getRules m)) (getMethods m)).

Definition inlineSingle_Meths_pos newMeths n :=
  match nth_error newMeths n with
  | Some f => map (inlineSingle_Meth f) newMeths
  | None => newMeths
  end.

Definition inlineAll_Meths meths := fold_left inlineSingle_Meths_pos (0 upto (length meths)) meths.

(* BaseModule version of inlineAll_Meths done *)
Definition inlineAll_Meths_mod m :=
  (BaseMod (getRegisters m) (getRules m) (inlineAll_Meths (getMethods m))).

Definition inlineAll_All regs rules meths :=
  (BaseMod regs (inlineAll_Rules (inlineAll_Meths meths) rules) (inlineAll_Meths meths)).

(* BaseModule version of inlineAll_All done *)
Definition inlineAll_All_mod m :=
  inlineAll_All (getAllRegisters m) (getAllRules m) (getAllMethods m).

(* Module version of inlineAll_All done *)
Definition flatten_inline_everything m :=
  createHide (inlineAll_All_mod m) (getHidden m).

Definition removeHides (m: BaseModule) s :=
  BaseMod (getRegisters m) (getRules m)
          (filter (fun df => negb (getBool (in_dec string_dec (fst df) s))) (getMethods m)).

(* BaseModule of inlineAll_All which removes initially hidden methods *)
Definition flatten_inline_remove m :=
  removeHides (inlineAll_All_mod m) (getHidden m).
  















(** Notations for expressions *)

Notation Default := (getDefaultConst _).

Notation "k @# ty" := (Expr ty (SyntaxKind k)) (no associativity, at level 98, only parsing).

Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (only parsing) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)): kami_expr_scope.
Notation "$$ e" := (Const ltac:(assumption) e) (at level 8, only parsing) : kami_expr_scope.

Local Definition testStruct :=
  (STRUCT {
       "hello" :: Bit 10 ;
       "a" :: Bit 3 ;
       "b" :: Bit 5 ;
       "test" :: Bool }).

Local Definition testStructVal {ty}: testStruct @# ty :=
  (STRUCT {
       "hello" ::= $ 4 ;
       "a" ::= $ 23 ;
       "b" ::= $ 5 ;
       "test" ::= $$ true })%kami_expr.

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

Section testBit.
  Variable ty: Kind -> Type.
  Local Definition testBit := ($$ (natToWord 23 35))%kami_expr.
End testBit.

Notation "a $#[ i : j ]":=
  ltac:(let aTy := type of a in
        let aTySimpl := eval compute in aTy in
            match aTySimpl with
            | Expr _ (SyntaxKind (Bit ?w)) =>
              exact (ConstExtract
                       j
                       (i + 1 - j)%nat
                       (w - 1 - i)%nat
                       (@castBits _ w (j + (i + 1 - j) + (w - 1 - i)) ltac:(abstract (lia || nia)) a))
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
  ((BinBit (Concat _ _)) a .. (BinBit (Concat _ _) b (@Const _ (Bit 0) WO)) ..)
    (at level 100, a at level 99): kami_expr_scope.
Notation "{< a , .. , b >}" :=
  (Word.combine b .. (Word.combine a WO) ..)
    (at level 100, a at level 99): word_scope.

Infix "<" := (BinBitBool (LessThan _)) : kami_expr_scope.
Notation "x > y" := (BinBitBool (LessThan _) y x) : kami_expr_scope.
Notation "x >= y" := (UniBool Neg (BinBitBool (LessThan _) x y)) : kami_expr_scope.
Notation "x <= y" := (UniBool Neg (BinBitBool (LessThan _) y x)) : kami_expr_scope.
Infix "<s" := (Slt _) : kami_expr_scope.
Notation "x >s y" := (Slt _ y x) : kami_expr_scope.
Notation "x >=s y" := (UniBool Neg (Slt _ x y)) (at level 100) : kami_expr_scope.
Notation "x <=s y" := (UniBool Neg (Slt _ y x)) (at level 100): kami_expr_scope.
Infix "==" := Eq (at level 39, no associativity) : kami_expr_scope.
Notation "x != y" := (UniBool Neg (Eq x y))
                (at level 39, no associativity) : kami_expr_scope.
Notation "v @[ idx ] " := (ReadArray v idx) (at level 38) : kami_expr_scope.
Notation "v '@[' idx <- val ] " := (UpdateArray v idx val) (at level 38) : kami_expr_scope.

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
                                | Expr _ (SyntaxKind ?y) => getStructStringFn y f
                                | _ => let y := eval hnf in v in
                                           getStructFull y f
                                end.

Notation "s @% f" := (ReadStruct s ltac:(let typeS := type of s in
                                         getStructFull typeS f))
                       (at level 38, only parsing) : kami_expr_scope.

Notation "name ::= value" :=
  (name, value) (only parsing): kami_switch_init_scope.
Delimit Scope kami_switch_init_scope with switch_init.

Notation "s '@%[' f <- v ]" := (UpdateStruct s%kami_expr (ltac:(let typeS := type of s in
                                                               getStructFull typeS f))
                                             v%kami_expr)
                                 (at level 100, only parsing) : kami_expr_scope.

Local Definition testExtract ty n n1 n2 (pf1: n > n1) (pf2: n1 > n2) (a: Bit n @# ty) := (a $#[n1 : n2])%kami_expr.

Local Definition testConcat ty (w1: Bit 10 @# ty) (w2: Bit 2 @# ty) (w3: Bit 5 @# ty) :=
  {< w1, w2, w3 >}%kami_expr.

Local Definition testArrayAccess ty (v: Array 4 (Bit 10) @# ty) (idx : Bit 2 @# ty) := (v @[ idx <- v @[ idx ]])%kami_expr.

Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) : kami_expr_scope.

Local Definition testConstNat ty (w1 w2: Bit 10 @# ty): Bit 10 @# ty := (w1 + w2 + $4 + $6)%kami_expr.

Notation "nkind <[ def ]>" := (@NativeKind nkind def) (at level 100): kami_expr_scope.

(** Notations for action *)

Notation "'Call' meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, Void) a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' name : retT <- meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, retT) a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' meth () ; cont " :=
  (MCall meth%string (Void, Void) (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_action_scope.
Notation "'Call' name : retT <- meth () ; cont " :=
  (MCall meth%string (Void, retT) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'LETN' name : fullkind <- expr ; cont " :=
  (LetExpr (k := fullkind) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name <- expr ; cont " :=
  (LetExpr expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (LetExpr (k := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name <- act ; cont " :=
  (LetAction act (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name : t <- act ; cont " :=
  (LetAction (k := t) act (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'NondetN' name : fullkind ; cont" :=
  (ReadNondet fullkind (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'Nondet' name : kind ; cont" :=
  (ReadNondet (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'ReadN' name : fullkind <- reg ; cont " :=
  (ReadReg reg fullkind (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg reg _ (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg reg (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_action_scope.
Notation "'WriteN' reg : fullkind <- expr ; cont " :=
  (@WriteReg _ _ reg fullkind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg reg expr%kami_expr cont)
    (at level 12, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@WriteReg _ _ reg (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 99) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 13, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 13, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact ; cont" :=
  (IfElse cexpr%kami_expr tact (Return (Const _ Default)) (fun _ => cont))
    (at level 13, right associativity) : kami_action_scope.
Notation "'Assert' expr ; cont " :=
  (Assertion expr%kami_expr cont)
    (at level 12, right associativity) : kami_action_scope.
Notation "'System' sysexpr ; cont " :=
  (Sys sysexpr%kami_expr cont)
    (at level 12, right associativity) : kami_action_scope.
Notation "'Ret' expr" :=
  (Return expr%kami_expr) (at level 12) : kami_action_scope.
Notation "'Retv'" := (Return (Const _ (k := Void) Default)) : kami_action_scope.

Notation "'LETE' name <- expr ; cont " :=
  (LetE expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_expr_scope.
Notation "'LETE' name : t <- expr ; cont " :=
  (LetE (k' := t) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 99) : kami_expr_scope.
Notation "'RetE' expr" :=
  (NormExpr expr%kami_expr) (at level 12) : kami_expr_scope.

Notation "k ## ty" := (LetExprSyntax ty k) (no associativity, at level 98, only parsing).

Notation "'LETC' name <- v ; c " :=
  (LETE name <- RetE v ; c)%kami_expr
                           (at level 12, right associativity, name at level 99) : kami_expr_scope.

Notation "'LETC' name : t <- v ; c " :=
  (LETE name : t <- RetE v ; c)%kami_expr
                               (at level 12, right associativity, name at level 99) : kami_expr_scope.


Delimit Scope kami_action_scope with kami_action.

Local Open Scope kami_action.
Local Open Scope kami_expr.
Local Definition testFieldAccess (ty: Kind -> Type): ActionT ty (Bit 10) :=
  (LET val: testStruct <- testStructVal;
     Ret (#val @% "hello")).
Local Close Scope kami_expr.
Local Close Scope kami_action.

Local Definition testFieldUpd (ty: Kind -> Type) := 
  ((testStructVal (ty := ty)) @%[ "hello" <- Const ty (natToWord 10 23) ])%kami_expr.


Fixpoint gatherActions (ty: Kind -> Type) k_in (acts: list (ActionT ty k_in)) k_out (cont: list (k_in @# ty) -> ActionT ty k_out): ActionT ty k_out :=
  match acts with
  | nil => cont nil
  | x :: xs =>
    (LETA val <- x;
       gatherActions xs (fun vals => cont ((#val)%kami_expr :: vals)))%kami_action
  end.

Notation "'GatherActions' actionList 'as' val ; cont" :=
  (gatherActions actionList (fun val => cont) (* nil *))
    (at level 12, right associativity, val at level 99) : kami_action_scope.

Definition readNames (ty: Kind -> Type) k names := map (fun r => Read tmp: k <- r; Ret #tmp)%kami_action names.

Notation "'ReadToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (readNames _ k names) (fun val => cont) (* nil *))
    (at level 12, right associativity, val at level 99) : kami_action_scope.

Definition callNames (ty: Kind -> Type) k names := map (fun r => Call tmp : k <- r(); Ret #tmp)%kami_action names.

Notation "'CallToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (callNames _ k names) (fun val => cont) (* nil *))
    (at level 12, right associativity, val at level 99): kami_action_scope.

Definition writeNames (ty: Kind -> Type) k namesVals := map (fun r => Write (fst r) : k <- snd r; Ret (Const ty WO))%kami_action namesVals.

Notation "'WriteToList' names 'of' k 'using' vals ; cont" :=
  (gatherActions (@writeNames _ k (List.combine names vals)) (fun _ => cont) (* nil *))
    (at level 12, right associativity, vals at level 99) : kami_action_scope.

(** * Notation for normal mods *)

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


Definition makeModule (im : InModule) :=
  let '(regs, rules, meths) := makeModule' im in
  BaseMod regs rules meths.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Notation "'RegisterN' name : type <- init" :=
  (MERegister (name%string, existT optConstFullT type (Some init)))
    (at level 12, name at level 99) : kami_scope.

Notation "'Register' name : type <- init" :=
  (MERegister (name%string, existT optConstFullT (SyntaxKind type) (Some (makeConst init))))
    (at level 12, name at level 99) : kami_scope.

Notation "'RegisterU' name : type" :=
  (MERegister (name%string, existT optConstFullT (SyntaxKind type) None))
    (at level 12, name at level 99) : kami_scope.

Section Positive.
    Import BinPosDef.
    Local Open Scope positive_scope.
    Fixpoint of_pos (p : positive) (rest : string) : string :=
        match p with
        | 1 => String "1" rest
        | 2 => String "2" rest
        | 3 => String "3" rest
        | 4 => String "4" rest
        | 5 => String "5" rest
        | 6 => String "6" rest
        | 7 => String "7" rest
        | 8 => String "8" rest
        | 9 => String "9" rest
        | 10 => String "A" rest
        | 11 => String "B" rest
        | 12 => String "C" rest
        | 13 => String "D" rest
        | 14 => String "E" rest
        | 15 => String "F" rest
        | p'~0~0~0~0 => of_pos p' (String "0" rest)
        | p'~0~0~0~1 => of_pos p' (String "1" rest)
        | p'~0~0~1~0 => of_pos p' (String "2" rest)
        | p'~0~0~1~1 => of_pos p' (String "3" rest)
        | p'~0~1~0~0 => of_pos p' (String "4" rest)
        | p'~0~1~0~1 => of_pos p' (String "5" rest)
        | p'~0~1~1~0 => of_pos p' (String "6" rest)
        | p'~0~1~1~1 => of_pos p' (String "7" rest)
        | p'~1~0~0~0 => of_pos p' (String "8" rest)
        | p'~1~0~0~1 => of_pos p' (String "9" rest)
        | p'~1~0~1~0 => of_pos p' (String "A" rest)
        | p'~1~0~1~1 => of_pos p' (String "B" rest)
        | p'~1~1~0~0 => of_pos p' (String "C" rest)
        | p'~1~1~0~1 => of_pos p' (String "D" rest)
        | p'~1~1~1~0 => of_pos p' (String "E" rest)
        | p'~1~1~1~1 => of_pos p' (String "F" rest)
        end.
    Local Close Scope positive_scope.
    Definition natToHexStr (n : nat) : string :=
        match (BinNat.N.of_nat n) with
        | N0     => "0"
        | Npos p => of_pos p ""
        end.
End Positive.

Definition AddIndexToName name idx := (name ++ "_" ++ natToHexStr idx)%string.

Definition AddIndicesToNames name idxs := map (fun x => AddIndexToName name x) idxs.


(* Definition test ty : ActionT ty Void := *)
(*   (CallToList (AddIndicesToNames "ext_source" (0 upto 10 )) of Bool as ext_sources; *)
(*      WriteToList (AddIndicesToNames "clicintip" ( 0 upto 10)) of Bool using ext_sources; Retv)%kami_action. *)

(* Eval compute in test. *)


Notation "'RegisterArray' name 'using' nums : type <- init" :=
  (MERegAry (
    map (fun idx =>
      (AddIndexToName name idx, existT optConstFullT (SyntaxKind type) (Some (makeConst init)))
    ) nums
  ))
    (at level 12, name at level 9, nums at level 9) : kami_scope.

Delimit Scope kami_scope with kami.

Notation "'Method' name () : retT := c" :=
  (MEMeth (name%string, existT MethodT (Void, retT)
                               (fun ty (_: ty Void) => c%kami_action : ActionT ty retT)))
    (at level 12, name at level 9) : kami_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MEMeth (name%string, existT MethodT (dom, retT)
                               (fun ty (param : ty dom) => c%kami_action : ActionT ty retT)))
    (at level 12, name at level 9, param at level 99) : kami_scope.

Notation "'Rule' name := c" :=
  (MERule (name%string, fun ty => (c)%kami_action : ActionT ty Void))
    (at level 12) : kami_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..))
    (only parsing).

Notation "'Switch' val 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons (IF val == fst s1%switch_init then pack (snd s1%switch_init) else $0)%kami_expr ..
                                (cons (IF val == fst sN%switch_init then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

Notation "'Switch' val 'Of' inK 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons (IF val == ((fst s1%switch_init): inK @# _) then pack (snd s1%switch_init) else $0)%kami_expr ..
                                (cons (IF val == ((fst sN%switch_init): inK @# _) then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

Definition testSwitch ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Retn Bool With {
            $$ (natToWord 5 5) ::= $$ true ;
            $$ (natToWord 5 6) ::= $$ false
          })%kami_expr.

Definition testSwitch2 ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Of Bit 5 Retn Bool With {
            $$ (natToWord 5 5) ::= $$ true ;
            $$ (natToWord 5 6) ::= $$ false
          })%kami_expr.


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

(* Infix "++" := ConcatMod: kami_scope. *)

Section tets.
  Variable a : string.
  Local Example test := MOD_WF{
                      Register (a ++ "x") : Bool <- true
                        with Register (a ++ "y") : Bool <- false
                        with Rule (a ++ "r1") := ( Read y: Bool <- a++"y";
                                                     Write (a++"x"): Bool <- #y;
                                                     Retv )
                    }.
End tets.

Local Example test2 a b := (ConcatMod (test a) (test b))%kami.










Definition Maybe k :=
  STRUCT {
      "valid" :: Bool;
      "data"  :: k
    }.

Definition Pair (A B: Kind) := (STRUCT {
                                    "fst" :: A;
                                    "snd" :: B
                               }).


Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= x })%kami_expr
    (at level 100, only parsing) : kami_expr_scope.

Definition Invalid {ty: Kind -> Type} {k} := (STRUCT { "valid" ::= $$ false ; "data" ::= $$ (getDefaultConst k) })%kami_expr.

Definition WriteRegFile n dataT := STRUCT {
                                       "addr" :: Bit (Nat.log2_up n);
                                       "data" :: dataT }.

Notation "'InvData' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= x })%kami_expr
    (at level 100, only parsing) : kami_expr_scope.


Definition extractArbitraryRange ty sz (inst: Bit sz ## ty) (range: nat * nat):
  Bit (fst range + 1 - snd range) ## ty :=
  (LETE i <- inst ;
     RetE (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range)
                        (ZeroExtendTruncLsb _ #i)))%kami_expr.
   


Fixpoint gatherLetExpr (ty: Kind -> Type)
         (acts: list (string * {k_in: Kind & LetExprSyntax ty k_in})%type)
         k_out
         (cont: list (string * {k_in: Kind & k_in @# ty}) -> LetExprSyntax ty k_out):
            LetExprSyntax ty k_out :=
  match acts with
  | nil => cont nil
  | cons x xs =>
    (LETE val <- (projT2 (snd x));
       gatherLetExpr xs (fun vals => cont (cons (fst x, existT _ (projT1 (snd x)) (#val)%kami_expr) vals)))%kami_expr
  end.

Fixpoint gatherLetExprVec (ty: Kind -> Type) n
         (acts: Vector.t ({k_in: (string * Kind) & LetExprSyntax ty (snd k_in)})%type n)
         k_out
         (cont: Vector.t ({k_in: (string * Kind) & (snd k_in) @# ty}) n -> LetExprSyntax ty k_out):
            LetExprSyntax ty k_out :=
  match acts in Vector.t _ n return (Vector.t ({k_in: (string * Kind) & (snd k_in) @# ty}) n ->
                                     LetExprSyntax ty k_out) -> LetExprSyntax ty k_out with
  | Vector.nil => fun cont => cont (Vector.nil _)
  | Vector.cons x _ xs =>
    fun cont =>
      (LETE val <- (projT2 x);
         gatherLetExprVec xs (fun vals => cont
                                            (Vector.cons _
                                                         (existT _ (projT1 x) (#val)%kami_expr)
                                                         _ vals)))%kami_expr
  end cont.

Definition structFromExprs ty n (ls: Vector.t {k_in: (string * Kind) & (snd k_in) @# ty} n) :=
  Struct
    (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
    (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j)).
               
Definition structFromLetExprs ty n (ls: Vector.t {k_in: (string * Kind) & (snd k_in) ## ty} n) :=
  Struct
    (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
    (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j)).

Local Open Scope kami_expr.
Fixpoint gatherLetExprVector (ty: Kind -> Type) n
         (acts: Vector.t ({k_in: (string * Kind) & LetExprSyntax ty (snd k_in)})%type n)
         {struct acts}:
  LetExprSyntax ty (structFromLetExprs acts) :=
  (match acts in Vector.t _ n return
         LetExprSyntax ty (structFromLetExprs acts) with
   | Vector.nil => RetE (getStructVal (Vector.nil _))
   | Vector.cons x n' xs =>
     (LETE val <- projT2 x;
        LETE fullStruct <- @gatherLetExprVector ty _ xs;
        RetE (BuildStruct _ _ (fun i: Fin.t (S n') =>
                                 match i as il in Fin.t (S nl) return
                                       forall (xs: Vector.t _ nl),
                                         ty (structFromLetExprs xs) ->
                                         (snd (Vector.nth
                                                 (Vector.map (@projT1 _ _)
                                                             (Vector.cons _ x _ xs)) il)) @# ty
                                 with
                                 | Fin.F1 _ => fun _ _ => #val
                                 | Fin.FS _ j => fun _ fullStruct => ReadStruct #fullStruct j
                                 end xs fullStruct))
     )
   end).
Local Close Scope kami_expr.



(*
 * Kami Rewrite
   + Inlining Theorem (moderate)
   + Compiler verification (difficult)
 * PUAR: Linux/Certikos
 *)
