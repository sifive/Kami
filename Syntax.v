Require Export Bool Ascii String FunctionalExtensionality Psatz PeanoNat.
Require Export Kami.StdLib.Fin.
Require Export Kami.StdLib.Vector.
Require Export Kami.Lib.VectorFacts Kami.Lib.EclecticLib.
Require Export List.

Require Export Kami.Lib.Word Kami.Lib.WordProperties.
Export ListNotations.

Require Import Permutation.
Require Import ZArith.

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
| Struct  : forall {n}, (Fin n -> Kind) -> (Fin n -> string) -> Kind
| Array   : nat -> Kind -> Kind.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type) (c : t) : FullKind.

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstStruct {n} fk fs (fv: forall i, ConstT (fk i)): ConstT (@Struct n fk fs)
| ConstArray {n} {k} (fk: Fin n -> ConstT k): ConstT (Array n k).

Inductive ConstFullT: FullKind -> Type :=
| SyntaxConst k: ConstT k -> ConstFullT (SyntaxKind k)
| NativeConst t (c' : t) : ConstFullT (NativeKind c').

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

Notation Default := (getDefaultConst _).

Fixpoint getDefaultConstFullKind (k : FullKind) : ConstFullT k :=
  match k with
  | SyntaxKind k' => SyntaxConst (getDefaultConst k')
  | NativeKind t c' => NativeConst c'
  end.

Inductive UniBoolOp: Set :=
| Neg: UniBoolOp.

Inductive CABoolOp: Set :=
| And: CABoolOp
(* | Or: CABoolOp *)
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
(* | Bor: CABitOp *)
| Bxor: CABitOp.

Inductive BinBitBoolOp: nat -> nat -> Set :=
| LessThan n: BinBitBoolOp n n.

Fixpoint type (k: Kind): Type :=
  match k with
  | Bool => bool
  | Bit n => word n
  | Struct n fk fs => forall i, type (fk i)
  | Array n k' => Fin n -> type k'
  end.

Fixpoint evalConstT k (e: ConstT k): type k :=
  match e in ConstT k return type k with
    | ConstBool b => b
    | ConstBit n w => w
    | ConstStruct n fk fs fv => fun i => evalConstT (fv i)
    | ConstArray n k' fv => fun i => evalConstT (fv i)
  end.

Section Phoas.
  Variable ty: Kind -> Type.
  Definition fullType k := match k with
                             | SyntaxKind k' => ty k'
                             | NativeKind k' c' => k'
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
  | ReadStruct {n} (fk: Fin n -> Kind) (fs: Fin n -> string)
               (e: Expr (SyntaxKind (Struct fk fs))) i:
      Expr (SyntaxKind (fk i))
  | BuildStruct {n} (fk: Fin n -> Kind) (fs: Fin n -> string)
                (fv: forall i, Expr (SyntaxKind (fk i))):
      Expr (SyntaxKind (Struct fk fs))
  | ReadArray {n} m k: Expr (SyntaxKind (Array n k)) ->
                   Expr (SyntaxKind (Bit m)) ->
                   Expr (SyntaxKind k)
  | ReadArrayConst {n} k: Expr (SyntaxKind (Array n k)) ->
                        Fin n ->
                        Expr (SyntaxKind k)
  | BuildArray {n} k: (Fin n -> Expr (SyntaxKind k)) -> Expr (SyntaxKind (Array n k))
  | Kor k: list (Expr (SyntaxKind k)) -> Expr (SyntaxKind k)
  | ToNative k:
      Expr (SyntaxKind k) -> Expr (@NativeKind (type k) (evalConstT (getDefaultConst k)))
  | FromNative k: Expr (@NativeKind (type k) (evalConstT (getDefaultConst k))) ->
                  Expr (SyntaxKind k).

  Definition UpdateArray n m k (e: Expr (SyntaxKind (Array n k)))
             (i: Expr (SyntaxKind (Bit m)))
             (v: Expr (SyntaxKind k)) :=
    BuildArray (fun i' : Fin n =>
                  ITE (Eq i (Const (natToWord _ (proj1_sig (to_nat i'))))) v
                      (ReadArrayConst e i')).

  Definition UpdateArrayConst n k (e: Expr (SyntaxKind (Array n k)))
             (i: Fin n)
             (v: Expr (SyntaxKind k)) :=
    BuildArray (fun i' : Fin n =>
                  match Kami.StdLib.Fin.eq_dec i i' with
                  | left _ => v
                  | right _ => ReadArrayConst e i'
                  end).

  Definition UpdateStruct n (fk: Fin n -> Kind) (fs: Fin n -> string)
             (e: Expr (SyntaxKind (Struct fk fs))) i (v: Expr (SyntaxKind (fk i))) :=
    BuildStruct fk fs (fun i' => match Kami.StdLib.Fin.eq_dec i i' with
                                 | left pf =>
                                   match pf in _ = Y return
                                         Expr (SyntaxKind (fk Y)) with
                                   | eq_refl => v
                                   end
                                 | right _ => ReadStruct e i'
                                 end).

  Section BitOps.
    Definition castBits ni no (pf: ni = no) (e: Expr (SyntaxKind (Bit ni))) :=
      nat_cast (fun n => Expr (SyntaxKind (Bit n))) pf e.

    Definition Slt n (e1 e2: Expr (SyntaxKind (Bit (n + 1)))) :=
      Eq (Eq (UniBit (TruncMsb n 1) e1) (UniBit (TruncMsb n 1) e2)) (BinBitBool (LessThan _) e1 e2).

    Definition ConstExtract lsb n msb (e: Expr (SyntaxKind (Bit (lsb + n + msb)))): Expr (SyntaxKind (Bit n)) :=
      UniBit (TruncMsb lsb n) (UniBit (TruncLsb (lsb + n) msb) e).

    Definition OneExtend msb lsb (e: Expr (SyntaxKind (Bit lsb))): Expr (SyntaxKind (Bit (lsb + msb))) :=
      (BinBit (Concat msb lsb) (Const (wones msb))) e.

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
    
    Definition OneExtendTruncLsb ni no (e: Expr (SyntaxKind (Bit ni))):
      Expr (SyntaxKind (Bit no)).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@OneExtend (no - ni) ni e)
        | right isGe => UniBit (TruncLsb no (ni - no)) (castBits _ e)
        end; abstract lia.
    Defined.

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

    Fixpoint sumSizes {n}: (Fin n -> nat) -> nat :=
      match n return (Fin n -> nat) -> nat with
      | 0 => fun _ => 0
      | S m => fun sizes => sumSizes (fun x => sizes (FS x)) + sizes F1
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

    Fixpoint concatStructExpr {n} {struct n}:
      forall (sizes: Fin n -> nat)
             (f: forall i, Expr (SyntaxKind (Bit (sizes i)))),
        Expr (SyntaxKind (Bit (sumSizes sizes))) :=
      match n return forall
          (sizes: Fin n -> nat)
          (f: forall i, Expr (SyntaxKind (Bit (sizes i)))),
          Expr (SyntaxKind (Bit (sumSizes sizes))) with
      | 0 => fun _ _ => Const WO
      | S m => fun sizes f =>
                 BinBit
                   (Concat _ _) (f F1)
                   (@concatStructExpr m (fun x => (sizes (FS x))) (fun x => f (FS x)))
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
    
    Fixpoint sumSizesMsbs {n} : forall i: Fin n, (Fin n -> nat) -> nat :=
      match n as m return forall i : Fin m, (Fin m -> nat) -> nat with
      | 0 => Fin.case0 (fun i => (Fin 0 -> nat) -> nat)
      | S m =>
        fun i =>
          match i with
          | inl _ => fun _ => 0
          | inr j =>
            fun sizes : Fin (S m) -> nat =>
              sumSizesMsbs j (fun k : Fin m => sizes (FS k)) + sizes F1
          end
      end.

    Lemma sumSizesMsbsLt {n} : forall (sizes : Fin n -> nat) (i : Fin n), sumSizesMsbs i sizes + sizes i <= sumSizes sizes.
    Proof.
      induction n as [|m IH].
      + exact (fun sizes => Fin.case0 (fun i => sumSizesMsbs i sizes + sizes i <= sumSizes sizes)).
      + intro sizes; destruct i as [u|j].
        - destruct u; simpl; unfold F1; exact (le_plus_r (sumSizes (fun j : Fin m => sizes (FS j))) (sizes F1)).
        - simpl.
          rewrite <- (Nat.add_assoc
            (sumSizesMsbs j (fun k : Fin m => sizes (FS k)))
            (sizes F1)
            (sizes (inr j : Fin (S m)))).
          rewrite (Nat.add_comm
            (sizes F1)
            (sizes (inr j : Fin (S m)))).
          rewrite (Nat.add_assoc
            (sumSizesMsbs j (fun k : Fin m => sizes (FS k)))
            (sizes (inr j : Fin (S m)))
            (sizes F1)).
          apply (plus_le_compat_r
            (sumSizesMsbs j (fun k : Fin m => sizes (FS k)) + sizes (inr j))
            (sumSizes (fun k : Fin m => sizes (FS k)))
            (sizes F1)).
          exact (IH (fun k : Fin m => sizes (FS k)) j).
      Qed.
            
    Lemma helper_sumSizes n : forall (i: Fin n),
      forall (sizes: Fin n -> nat),
        sumSizes sizes =
        (sumSizes sizes - (sumSizesMsbs i sizes + sizes i)) + sizes i + sumSizesMsbs i sizes.
    Proof.
      intros i sizes.
      rewrite (Nat.add_comm _ (sumSizesMsbs i sizes)).
      rewrite (Nat.add_comm _ (sizes i)).
      rewrite (Nat.add_assoc
        (sumSizesMsbs i sizes)
        (sizes i)
        _).
      rewrite (le_plus_minus_r
        (sumSizesMsbs i sizes + sizes i)
        (sumSizes sizes)
        (sumSizesMsbsLt sizes i)). 
      reflexivity.
    Qed.
    
    Lemma helper_array {n} (i: Fin n):
      forall size_k,
        n * size_k =
          (proj1_sig (to_nat i) * size_k) + size_k +
          (n * size_k - ((proj1_sig (to_nat i) * size_k) + size_k)) .
    Proof.
      intro size_k.
      set (Hlt :=
        @mult_le_compat_r
         (S (proj1_sig (to_nat i)))
         n
         size_k
         (proj2_sig (to_nat i))
        : S (proj1_sig (to_nat i)) * size_k <= n * size_k).
      simpl in Hlt.
      rewrite (Nat.add_comm size_k (proj1_sig (to_nat i) * size_k)) in Hlt.
      rewrite (le_plus_minus_r
        (proj1_sig (to_nat i) * size_k + size_k)
        (n * size_k) Hlt).
      reflexivity.
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
                           (@castBits _ _ (helper_sumSizes n i (fun j => size (fk j))) e)))
      | Array n k =>
        fun e =>
          BuildArray
            (fun i => unpack _ (ConstExtract (proj1_sig (to_nat i) * size k) _ _
                                             (@castBits _ _ (helper_array _ _) e)))
      end.
  End BitOps.
  
  Inductive BitFormat :=
  | Binary
  | Decimal
  | Hex.

  Definition FullBitFormat := (nat * BitFormat)%type.

  Inductive FullFormat: Kind -> Type :=
  | FBool: nat -> BitFormat -> FullFormat Bool
  | FBit n: nat -> BitFormat -> FullFormat (Bit n)
  | FStruct n fk fs: (forall i, FullFormat (fk i)) -> FullFormat (@Struct n fk fs)
  | FArray n k: FullFormat k -> FullFormat (@Array n k).

  Fixpoint fullFormatHex k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Hex
    | Bit n => FBit n ((n+3)/4) Hex
    | Struct n fk fs => FStruct n fk fs (fun i => fullFormatHex (fk i))
    | Array n k => FArray n (fullFormatHex k)
    end.

  Fixpoint fullFormatBinary k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Binary
    | Bit n => FBit n n Binary
    | Struct n fk fs => FStruct n fk fs (fun i => fullFormatBinary (fk i))
    | Array n k => FArray n (fullFormatBinary k)
    end.

  Fixpoint fullFormatDecimal k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Decimal
    | Bit n => FBit n 0 Decimal
    | Struct n fk fs => FStruct n fk fs (fun i => fullFormatDecimal (fk i))
    | Array n k => FArray n (fullFormatDecimal k)
    end.

  Inductive SysT: Type :=
  | DispString (s: string): SysT
  | DispExpr k (e: Expr (SyntaxKind k)) (ff: FullFormat k): SysT
  | Finish: SysT.

  Definition DispHex k (e: Expr (SyntaxKind k)) :=
    DispExpr e (fullFormatHex k).
  
  Definition DispBinary k (e: Expr (SyntaxKind k)) :=
    DispExpr e (fullFormatBinary k).
    
  Definition DispDecimal k (e: Expr (SyntaxKind k)) :=
    DispExpr e (fullFormatDecimal k).

  Inductive LetExprSyntax k :=
  | NormExpr (e: Expr (SyntaxKind k)): LetExprSyntax k
  | SysE (ls: list SysT) (e: LetExprSyntax k): LetExprSyntax k
  | LetE k' (e: LetExprSyntax k') (cont: ty k' -> LetExprSyntax k): LetExprSyntax k
  | IfElseE (pred: Expr (SyntaxKind Bool)) k' (t f: LetExprSyntax k') (cont: ty k' -> LetExprSyntax k):
      LetExprSyntax k.
    
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
  | Sys: list SysT -> ActionT lretT -> ActionT lretT
  | Return: Expr (SyntaxKind lretT) -> ActionT lretT.

  Fixpoint convertLetExprSyntax_ActionT k (e: LetExprSyntax k) :=
    match e in LetExprSyntax _ return ActionT k with
    | NormExpr e' => Return e'
    | LetE _ e' cont => LetAction (convertLetExprSyntax_ActionT e') (fun v => convertLetExprSyntax_ActionT (cont v))
    | SysE ls cont => Sys ls (convertLetExprSyntax_ActionT cont)
    | IfElseE pred k' t f cont => IfElse pred (convertLetExprSyntax_ActionT t)
                                         (convertLetExprSyntax_ActionT f)
                                         (fun v => convertLetExprSyntax_ActionT (cont v))
    end.
End Phoas.

Definition Action (retTy : Kind) := forall ty, ActionT ty retTy.

Definition Signature := (Kind * Kind)%type.
Definition MethodT (sig : Signature) := forall ty, ty (fst sig) -> ActionT ty (snd sig).

Notation Void := (Bit 0).

Notation Attribute A := (string * A)%type (only parsing).

Section RegInitValT.
  Variable x: FullKind.
  Definition RegInitValT := option (ConstFullT x).
End RegInitValT.

Definition RegInitT := Attribute (sigT RegInitValT).
Definition DefMethT := Attribute (sigT MethodT).
Definition RuleT := Attribute (Action Void).

Inductive RegFileInitT (IdxNum: nat) (Data: Kind) :=
| RFNonFile (init: option (ConstT Data))
| RFFile (isAscii: bool) (isArg: bool) (file: string) (offset size: nat) (init: Fin IdxNum -> ConstT Data).

Record SyncRead := { readReqName : string ;
                     readResName : string ;
                     readRegName : string }.

Inductive RegFileReaders :=
| Async (reads: list string)
| Sync (isAddr: bool) (reads: list SyncRead).

Record RegFileBase := { rfIsWrMask : bool ;
                        rfNum: nat ;
                        rfDataArray: string ;
                        rfRead: RegFileReaders ;
                        rfWrite: string ;
                        rfIdxNum: nat ;
                        rfData: Kind ;
                        rfInit: RegFileInitT rfIdxNum rfData }.
                       
Inductive BaseModule: Type :=
| BaseRegFile (rf: RegFileBase)
| BaseMod (regs: list RegInitT) (rules: list RuleT) (dms: list DefMethT).

Inductive Mod: Type :=
| Base (m: BaseModule): Mod
| HideMeth (m: Mod) (meth: string): Mod
| ConcatMod (m1 m2: Mod): Mod.

Coercion Base: BaseModule >-> Mod.

Notation getKindAttr ls := (map (fun x => (fst x, projT1 (snd x))) ls).

Definition getRegFileRegisters m :=
  match m with
  | @Build_RegFileBase isWrMask num dataArray readers write IdxNum Data init =>
    (dataArray, existT RegInitValT (SyntaxKind (Array IdxNum Data))
                       match init with
                       | RFNonFile x => match x with
                                        | None => None
                                        | Some init' => Some (SyntaxConst (ConstArray (fun _ => init')))
                                        end
                       | RFFile isAscii isArg file offset size init => Some (SyntaxConst (ConstArray init))
                       end) :: match readers with
                               | Async _ => []
                               | Sync isAddr read =>
                                 if isAddr
                                 then map (fun x => (readRegName x, existT RegInitValT (SyntaxKind (Bit (Nat.log2_up IdxNum)))
                                                                           None)) read
                                 else map (fun x => (readRegName x, existT RegInitValT (SyntaxKind (Array num Data)) None)) read
                               end
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

Definition getStruct ls :=
  (Struct (fun i => snd (nth_Fin ls i)) (fun j => fst (nth_Fin ls j))).
Arguments getStruct : simpl never.

Definition getStructVal ty ls :=
  (BuildStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => Expr ty (SyntaxKind (snd x)))
                                      ls k (projT2 (nth_Fin ls (Kami.StdLib.Fin.cast k (map_length_red (@projT1 _ _) ls)))))).
Arguments getStructVal : simpl never.

Definition getStructConst ls :=
  (ConstStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => ConstT (snd x))
                                      ls k (projT2 (nth_Fin ls (Kami.StdLib.Fin.cast k (map_length_red (@projT1 _ _) ls)))))).
Arguments getStructConst : simpl never. 

Definition WriteRq lgIdxNum Data := (getStruct (cons ("addr", Bit lgIdxNum)
                                                     (cons ("data", Data) nil))).

  (* STRUCT_TYPE { "addr" :: Bit lgIdxNum ; *)
  (*               "data" :: Data }. *)

Definition WriteRqMask lgIdxNum num Data := (getStruct (cons ("addr", Bit lgIdxNum)
                                                             (cons ("data", Array num Data)
                                                                   (cons ("mask", Array num Bool)
                                                                         nil)))).

(* Definition WriteRqMask lgIdxNum num Data := STRUCT_TYPE { "addr" :: Bit lgIdxNum ; *)
(*                                                           "data" :: Array num Data ; *)
(*                                                           "mask" :: Array num Bool }. *)

Definition buildNumDataArray num dataArray IdxNum Data ty (idx: ty (Bit (Nat.log2_up IdxNum))) :=
  ReadReg dataArray (SyntaxKind (Array IdxNum Data))
          (fun val =>
             Return (BuildArray (fun i: Fin num =>
                                   ReadArray
                                     (Var ty _ val)
                                     (CABit Add (Var ty (SyntaxKind _) idx ::
                                                     Const ty (natToWord _ (proj1_sig (to_nat i))) :: nil))))).

Definition updateNumDataArray num dataArray IdxNum Data ty (idxData: ty (WriteRq (Nat.log2_up IdxNum)
                                                                                 (Array num Data))):
  ActionT ty Void :=
  ReadReg dataArray (SyntaxKind (Array IdxNum Data))
          (fun val =>
             WriteReg dataArray
                      (fold_left (fun newArr i =>
                                    (UpdateArray newArr
                                                 (CABit Add (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                        F1 ::
                                                                        Const ty (natToWord _ (proj1_sig (to_nat i))) ::
                                                                        nil))
                                                 (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                             (FS F1)) i))) (getFins num)
                                 (Var ty (SyntaxKind (Array IdxNum Data)) val))
                      (Return (Const _ WO))).

Definition updateNumDataArrayMask num dataArray IdxNum Data ty (idxData: ty (WriteRqMask
                                                                               (Nat.log2_up IdxNum) num Data)):
  ActionT ty Void :=
  ReadReg dataArray (SyntaxKind (Array IdxNum Data))
          (fun val =>
             WriteReg dataArray
                      (fold_left (fun newArr i =>
                                    ITE
                                      (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData) (FS (FS F1))) i)
                                      (UpdateArray newArr
                                                   (CABit Add (ReadStruct
                                                                 (Var ty (SyntaxKind _) idxData)
                                                                 F1 :: Const ty (natToWord _ (proj1_sig (to_nat i))) ::
                                                                 nil))
                                                   (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                               (FS F1)) i))
                                      newArr
                                 ) (getFins num)
                                 (Var ty (SyntaxKind (Array IdxNum Data)) val))
                      (Return (Const _ WO))).

Definition readRegFile num dataArray (read: list string) IdxNum Data :=
  (map (fun x => (x, existT MethodT (Bit (Nat.log2_up IdxNum), Array num Data)
                            (buildNumDataArray num dataArray IdxNum Data))) read).

Definition writeRegFileFn (isWrMask: bool) num dataArray (write: string) IdxNum Data :=
  (write,
   if isWrMask
   then existT MethodT (WriteRqMask (Nat.log2_up IdxNum) num Data, Void)
               (updateNumDataArrayMask num dataArray IdxNum Data)
   else existT MethodT (WriteRq (Nat.log2_up IdxNum) (Array num Data), Void)
               (updateNumDataArray num dataArray IdxNum Data)).

Definition readSyncRegFile (isAddr: bool) num dataArray (read: list SyncRead) IdxNum Data :=
  if isAddr
  then
    ((map (fun r =>
             (readReqName r,
              existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                     (fun ty idx =>
                        WriteReg (readRegName r) (Var ty (SyntaxKind _) idx)
                                 (Return (Const _ WO)))))) read)
      ++
      (map (fun r =>
              (readResName r,
               existT MethodT (Void, Array num Data)
                      (fun ty _ =>
                         ReadReg (readRegName r) (SyntaxKind (Bit (Nat.log2_up IdxNum)))
                                 (buildNumDataArray num dataArray IdxNum Data ty))))
           read)
  else
    ((map (fun r =>
             (readReqName r,
              existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                     (fun ty idx =>
                        LetAction (buildNumDataArray num dataArray IdxNum Data ty idx)
                                  (fun vals => WriteReg (readRegName r) (Var ty (SyntaxKind _) vals)
                                                        (Return (Const _ WO)))))) read)
      ++
      (map (fun r =>
              (readResName r,
               existT MethodT (Void, Array num Data)
                      (fun ty x =>
                         ReadReg (readRegName r) (SyntaxKind (Array num Data))
                                 (fun data =>
                                    Return (Var ty (SyntaxKind (Array num Data)) data)))))
           read)).

Definition getRegFileMethods m :=
  match m with
  | @Build_RegFileBase isWrMask num dataArray readers write IdxNum Data init =>
    writeRegFileFn isWrMask num dataArray write IdxNum Data ::
                   match readers with
                   | Async read =>
                     readRegFile num dataArray read IdxNum Data
                   | Sync isAddr read =>
                     readSyncRegFile isAddr num dataArray read IdxNum Data
                   end
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

Section WfBaseMod.

  Variable ty : Kind -> Type.
  
  Section WfActionT.
    Variable regs : list (string * {x : FullKind & RegInitValT x}).

    Inductive WfActionT: forall lretT, ActionT ty lretT -> Prop :=
    | WfMCall meth s e lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (MCall meth s e c)
    | WfLetExpr k (e: Expr ty k) lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (LetExpr e c)
    | WfLetAction k (a: ActionT ty k) lretT c: WfActionT a -> (forall v, WfActionT (c v)) -> @WfActionT lretT (LetAction a c)
    | WfReadNondet k lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (ReadNondet k c)
    | WfReadReg r k lretT c: (forall v, WfActionT (c v)) -> In (r, k) (getKindAttr regs) ->
                             @WfActionT lretT (ReadReg r k c)
    | WfWriteReg r k (e: Expr ty k) lretT c: WfActionT c  -> In (r, k) (getKindAttr regs) ->
                                               @WfActionT lretT (WriteReg r e c)
    | WfIfElse p k (atrue: ActionT ty k) afalse lretT c: (forall v, WfActionT (c v)) -> WfActionT atrue ->
                                                           WfActionT afalse -> @WfActionT lretT (IfElse p atrue afalse c)
    | WfSys ls lretT c: WfActionT c -> @WfActionT lretT (Sys ls c)
    | WfReturn lretT e: @WfActionT lretT (Return e).

    Definition lookup{K X} : (K -> K -> bool) -> K -> list (K * X) -> option X :=
      fun eqbk key pairs => match List.find (fun p => eqbk key (fst p)) pairs with
                            | Some p => Some (snd p)
                            | None => None
                            end.

    Lemma lookup_cons : forall K V (eqb : K -> K -> bool) k k' v (ps : list (K*V)), lookup eqb k ((k',v)::ps) =
      if eqb k k' then Some v else lookup eqb k ps.
    Proof.
      intros.
      unfold lookup.
      unfold find.
      simpl.
      destruct (eqb k k'); auto.
    Qed.

    Fixpoint WfActionT_new{k}(a : ActionT ty k) : Prop :=
    match a with
    | MCall meth s e cont => forall x, WfActionT_new (cont x)
    | LetExpr k e cont => forall x, WfActionT_new (cont x)
    | LetAction k a cont => (WfActionT_new a /\ forall x, WfActionT_new (cont x))
    | ReadNondet k cont => forall x, WfActionT_new (cont x)
    | ReadReg r k' cont => match lookup String.eqb r regs with
                           | None => False
                           | Some (existT k'' _) => k' = k'' /\ forall x, WfActionT_new (cont x)
                           end
    | WriteReg r k' e a => match lookup String.eqb r regs with
                           | None => False
                           | Some (existT k'' _) => k' = k'' /\ WfActionT_new a
                           end
    | IfElse e k1 a1 a2 cont => (WfActionT_new a1 /\ WfActionT_new a2 /\ forall x, WfActionT_new (cont x))
    | Sys _ a => WfActionT_new a
    | Return _ => True
    end.

    Fixpoint WfRules(rules : list RuleT) :=
      match rules with
      | [] => True
      | r::rs => WfActionT_new (snd r ty) /\ WfRules rs
      end.

    Fixpoint WfMeths(meths : list (string * {x : Signature & MethodT x})) :=
      match meths with
      | [] => True
      | m::ms => (forall v, WfActionT_new (projT2 (snd m) ty v)) /\ WfMeths ms
      end.
    
  End WfActionT.

  Definition WfBaseModule (m : BaseModule) :=
    (forall rule, In rule (getRules m) -> WfActionT (getRegisters m) (snd rule ty)) /\
    (forall meth, In meth (getMethods m) -> forall v, WfActionT (getRegisters m) (projT2 (snd meth) ty v)) /\
    NoDup (map fst (getMethods m)) /\ NoDup (map fst (getRegisters m)) /\ NoDup (map fst (getRules m)).

  Definition WfBaseModule_new(m : BaseModule) :=
    (WfRules (getRegisters m) (getRules m)) /\
    (WfMeths (getRegisters m) (getMethods m)) /\
    (NoDup (map fst (getMethods m))) /\
    (NoDup (map fst (getRegisters m))) /\
    (NoDup (map fst (getRules m))).

  Section WfActionT'.

  Variable m : BaseModule.

   Inductive WfActionT': forall lretT, ActionT type lretT -> Prop :=
  | WfMCall' meth s e lretT c v: (WfActionT' (c v)) -> @WfActionT' lretT (MCall meth s e c)
  | WfLetExpr' k (e: Expr type k) lretT c v: (WfActionT' (c v)) -> @WfActionT' lretT (LetExpr e c)
  | WfLetAction' k (a: ActionT type k) lretT c v: WfActionT' a -> (WfActionT' (c v)) -> @WfActionT' lretT (LetAction a c)
  | WfReadNondet' k lretT c v: (WfActionT' (c v)) -> @WfActionT' lretT (ReadNondet k c)
  | WfReadReg' r k lretT c v: (WfActionT' (c v)) -> In (r, k) (getKindAttr (getRegisters m)) ->
                           @WfActionT' lretT (ReadReg r k c)
  | WfWriteReg' r k (e: Expr type k) lretT c: WfActionT' c  -> In (r, k) (getKindAttr (getRegisters m)) ->
                                             @WfActionT' lretT (WriteReg r e c)
  | WfIfElse' p k (atrue: ActionT type k) afalse lretT c v: (WfActionT' (c v)) -> WfActionT' atrue ->
                                                         WfActionT' afalse -> @WfActionT' lretT (IfElse p atrue afalse c)
  | WfSys' ls lretT c: WfActionT' c -> @WfActionT' lretT (Sys ls c)
  | WfReturn' lretT e: @WfActionT' lretT (Return e).

  End WfActionT'.

End WfBaseMod.

  Lemma WfLetExprSyntax k m (e: LetExprSyntax type k): WfActionT (getRegisters m) (convertLetExprSyntax_ActionT e).
  Proof.
    induction e; constructor; auto.
  Qed.

  Lemma WfLetExprSyntax_new k m (e: LetExprSyntax type k): WfActionT_new (getRegisters m) (convertLetExprSyntax_ActionT e).
  Proof.
    induction e; simpl; repeat split; auto.
  Qed.

Section WfBaseModProofs.

Lemma In_getKindAttr : forall r k (regs : list (string * {x : FullKind & RegInitValT x})), In (r,k) (getKindAttr regs) -> In r (map fst regs).
Proof.
  intros.
  rewrite in_map_iff in H.
  dest.
  inv H.
  apply in_map; auto.
Qed.

Lemma In_lookup : forall r k (regs : list (string * {x : FullKind & RegInitValT x})), NoDup (map fst regs) -> In (r,k) (getKindAttr regs) -> exists k' v, k = k' /\ lookup String.eqb r regs = Some (existT _ k' v).
Proof.
  induction regs; intros.
  - destruct H0.
  - destruct H0.
    + destruct a.
      destruct s0.
      destruct r0.
      * inversion H0.
        exists x; eexists.
        split.
        ** auto.
        ** unfold lookup; simpl.
           rewrite String.eqb_refl.
           reflexivity.
      * inversion H0.
        exists k; eexists.
        split.
        ** auto.
        ** unfold lookup; simpl.
           rewrite String.eqb_refl.
           simpl.
           reflexivity.
    + assert (NoDup (map fst regs)).
      inversion H; auto.
      destruct (IHregs H1 H0) as [k' [v [Hk' Hv]]].
      exists k', v.
      split.
      * auto.
      * destruct a.
        destruct s0.
        destruct r0.
        ** rewrite lookup_cons.
           destruct (r =? s) eqn:G.
           *** rewrite String.eqb_eq in G.
               rewrite <- G in H.
               inversion H.
               elim H4.
               eapply In_getKindAttr.
               exact H0.
           *** auto.
        ** rewrite lookup_cons.
           destruct (r =? s) eqn:G.
           *** rewrite String.eqb_eq in G.
               rewrite <- G in H.
               inversion H.
               elim H4.
               eapply In_getKindAttr.
               exact H0.
           *** auto.
Qed.

Lemma lookup_In : forall r k v regs, lookup String.eqb r (regs) = Some (existT RegInitValT k v) -> In (r,k) (getKindAttr regs).
Proof.
  induction regs; intros.
  - discriminate H.
  - destruct a.
    destruct s0.
    rewrite lookup_cons in H.
    + destruct (r =? s) eqn:G.
      * rewrite String.eqb_eq in G.
        inversion H.
        left; simpl; congruence.
      * right.
        apply IHregs.
        auto.
Qed.

Lemma WfActionT_WfActionT_new{ty lret} : forall regs (a : ActionT ty lret), NoDup (map fst regs) -> WfActionT regs a -> WfActionT_new regs a.
Proof.
  intros.
  induction a; simpl; intros.
  - apply H1.
    inversion H0.
    EqDep_subst.
    apply H4.
  - apply H1.
    inversion H0.
    EqDep_subst.
    apply H4.
  - inversion H0.
    split.
    + apply IHa.
      EqDep_subst.
      auto.
    + EqDep_subst.
      intro.
      auto.
  - inversion H0.
    apply H1.
    EqDep_subst.
    auto.
  - inversion H0.
    unfold getRegisters in H7.
    destruct (In_lookup _ _ _ H H7) as [k' [v [Hk Hv]]].
    rewrite Hv.
    split.
    + auto.
    + intro.
      apply H1.
      EqDep_subst.
      apply H5.
  - inversion H0.
    unfold getRegisters in H7.
    destruct (In_lookup _ _ _ H H7) as [k' [v [Hk Hv]]].
    rewrite Hv.
    split.
    + auto.
    + apply IHa.
      EqDep_subst; auto.
  - inversion H0.
   repeat split.
    + apply IHa1.
      EqDep_subst.
      auto.
    + apply IHa2.
      EqDep_subst.
      auto.
    + intro; apply H1.
      EqDep_subst.
      apply H6.
  - apply IHa.
    inversion H0.
    EqDep_subst.
    auto.
  - auto.
Qed.

Lemma wf_rules_In : forall ty regs rules, NoDup (map fst regs) -> (forall rule : RuleT, In rule rules -> WfActionT regs (snd rule ty)) -> WfRules ty regs rules.
Proof.
  induction rules; intros.
  - simpl; auto.
  - simpl.
    split.
    + eapply WfActionT_WfActionT_new.
      * auto.
      * apply H0; left; auto.
    + eapply IHrules.
      * auto.
      * intros.
        apply H0.
        right; auto.
Qed.

Lemma wf_meths_In : forall ty regs dms, NoDup (map fst regs) -> (forall (meth : string * {x : Signature & MethodT x}),
    In meth dms -> forall v : ty (fst (projT1 (snd meth))), WfActionT regs (projT2 (snd meth) ty v)) -> WfMeths ty regs dms.
Proof.
  induction dms; intros.
  - simpl; auto.
  - simpl.
    split.
    + intro; eapply WfActionT_WfActionT_new; auto.
      apply H0.
      left; auto.
    + eapply IHdms.
      * auto.
      * intros.
        apply H0.
        right; auto.
Qed.

(* 
Lemma wf_meths_In_BaseRegFile : forall ty rfs (ms : list (string * {x : Signature & MethodT x})), NoDup (map fst (getRegisters (BaseRegFile rfs))) ->   (forall meth, In meth ms ->
 forall v : ty (fst (projT1 (snd meth))) , WfActionT (BaseRegFile rfs) (projT2 (snd meth) ty v)) -> WfMeths (BaseRegFile rfs) ty ms.
Proof.
  induction ms; intros.
  - simpl; auto.
  - simpl; split.
    + intro; eapply WfActionT_WfActionT_new.
      * auto.
      * apply H0.
        left; auto.
    + apply IHms; auto.
      intros; apply H0; right; auto.
Qed.
 *)

Lemma WfBaseModule_WfBaseModule_new : forall ty bm, WfBaseModule ty bm -> WfBaseModule_new ty bm.
Proof.
  intros ty bm [wf_actions [wf_meths [nodup_meths [nodup_regs nodup_rules]]]].
  unfold WfBaseModule_new.
  repeat split; auto.
  - destruct bm.
    + exact I.
    + simpl; eapply wf_rules_In; auto.
  - eapply wf_meths_In; auto.
Qed.

Lemma WfActionT_new_WfActionT{ty lret} : forall (a : ActionT ty lret) m, WfActionT_new m a -> WfActionT m a.
Proof.
  intros.
  induction a; simpl in *.
  - apply WfMCall.
    intro; apply H0; apply H.
  - apply WfLetExpr.
    intro; apply H0; apply H.
  - apply WfLetAction.
    + apply IHa; tauto.
    + intro; apply H0; apply H.
  - apply WfReadNondet.
    intro; apply H0; apply H.
  - apply WfReadReg.
    + intro; apply H0.
      destruct lookup.
      * destruct s; apply H.
      * destruct H.
    + destruct lookup eqn:G.
      * destruct s.
        destruct H.
        rewrite H.
        unfold getRegisters.
        eapply lookup_In.
        exact G.
      * destruct H.
  - apply WfWriteReg.
    + apply IHa.
      destruct lookup.
      * destruct s; apply H.
      * destruct H.
    + destruct lookup eqn:G.
      * destruct s.
        destruct H.
        rewrite H.
        unfold getRegisters.
        eapply lookup_In.
        exact G.
      * destruct H.
  - apply WfIfElse.
    + intro; apply H0; apply H.
    + tauto.
    + tauto.
  - apply WfSys; tauto.
  - apply WfReturn.
Qed.

Lemma WfActionT_new_WfActionT_iff{ty lret} : forall (a : ActionT ty lret) m, NoDup (map fst m) -> WfActionT_new m a <-> WfActionT m a.
Proof.
  intros; split; intro.
  - apply WfActionT_new_WfActionT; auto.
  - apply WfActionT_WfActionT_new; auto.
Qed.

Lemma In_wf_rules : forall ty regs rules, NoDup (map fst regs) -> WfRules ty regs rules -> (forall rule : RuleT, In rule rules -> WfActionT regs (snd rule ty)).
Proof.
  induction rules; intros.
  - destruct H1.
  - simpl in H0; destruct H0.
    destruct H1.
    + eapply WfActionT_new_WfActionT; congruence.
    + apply IHrules; auto.
Qed.

Lemma In_wf_meths : forall ty regs dms, NoDup (map fst regs) -> WfMeths ty regs dms -> forall meth : string * {x : Signature & MethodT x}, In meth dms -> forall v : ty (fst (projT1 (snd meth))),
  WfActionT regs (projT2 (snd meth) ty v).
Proof.
  induction dms; intros.
  - destruct H1.
  - simpl in H0; destruct H0.
    destruct H1.
    + eapply WfActionT_new_WfActionT.
      rewrite H1 in H0.
      apply H0.
    + apply IHdms; auto.
Qed.

Lemma WfBaseModule_new_WfBaseModule : forall ty bm, WfBaseModule_new ty bm -> WfBaseModule ty bm.
Proof.
  intros ty bm [wf_actions [wf_meths [nodup_meths [nodup_regs nodup_rules]]]].
  unfold WfBaseModule.
  repeat split; auto.
  - intros.
    + eapply In_wf_rules; eauto.
  - intros.
    + eapply In_wf_meths; eauto.
Qed.

Lemma WfBaseModule_WfBaseModule_new_iff : forall ty bm, WfBaseModule ty bm <-> WfBaseModule_new ty bm.
Proof.
  intros ty bm; split; intro.
  - apply WfBaseModule_WfBaseModule_new; auto.
  - apply WfBaseModule_new_WfBaseModule; auto.
Qed.

End WfBaseModProofs.

Inductive WfConcatActionT{ty} : forall lretT, ActionT ty lretT -> Mod -> Prop :=
| WfConcatMCall meth s e lretT c m' :(forall v, WfConcatActionT (c v) m') -> ~In meth (getHidden m') ->
                                     @WfConcatActionT ty lretT (MCall meth s e c) m'
| WfConcatLetExpr k (e : Expr ty k) lretT c m' : (forall v, WfConcatActionT (c v) m') ->
                                                   @WfConcatActionT ty lretT (LetExpr e c) m'
| WfConcatLetAction k (a : ActionT ty k) lretT c m' : WfConcatActionT a m' -> (forall v, WfConcatActionT (c v) m') ->
                                                        @WfConcatActionT ty lretT (LetAction a c) m'
| WfConcatReadNondet k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT ty lretT (ReadNondet k c) m'
| WfConcatReadReg r k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT ty lretT (ReadReg r k c) m'
| WfConcatWriteReg r k (e: Expr ty k) lretT c m': WfConcatActionT c m' -> @WfConcatActionT ty lretT (WriteReg r e c) m'
| WfConcatIfElse p k (atrue: ActionT ty k) afalse lretT c m': (forall v, WfConcatActionT (c v) m') ->
                                                                WfConcatActionT atrue m' -> WfConcatActionT afalse m' ->
                                                                @WfConcatActionT ty lretT (IfElse p atrue afalse c) m'
| WfConcatSys ls lretT c m': WfConcatActionT c m' -> @WfConcatActionT ty lretT (Sys ls c) m'
| WfConcatReturn lretT e m': @WfConcatActionT ty lretT (Return e) m'.

Fixpoint WfConcatActionT_new{ty lret}(a : ActionT ty lret)(m : Mod) : Prop :=
  match a with
  | MCall meth s e cont => (~In meth (getHidden m)) /\ forall x, WfConcatActionT_new (cont x) m
  | LetExpr k e cont => forall x, WfConcatActionT_new (cont x) m
  | LetAction k a cont => WfConcatActionT_new a m /\ forall x, WfConcatActionT_new (cont x) m
  | ReadNondet k cont => forall x, WfConcatActionT_new (cont x) m
  | ReadReg r k cont => forall x, WfConcatActionT_new (cont x) m
  | WriteReg r k e a => WfConcatActionT_new a m
  | IfElse e k a1 a2 cont => WfConcatActionT_new a1 m /\ WfConcatActionT_new a2 m /\ forall x, WfConcatActionT_new (cont x) m
  | Sys _ a => WfConcatActionT_new a m
  | Return _ => True
  end.

Lemma WfConcatActionT_WfConcatActionT_new : forall ty lret m (a : ActionT ty lret), WfConcatActionT a m -> WfConcatActionT_new a m.
Proof.
  intros ty lret m a wf_a.
  induction a; inversion wf_a; simpl; EqDep_subst; auto.
Qed.

Lemma WfConcatActionT_new_WfConcatActionT : forall ty lret m (a : ActionT ty lret), WfConcatActionT_new a m -> WfConcatActionT a m.
Proof.
  intros ty lret m a wf_a.
  induction a; simpl in wf_a; econstructor; auto; try tauto.
  - intro; apply H; apply wf_a.
  - intro; apply H; apply wf_a.
  - intro; apply H; apply wf_a; auto.
Qed.

Lemma WfConcatActionT_WfConcatActionT_new_iff : forall ty lret m (a : ActionT ty lret), WfConcatActionT a m <-> WfConcatActionT_new a m.
Proof.
  intros ty lret m a; split; intro.
  - apply WfConcatActionT_WfConcatActionT_new; auto.
  - apply WfConcatActionT_new_WfConcatActionT; auto.
Qed.

Definition WfConcat ty m m' :=
  (forall rule, In rule (getAllRules m) -> WfConcatActionT (snd rule ty) m') /\
  (forall meth, In meth (getAllMethods m) -> forall v, WfConcatActionT (projT2 (snd meth) ty v) m').

Definition WfConcat_new ty m m' :=
  (forall rule, In rule (getAllRules m) -> WfConcatActionT_new (snd rule ty) m') /\
  (forall meth, In meth (getAllMethods m) -> forall v, WfConcatActionT_new (projT2 (snd meth) ty v) m').

Lemma WfConcat_WfConcat_new_iff : forall ty m m', WfConcat ty m m' <-> WfConcat_new ty m m'.
Proof.
  unfold WfConcat, WfConcat_new; intros; repeat split; intros; destruct H.
  - rewrite <- WfConcatActionT_WfConcatActionT_new_iff; auto.
  - rewrite <- WfConcatActionT_WfConcatActionT_new_iff; auto.
  - rewrite WfConcatActionT_WfConcatActionT_new_iff; auto.
  - rewrite WfConcatActionT_WfConcatActionT_new_iff; auto.
Qed.

Section WfMod.
  Variable ty : Kind -> Type.
  Inductive WfMod : Mod -> Prop :=
  | BaseWf m (HWfBaseModule: WfBaseModule ty m): WfMod (Base m)
  | HideMethWf m s (HHideWf: In s (map fst (getAllMethods m))) (HWf: WfMod m): WfMod (HideMeth m s)
  | ConcatModWf m1 m2 (HDisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2))
                (HDisjRules: DisjKey (getAllRules m1) (getAllRules m2))
                (HDisjMeths: DisjKey (getAllMethods m1) (getAllMethods m2))
                (HWf1: WfMod m1) (HWf2: WfMod m2)(WfConcat1: WfConcat ty m1 m2)
                (WfConcat2 : WfConcat ty m2 m1): WfMod (ConcatMod m1 m2).

Fixpoint WfMod_new(m : Mod) : Prop :=
  match m with
  | Base m => WfBaseModule_new ty m
  | HideMeth m s => In s (map fst (getAllMethods m)) /\ WfMod_new m
  | ConcatMod m1 m2 => DisjKey (getAllRegisters m1) (getAllRegisters m2) /\ DisjKey (getAllRules m1) (getAllRules m2) /\ DisjKey (getAllMethods m1) (getAllMethods m2) /\
                         WfMod_new m1 /\ WfMod_new m2 /\ WfConcat_new ty m1 m2 /\ WfConcat_new ty m2 m1
  end.

End WfMod.

Lemma WfMod_WfMod_new : forall ty m, WfMod ty m -> WfMod_new ty m.
Proof.
  intros ty m wf_m; induction m; inversion wf_m; simpl.
  - rewrite <- WfBaseModule_WfBaseModule_new_iff; auto.
  - auto.
  - repeat rewrite <- WfConcat_WfConcat_new_iff; tauto.
Qed.

Lemma WfMod_new_WfMod : forall ty m, WfMod_new ty m -> WfMod ty m.
Proof.
  intros ty m wf_m; induction m; inversion wf_m; simpl.
  - econstructor; auto; simpl in wf_m.
    unfold WfBaseModule.
    unfold WfBaseModule_new in wf_m; dest.
    repeat split; try auto.
    + intro; apply In_wf_rules; auto.
    + intro; apply In_wf_meths; auto.
  - econstructor; auto.
  - repeat rewrite <- WfConcat_WfConcat_new_iff in H0; econstructor; try tauto.
Qed.

Lemma WfMod_new_WfMod_iff : forall ty m, WfMod_new ty m <-> WfMod ty m.
Proof.
  intros ty m; split; eauto using WfMod_new_WfMod, WfMod_WfMod_new.
Qed.

Record ModWf ty : Type := { module :> Mod;
                            wfMod : WfMod ty module }.

Record ModWf_new ty : Type := { module_new :> Mod;
  wfMod_new : WfMod_new ty module_new }.

Record ModWfOrd ty := { modWf :> ModWf ty;
                     modOrd : list string }.

Record ModWfOrd_new ty := { modWf_new :> ModWf_new ty;
                            modOrd_new : list string }.

Record BaseModuleWf ty :=
  { baseModule :> BaseModule ;
    wfBaseModule : WfBaseModule ty baseModule }.

Record BaseModuleWf_new ty :=
  { baseModule_new :> BaseModule ;
    wfBaseModule_new : WfBaseModule_new ty baseModule_new }.

Record BaseModuleWfOrd ty :=
  { baseModuleWf :> BaseModuleWf ty;
    baseModuleOrd : list string }.

Record BaseModuleWfOrd_new ty :=
  { baseModuleWf_new :> BaseModuleWf_new ty ;
    baseModuleOrd_new : list string }.

Definition getModWf ty (m: BaseModuleWf ty) :=
  {| module := m;
     wfMod := BaseWf (wfBaseModule m) |}.

Definition getModWfOrd ty (m: BaseModuleWfOrd ty) :=
  {| modWf := getModWf m;
     modOrd := baseModuleOrd m |}.

Coercion getModWf: BaseModuleWf >-> ModWf.
Coercion getModWfOrd: BaseModuleWfOrd >-> ModWfOrd.

Section NoCallActionT.
  Variable ls: list DefMethT.
  Variable ty : Kind -> Type.
  
  Inductive NoCallActionT: forall k , ActionT ty k -> Prop :=
  | NoCallMCall meth s e lretT c: ~ In (meth, s) (getKindAttr ls) -> (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (MCall meth s e c)
  | NoCallLetExpr k (e: Expr ty k) lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (LetExpr e c)
  | NoCallLetAction k (a: ActionT ty k) lretT c: NoCallActionT a -> (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (LetAction a c)
  | NoCallReadNondet k lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (ReadNondet k c)
  | NoCallReadReg r k lretT c: (forall v, NoCallActionT (c v)) -> @NoCallActionT lretT (ReadReg r k c)
  | NoCallWriteReg r k (e: Expr ty k) lretT c: NoCallActionT c  -> @NoCallActionT lretT (WriteReg r e c)
  | NoCallIfElse p k (atrue: ActionT ty k) afalse lretT c: (forall v, NoCallActionT (c v)) -> NoCallActionT atrue -> NoCallActionT afalse -> @NoCallActionT lretT (IfElse p atrue afalse c)
  | NoCallSys ls lretT c: NoCallActionT c -> @NoCallActionT lretT (Sys ls c)
  | NoCallReturn lretT e: @NoCallActionT lretT (Return e).
End NoCallActionT.

Section NoSelfCallBaseModule.
  Variable m: BaseModule.
  
  Definition NoSelfCallRuleBaseModule (rule : Attribute (Action Void)) :=
    forall ty, NoCallActionT (getMethods m) (snd rule ty).
  
  Definition NoSelfCallRulesBaseModule :=
    forall rule ty, In rule (getRules m) ->
                    NoCallActionT (getMethods m) (snd rule ty).
  
  Definition NoSelfCallMethsBaseModule :=
    forall meth ty, In meth (getMethods m) ->
                 forall (arg: ty (fst (projT1 (snd meth)))), NoCallActionT (getMethods m) (projT2 (snd meth) ty arg).

  Definition NoSelfCallBaseModule :=
    NoSelfCallRulesBaseModule /\ NoSelfCallMethsBaseModule.
End NoSelfCallBaseModule.







(* Semantics *)

Definition mk_eq : forall m n, (m =? n)%nat = true -> m = n.
Proof.
  induction m.
  - destruct n.
    + auto.
    + intro; discriminate.
  - destruct n.
    + intro; discriminate.
    + simpl.
      intro.
      f_equal.
      apply IHm.
      exact H.
Defined.

Fixpoint Kind_decb(k1 k2 : Kind) : bool.
Proof.
  refine (
    match k1,k2 with
    | Bool, Bool => true
    | Bit n, Bit m => Nat.eqb n m
    | Array n k, Array m k' => Nat.eqb n m && Kind_decb k k'
    | Struct n ks fs, Struct m ks' fs' => _
    | _,_ => false
    end).
  destruct (Nat.eqb n m) eqn:G.
  exact (Fin_forallb (fun i => Kind_decb (ks i) (ks' (Fin.cast i (mk_eq _ _ G)))) && Fin_forallb (fun i => String.eqb (fs i) (fs' (Fin.cast i (mk_eq _ _ G))))).
  exact false.
Defined.

Lemma Kind_decb_refl : forall k, Kind_decb k k = true.
Proof.
  induction k; simpl; auto.
  - apply Nat.eqb_refl.
  -
    rewrite silly_lemma_true with (pf := (Nat.eqb_refl _)) by apply Nat.eqb_refl.
    rewrite andb_true_iff; split; rewrite Fin_forallb_correct; intros.
    + rewrite (hedberg Nat.eq_dec _ eq_refl); simpl; rewrite <- (cast_eq i (eq_refl n)); apply H.
    + rewrite (hedberg Nat.eq_dec _ eq_refl); simpl; rewrite <- (cast_eq i (eq_refl n)); apply String.eqb_refl.
  - rewrite andb_true_iff; split; auto.
    apply Nat.eqb_refl.
Qed.

Lemma Kind_decb_eq : forall k1 k2, Kind_decb k1 k2 = true <-> k1 = k2.
Proof.
  induction k1; intros; destruct k2; split; intro; try (reflexivity || discriminate).
  - simpl in H; rewrite Nat.eqb_eq in H; congruence.
  - inversion H; simpl; apply Nat.eqb_refl.
  - destruct (n =? n0)%nat eqn:G.
    + simpl in H0.
      rewrite (@silly_lemma_true bool (n =? n0)%nat _ _ G) in H0 by auto.
      pose proof G. (* <=== *)
      rewrite Nat.eqb_eq in H1 by auto.
      rewrite andb_true_iff in H0; destruct H0 as [G1 G2]; rewrite Fin_forallb_correct in G1,G2; subst.
      rewrite (hedberg Nat.eq_dec _ eq_refl) in G1,G2; simpl in *.
      setoid_rewrite H in G1.
      setoid_rewrite String.eqb_eq in G2.
      f_equal; extensionality i.
      * rewrite (G1 i).
        rewrite <- (cast_eq i (eq_refl)).
        reflexivity.
      * rewrite (G2 i).
        rewrite <- (cast_eq i (eq_refl)).
        reflexivity.
    + simpl in H0.
      rewrite silly_lemma_false in H0; try discriminate; auto.
  - rewrite H0; apply Kind_decb_refl.
  - simpl in H; rewrite andb_true_iff in H.
    destruct H as [H1 H2]; rewrite Nat.eqb_eq in H1; rewrite IHk1 in H2; congruence.
  - simpl.
    rewrite andb_true_iff; inversion H; split.
    + apply Nat.eqb_refl.
    + rewrite <- H2, IHk1; reflexivity.
Qed.

Lemma Kind_dec (k1 k2 : Kind): {k1 = k2} + {k1 <> k2}.
Proof.
  destruct (Kind_decb k1 k2) eqn:G.
  left; abstract (rewrite Kind_decb_eq in G; auto).
  right; abstract (intro;
                   rewrite <- Kind_decb_eq in H;
                   rewrite H in G; discriminate).
Defined.

Definition Signature_decb : Signature -> Signature -> bool :=
  fun '(k,l) '(k',l') => Kind_decb k k' && Kind_decb l l'.

Lemma Signature_decb_eq : forall s1 s2, Signature_decb s1 s2 = true <-> s1 = s2.
Proof.
  intros [] []; simpl; rewrite andb_true_iff; repeat rewrite Kind_decb_eq; firstorder congruence.
Qed.

Definition Signature_dec (s1 s2 : Signature) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct (Signature_decb s1 s2) eqn:G.
  left; abstract (rewrite <- Signature_decb_eq; auto).
  right; (intro;
          rewrite <- Signature_decb_eq in H;
          rewrite H in G; discriminate).
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
    + destruct (IHn (fun i => k (FS i)) (fun i => X (FS i)) (fun i => s (FS i))
                    (fun i => e1 (FS i)) (fun i => e2 (FS i))).
      * destruct (X F1 (e1 F1) (e2 F1)).
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
      destruct (IHn (fun i => e1 (FS i)) (fun i => e2 (FS i))).
      * destruct (IHk (e1 F1) (e2 F1)).
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
    (* | Or => fold_left orb ws false *)
    | Xor => fold_left xorb ws false
  end.

Definition evalUniBit n1 n2 (op: UniBitOp n1 n2): word n1 -> word n2 :=
  match op with
  | Inv n => (@wnot n)
  | TruncLsb lsb msb => truncLsb 
  | TruncMsb lsb msb => truncMsb
  | UAnd n =>  fun w => boolToWord 1 (@wuand n w)
  | UOr n => fun w => boolToWord 1 (@wuor n w)
  | UXor n => fun w => boolToWord 1 (@wuxor n w)
  end.

Definition wneg_simple sz (x: word sz) := wnot x ^+ (natToWord _ 1).

Definition wminus_simple sz (x y: word sz) := x ^+ (wneg_simple y).

Lemma wneg_simple_wneg sz: forall (x: word sz), wneg_simple x = wneg x.
Proof.
  unfold wneg_simple.
  intros.
  rewrite wneg_wnot.
  rewrite wminus_wplus_undo.
  reflexivity.
Qed.

Lemma wminus_simple_wminus sz: forall (x y: word sz), wminus_simple x y = wsub x y.
Proof.
  unfold wminus_simple.
  intros.
  rewrite wneg_simple_wneg.
  rewrite wminus_def.
  reflexivity.
Qed.

Definition evalBinBit n1 n2 n3 (op: BinBitOp n1 n2 n3)
  : word n1 -> word n2 -> word n3 :=
  match op with
    | Sub n => @wsub n
    | Div n => @wdiv n
    | Rem n => @wmod n
    | Sll n m => (fun x y => wslu x (ZToWord _ (wordVal _ y)))
    | Srl n m => (fun x y => wsru x (ZToWord _ (wordVal _ y)))
    | Sra n m => wsra
    | Concat n1 n2 => wconcat
  end.

Definition evalCABit n (op: CABitOp) (ls: list (word n)): word n :=
  match op with
    | Add => fold_left (@wadd n) ls (ZToWord n 0)
    | Mul => fold_left (@wmul n) ls (ZToWord n 1)
    | Band => fold_left (@wand n) ls  (ZToWord n ((2 ^ (Z.of_nat n)) - 1))
    (* | Bor => fold_left (@wor n) ls (ZToWord n 0) *)
    | Bxor => fold_left (@wxor n) ls (ZToWord n 0)
  end.

Definition evalBinBitBool n1 n2 (op: BinBitBoolOp n1 n2)
  : word n1 -> word n2 -> bool :=
  match op with
    | LessThan n => fun a b => @wltu n a b
  end.

Definition evalConstFullT k (e: ConstFullT k) :=
  match e in ConstFullT k return fullType type k with
    | SyntaxConst k' c' => evalConstT c'
    | NativeConst t c' => c'
  end.

Fixpoint evalKorOpBin (k : Kind) : type k -> type k -> type k :=
  match k in Kind return (type k -> type k -> type k) with
  | Bool => orb
  | Bit n => @wor n
  | Array n k' => fun a1 a2 => (fun i => (evalKorOpBin k' (a1 i) (a2 i)))
  | Struct n fv _ => fun (s1 s2 : forall i, type (fv i)) =>
                     (fun i => (evalKorOpBin (fv i) (s1 i) (s2 i)))
  end.

Definition evalKorOp (k : Kind) : list (type k) -> type k -> type k :=
  fold_left (evalKorOpBin k).

(* maps register names to the values which they currently hold *)
Notation RegT := (Attribute (sigT (fullType type))).
Definition RegsT := (list RegT).

(* a pair of the value sent to a method call and the value it returned *)
Definition SignT k := (type (fst k) * type (snd k))%type.

(* a list of simulatenous method call actions made during a single step *)
Notation MethT := (Attribute (sigT SignT)).
Definition MethsT := (list MethT).

Section Semantics.
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
      | ReadArray n m k fv i =>
        match lt_dec (Z.to_nat (wordVal _ (@evalExpr _ i))) n with
        | left pf => fun fv => fv (of_nat_lt pf)
        | right _ => fun _ => evalConstT (getDefaultConst k)
        end (@evalExpr _ fv)
      | ReadArrayConst n k fv i =>
        (@evalExpr _ fv) i
      | BuildArray n k fv => fun i => @evalExpr _ (fv i)
      | Kor k e => evalKorOp k (map (@evalExpr _) e) (evalConstT (getDefaultConst k))
      | ToNative _ e => evalExpr e
      | FromNative _ e => evalExpr e
    end.
  Arguments evalExpr : simpl nomatch.
      
  Fixpoint evalLetExpr k (e: LetExprSyntax type k) :=
    match e in LetExprSyntax _ _ return type k with
    | NormExpr e' => evalExpr e'
    | SysE ls cont => evalLetExpr cont
    | LetE _ e' cont => evalLetExpr (cont (evalLetExpr e'))
    | IfElseE pred _ t f cont => evalLetExpr (cont (if evalExpr pred
                                                    then evalLetExpr t
                                                    else evalLetExpr f))
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
  | SemSys
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

Section MethT_dec.
  (*
  Asserts that, if the values passed to, and
  returned by, a method are equal, the Gallina
  values passed to, and returned by, a method
  are also equal.
   *)
  Lemma method_values_eq
  :  forall (s : Signature) (x y : SignT s), existT SignT s x = existT SignT s y -> x = y.
  Proof.
    intros. inv H.
    apply (Eqdep_dec.inj_pair2_eq_dec Signature Signature_dec SignT) in H1. auto.
  Qed.

  (*
  Asserts that the values passed to and returned
  by two method calls differ if their signatures
  differ.
   *)
  Lemma method_values_neq 
    :  forall (s r : Signature) (x : SignT s) (y : SignT r), s <> r -> existT SignT s x <> existT SignT r y.
  Proof.
    intros.
    unfold not. intros.
    inv H0. 
    apply H; reflexivity.
  Qed.
    
  (*Proof (fun s r x y H H0 => H (projT1_eq H0)).*)

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
  
End MethT_dec.
  
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

Definition getListFullLabel_diff (f : MethT) (l : list FullLabel) :=
  ((getNumExecs f l) - (getNumCalls f l))%Z.

Definition MatchingExecCalls_Base (l : list FullLabel) m :=
  forall f,
    In (fst f, projT1 (snd f)) (getKindAttr (getMethods m)) ->
    (getNumCalls f l <= getNumExecs f l)%Z.

Definition MatchingExecCalls_Concat (lcall lexec : list FullLabel) mexec :=
  forall f,
    (getNumCalls f lcall <> 0%Z) ->
    In (fst f, projT1 (snd f)) (getKindAttr (getAllMethods mexec)) ->
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
End BaseModule.

Inductive Step: Mod -> RegsT -> list FullLabel -> Prop :=
| BaseStep m o l (HSubsteps: Substeps m o l) (HMatching: MatchingExecCalls_Base l  m):
    Step (Base m) o l
| HideMethStep m s o l (HStep: Step m o l)
               (HHidden : forall v, In (s, projT1 v) (getKindAttr (getAllMethods m)) -> getListFullLabel_diff (s, v) l = 0%Z):
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

Definition UpdRegs (u: list RegsT) (o o': RegsT)
  := getKindAttr o = getKindAttr o' /\
     (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                   ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

Notation regInit := (fun (o': RegT) (r: RegInitT)  => fst o' = fst r /\
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
  | x :: xs => if String.eqb s (fst x)
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
End Trace.

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

Definition TraceEquiv m1 m2 := TraceInclusion m1 m2 /\ TraceInclusion m2 m1.















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
  | Sys ls cont => getCallsWithSign cont
  | IfElse pred ktf t f cont =>
    getCallsWithSign t ++ getCallsWithSign f ++ getCallsWithSign (cont tt)
  end.

Definition getCallsWithSignPerRule (rule: Attribute (Action Void)) :=
  getCallsWithSign (snd rule _).

Definition getCallsWithSignPerMeth (meth: DefMethT) :=
  getCallsWithSign (projT2 (snd meth) _ tt).

Fixpoint getCallsWithSignPerMod (mm: Mod) :=
  match mm with
  | Base m => concat (map getCallsWithSignPerRule (getRules m))++ concat (map getCallsWithSignPerMeth (getMethods m))
  | HideMeth m _ => getCallsWithSignPerMod m
  | ConcatMod m1 m2 => getCallsWithSignPerMod m1 ++ getCallsWithSignPerMod m2
  end.

Definition getCallsPerMod (m: Mod) := map fst (getCallsWithSignPerMod m).

Fixpoint getRegWrites k (a: ActionT (fun _ => unit) k) :=
  match a in ActionT _ _ with
  | MCall meth k argExpr cont =>
    getRegWrites (cont tt)
  | Return x => nil
  | LetExpr k' expr cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * FullKind) with
    | SyntaxKind k => fun cont => getRegWrites (cont tt)
    | _ => fun _ => nil
    end cont
  | LetAction k' a' cont =>
    getRegWrites a' ++ getRegWrites (cont tt)
  | ReadNondet k' cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * FullKind) with
    | SyntaxKind k => fun cont =>
                        getRegWrites (cont tt)
    | _ => fun _ => nil
    end cont
  | ReadReg r k' cont =>
    match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) ->
                    list (string * FullKind) with
    | SyntaxKind k => fun cont =>
                        getRegWrites (cont tt)
    | _ => fun _ => nil
    end cont
  | WriteReg r k' expr cont =>
    (r, k') :: getRegWrites cont
  | Sys ls cont => getRegWrites cont
  | IfElse pred ktf t f cont =>
    getRegWrites t ++ getRegWrites f ++ getRegWrites (cont tt)
  end.






(* Utility functions *)

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

Definition autoHide (m: Mod) := createHideMod m (filter (fun i => existsb (String.eqb i) (getCallsPerMod m))
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

  Fixpoint inlineSingle k (a: ActionT ty k) (f: DefMethT): ActionT ty k :=
    match a with
    | MCall g sign arg cont =>
      match String.eqb (fst f) g with
      | true =>
        match Signature_dec sign (projT1 (snd f)) with
        | left isEq =>
          LetAction (LetExpr match isEq in _ = Y return Expr ty (SyntaxKind (fst Y)) with
                             | eq_refl => arg
                             end (projT2 (snd f) ty))
                    (fun ret => inlineSingle (match isEq in _ = Y return ty (snd Y) -> ActionT ty k with
                                              | eq_refl => cont
                                              end ret) f)
        | right _ => MCall g sign arg (fun ret => inlineSingle (cont ret) f)
        end
      | false => MCall g sign arg (fun ret => inlineSingle (cont ret) f)
      end
    | LetExpr _ e cont =>
      LetExpr e (fun ret => inlineSingle (cont ret) f)
    | LetAction _ a cont =>
      LetAction (inlineSingle a f) (fun ret => inlineSingle (cont ret) f)
    | ReadNondet k c =>
      ReadNondet k (fun ret => inlineSingle (c ret) f)
    | ReadReg r k c =>
      ReadReg r k (fun ret => inlineSingle (c ret) f)
    | WriteReg r k e a =>
      WriteReg r e (inlineSingle a f)
    | IfElse p _ aT aF c =>
      IfElse p (inlineSingle aT f) (inlineSingle aF f) (fun ret => inlineSingle (c ret) f)
    | Sys ls c =>
      Sys ls (inlineSingle c f)
    | Return e =>
      Return e
    end.

End inlineSingle.

Definition inlineSingle_Rule  (f : DefMethT) (rle : RuleT): RuleT :=
  let (s, a) := rle in
  (s, fun ty => inlineSingle (a ty) f).

Definition inlineSingle_Rule_map_BaseModule (f : DefMethT) (m : BaseModule) :=
  BaseMod (getRegisters m) (map (inlineSingle_Rule f) (getRules m)) (getMethods m).

Fixpoint inlineSingle_Rule_in_list (f : DefMethT) (rn : string) (lr : list RuleT) : list RuleT :=
  match lr with
  | rle'::lr' => match String.eqb rn (fst rle') with
                 | false => rle'
                 | true => inlineSingle_Rule f rle'
                 end ::(inlineSingle_Rule_in_list f rn lr')
  | nil => nil
  end.

Definition inlineSingle_Rule_BaseModule (f : DefMethT) (rn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (inlineSingle_Rule_in_list f rn (getRules m)) (getMethods m).

Definition inlineSingle_Meth (f : DefMethT) (meth : DefMethT): DefMethT :=
  let (name, sig_body) := meth in
  (name,
   if String.eqb (fst f) name
   then sig_body
   else
     let (sig, body) := sig_body in
     existT _ sig (fun ty arg => inlineSingle (body ty arg) f)).

Definition inlineSingle_Meth_map_BaseModule (f : DefMethT) (m : BaseModule) :=
  BaseMod (getRegisters m) (getRules m) (map (inlineSingle_Meth f) (getMethods m)).

Fixpoint inlineSingle_Meth_in_list (f : DefMethT) (gn : string) (lm : list DefMethT) : list DefMethT :=
  match lm with
  | meth'::lm' => match String.eqb gn (fst meth') with
                  | false => meth'
                  | true => (inlineSingle_Meth f meth')
                  end ::(inlineSingle_Meth_in_list f gn lm')
  | nil => nil
  end.

Definition inlineSingle_Meth_BaseModule (f : DefMethT) (fn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (getRules m) (inlineSingle_Meth_in_list f fn (getMethods m)).

Section inlineSingle_nth.
  Variable (f : DefMethT).
  Variable (regs: list RegInitT) (rules: list RuleT) (meths: list DefMethT).

  Definition inlineSingle_BaseModule : BaseModule :=
    BaseMod regs (map (inlineSingle_Rule f) rules) (map (inlineSingle_Meth f) meths).

  Definition inlineSingle_BaseModule_nth_Meth xs : BaseModule :=
    BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs).

  Definition inlineSingle_BaseModule_nth_Rule xs : BaseModule :=
    BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths.
End inlineSingle_nth.

Definition inlineSingle_Rules_pos meths n rules :=
  match nth_error meths n with
  | Some f => map (inlineSingle_Rule f) rules
  | None => rules
  end.

Definition inlineAll_Rules meths rules := fold_left (fun newRules n => inlineSingle_Rules_pos meths n newRules) (seq 0 (length meths)) rules.

Definition inlineAll_Rules_mod m :=
  (BaseMod (getRegisters m) (inlineAll_Rules (getMethods m) (getRules m)) (getMethods m)).

Definition inlineSingle_Meths_pos newMeths n :=
  match nth_error newMeths n with
  | Some f => map (inlineSingle_Meth f) newMeths
  | None => newMeths
  end.

Definition inlineAll_Meths meths := fold_left inlineSingle_Meths_pos (seq 0 (length meths)) meths.

Definition inlineAll_Meths_mod m :=
  (BaseMod (getRegisters m) (getRules m) (inlineAll_Meths (getMethods m))).

Definition inlineAll_All regs rules meths :=
  (BaseMod regs (inlineAll_Rules (inlineAll_Meths meths) rules) (inlineAll_Meths meths)).

Definition inlineAll_All_mod m :=
  inlineAll_All (getAllRegisters m) (getAllRules m) (getAllMethods m).

Definition flatten_inline_everything m :=
  createHide (inlineAll_All_mod m) (getHidden m).

Definition removeHides (m: BaseModule) s :=
  BaseMod (getRegisters m) (getRules m)
          (filter (fun df => negb (existsb (String.eqb (fst df)) s)) (getMethods m)).

Definition flatten_inline_remove m :=
  removeHides (inlineAll_All_mod m) (getHidden m).

(* Last Set of Utility Functions *)

Definition hiddenBy (meths : list DefMethT) (h : string) : bool :=
  (existsb (String.eqb h) (map fst meths)).

Definition getAllBaseMethods (lb : list BaseModule) : (list DefMethT) :=
  (concat (map getMethods lb)).

Definition hiddenByBase (lb : list BaseModule) (h : string) : bool :=
  (hiddenBy (getAllBaseMethods lb) h).

Local Notation complement f := (fun x => negb (f x)).

Definition separateHides (tl : list string * (list RegFileBase * list BaseModule)) :
  (list string * list string) :=
  (filter (hiddenByBase (map BaseRegFile (fst (snd tl)))) (fst tl),
   filter (complement (hiddenByBase (map BaseRegFile (fst (snd tl))))) (fst tl)).

Definition separateModHides (m: Mod) :=
  let '(hides, (rfs, mods)) := separateMod m in
  let '(hidesRf, hidesBm) := separateHides (hides, (rfs, mods)) in
  (hidesRf, (rfs, createHide (inlineAll_All_mod (mergeSeparatedBaseMod mods)) hidesBm)).

Definition separateModRemove (m : Mod) :=
  let '(hides, (rfs, mods)) := separateMod m in
  let '(hidesRf, hidesBm) := separateHides (hides, (rfs, mods)) in
  (hidesRf, (rfs, removeHides (inlineAll_All_mod (mergeSeparatedBaseMod mods)) hidesBm)).

Definition baseNoSelfCalls (m : Mod) :=
  let '(hides, (rfs, mods)) := separateMod m in
  NoSelfCallBaseModule (inlineAll_All_mod (mergeSeparatedBaseMod mods)).

Definition separateModHidesNoInline (m : Mod) :=
  let '(hides, (rfs, mods)) := separateMod m in
  (hides, (rfs, getFlat (mergeSeparatedBaseMod mods))).

(* Helper functions for struct - Gallina versions of getters and setters *)

Local Definition option_bind
  (T U : Type)
  (x : option T)
  (f : T -> option U)
  :  option U
  := match x with
       | Some y => f y
       | None => None
     end.

Local Notation "X >>- F" := (option_bind X F) (at level 85, only parsing).

Fixpoint struct_get_field_index'
         (name: string) {n}
  := match n return
         forall (get_name : Fin n -> string),
                option (Fin n)
     with
     | 0 => fun _ => None
     | S m => fun get_name =>
       if String.eqb (get_name F1) name
       then Some F1
       else match struct_get_field_index' name (fun i => get_name (FS i)) with
            | Some i => Some (FS i)
            | None => None
            end
     end.

Definition struct_get_field_index n (kinds: Fin n -> Kind) (names: Fin n -> string) ty (e: Expr ty (SyntaxKind (Struct kinds names))) name
  := struct_get_field_index' name names.

Local Definition struct_get_field_aux
  (ty: Kind -> Type)
  (n : nat)
  (get_kind : Fin n -> Kind)
  (get_name : Fin n -> string)
  (packet : Expr ty (SyntaxKind (Struct get_kind get_name)))
  (name : string)
  :  option ({kind : Kind & Expr ty (SyntaxKind kind)})
  := struct_get_field_index packet name >>-
       fun index
         => Some
              (existT
                (fun kind : Kind => Expr ty (SyntaxKind kind))
                (get_kind index)
                (ReadStruct packet index)).

Definition struct_get_field
  (ty: Kind -> Type)
  (n : nat)
  (get_value : Fin n -> Kind)
  (get_name : Fin n -> string)
  (packet : Expr ty (SyntaxKind (Struct get_value get_name)))
  (name : string)
  (k : Kind)
  :  option (Expr ty (SyntaxKind k)).
Proof.
refine (let y := @struct_get_field_aux ty n get_value get_name packet name in
        match y with
        | None => None
        | Some (existT x y) => _
        end).
destruct (Kind_decb x k) eqn:G.
- apply Kind_decb_eq in G.
  subst.
  exact (Some y).
- exact None.
Defined.

Definition struct_get_field_default
  (ty: Kind -> Type)
  (n : nat)
  (get_value : Fin n -> Kind)
  (get_name : Fin n -> string)
  (packet : Expr ty (SyntaxKind (Struct get_value get_name)))
  (name : string)
  (kind : Kind)
  (default : Expr ty (SyntaxKind kind))
  :  Expr ty (SyntaxKind kind)
  := match struct_get_field packet name kind with
       | Some field_value => field_value
       | None => default
     end.

Definition struct_set_field
  (ty: Kind -> Type)
  (n : nat)
  (get_kind : Fin n -> Kind)
  (get_name : Fin n -> string)
  (packet : Expr ty (SyntaxKind (Struct get_kind get_name)))
  (name : string)
  (kind : Kind)
  (value : Expr ty (SyntaxKind kind))
  :  option (Expr ty (SyntaxKind (Struct get_kind get_name))).
Proof.
  refine (let y := struct_get_field_index packet name in
          match y with
          | None => None
          | Some i => _
          end).
  destruct (Kind_dec (get_kind i) kind).
  - subst.
    exact (Some (UpdateStruct packet i value)).
  - exact None.
Defined.

Definition struct_set_field_default
           (ty: Kind -> Type)
           (n : nat)
           (get_kind : Fin n -> Kind)
           (get_name : Fin n -> string)
           (packet : Expr ty (SyntaxKind (Struct get_kind get_name)))
           (name : string)
           (kind : Kind)
           (value : Expr ty (SyntaxKind kind))
  : Expr ty (SyntaxKind (Struct get_kind get_name)).
Proof.
  refine (let y := struct_get_field_index packet name in
          match y with
          | None => packet
          | Some i => _
          end).
  destruct (Kind_dec (get_kind i) kind).
  - subst.
    exact (UpdateStruct packet i value).
  - exact packet.
Defined.

Create HintDb KamiDb.
Hint Unfold 
     inlineSingle_Meths_pos
     flatten_inline_remove 
     getHidden
     getAllRegisters
     getAllMethods
     getAllRules
     inlineAll_All_mod
     inlineAll_All
     writeRegFileFn
     readRegFile
     createHideMod
     List.find
     List.fold_right
     List.fold_left
     List.filter
     List.length
     List.app
     List.seq
     List.nth_error
     List.map
     List.concat
     List.existsb
     List.nth
     Datatypes.length
     Ascii.eqb
     String.eqb
     Bool.eqb
     Datatypes.negb
     Datatypes.andb
     Datatypes.orb
     Datatypes.fst
     Datatypes.snd
     String.append
  : KamiDb.
(* TODO
   + PUAR: Linux/Certikos
 *)

