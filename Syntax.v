Require Export Bool Ascii String List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word Lib.VectorFacts Lib.EclecticLib.

Export Word.Notations.
Export ListNotations.

Require Import Permutation RecordUpdate.RecordSet.
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
| Struct  : forall n, (Fin.t n -> Kind) -> (Fin.t n -> string) -> Kind
| Array   : nat -> Kind -> Kind.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type) (c : t) : FullKind.

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstStruct n fk fs (fv: forall i, ConstT (fk i)): ConstT (@Struct n fk fs)
| ConstArray n k (fk: Fin.t n -> ConstT k): ConstT (Array n k).

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

Fixpoint getDefaultConstFullKind (k : FullKind) : ConstFullT k :=
  match k with
  | SyntaxKind k' => SyntaxConst (getDefaultConst k')
  | NativeKind t c' => NativeConst c'
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
    BuildStruct fk fs (fun i' => match Fin_eq_dec i i' with
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

    Lemma helper_sumSizes n (i: Fin.t n):
      forall (sizes: Fin.t n -> nat), sumSizes sizes = (sumSizes sizes - (sumSizesMsbs i sizes + sizes i)) + sizes i + sumSizesMsbs i sizes.
    Proof.
      induction i; simpl; intros; auto.
      - lia.
      - specialize (IHi (fun x => sizes (Fin.FS x))).
        lia.
    Qed.
    
    Lemma helper_array n (i: Fin.t n):
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

  Inductive FullFormat: Kind -> Type :=
  | FBool: nat -> BitFormat -> FullFormat Bool
  | FBit n: nat -> BitFormat -> FullFormat (Bit n)
  | FStruct n fk fs: (forall i, FullFormat (fk i)) -> FullFormat (@Struct n fk fs)
  | FArray n k: FullFormat k -> FullFormat (@Array n k).

  Fixpoint fullFormatHex k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Hex
    | Bit n => FBit n (n/4) Hex
    | Struct n fk fs => FStruct fk fs (fun i => fullFormatHex (fk i))
    | Array n k => FArray n (fullFormatHex k)
    end.

  Fixpoint fullFormatBinary k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Binary
    | Bit n => FBit n n Binary
    | Struct n fk fs => FStruct fk fs (fun i => fullFormatBinary (fk i))
    | Array n k => FArray n (fullFormatBinary k)
    end.

  Fixpoint fullFormatDecimal k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Decimal
    | Bit n => FBit n 0 Decimal
    | Struct n fk fs => FStruct fk fs (fun i => fullFormatDecimal (fk i))
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
| RFFile (isAscii: bool) (isArg: bool) (file: string) (offset size: nat) (init: Fin.t IdxNum -> ConstT Data).

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
                               | Async _ => nil
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

(** Notations for Struct **)

Delimit Scope kami_expr_scope with kami_expr.

Notation "name :: ty" := (name%string,  ty) (only parsing) : kami_struct_scope.
Delimit Scope kami_struct_scope with kami_struct.

Definition getStruct ls :=
  (Struct (fun i => snd (nth_Fin ls i)) (fun j => fst (nth_Fin ls j))).

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
             Return (BuildArray (fun i: Fin.t num =>
                                   ReadArray
                                     (Var ty _ val)
                                     (CABit Add (Var ty (SyntaxKind _) idx ::
                                                     Const ty (natToWord _ (proj1_sig (Fin.to_nat i))) :: nil))))).
                                                                                                                   
Definition updateNumDataArray num dataArray IdxNum Data ty (idxData: ty (WriteRq (Nat.log2_up IdxNum)
                                                                                 (Array num Data))):
  ActionT ty Void :=
  ReadReg dataArray (SyntaxKind (Array IdxNum Data))
          (fun val =>
             WriteReg dataArray
                      (fold_left (fun newArr i =>
                                    (UpdateArray newArr
                                                 (CABit Add (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                        Fin.F1 ::
                                                                        Const ty (natToWord _ (proj1_sig (Fin.to_nat i))) ::
                                                                        nil))
                                                 (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                             (Fin.FS Fin.F1)) i))) (getFins num)
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
                                      (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData) (Fin.FS (Fin.FS Fin.F1))) i)
                                      (UpdateArray newArr
                                                   (CABit Add (ReadStruct
                                                                 (Var ty (SyntaxKind _) idxData)
                                                                 Fin.F1 :: Const ty (natToWord _ (proj1_sig (Fin.to_nat i))) ::
                                                                 nil))
                                                   (ReadArrayConst (ReadStruct (Var ty (SyntaxKind _) idxData)
                                                                               (Fin.FS Fin.F1)) i))
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
  | WfReadReg r k lretT c: (forall v, WfActionT (c v)) -> In (r, k) (getKindAttr (getRegisters m)) ->
                           @WfActionT lretT (ReadReg r k c)
  | WfWriteReg r k (e: Expr type k) lretT c: WfActionT c  -> In (r, k) (getKindAttr (getRegisters m)) ->
                                             @WfActionT lretT (WriteReg r e c)
  | WfIfElse p k (atrue: ActionT type k) afalse lretT c: (forall v, WfActionT (c v)) -> WfActionT atrue ->
                                                         WfActionT afalse -> @WfActionT lretT (IfElse p atrue afalse c)
  | WfSys ls lretT c: WfActionT c -> @WfActionT lretT (Sys ls c)
  | WfReturn lretT e: @WfActionT lretT (Return e).

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

 (* Lemma WfActionTEquiv lret a: @WfActionT' lret a -> WfActionT a.
   Proof.
     induction a; intros.
     -
       inv H0; EqDep_subst.
       econstructor; intros.
       intros. *)

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
| WfConcatMCall meth s e lretT c m' :(forall v, WfConcatActionT (c v) m') -> ~In meth (getHidden m') ->
                                     @WfConcatActionT lretT (MCall meth s e c) m'
| WfConcatLetExpr k (e : Expr type k) lretT c m' : (forall v, WfConcatActionT (c v) m') ->
                                                   @WfConcatActionT lretT (LetExpr e c) m'
| WfConcatLetAction k (a : ActionT type k) lretT c m' : WfConcatActionT a m' -> (forall v, WfConcatActionT (c v) m') ->
                                                        @WfConcatActionT lretT (LetAction a c) m'
| WfConcatReadNondet k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (ReadNondet k c) m'
| WfConcatReadReg r k lretT c m': (forall v, WfConcatActionT (c v) m') -> @WfConcatActionT lretT (ReadReg r k c) m'
| WfConcatWriteReg r k (e: Expr type k) lretT c m': WfConcatActionT c m' -> @WfConcatActionT lretT (WriteReg r e c) m'
| WfConcatIfElse p k (atrue: ActionT type k) afalse lretT c m': (forall v, WfConcatActionT (c v) m') ->
                                                                WfConcatActionT atrue m' -> WfConcatActionT afalse m' ->
                                                                @WfConcatActionT lretT (IfElse p atrue afalse c) m'
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

Local Ltac Struct_neq :=
  match goal with
  | |- Struct _ _ <> Struct _ _ =>
    let H := fresh in intro H;
                      injection H;
                      intros;
                      repeat (existT_destruct Nat.eq_dec)
  end.

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

Definition Signature_dec (s1 s2: Signature): {s1 = s2} + {s1 <> s2}.
  refine match s1, s2 with
         | (k11, k12), (k21, k22) => match Kind_dec k11 k21, Kind_dec k12 k22 with
                                     | left pf1, left pf2 => left _
                                     | left pf1, right pf2 => right (fun x => pf2 _)
                                     | right pf1, left pf2 => right (fun x => pf1 _)
                                     | right pf1, right pf2 => right (fun x => pf1 _)
                                     end
         end.
  - subst; auto.
  - exact (f_equal snd x).
  - exact (f_equal fst x).
  - exact (f_equal fst x).
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

Definition wneg_simple sz (x: word sz) := wnot x ^+ $1.

Definition wminus_simple sz (x y: word sz) := x ^+ (wneg_simple y).

Lemma wneg_simple_wneg sz: forall (x: word sz), wneg_simple x = wneg x.
Proof.
  unfold wneg_simple.
  intros.
  rewrite wneg_wnot.
  rewrite wminus_wplus_undo.
  reflexivity.
Qed.

Lemma wminus_simple_wminus sz: forall (x y: word sz), wminus_simple x y = wminus x y.
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
    | Sub n => @wminus_simple n
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
        match lt_dec (wordToNat (@evalExpr _ i)) n with
        | left pf => fun fv => fv (Fin.of_nat_lt pf)
        | right _ => fun _ => evalConstT (getDefaultConst k)
        end (@evalExpr _ fv)
      | ReadArrayConst n k fv i =>
        (@evalExpr _ fv) i
      | BuildArray n k fv => fun i => @evalExpr _ (fv i)
    end.
  
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
    intros. inv H. apply (Eqdep_dec.inj_pair2_eq_dec Signature Signature_dec SignT) in H1. auto.
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

Definition getCallsWithSignPerMod (m: Mod) :=
  concat (map getCallsWithSignPerRule (getAllRules m)) ++ concat (map getCallsWithSignPerMeth (getAllMethods m)).

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
    | Sys ls c =>
      Sys ls (inlineSingle c)
    | Return e =>
      Return e
    end.

End inlineSingle.

Definition inlineSingle_Rule  (f : DefMethT) (rle : RuleT): RuleT :=
  let (s, a) := rle in
  (s, fun ty => inlineSingle f (a ty)).

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

Definition inlineSingle_Rule_BaseModule (f : DefMethT) (rn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (inlineSingle_Rule_in_list f rn (getRules m)) (getMethods m).

Definition inlineSingle_Meth (f : DefMethT) (meth : DefMethT): DefMethT :=
  let (name, sig_body) := meth in
  (name,
   if string_dec (fst f) name
   then sig_body
   else
     let (sig, body) := sig_body in
     existT _ sig (fun ty arg => inlineSingle f (body ty arg))).

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
          (filter (fun df => negb (getBool (in_dec string_dec (fst df) s))) (getMethods m)).

Definition flatten_inline_remove m :=
  removeHides (inlineAll_All_mod m) (getHidden m).
  


(* Last Set of Utility Functions *)

Definition hiddenBy (meths : list DefMethT) (h : string) : bool :=
  (getBool (in_dec string_dec h (map fst meths))).

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














(** Notations for expressions *)

Notation "k @# ty" := (Expr ty (SyntaxKind k)) (no associativity, at level 98, only parsing).

Notation Default := (getDefaultConst _).

Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (only parsing) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)): kami_expr_scope.
Notation "$$ e" := (Const ltac:(assumption) e) (at level 8, only parsing) : kami_expr_scope.

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

Notation "a $#[ i : j ]":=
  ltac:(let aTy := type of a in
        match aTy with
        | Expr _ (SyntaxKind ?bv) =>
          let bvSimpl := eval compute in bv in
              match bvSimpl with
              | Bit ?w =>
                let middle := eval simpl in (i + 1 - j)%nat in
                    let top := eval simpl in (w - 1 - i)%nat in
                exact (ConstExtract j middle top (@castBits _ w (j + middle + top) ltac:(abstract (lia || nia)) a))
              end
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

Definition struct_get_field_index
  (ty: Kind -> Type)
  (n : nat)
  (get_kind : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_kind get_name @# ty)
  (name : string)
  :  option (Fin.t (S n))
  := nat_rect
       (fun m : nat => m < (S n) -> option (Fin.t (S n)))
       (fun H : 0 < (S n)
         => let index : Fin.t (S n)
              := Fin.of_nat_lt H in
            if (string_dec name (get_name index))
              then Some index
              else None)
       (fun (m : nat)
         (F : m < (S n) -> option (Fin.t (S n)))
         (H : S m < (S n))
         => let H0
              :  m < (S n)
              := PeanoNat.Nat.lt_lt_succ_r m n
                   (Lt.lt_S_n m n H) in
            let index
              :  Fin.t (S n)
              := Fin.of_nat_lt H in
            if (string_dec name (get_name index))
              then Some index
              else F H0)
       n
       (PeanoNat.Nat.lt_succ_diag_r n).

Local Ltac struct_get_field_ltac packet name :=
  let val := eval cbv in (struct_get_field_index packet name) in
      match val with
      | Some ?x => exact (ReadStruct packet x)
      | None =>
        let newstr := constr:(("get field not found in struct" ++ name)%string) in
        fail 0 newstr
      | _ =>
        let newstr := constr:(("major error - struct_get_field_index not reducing " ++ name)%string) in
        fail 0 newstr
      end.

Local Ltac struct_set_field_ltac packet name newval :=
  let val := eval cbv in (struct_get_field_index packet name) in
      match val with
      | Some ?x => exact (UpdateStruct packet x newval)
      | None =>
        let newstr := constr:(("set field not found in struct " ++ name)%string) in
        fail 0 newstr
      | _ =>
        let newstr := constr:(("major error - struct_set_field_index not reducing " ++ name)%string) in
        fail 0 newstr
      end.

Notation "s @% f" := ltac:(struct_get_field_ltac s%kami_expr f%string)
  (at level 38, only parsing): kami_expr_scope.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (snd a)))
          (name%string, _) value) (at level 50) : kami_struct_init_scope.
Delimit Scope kami_struct_init_scope with struct_init.

Notation getStructVal ls :=
  (BuildStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => Expr _ (SyntaxKind (snd x)))
                                      ls k (projT2 (nth_Fin ls (Fin.cast k (map_length_red (@projT1 _ _) ls)))))).

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStructVal (cons s1%struct_init ..
                      (cons sN%struct_init nil) ..))
  : kami_expr_scope.

Notation "name ::= value" :=
  (name, value) (only parsing): kami_switch_init_scope.
Delimit Scope kami_switch_init_scope with switch_init.

Notation "s '@%[' f <- v ]" := ltac:(struct_set_field_ltac s f v)
  (at level 38, only parsing): kami_expr_scope.

Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) : kami_expr_scope.

Notation "nkind <[ def ]>" := (@NativeKind nkind def) (at level 100): kami_expr_scope.

(* One hot switches *)
Notation "'Switch' val 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons (IF val == fst s1%switch_init then pack (snd s1%switch_init) else $0)%kami_expr ..
                                (cons (IF val == fst sN%switch_init then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

Notation "'Switch' val 'Of' inK 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons (IF val == ((fst s1%switch_init): inK @# _) then pack (snd s1%switch_init) else $0)%kami_expr ..
                                (cons (IF val == ((fst sN%switch_init): inK @# _) then pack (snd sN%switch_init)else $0)%kami_expr nil) ..))):
    kami_expr_scope.

(* Notations for Let Expressions *)
Notation "'LETE' name <- expr ; cont " :=
  (LetE expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'LETE' name : t <- expr ; cont " :=
  (LetE (k' := t) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'RetE' expr" :=
  (NormExpr expr%kami_expr) (at level 13) : kami_expr_scope.
Notation "'LETC' name <- v ; c " :=
  (LETE name <- RetE v ; c)%kami_expr
                           (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'LETC' name : t <- v ; c " :=
  (LETE name : t <- RetE v ; c)%kami_expr
                               (at level 13, right associativity, name at level 99) : kami_expr_scope.
Notation "'SystemE' ls ; c " :=
  (SysE ls c)%kami_expr (at level 13, right associativity, ls at level 99): kami_expr_scope.
Notation "'IfE' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElseE cexpr%kami_expr tact fact (fun name => cont))
    (at level 14, right associativity) : kami_expr_scope.
Notation "'IfE' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElseE cexpr%kami_expr tact fact (fun _ => cont))
    (at level 14, right associativity) : kami_expr_scope.
Notation "'IfE' cexpr 'then' tact ; cont" :=
  (IfElseE cexpr%kami_expr tact (RetE (Const _ Default))%kami_expr (fun _ => cont))
    (at level 14, right associativity) : kami_expr_scope.



Notation "k ## ty" := (LetExprSyntax ty k) (no associativity, at level 98, only parsing).

(** Notations for action *)

Notation "'Call' meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, Void) a%kami_expr (fun _ => cont))
    (at level 13, right associativity, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' name : retT <- meth ( a : argT ) ; cont " :=
  (MCall meth%string (argT, retT) a%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 0, meth at level 0, a at level 99) : kami_action_scope.
Notation "'Call' meth () ; cont " :=
  (MCall meth%string (Void, Void) (Const _ Default) (fun _ => cont))
    (at level 13, right associativity, meth at level 0) : kami_action_scope.
Notation "'Call' name : retT <- meth () ; cont " :=
  (MCall meth%string (Void, retT) (Const _ Default) (fun name => cont))
    (at level 13, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'LETN' name : fullkind <- expr ; cont " :=
  (LetExpr (k := fullkind) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name <- expr ; cont " :=
  (LetExpr expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (LetExpr (k := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name <- act ; cont " :=
  (LetAction act (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'LETA' name : t <- act ; cont " :=
  (LetAction (k := t) act (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'NondetN' name : fullkind ; cont" :=
  (ReadNondet fullkind (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Nondet' name : kind ; cont" :=
  (ReadNondet (SyntaxKind kind) (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'ReadN' name : fullkind <- reg ; cont " :=
  (ReadReg reg fullkind (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg reg _ (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg reg (SyntaxKind kind) (fun name => cont))
    (at level 13, right associativity, name at level 99) : kami_action_scope.
Notation "'WriteN' reg : fullkind <- expr ; cont " :=
  (@WriteReg _ _ reg fullkind expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg reg expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@WriteReg _ _ reg (SyntaxKind kind) expr%kami_expr cont)
    (at level 13, right associativity, reg at level 99) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'If' cexpr 'then' tact ; cont" :=
  (IfElse cexpr%kami_expr tact (Return (Const _ Default)) (fun _ => cont))
    (at level 14, right associativity) : kami_action_scope.
Notation "'System' sysexpr ; cont " :=
  (Sys sysexpr%kami_expr cont)
    (at level 13, right associativity) : kami_action_scope.
Notation "'Ret' expr" :=
  (Return expr%kami_expr)%kami_expr (at level 13) : kami_action_scope.
Notation "'Retv'" := (Return (Const _ (k := Void) Default)) : kami_action_scope.

Delimit Scope kami_action_scope with kami_action.

(* Complex List Actions *)
Fixpoint gatherActions (ty: Kind -> Type) k_in (acts: list (ActionT ty k_in)) k_out
         (cont: list (k_in @# ty) -> ActionT ty k_out): ActionT ty k_out :=
  match acts with
  | nil => cont nil
  | x :: xs =>
    (LETA val <- x;
       gatherActions xs (fun vals => cont ((#val)%kami_expr :: vals)))%kami_action
  end.

Notation "'GatherActions' actionList 'as' val ; cont" :=
  (gatherActions actionList (fun val => cont))
    (at level 13, right associativity, val at level 99) : kami_action_scope.

Definition readNames (ty: Kind -> Type) k names := map (fun r => Read tmp: k <- r; Ret #tmp)%kami_action names.

Notation "'ReadToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (readNames _ k names) (fun val => cont))
    (at level 13, right associativity, val at level 99) : kami_action_scope.

Definition callNames (ty: Kind -> Type) k names := map (fun r => Call tmp : k <- r(); Ret #tmp)%kami_action names.

Notation "'CallToList' names 'of' k 'as' val ; cont" :=
  (gatherActions (callNames _ k names) (fun val => cont))
    (at level 13, right associativity, val at level 99): kami_action_scope.

Definition writeNames (ty: Kind -> Type) k namesVals :=
  map (fun r => Write (fst r) : k <- snd r; Ret (Const ty WO))%kami_action namesVals.

Notation "'WriteToList' names 'of' k 'using' vals ; cont" :=
  (gatherActions (@writeNames _ k (List.combine names vals)) (fun _ => cont))
    (at level 13, right associativity, vals at level 99) : kami_action_scope.

(* Notation for normal mods *)

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

Definition makeModule (im : InModule) :=
  let '(regs, rules, meths) := makeModule' im in
  BaseMod regs rules meths.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Delimit Scope kami_init_scope with kami_init.

Notation "'ARRAY' { x1 ; .. ; xn }" :=
  (BuildArray (nth_Fin (cons x1%kami_init .. (cons xn%kami_init nil) ..)))
  : kami_expr_scope.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => ConstT (snd a))
          (name%string, _) value) (at level 50) : kami_struct_initial_scope.
Delimit Scope kami_struct_initial_scope with struct_initial.

Notation getStructConst ls :=
  (ConstStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => ConstT (snd x))
                                      ls k (projT2 (nth_Fin ls (Fin.cast k (map_length_red (@projT1 _ _) ls)))))).

Delimit Scope kami_scope with kami.

Notation "'RegisterN' name : type <- init" :=
  (MERegister (name%string, existT RegInitValT type (Some ((NativeConst init)%kami_init)%word)))
    (at level 13, name at level 99) : kami_scope.

Notation "'Register' name : type <- init" :=
  (MERegister (name%string, existT RegInitValT (SyntaxKind type) (Some (makeConst ((init)%kami_init)%word))))
    (at level 13, name at level 99) : kami_scope.

Notation "'RegisterU' name : type" :=
  (MERegister (name%string, existT RegInitValT (SyntaxKind type) None))
    (at level 13, name at level 99) : kami_scope.

Notation "'Method' name () : retT := c" :=
  (MEMeth (name%string, existT MethodT (Void, retT)
                               (fun ty (_: ty Void) => c%kami_action : ActionT ty retT)))
    (at level 13, name at level 9) : kami_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MEMeth (name%string, existT MethodT (dom, retT)
                               (fun ty (param : ty dom) => c%kami_action : ActionT ty retT)))
    (at level 13, name at level 9, param at level 99) : kami_scope.

Notation "'Rule' name := c" :=
  (MERule (name%string, fun ty => (c)%kami_action : ActionT ty Void))
    (at level 13) : kami_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..))
    (only parsing).

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

Local Ltac constructor_simpl :=
  econstructor; eauto; simpl; unfold not; intros.

Ltac destruct_string_dec :=
  repeat match goal with
         | H: context[string_dec ?P%string ?Q%string] |- _ =>
           destruct (string_dec P Q)
         | |- context[string_dec ?P%string ?Q%string] =>
           destruct (string_dec P Q)
         end.

Local Ltac process_append :=
  repeat match goal with
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           apply append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ =>
           apply append_remove_suffix in H; subst
         | |- (?a ++ ?b)%string = (?a ++ ?c)%string =>
           apply append_remove_prefix
         | |- (?a ++ ?b)%string = (?c ++ ?b)%string =>
           apply append_remove_suffix
         end.

Local Ltac finish_append :=
  auto; try (apply InSingleton || discriminate || tauto || congruence).

Ltac discharge_append :=
  simpl; unfold getBool in *; process_append; finish_append.

Ltac discharge_DisjKey :=
  repeat match goal with
         | |- DisjKey _ _ =>
           rewrite (DisjKeyWeak_same string_dec); unfold DisjKeyWeak; simpl; intros
         | H: _ \/ _ |- _ => destruct H; subst
         end; discharge_append.

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
         end;
  discharge_DisjKey.

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






Section Positive.
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


Notation "'RegisterVec' name 'using' nums : type <- init" :=
  (MERegAry (
    map (fun idx =>
      (AddIndexToName name idx, existT RegInitValT (SyntaxKind type) (Some (makeConst (init)%kami_init)))
    ) nums
  ))
    (at level 13, name at level 9, nums at level 9) : kami_scope.



(* Gallina Record Notations *)
Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
                                    (at level 12, left associativity).
Notation "x <| proj  ::==  f |>" := (set proj f x)
                                      (at level 12, f at next level, left associativity).






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

Local Definition struct_get_field_aux
  (ty: Kind -> Type)
  (n : nat)
  (get_kind : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_kind get_name @# ty)
  (name : string)
  :  option ({kind : Kind & kind @# ty})
  := struct_get_field_index packet name >>-
       fun index
         => Some
              (existT
                (fun kind : Kind => kind @# ty)
                (get_kind index)
                (ReadStruct packet index)).

Definition struct_get_field
  (ty: Kind -> Type)
  (n : nat)
  (get_value : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_value get_name @# ty)
  (name : string)
  (kind : Kind)
  :  option (kind @# ty)
  := struct_get_field_aux packet name >>-
       sigT_rect
         (fun _ => option (kind @# ty))
         (fun field_kind field_value
           => sumbool_rect
                (fun _ => option (kind @# ty))
                (fun H : field_kind = kind
                  => Some (
                       eq_rect
                         field_kind
                         (fun k => k @# ty)
                         field_value
                         kind
                         H))
                (fun _ : field_kind <> kind
                  => None)
                (Kind_dec field_kind kind)).

Definition struct_get_field_default
  (ty: Kind -> Type)
  (n : nat)
  (get_value : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_value get_name @# ty)
  (name : string)
  (kind : Kind)
  (default : kind @# ty)
  :  kind @# ty
  := match struct_get_field packet name kind with
       | Some field_value
         => field_value
       | None
         => default
     end.

Definition struct_set_field
  (ty: Kind -> Type)
  (n : nat)
  (get_kind : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_kind get_name @# ty)
  (name : string)
  (kind : Kind)
  (value : kind @# ty)
  :  option (Struct get_kind get_name @# ty)
  := struct_get_field_index packet name >>-
       fun index
         => sumbool_rect
              (fun _ => option (Struct get_kind get_name @# ty))
              (fun H : get_kind index = kind
                => Some
                     (UpdateStruct packet index
                       (eq_rect_r (fun k => k @# ty) value H)))
             (fun _ => None)
             (Kind_dec (get_kind index) kind).





Section mod_test.
  Variable a: string.
  Local Notation "^ x" := (a ++ "." ++ x)%string (at level 0).
  Local Example test := MOD_WF{
                              Register (^"x") : Bool <- true
                                with Register (^"y") : Bool <- false
                                with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                         Write (^"x"): Bool <- #y;
                                                         Retv )
                          }.

  Local Example test1 := MODULE_WF{
                             Register (^"x") : Bool <- true
                               with Register (^"y") : Bool <- false
                               with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                        Write (^"x"): Bool <- #y;
                                                        Retv )
                           }.
End mod_test.





Local Example test_normaldisj:
  DisjKey (map (fun x => (x, 1)) ("a" :: "b" :: "c" :: nil))%string
          (map (fun x => (x, 2)) ("d" :: "e" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_prefix_disj a:
  DisjKey (map (fun x => ((a ++ x)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((a ++ x)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_suffix_disj a:
  DisjKey (map (fun x => ((x ++ a)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((x ++ a)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.










(* Testing the Notations *)

Local Example testSwitch ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Retn Bool With {
            $$ (natToWord 5 5) ::= $$ true ;
            $$ (natToWord 5 6) ::= $$ false
          })%kami_expr.

Local Example testSwitch2 ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Of Bit 5 Retn Bool With {
            $$ (natToWord 5 5) ::= $$ true ;
            $$ (natToWord 5 6) ::= $$ false
          })%kami_expr.


Local Example test2 a b := (ConcatMod (test a) (test b))%kami.

Definition extractArbitraryRange ty sz (inst: Bit sz ## ty) (range: nat * nat):
  Bit (fst range + 1 - snd range) ## ty :=
  (LETE i <- inst ;
     RetE (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range)
                        (ZeroExtendTruncLsb _ #i)))%kami_expr.
   

Section unittests.

  Open Scope kami_expr.

  Local Notation "X ==> Y" := (evalExpr X = Y) (at level 75).

  Let test_struct
    :=  STRUCT {
            "field0" ::= Const type false;
            "field1" ::= Const type (natToWord 4 2);
            "field2" ::= Const type (natToWord 5 3)}%kami_expr%struct_init.

  Section struct_get_field_default_unittests.
    Let test0
    :  test_struct @% "field0" ==> false
      := eq_refl false.

    Let test1
      : test_struct @% "field1" ==> natToWord 4 2
      := eq_refl (natToWord 4 2).
    
    Let test2
      : test_struct @% "field2" ==> natToWord 5 3
      := eq_refl (natToWord 5 3).

  End struct_get_field_default_unittests.

  Section struct_set_field_unittests.

    Let test_0
    :  (test_struct @%["field0" <- (Const type true)]) @% "field0"
                                                       ==> true
      := eq_refl true.

    Let test_1
      :  (test_struct @%["field1" <- (Const type (natToWord 4 5))]) @% "field1"
                                                                    ==> natToWord 4 5
      := eq_refl (natToWord 4 5).

    Let test_2
      :  (test_struct @%["field2" <- (Const type (natToWord 5 5))]) @% "field2"
                                                                    ==> natToWord 5 5
      := eq_refl (natToWord 5 5).
  End struct_set_field_unittests.

  Close Scope kami_expr.

End unittests.


Local Definition testConcat ty (w1: Bit 10 @# ty) (w2: Bit 2 @# ty) (w3: Bit 5 @# ty) :=
  {< w1, w2, w3 >}%kami_expr.

Local Definition testArrayAccess ty (v: Array 4 (Bit 10) @# ty) (idx : Bit 2 @# ty) := (v @[ idx <- v @[ idx ]])%kami_expr.

Local Definition testConstNat ty (w1 w2: Bit 10 @# ty): Bit 10 @# ty := (w1 + w2 + $4 + $6)%kami_expr.

Local Definition testExtract ty n n1 n2 (pf1: n > n1) (pf2: n1 > n2) (a: Bit n @# ty) := (a $#[n1 : n2])%kami_expr.
















Notation "'STRUCT_TYPE' { s1 ; .. ; sN }" :=
  (getStruct (cons s1%kami_struct .. (cons sN%kami_struct nil) ..)).

Notation "'ARRAY_CONST' { x1 ; .. ; xn }" :=
  (ConstArray (nth_Fin' (cons (x1%kami_init)%word .. (cons (xn%kami_init)%word nil) ..) eq_refl)).

Notation "'STRUCT_CONST' { s1 ; .. ; sN }" :=
  (getStructConst (cons (s1%struct_initial)%word ..
                               (cons (sN%struct_initial)%word nil) ..)).

Definition ltO{X} : forall n, n < 0 -> X.
Proof.
  refine (fun n p => match (_:False) with end); lia.
Defined.

Lemma ltSmSn_ltmn : forall {m n},
  S m < S n -> m < n.
Proof.
  intros; lia.
Qed.

Fixpoint mkFin i n : i < n -> Fin.t n :=
  match n with
  | 0 => fun p => ltO p
  | S m => match i with
           | 0 => fun _ => Fin.F1
           | S j => fun p => Fin.FS (mkFin (ltSmSn_ltmn p))
           end
  end.

Notation "i #: n" := (@mkFin (i)%nat (n)%nat ltac:(lia)) (at level 10, only parsing).

(* Useful Struct *)
Definition Maybe k :=  STRUCT_TYPE {
                           "valid" :: Bool;
                           "data"  :: k }.

Definition Pair (A B: Kind) := STRUCT_TYPE {
                                   "fst" :: A;
                                   "snd" :: B }.


Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= x })%kami_expr
    (at level 100, only parsing) : kami_expr_scope.

Definition Invalid {ty: Kind -> Type} {k} := (STRUCT { "valid" ::= $$ false ; "data" ::= $$ (getDefaultConst k) })%kami_expr.

Notation "'InvData' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= x })%kami_expr
    (at level 100, only parsing) : kami_expr_scope.


Local Definition testStruct :=
  (STRUCT_TYPE {
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



Local Open Scope kami_action.
Local Open Scope kami_expr.
Local Definition testFieldAccess (ty: Kind -> Type): ActionT ty (Bit 10) :=
  (LET val: testStruct <- testStructVal;
     Ret (#val @% "hello"))%kami_action.
Local Close Scope kami_expr.
Local Close Scope kami_action.

Local Definition testFieldUpd (ty: Kind -> Type) := 
  ((testStructVal (ty := ty)) @%[ "hello" <- Const ty (natToWord 10 23) ])%kami_expr.



(* TODO
   + Compiler verification (difficult)
   + PUAR: Linux/Certikos
 *)

