Require Export Bool Ascii String Fin List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word Kami.Lib.VectorFacts Kami.Lib.EclecticLib.

Export Word.Notations.
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
  | ReadArray n m k: Expr (SyntaxKind (Array n k)) ->
                   Expr (SyntaxKind (Bit m)) ->
                   Expr (SyntaxKind k)
  | ReadArrayConst n k: Expr (SyntaxKind (Array n k)) ->
                        Fin.t n ->
                        Expr (SyntaxKind k)
  | BuildArray n k: (Fin.t n -> Expr (SyntaxKind k)) -> Expr (SyntaxKind (Array n k)).

  Definition UpdateArray n m k (e: Expr (SyntaxKind (Array n k)))
             (i: Expr (SyntaxKind (Bit m)))
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

Definition getStruct ls :=
  (Struct (fun i => snd (nth_Fin ls i)) (fun j => fst (nth_Fin ls j))).
Arguments getStruct : simpl never.

Definition getStructVal ty ls :=
  (BuildStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => Expr ty (SyntaxKind (snd x)))
                                      ls k (projT2 (nth_Fin ls (Fin.cast k (map_length_red (@projT1 _ _) ls)))))).
Arguments getStructVal : simpl never.

Definition getStructConst ls :=
  (ConstStruct (fun i => snd (nth_Fin (map (@projT1 _ _) ls) i))
               (fun j => fst (nth_Fin (map (@projT1 _ _) ls) j))
               (fun k => nth_Fin_map2 (@projT1 _ _) (fun x => ConstT (snd x))
                                      ls k (projT2 (nth_Fin ls (Fin.cast k (map_length_red (@projT1 _ _) ls)))))).
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

Local Ltac Struct_neq :=
  match goal with
  | |- Struct _ _ <> Struct _ _ =>
    let H := fresh in intro H;
                      injection H;
                      intros;
                      repeat (existT_destruct Nat.eq_dec)
  end.

(*
Definition Kind_dec (k1: Kind): forall k2, {k1 = k2} + {k1 <> k2}.
Proof.
  induction k1; destruct k2; try (right; (intros; abstract congruence)).
  - left; abstract (reflexivity).
  - destruct (Nat.eq_dec n n0); [left; abstract (subst; reflexivity) | right; abstract congruence].
  - destruct (Nat.eq_dec n n0).
    + subst.
      induction n0.
      * left.
        abstract (f_equal; extensionality x; apply Fin.case0; exact x).
      * destruct  (IHn0 (fun i => s (Fin.FS i)) (fun i => k (Fin.FS i))
                         (fun i => H (Fin.FS i)) (fun i => k0 (Fin.FS i))
                         (fun i => s0 (Fin.FS i))).
        -- destruct (string_dec (s Fin.F1) (s0 Fin.F1)).
           ++ destruct (H Fin.F1 (k0 Fin.F1)).
              ** left.
                 abstract (
                 injection e;
                 intros;
                 repeat (existT_destruct Nat.eq_dec);
                 f_equal; extensionality x; apply (Fin.caseS' x); try assumption;
                 apply equal_f; assumption).
              ** right.
                 abstract (Struct_neq;
                           apply (n eq_refl)).
           ++ right.
              abstract (Struct_neq;
                        apply (n eq_refl)).
        -- right.
           abstract (Struct_neq;
                     apply (n eq_refl)).
    + right.
      abstract (intro;
                injection H0 as H0;
                intros;
                apply (n1 H0)).
  - destruct (Nat.eq_dec n n0).
    + destruct (IHk1 k2).
      * left.
        abstract (subst; reflexivity).
      * right.
        abstract (subst; intro;
                  injection H as H;
                  apply (n1 H)).
    + right.
      abstract (subst; intro;
                injection H as H;
                apply (n1 H)).
Defined.
*)

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
  exact (Fin_forallb (fun i => Kind_decb (ks i) (ks' (Fin_cast i (proj1 (Nat.eqb_eq n m) G)))) && Fin_forallb (fun i => String.eqb (fs i) (fs' (Fin_cast i (proj1 (Nat.eqb_eq n m) G))))).
  exact false.
Defined.


Lemma Kind_decb_refl : forall k, Kind_decb k k = true.
Proof.
  induction k; simpl; auto.
  - apply Nat.eqb_refl.
  -
    rewrite silly_lemma_true with (pf := (Nat.eqb_refl _)) by apply Nat.eqb_refl.
    rewrite andb_true_iff; split; rewrite Fin_forallb_correct; intros.
    + rewrite (hedberg Nat.eq_dec _ eq_refl); simpl; apply H.
    + rewrite (hedberg Nat.eq_dec _ eq_refl); simpl; apply String.eqb_refl.
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
      pose proof G.
      rewrite Nat.eqb_eq in H1 by auto.
      rewrite andb_true_iff in H0; destruct H0 as [G1 G2]; rewrite Fin_forallb_correct in G1,G2; subst.
      rewrite (hedberg Nat.eq_dec _ eq_refl) in G1,G2; simpl in *.
      setoid_rewrite H in G1.
      setoid_rewrite String.eqb_eq in G2.
      f_equal; extensionality i; auto.
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

Lemma Kind_dec : forall k1 k2 : Kind, {k1 = k2} + {k1 <> k2}.
Proof.
  intros.
  destruct (Kind_decb k1 k2) eqn:G.
  rewrite Kind_decb_eq in G; auto.
  right; intro.
  rewrite <- Kind_decb_eq in H.
  rewrite H in G; discriminate.
Qed.

Definition Signature_decb : Signature -> Signature -> bool :=
  fun '(k,l) '(k',l') => Kind_decb k k' && Kind_decb l l'.

Lemma Signature_decb_eq : forall s1 s2, Signature_decb s1 s2 = true <-> s1 = s2.
Proof.
  intros [] []; simpl; rewrite andb_true_iff; repeat rewrite Kind_decb_eq; firstorder congruence.
Qed.

(*
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
*)

Definition Signature_dec (s1 s2 : Signature) : {s1 = s2} + {s1 <> s2}.
Proof.
  intros; destruct (Signature_decb s1 s2) eqn:G.
  left; rewrite <- Signature_decb_eq; auto.
  right; intro.
  rewrite <- Signature_decb_eq in H.
  rewrite H in G; discriminate.
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
    | Sll n m => (fun x y => wlshift' x (wordToNat y))
    | Srl n m => (fun x y => wrshift' x (wordToNat y))
    | Sra n m => (fun x y => wrshifta' x (wordToNat y))
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
      | ReadArray n m k fv i =>
        match lt_dec (wordToNat (@evalExpr _ i)) n with
        | left pf => fun fv => fv (Fin.of_nat_lt pf)
        | right _ => fun _ => evalConstT (getDefaultConst k)
        end (@evalExpr _ fv)
      | ReadArrayConst n k fv i =>
        (@evalExpr _ fv) i
      | BuildArray n k fv => fun i => @evalExpr _ (fv i)
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











Fixpoint struct_get_field_index'
         (name: string) n
  := match n return
         forall (get_name : Fin.t n -> string),
                option (Fin.t n)
     with
     | 0 => fun _ => None
     | S m => fun get_name =>
       if String.eqb (get_name Fin.F1) name
       then Some Fin.F1
       else match struct_get_field_index' name _ (fun i => get_name (Fin.FS i)) with
            | Some i => Some (Fin.FS i)
            | None => None
            end
     end.

Definition struct_get_field_index n (kinds: Fin.t n -> Kind) (names: Fin.t n -> string) ty (e: Expr ty (SyntaxKind (Struct kinds names))) name
  := struct_get_field_index' name names.

Ltac struct_get_field_ltac packet name :=
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

Ltac struct_set_field_ltac packet name newval :=
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
         | H: (_ ++ _)%string = (_ ++ _)%string |- _ =>
           rewrite <- ?append_assoc in H; cbn [append] in H
         | |- (_ ++ _)%string = (_ ++ _)%string =>
           rewrite <- ?append_assoc; cbn [append]
         end;
  repeat match goal with
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           apply append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ =>
           apply append_remove_suffix in H; subst
         | |- (?a ++ ?b)%string = (?a ++ ?c)%string =>
           apply append_remove_prefix
         | |- (?a ++ ?b)%string = (?c ++ ?b)%string =>
           apply append_remove_suffix
         | H: (?a ++ (String ?x ?b))%string = (?c ++ (String ?y ?d))%string |- _ =>
           apply (f_equal string_rev) in H;
           rewrite (string_rev_append a (String x b)), (string_rev_append c (String y d)) in H;
           cbn [string_rev] in H;
           rewrite <- ?append_assoc in H; cbn [append] in H
         end.

Local Ltac finish_append :=
  auto; try (apply InSingleton || discriminate || tauto || congruence).

Ltac discharge_append :=
  simpl; unfold getBool in *; process_append; finish_append.

Goal forall (a b c: string),
  (a ++ "a" <> a ++ "b"
  /\ a ++ "a" ++ b <> c ++ "b" ++ b
  /\ a ++ "a" ++ "b" <> a ++ "a" ++ "c"
  /\ "a" ++ a <> "b" ++ b
  /\ (a ++ "a") ++ b <> a ++ "b" ++ a
  /\ (a ++ (b ++ "b")) ++ "c" <> (a ++ b) ++ "d")%string.
Proof. intuition idtac; discharge_append. Qed.

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
         | |- forall _, _ => intros
         | |- _ -> _ => intros 
         | H: In _ (getAllMethods _) |- _ => simpl in H;inversion H;subst;clear H;simpl
         end;
  discharge_DisjKey.


(* NOTATIONS WERE HERE *)

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
  (get_kind : Fin.t n -> Kind)
  (get_name : Fin.t n -> string)
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
  (get_value : Fin.t n -> Kind)
  (get_name : Fin.t n -> string)
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
  (get_value : Fin.t n -> Kind)
  (get_name : Fin.t n -> string)
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
  (get_kind : Fin.t n -> Kind)
  (get_name : Fin.t n -> string)
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
           (get_kind : Fin.t n -> Kind)
           (get_name : Fin.t n -> string)
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
     EclecticLib.nth_Fin
  : KamiDb.
(* TODO
   + PUAR: Linux/Certikos
 *)

