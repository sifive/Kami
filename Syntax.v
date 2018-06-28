Require Export Bool String List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word Lib.VectorFacts Lib.EclecticLib.

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
(* | ConstExtract lsb n msb: UniBitOp (lsb + n + msb) n (* LSB : n1, MSB : n3 *). *)

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

  (* Definition lgCeil i := S (Nat.log2_iter (pred (pred i)) 0 1 0). *)

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
                      (ReadArray e (Const (natToWord _ (proj1_sig (Fin.to_nat i')))))).

  Definition UpdateArrayConst n k (e: Expr (SyntaxKind (Array n k)))
             (i: Fin.t n)
             (v: Expr (SyntaxKind k)) :=
    BuildArray (fun i' : Fin.t n =>
                  match Fin.eq_dec i i' with
                  | left _ => v
                  | right _ => ReadArray e (Const (natToWord _ (proj1_sig (Fin.to_nat i'))))
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

  Section BitOps.
    Definition castBits ni no (pf: ni = no) (e: Expr (SyntaxKind (Bit ni))) :=
      nat_cast (fun n => Expr (SyntaxKind (Bit n))) pf e.

    Definition Slt n (e1 e2: Expr (SyntaxKind (Bit (n + 1)))) :=
      Eq (Eq (UniBit (TruncMsb n 1) e1) (UniBit (TruncMsb n 1) e2)) (BinBitBool (LessThan _) e1 e2).

    (* Definition TruncMsb lsb msb (e: Expr (SyntaxKind (Bit (lsb + msb)))): Expr (SyntaxKind (Bit msb)). *)
    (*   refine *)
    (*     (UniBit (ConstExtract lsb msb 0) (castBits _ e)). *)
    (*   abstract (Omega.omega). *)
    (* Defined. *)

    (* Definition TruncLsb lsb msb (e: Expr (SyntaxKind (Bit (lsb + msb)))): *)
    (*   Expr (SyntaxKind (Bit lsb)) := *)
    (*   (UniBit (ConstExtract 0 lsb msb) e). *)

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

    Fixpoint pack (k: Kind): Expr (SyntaxKind k) -> Expr (SyntaxKind (Bit (size k))) :=
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
               BinBit
                 (Concat (m * size k) (size k)) (help m)
                 (@pack k (ReadArray e (Const (natToWord (Nat.log2_up n) m))))
             end) n
      end.

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
        n * size_k = (n * size_k - ((proj1_sig (Fin.to_nat i) * size_k) + size_k)) + size_k + (proj1_sig (Fin.to_nat i) * size_k).
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
            (fun i => unpack _ (ConstExtract _ _ (proj1_sig (Fin.to_nat i) * size k)
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
  | DispArray: forall n k, Expr (SyntaxKind (Array n k)) -> FullBitFormat -> SysT.
  
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

Inductive BaseModule: Type :=
| RegFile (dataArray: string) (read: list string) (write: string) (IdxNum: nat) (Data: Kind)
          (init: option (ConstT Data)): BaseModule
| SyncRegFileAddr (dataArray: string) (read: list (string * string * string)) (write: string)
                  (IdxNum: nat) (Data: Kind) (init: option (ConstT Data)): BaseModule
| SyncRegFileData (dataArray: string) (read: list (string * string * string)) (write: string)
                  (IdxNum: nat) (Data: Kind) (init: option (ConstT Data)): BaseModule
| BaseMod (regs: list RegInitT) (rules: list RuleT) (dms: list DefMethT): BaseModule.

Inductive Mod: Type :=
| Base (m: BaseModule): Mod
| HideMeth (m: Mod) (meth: string): Mod
| ConcatMod (m1 m2: Mod): Mod.








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

(* Definition getStructVal ty n *)
(*            (ls: Vector.t {x: Attribute Kind & Expr ty (SyntaxKind (snd x))} n) := *)
(*   (BuildStruct (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i)) *)
(*                (fun i => fst (Vector.nth (Vector.map (@projT1 _ _) ls) i)) *)
(*                (fun i => Vector_nth_map2_r (@projT1 _ _) (fun x => Expr ty (SyntaxKind (snd x))) ls i (projT2 (Vector.nth ls i)))). *)

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (getStructVal (Vector.cons _ s1%struct_init _ ..
                             (Vector.cons _ sN%struct_init _ (Vector.nil _)) ..))
  : kami_expr_scope.


(** Notations for expressions *)

Notation Default := (getDefaultConst _).

Notation "k @# ty" := (Expr ty (SyntaxKind k)) (no associativity, at level 98, only parsing).

Notation "# v" := (Var ltac:(assumption) (SyntaxKind _) v) (at level 0) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (at level 0): kami_expr_scope.
Notation "$$ e" := (Const ltac:(assumption) e) (at level 8) : kami_expr_scope.

Local Definition testStruct :=
  (STRUCT {
       "hello" :: Bit 10 ;
       "a" :: Bit 3 ;
       "b" :: Bit 5 ;
       "test" :: Bool }).

Local Definition testStructVal ty: testStruct @# ty :=
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
        let aTySimpl := eval compute in aTy in
            match aTySimpl with
            | Expr _ (SyntaxKind (Bit ?w)) =>
              exact (ConstExtract
                       j
                       (i + 1 - j)%nat
                       (w - 1 - i)%nat
                       (@castBits _ w (j + (i + 1 - j) + (w - 1 - i)) ltac:(abstract (lia || nia)) a))
            end) (at level 100, i at level 99) : kami_expr_scope.
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

Ltac findStructIdx v f :=
  let idx := eval cbv in (Vector_find (fun x => getBool (string_dec (fst x) f%string)) v) in
      exact idx.

Ltac getStructList fs f := match fs with
                           | (fun i: Fin.t _ =>
                                fst (Vector.nth ?v i)): Fin.t _ -> string =>
                             findStructIdx v f
                           | _ => let y := eval hnf in fs in
                                      getStructList y f
                           end.

Ltac getStructStringFn v f := match v with
                              | Struct ?fk ?fs => getStructList fs f
                              | _ => let y := eval hnf in v in
                                         getStructStringFn y f
                              end.

Ltac getStructFull v f := match v with
                          | Expr _ (SyntaxKind ?y) => getStructStringFn y f
                          | _ => let y := eval hnf in v in
                                     getStructFull y f
                          end.

Notation "s @% f" := (ReadStruct s ltac:(let typeS := type of s in
                                         getStructFull typeS f))
                       (at level 38) : kami_expr_scope.

Notation "name ::= value" :=
  (name, value): kami_switch_init_scope.
Delimit Scope kami_switch_init_scope with switch_init.

Notation "'Switch' val 'Of' inK 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons ((SignExtend _ (pack (val == (fst s1%switch_init: Expr _ (SyntaxKind inK))))) & pack (snd s1%switch_init))%kami_expr ..
                                (cons ((SignExtend _ (pack (val == (fst sN%switch_init: Expr _ (SyntaxKind inK))))) & pack (snd sN%switch_init))%kami_expr nil) ..))):
    kami_expr_scope.

Notation "'Switch' val 'Retn' retK 'With' { s1 ; .. ; sN }" :=
  (unpack retK (CABit Bor (cons ((SignExtend _ (pack (val == (fst s1%switch_init)))) & pack (snd s1%switch_init))%kami_expr ..
                                (cons ((SignExtend _ (pack (val == (fst sN%switch_init)))) & pack (snd sN%switch_init))%kami_expr nil) ..))):
    kami_expr_scope.

Definition testSwitch ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Retn Bool With {
            $$ (natToWord 5 5) ::= $$ true ;
            $$ (natToWord 5 6) ::= $$ false
          })%kami_expr.

Definition testFieldAccess ty := 
  ((testStructVal ty) @% "hello")%kami_expr.

Notation "s '@%[' f <- v ]" := (UpdateStruct s%kami_expr (ltac:(let typeS := type of s in
                                                               getStructFull typeS f))
                                             v%kami_expr)
                                 (at level 100) : kami_expr_scope.

Definition testFieldUpd ty := 
  ((testStructVal ty) @%[ "hello" <- Const ty (natToWord 10 23) ])%kami_expr.

Local Definition testExtract ty n n1 n2 (pf1: n > n1) (pf2: n1 > n2) (a: Bit n @# ty) := (a $[n1 : n2])%kami_expr.

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

Delimit Scope kami_action_scope with kami_action.

(** * Notation for normal modules *)

Inductive ModuleElt :=
| MERegister (_ : RegInitT)
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
    | MERule mrule => (iregs, mrule :: irules, imeths)
    | MEMeth mmeth => (iregs, irules, mmeth :: imeths)
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

Delimit Scope kami_scope with kami.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..))
    (at level 12, only parsing).

Ltac existT_destruct :=
  match goal with
  | H: existT _ _ _ = existT _ _ _ |- _ =>
    apply EqdepFacts.eq_sigT_eq_dep in H;
    apply (Eqdep_dec.eq_dep_eq_dec Nat.eq_dec) in H;
    subst
  end.

Ltac Struct_neq :=
  match goal with
  | |- Struct _ _ <> Struct _ _ =>
    let H := fresh in intro H;
                      injection H;
                      intros;
                      repeat existT_destruct
  end.

Ltac inv H :=
  inversion H; subst; clear H.


Lemma Kind_dec (k1: Kind): forall k2, {k1 = k2} + {k1 <> k2}.
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
           repeat existT_destruct.
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
Qed.

Lemma Kind_eq: forall k, Kind_dec k k = left eq_refl.
Proof.
  intros; destruct (Kind_dec k k).
  - f_equal.
    apply Eqdep_dec.UIP_dec.
    apply Kind_dec.
  - apply (match n eq_refl with end).
Qed.

Lemma Signature_dec: forall (s1 s2: Signature), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality; apply Kind_dec.
Qed.

Lemma Signature_eq: forall sig, Signature_dec sig sig = left eq_refl.
Proof.
  intros; destruct (Signature_dec sig sig).
  - f_equal.
    apply Eqdep_dec.UIP_dec.
    apply Signature_dec.
  - apply (match n eq_refl with end).
Qed.

Fixpoint type (k: Kind): Type :=
  match k with
    | Bool => bool
    | Bit n => word n
    | Struct n fk fs => forall i, type (fk i)
    | Array n k' => Fin.t n -> type k'
  end.

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

(* Eval compute in ((evalBinBit (Concat 2 3) (WO~0~1) (WO~1~0~1))). *)
(* Eval compute in wordToNat ((evalBinBit (Concat 2 3) (WO~0~1) (WO~1~0~1))). *)
(* Eval compute in ((evalBinBit (Concat 3 2) (WO~1~0~1)) (WO~0~1) ). *)
(* Eval compute in wordToNat ((evalBinBit (Concat 3 2) (WO~1~0~1)) (WO~0~1) ). *)

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
Definition RegsT := list (Attribute (sigT (fullType type))).

(* a pair of the value sent to a method call and the value it returned *)
Definition SignT k := (type (fst k) * type (snd k))%type.

(* a list of simulatenous method call actions made during a single step *)
Definition MethT := Attribute (sigT SignT).
Definition MethsT := list MethT.

Notation getKindAttr ls := (map (fun x => (fst x, projT1 (snd x))) ls).

Fixpoint getRegisters m :=
  match m with
  | RegFile dataArray read write IdxNum Data init =>
    (dataArray, existT optConstFullT (SyntaxKind (Array IdxNum Data))
                       match init with
                       | None => None
                       | Some init' => Some (SyntaxConst (ConstArray (fun _ => init')))
                       end) :: nil
  | SyncRegFileAddr dataArray read write IdxNum Data init =>
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
  | SyncRegFileData dataArray read write IdxNum Data init =>
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
  | BaseMod regs rules dms => regs
  end.

Section Semantics.
  Variable m: BaseModule.
  
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

  Variable o: RegsT.

  Inductive SemAction:
    forall k, ActionT type k -> RegsT -> RegsT -> MethsT -> type k -> Prop :=
  | SemMCall
      meth s (marg: Expr type (SyntaxKind (fst s)))
      (mret: type (snd s))
      retK (fret: type retK)
      (cont: type (snd s) -> ActionT type retK)
      readRegs newRegs (calls: MethsT) acalls
      (HDisjCalls: key_not_In meth calls)
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
      (HDisjCalls: DisjKey calls callsCont)
      (HSemAction: SemAction a readRegs newRegs calls v)
      (HSemActionCont: SemAction (cont v) readRegsCont newRegsCont callsCont fret):
      SemAction (LetAction a cont) (readRegs ++ readRegsCont) (newRegs ++ newRegsCont)
                (calls ++ callsCont) fret
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
      (HDisjCalls: DisjKey calls1 calls2)
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
      (HDisjCalls: DisjKey calls1 calls2)
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

  Theorem inversionSemAction
          k a reads news calls retC
          (evalA: @SemAction k a reads news calls retC):
    match a with
    | MCall m s e c =>
      exists mret pcalls,
      key_not_In m pcalls /\
      SemAction (c mret) reads news pcalls retC /\
      calls = (m, (existT _ _ (evalExpr e, mret))) :: pcalls
    | LetExpr _ e cont =>
      SemAction (cont (evalExpr e)) reads news calls retC
    | LetAction _ a cont =>
      exists reads1 news1 calls1 reads2 news2 calls2 r1,
      DisjKey news1 news2 /\
      DisjKey calls1 calls2 /\  
      SemAction a reads1 news1 calls1 r1 /\
      SemAction (cont r1) reads2 news2 calls2 retC /\
      reads = reads1 ++ reads2 /\
      news = news1 ++ news2 /\
      calls = calls1 ++ calls2
    | ReadNondet k c =>
      exists rv,
      SemAction (c rv) reads news calls retC
    | ReadReg r k c =>
      exists rv reads2,
      In (r, existT _ k rv) o /\
      SemAction (c rv) reads2 news calls retC /\
      reads = (r, existT _ k rv) :: reads2
    | WriteReg r k e a =>
      exists pnews,
      In (r, k) (getKindAttr o) /\
      key_not_In r pnews /\
      SemAction a reads pnews calls retC /\
      news = (r, (existT _ _ (evalExpr e))) :: pnews
    | IfElse p _ aT aF c =>
      exists reads1 news1 calls1 reads2 news2 calls2 r1,
      DisjKey news1 news2 /\
      DisjKey calls1 calls2 /\
      match evalExpr p with
      | true =>
        SemAction aT reads1  news1 calls1 r1 /\
        SemAction (c r1) reads2 news2 calls2 retC /\
        reads = reads1 ++ reads2 /\
        news = news1 ++ news2 /\
        calls = calls1 ++ calls2
      | false =>
        SemAction aF reads1 news1 calls1 r1 /\
        SemAction (c r1) reads2 news2 calls2 retC /\
        reads = reads1 ++ reads2 /\
        news = news1 ++ news2 /\
        calls = calls1 ++ calls2
      end
    | Assertion e c =>
      SemAction c reads news calls retC /\
      evalExpr e = true
    | Sys _ c =>
      SemAction c reads news calls retC
    | Return e =>
      retC = evalExpr e /\
      news = nil /\
      calls = nil
    end.
  Proof.
    destruct evalA; eauto; repeat eexists; try destruct (evalExpr p); eauto; try discriminate.
  Qed.

  Lemma SemActionReadsSub k a reads upds calls ret:
    @SemAction k a reads upds calls ret ->
    SubList reads o.
  Proof.
    induction 1; auto;
      unfold SubList in *; intros;
        rewrite ?in_app_iff in *.
    - firstorder.
    - subst; firstorder.
      subst.
      firstorder.
    - subst.
      rewrite in_app_iff in H1.
      destruct H1; intuition.
    - subst.
      rewrite in_app_iff in H1.
      destruct H1; intuition.
    - subst; simpl in *; intuition.
  Qed.
End Semantics.

Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).


Fixpoint getRules m :=
  match m with
  | RegFile dataArray read write IdxNum Data init => nil
  | SyncRegFileAddr dataArray read write IdxNum Data init => nil
  | SyncRegFileData dataArray read write IdxNum Data init => nil
  | BaseMod regs rules dms => rules
  end.

Definition WriteRq IdxNum Data := STRUCT { "addr" :: Bit (Nat.log2_up IdxNum) ;
                                           "data" :: Data }.

Fixpoint getMethods m :=
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
  | SyncRegFileAddr dataArray read write IdxNum Data init =>
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
      :: (map (fun r =>
                 (fst (fst r),
                  existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                         (fun ty x =>
                            WriteReg (snd r) (Var ty (SyntaxKind _) x)
                                     (Return (Const _ WO)))))) read
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
  | SyncRegFileData dataArray read write IdxNum Data init =>
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
      :: (map (fun r =>
                 (fst (fst r),
                  existT MethodT (Bit (Nat.log2_up IdxNum), Void)
                         (fun ty x =>
                            ReadReg (snd r) (SyntaxKind (Bit (Nat.log2_up IdxNum)))
                                    (fun data =>
                                       WriteReg (snd r) (Var ty (SyntaxKind _) data)
                                                (Return (Const _ WO)))))) read)
      ++
      (map (fun r =>
                 (snd (fst r),
                  existT MethodT (Void, Data)
                         (fun ty x =>
                            ReadReg (snd r) (SyntaxKind Data)
                                    (fun data =>
                                       Return (Var ty _ data)))))
           read)
  | BaseMod regs rules dms => dms
  end.

Inductive RuleOrMeth :=
| Rle (rn: string)
| Meth (f: MethT).

Notation getRleOrMeth := (fun x => fst (snd x)).

Definition InExec f (l: list (RegsT * (RuleOrMeth * MethsT))) :=
  In (Meth f) (map getRleOrMeth l).

Definition InCall f (l: list (RegsT * (RuleOrMeth * MethsT))) :=
  exists x, In x l /\ In f (snd (snd x)).

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

Notation FullLabel := (RegsT * (RuleOrMeth * MethsT))%type.

Fixpoint getHidden m :=
  match m with
  | Base _ => []
  | ConcatMod m1 m2 => getHidden m1 ++ getHidden m2
  | HideMeth m' s => s :: getHidden m'
  end.

Definition MatchingExecCalls (lexec lcall: list FullLabel) mcall :=
  forall f, InCall f lexec ->
            In (fst f) (map fst (getAllMethods mcall)) ->
            ~ In (fst f) (getHidden mcall) /\ InExec f lcall.

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
            (HNoCall: forall c, In c cs -> InCall c ls -> False)
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
            (HNoCall: forall c, In c cs -> InCall c ls -> False)
            (HSubsteps: Substeps ls):
      Substeps l.
End BaseModule.

Inductive Step: Mod -> RegsT -> list FullLabel -> Prop :=
| BaseStep m o l (HSubsteps: Substeps m o l) (HMatching: MatchingExecCalls l l (Base m)):
    Step (Base m) o l
| HideMethStep m s o l (HStep: Step m o l)
               (HHidden: forall v, In s (map fst (getAllMethods m)) -> InExec (s, v) l -> InCall (s, v) l):
    Step (HideMeth m s) o l
| ConcatModStep m1 m2 o1 o2 l1 l2
                (HStep1: Step m1 o1 l1)
                (HStep2: Step m2 o2 l2)
                (HMatching1: MatchingExecCalls l1 l2 m2)
                (HMatching2: MatchingExecCalls l2 l1 m1)
                (HNoRle: forall x y, In x l1 -> In y l2 -> match fst (snd x), fst (snd y) with
                                                           | Rle _, Rle _ => False
                                                           | _, _ => True
                                                           end)
                (HNoCall: forall x, InCall x l1 -> InCall x l2 -> False)
                o l
                (HRegs: o = o1 ++ o2)
                (HLabels: l = l1 ++ l2):
    Step (ConcatMod m1 m2) o l.

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











Definition UpdRegs' (u: list RegsT) (o o': RegsT)
  := map fst o = map fst o' /\
     (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                   ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

Definition filterRegs f m (o: RegsT) :=
  filter (fun x => f (getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m))))) o.

Definition filterExecs f m (l: list FullLabel) :=
  filter (fun x => f match fst (snd x) with
                     | Rle y =>
                       getBool (in_dec string_dec y (map fst (getAllRules m)))
                     | Meth (y, _) =>
                       getBool (in_dec string_dec y (map fst (getAllMethods m)))
                     end) l.


Definition TraceInclusion m1 m2 :=
  forall o1 ls1,
    Trace m1 o1 ls1 ->
    exists o2 ls2,
      Trace m2 o2 ls2 /\
      length ls1 = length ls2 /\
      (nthProp2
         (fun l1 l2 =>
            (forall f, (InExec f l1 /\ ~ InCall f l1) <->
                       (InExec f l2 /\ ~ InCall f l2)) /\
            (forall f, (~ InExec f l1 /\ InCall f l1) <->
                       (~ InExec f l2 /\ InCall f l2)) /\
            (forall f, ((InExec f l1 /\ InCall f l1) \/ (~ InExec f l1 /\ ~ InCall f l1)) <->
                       ((InExec f l2 /\ InCall f l2) \/ (~ InExec f l2 /\ ~ InCall f l2))) /\
            ((exists rle, In (Rle rle) (map (fun x => fst (snd x)) l2)) ->
             (exists rle, In (Rle rle) (map (fun x => fst (snd x)) l1)))) ls1 ls2).


Section WfBaseMod.
  Variable m: BaseModule.
  
  Inductive WfActionT: forall lretT, ActionT type lretT -> Prop :=
  | WfMCall meth s e lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (MCall meth s e c)
  | WfLetExpr k (e: Expr type k) lretT c: WfActionT (c (evalExpr e)) -> @WfActionT lretT (LetExpr e c)
  | WfLetAction k (a: ActionT type k) lretT c: WfActionT a -> (forall v, WfActionT (c v)) -> @WfActionT lretT (LetAction a c)
  | WfReadNondet k lretT c: (forall v, WfActionT (c v)) -> @WfActionT lretT (ReadNondet k c)
  | WfReadReg r k lretT c: (forall v, WfActionT (c v)) -> In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (ReadReg r k c)
  | WfWriteReg r k (e: Expr type k) lretT c: WfActionT c  -> In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (WriteReg r e c)
  | WfIfElse p k (atrue: ActionT type k) afalse lretT c: (forall v, WfActionT (c v)) -> WfActionT atrue -> WfActionT afalse -> @WfActionT lretT (IfElse p atrue afalse c)
  | WfAssertion (e: Expr type (SyntaxKind Bool)) lretT c: WfActionT c -> @WfActionT lretT (Assertion e c)
  | WfSys ls lretT c: WfActionT c -> @WfActionT lretT (Sys ls c)
  | WfReturn lretT e: @WfActionT lretT (Return e).

  Definition WfBaseMod :=
    (forall rule, In rule (getRules m) -> WfActionT (snd rule type)) /\
    (forall meth, In meth (getMethods m) -> forall v, WfActionT (projT2 (snd meth) type v)).
End WfBaseMod.

Inductive WfConcatActionT : forall lretT, ActionT type lretT -> Mod -> Prop :=
| WfConcatMCall meth s e lretT c m' :(forall v, WfConcatActionT (c v) m') -> ~In meth (getHidden m') -> @WfConcatActionT lretT (MCall meth s e c) m'
| WfConcatLetExpr k (e : Expr type k) lretT c m' : WfConcatActionT (c (evalExpr e)) m' -> @WfConcatActionT lretT (LetExpr e c) m'
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
| BaseWf m (WfBaseModule: WfBaseMod m)(NoDupMeths: NoDup (map fst (getMethods m)))
         (NoDupRegs : NoDup (map fst (getRegisters m)))(NoDupRle : NoDup (map fst (getRules m))): WfMod (Base m)
| HideMethWf m s (HHideWf: In s (map fst (getAllMethods m))) (HWf: WfMod m): WfMod (HideMeth m s)
| ConcatModWf m1 m2 (HDisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2))
              (HDisjRules: DisjKey (getAllRules m1) (getAllRules m2))
              (HDisjMeths: DisjKey (getAllMethods m1) (getAllMethods m2))
              (HWf1: WfMod m1) (HWf2: WfMod m2)(WfConcat1: WfConcat m1 m2)
              (WfConcat2 : WfConcat m2 m1): WfMod (ConcatMod m1 m2).

Definition getFlat m := BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m).

Fixpoint createHide (m: BaseModule) (hides: list string) :=
  match hides with
  | nil => Base m
  | x :: xs => HideMeth (createHide m xs) x
  end.

Definition flatten m := createHide (getFlat m) (getHidden m).



Definition StepSubstitute m o l :=
  Substeps (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) o l /\
  MatchingExecCalls l l (Base (getFlat m)) /\
  (forall s v, In s (map fst (getAllMethods m)) -> In s (getHidden m) -> InExec (s, v) l -> InCall (s, v) l).


Section inlineSingle.
  Variable ty: Kind -> Type.
  Variable f: DefMethT.
  Variable cheat: forall t, t.
  
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


Definition inlinesingle_Rule  (f : DefMethT) (rle : RuleT): RuleT.
Proof.
  unfold RuleT in *.
  destruct rle.
  constructor.
  - apply s.
  - unfold Action in *.
    intro.
    apply (inlineSingle f (a ty)).
Defined.

Definition inlinesingle_Meth (f : DefMethT) (meth : DefMethT): DefMethT.
Proof.
  unfold DefMethT in *.
  destruct meth.
  constructor.
  - apply s.
  -  destruct s0.
     unfold MethodT; unfold MethodT in m.
     exists x.
     intros.
     apply (inlineSingle f (m ty X)).
Defined.

Definition inlinesingle_BaseModule (m : BaseModule) (f : DefMethT) : BaseModule :=
  BaseMod (getRegisters m) (map (inlinesingle_Rule f) (getRules m)) (map (inlinesingle_Meth f) (getMethods m)).

Fixpoint inlinesingle_Mod (m : Mod) (f : DefMethT) : Mod :=
  match m with
  |Base bm => Base (inlinesingle_BaseModule bm f)
  |HideMeth m' s => HideMeth (inlinesingle_Mod m' f) s
  |ConcatMod m1 m2 => ConcatMod (inlinesingle_Mod m1 f) (inlinesingle_Mod m2 f)
  end.

(*
 * Kami Rewrite
   + Flattening Theorem (easy)
   + Inlining Theorem (moderate)
   + Compiler verification (difficult)
 * Verify FPU
   + Write Spec in a generic manner
   + Use Word library to prove things.
 * Equivalence checking
   + Prove compiler (difficult)
   + Match RTL (easy)
 * PUAR: Linux/Certikos
 *)
