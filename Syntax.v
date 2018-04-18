Require Export Bool String List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word bbv.WordProps Lib.VectorFacts Lib.EclecticLib.

Require Vector.

Import Coq.Vectors.VectorDef.VectorNotations.
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
      ITE (Eq (UniBit (TruncMsb n 1) e1) (Const WO~0))
          (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const WO~0)) (BinBitBool (LessThan _) e1 e2) (Const true))
          (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const WO~1)) (BinBitBool (LessThan _) e2 e1) (Const false)).
      

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
Definition RegInitT := Attribute (sigT ConstFullT).
Definition DefMethT := Attribute (sigT MethodT).
Definition RuleT := Attribute (Action Void).

Inductive BaseModule: Type :=
| RegFile (dataArray: string) (read: list string) (write: string) (IdxNum: nat) (Data: Kind)
          (init: ConstT Data): BaseModule
| SyncRegFileAddr (dataArray: string) (read: list (string * string * string)) (write: string)
                  (IdxNum: nat) (Data: Kind) (init: ConstT Data): BaseModule
| SyncRegFileData (dataArray: string) (read: list (string * string * string)) (write: string)
                  (IdxNum: nat) (Data: Kind) (init: ConstT Data): BaseModule
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

Ltac getStructList structVal :=
  
  let structV := (let structValF := eval cbv [structVal] in structVal in exact structValF || exact structVal) in
  match type of structV with
  | Expr _ (SyntaxKind ?val) => (let y := eval cbv [val] in val in
                                     match y with
                                     | getStruct ?ls => exact ls
                                     end ||
                                     match val with
                                     | getStruct ?ls => exact ls
                                     end)
  end.

Notation "s @% f" := (ReadStruct s ltac:(let structV := eval cbv in s in
                                             let typeStructV := type of structV in
                                             match type of structV with
                                             | Expr _ (SyntaxKind ?val) =>
                                               let valS := eval compute in val in
                                                   match valS with
                                                   | Struct (fun i => let (_, _) := _ ?ls in _)
                                                            (fun j => let (_, _) := _ ?ls in _) =>
                                                     let idx := eval cbv in (Vector_find_opt (fun x => getBool (string_dec (fst x) f%string)) ls) in
                                                         match idx with
                                                         | Some ?idx' =>
                                                           exact idx'
                                                         end
                                                   end
                                             end))
                       (at level 38) : kami_expr_scope.

Definition testFieldAccess ty := 
  ((testStructVal ty) @% "hello")%kami_expr.

Notation "s '@%[' f <- v ]" := (UpdateStruct s%kami_expr ltac:(let structV := eval cbv in s in
                                                                   let typeStructV := type of structV in
                                                                   match type of structV with
                                                                   | Expr _ (SyntaxKind ?val) =>
                                                                     match val with
                                                                     | Struct (fun i => let (_, _) := _ ?ls in _)
                                                                              (fun j => let (_, _) := _ ?ls in _) =>
                                                                       let idx := eval cbv in (Vector_find_opt (fun x => getBool (string_dec (fst x) f%string)) ls) in
                                                                           match idx with
                                                                           | Some ?idx' =>
                                                                             exact idx'
                                                                           end
                                                                     end
                                                                   end) v%kami_expr)
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
  (LetAction (k := SyntaxKind t) act (fun name => cont))
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
  (MERegister (name%string, existT ConstFullT type init))
    (at level 12, name at level 99) : kami_scope.

Notation "'Register' name : type <- init" :=
  (MERegister (name%string, existT ConstFullT (SyntaxKind type) (makeConst init)))
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


Lemma SignT_dec: forall k1 k2 (s1 s2: SignT (k1, k2)), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  simpl in *.
  apply prod_dec; simpl; auto;
    apply isEq.
Qed.

Lemma sigT_SignT_dec: forall s1 s2: (sigT SignT), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  destruct (Signature_dec x x0); subst.
  - destruct (SignT_dec s s0); subst.
    + left; reflexivity.
    + right; intro.
      apply EqdepFacts.eq_sigT_eq_dep in H.
      apply (Eqdep_dec.eq_dep_eq_dec (Signature_dec)) in H.
      tauto.
  - right; intro.
    inversion H.
    tauto.
Qed.

Lemma MethT_dec: forall s1 s2: MethT, {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  destruct s1, s2.
  apply prod_dec.
  - apply string_dec.
  - apply sigT_SignT_dec.
Qed.

Notation getKindAttr ls := (map (fun x => (fst x, projT1 (snd x))) ls).

Fixpoint getRegisters m :=
  match m with
  | RegFile dataArray read write IdxNum Data init =>
    (dataArray, existT ConstFullT (SyntaxKind (Array IdxNum Data))
                       (SyntaxConst (ConstArray (fun _ => init)))) :: nil
  | SyncRegFileAddr dataArray read write IdxNum Data init =>
    (dataArray, existT ConstFullT (SyntaxKind (Array IdxNum Data))
                       (SyntaxConst (ConstArray (fun _ => init))))
      ::
      map (fun x => (snd x, existT ConstFullT (SyntaxKind Data) (SyntaxConst init))) read
  | SyncRegFileData dataArray read write IdxNum Data init =>
    (dataArray, existT ConstFullT (SyntaxKind (Array IdxNum Data))
                       (SyntaxConst (ConstArray (fun _ => init))))
      ::
      map (fun x => (snd x, existT ConstFullT (SyntaxKind Data) (SyntaxConst init))) read
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

Local Notation getRleOrMeth := (fun x => fst (snd x)).

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

Local Notation FullLabel := (RegsT * (RuleOrMeth * MethsT))%type.

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

Notation regInit := (fun r => (fst r, existT _ _ (evalConstFullT (projT2 (snd r))))).

Section Trace.
  Variable m: Mod.
  Inductive Trace: RegsT -> list (list FullLabel) -> Prop :=
  | InitTrace o' ls'
              (HUpdRegs: o' = (map regInit (getAllRegisters m)))
              (HTrace: ls' = nil):
      Trace o' ls'
  | ContinueTrace o ls l o' ls'
                  (HOldTrace: Trace o ls)
                  (HStep: Step m o l)
                  (HUpdRegs: UpdRegs (map fst l) o o')
                  (HTrace: ls' = l :: ls):
      Trace o' ls'.
End Trace.










Section evalExpr.

  Lemma nat_cast_same n: forall (P: nat -> Type) (e: P n), nat_cast P eq_refl e = e.
  Proof.
    induction n; simpl; auto; intros.
    eapply (IHn (fun n => P (S n))).
  Qed.
  
  Lemma castBits_same ty ni no (pf: ni = no) (e: Expr ty (SyntaxKind (Bit ni))): castBits pf e = match pf in _ = Y return Expr ty (SyntaxKind (Bit Y)) with
                                                                                                 | eq_refl => e
                                                                                                 end.
  Proof.
    unfold castBits.
    destruct pf.
    rewrite nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_castBits: forall ni no (pf: ni = no) (e: Bit ni @# type), evalExpr (castBits pf e) =
                                                                           nat_cast (fun n => word n) pf (evalExpr e).
  Proof.
    intros.
    unfold castBits.
    destruct pf.
    rewrite ?nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_BinBit: forall kl kr k (op: BinBitOp kl kr k)
                                (l1 l2: Bit kl @# type)
                                (r1 r2: Bit kr @# type),
    evalExpr l1 = evalExpr l2 ->
    evalExpr r1 = evalExpr r2 ->
    evalExpr (BinBit op l1 r1) = evalExpr (BinBit op l2 r2).
  Proof.
    intros.
    induction op; simpl; try congruence.
  Qed.

  Lemma evalExpr_ZeroExtend: forall lsb msb (e1 e2: Bit lsb @# type), evalExpr e1 = evalExpr e2 ->
                                                                      evalExpr (ZeroExtend msb e1) = evalExpr (ZeroExtend msb e2).
  Proof.
    intros.
    unfold ZeroExtend.
    erewrite evalExpr_BinBit; eauto.
  Qed.

  Lemma evalExpr_pack_Bool: forall (e1 e2: Bool @# type),
      evalExpr e1 = evalExpr e2 ->
      evalExpr (pack e1) = evalExpr (pack e2).
  Proof.
    intros.
    simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma evalExpr_Void (e: Expr type (SyntaxKind (Bit 0))):
    evalExpr e = WO.
  Proof.
    inversion e; auto.
  Qed.

  Lemma evalExpr_countLeadingZeros ni: forall no (e: Expr type (SyntaxKind (Bit ni))),
      evalExpr (countLeadingZeros no e) = countLeadingZerosWord no (evalExpr e).
  Proof.
    induction ni; simpl; intros; auto.
    rewrite evalExpr_castBits.
    simpl.
    unfold wzero at 2.
    rewrite wzero_wplus.
    match goal with
    | |- (if getBool ?P then _ else _) = (if ?P then _ else _) => destruct P; auto
    end.
    repeat f_equal.
    rewrite IHni.
    simpl.
    rewrite evalExpr_castBits.
    repeat f_equal.
  Qed.




  Lemma evalExpr_pack: forall k (e1 e2: k @# type),
      evalExpr e1 = evalExpr e2 ->
      evalExpr (pack e1) = evalExpr (pack e2).
  Proof.
    intros.
    induction k; simpl; rewrite ?H; try auto.
    admit.
    admit.
  Admitted.
End evalExpr.



















Definition UpdRegs' (u: list RegsT) (o o': RegsT)
  := map fst o = map fst o' /\
     (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                   ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

Lemma UpdRegs_same: forall u o o', UpdRegs u o o' -> UpdRegs' u o o'.
Proof.
  unfold UpdRegs, UpdRegs'.
  intros; dest.
  apply (f_equal (map fst)) in H.
  rewrite ?map_map in H; simpl in *.
  setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; tauto.
Qed.

Definition filterRegs f m (o: RegsT) :=
  filter (fun x => f (getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m))))) o.

Definition filterExecs f m (l: list FullLabel) :=
  filter (fun x => f match fst (snd x) with
                     | Rle y =>
                       getBool (in_dec string_dec y (map fst (getAllRules m)))
                     | Meth (y, _) =>
                       getBool (in_dec string_dec y (map fst (getAllMethods m)))
                     end) l.

Lemma getKindAttr_map_fst A (P Q: A -> Type)
  : forall (l2: list (Attribute (sigT P))) (l1: list (Attribute (sigT Q))),
    getKindAttr l1 = getKindAttr l2 ->
    map fst l1 = map fst l2.
Proof.
  induction l2; simpl; auto; intros.
  - apply map_eq_nil in H; subst; auto.
  - destruct l1; simpl in *.
    + discriminate.
    + inv H; f_equal.
      apply IHl2; auto.
Qed.

Lemma Step_getAllRegisters m o l:
  Step m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; auto; simpl.
  - inv HSubsteps; auto.
  - rewrite map_app.
    rewrite <- IHStep1, <- IHStep2, HRegs.
    rewrite map_app.
    auto.
Qed.

Lemma Step_getAllRegisters_fst m o l:
  Step m o l ->
  map fst o = map fst (getAllRegisters m).
Proof.
  intros.
  apply Step_getAllRegisters in H.
  eapply getKindAttr_map_fst; eauto.
Qed.

Lemma DisjRegs_1_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_1_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.

Lemma Substeps_rm_In m o l:
  Substeps m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getMethods m)))
             end = true.
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getRules m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInRules)).
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getMethods m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInMeths)).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_In m o l:
  Step m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m)))
             end = true.
Proof.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_In; eauto.
  - subst.
    specialize (IHStep1 fv).
    specialize (IHStep2 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite in_app_iff in *.
    + destruct (in_dec string_dec b (map fst (getAllRules m1))),
      (in_dec string_dec b (map fst (getAllRules m2))); simpl in *; tauto.
    + destruct (in_dec string_dec s (map fst (getAllMethods m1))),
      (in_dec string_dec s (map fst (getAllMethods m2))); simpl in *; tauto.
Qed.

Lemma Substeps_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getRules m2) ->
  DisjKey (getAllMethods m1) (getMethods m2) ->
  Substeps m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros; subst; try tauto.
  - destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getAllRules m1))); simpl; auto.
      apply (in_map fst) in HInRules.
      clear - DisjRules DisjMeths HInRules i; firstorder.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getAllMethods m1))); simpl; auto.
      apply (in_map fst) in HInMeths.
      clear - DisjRules DisjMeths HInMeths i; firstorder.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_not_In; eauto.
  - subst.
    assert (sth1: DisjKey (getAllRules m1) (getAllRules m0)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth2: DisjKey (getAllMethods m1) (getAllMethods m0)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    assert (sth3: DisjKey (getAllRules m1) (getAllRules m2)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth4: DisjKey (getAllMethods m1) (getAllMethods m2)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    specialize (IHStep1 sth1 sth2 fv).
    specialize (IHStep2 sth3 sth4 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite ?in_app_iff in *; simpl in *; firstorder fail.
Qed.
  
Lemma DisjMeths_1_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m1 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_not_In; eauto.
  - eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m2 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_In; eauto.
  - eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.
  
Lemma DisjMeths_1_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m1 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_true_iff.
      eapply Step_rm_not_In; eauto.
  - setoid_rewrite negb_false_iff.
    eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m2 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_false_iff.
      eapply Step_rm_In; eauto.
  - setoid_rewrite negb_true_iff.
    eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.

Lemma Substeps_upd_SubList_key m o l:
  Substeps m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - simpl in *; tauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Substeps_upd_In m o l:
  Substeps m o l ->
  forall x, In x (map fst l) ->
            forall s: string, In s (map fst x) ->
                              In s (map fst (getRegisters m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest; subst.
  destruct x0; simpl.
  eapply Substeps_upd_SubList_key; eauto.
Qed.

Lemma Substeps_read m o l:
  Substeps m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
Qed.
  
Lemma Step_upd_SubList_key m o l:
  Step m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_upd_SubList_key; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 x s v).
    specialize (IHStep2 x s v).
    tauto.
Qed.

Lemma Step_read m o l:
  Step m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_read; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 s v).
    specialize (IHStep2 s v).
    tauto.
Qed.
  
Section SplitJoin.
  Variable m1 m2: Mod.

  Variable DisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2).
  Variable DisjRules: DisjKey (getAllRules m1) (getAllRules m2).
  Variable DisjMethods: DisjKey (getAllMethods m1) (getAllMethods m2).

  Lemma SplitStep o l:
    Step (ConcatMod m1 m2) o l ->
    Step m1 (filterRegs id m1 o) (filterExecs id m1 l) /\
    Step m2 (filterRegs id m2 o) (filterExecs id m2 l) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    MatchingExecCalls (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
    MatchingExecCalls (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
    (forall x y : FullLabel,
        In x (filterExecs id m1 l) ->
        In y (filterExecs id m2 l) ->
        match fst (snd x) with
        | Rle _ => match fst (snd y) with
                   | Rle _ => False
                   | Meth _ => True
                   end
        | Meth _ => True
        end) /\
    (forall x : MethT, InCall x (filterExecs id m1 l) -> InCall x (filterExecs id m2 l) -> False) /\
    l = filterExecs id m1 l ++ filterExecs id m2 l.
  Proof.
    intros H.
    inv H; intros.
    pose proof (Step_getAllRegisters_fst HStep1) as HRegs1.
    pose proof (Step_getAllRegisters_fst HStep2) as HRegs2.
    unfold filterRegs.
    rewrite DisjRegs_1_id with (l2 := getAllRegisters m2) (o1 := o1),
                               DisjRegs_2_id with (l1 := getAllRegisters m1) (o2 := o2); auto.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2), DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    Opaque MatchingExecCalls.
    repeat split; auto.
  Qed.

  Lemma Step_upd_1 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m1)) ->
      In x (map fst (filterExecs id m1 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H0 _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.
    
  Lemma Step_upd_2 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m2)) ->
      In x (map fst (filterExecs id m2 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.
  
  Lemma SplitTrace o ls:
    Trace (ConcatMod m1 m2) o ls ->
    Trace m1 (filterRegs id m1 o) (map (filterExecs id m1) ls) /\
    Trace m2 (filterRegs id m2 o) (map (filterExecs id m2) ls) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    mapProp
      (fun l =>
         MatchingExecCalls (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
         MatchingExecCalls (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
         (forall x y : FullLabel,
             In x (filterExecs id m1 l) ->
             In y (filterExecs id m2 l) ->
             match fst (snd x) with
             | Rle _ => match fst (snd y) with
                        | Rle _ => False
                        | Meth _ => True
                        end
             | Meth _ => True
             end) /\
         (forall x : MethT, InCall x (filterExecs id m1 l) -> InCall x (filterExecs id m2 l) -> False) /\
         l = filterExecs id m1 l ++ filterExecs id m2 l) ls /\
  map fst o = map fst (getAllRegisters (ConcatMod m1 m2)).
  Proof.
    Opaque MatchingExecCalls.
    induction 1; subst; simpl.
    - unfold filterRegs, filterExecs; simpl.
      rewrite ?map_app, ?filter_app.
      unfold id in *.
      pose proof (filter_In_map_same string_dec
                                     (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                     (getAllRegisters m1)) as sth1.
      pose proof (filter_DisjKeys string_dec
                                  (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                  DisjRegs) as sth2.
      pose proof (filter_In_map_same string_dec
                                     (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                     (getAllRegisters m2)) as sth3.
      assert (DisjRegs': DisjKey (getAllRegisters m2) (getAllRegisters m1)) by
          (clear - DisjRegs; firstorder).
      pose proof (filter_DisjKeys string_dec
                                  (fun x => existT _ _ (evalConstFullT (projT2 x)))
                                  DisjRegs') as sth4.
      simpl in *.
      rewrite ?sth1, ?sth2, ?sth3, ?sth4, ?app_nil_r.
      simpl.
      repeat split; try constructor; auto.
      rewrite ?map_map, ?map_app.
      simpl.
      rewrite ?sth5; auto.
    - pose proof HStep as HStep'.
      apply SplitStep in HStep.
      dest.
      repeat split; try econstructor 2; eauto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H13; auto.
        * unfold filterRegs, id in H15.
          rewrite filter_In in H15; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m1))); [simpl in *| discriminate].
          specialize (H14 _ _ H15).
          destruct H14; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_1; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H17.
                rewrite in_map_iff in H17; dest.
                rewrite filter_In in H20; dest.
                setoid_rewrite in_map_iff at 1 in H14.
                clear - H14 H17 H20 H19.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m1))); simpl; auto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H13; auto.
        * unfold filterRegs, id in H15.
          rewrite filter_In in H15; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m2))); [simpl in *| discriminate].
          specialize (H14 _ _ H15).
          destruct H14; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_2; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H17.
                rewrite in_map_iff in H17; dest.
                rewrite filter_In in H20; dest.
                setoid_rewrite in_map_iff at 1 in H14.
                clear - H14 H17 H20 H19.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m2))); simpl; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H13 in H4.
        simpl in H4.
        rewrite map_app in H4.
        unfold filterRegs, id.
        apply filter_map_app_sameKey; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H13 in H4.
        simpl in H4.
        auto.
  Qed.

  Lemma JoinStep o1 o2 l1 l2:
    Step m1 o1 l1 ->
    Step m2 o2 l2 ->
    (MatchingExecCalls l1 l2 m2) ->
    (MatchingExecCalls l2 l1 m1) ->
    (forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                           | Rle _, Rle _ => False
                                           | _, _ => True
                                           end) ->
    (forall x, InCall x l1 -> InCall x l2 -> False) ->
    Step (ConcatMod m1 m2) (o1 ++ o2) (l1 ++ l2).
  Proof.
    intros.
    econstructor 3; eauto.
  Qed.

  Lemma JoinTrace_basic l:
    forall o1 o2,
    Trace m1 o1 (map fst l) ->
    Trace m2 o2 (map snd l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls l1 l2 m2) l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls l2 l1 m1) l) ->
    (mapProp2 (fun l1 l2 =>
                 (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                     In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                             | Rle _ => match fst (snd x2) with
                                                        | Rle _ => False
                                                        | Meth _ => True
                                                        end
                                             | Meth _ => True
                                             end)) l) ->
    (mapProp2 (fun l1 l2 =>
                 (forall x, InCall x l1 ->
                            InCall x l2 -> False)) l) ->
    Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) l).
  Proof.
    induction l; simpl; intros.
    - inversion H; inversion H0; subst; try discriminate.
      constructor; auto.
      simpl.
      rewrite map_app.
      reflexivity.
    - destruct a; simpl in *; dest.
      inv H; [discriminate| ]; inv H0; [discriminate|].
      inv HTrace; inv HTrace0.
      specialize (IHl _ _ HOldTrace HOldTrace0 H8 H7 H6).
      econstructor 2 with (o := o ++ o0); eauto.
      eapply JoinStep; eauto.
      unfold UpdRegs in *; dest.
      split.
      + rewrite ?map_app.
        congruence.
      + intros.
        rewrite in_app_iff in H11.
        destruct H11.
        * specialize (H10 _ _ H11).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H10; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H13; [firstorder fail|].
             rewrite in_map_iff in H14; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep0 _ _ _ H13 H15).
             pose proof (Step_read HStep _ _ H12).
             firstorder fail.
        * specialize (H0 _ _ H11).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H0; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H13; [|firstorder fail].
             rewrite in_map_iff in H14; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep _ _ _ H13 H15).
             pose proof (Step_read HStep0 _ _ H12).
             firstorder fail.
  Qed.

  Lemma JoinTrace_len l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls l1 l2 m2) l1 l2) ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls l2 l1 m1) l1 l2) ->
      (mapProp_len (fun l1 l2 =>
                      (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                          In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                  | Rle _ => match fst (snd x2) with
                                                             | Rle _ => False
                                                             | Meth _ => True
                                                             end
                                                  | Meth _ => True
                                                  end)) l1 l2) ->
      (mapProp_len (fun l1 l2 =>
                      (forall x, InCall x l1 -> InCall x l2 -> False)) l1 l2) ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (zip l1 l2)).
  Proof.
    intros.
    eapply JoinTrace_basic; rewrite ?fst_zip, ?snd_zip; eauto;
      eapply mapProp2_len_same; eauto.
  Qed.

  Lemma JoinTrace l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      nthProp2 (fun l1 l2 => MatchingExecCalls l1 l2 m2 /\
                             MatchingExecCalls l2 l1 m1 /\
                             (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                                 In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                         | Rle _ => match fst (snd x2) with
                                                                    | Rle _ => False
                                                                    | Meth _ => True
                                                                    end
                                                         | Meth _ => True
                                                         end) /\
                             (forall x, InCall x l1 -> InCall x l2 -> False)) l1 l2 ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (zip l1 l2)).
  Proof.
    intros ? ? ? ?.
    setoid_rewrite <- mapProp_len_nthProp2; auto.
    repeat rewrite mapProp_len_conj; auto.
    pose proof (@JoinTrace_len l1 l2 o1 o2 H).
    intros; dest.
    firstorder fail.
  Qed.
End SplitJoin.

Lemma InExec_dec: forall x l, {InExec x l} + {~ InExec x l}.
Proof.
  unfold InExec; intros.
  apply in_dec; intros.
  decide equality.
  - apply string_dec.
  - apply MethT_dec.
Qed.

Lemma Substeps_meth_In m o l:
  Substeps m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      apply (in_map fst _ _ HInMeths).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_meth_In m o l:
  Step m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - eapply Substeps_meth_In; eauto.
  - eauto.
  - rewrite map_app, in_app_iff in *.
    clear - IHStep1 IHStep2 H1;
      firstorder fail.
Qed.

Lemma Step_meth_InExec m o l:
  Step m o l ->
  forall f, InExec f l ->
            In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  unfold InExec in *.
  rewrite in_map_iff in H0.
  dest.
  destruct x; simpl in *.
  destruct p; simpl in *; subst.
  eapply Step_meth_In; eauto.
Qed.

Lemma Trace_meth_In m o ls:
  Trace m o ls ->
  forall u f cs i l, nth_error ls i = Some l ->
                     In (u, (Meth f, cs)) l ->
                     In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; auto; destruct i; simpl in *.
  - subst; simpl in *; congruence.
  - subst; simpl in *; congruence.
  - subst.
    eapply Step_meth_In with (o := o) (u := u) (f := f) (cs := cs) in H1; eauto.
    inv H0; auto.
  - subst; simpl in *.
    eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_In_map m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                In (Meth f) (map (fun x => fst (snd x)) l) ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest.
  destruct x.
  destruct p.
  simpl in *; subst.
  eapply Trace_meth_In; eauto.
Qed.
  
Lemma Trace_meth_InExec m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                InExec f l ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  apply Trace_meth_In_map.
Qed.

Lemma InExec_app_iff: forall x l1 l2, InExec x (l1 ++ l2) <-> InExec x l1 \/ InExec x l2.
Proof.
  unfold InExec in *; intros.
  rewrite map_app.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma InCall_app_iff: forall x l1 l2, InCall x (l1 ++ l2) <-> InCall x l1 \/ InCall x l2.
Proof.
  unfold InCall in *; intros.
  setoid_rewrite in_app_iff.
  firstorder fail.
Qed.

Lemma Step_meth_InCall_InDef_InExec m o ls:
  Step m o ls ->
  forall (f : MethT),
    InCall f ls ->
    In (fst f) (map fst (getAllMethods m)) -> InExec f ls.
Proof.
  induction 1.
  - unfold MatchingExecCalls in *.
    firstorder fail.
  - assumption.
  - subst.
    simpl.
    rewrite map_app.
    setoid_rewrite in_app_iff.
    setoid_rewrite InExec_app_iff.
    intros.
    rewrite InCall_app_iff in H1.
    unfold MatchingExecCalls in *.
    repeat match goal with
           | H: forall (x: MethT), _ |- _ => specialize (H f)
           end.
    tauto.
Qed.

Lemma Trace_meth_InCall_InDef_InExec m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l -> InCall f l ->
    In (fst f) (map fst (getAllMethods m)) -> InExec f l.
Proof.
  induction 1; subst; auto; simpl; intros.
  - destruct i; simpl in *; try congruence.
  - destruct i; simpl in *.
    + inv H0.
      eapply Step_meth_InCall_InDef_InExec; eauto.
    + eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_InCall_not_InExec_not_InDef m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l ->
    InCall f l ->
    ~ InExec f l ->
    ~ In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  intro.
  eapply Trace_meth_InCall_InDef_InExec in H3; eauto.
Qed.

Lemma InCall_dec: forall x l, InCall x l \/ ~ InCall x l.
Proof.
  unfold InCall; intros.
  induction l; simpl.
  - right.
    intro.
    dest; auto.
  - destruct IHl; dest.
    + left.
      exists x0.
      split; tauto.
    + pose proof (in_dec MethT_dec x (snd (snd a))).
      destruct H0.
      * left; exists a; tauto.
      * right; intro.
        dest.
        destruct H0; subst.
        -- auto.
        -- firstorder fail.
Qed.

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

Section ModularSubstition.
  Variable a b a' b': Mod.
  Variable DisjRegs: DisjKey (getAllRegisters a) (getAllRegisters b).
  Variable DisjRules: DisjKey (getAllRules a) (getAllRules b).
  Variable DisjMeths: DisjKey (getAllMethods a) (getAllMethods b).
  Variable DisjRegs': DisjKey (getAllRegisters a') (getAllRegisters b').
  Variable DisjMeths': DisjKey (getAllMethods a') (getAllMethods b').
  Variable SameList_a: forall x, (In x (map fst (getAllMethods a)) /\
                                  ~ In x (getHidden a)) <->
                                 (In x (map fst (getAllMethods a')) /\
                                  ~ In x (getHidden a')).
  Variable Subset_a: forall x, In x (map fst (getAllMethods a')) ->
                               In x (map fst (getAllMethods a)).
  Variable SameList_b: forall x, (In x (map fst (getAllMethods b)) /\
                                  ~ In x (getHidden b)) <->
                                 (In x (map fst (getAllMethods b')) /\
                                  ~ In x (getHidden b')).
  Variable Subset_b: forall x, In x (map fst (getAllMethods b')) ->
                               In x (map fst (getAllMethods b)).

  Lemma ModularSubstition: TraceInclusion a a' ->
                           TraceInclusion b b' ->
                           TraceInclusion (ConcatMod a b) (ConcatMod a' b').
  Proof.
    unfold TraceInclusion in *; intros.
    pose proof (SplitTrace DisjRegs DisjRules DisjMeths H1); dest.
    specialize (@H _ _ H2).
    specialize (@H0 _ _ H3).
    dest.
    exists (x1 ++ x).
    exists (map (fun x => fst x ++ snd x) (zip x2 x0)).
    pose proof H9 as sth1.
    pose proof H7 as sth2.
    rewrite map_length in H9, H7.
    rewrite H9 in H7.
    rewrite mapProp_nthProp in H5.
    repeat split.
    - apply JoinTrace; auto; unfold nthProp, nthProp2 in *; intros; auto.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in H10, H8;
        case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        case_eq (nth_error ls1 i);
        intros;
        try congruence; auto;
          [rewrite H11, H12, H13 in *; dest|
           solve [exfalso; apply (nth_error_len _ _ _ H11 H13 H9)]].
      Opaque MatchingExecCalls.
      repeat split; intros.
      Transparent MatchingExecCalls.
      + unfold MatchingExecCalls in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (DisjMeths (fst f));
          try specialize (DisjMeths' (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (Subset_b H25).
        destruct (InExec_dec f l1); [pose proof (Trace_meth_InExec H _ _ H13 i0) as sth; clear - DisjMeths' sth H25; firstorder fail|].
        pose proof (proj2 H21 (conj n H24)); dest.
        specialize (H5 H27 Subset_b); dest.
        clear - H28 H27 H16 H8 SameList_b H5 Subset_b; firstorder fail.
      + unfold MatchingExecCalls in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (DisjMeths (fst f));
          try specialize (DisjMeths' (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (Subset_a H25).
        destruct (InExec_dec f l0); [pose proof (Trace_meth_InExec H0 _ _ H12 i0) as sth; clear - DisjMeths' sth H25; firstorder fail|].
        pose proof (proj2 H18 (conj n H24)); dest.
        specialize (H14 H27 Subset_a); dest.
        clear - H28 H27 H16 H10 SameList_a H14 Subset_a; firstorder fail.
      + destruct x3, x4, p, p0, r1, r2; simpl; auto.
        pose proof (in_map (fun x => fst (snd x)) _ _ H24) as sth3.
        pose proof (in_map (fun x => fst (snd x)) _ _ H25) as sth4.
        simpl in *.
        assert (sth5: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id a l))) by
            (clear - H23 sth3; firstorder fail).
        assert (sth6: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id b l))) by
            (clear - H20 sth4; firstorder fail).
        dest.
        rewrite in_map_iff in *; dest.
        specialize (H15 _ _ H29 H28).
        rewrite H27, H26 in *.
        assumption.
      + destruct (InExec_dec x3 l1), (InExec_dec x3 l0).
        * pose proof (Trace_meth_InExec H _ _ H13 i0) as sth3.
          pose proof (Trace_meth_InExec H0 _ _ H12 i1) as sth4.
          clear - DisjMeths' sth3 sth4.
          firstorder fail.
        * pose proof (Trace_meth_InExec H _ _ H13 i0) as i0'.
          pose proof (Trace_meth_InCall_not_InExec_not_InDef H0 _ H12 H25 n) as n'.
          pose proof (proj2 (H18 _) (conj n H25)); dest.
          unfold MatchingExecCalls in *.
          pose proof (proj2 (H22 _) (or_introl (conj i0 H24))).
          destruct H28; dest.
          -- eapply H16; eauto.
          -- specialize (Subset_a _ i0').
             specialize (H14 _ H27 Subset_a); tauto.
        * pose proof (Trace_meth_InExec H0 _ _ H12 i0) as i0'.
          pose proof (Trace_meth_InCall_not_InExec_not_InDef H _ H13 H24 n) as n'.
          pose proof (proj2 (H21 _) (conj n H24)); dest.
          unfold MatchingExecCalls in *.
          pose proof (proj2 (H19 _) (or_introl (conj i0 H25))).
          destruct H28; dest.
          -- eapply H16; eauto.
          -- specialize (Subset_b _ i0').
             specialize (H5 _ H27 Subset_b); tauto.
        * pose proof (proj2 (H21 _) (conj n H24)); dest.
          pose proof (proj2 (H18 _) (conj n0 H25)); dest.
          clear - H27 H29 H16. specialize (H16 x3); tauto.
    - rewrite map_length.
      rewrite length_zip; congruence.
    - unfold nthProp, nthProp2 in *; intros.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in *.
      simpl in *.
      case_eq (nth_error ls1 i); intros; rewrite H11 in *; auto.
      setoid_rewrite (nth_error_zip (fun x3 => fst x3 ++ snd x3) _ i x2 x0); auto.
      case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        intros; auto; rewrite H12, H13 in *; simpl in *; intros.
      split; intros.
      + rewrite ?InExec_app_iff in *.
        rewrite ?InCall_app_iff in *.
        rewrite ?Demorgans in *.
        split; intros; dest.
        * rewrite H19 in H14, H15; clear H19.
          rewrite InExec_app_iff, InCall_app_iff in *.
          assert (~ InCall f (filterExecs id a l) /\
                  ~ InCall f (filterExecs id b l)) by (clear - H15; tauto).
          clear H15; dest.
          specialize (H10 f); specialize (H8 f).
          split; [tauto|].
          intro.
          destruct H14, H26; try tauto.
          -- destruct (InExec_dec f l0).
             ++ pose proof (Trace_meth_InExec H0 _ _ H12 i0) as sth.
                pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H14)
                  as sth3.
                specialize (Subset_b _ sth).
                clear - sth3 Subset_b DisjMeths; firstorder fail.
             ++ pose proof (proj2 (H20 _ ) (conj n H26)); dest.
                tauto.
          -- destruct (InExec_dec f l1).
             ++ pose proof (Trace_meth_InExec H _ _ H13 i0) as sth.
                pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H14)
                  as sth3.
                specialize (Subset_a _ sth).
                clear - sth3 Subset_a DisjMeths; firstorder fail.
             ++ pose proof (proj2 (H23 _ ) (conj n H26)); dest.
                tauto.
        * assert (~ InCall f l1 /\ ~ InCall f l0) by (clear - H15; tauto).
          clear H15; dest.
          rewrite H19.
          rewrite InExec_app_iff.
          rewrite InCall_app_iff.
          specialize (H10 f); specialize (H8 f).
          split; [tauto|].
          intro.
          destruct H14, H27; try tauto.
          -- destruct (InExec_dec f (filterExecs id b l)).
             ++ pose proof (Trace_meth_InExec H _ _ H13 H14) as sth.
                pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) i0)
                  as sth3.
                specialize (Subset_a _ sth).
                clear - sth3 Subset_a DisjMeths; firstorder fail.
             ++ pose proof (proj1 (H20 _) (conj n H27)); dest.
                tauto.
          -- destruct (InExec_dec f (filterExecs id a l)).
             ++ pose proof (Trace_meth_InExec H0 _ _ H12 H14) as sth.
                pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) i0)
                  as sth3.
                specialize (Subset_b _ sth).
                clear - sth3 Subset_b DisjMeths; firstorder fail.
             ++ pose proof (proj1 (H23 _) (conj n H27)); dest.
                tauto.
      + split; intros.
        * rewrite ?InExec_app_iff in *.
          rewrite ?InCall_app_iff in *.
          rewrite ?Demorgans in *.
          split; intros; dest.
          -- rewrite H19 in H14, H15; rewrite ?InExec_app_iff, ?InCall_app_iff,
                                      ?Demorgans in *.
             assert (~ InExec f (filterExecs id a l) /\
                     ~ InExec f (filterExecs id b l)) by (clear - H14; firstorder fail).
             clear H14; dest.
             specialize (H20 f); specialize (H23 f).
             split; [|tauto].
             intro.
             destruct H15, H27; try tauto.
             ++ unfold MatchingExecCalls in *.
                pose proof (Trace_meth_InExec H0 _ _ H12 H27) as sth.
                specialize (Subset_b _ sth).
                specialize (H5 f).
                tauto.
             ++ unfold MatchingExecCalls in *.
                pose proof (Trace_meth_InExec H _ _ H13 H27) as sth.
                specialize (Subset_a _ sth).
                specialize (H16 f).
                tauto.
          -- assert (~ InExec f l1 /\ ~ InExec f l0) by (clear - H14; firstorder fail).
             clear H14; dest.
             rewrite H19 .
             rewrite InExec_app_iff, InCall_app_iff.
             specialize (H20 f); specialize (H23 f).
             split; [|tauto].
             intro.
             destruct H15, H27; try tauto.
             ++ unfold MatchingExecCalls in *.
                destruct (InCall_dec f (filterExecs id b l)).
                ** pose proof (proj2 H23 (conj H14 H15)); dest.
                   eapply H18; eauto.
                ** pose proof (proj1 (H8 _) (conj H27 H28)).
                   tauto.
             ++ unfold MatchingExecCalls in *.
                destruct (InCall_dec f (filterExecs id a l)).
                ** pose proof (proj2 H20 (conj H26 H15)); dest.
                   eapply H18; eauto.
                ** pose proof (proj1 (H10 _) (conj H27 H28)).
                   tauto.
        * split; intros;
            unfold MatchingExecCalls in *; dest;
              repeat match goal with
                     | H: forall x: MethT, _ |- _ => specialize (H f)
                     end; try (specialize (DisjMeths (fst f)); specialize (SameList_a (fst f)); specialize (Subset_a (fst f));
                specialize (SameList_b (fst f)); specialize (Subset_b (fst f))).
          -- split; intros; dest.
             ++ rewrite H17 in H24.
                rewrite InExec_app_iff, InCall_app_iff in *.
                dest.
                destruct H24; dest.
                ** destruct H24, H25.
                   --- assert (~ InCall f (filterExecs id b l)) by tauto.
                       assert (~ InExec f (filterExecs id b l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H24).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H27).
                         tauto.
                       }
                       pose proof (proj1 H19 (or_intror (conj H27 H26))).
                       destruct H28; [left; clear - H28; tauto| dest].
                       pose proof (proj1 H22 (or_introl (conj H24 H25))).
                       destruct H30; [left; clear - H30; tauto| dest].
                       clear - H28 H29 H30 H31; tauto.
                   --- assert (~ InCall f (filterExecs id a l)) by tauto.
                       assert (~ InExec f (filterExecs id b l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H24).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H27).
                         tauto.
                       }
                       clear - H24 H25 H26 H27 H10 H21 H8 H18; tauto.
                   --- assert (~ InCall f (filterExecs id b l)) by tauto.
                       assert (~ InExec f (filterExecs id a l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H27).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H24).
                         tauto.
                       }
                       clear - H24 H25 H26 H27 H10 H21 H8 H18; tauto.
                   --- assert (~ InCall f (filterExecs id a l)) by tauto.
                       assert (~ InExec f (filterExecs id a l)).
                       { intro.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) H27).
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) H24).
                         tauto.
                       }
                       pose proof (proj1 H22 (or_intror (conj H27 H26))).
                       destruct H28; [left; clear - H28; tauto| dest].
                       pose proof (proj1 H19 (or_introl (conj H24 H25))).
                       destruct H30; [left; clear - H30; tauto| dest].
                       clear - H28 H29 H30 H31; tauto.
                ** assert (~ InExec f (filterExecs id a l) /\ ~ InExec f (filterExecs id b l)) by (clear - H24; tauto); clear H24.
                   assert (~ InCall f (filterExecs id a l) /\ ~ InCall f (filterExecs id b l)) by (clear - H25; tauto); clear H25.
                   dest.
                   pose proof (proj1 H22 (or_intror (conj H26 H24))).
                   pose proof (proj1 H19 (or_intror (conj H27 H25))).
                   destruct H28, H29; clear - H28 H29; try tauto.
             ++ rewrite H17.
                rewrite InExec_app_iff, InCall_app_iff in *.
                dest.
                specialize (DisjMeths' (fst f)).
                destruct H24; dest.
                ** destruct H24, H25.
                   --- pose proof (proj2 H22 (or_introl (conj H24 H25))).
                       destruct H26; [clear - H26; tauto| dest].
                       pose proof (Trace_meth_InExec H _ _ H13 H24).
                       specialize (Subset_a H28).
                       assert (~ In (fst f) (map fst (getAllMethods b))) by (clear - Subset_a DisjMeths; tauto).
                       assert (~ InExec f (filterExecs id b l)).
                       { intro Help.
                         pose proof (Trace_meth_InExec H3 _ _ (map_nth_error _ i ls1 H11) Help).
                         tauto.
                       }
                       destruct (InCall_dec f (filterExecs id b l)); [| clear - H26 H27 H30 H31; tauto].
                       specialize (H14 H31 Subset_a); dest; tauto.
                   --- destruct (InCall_dec f l1), (InExec_dec f l0).
                       +++ pose proof (Trace_meth_InExec H _ _ H13 H24).
                           pose proof (Trace_meth_InExec H0 _ _ H12 i0).
                           clear - DisjMeths' H27 H28; tauto.
                       +++ pose proof (proj2 H18 (conj n H25)); dest.
                           pose proof (proj2 H22 (or_introl (conj H24 H26))).
                           destruct H29; [clear - H16 H29; tauto| dest].
                           pose proof (Trace_meth_InExec H _ _ H13 H24).
                           specialize (Subset_a H31).
                           specialize (H14 H28 Subset_a); clear - H14 H29; tauto.
                       +++ pose proof (Trace_meth_InExec H0 _ _ H12 i0).
                           specialize (Subset_b H27).
                           pose proof (Trace_meth_InExec H _ _ H13 H24).
                           specialize (Subset_a H28).
                           clear - Subset_a Subset_b DisjMeths; tauto.
                       +++ pose proof (proj2 H10 (conj H24 H26)); dest.
                           pose proof (proj2 H18 (conj n H25)); dest.
                           clear - H27 H30; tauto.
                   --- destruct (InCall_dec f l0), (InExec_dec f l1).
                       +++ pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           pose proof (Trace_meth_InExec H _ _ H13 i0).
                           clear - DisjMeths' H27 H28; tauto.
                       +++ pose proof (proj2 H21 (conj n H25)); dest.
                           pose proof (proj2 H19 (or_introl (conj H24 H26))).
                           destruct H29; [clear - H16 H29; tauto| dest].
                           pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           specialize (Subset_b H31).
                           specialize (H5 H28 Subset_b); clear - H5 H29; tauto.
                       +++ pose proof (Trace_meth_InExec H _ _ H13 i0).
                           specialize (Subset_a H27).
                           pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                           specialize (Subset_b H28).
                           clear - Subset_a Subset_b DisjMeths; tauto.
                       +++ pose proof (proj2 H8 (conj H24 H26)); dest.
                           pose proof (proj2 H21 (conj n H25)); dest.
                           clear - H27 H30; tauto.
                   --- pose proof (proj2 H19 (or_introl (conj H24 H25))).
                       destruct H26; [clear - H26; tauto| dest].
                       pose proof (Trace_meth_InExec H0 _ _ H12 H24).
                       specialize (Subset_b H28).
                       assert (~ In (fst f) (map fst (getAllMethods a))) by (clear - Subset_b DisjMeths; tauto).
                       assert (~ InExec f (filterExecs id a l)).
                       { intro Help.
                         pose proof (Trace_meth_InExec H2 _ _ (map_nth_error _ i ls1 H11) Help).
                         tauto.
                       }
                       destruct (InCall_dec f (filterExecs id a l)); [| clear - H26 H27 H30 H31; tauto].
                       specialize (H5 H31 Subset_b); dest; tauto.
                ** assert (~ InExec f l1 /\ ~ InExec f l0) by (clear - H24; tauto); dest.
                   assert (~ InCall f l1 /\ ~ InCall f l0) by (clear - H25; tauto); dest.
                   clear - H22 H19 H26 H27 H28 H29.
                   pose proof (proj2 H22 (or_intror (conj H26 H28))).
                   pose proof (proj2 H19 (or_intror (conj H27 H29))).
                   clear H22 H19; tauto.
          -- intros; dest; rewrite ?map_app, ?in_app_iff in *.
             rewrite H18.
             rewrite map_app.
             setoid_rewrite in_app_iff.
             clear - H14 H21 H24.
             firstorder fail.
  Qed.
End ModularSubstition.












    


Lemma TraceInclusion_refl: forall m, TraceInclusion m m.
Proof.
  unfold TraceInclusion; intros.
  exists o1, ls1.
  repeat split; auto.
  unfold nthProp2; intros.
  destruct (nth_error ls1 i); auto.
  repeat split; intros; tauto.
Qed.

Lemma TraceInclusion_trans: forall m1 m2 m3, TraceInclusion m1 m2 ->
                                             TraceInclusion m2 m3 ->
                                             TraceInclusion m1 m3.
Proof.
  unfold TraceInclusion; intros.
  specialize (H _ _ H1); dest.
  specialize (H0 _ _ H); dest.
  exists x1, x2.
  repeat split; auto.
  - congruence.
  - unfold nthProp2 in *; intros.
    specialize (H3 i); specialize (H5 i).
    case_eq (nth_error ls1 i);
      case_eq (nth_error x0 i);
      case_eq (nth_error x2 i);
      intros; auto.
    + rewrite H6, H7, H8 in *.
      dest.
      split; [|split; [|split]]; intros;
        repeat match goal with
               | H: forall x: MethT, _ |- _ => specialize (H f)
               end.
      * tauto.
      * tauto.
      * rewrite <- H13 in H10.
        assumption.
      * tauto.
    + pose proof (nth_error_len _ _ _ H7 H6 H4); tauto.
Qed.








Lemma UpdRegs_nil_upd: forall o, NoDup (map fst o) -> forall o', UpdRegs [] o o' -> o = o'.
Proof.
  unfold UpdRegs.
  intros.
  dest.
  simpl in *.
  assert (sth: forall s v, In (s, v) o' -> In (s, v) o).
  { intros.
    specialize (H1 s v H2).
    destruct H1; dest; try auto.
    tauto.
  }
  clear H1.
  generalize o' H H0 sth.
  clear o' H H0 sth.
  induction o; destruct o'; simpl; auto; intros.
  - discriminate.
  - discriminate.
  - inv H0.
    inv H.
    specialize (IHo _ H6 H4).
    destruct p, a; simpl in *; subst; auto; repeat f_equal; auto.
    + specialize (sth s s0 (or_introl eq_refl)).
      destruct sth.
      * inv H; subst; auto.
      * apply (in_map fst) in H; simpl in *; tauto.
    + eapply IHo; intros.
      specialize (sth _ _ (or_intror H)).
      destruct sth; [|auto].
      inv H0; subst.
      apply (f_equal (map fst)) in H4.
      rewrite ?map_map in *; simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H4; try tauto.
      apply (in_map fst) in H; simpl in *; congruence.
Qed.

Lemma Trace_NoDup m o l:
  Trace m o l ->
  NoDup (map fst (getAllRegisters m)) ->
  NoDup (map fst o).
Proof.
  induction 1; subst.
  - rewrite map_map; simpl.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst); intros; tauto.
  - unfold UpdRegs in *; intros; dest.
    apply (f_equal (map fst)) in H1.
    rewrite ?map_map in *; simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H1; try tauto.
    rewrite H1 in *; eapply IHTrace; eauto.
Qed.

Lemma Trace_sameRegs m o l:
  Trace m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; subst; auto.
  - rewrite map_map; simpl; auto.
  - unfold UpdRegs in *; dest. congruence.
Qed.

Lemma Step_empty m:
  forall o,
    getKindAttr o = getKindAttr (getAllRegisters m) ->
    Step m o [].
Proof.
  induction m; simpl; intros; auto.
  - constructor; auto.
    + constructor; auto.
    + unfold MatchingExecCalls; firstorder fail.
  - constructor 2.
    + eapply IHm; eauto.
    + intros.
      unfold InExec in *; simpl in *.
      tauto.
  - rewrite map_app in H.
    pose proof (list_split _ _ _ _ _ H).
    dest.
    specialize (IHm1 _ H1).
    specialize (IHm2 _ H2).
    constructor 3 with (o1 := x) (o2 := x0) (l1 := []) (l2 := []); auto.
    + unfold MatchingExecCalls; intros.
      unfold InCall in *; simpl in *; dest; tauto.
    + unfold MatchingExecCalls; intros.
      unfold InCall in *; simpl in *; dest; tauto.
    + intros.
      simpl in *; tauto.
    + intros.
      unfold InCall in *; simpl in *; dest; tauto.
Qed.

Lemma Trace_Step_empty m o l:
  Trace m o l ->
  Step m o [].
Proof.
  intros.
  apply Trace_sameRegs in H.
  apply Step_empty in H.
  auto.
Qed.

Section StepSimulation.
  Variable imp spec: Mod.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: simRel (map regInit (getAllRegisters imp)) (map regInit (getAllRegisters spec)).
  Variable NoDupRegs: NoDup (map fst (getAllRegisters imp)).
  
  Variable stepSimulationNonZero:
    forall oImp lImp oImp',
      Step imp oImp lImp ->
      lImp <> nil ->
      UpdRegs (map fst lImp) oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        exists lSpec oSpec',
          Step spec oSpec lSpec /\
          UpdRegs (map fst lSpec) oSpec oSpec' /\
          simRel oImp' oSpec' /\
          (forall f : MethT, InExec f lImp /\ ~ InCall f lImp <-> InExec f lSpec /\ ~ InCall f lSpec) /\
          (forall f : MethT, ~ InExec f lImp /\ InCall f lImp <-> ~ InExec f lSpec /\ InCall f lSpec) /\
          (forall f : MethT, InExec f lImp /\ InCall f lImp \/ ~ InExec f lImp /\ ~ InCall f lImp <->
                             InExec f lSpec /\ InCall f lSpec \/ ~ InExec f lSpec /\ ~ InCall f lSpec) /\
          ((exists rle : string, In (Rle rle) (map getRleOrMeth lSpec)) -> (exists rle : string, In (Rle rle) (map getRleOrMeth lImp))).

  Lemma StepDecomposition':
    forall (oImp : RegsT) (lsImp : list (list FullLabel)),
      Trace imp oImp lsImp ->
      exists (oSpec : RegsT) (lsSpec : list (list FullLabel)),
        Trace spec oSpec lsSpec /\
        Datatypes.length lsImp = Datatypes.length lsSpec /\
        nthProp2
          (fun l1 l2 : list FullLabel =>
             (forall f : MethT, InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ ~ InCall f l2) /\
             (forall f : MethT, ~ InExec f l1 /\ InCall f l1 <-> ~ InExec f l2 /\ InCall f l2) /\
             (forall f : MethT, InExec f l1 /\ InCall f l1 \/ ~ InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ InCall f l2 \/ ~ InExec f l2 /\ ~ InCall f l2) /\
             ((exists rle : string, In (Rle rle) (map getRleOrMeth l2)) -> (exists rle : string, In (Rle rle) (map getRleOrMeth l1)))
          ) lsImp lsSpec /\
        simRel oImp oSpec.
  Proof.
    induction 1; subst; simpl; auto; intros.
    - exists (map regInit (getAllRegisters spec)), []; repeat split; auto.
      + econstructor 1; eauto.
      + unfold nthProp2; intros.
        destruct (nth_error [] i); auto.
        repeat split; intros; tauto.
    - dest.
      destruct l.
      + simpl in *.
        exists x, ([] :: x0); repeat split; simpl in *; auto.
        * constructor 2 with (o := x) (ls := x0) (l := []); simpl; auto.
          -- eapply Trace_Step_empty; eauto.
          -- clear.
             unfold UpdRegs; split; intros; try tauto.
             right; split; try intro; dest; auto.
        * rewrite nthProp2_cons; split; simpl; auto; repeat split; dest; simpl in *; try tauto.
          constructor.
        * pose proof (Trace_NoDup H NoDupRegs) as sth.
          pose proof (UpdRegs_nil_upd sth HUpdRegs); subst; auto.
      + specialize (stepSimulationNonZero HStep ltac:(intro; discriminate) HUpdRegs H3).
        destruct stepSimulationNonZero as [lSpec [oSpec' [stepSpec [updSpec [sim lSpecProp]]]]].
        exists oSpec', (lSpec :: x0); repeat split; simpl in *; auto.
        * econstructor 2; eauto.
        * simpl.
          rewrite nthProp2_cons; split; auto.
  Qed.

  Lemma StepDecomposition:
    TraceInclusion imp spec.
  Proof.
    unfold TraceInclusion; intros.
    eapply StepDecomposition' in H.
    dest.
    exists x, x0.
    repeat split; auto.
  Qed.
End StepSimulation.

Lemma NoMeths_Substeps m o ls:
  getMethods m = [] ->
  Substeps m o ls ->
  ls = nil \/ exists u rl cs, ls = (u, (Rle rl, cs)) :: nil.
Proof.
  intros nilMeths substeps.
  induction substeps; intros; auto; subst.
  - destruct IHsubsteps; subst.
    + right.
      repeat eexists; eauto.
    + dest; subst.
      specialize (HNoRle _ (or_introl eq_refl)); simpl in *.
      tauto.
  - rewrite nilMeths in *.
    simpl in *.
    tauto.
Qed.
    







Section DecompositionZero.
  Variable imp spec: BaseModule.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: simRel (map regInit (getRegisters imp)) (map regInit (getRegisters spec)).
  Variable NoDupRegs: NoDup (map fst (getRegisters imp)).

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp uImp rleImp csImp oImp',
      Substeps imp oImp [(uImp, (Rle rleImp, csImp))] ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((getKindAttr oSpec = getKindAttr (getRegisters spec) /\ simRel oImp' oSpec /\ csImp = []) \/
         (exists uSpec rleSpec oSpec',
             Substeps spec oSpec [(uSpec, (Rle rleSpec, csImp))] /\
             UpdRegs [uSpec] oSpec oSpec' /\
             simRel oImp' oSpec')).

  Lemma decompositionZero:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    apply StepDecomposition with (simRel := simRel); auto; intros.
    inv H.
    pose proof HSubsteps as sth.
    inv HSubsteps; simpl in *.
    - tauto.
    - pose proof (NoMeths_Substeps NoMeths HSubstep).
      destruct H; [subst | dest; subst].
      + simpl in *.
        specialize (@simulation _ _ _ _ oImp' sth H1 _ H2).
        destruct simulation; dest; subst.
        * exists nil, oSpec.
          repeat split; auto.
          constructor; auto.
          -- constructor; auto.
          -- clear; firstorder fail.
          -- intros.
             right; split; try intro; dest; simpl in *; try tauto.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *.
             destruct H4; congruence.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *.
             destruct H4; congruence.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *; tauto.
          -- dest; unfold InExec in *; dest; try tauto; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- unfold InCall in *; clear - H4.
             dest.
             simpl in *.
             destruct H0; subst; simpl in *; tauto.
          -- intros.
             destruct H4; dest.
             ++ unfold InExec in H4; simpl in *.
                destruct H4; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec, InCall in *; simpl in *; tauto.
                ** unfold InExec, InCall in *; simpl in *; dest; tauto.
          -- intros.
             destruct H4; dest.
             ++ unfold InExec in H4; simpl in *; tauto.
             ++ right.
                split; intro.
                ** unfold InExec, InCall in *; simpl in *. destruct H6; [discriminate | tauto].
                ** unfold InExec, InCall in *; simpl in *; dest; destruct H6; subst; simpl in *; tauto.
          -- intros.
             dest.
             simpl in *.
             tauto.
        * exists [(x, (Rle x0, cs))], x1.
          repeat split; auto.
          -- constructor; auto.
             unfold MatchingExecCalls; intros.
             simpl in *.
             rewrite NoMethsSpec in *; simpl in *; tauto.
          -- unfold UpdRegs in *; dest.
             auto.
          -- intros.
             unfold UpdRegs in *; dest.
             simpl in *.
             eapply H6; eauto.
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- dest.
             unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
          -- intro.
             dest.
             unfold InExec in *; simpl in *; destruct H6; [discriminate | tauto].
          -- dest.
             unfold InCall in *; simpl in *; destruct H6; dest.
             eexists.
             split; [apply (or_introl eq_refl)|].
             simpl.
             destruct H6; subst; simpl in *; auto.
             tauto.
          -- intro.
             dest.
             unfold InExec in *; simpl in *; destruct H6; [discriminate | tauto].
          -- dest.
             unfold InCall in *; simpl in *; destruct H6; dest.
             eexists.
             split; [apply (or_introl eq_refl)|].
             simpl.
             destruct H6; subst; simpl in *; auto.
             tauto.
          -- intros; dest.
             destruct H5; dest.
             ++ dest.
                unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec in *; simpl in *; destruct H7; [discriminate | tauto].
                ** unfold InCall in *; dest; simpl in *.
                   assert (sth2: exists x, ((u, (Rle rn, cs)) = x \/ False) /\ In f (snd (snd x))).
                   { eexists.
                     split.
                     - left; reflexivity.
                     - simpl.
                       destruct H7; [|tauto].
                       subst; simpl in *; auto.
                   }
                   tauto.
          -- intros; dest.
             destruct H5; dest.
             ++ dest.
                unfold InExec in *; simpl in *; destruct H5; [discriminate | tauto].
             ++ right.
                split; intro.
                ** unfold InExec in *; simpl in *; destruct H7; [discriminate | tauto].
                ** unfold InCall in *; dest; simpl in *.
                   assert (sth2: exists x1, ((x, (Rle x0, cs)) = x1 \/ False) /\ In f (snd (snd x1))).
                   { eexists.
                     split.
                     - left; reflexivity.
                     - simpl.
                       destruct H7; [|tauto].
                       subst; simpl in *; auto.
                   }
                   tauto.
          -- intros.
             simpl in *.
             dest.
             destruct H5; [|tauto].
             exists rn.
             left; auto.
      + specialize (HNoRle _ (or_introl eq_refl)); simpl in *; tauto.
    - rewrite NoMeths in *.
      simpl in *; tauto.
  Qed.
End DecompositionZero.


Definition StepSubstitute m o l :=
  Substeps (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) o l /\
  MatchingExecCalls l l (Base (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m))) /\
  (forall s v, In s (map fst (getAllMethods m)) -> In s (getHidden m) -> InExec (s, v) l -> InCall (s, v) l).

Section WfBaseMod.
  Variable m: BaseModule.
  
  Inductive WfActionT: forall lretT, ActionT type lretT -> Prop :=
  | WfMCall meth s e lretT c: forall v, WfActionT (c v) -> @WfActionT lretT (MCall meth s e c)
  | WfLetExpr k (e: Expr type k) lretT c: forall v, WfActionT (c v) -> @WfActionT lretT (LetExpr e c)
  | WfLetAction k (a: ActionT type k) lretT c: forall v, WfActionT (c v) -> @WfActionT lretT (LetAction a c)
  | WfReadNondet k lretT c: forall v, WfActionT (c v) -> @WfActionT lretT (ReadNondet k c)
  | WfReadReg r k lretT c: forall v, WfActionT (c v) -> In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (ReadReg r k c)
  | WfWriteReg r k (e: Expr type k) lretT c: In (r, k) (getKindAttr (getRegisters m)) -> @WfActionT lretT (WriteReg r e c)
  | WfIfElse p k (atrue: ActionT type k) afalse lretT c: forall v, WfActionT (c v) -> WfActionT atrue -> WfActionT afalse -> @WfActionT lretT (IfElse p atrue afalse c)
  | WfAssertion (e: Expr type (SyntaxKind Bool)) lretT c: WfActionT c -> @WfActionT lretT (Assertion e c)
  | WfSys ls lretT c: WfActionT c -> @WfActionT lretT (Sys ls c)
  | WfReturn lretT e: @WfActionT lretT (Return e).

  Definition WfBaseMod :=
    (forall rule, In rule (getRules m) -> WfActionT (snd rule type)) /\
    (forall meth, In meth (getMethods m) -> forall v, WfActionT (projT2 (snd meth) type v)).
End WfBaseMod.

Inductive WfMod: Mod -> Prop :=
| BaseWf m (WfBaseModule: WfBaseMod m): WfMod (Base m)
| HideMethWf m s (HHideWf: In s (map fst (getAllMethods m))) (HWf: WfMod m): WfMod (HideMeth m s)
| ConcatModWf m1 m2 (HDisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2))
              (HDisjRules: DisjKey (getAllRules m1) (getAllRules m2))
              (HDisjMeths: DisjKey (getAllMethods m1) (getAllMethods m2))
              (HWf1: WfMod m1) (HWf2: WfMod m2): WfMod (ConcatMod m1 m2).

Definition getFlat m := BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m).

Fixpoint createHide (m: BaseModule) (hides: list string) :=
  match hides with
  | nil => Base m
  | x :: xs => HideMeth (createHide m xs) x
  end.

Definition flatten m := createHide (getFlat m) (getHidden m).

Lemma createHide_hides: forall hides m, getHidden (createHide m hides) = hides.
Proof.
  induction hides; simpl; auto; intros; f_equal; auto.
Qed.

Lemma createHide_Regs: forall m l, getAllRegisters (createHide m l) = getRegisters m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Rules: forall m l, getAllRules (createHide m l) = getRules m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Meths: forall m l, getAllMethods (createHide m l) = getMethods m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma getFlat_Hide m s:
  getFlat (HideMeth m s) = getFlat m.
Proof.
  unfold getFlat; auto.
Qed.

Lemma WfMod_Hidden m:
  WfMod m ->
  forall s, In s (getHidden m) -> In s (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; auto; intros.
  - tauto.
  - destruct H0; subst; auto.
  - rewrite map_app, in_app_iff in *.
    specialize (IHWfMod1 s); specialize (IHWfMod2 s); tauto.
Qed.

Lemma SemActionUpdSub o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  SubList (getKindAttr upds) (getKindAttr o).
Proof.
  induction 1; auto;
    unfold SubList in *; intros;
      rewrite ?in_app_iff in *.
  - rewrite map_app, in_app_iff in *.
    destruct H1; firstorder fail.
  - subst; firstorder; simpl in *.
    subst.
    assumption.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst; simpl in *; intuition.
Qed.

Lemma SemActionExpandRegs o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  forall o', SubList reads o' ->
             SubList (getKindAttr upds) (getKindAttr o') ->
             @SemAction o' k a reads upds calls ret.
Proof.
  intros.
  induction H; try solve [econstructor; auto].
  - subst.
    specialize (IHSemAction H0).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_cons in H0; dest.
    specialize (IHSemAction H2 H1).
    econstructor; eauto.
  - subst.
    simpl in *.
    apply SubList_cons in H1; dest.
    specialize (IHSemAction H0 H2).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor 8; eauto.
Qed.

Lemma Substeps_combine m1 o1 l1:
  Substeps m1 o1 l1 ->
  forall m2 o2 l2  (DisjRegs: DisjKey (getRegisters m1) (getRegisters m2)) (DisjMeths: DisjKey (getMethods m1) (getMethods m2))
         (HOneRle: forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                         | Rle _, Rle _ => False
                                                         | _, _ => True
                                                         end)
         (HNoCall: forall x, InCall x l1 -> InCall x l2 -> False),
    Substeps m2 o2 l2 ->
    Substeps (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) (o1 ++ o2) (l1 ++ l2).
Proof.
  induction 1; intros.
  - induction H; simpl in *.
    + constructor 1; auto; simpl.
      rewrite ?map_app; congruence.
    + econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
    + econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False) by (clear - HNoCall0; firstorder fail).
    specialize (IHSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HNoRle; eauto| ].
      unfold SubList in *.
      specialize (HOneRle _ x (or_introl eq_refl) H1); simpl in *; assumption.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      unfold InCall.
      eexists; split; simpl; eauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False) by (clear - HNoCall0; firstorder fail).
    specialize (IHSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      unfold InCall.
      eexists; split; simpl; eauto.
Qed.

Lemma Substeps_flatten m o l:
  Substeps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l ->
  Substeps m o l.
Proof.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma Step_substitute' m o l:
  Step m o l -> forall (HWfMod: WfMod m), StepSubstitute m o l.
Proof.
  unfold StepSubstitute.
  induction 1; auto; simpl; intros; dest; unfold MatchingExecCalls in *; simpl in *.
  - repeat split.
    clear HMatching.
    induction HSubsteps.
    + econstructor 1; eauto.
    + econstructor 2; eauto.
    + econstructor 3; eauto.
    + simpl; tauto.
    + specialize (HMatching f); tauto.
    + intros; tauto.
  - inv HWfMod.
    specialize (IHStep HWf); dest.
    repeat split; auto.
    + specialize (H1 f); tauto.
    + intros.
      destruct H4; simpl in *; subst.
      -- apply HHidden; auto.
      -- apply H2; auto.
  - inv HWfMod.
    specialize (IHStep1 HWf1).
    specialize (IHStep2 HWf2).
    dest.
    subst; repeat split; auto.
    + pose proof (Substeps_combine H4 HDisjRegs HDisjMeths HNoRle HNoCall H1 (m2 := BaseMod (getAllRegisters m2) _ _)).
      simpl in *.
      assumption.
    + rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: MethT, _ |- _ => specialize (H f)
             end; tauto.
    + intros.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: string, _ |- _ => specialize (H s)
             | H: forall x: MethT, _ |- _ => specialize (H (s, v))
             end.
      specialize (H6 v); specialize (H3 v).
      destruct H7, H8, H9; try tauto.
      * pose proof (Step_meth_InExec H0 _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (Step_meth_InExec H _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
Qed.

Lemma StepSubstitute_flatten m o l (HWfMod: WfMod m):
  Step (flatten m) o l <-> StepSubstitute m o l.
Proof.
  unfold flatten, getFlat, StepSubstitute.
  split; intros.
  - induction (getHidden m).
    + simpl in *.
      inv H.
      split; [auto| split; [auto| intros; tauto]].
    + simpl in *.
      inv H.
      specialize (IHl0 HStep); dest.
      split; [auto| split; [auto| intros]].
      rewrite createHide_Meths in *; simpl in *.
      destruct H3; [subst |clear - H1 H2 H3 H4; firstorder fail].
      firstorder fail.
  - induction (getHidden m); simpl; auto; dest.
    + constructor; auto.
    + assert (sth: Step (createHide (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) l0) o l) by firstorder fail.
      assert (sth2: forall v, In a (map fst (getAllMethods m)) -> InExec (a, v) l -> InCall (a, v) l) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths.
      auto.
Qed.
    
Lemma Step_substitute m o l (HWfMod: WfMod m):
  Step m o l -> Step (flatten m) o l.
Proof.
  intros Stp.
  apply Step_substitute' in Stp; auto.
  rewrite StepSubstitute_flatten in *; auto.
Qed.

Definition concatFlat m1 m2 := BaseMod (getRegisters m1 ++ getRegisters m2)
                                       (getRules m1 ++ getRules m2)
                                       (getMethods m1 ++ getMethods m2).

Lemma splitRegs o m1 m2 (DisjRegisters: DisjKey (getRegisters m1) (getRegisters m2)):
  getKindAttr o = getKindAttr (getRegisters m1 ++ getRegisters m2) ->
  getKindAttr (filter (fun x : string * {x : FullKind & fullType type x} => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) = getKindAttr (getRegisters m1).
Proof.
  intros HRegs.
  rewrite map_app in *.
  pose proof (filter_map_simple (fun x: string * {x: FullKind & fullType type x} => (fst x, projT1 (snd x)))
                                (fun x => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) as sth.
  simpl in sth.
  setoid_rewrite <- sth.
  setoid_rewrite HRegs.
  rewrite filter_app.
  setoid_rewrite filter_false_list at 2.
  - rewrite filter_true_list at 1.
    + rewrite app_nil_r; auto.
    + intros.
      apply (in_map fst) in H.
      rewrite map_map in H.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
      destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
  - intros.
    apply (in_map fst) in H.
    rewrite map_map in H.
    simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
    destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
    specialize (DisjRegisters (fst a)).
    tauto.
Qed.


Section SplitSubsteps.
  Variable m1 m2: BaseModule.
  Variable DisjRegs: DisjKey (getRegisters m1) (getRegisters m2).
  Variable DisjRules: DisjKey (getRules m1) (getRules m2).
  Variable DisjMeths: DisjKey (getMethods m1) (getMethods m2).

  Variable WfMod1: WfBaseMod m1.
  Variable WfMod2: WfBaseMod m2.
  
  Lemma split_Substeps o l:
    Substeps (concatFlat m1 m2) o l ->
    MatchingExecCalls l l (Base (concatFlat m1 m2)) ->
    exists o1 o2 l1 l2,
      o = o1 ++ o2 /\
      l = l1 ++ l2 /\
      Substeps m1 o1 l1 /\
      Substeps m2 o2 l2 /\
      MatchingExecCalls l1 l1 (Base m1) /\
      MatchingExecCalls l2 l2 (Base m2) /\
      MatchingExecCalls l1 l2 (Base m2) /\
      MatchingExecCalls l2 l1 (Base m1) /\
      (forall x y : FullLabel,
          In x l1 -> In y l2 -> match fst (snd x) with
                                | Rle _ => match fst (snd y) with
                                           | Rle _ => False
                                           | Meth _ => True
                                           end
                                | Meth _ => True
                                end) /\
      (forall x : MethT, InCall x l1 -> InCall x l2 -> False).
  Proof.
    induction 1; simpl in *.
    - rewrite map_app in *.
      pose proof (list_split _ _ _ _ _ HRegs); dest.
      intros.
      exists x, x0, [], [].
      split; [auto|].
      split; [auto|].
      split; [constructor; auto|].
      split; [constructor; auto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; [unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto|].
      split; unfold MatchingExecCalls; intros; unfold InCall, InExec in *; simpl in *; dest; try tauto.
    - subst; intros.
      destruct WfMod1 as [r1 df1].
      destruct WfMod2 as [r2 df2].
      unfold WfBaseMod in *.
      destruct WfMod1 as [Rules1 Meths1].
      destruct WfMod2 as [Rules2 Meths2].
      admit.
    - admit.
  Admitted.
End SplitSubsteps.

Lemma substitute_Step' m (HWfMod: WfMod m):
  forall o l,
    StepSubstitute m o l -> Step m o l.
Proof.
  unfold StepSubstitute.
  induction m; simpl in *; intros; dest.
  - constructor; auto.
    eapply Substeps_flatten; eauto.
  - constructor 2.
    + apply IHm; inv HWfMod; firstorder fail.
    + clear - H1; firstorder fail.
  - inv HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    (* pose proof (@split_Substeps (getFlat m1) (getFlat m2) HDisjRegs HDisjRules HDisjMeths _ _ H H0); dest. *)
    (* (* apply split_Substeps in H; eauto. *) *)
    (* econstructor; eauto. *)
    admit.
Admitted.

Lemma substitute_Step m o l (HWfMod: WfMod m):
  Step (flatten m) o l -> Step m o l.
Proof.
  rewrite StepSubstitute_flatten in *; auto.
  apply substitute_Step'; auto.
Qed.

Section TraceSubstitute.
  Variable m: Mod.
  Variable WfMod_m: WfMod m.

  Lemma Trace_flatten_same: forall o l, Trace m o l <-> Trace (flatten m) o l.
  Proof.
    intros.
    split; induction 1; subst.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply Step_substitute in HStep; auto.
      econstructor 2; eauto.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply substitute_Step in HStep; auto.
      econstructor 2; eauto.
  Qed.

  Lemma Trace_Inclusion_flatten_r: TraceInclusion m (flatten m).
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same; auto.
  Qed.

  Lemma Trace_Inclusion_flatten_l: TraceInclusion (flatten m) m.
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same; auto.
  Qed.
End TraceSubstitute.
    
Lemma SameTrace m1 m2:
  (forall o1 l, Trace m1 o1 l -> exists o2, Trace m2 o2 l) ->
  TraceInclusion m1 m2.
Proof.
  unfold TraceInclusion; intros.
  pose proof (H _ _ H0); dest.
  exists x, ls1; auto.
  repeat split; auto.
  - unfold nthProp2; intros.
    destruct (nth_error ls1 i); auto.
    repeat split; tauto.
Qed.

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


Lemma WfMod_createHide l: forall m, WfMod (createHide m l) <-> SubList l (map fst (getMethods m)).
Proof.
  split.
  - induction l; simpl; auto; intros; unfold SubList; simpl; intros; try tauto.
    inv H.
    destruct H0; subst; rewrite createHide_Meths in *; firstorder fail.
  - unfold SubList; induction l; simpl; intros; try tauto.
    + constructor.
      admit.
    + assert (WfMod (createHide m l)) by firstorder fail.
      assert (In a (map fst (getMethods m))) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths.
      auto.
Admitted.

Lemma flatten_WfMod m: WfMod m -> WfMod (flatten m).
Proof.
  unfold flatten.
  induction 1; simpl; auto; intros.
  - constructor; auto.
    admit.
  - constructor; auto.
    rewrite createHide_Meths.
    auto.
  - unfold getFlat in *; simpl.
    rewrite WfMod_createHide in *; simpl in *.
    rewrite map_app.
    unfold SubList in *; intros.
    rewrite in_app_iff in *.
    specialize (IHWfMod1 x).
    specialize (IHWfMod2 x).
    tauto.
Admitted.




