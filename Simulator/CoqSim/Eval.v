Require Import Compare_dec List String Streams FinFun.
Import ListNotations Fin2Restrict.

Require Import Kami.AllNotations.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Import Kami.Simulator.CoqSim.HaskellTypes.Notations.

Section Eval.

Fixpoint eval_Kind(k : Kind) : Type :=
  match k with
  | Bool => bool
  | Bit n => BV n
  | Struct n ks fs => Tuple (fun i => eval_Kind (ks i))
  | Array n k' => Vector n (eval_Kind k')
  end.

Definition print_BF(bf : BitFormat){n} : BV n -> string :=
  match bf with
  | Binary => print_bv_bin
  | Decimal => print_bv_dec
  | Hex => print_bv_hex
  end.

Fixpoint print_Kind(k : Kind)(ff : FullFormat k) : eval_Kind k -> string :=
  match ff with
  | FBool n _ => fun x => space_pad n (if x then "1" else "0")
  | FBit n m bf => fun x => (*zero_pad m*) (print_BF bf x)
  | FStruct n fk fs ffs => fun x => ("{ " ++ String.concat "; " (v_to_list (vmap (fun '(str1,str2) => str1 ++ ":" ++ str2) (add_strings fs (tup_to_vec _ (fun i => print_Kind (ffs i)) x)))) ++ "; }")%string
  | FArray n k' ff' => fun x => ("[" ++ String.concat "; " (List.map (fun i => nat_decimal_string (f2n i) ++ "=" ++ print_Kind ff' (vector_index i x)) (getFins n)) ++ "; ]")%string
  end.

Fixpoint Kind_eq{k} : eval_Kind k -> eval_Kind k -> bool :=
  match k return eval_Kind k -> eval_Kind k -> bool with
  | Bool => Bool.eqb
  | Bit n => bv_eq
  | Struct n ks fs => TupEq (fun i => eval_Kind (ks i)) (fun i => @Kind_eq (ks i))
  | Array n k' => vector_eq (@Kind_eq k')
  end.

Definition eval_FK(k : FullKind) :=
  match k with
  | SyntaxKind k' => eval_Kind k'
  | NativeKind t _ => t
  end.

Fixpoint default_val(k : Kind) : eval_Kind k :=
  match k return eval_Kind k with
  | Bool => false
  | Bit n => nat_to_bv 0
  | Struct n ks fs => mkTup (fun i => eval_Kind (ks i)) (fun i => default_val (ks i))
  | Array n k' => make_vector (fun _ => default_val k')
  end.

Definition default_val_FK(k : FullKind) : eval_FK k :=
  match k with
  | SyntaxKind k' => default_val k'
  | NativeKind T t => t
  end.

Fixpoint rand_tuple{n} : forall ts : Fin.t n -> Type, (forall i, IO (ts i)) -> IO (Tuple ts) :=
  match n with
  | 0 => fun _ _ => ret tt
  | S m => fun ts mxs => (
      do x <- mxs Fin.F1;
      do xs <- rand_tuple (fun j => ts (Fin.FS j)) (fun j => mxs (Fin.FS j));
      ret (x,xs)
      )
  end.

Fixpoint rand_val(k : Kind) : IO (eval_Kind k) :=
  match k return IO (eval_Kind k) with
  | Bool => rand_bool
  | Bit n => rand_bv n
  | Struct n ks fs => rand_tuple (fun i => eval_Kind (ks i)) (fun i => rand_val (ks i))
  | Array n k' => rand_vector (rand_val k')
  end.

Fixpoint rand_val_FK(k : FullKind) : IO (eval_FK k) :=
  match k with
  | SyntaxKind k' => rand_val k'
  | NativeKind k' c => ret c
  end.

Definition eval_UniBool(op : UniBoolOp) : bool -> bool :=
  match op with
  | Neg => negb
  end.

Definition eval_CABool(op : CABoolOp) : list bool -> bool :=
  match op with
  | And => fun xs => fold_left andb xs true
  | Or => fun xs => fold_left orb xs false
  | Xor => fun xs => fold_left xorb xs false
  end.

Definition eval_UniBit{m n}(op : UniBitOp m n) : BV m -> BV n :=
  match op with
  | Inv n => bv_inv
  | TruncLsb lsb msb => bv_trunc_lsb
  | TruncMsb lsb msb => bv_trunc_msb
  | UAnd n => bv_uand
  | UOr n => bv_uor
  | UXor n => bv_uxor
  end.

Definition eval_BinBit{m n p}(op : BinBitOp m n p) : BV m -> BV n -> BV p :=
  match op with
  | Sub n => bv_sub
  | Div n => bv_div
  | Rem n => bv_rem
  | Sll n m => bv_sll
  | Srl n m => bv_srl
  | Sra n m => bv_sra
  | Concat msb lsb => bv_concat
  end.

Definition eval_CABit{n}(op : CABitOp) : list (BV n) -> BV n :=
  match op with
  | Add => bv_add
  | Mul => bv_mul
  | Band => bv_band
  | Bor => bv_bor
  | Bxor => bv_bxor
  end.

Definition eval_BinBitBool{m n}(op : BinBitBoolOp m n) : BV m -> BV n -> bool :=
  match op with
  | LessThan n => bv_lt
  end.

Fixpoint eval_ConstT{k}(e : ConstT k) : eval_Kind k :=
  match e with
  | ConstBool b => b
  | ConstBit n w => nat_to_bv (wordToNat w)
  | ConstStruct n ks ss es => mkTup (fun i => eval_Kind (ks i)) (fun i => eval_ConstT (es i))
  | ConstArray n k' es => make_vector (fun i => eval_ConstT (es i))
  end.

Definition eval_ConstFullT{k} (e : ConstFullT k) : eval_FK k :=
  match e with
  | SyntaxConst k' c' => eval_ConstT c'
  | NativeConst t c' => c'
  end.

Fixpoint eval_Expr{k}(e : Expr eval_Kind k) : eval_FK k :=
  match e with
  | Var _ v => v
  | Const _ v => eval_ConstT v
  | UniBool op e => eval_UniBool op (eval_Expr e)
  | CABool op es => eval_CABool op (List.map eval_Expr es)
  | UniBit m n op e => eval_UniBit op (eval_Expr e)
  | BinBit m n p op e1 e2 => eval_BinBit op (eval_Expr e1) (eval_Expr e2)
  | CABit n op es => eval_CABit op (List.map eval_Expr es)
  | BinBitBool m n op e1 e2 => eval_BinBitBool op (eval_Expr e1) (eval_Expr e2)
  | ITE _ p e1 e2 => eval_Expr (if eval_Expr p then e1 else e2)
  | Eq _ e1 e2 => Kind_eq (eval_Expr e1) (eval_Expr e2)
  | ReadStruct n ks ss e i => tup_index i _ (eval_Expr e)
  | BuildStruct n ks ss es => mkTup _ (fun i => eval_Expr (es i))
  | ReadArray n m k v i => match lt_dec (bv_to_nat (eval_Expr i)) n with
                           | left pf => vector_index (Fin.of_nat_lt pf) (eval_Expr v)
                           | right _ => eval_ConstT (getDefaultConst k)
                           end
  | ReadArrayConst n k v i => vector_index i (eval_Expr v)
  | BuildArray n k v => make_vector (fun i => eval_Expr (v i))
  end.

(* Fixpoint val_unpack'(k : Kind) : BV (size k) -> eval_Kind k.
Proof.
  induction k; simpl; intro e.
  (* Bool *)
  - exact (weqb e (nat_to_word 1)).
  (* BV *)
  - exact e.
  (* Tup *)
  - admit.
  - 
 *)


Definition val_unpack(k : Kind) : BV (size k) -> eval_Kind k :=
  fun w => eval_Expr (unpack _ (Const _ (ConstBit (natToWord _ (bv_to_nat w))))).

Definition eval_SysT(s : SysT eval_Kind) : IO unit :=
  match s with
  | DispString s => print s
  | DispExpr k e ff => print (print_Kind ff (eval_Expr e))
  | Finish => exit
  end.

Fixpoint eval_list_SysT(xs : list (SysT eval_Kind)) : IO unit :=
  match xs with
  | [] => ret tt
  | s::ys => (
      do _ <- eval_SysT s;
      eval_list_SysT ys
      )
  end.

End Eval.
