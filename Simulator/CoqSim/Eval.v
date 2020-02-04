Require Import Compare_dec List String Streams FinFun.
Import ListNotations Fin2Restrict.

Require Import Kami.AllNotations.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.SimTypes.
Require Import Kami.Simulator.CoqSim.HaskellTypes.

Section Eval.

Variable Word : nat -> Type.
Variable Vec : nat -> Type -> Type.
Variable M : Type -> Type.

Context `{IsWord Word}.
Context `{IsVector Vec}.
Context `{IOMonad Word Vec M}.

Fixpoint eval_Kind(k : Kind) : Type :=
  match k with
  | Bool => bool
  | Bit n => Word n
  | Struct n ks fs => Tuple (fun i => eval_Kind (ks i))
  | Array n k' => Vec n (eval_Kind k')
  end.

Definition print_BF(bf : BitFormat){n} : Word n -> string :=
  match bf with
  | Binary => print_word_bin
  | Decimal => print_word_dec
  | Hex => print_word_hex
  end.

Axiom cheat : forall {X},X.

Fixpoint print_Kind(k : Kind)(ff : FullFormat k) : eval_Kind k -> string :=
  match ff with
  | FBool n _ => fun x => space_pad n (if x then "1" else "0")
  | FBit n m bf => fun x => (*zero_pad m*) (print_BF bf x)
  | FStruct n fk fs ffs => fun x => ("{ " ++ String.concat "; " (v_to_list (vmap (fun '(str1,str2) => str1 ++ ":" ++ str2) (add_strings fs (tup_to_vec _ (fun i => print_Kind (ffs i)) x)))) ++ "; }")%string
  | FArray n k' ff' => fun x => ("[" ++ String.concat "; " (List.map (fun i => nat_decimal_string (f2n i) ++ "=" ++ print_Kind ff' (index i x)) (getFins n)) ++ "; ]")%string
  end.

Fixpoint Kind_eq{k} : eval_Kind k -> eval_Kind k -> bool :=
  match k return eval_Kind k -> eval_Kind k -> bool with
  | Bool => Bool.eqb
  | Bit n => weqb
  | Struct n ks fs => TupEq (fun i => eval_Kind (ks i)) (fun i => @Kind_eq (ks i))
  | Array n k' => vec_eq (@Kind_eq k')
  end.

Definition eval_FK(k : FullKind) :=
  match k with
  | SyntaxKind k' => eval_Kind k'
  | NativeKind t _ => t
  end.

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

Fixpoint default_val(k : Kind) : eval_Kind k :=
  match k return eval_Kind k with
  | Bool => false
  | Bit n => nat_to_word 0
  | Struct n ks fs => mkTup (fun i => eval_Kind (ks i)) (fun i => default_val (ks i))
  | Array n k' => make_vec (fun _ => default_val k')
  end.

Definition default_val_FK(k : FullKind) : eval_FK k :=
  match k with
  | SyntaxKind k' => default_val k'
  | NativeKind T t => t
  end.

Fixpoint rand_tuple{n} : forall ts : Fin.t n -> Type, (forall i, M (ts i)) -> M (Tuple ts) :=
  match n with
  | 0 => fun _ _ => ret tt
  | S m => fun ts mxs => (
      do x <- mxs Fin.F1;
      do xs <- rand_tuple (fun j => ts (Fin.FS j)) (fun j => mxs (Fin.FS j));
      ret (x,xs)
      )
  end.

Fixpoint rand_val(k : Kind) : M (eval_Kind k) :=
  match k return M (eval_Kind k) with
  | Bool => rand_bool
  | Bit n => rand_word n
  | Struct n ks fs => rand_tuple (fun i => eval_Kind (ks i)) (fun i => rand_val (ks i))
  | Array n k' => rand_vec (rand_val k')
  end.

Fixpoint rand_val_FK(k : FullKind) : M (eval_FK k) :=
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

Definition eval_UniBit{m n}(op : UniBitOp m n) : Word m -> Word n :=
  match op with
  | Inv n => inv
  | TruncLsb lsb msb => trunc_lsb
  | TruncMsb lsb msb => trunc_msb
  | UAnd n => uand
  | UOr n => uor
  | UXor n => uxor
  end.

Definition eval_BinBit{m n p}(op : BinBitOp m n p) : Word m -> Word n -> Word p :=
  match op with
  | Sub n => sub
  | Div n => div
  | Rem n => rem
  | Sll n m => sll
  | Srl n m => srl
  | Sra n m => sra
  | Concat msb lsb => concat
  end.

Definition eval_CABit{n}(op : CABitOp) : list (Word n) -> Word n :=
  match op with
  | Add => add
  | Mul => mul
  | Band => band
  | Bor => bor
  | Bxor => bxor
  end.

Definition eval_BinBitBool{m n}(op : BinBitBoolOp m n) : Word m -> Word n -> bool :=
  match op with
  | LessThan n => wltb
  end.

Fixpoint eval_ConstT{k}(e : ConstT k) : eval_Kind k :=
  match e with
  | ConstBool b => b
  | ConstBit n w => nat_to_word (wordToNat w)
  | ConstStruct n ks ss es => mkTup (fun i => eval_Kind (ks i)) (fun i => eval_ConstT (es i))
  | ConstArray n k' es => make_vec (fun i => eval_ConstT (es i))
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
  | ReadArray n m k v i => match lt_dec (word_to_nat (eval_Expr i)) n with
                           | left pf => index (Fin.of_nat_lt pf) (eval_Expr v)
                           | right _ => eval_ConstT (getDefaultConst k)
                           end
  | ReadArrayConst n k v i => index i (eval_Expr v)
  | BuildArray n k v => make_vec (fun i => eval_Expr (v i))
  end.

(* Fixpoint chop_word{n x} : Word (n * x) -> Vec n (Word x) :=
  match n with
  | 

Fixpoint val_unpack'(k : Kind) : Word (size k) -> eval_Kind k.
Proof.
  induction k; simpl; intro e.
  (* Bool *)
  - exact (weqb e (nat_to_word 1)).
  (* Word *)
  - exact e.
  (* Tup *)
  - admit.
  - 
 *)


Definition val_unpack(k : Kind) : Word (size k) -> eval_Kind k :=
  fun w => eval_Expr (unpack _ (Const _ (ConstBit (natToWord _ (word_to_nat w))))).

Definition eval_SysT(s : SysT eval_Kind) : M unit :=
  match s with
  | DispString s => print s
  | DispExpr k e ff => print (print_Kind ff (eval_Expr e))
  | Finish => exit
  end.

Fixpoint eval_list_SysT(xs : list (SysT eval_Kind)) : M unit :=
  match xs with
  | [] => ret tt
  | s::ys => (
      do _ <- eval_SysT s;
      eval_list_SysT ys
      )
  end.

End Eval.

