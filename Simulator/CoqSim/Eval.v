Require Import Compare_dec List String.
Import ListNotations.

Require Import Kami.AllNotations.
Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.IO.
Require Import Kami.Simulator.CoqSim.TransparentProofs.

Fixpoint eval_Kind (k : Kind) : Type :=
  match k with
  | Bool => bool
  | Bit n => word n
  | Struct n ks fs => Tuple (fun i => eval_Kind (ks i))
  | Array n k' => Vec (eval_Kind k') n
  end.

Definition print_BF(bf : BitFormat) : nat -> string :=
  match bf with
  | Binary => nat_binary_string
  | Decimal => nat_decimal_string
  | Hex => nat_hex_string
  end.
    
Fixpoint print_Kind (k : Kind) (ff : FullFormat k) : eval_Kind k -> string :=
  match ff with
  | FBool n _ => fun x => space_pad n (if x then "1" else "0")
  | FBit n m bf => fun x => zero_pad m (print_BF bf (wordToNat _ x))
  | FStruct n fk fs ffs => fun x => ("{" ++ String.concat "; " (vec_to_list (vec_map (fun '(str1,str2) => str1 ++ ":" ++ str2) (add_strings fs (tup_to_vec _ (fun i => print_Kind (ffs i)) x)))) ++ "}")%string
  | FArray n k' ff' => fun x => ("[" ++ String.concat "; " (vec_to_list (vec_map (fun '(n,y) => nat_decimal_string n ++ "=" ++ print_Kind ff' y) (add_indices x))) ++ "]")%string (*fix*)
  end.

Fixpoint Kind_eq{k} : eval_Kind k -> eval_Kind k -> bool :=
  match k with
  | Bool => Bool.eqb
  | Bit n => @weqb n
  | Struct n ks fs => TupEq (fun i => eval_Kind (ks i)) (fun i => @Kind_eq (ks i))
  | Array n k' => VecEq (@Kind_eq k')
  end.

Definition eval_FK(k : FullKind) :=
  match k with
  | SyntaxKind k' => eval_Kind k'
  | NativeKind t _ => t
  end.

Fixpoint rand_val(k : Kind) : IO (eval_Kind k) :=
  match k with
  | Bool => rand_bool
  | Bit n => rand_word n
  | Struct n ks fs => rand_tuple (fun i => eval_Kind (ks i)) (fun i => rand_val (ks i))
  | Array n k' => rand_vec (rand_val k')
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

Definition eval_UniBit{m n}(op : UniBitOp m n) : word m -> word n :=
  evalUniBit op.

Definition eval_BinBit{m n p}(op : BinBitOp m n p) : word m -> word n -> word p :=
  evalBinBit op.

Definition eval_CABit{n}(op : CABitOp) : list (word n) -> word n :=
  evalCABit op.

Definition eval_BinBitBool{m n}(op : BinBitBoolOp m n) : word m -> word n -> bool :=
  evalBinBitBool op.

Fixpoint eval_ConstT{k}(e : ConstT k) : eval_Kind k :=
  match e with
  | ConstBool b => b
  | ConstBit n w => w
  | ConstStruct n ks ss es => mkTup (fun i => eval_Kind (ks i)) (fun i => eval_ConstT (es i))
  | ConstArray n k' es => mkVec (fun i => eval_ConstT (es i))
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
  | CABool op es => eval_CABool op (map eval_Expr es)
  | UniBit m n op e => eval_UniBit op (eval_Expr e)
  | BinBit m n p op e1 e2 => eval_BinBit op (eval_Expr e1) (eval_Expr e2)
  | CABit n op es => eval_CABit op (map eval_Expr es)
  | BinBitBool m n op e1 e2 => eval_BinBitBool op (eval_Expr e1) (eval_Expr e2)
  | ITE _ p e1 e2 => eval_Expr (if eval_Expr p then e1 else e2)
  | Eq _ e1 e2 => Kind_eq (eval_Expr e1) (eval_Expr e2)
  | ReadStruct n ks ss e i => tup_index i _ (eval_Expr e)
  | BuildStruct n ks ss es => mkTup _ (fun i => eval_Expr (es i))
  | ReadArray n m k v i => match lt_dec (wordToNat _ (eval_Expr i)) n with
                           | left pf => vec_index (Fin.of_nat_lt pf) (eval_Expr v)
                           | right _ => eval_ConstT (getDefaultConst k)
                           end
  | ReadArrayConst n k v i => vec_index i (eval_Expr v)
  | BuildArray n k v => mkVec (fun i => eval_Expr (v i))
  end.

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
      io_do _ <- eval_SysT s;
      eval_list_SysT ys
      )
  end.

Section EvalAction.

Definition SimReg := (string * {x : _ & fullType eval_Kind x})%type.
Definition SimRegs := list SimReg.

Variable regs : SimRegs.

Fixpoint mkProd(ts : list Type) : Type :=
  match ts with
  | [] => unit
  | T::ts' => (T * mkProd ts')%type
  end.

Fixpoint return_meth(meth : string)(sig : Signature)(meths : list (string * Signature)) : mkProd (map (fun dec => eval_Kind (fst (snd dec)) -> IO (eval_Kind (snd (snd dec)))) meths) -> option (eval_Kind (fst (sig)) -> IO (eval_Kind (snd (sig)))).
 refine match meths return mkProd (map (fun dec => eval_Kind (fst (snd dec)) -> IO (eval_Kind (snd (snd dec)))) meths) -> option (eval_Kind (fst (sig)) -> IO (eval_Kind (snd (sig)))) with
  | [] => fun _ => None
  | dec::meths' => match string_sigb (meth,sig) dec with
                   | left pf => fun fs => Some _
                   | right _ => fun fs => return_meth meth sig meths' (snd fs)
                   end
  end.
Proof.
  assert (sig = snd dec).
  rewrite <- pf; auto.
  rewrite H.
  exact (fst fs).
Defined.

Fixpoint eval_ActionT{k}(meths : list (string * Signature))(updates : SimRegs)(a : ActionT eval_Kind k)(fs : mkProd (map (fun dec => eval_Kind (fst (snd dec)) -> IO (eval_Kind (snd (snd dec)))) meths)){struct a} : IO (SimRegs * eval_Kind k).
  refine match a with
  | MCall meth s e cont => match return_meth meth s meths fs with
                           | None => error ("Method " ++ meth ++ " not found")
                           | Some f => (
                                io_do v <- f (eval_Expr e);
                                eval_ActionT _ meths updates (cont v) fs
                                )
                           end
  | LetExpr k e cont => eval_ActionT _ meths updates (cont (eval_Expr e)) fs
  | LetAction k a cont => (
      io_do p <- eval_ActionT _ meths updates a fs;
      eval_ActionT _ meths (fst p) (cont (snd p)) fs
      )
  | ReadNondet k cont => (
      io_do v <- rand_val_FK k;
      eval_ActionT _ meths updates (cont v) fs
      )
  | ReadReg r k cont => match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
  | WriteReg r k e a => match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
  | IfElse e k a1 a2 cont => let a := if (eval_Expr e) then a1 else a2 in (
      io_do p <- eval_ActionT _ meths updates a fs;
      eval_ActionT _ meths (fst p) (cont (snd p)) fs
      )
  | Sys ss a => (
      io_do _ <- eval_list_SysT ss;
      eval_ActionT _ meths updates a fs
      )
  | Return e => ret (updates, eval_Expr e)
  end.
Proof.
  - destruct p.
    destruct x.
    * destruct k.
      + destruct (Kind_dec2 k1 k).
        ++ rewrite e in f.
           exact (eval_ActionT _ meths updates (cont f) fs).
        ++ exact (error "mismatch").
      + exact (error "no natives").
    * exact (error "no natives").
  - destruct p as [x _].
    destruct k.
    * destruct x.
      + destruct (Kind_dec2 k k1).
        ++ exact (eval_ActionT _ meths ((r, existT _ (SyntaxKind k) (eval_Expr e))::updates) a fs).
        ++ exact (error "mismatch").
      + exact (error "no natives!!!!").
    * exact (error "no natives").
Defined.

Fixpoint curried(X : Type)(ts : list Type) : Type :=
  match ts with
  | [] => X
  | T::ts' => T -> curried X ts'
  end.

Fixpoint curry(X : Type)(ts : list Type) : (mkProd ts -> X) -> curried X ts :=
  match ts return (mkProd ts -> X) -> curried X ts with
  | [] => fun f => f tt
  | T::ts' => fun f t => curry ts' (fun xs => f (t,xs))
  end.

End EvalAction.

Fixpoint do_single_update(upd : SimReg)(regs : SimRegs) : SimRegs :=
  match upd with
  | (reg,v) => match regs with
               | [] => []
               | (reg',v')::regs' => if String.eqb reg reg' then (reg,v)::regs' else (reg',v')::do_single_update upd regs'
               end
  end.

Definition do_updates(upds : SimRegs)(regs : SimRegs) : SimRegs :=
  fold_right do_single_update regs upds.

Definition foo meths := SimRegs -> mkProd (map (fun dec : string * (Kind * Kind) => eval_Kind (fst (snd dec)) -> IO (eval_Kind (snd (snd dec)))) meths) -> IO (SimRegs * eval_Kind Void).

CoFixpoint eval_BaseModule_rr_aux(meths : list (string * Signature))(curr_regs : SimRegs)(rem_rules all_rules : list (foo meths)) : mkProd (map (fun dec : string * (Kind * Kind) => eval_Kind (fst (snd dec)) -> IO (eval_Kind (snd (snd dec)))) meths) -> IO unit :=
  match rem_rules with
  | [] => fun fs => bind (ret tt) (fun _ => eval_BaseModule_rr_aux curr_regs all_rules all_rules fs)
  | a::xs => fun fs => (
      io_do p <- a curr_regs fs;
      eval_BaseModule_rr_aux (do_updates (fst p) curr_regs) xs all_rules fs
      )
  end.


Definition initialize_SimRegs(regs : list RegInitT) : SimRegs :=
  map (fun '(r,existT k v) => match v return SimReg with
                              | None => (r,existT _ k (eval_ConstFullT (getDefaultConstFullKind k)))
                              | Some c => (r,existT _ k (eval_ConstFullT c))
                              end) regs.

Definition mkActionT : RuleT -> ActionT eval_Kind Void :=
  fun '(_,a) => a eval_Kind.

Definition eval_BaseModule_rr_unc(meths : list (string * Signature))(m : BaseModule) :=
  match m with
  | BaseRegFile _ => fun _ => error "BaseRegFile not supported"
  | BaseMod regs rules _ => let all_rules := map (fun r rgs fs => @eval_ActionT rgs Void meths [] (mkActionT r) fs) rules in eval_BaseModule_rr_aux (initialize_SimRegs regs) all_rules all_rules
  end.

Definition eval_BaseModule_rr meths m := curry _ (eval_BaseModule_rr_unc meths m).

Require Import Kami.Tutorial.SyntaxEx.

Section BigTest.

Definition sigs := [("extMeth1",(Bit 20, Bool));("extMeth2",(Bit 20,Void));("extMeth3",(Void,Bit 4));("extMeth4",(Void,Void));("extMeth2_2",(Bit 20, Void))].

Definition out := eval_BaseModule_rr sigs (exampleModule "test").

Ltac mycbv x := let y := (eval cbv [x eval_BaseModule_rr eval_BaseModule_rr_aux eval_ActionT lookup fst find fullType Bool.eqb snd Datatypes.length curried
  eval_list_SysT eval_SysT eval_Expr string_sigb eq_trans f_equal
  Signature_decb String.eqb Ascii.eqb andb Kind_decb Nat.eqb
  eq_rect_r eq_rect eq_sym orb projT1 projT2 lt_dec tup_index Fin_forallb Signature_dec2 string_dec2 Kind_dec2 Kind_decb_eq2
  string_rec String_eqb_eq2 string_ind Kind_ind Ascii_eqb_eq2 ascii_dec Nat_eqb_eq2 Nat_eqb_refl2 nth_Fin' curry] in x) in
  let z := eval simpl in y in
  let w := eval cbv [eq_rect_r eq_rect eq_sym nth_Fin' nth_Fin cast Datatypes.length eq_add_S f_equal] in z in
  let v := eval simpl in w in
   exact w.

Definition out2 := ltac:(mycbv out).

End BigTest.

Require Import ExtrHaskellBasic.
Extraction Language Haskell.

Extract Inductive IO => "Prelude.IO"

  [
    "Prelude.putStrLn"
    "Prelude.return"
    "(GHC.Base.>>=)"
    "Prelude.error"
    "Prelude.return (unsafeCoerce Prelude.True)" (*fix*)
    "Prelude.return (unsafeCoerce 0)"    (*fix*)
    "System.Exit.exitSuccess"
  ]

  "Prelude.error ""Pattern matching on IO not supported""".
