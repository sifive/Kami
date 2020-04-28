Require Import Kami.Syntax Program.

Axiom cheat : forall {X},X.

Section Constants.

Fixpoint all_left_list{X Y}(zs : list (X + Y)) : option (list X) :=
  match zs with
  | [] => Some []
  | inl x :: zs' => match all_left_list zs' with
                    | None => None
                    | Some xs => Some (x :: xs)
                    end
  | inr _ :: _ => None
  end.

Definition FinFunc_cons{n}{X : Fin.t (S n) -> Type}(x : X F1)(f : forall i, X (FS i)) : forall i, X i.
Proof.
  intro i.
  dependent destruction i.
  - exact x.
  - exact (f i).
Defined.

Fixpoint all_left_Fin{n} : forall {X Y : Fin.t n -> Type}, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) :=
  match n return forall X Y : Fin.t n -> Type, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) with
  | 0 => fun X Y _ => Some (case0 _)
  | S m => fun X Y f => match f F1 with
                        | inl x => match @all_left_Fin m (fun i => X (FS i)) (fun i => Y (FS i)) (fun i => f (FS i)) with
                                   | None => None
                                   | Some g => Some (FinFunc_cons x g)
                                   end
                        | inr _ => None
                        end
  end.
(* 
Definition coerce_Const_Bool : ConstT Bool -> bool.
Proof.
  intro c.
  dependent destruction c.
  exact b.
Defined.

Definition coerce_Const_Bit{n} : ConstT (Bit n) -> word n.
Proof.
  intro c.
  dependent destruction c.
  exact w.
Defined. *)

Definition back_to_Expr{ty k}(s : ConstT k + Expr ty (SyntaxKind k)) : Expr ty (SyntaxKind k) :=
  match s with
  | inl c => Const ty c
  | inr e => e
  end.

Fixpoint wrap_ConstT{k} : type k -> ConstT k:=
  match k return type k -> ConstT k with
  | Bool => ConstBool
  | Bit n => @ConstBit n
  | Struct n ks fs => fun c => ConstStruct ks fs (fun i => wrap_ConstT (c i))
  | Array n k => fun c => ConstArray (fun i => wrap_ConstT (c i))
  end.

Definition squash_CABool{ty}(xs : list (ConstT Bool  + Expr ty (SyntaxKind Bool)))(op : CABoolOp) :
  ConstT Bool + Expr ty (SyntaxKind Bool) :=
  match all_left_list xs with
  | None => inr (CABool op (map back_to_Expr xs))
  | Some cs => inl (ConstBool (evalCABool op (map (@evalConstT _) cs)))
  end.

Definition squash_CABit{ty n}(xs : list (ConstT (Bit n) + Expr ty (SyntaxKind (Bit n))))(op : CABitOp) : ConstT (Bit n) + Expr ty (SyntaxKind (Bit n)) :=
  match all_left_list xs with
  | None => inr (CABit op (map back_to_Expr xs))
  | Some cs => inl (ConstBit (evalCABit op (map (@evalConstT _) cs)))
  end.

Definition squash_Kor{ty k}(xs : list (ConstT k + Expr ty (SyntaxKind k))) : ConstT k + Expr ty (SyntaxKind k) :=
  match all_left_list xs with
  | None => inr (Kor (map back_to_Expr xs))
  | Some cs => inl (wrap_ConstT (evalKorOp _ (map (@evalConstT _) cs) (evalConstT (getDefaultConst k))))
  end.

Fixpoint Const_eqb{k} : ConstT k -> ConstT k -> bool.
Proof.
  destruct k; intros c1 c2;
  dependent destruction c1;
  dependent destruction c2.
  - exact (Bool.eqb b b0).
  - exact (weqb w w0).
  - exact (Fin_forallb (fun i => Const_eqb (k i) (fv i) (fv0 i))).
  - exact (Fin_forallb (fun i => Const_eqb k (fk i) (fk0 i))).
Defined.

Lemma weqb_refl : forall (n : nat)(x : word n), weqb x x = true.
Proof.
  intros.
  destruct (weqb x x) eqn:G.
  - reflexivity.
  - elim (weqb_false _ _ G eq_refl).
Qed.

Lemma Const_eqb_correct : forall (k : Kind)(c1 c2 : ConstT k), Const_eqb c1 c2 = true <-> c1 = c2.
Proof.
  dependent induction c1; dependent destruction c2.
  - split; intro.
    + destruct (eqb_true_iff b b0).
      rewrite (H0 H); reflexivity.
    + inversion H; apply eqb_true_iff; auto.
  - split; intro.
    + rewrite (weqb_true _ _ H); reflexivity.
    + rewrite H.
      apply weqb_refl.
  - split; intro.
    + f_equal.
      apply functional_extensionality_dep.
      intro.
      simpl in H0.
      unfold simplification_existT1 in H0.
      unfold solution_left in H0.
      unfold eq_rect_r in H0.
      unfold eq_rect in H0.
      unfold eq_sym in H0.
      unfold f_equal in H0.
      unfold simplification_existT2 in H0.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n => t n -> string) n fs fs eq_refl = eq_refl).
      admit.
      rewrite H1 in H0.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n => t n -> Kind) n fk fk eq_refl = eq_refl).
      admit.
      rewrite H2 in H0.
      rewrite H1 in H0.
      rewrite H2 in H0.
      simpl.
      Search _ Fin_forallb.
      rewrite Fin_forallb_correct in H0.
      apply H.
      apply H0.
    + simpl.
      unfold simplification_existT1.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold eq_sym.
      unfold f_equal.
      unfold simplification_existT2.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n0 => t n0 -> string) n fs fs eq_refl = eq_refl).
      admit.
      rewrite H1.
      assert (Eqdep.EqdepTheory.inj_pair2 nat (fun n0 => t n0 -> Kind) n fk fk eq_refl = eq_refl).
      admit.
      rewrite H2.
      rewrite H1.
      rewrite H2.
      rewrite Fin_forallb_correct.
      intro.
      apply H.
      inversion H0.
      assert (fv = fv0).
      admit.
      rewrite H3; reflexivity.
  - split; intro.
    + f_equal.
      apply functional_extensionality.
      intro.
      simpl in H0.
      unfold solution_left in H0.
      unfold eq_rect_r in H0.
      unfold eq_rect in H0.
      unfold eq_sym in H0.
      unfold f_equal in H0.
      rewrite Fin_forallb_correct in H0.
      apply H.
      apply H0.
    + simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold eq_sym.
      unfold f_equal.
      rewrite Fin_forallb_correct.
      intro.
      apply H.
      assert (fk = fk0).
      admit.
      rewrite H1; reflexivity.
Admitted.

Definition result ty (k : FullKind) : Type :=
  match k with
  | SyntaxKind k' => ConstT k' + Expr ty (SyntaxKind k')
  | NativeKind _ _ => unit
  end.

Check Kor.

Fixpoint simplify_consts_aux{ty k}(e : Expr ty k) : result ty k :=
  match e in Expr _ k' return result ty k' with
  | Var k x => match k return fullType ty k -> result ty k  with
               | SyntaxKind k' => fun x => inr (Var ty (SyntaxKind k') x)
               | NativeKind _ _ => fun _ => tt
               end x
  | Const _ c => inl c
  | UniBool o e' => match simplify_consts_aux  e' with
                    | inl c => inl (ConstBool (evalUniBool o (evalConstT c)))
                    | inr e'' => inr (UniBool o e'')
                    end
  | CABool o es => squash_CABool (map simplify_consts_aux es) o
  | UniBit n1 n2 o e => match simplify_consts_aux e with
                        | inl c => (inl (ConstBit (evalUniBit o (evalConstT c))))
                        | inr e' => inr (UniBit o e')
                        end
  | CABit n o es => squash_CABit (map simplify_consts_aux es) o
  | BinBit n1 n2 n3 o e1 e2 => match simplify_consts_aux e1, simplify_consts_aux e2 with
                               | inl c1 , inl c2  => inl (ConstBit (evalBinBit o (evalConstT c1) (evalConstT c2)))
                               | inl c1 , inr e2' => inr (BinBit o (Const ty c1) e2')
                               | inr e1', inl c2  => inr (BinBit o e1' (Const ty c2))
                               | inr e1', inr e2' => inr (BinBit o e1' e2')
                               end
  | BinBitBool n1 n2 o e1 e2 => match simplify_consts_aux e1, simplify_consts_aux e2 with
                               | inl c1 , inl c2  => inl (ConstBool (evalBinBitBool o (evalConstT c1) (evalConstT c2)))
                               | inl c1 , inr e2' => inr (BinBitBool o (Const ty c1) e2')
                               | inr e1', inl c2  => inr (BinBitBool o e1' (Const ty c2))
                               | inr e1', inr e2' => inr (BinBitBool o e1' e2')
                               end
  | ITE k e1 e2 e3 => match k return Expr ty k -> Expr ty k -> result ty k with
                      | SyntaxKind k' => fun e2 e3 => match simplify_consts_aux e1 with
                                                      | inl c => simplify_consts_aux (if evalConstT c then e2 else e3)
                                                      | inr e' => inr (ITE e' (back_to_Expr (simplify_consts_aux e2)) (back_to_Expr (simplify_consts_aux e2)))
                                                      end
                      | NativeKind _ _ => fun _ _ => tt
                      end e2 e3
  | Eq k e1 e2 => match simplify_consts_aux e1, simplify_consts_aux e2 with
                  | inl c1, inl c2   => inl (ConstBool (Const_eqb c1 c2))
                  | inl c1, inr e2'  => inr (Eq (Const ty c1) e2')
                  | inr e1', inl c2  => inr (Eq e1' (Const ty c2))
                  | inr e1', inr e2' => inr (Eq e1' e2')
                  end
  | ReadStruct n fk fs e i => match simplify_consts_aux e with
                              | inl c => inl (wrap_ConstT (evalConstT c i))
                              | inr e' => inr (ReadStruct e' i)
                              end
  | BuildStruct n fk fs fv => match all_left_Fin (fun i => simplify_consts_aux (fv i)) with
                              | Some c => inl (ConstStruct _ _ c)
                              | None => inr (BuildStruct _ _ (fun i => back_to_Expr (simplify_consts_aux (fv i))))
                              end
  | ReadArray n m k e1 e2 => match simplify_consts_aux e1, simplify_consts_aux e2 with
                             | inl c1, inl c2 => match lt_dec (Z.to_nat (wordVal _ (evalConstT c2))) n with
                                                 | left pf => inl (wrap_ConstT (evalConstT c1 (Fin.of_nat_lt pf)))
                                                 | _ => inl (getDefaultConst _)
                                                 end
                             | inl c1, inr e2' => inr (ReadArray (Const ty c1) e2')
                             | inr e1', inl c2 => inr (ReadArray e1' (Const ty c2))
                             | inr e1', inr e2' => inr (ReadArray e1' e2')
                             end
  | ReadArrayConst n k e i => match simplify_consts_aux e with
                              | inl c => inl (wrap_ConstT (evalConstT c i))
                              | inr e' => inr (ReadArrayConst e' i)
                              end
  | BuildArray n k es => match all_left_Fin (fun i => simplify_consts_aux (es i)) with
                         | Some c => inl (ConstArray c)
                         | None => inr (BuildArray (fun i => back_to_Expr (simplify_consts_aux (es i))))
                         end
  | Kor k es => squash_Kor (map simplify_consts_aux es)
  | ToNative k e => tt
  | FromNative k e => inr (FromNative k e)
  end.

Definition simplify_consts{ty k}(e : Expr ty (SyntaxKind k)) : ConstT k + Expr ty (SyntaxKind k) :=
  simplify_consts_aux e.

Check isEq.
Check 

End Constants.

Section AssocComConstantSquashing.

(* putting this in mothballs for now *)

Inductive Binop := AndOp | OrOp | XorOp.

Inductive PassedExpr ty k :=
  | JustConst : ConstT k -> PassedExpr ty k
  | JustVar : Expr ty (SyntaxKind k) -> PassedExpr ty k
  | Mixed : ConstT k -> Expr ty (SyntaxKind k) -> Binop -> PassedExpr ty k.

Fixpoint sep_consts{ty k}(e : Expr ty (SyntaxKind k)) : PassedExpr ty k.
Proof.
  dependent destruction e.
  (* Var *)
  - exact (JustVar (Var _ _ f)).
  (* Const *)
  - exact (JustConst _ c).
  (* UniBool *)
  - destruct (sep_consts _ _ e) eqn:G.
    (* JustConst *)
    + dependent destruction c.
      exact (JustConst ty (negb b)).
    (* JustVar *)
    + exact (JustVar (UniBool u e0)).
    (* Mixed *)
    + dependent destruction c.
      destruct b0.
      (* AndOp *)
      * exact (Mixed (negb b) (UniBool Neg e0) OrOp).
      (* OrOp *)
      * exact (Mixed (negb b) (UniBool Neg e0) AndOp).
      (* XorOp *)
      * exact (Mixed (negb b) e0 XorOp).
  (* CABool *)
  - admit.
  (* UniBit *)
  - admit.
  (* CABit *)
  - admit.
  (* BinBit *)
  - admit.
  (* BinBitBool *)
Admitted.

End AssocComConstantSquashing.

























