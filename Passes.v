Require Import Kami.Syntax Program.

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

Lemma all_left_list_correct : forall {X Y}(zs : list (X + Y))(xs : list X),
  all_left_list zs = Some xs -> zs = map inl xs.
Proof.
  induction zs; intros.
  - inversion H; reflexivity.
  - simpl in H.
    + destruct a.
      * destruct (all_left_list zs) eqn:G.
        ** inversion H.
           simpl; f_equal.
           apply IHzs; auto.
        ** discriminate.
      * discriminate.
Qed.

Fixpoint all_left_Fin{n} : forall {X Y : Fin.t n -> Type}, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) :=
  match n return forall X Y : Fin.t n -> Type, (forall i : Fin.t n, X i + Y i) -> option (forall i, X i) with
  | 0 => fun X Y _ => Some (case0 _)
  | S m => fun X Y f => match f F1 with
                        | inl x => match @all_left_Fin m (fun i => X (FS i)) (fun i => Y (FS i)) (fun i => f (FS i)) with
                                   | None => None
                                   | Some g => Some (fun i => fin_case i _ x g)
                                   end
                        | inr _ => None
                        end
  end.

Lemma all_left_Fin_correct{n} : forall {X Y : Fin.t n -> Type}(f : forall i, X i + Y i)(g : forall i, X i),
  all_left_Fin f = Some g -> forall i, f i = inl (g i).
Proof.
  induction n; intros.
  - dependent destruction i.
  - dependent destruction i.
    + simpl in H.
      destruct (f F1).
      * destruct all_left_Fin.
        ** inversion H; reflexivity.
        ** discriminate.
      * discriminate.
    + apply (IHn (fun i => X (FS i)) (fun i => Y (FS i)) (fun i => f (FS i)) (fun i => g (FS i))).
      simpl in H.
      destruct (f F1).
      * destruct all_left_Fin.
        ** inversion H; reflexivity.
        ** discriminate.
      * discriminate.
Qed.

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

Lemma eval_wrap : forall {k}(x : type k), evalConstT (wrap_ConstT x) = x.
Proof.
  induction k; intro.
  - reflexivity.
  - reflexivity.
  - simpl; apply functional_extensionality_dep.
    intro.
    apply H.
  - simpl; apply functional_extensionality.
    intro.
    apply IHk.
Qed.

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

Definition result ty (k : FullKind) : Type :=
  match k with
  | SyntaxKind k' => ConstT k' + Expr ty (SyntaxKind k')
  | NativeKind _ _ => unit
  end.

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
                                                      | inr e' => inr (ITE e' (back_to_Expr (simplify_consts_aux e2)) (back_to_Expr (simplify_consts_aux e3)))
                                                      end
                      | NativeKind _ _ => fun _ _ => tt
                      end e2 e3
  | Eq k e1 e2 => match simplify_consts_aux e1, simplify_consts_aux e2 with
                  | inl c1, inl c2   => inl (ConstBool (getBool (isEq _ (evalConstT c1) (evalConstT c2))))
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

Lemma Forall_eq_map : forall {X Y}(f g : X -> Y)(xs : list X),
  Forall (fun x => f x = g x) xs -> map f xs = map g xs.
Proof.
  induction xs; intros.
  - reflexivity.
  - simpl.
    inversion H.
    pose (IHxs H3); congruence.
Qed.

Lemma map_compose : forall {X Y Z}(g : Y -> Z)(f : X -> Y)(xs : list X),
  map (compose g f) xs = map g (map f xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs; reflexivity.
Qed.

Lemma simplify_consts_aux_correct : forall {k}(e : Expr type k),
  match k return (Expr type k -> result type k -> Prop) with
  | SyntaxKind k' => fun e r => evalExpr e = match r with
                                             | inl c => evalConstT c
                                             | inr e' => evalExpr e'
                                             end
  | NativeKind _ _ => fun _ _ => True
  end e (simplify_consts_aux e).
Proof.
  intros.
  apply (@Expr_ind2 type (fun k e' =>
  match k as k0 return (Expr type k0 -> result type k0 -> Prop) with
| SyntaxKind k' =>
    fun (e0 : Expr type (SyntaxKind k')) (r : result type (SyntaxKind k')) =>
    evalExpr e0 = match r with
                  | inl c => evalConstT c
                  | inr e' => evalExpr e'
                  end
| @NativeKind t c =>
    fun (_ : Expr type (NativeKind c)) (_ : result type (NativeKind c)) => True
end e' (simplify_consts_aux e'))); intros.
  - destruct k0.
    + simpl; reflexivity.
    + exact I.
  - simpl; reflexivity.
  - simpl.
    destruct (simplify_consts_aux e0); simpl; congruence.
  - simpl.
    unfold squash_CABool.
    destruct all_left_list eqn:G.
    + simpl.
      pose (all_left_list_correct _ G).
      f_equal.
      unfold simplify_consts_aux.
      pose (Forall_eq_map (@evalExpr (SyntaxKind Bool)) _ H) as pf.
      simpl fullType in pf.
      rewrite pf.
      assert ((fun (e' : Expr type (SyntaxKind Bool)) => match simplify_consts_aux e' with
                        | inl c0 => evalConstT c0
                        | inr e0' => evalExpr e0'
                        end) = compose (fun (x : result type (SyntaxKind Bool)) => match x with
                                                 | inl c0 => evalConstT c0
                                                 | inr e0' => evalExpr e0'
                                                 end)
                                                  simplify_consts_aux) by (unfold compose; reflexivity).
     simpl type in H0.
     rewrite H0.
     rewrite map_compose.
     simpl result.
     rewrite e0.
     rewrite <- map_compose.
     unfold compose.
     reflexivity.
    + simpl.
      f_equal.
      repeat rewrite <- map_compose.
      unfold compose.
      unfold back_to_Expr.
      clear G.
      induction l.
      * reflexivity.
      * simpl.
        inversion H.
        rewrite H2.
        destruct (simplify_consts_aux a) eqn:G1.
        ** simpl; f_equal.
           apply IHl; auto.
        ** f_equal.
           apply IHl; auto.
  - simpl.
    destruct (simplify_consts_aux e0); simpl; congruence.
  - simpl.
    unfold squash_CABit.
    destruct all_left_list eqn:G.
    + simpl.
      pose (all_left_list_correct _ G).
      f_equal.
      unfold simplify_consts_aux.
      pose (Forall_eq_map (@evalExpr (SyntaxKind (Bit n))) _ H) as pf.
      simpl fullType in pf.
      rewrite pf.
      assert ((fun (e' : Expr type (SyntaxKind (Bit n))) => match simplify_consts_aux e' with
                        | inl c0 => evalConstT c0
                        | inr e0' => evalExpr e0'
                        end) = compose (fun (x : result type (SyntaxKind (Bit n))) => match x with
                                                 | inl c0 => evalConstT c0
                                                 | inr e0' => evalExpr e0'
                                                 end)
                                                  simplify_consts_aux) by (unfold compose; reflexivity).
     simpl type in H0.
     rewrite H0.
     rewrite map_compose.
     simpl result.
     rewrite e0.
     rewrite <- map_compose.
     unfold compose.
     reflexivity.
    + simpl.
      f_equal.
      repeat rewrite <- map_compose.
      unfold compose.
      unfold back_to_Expr.
      clear G.
      induction l.
      * reflexivity.
      * simpl.
        inversion H.
        rewrite H2.
        destruct (simplify_consts_aux a) eqn:G1.
        ** simpl; f_equal.
           apply IHl; auto.
        ** f_equal.
           apply IHl; auto.
  - simpl.
    destruct (simplify_consts_aux e0); destruct (simplify_consts_aux e1); simpl; congruence.
  - simpl.
    destruct (simplify_consts_aux e0); destruct (simplify_consts_aux e1); simpl; congruence.
  - destruct k0.
    + simpl.
      destruct (simplify_consts_aux e0).
      * rewrite H.
        destruct (evalConstT c).
        ** destruct (simplify_consts_aux e1); auto.
        ** destruct (simplify_consts_aux e2); auto.
      * simpl.
        rewrite H.
        unfold back_to_Expr.
        destruct (simplify_consts_aux e1); destruct (simplify_consts_aux e2);
        simpl; rewrite H1; rewrite H0; reflexivity.
    + exact I.
  - simpl.
    unfold getBool.
    destruct isEq; destruct (simplify_consts_aux e0); destruct (simplify_consts_aux e1).
    + destruct isEq.
      * reflexivity.
      * congruence.
    + simpl.
      destruct isEq.
      * reflexivity.
      * congruence.
    + simpl.
      destruct isEq.
      * reflexivity.
      * congruence.
    + simpl.
      destruct isEq.
      * reflexivity.
      * congruence.
    + simpl.
      destruct isEq.
      * congruence.
      * reflexivity.
    + simpl.
      destruct isEq.
      * congruence.
      * reflexivity.
    + simpl.
      destruct isEq.
      * congruence.
      * reflexivity.
    + simpl.
      destruct isEq.
      * congruence.
      * reflexivity.
  - simpl.
    destruct (simplify_consts_aux e0).
    + rewrite <- H.
      symmetry; apply eval_wrap.
    + simpl; congruence.
  - simpl.
    apply functional_extensionality_dep.
    intro.
    destruct all_left_Fin eqn:G.
    + simpl.
      pose (all_left_Fin_correct _ G x).
      simpl in e0.
      pose (H x).
      rewrite e0 in e1; auto.
    + simpl.
      destruct simplify_consts_aux eqn:G1;
      pose (H x) as Hx; rewrite G1 in Hx; simpl; auto.
  - simpl.
    destruct (simplify_consts_aux e0); destruct (simplify_consts_aux e1).
    + rewrite H0.
      destruct lt_dec.
      * rewrite eval_wrap; congruence.
      * reflexivity.
    + simpl.
      rewrite H0.
      destruct lt_dec.
      * congruence.
      * reflexivity.
    + simpl.
      rewrite H0.
      destruct lt_dec.
      * congruence.
      * reflexivity.
    + simpl.
      rewrite H0.
      destruct lt_dec.
      * congruence.
      * reflexivity.
  - simpl.
    destruct (simplify_consts_aux e0).
    + rewrite eval_wrap; congruence.
    + simpl; congruence.
  - simpl.
    apply functional_extensionality.
    intro.
    destruct all_left_Fin eqn:G.
    + pose (all_left_Fin_correct _ G x).
      simpl in e1.
      pose (H x).
      rewrite e1 in e2.
      simpl; auto.
    + simpl.
      unfold back_to_Expr.
      destruct (simplify_consts_aux (e0 x)) eqn:G1;
      pose (H x) as Hx; rewrite G1 in Hx; auto.
  - simpl.
    unfold squash_Kor.
    destruct all_left_list eqn:G.
    + rewrite eval_wrap.
      pose (all_left_list_correct _ G).
      f_equal.
      pose (Forall_eq_map (@evalExpr (SyntaxKind k0)) _ H) as pf.
      simpl fullType in pf.
      rewrite pf.
      assert ((fun (e' : Expr type (SyntaxKind k0)) => match simplify_consts_aux e' with
                        | inl c0 => evalConstT c0
                        | inr e0' => evalExpr e0'
                        end) = compose (fun (x : result type (SyntaxKind k0)) => match x with
                                                 | inl c0 => evalConstT c0
                                                 | inr e0' => evalExpr e0'
                                                 end)
                                                  simplify_consts_aux) by (unfold compose; reflexivity).
     simpl type in H0.
     rewrite H0.
     rewrite map_compose.
     simpl result.
     rewrite e0.
     rewrite <- map_compose.
     unfold compose.
     reflexivity.
    + simpl.
      f_equal.
      repeat rewrite <- map_compose.
      unfold compose.
      clear G.
      induction l.
      * reflexivity.
      * simpl.
        inversion H.
        destruct (simplify_consts_aux a).
        ** simpl; rewrite H2.
           f_equal.
           apply IHl; auto.
        ** simpl; rewrite H2.
           f_equal.
           apply IHl; auto.
  - exact I.
  - reflexivity.
Qed.

Definition simplify_consts{ty k}(e : Expr ty (SyntaxKind k)) : Expr ty (SyntaxKind k) :=
  match simplify_consts_aux e with
  | inl c => Const ty c
  | inr e' => e'
  end.

Lemma simplify_consts_correct : forall {k}(e : Expr type (SyntaxKind k)), evalExpr (simplify_consts e) = evalExpr e.
Proof.
  intros.
  unfold simplify_consts.
  pose (simplify_consts_aux_correct e) as pf.
  simpl in pf.
  rewrite pf.
  clear pf.
  destruct (simplify_consts_aux e); reflexivity.
Qed.

End Constants.

(* putting this in mothballs for now *)
(*
Section AssocComConstantSquashing.

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

*)























