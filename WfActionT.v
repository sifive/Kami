Require Export Bool Ascii String Fin List FunctionalExtensionality Psatz PeanoNat.
Require Export Kami.Syntax.

Print ActionT.
Print Kind.
Print fullType.
Print unit.
Print tt.
Check tt.

Fixpoint WfActionT_unit {k} (regs : list (string * {x : FullKind & RegInitValT x})) (a : ActionT (fun _ => unit) k) : bool :=
                             match a with
                             | MCall meth s e cont => WfActionT_unit regs (cont tt)
                             | LetExpr k' e cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                   | SyntaxKind k'' => fun cont => WfActionT_unit regs (cont tt)
                                                   | @NativeKind k'' v => fun cont => false
                                                   end cont
                             | LetAction k a cont => WfActionT_unit regs a && WfActionT_unit regs (cont tt)
                             | ReadNondet k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                    | SyntaxKind k'' => fun cont => WfActionT_unit regs (cont tt)
                                                    | @NativeKind k'' v => fun cont => false
                                                    end cont
                             | ReadReg r k' cont => match lookup String.eqb r regs with
                                                    | None => false
                                                    | Some (existT k'' _) =>
                                                      match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                      | SyntaxKind k''' => match k'' with
                                                                           | SyntaxKind k'''' => fun cont => Kind_decb k''' k'''' && WfActionT_unit regs (cont tt)
                                                                           | @NativeKind k'''' v => fun cont => false
                                                                           end
                                                      | @NativeKind k''' v => fun cont => false
                                                      end cont
                                                   end
                             | WriteReg r k' e cont => match lookup String.eqb r regs with
                                                     | None => false
                                                     | Some (existT k'' _) =>
                                                        match k',k'' with
                                                        | SyntaxKind k''',SyntaxKind k'''' => Kind_decb k''' k'''' && WfActionT_unit regs cont
                                                        | _,_ => false
                                                        end
                                                     end
                             | IfElse cond k' atrue afalse cont => (WfActionT_unit regs atrue) && (WfActionT_unit regs afalse) && (WfActionT_unit regs (cont tt))
                             | Sys l cont => WfActionT_unit regs cont
                             | Return e => true
                             (*| _ => false*)
                             end.

Fixpoint has_native {k} (a : ActionT (fun _ => unit) k) : bool :=
                         match a with
                         | MCall meth s e cont => has_native (cont tt)
                         | LetExpr k' e cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                | SyntaxKind k'' => fun cont => has_native (cont tt)
                                                | @NativeKind k'' v => fun cont => true
                                                end cont
                         | LetAction k a cont => has_native a || has_native (cont tt)
                         | ReadNondet k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                 | SyntaxKind k'' => fun cont => has_native (cont tt)
                                                 | @NativeKind k'' v => fun cont => true
                                                 end cont
                         | ReadReg r k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                | SyntaxKind k''' => fun cont => has_native (cont tt)
                                                | @NativeKind k''' v => fun cont => true
                                                end cont
                         | WriteReg r k' e cont => match k' with
                                                   | SyntaxKind k'' => has_native cont
                                                   | _ => true
                                                   end
                         | IfElse cond k' atrue afalse cont => (has_native atrue) || (has_native afalse) || (has_native (cont tt))
                         | Sys l cont => has_native cont
                         | Return e => false
                         (*| _ => false*)
                         end.
                        

Theorem test: forall regs k (a:ActionT (fun _ => unit) k), (WfActionT_unit regs a && negb(has_native a))=true -> @WfActionT_new regs (fun _ => unit) k a.
Proof.
  intros.
  induction a.
  - simpl.
    intros.
    eapply H0.
    simpl in H.
    simpl.
    destruct x.
    apply H.
  - simpl.
    intros.
    destruct k.
    + eapply H0.
      simpl in x.
      destruct x.
      simpl in H.
      apply H.
    + simpl.
      simpl in H.
      inversion H.
  - simpl.
    intros.
    split.
    + apply IHa.
      remember (WfActionT_unit regs a).
      destruct b.
      * remember (has_native a).
        destruct b.
        -- simpl in H.
           rewrite <- Heqb0 in H.
           simpl in H.
           rewrite andb_false_r in H.
           inversion H.
        -- reflexivity.
      * simpl in H.
        rewrite <- Heqb in H.
        rewrite andb_false_l in H.
        inversion H.
    + intros.
      eapply H0.
      destruct x.
      simpl in H.
      remember (WfActionT_unit regs (a0 tt)).
      destruct b.
      * remember (has_native (a0 tt)).
        destruct b.
        -- simpl in H.
           rewrite orb_true_r in H.
           simpl in H.
           rewrite andb_false_r in H.
           inversion H.
        -- reflexivity.
      * simpl in H.
        rewrite andb_false_r in H.
        rewrite andb_false_l in H.
        inversion H.
  - simpl.
    intros.
    destruct k.
    + eapply H0.
      simpl in x.
      destruct x.
      simpl in H.
      apply H.
    + simpl.
      simpl in H.
      inversion H.
  - simpl.
    intros.
    destruct k.
    + remember (lookup String.eqb r regs).
      destruct o.
      * destruct s.
        split.
        -- destruct x.
           ++ simpl in H.
              rewrite <- Heqo in H.
              remember (Kind_decb k k0).
              destruct b.
              ** symmetry in Heqb.
                 rewrite Kind_decb_eq in Heqb.
                 subst.
                 reflexivity.
              ** rewrite andb_false_l in H.
                 inversion H.
           ++ simpl in H.
              rewrite <- Heqo in H.
              rewrite andb_false_l in H.
              inversion H.
        -- simpl in H.
           rewrite <- Heqo in H.
           destruct x.
           ++ remember (Kind_decb k k0).
              destruct b.
              ** symmetry in Heqb.
                 rewrite Kind_decb_eq in Heqb.
                 subst.
                 simpl.
                 intros.
                 apply H0.
                 destruct x.
                 rewrite andb_true_l in H.
                 apply H.
              ** rewrite andb_false_l in H.
                 inversion H.
           ++ rewrite andb_false_l in H.
              inversion H.
      * simpl in H.
        rewrite <- Heqo in H.
        rewrite andb_false_l in H.
        inversion H.
    + simpl in H.
      rewrite andb_false_r in H.
      inversion H.
  - simpl.
    remember (lookup String.eqb r regs).
    destruct o.
    + destruct s.
      split.
      * destruct x.
        ++ simpl in H.
           rewrite <- Heqo in H.
           destruct k.
           -- remember (Kind_decb k k0).
              destruct b.
              ** symmetry in Heqb.
                 rewrite Kind_decb_eq in Heqb.
                 subst.
                 reflexivity.
              ** rewrite andb_false_l in H.
                 inversion H.
           -- rewrite andb_false_l in H.
              inversion H.
        ++ simpl in H.
           rewrite <- Heqo in H.
           destruct k.
           -- rewrite andb_false_l in H.
              inversion H.
           -- rewrite andb_false_l in H.
              inversion H.
      * simpl in H.
        rewrite <- Heqo in H.
        destruct k.
        ++ destruct x.
           -- apply IHa.
              simpl.
              remember (Kind_decb k k0).
              destruct b.
              ** rewrite andb_true_l in H.
                 apply H.
              ** rewrite andb_false_l in H.
                 inversion H.
           -- rewrite andb_false_l in H.
              inversion H.
        ++ rewrite andb_false_l in H.
           inversion H.
    + simpl in H.
      rewrite <- Heqo in H.
      rewrite andb_false_l in H.
      inversion H.
  - simpl in H.
    simpl.
    split.
    + apply IHa1.
      remember (WfActionT_unit regs a1).
      destruct b.
      * remember (has_native a1).
        destruct b.
        ++ rewrite orb_true_l in H.
           simpl in H.
           rewrite andb_false_r in H.
           inversion H.
        ++ reflexivity.
      * rewrite andb_false_l in H.
        inversion H.
    + split.
      * apply IHa2.
        remember (WfActionT_unit regs a2).
        destruct b.
        ++ remember (has_native a2).
           destruct b.
           -- rewrite orb_true_r in H.
              rewrite orb_true_l in H.
              simpl in H.
              rewrite andb_false_r in H.
              inversion H.
           -- reflexivity.
        ++ rewrite andb_false_r in H.
           rewrite andb_false_l in H.
           inversion H.
      * intros.
        destruct x.
        apply H0.
        remember (WfActionT_unit regs (a3 tt)).
        destruct b.
        ++ remember (has_native (a3 tt)).
           destruct b.
           -- rewrite orb_true_r in H.
              simpl in H.
              rewrite andb_false_r in H.
              inversion H.
           -- reflexivity.
        ++ rewrite andb_false_r in H.
           rewrite andb_false_l in H.
           inversion H.
  - simpl.
    apply IHa.
    simpl in H.
    apply H.
  - simpl.
    apply I.
Qed.

Axiom test2: forall regs k (a:forall ty k, ActionT ty k), @WfActionT_new regs (fun _ => unit) k (a (fun _ => unit) k) ->
                                                          forall ty k, @WfActionT_new regs ty k (a ty k).


