Require Import Kami.All.

Notation sz := 5.

Section Named.
  Variable name: string.
  Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0).

    Definition IncrementerImpl :=
      MODULE {
          Register ^"counter" : Bit sz <- Default
            with Register ^"counter1" : Bit sz <- Default
            with Register ^"isSending" : Bool <- true
                                             
            with Rule ^"send" :=
            ( Read isSending: Bool <- ^"isSending" ;
                Assert #isSending ;
                Read counter: Bit sz <- ^"counter" ;
                Call "counterVal"(#counter: _);
                Write ^"isSending" <- !#isSending ;
                Retv )

            with Rule ^"inc" :=
              ( Read isSending: Bool <- ^"isSending" ;
                  Assert !#isSending ;
                  Read counter: Bit sz <- ^"counter" ;
                  Write ^"counter" <- #counter + $1;
                  Write ^"isSending" <- !#isSending ;
                  Retv )
        }.

  Definition IncrementerSpec :=
    MODULE {
        Register ^"counter" : Bit sz <- Default
          with Register ^"counter1" : Bit sz <- Default
                                         
          with Rule ^"send_and_inc" :=
          ( Read counter: Bit sz <- ^"counter" ;
              Call "counterVal"(#counter: _);
              Write ^"counter" <- #counter + $1;
              Retv)
      }.

  Record Incrementer_invariant (impl spec: RegsT) : Prop :=
    { counterImpl: word sz ;
      isSending: bool ;
      implEq : impl = (^"counter", existT _ (SyntaxKind (Bit sz)) counterImpl)
                        :: (^"counter1", existT _ (SyntaxKind (Bit sz)) $0)
                        :: (^"isSending", existT _ (SyntaxKind Bool) isSending) :: nil ;
      specEq : spec = (^"counter", existT _ (SyntaxKind (Bit sz))
                                         (if isSending then counterImpl else counterImpl ^+ $1))
                        :: (^"counter1", existT  _ (SyntaxKind (Bit sz)) $0)
                        :: nil
    }.

  Theorem Incrementer_TraceInclusion:
    TraceInclusion (Base IncrementerImpl) (Base IncrementerSpec).
  Proof.
    discharge_simulation Incrementer_invariant; discharge_CommonRegisterAuto.
    - simplify_simulatingRule ^"send_and_inc"; subst.
      + rewrite (word0 x0); auto.
      + repeat discharge_string_dec.
        repeat (econstructor; eauto; simpl; subst).
        rewrite wzero_wplus; auto.
    - simplify_nilStep.
      econstructor; simpl; eauto; subst.
      rewrite negb_true_iff in *; subst.
      rewrite wzero_wplus; simpl; auto.
  Qed.
End Named.
