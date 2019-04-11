Require Import Kami.All.


Notation sz := 5.

Section Named.
  Variable name: string.
  Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0).

    Definition IncrementerImpl :=
      MODULE_WF {
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
    MODULE_WF {
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
End Named.

Theorem Incrementer_TraceInclusion (name: string) :
  TraceInclusion (Base (IncrementerImpl name)) (Base (IncrementerSpec name)).
Proof.
  discharge_simulationGeneral (Incrementer_invariant name); discharge_CommonRegisterAuto.
  - right; do 2 (do 2 eexists; repeat split; eauto; simpl in * ).
    + discharge_SemAction; subst; auto.
    + repeat discharge_string_dec.
      repeat (econstructor; eauto; simpl; subst).
      rewrite wzero_wplus; auto.
  - left; split; auto; simpl in *.
    discharge_string_dec.
    repeat (econstructor; eauto; simpl; subst).
    rewrite negb_true_iff in *; subst.
    rewrite wzero_wplus; simpl; auto.
Qed.
