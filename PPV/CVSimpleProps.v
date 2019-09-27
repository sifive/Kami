Require Import Kami.All.
Require Import Kami.Notations.
Require Import Kami.PPV.CVSimpleSem.
Require Import Kami.PPV.CVSimple.
(* Section PropertiesSimple *)

Lemma RME_Simple_RME_Equiv map:
  forall old upds,
    Sem_RME_simple (RME_simple_of_RME map) (old, upds) ->
    SemRegMapExpr map (old, upds).
Proof.
  induction map; intros; try (inv H; EqDep_subst).
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
Qed.

Lemma CA_Simple_CA_Equiv {k : Kind} (ca : CompActionT type (RegsT * list RegsT) k) :
  forall regMap calls val,
    SemCA_simple (CA_simple_of_CA ca) regMap calls val ->
    SemCompActionT ca regMap calls val.
Proof.
  induction ca; intros; try ((inv H0 || inv H); EqDep_subst).
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto using RME_Simple_RME_Equiv.
  - econstructor 7; eauto.
    destruct regMap; inv HRegMapWf; econstructor; eauto using RME_Simple_RME_Equiv.
  - econstructor 8; eauto.
  - econstructor 9; eauto using RME_Simple_RME_Equiv.
  - inv HSemCA_simple; simpl in *; EqDep_subst; rewrite unifyWO in *.
    inv HSemCA_simple_a; EqDep_subst.
Admitted.  

(* End PropertiesSimple *)

