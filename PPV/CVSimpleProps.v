Require Import Kami.All.
Require Import Kami.Notations.
Require Import Kami.PPV.CVSimpleSem.
Require Import Kami.PPV.CVSimple.
Require Import Kami.CVProperties.
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
    destruct regMap_a; inv HRegMapWf; inv H0; EqDep_subst.
    + inv HUpdate; EqDep_subst.
      econstructor 10; eauto using RME_Simple_RME_Equiv.
      * econstructor; eauto.
        econstructor; eauto using RME_Simple_RME_Equiv.
      * econstructor 10; eauto using RME_Simple_RME_Equiv.
        econstructor; eauto.
        eapply SemUpdRegMapFalse; eauto using RME_Simple_RME_Equiv.
    + econstructor 11; eauto using RME_Simple_RME_Equiv.
      econstructor; eauto using RME_Simple_RME_Equiv.
  - inv HSemCA_simple; simpl in *; EqDep_subst; rewrite unifyWO in *.
    inv HSemCA_simple_a; EqDep_subst.
    destruct regMap_a; inv HRegMapWf; inv H0; EqDep_subst;[|discriminate].
    econstructor 12; eauto.
    econstructor; eauto using RME_Simple_RME_Equiv.
  - inv HSemCA_simple; simpl in *; EqDep_subst; rewrite unifyWO in *.
    inv HSemCA_simple_a; EqDep_subst.
    destruct regMap_a; inv HRegMapWf; inv H0; EqDep_subst;[discriminate|].
    econstructor 13; eauto using RME_Simple_RME_Equiv.
    econstructor; eauto using RME_Simple_RME_Equiv.
  - econstructor 14; eauto using RME_Simple_RME_Equiv.
  - econstructor 15; eauto using RME_Simple_RME_Equiv.
Qed.

Lemma CA_Simple_Trace_CA_Trace_Equiv {k : Kind} (ca : CompActionT type (RegsT * list RegsT) k) :
  forall regInits o lupds lcalls,
    SemCA_simple_Trace (CA_simple_of_CA ca) regInits o lupds lcalls ->
    SemCompTrace ca regInits o lupds lcalls.
Proof.
  induction 1;[econstructor 1 | econstructor 2]; eauto using CA_Simple_CA_Equiv.
Qed.

Lemma CA_Simple_TraceEquiv (b : BaseModule) (lrf : list RegFileBase) o :
  let m := inlineAll_All_mod (mergeSeparatedSingle b lrf) in
  let regInits := (getRegisters b) ++ (concat (map getRegFileRegisters lrf)) in
  forall rules lupds lcalls
         (HWfMod : WfMod (mergeSeparatedSingle b lrf))
         (HNoSelfCallsBase : NoSelfCallBaseModule b),
    SubList rules (getRules b) ->
    SemCA_simple_Trace (CA_simple_of_CA (compileRulesRf type (o, nil) rules lrf)) regInits o lupds lcalls ->
    (forall upds u, In upds lupds -> In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists (lss : list (list (list FullLabel))),
      Forall2 (fun x y => x = (map getLabelUpds y)) lupds lss /\
      (forall x, In x lss -> (map Rle (map fst (rev rules))) = getLabelExecs (concat x)) /\ 
      Forall2 (fun x y => x = concat (map getLabelCalls (rev y))) lcalls lss /\
      Trace m o (concat lss).
Proof.
  intros; eapply CompTraceEquiv; eauto using CA_Simple_Trace_CA_Trace_Equiv.
Qed.
  
(* End PropertiesSimple *)

