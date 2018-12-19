Require Import Kami.Syntax.
Import ListNotations.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Kami.PPlusProperties.

Theorem StepSimulation (imp spec : Mod) (simRel : RegsT -> RegsT -> Prop)
        (initRel : forall rimp : list RegT,
            Forall2 regInit rimp (getAllRegisters imp)
            -> exists rspec, Forall2 regInit rspec (getAllRegisters spec)
                             /\ simRel rimp rspec) 
        (NoDupRegs : NoDup (map fst (getAllRegisters imp)))
        (stepSimulationNonZero : forall oImp lImp oImp',
            Step imp oImp lImp ->
            lImp <> nil ->
            UpdRegs (map fst lImp) oImp oImp' ->
            forall oSpec,
              simRel oImp oSpec ->
              exists lSpec oSpec',
                Step spec oSpec lSpec /\
                UpdRegs (map fst lSpec) oSpec oSpec' /\
                simRel oImp' oSpec' /\ WeakInclusion lImp lSpec) :
  TraceInclusion imp spec.
Proof.
  eauto using _StepSimulation.
Qed.

Theorem simulationZero (imp spec : BaseModule) (simRel : RegsT -> RegsT -> Prop)
        (initRel : forall rimp : list RegT,
            Forall2 regInit rimp (getAllRegisters imp)
            -> exists rspec, Forall2 regInit rspec (getAllRegisters spec)
                             /\ simRel rimp rspec) 
        (NoDupRegs : NoDup (map fst (getAllRegisters imp)))
        (NoMeths : getMethods imp = [])
        (NoMethsSpec: getMethods spec = [])
        (simulation : forall oImp uImp rleImp csImp oImp',
            Substeps imp oImp [(uImp, (Rle rleImp, csImp))] ->
            UpdRegs [uImp] oImp oImp' ->
            forall oSpec,
              simRel oImp oSpec ->
              (getKindAttr oSpec = getKindAttr (getRegisters spec) /\ simRel oImp' oSpec
               /\ csImp = [])
              \/ exists uSpec rleSpec oSpec',
                  Substeps spec oSpec [(uSpec, (Rle rleSpec, csImp))] /\
                  UpdRegs [uSpec] oSpec oSpec' /\
                  simRel oImp' oSpec') :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationZero.
Qed.

Theorem flatten_WfMod m :
  WfMod m -> WfMod (flatten m).
Proof.
  eauto using _flatten_WfMod.
Qed.

Definition flatten_ModWf m := flattened_ModWf m.

Theorem TraceInclusion_flatten_r (m : ModWf) :
  TraceInclusion m (flatten_ModWf m).
Proof.
  eauto using _TraceInclusion_flatten_r.
Qed.

Theorem TraceInclusion_flatten_l (m : ModWf) :
  TraceInclusion (flatten_ModWf m) m.
Proof.
  eauto using _TraceInclusion_flatten_l.
Qed.

Theorem ModularSubstitution (a b a' b' : Mod)
        (SameList_a : forall x,
            (In x (map fst (getAllMethods a)) /\
             ~ In x (getHidden a)) <->
            (In x (map fst (getAllMethods a')) /\
             ~ In x (getHidden a')))
        (SameList_b : forall x,
            (In x (map fst (getAllMethods b)) /\
             ~ In x (getHidden b)) <->
            (In x (map fst (getAllMethods b')) /\
             ~ In x (getHidden b')))
        (wfAConcatB : WfMod (ConcatMod a b))
        (wfA'ConcatB' : WfMod (ConcatMod a' b')):
  TraceInclusion a a' ->
  TraceInclusion b b' ->
  TraceInclusion (ConcatMod a b) (ConcatMod a' b').
Proof.
  eauto using _ModularSubstitution.
Qed.

Theorem simulationZeroAct (imp spec : BaseModuleWf) (simRel : RegsT -> RegsT -> Prop)
        (simRelGood : forall oImp oSpec : RegsT,
        simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec))
        (initRel : forall rimp : list RegT,
            Forall2 regInit rimp (getAllRegisters imp)
            -> exists rspec, Forall2 regInit rspec (getAllRegisters spec)
                             /\ simRel rimp rspec) 
        (NoMeths : getMethods imp = [])
        (NoMethsSpec: getMethods spec = [])
        (simulation : forall oImp rImp uImp rleImp csImp oImp' aImp,
            In (rleImp, aImp) (getRules imp) ->
            SemAction oImp (aImp type) rImp uImp csImp WO ->
            UpdRegs [uImp] oImp oImp' ->
            forall oSpec,
              simRel oImp oSpec ->
              (simRel oImp' oSpec /\ csImp = [])
              \/ (exists rleSpec aSpec,
                  In (rleSpec, aSpec) (getRules spec) /\
                  exists rSpec uSpec,
                    SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                    exists oSpec',
                      UpdRegs [uSpec] oSpec oSpec' /\
                      simRel oImp' oSpec')):
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationZeroAct.
Qed.

Theorem simulationGen (imp spec : BaseModuleWf) (NoSelfCalls : NoSelfCallBaseModule spec)
        (simRel : RegsT -> RegsT -> Prop)
        (simRelGood : forall oImp oSpec : RegsT,
            simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec))
        (initRel : forall rimp : list RegT,
            Forall2 regInit rimp (getAllRegisters imp)
            -> exists rspec, Forall2 regInit rspec (getAllRegisters spec)
                             /\ simRel rimp rspec)
        (simulationRule :
           forall oImp rImp uImp rleImp csImp oImp' aImp,
             In (rleImp, aImp) (getRules imp) ->
             SemAction oImp (aImp type) rImp uImp csImp WO ->
             UpdRegs [uImp] oImp oImp' ->
             forall oSpec,
               simRel oImp oSpec ->
               ((simRel oImp' oSpec /\ csImp = []) \/
                (exists rleSpec aSpec,
                    In (rleSpec, aSpec) (getRules spec) /\
                    exists rSpec uSpec,
                      SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                      exists oSpec',
                        UpdRegs [uSpec] oSpec oSpec' /\
                        simRel oImp' oSpec')))
        (simulationMeth :
           forall oImp rImp uImp meth csImp oImp' sign aImp arg ret,
             In (meth, existT _ sign aImp) (getMethods imp) ->
             SemAction oImp (aImp type arg) rImp uImp csImp ret ->
             UpdRegs [uImp] oImp oImp' ->
             forall oSpec,
               simRel oImp oSpec ->
               exists aSpec rSpec uSpec,
                 In (meth, existT _ sign aSpec) (getMethods spec) /\
                 SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                 exists oSpec',
                   UpdRegs [uSpec] oSpec oSpec' /\
                   simRel oImp' oSpec')
        (notMethMeth :
           forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
             SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2))
        (notRuleMeth :
           forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (rleImpl1, aImp1) (getRules imp) ->
             SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2)) :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationGen.
Qed.

Theorem simulationGeneralEx (imp spec: BaseModuleWf) (NoSelfCalls: NoSelfCallBaseModule spec)
        (simRel: RegsT -> RegsT -> Prop)
        (simRelGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec))
        (simRelImpGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp))
        (initRel: forall rimp,
            Forall2 regInit rimp (getRegisters imp) ->
            exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec)
        (simulationRule:
           forall oImp rImp uImp rleImp csImp aImp,
             In (rleImp, aImp) (getRules imp) ->
             SemAction oImp (aImp type) rImp uImp csImp WO ->
             forall oSpec,
               simRel oImp oSpec ->
               ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
                (exists rleSpec aSpec,
                    In (rleSpec, aSpec) (getRules spec) /\
                    exists rSpec uSpec,
                      SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                      exists oSpec',
                        UpdRegs [uSpec] oSpec oSpec' /\
                        simRel (doUpdRegs uImp oImp) oSpec')))
        (simulationMeth:
           forall oImp rImp uImp meth csImp sign aImp arg ret,
             In (meth, existT _ sign aImp) (getMethods imp) ->
             SemAction oImp (aImp type arg) rImp uImp csImp ret ->
             forall oSpec,
               simRel oImp oSpec ->
               exists aSpec rSpec uSpec,
                 In (meth, existT _ sign aSpec) (getMethods spec) /\
                 SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                 exists oSpec',
                   UpdRegs [uSpec] oSpec oSpec' /\
                   simRel (doUpdRegs uImp oImp) oSpec')
        (notMethMeth:
           forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
             SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2))
        (notRuleMeth:
           forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (rleImpl1, aImp1) (getRules imp) ->
             SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2)) :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationGeneralEx.
Qed.

Theorem simulationZeroA (imp spec: BaseModuleWf) (simRel: RegsT -> RegsT -> Prop)
        (simRelGood: forall oImp oSpec,
            simRel oImp oSpec ->
            getKindAttr oSpec = getKindAttr (getRegisters spec))
        (simRelImpGood: forall oImp oSpec,
            simRel oImp oSpec ->
            getKindAttr oImp = getKindAttr (getRegisters imp))
        (initRel: forall rimp,
            Forall2 regInit rimp (getRegisters imp) ->
            exists rspec, Forall2 regInit rspec (getRegisters spec) /\
                          simRel rimp rspec)
        (NoMeths: getMethods imp = [])
        (NoMethsSpec: getMethods spec = [])
        (simulation:
           forall oImp rImp uImp rleImp csImp aImp,
             In (rleImp, aImp) (getRules imp) ->
             SemAction oImp (aImp type) rImp uImp csImp WO ->
             forall oSpec,
               simRel oImp oSpec ->
               ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
                (exists rleSpec aSpec,
                    In (rleSpec, aSpec) (getRules spec) /\
                    exists rSpec uSpec,
                      SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                      exists oSpec',
                        UpdRegs [uSpec] oSpec oSpec' /\
                        simRel (doUpdRegs uImp oImp) oSpec'))) :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationZeroA.
Qed.

Theorem simulationGeneral (imp spec: BaseModuleWf) (NoSelfCalls: NoSelfCallBaseModule spec)
        (simRel: RegsT -> RegsT -> Prop)
        (simRelGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec))
        (simRelImpGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp))
        (initRel: forall rimp,
            Forall2 regInit rimp (getRegisters imp) ->
            exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec)
        (simulationRule:
           forall oImp rImp uImp rleImp csImp aImp,
             In (rleImp, aImp) (getRules imp) ->
             SemAction oImp (aImp type) rImp uImp csImp WO ->
             forall oSpec,
               simRel oImp oSpec ->
               ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
                (exists rleSpec aSpec,
                    In (rleSpec, aSpec) (getRules spec) /\
                    exists rSpec uSpec,
                      SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                      simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))))
        (simulationMeth:
           forall oImp rImp uImp meth csImp sign aImp arg ret,
             In (meth, existT _ sign aImp) (getMethods imp) ->
             SemAction oImp (aImp type arg) rImp uImp csImp ret ->
             forall oSpec,
               simRel oImp oSpec ->
               exists aSpec rSpec uSpec,
                 In (meth, existT _ sign aSpec) (getMethods spec) /\
                 SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                 simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))
        (notMethMeth:
           forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
             SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2))
        (notRuleMeth:
           forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
                  rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
             In (rleImpl1, aImp1) (getRules imp) ->
             SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
             In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
             SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
             exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2)) :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationGeneral.
Qed.

Theorem simulationZeroAction (imp spec: BaseModuleWf) (simRel: RegsT -> RegsT -> Prop)
        (simRelGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec))
        (simRelImpGood: forall oImp oSpec,
            simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp))
        (initRel: forall rimp,
            Forall2 regInit rimp (getRegisters imp) ->
            exists rspec, Forall2 regInit rspec (getRegisters spec) /\
                          simRel rimp rspec)
        (NoMeths: getMethods imp = [])
        (NoMethsSpec: getMethods spec = [])
        (simulation:
           forall oImp rImp uImp rleImp csImp aImp,
             In (rleImp, aImp) (getRules imp) ->
             SemAction oImp (aImp type) rImp uImp csImp WO ->
             forall oSpec,
               simRel oImp oSpec ->
               ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
                (exists rleSpec aSpec,
                    In (rleSpec, aSpec) (getRules spec) /\
                    exists rSpec uSpec,
                      SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                      simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec)))) :
  TraceInclusion (Base imp) (Base spec).
Proof.
  eauto using _simulationZeroAction.
Qed.

Theorem WfMod_Concat_assoc_1 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod m1 (ConcatMod m2 m3)) -> WfMod (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  eauto using WfConcatAssoc1.
Qed.

Theorem WfMod_Concat_assoc_2 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) -> WfMod (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  eauto using WfConcatAssoc2.
Qed.

Theorem WfMod_BreakDownFile (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedBaseFile (fst (snd (separateMod m)))).
Proof.
  eauto using WfModBreakDownFile.
Qed.

Theorem WfMod_BreakDownMod (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedBaseMod (snd (snd (separateMod m)))).
Proof.
  eauto using WfModBreakDownMod.
Qed.

Theorem WfMod_merge (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedMod (separateMod m)).
Proof.
  eauto using merged_WellFormed.
Qed.

Theorem WfMod_getFlat (m : Mod) :
  WfMod m -> WfMod (getFlat m).
Proof.
  eauto using _WfMod_getFlat.
Qed.

Definition merge_ModWf m := WfMergedMod m.

Theorem TraceInclusion_merge_r (m : ModWf) :
  TraceInclusion m (merge_ModWf m).
Proof.
  eauto using TraceInclusion_Merge_l.
Qed.

Theorem TraceInclusion_merge_l (m : ModWf) :
  TraceInclusion (merge_ModWf m) m.
Proof.
  eauto using TraceInclusion_Merge_r.
Qed.

Theorem TraceInclusion_ConcatMod_comm (m1 m2 : Mod) : 
  WfMod (ConcatMod m1 m2) -> TraceInclusion (ConcatMod m1 m2) (ConcatMod m2 m1).
Proof.
  eauto using ConcatMod_comm.
Qed.

Theorem TraceInclusion_ConcatMod_assoc_1 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) ->
  TraceInclusion (ConcatMod m1 (ConcatMod m2 m3)) (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  eauto using ConcatModAssoc1.
Qed.

Theorem TraceInclusion_ConcatMod_assoc_2 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) ->
  TraceInclusion (ConcatMod (ConcatMod m1 m2) m3) (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  eauto using ConcatModAssoc2.
Qed.

Theorem TraceInclusion_inlineSingle_Rule_BaseModule_r (m : BaseModule) (f : DefMethT) (rn : string):
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion m (inlineSingle_Rule_BaseModule f rn m).
Proof.
  eauto using TraceInclusion_inlining_Rules_r.
Qed.

Theorem TraceInclusion_inlineSingle_Meth_BaseModule_r (m : BaseModule) (f : DefMethT) (gn : string) :
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion m (inlineSingle_Meth_BaseModule f gn m).
Proof.
  eauto using TraceInclusion_inlining_Meth_r.
Qed.

Theorem TraceInclusion_inline_Meth_transform_r (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  forall i : nat,
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (transform_nth_right (inlineSingle_Meth f) i meths)).
Proof.
  eauto using inline_meth_transform.
Qed.

Theorem TraceInclusion_inline_Rule_transform_r (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  forall i : nat,
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (transform_nth_right (inlineSingle_Rule f) i rules) meths).
Proof.
  eauto using inline_rule_transform.
Qed.

Theorem TraceInclusion_inline_Meth_fold_right_r (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall xs : list nat,
    In f meths ->
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs)).
Proof.
  eauto using inline_meth_fold_right.
Qed.

Theorem TraceInclusion_inline_Rule_fold_right_r (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall xs : list nat,
    In f meths ->
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths).
Proof.
  eauto using inline_rule_fold_right.
Qed.

Theorem TraceInclusion_inlineSingle_Rule_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs (map (inlineSingle_Rule f) rules) meths).
Proof.
  eauto using TraceInclusion_inline_BaseModule_rules.
Qed.

Theorem TraceInclusion_inlineSingle_Meth_r (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs rules (map (inlineSingle_Meth f) meths)).
Proof.
  eauto using TraceInclusion_inline_BaseModule_meths.
Qed.

Theorem TraceInclusion_inlineSingle_BaseModule_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths) (inlineSingle_BaseModule f regs rules meths).
Proof.
  eauto using TraceInclusion_inline_BaseModule_all.
Qed.

Theorem TraceInclusion_inlineSingle_Rules_pos_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall n : nat,
    WfMod (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths) /\
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths).
Proof.
  eauto using TraceInclusion_inlineSingle_pos_Rules.
Qed.

Theorem TraceInclusion_inlineAll_Rules_BaseMod_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (BaseMod regs (inlineAll_Rules meths rules) meths) /\
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs (inlineAll_Rules meths rules) meths).
Proof.
  eauto using TraceInclusion_inlineAll_pos_Rules.
Qed.

Theorem TraceInclusion_inlineSingle_Meths_pos_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall n : nat,
    WfMod (BaseMod regs rules (inlineSingle_Meths_pos meths n)) /\
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (inlineSingle_Meths_pos meths n)).
Proof.
  eauto using TraceInclusion_inlineSingle_pos_Meths.
Qed.

Theorem TraceInclusion_inlineAll_Meths_BaseMod_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (BaseMod regs rules (inlineAll_Meths meths)) /\
  TraceInclusion (BaseMod regs rules meths) (BaseMod regs rules (inlineAll_Meths meths)).
Proof.
  eauto using TraceInclusion_inlineAll_pos_Meths.
Qed.

Theorem TraceInclusion_inlineAll_All_r (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (inlineAll_All regs rules meths) /\
  TraceInclusion (BaseMod regs rules meths) (inlineAll_All regs rules meths).
Proof.
  eauto using TraceInclusion_inlineAll_pos.
Qed.

Theorem WfMod_flatten_inline_everything (m : ModWf) :
  WfMod (flatten_inline_everything m).
Proof.
  eauto using WfCreateHide_Mod.
Qed.

Theorem TraceInclusion_flatten_inline_everything_r (m : ModWf) :
  TraceInclusion m (inlined_ModWf m).
Proof.
  eauto using _TraceInclusion_flatten_inline_everything_r.
Qed.

Theorem WfMod_inlineSingle_Rule_map {f : DefMethT} {m : ModWf} (inMeths : In f (getAllMethods m)):
  WfMod (createHide (inlineSingle_Rule_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  eauto using inlineSingle_Rule_map_Wf.
Qed.

Theorem WfMod_inlineSingle_Meth_map {f : DefMethT} {m : ModWf} (inMeths : In f (getAllMethods m)) :
  WfMod (createHide (inlineSingle_Meth_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  eauto using inlineSingle_Meth_map_Wf.
Qed.

Theorem TraceInclusion_inlineSingle_Rule_map {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)):
  TraceInclusion m (inlineSingle_Rule_map_ModWf inMeths).
Proof.
  eauto using inlineSingle_Rule_map_TraceInclusion.
Qed.

Theorem TraceInclusion_inlineSingle_Meth_map {m : ModWf}  {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Meth_map_ModWf inMeths).
Proof.
  eauto using inlineSingle_Meth_map_TraceInclusion.
Qed.

Theorem WfMod_inlineSingle_Module {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  WfMod (inlineSingle_Module f m).
Proof.
  eauto using inlineSingle_Module_Wf.
Qed.

Theorem TraceInclusion_inlineSingle_Module_ModWf_r {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Module_ModWf inMeths).
Proof.
  eauto using inlineSingle_BaseModule_TraceInclusion.
Qed.

Theorem WfMod_inlineSingle_BaseModule_nth_Meth {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod
    (createHide
       (inlineSingle_BaseModule_nth_Meth f (getAllRegisters m) 
                                         (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  eauto using inlineSingle_BaseModule_nth_Meth_Wf.
Qed.

Theorem TraceInclusion_inlineSingle_BaseModule_nth_Meth_r {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Meth_ModWf inMeths xs).
Proof.
  eauto using inlineSingle_BaseModule_nth_Meth_TraceInclusion.
Qed.

Theorem WfMod_inlineSingle_BaseModule_nth_Rule {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod
    (createHide
       (inlineSingle_BaseModule_nth_Rule f (getAllRegisters m) 
                                         (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  eauto using inlineSingle_BaseModule_nth_Rule_Wf.
Qed.

Theorem TraceInclusion_inlineSingle_BaseModule_nth_Rule_r {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Rule_ModWf inMeths xs).
Proof.
  eauto using inlineSingle_BaseModule_nth_Rule_TraceInclusion.
Qed.

Theorem WfMod_inlineAll_Rules (m : ModWf):
  WfMod (inlineAll_Rules_Mod m).
Proof.
  eauto using inlineAll_Rules_Wf.
Qed.

Theorem TraceInclusion_inlineAll_Rules_r (m : ModWf) :
  TraceInclusion m (inlineAll_Rules_ModWf m).
Proof.
  eauto using inlineAll_Rules_TraceInclusion.
Qed.

Theorem WfMod_inlineAll_Meths (m : ModWf) :
  WfMod (inlineAll_Meths_Mod m).
Proof.
  eauto using inlineAll_Meths_Wf.
Qed.

Theorem TraceInclusion_inlineAll_Meths_r (m : ModWf) :
  TraceInclusion m (inlineAll_Meths_ModWf m).
Proof.
  eauto using inlineAll_Meths_TraceInclusion.
Qed.

Theorem WfMod_flatten_inline_remove (m : ModWf) :
  WfMod (flatten_inline_remove m).
Proof.
  eauto using flatten_inline_remove_Wf.
Qed.

Theorem TraceInclusion_removeHides_createHide (m : BaseModuleWf) (l : list string)
        (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (removeHides_ModWf m l) (createHide_ModWf m subList).
Proof.
  eauto using removeHides_createHide_TraceInclusion.
Qed.

Theorem TraceInclusion_createHide_removeHides (m : BaseModuleWf) (l : list string)
        (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (createHide_ModWf m subList) (removeHides_ModWf m l).
Proof.
  eauto using createHide_removeHides_TraceInclusion.
Qed.

Theorem TraceInclusion_flatten_inline_everything_flatten_inline_remove (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_everything m) (flatten_inline_remove_ModWf m).
Proof.
  eauto using flatten_inline_remove_TraceInclusion.
Qed.

Theorem TraceInclusion_inlineSingle_Rule_BaseModule_l (m : BaseModule) (f : DefMethT) (rn : string):
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion (inlineSingle_Rule_BaseModule f rn m) m.
Proof.
  eauto using TraceInclusion_inlining_Rules_l.
Qed.

Theorem TraceInclusion_inlineSingle_Meth_BaseModule_l (m : BaseModule) (f : DefMethT) (gn : string):
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion (inlineSingle_Meth_BaseModule f gn m) m.
Proof.
  eauto using TraceInclusion_inlining_Meths_l.
Qed.