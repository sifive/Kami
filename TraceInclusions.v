Require Import Kami.Syntax.
Import ListNotations.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Kami.PPlusProperties.

Theorem _StepSimulation (imp spec : Mod) (simRel : RegsT -> RegsT -> Prop)
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
  eauto using StepSimulation.
Qed.

Theorem _simulationZero (imp spec : BaseModule) (simRel : RegsT -> RegsT -> Prop)
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
  eauto using simulationZero.
Qed.

Theorem _flatten_WfMod m :
  WfMod m -> WfMod (flatten m).
Proof.
  eauto using flatten_WfMod.
Qed.

Theorem _TraceInclusion_flatten_r (m : ModWf) :
  TraceInclusion m (flattened_ModWf m).
Proof.
  eauto using TraceInclusion_flatten_r.
Qed.

Theorem _TraceInclusion_flatten_l (m : ModWf) :
  TraceInclusion (flattened_ModWf m) m.
Proof.
  eauto using TraceInclusion_flatten_l.
Qed.

Theorem _ModularSubstitution (a b a' b' : Mod)
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
  eauto using ModularSubstitution.
Qed.

Theorem _simulationZeroAct (imp spec : BaseModuleWf) (simRel : RegsT -> RegsT -> Prop)
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
  eauto using simulationZeroAct.
Qed.

Theorem _simulationGen (imp spec : BaseModuleWf) (NoSelfCalls : NoSelfCallBaseModule spec)
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
  eauto using simulationGen.
Qed.

Theorem _simulationGeneralEx (imp spec: BaseModuleWf) (NoSelfCalls: NoSelfCallBaseModule spec)
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
  eauto using simulationGeneralEx.
Qed.

Theorem _simulationZeroA (imp spec: BaseModuleWf) (simRel: RegsT -> RegsT -> Prop)
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
  eauto using simulationZeroA.
Qed.

Theorem _simulationGeneral (imp spec: BaseModuleWf) (NoSelfCalls: NoSelfCallBaseModule spec)
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
  eauto using simulationGeneral.
Qed.

Theorem _simulationZeroAction (imp spec: BaseModuleWf) (simRel: RegsT -> RegsT -> Prop)
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
  eauto using simulationZeroAction.
Qed.

Theorem _WfConcatAssoc1 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod m1 (ConcatMod m2 m3)) -> WfMod (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  eauto using WfConcatAssoc1.
Qed.

Theorem _WfConcatAssoc2 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) -> WfMod (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  eauto using WfConcatAssoc2.
Qed.

Theorem _WfModBreakDownFile (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedBaseFile (fst (snd (separateMod m)))).
Proof.
  eauto using WfModBreakDownFile.
Qed.

Theorem _WfModBreakDownMod (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedBaseMod (snd (snd (separateMod m)))).
Proof.
  eauto using WfModBreakDownMod.
Qed.

Theorem _merged_WellFormed (m : Mod) :
  WfMod m -> WfMod (mergeSeparatedMod (separateMod m)).
Proof.
  eauto using merged_WellFormed.
Qed.

Theorem _WfMod_getFlat (m : Mod) :
  WfMod m -> WfMod (getFlat m).
Proof.
  eauto using WfMod_getFlat.
Qed.

Theorem _TraceInclusion_Merge_l (m : ModWf) :
  TraceInclusion m (WfMergedMod m).
Proof.
  eauto using TraceInclusion_Merge_l.
Qed.

Theorem _TraceInclusion_Merge_r (m : ModWf) :
  TraceInclusion (WfMergedMod m) m.
Proof.
  eauto using TraceInclusion_Merge_r.
Qed.

Theorem _ConcatMod_comm (m1 m2 : Mod) : 
  WfMod (ConcatMod m1 m2) -> TraceInclusion (ConcatMod m1 m2) (ConcatMod m2 m1).
Proof.
  eauto using ConcatMod_comm.
Qed.

Theorem _ConcatModAssoc1 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) ->
  TraceInclusion (ConcatMod m1 (ConcatMod m2 m3)) (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  eauto using ConcatModAssoc1.
Qed.

Theorem _ConcatModAssoc2 (m1 m2 m3 : Mod) :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) ->
  TraceInclusion (ConcatMod (ConcatMod m1 m2) m3) (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  eauto using ConcatModAssoc2.
Qed.

(*
PPlusProperties.v:Theorem flatten_inline_remove_TraceInclusion (m : ModWf) :
 *)

Theorem _StrongPPlusTraceInclusion_PPlusTraceInclusion (m m' : BaseModule) :
  StrongPPlusTraceInclusion m m' -> PPlusTraceInclusion m m'.
Proof.
  eauto using StrongPPlusTraceInclusion_PPlusTraceInclusion.
Qed.

Theorem _PPlusTraceInclusion_PTraceInclusion (m m' : BaseModule) :
  PPlusTraceInclusion m m' -> PTraceInclusion m m'.
Proof.
  eauto using PPlusTraceInclusion_PTraceInclusion.
Qed.

Theorem _PPlusTraceInclusion_TraceInclusion (m m' : BaseModule) :
  WfMod m ->
  WfMod m' ->
  PPlusTraceInclusion m m' ->
  TraceInclusion m m'.
Proof.
  eauto using PPlusTraceInclusion_TraceInclusion.
Qed.

Theorem _TraceInclusion_inlining_Rules_r (m : BaseModule) (f : DefMethT) (rn : string):
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion m (inlineSingle_Rule_BaseModule f rn m).
Proof.
  eauto using TraceInclusion_inlining_Rules_r.
Qed.

Theorem _TraceInclusion_inlining_Meth_r (m : BaseModule) (f : DefMethT) (gn : string) :
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion m (inlineSingle_Meth_BaseModule f gn m).
Proof.
  eauto using TraceInclusion_inlining_Meth_r.
Qed.

Theorem _inline_meth_transform (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  forall i : nat,
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (transform_nth_right (inlineSingle_Meth f) i meths)).
Proof.
  eauto using inline_meth_transform.
Qed.

Theorem _inline_rule_transform (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  forall i : nat,
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (transform_nth_right (inlineSingle_Rule f) i rules) meths).
Proof.
  eauto using inline_rule_transform.
Qed.

Theorem _inline_meth_fold_right (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall xs : list nat,
    In f meths ->
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs)).
Proof.
  eauto using inline_meth_fold_right.
Qed.

Theorem _inline_rule_fold_right (f : DefMethT) (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall xs : list nat,
    In f meths ->
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths).
Proof.
  eauto using inline_rule_fold_right.
Qed.

Theorem _TraceInclusion_inline_BaseModule_rules (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs (map (inlineSingle_Rule f) rules) meths).
Proof.
  eauto using TraceInclusion_inline_BaseModule_rules.
Qed.

Theorem _TraceInclusion_inline_BaseModule_meths (regs : list RegInitT)
        (rules : list RuleT) (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs rules (map (inlineSingle_Meth f) meths)).
Proof.
  eauto using TraceInclusion_inline_BaseModule_meths.
Qed.

Theorem _TraceInclusion_inline_BaseModule_all (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT) (f : DefMethT):
  WfMod (BaseMod regs rules meths) ->
  In f meths ->
  TraceInclusion (BaseMod regs rules meths) (inlineSingle_BaseModule f regs rules meths).
Proof.
  eauto using TraceInclusion_inline_BaseModule_all.
Qed.

Theorem _TraceInclusion_inlineSingle_pos_Rules (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall n : nat,
    WfMod (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths) /\
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths).
Proof.
  eauto using TraceInclusion_inlineSingle_pos_Rules.
Qed.

Theorem _TraceInclusion_inlineAll_pos_Rules (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (BaseMod regs (inlineAll_Rules meths rules) meths) /\
  TraceInclusion (BaseMod regs rules meths)
                 (BaseMod regs (inlineAll_Rules meths rules) meths).
Proof.
  eauto using TraceInclusion_inlineAll_pos_Rules.
Qed.

Theorem _TraceInclusion_inlineSingle_pos_Meths (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  forall n : nat,
    WfMod (BaseMod regs rules (inlineSingle_Meths_pos meths n)) /\
    TraceInclusion (BaseMod regs rules meths)
                   (BaseMod regs rules (inlineSingle_Meths_pos meths n)).
Proof.
  eauto using TraceInclusion_inlineSingle_pos_Meths.
Qed.

Theorem _TraceInclusion_inlineAll_pos_Meths (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (BaseMod regs rules (inlineAll_Meths meths)) /\
  TraceInclusion (BaseMod regs rules meths) (BaseMod regs rules (inlineAll_Meths meths)).
Proof.
  eauto using TraceInclusion_inlineAll_pos_Meths.
Qed.

Theorem _TraceInclusion_inlineAll_pos (regs : list RegInitT) (rules : list RuleT)
        (meths : list DefMethT):
  WfMod (BaseMod regs rules meths) ->
  WfMod (inlineAll_All regs rules meths) /\
  TraceInclusion (BaseMod regs rules meths) (inlineAll_All regs rules meths).
Proof.
  eauto using TraceInclusion_inlineAll_pos.
Qed.

Theorem _WfCreateHide_Mod (m : ModWf) :
  WfMod (flatten_inline_everything m).
Proof.
  eauto using WfCreateHide_Mod.
Qed.

Theorem _TraceInclusion_flatten_inline_everything_r (m : ModWf) :
  TraceInclusion m (inlined_ModWf m).
Proof.
  eauto using TraceInclusion_flatten_inline_everything_r.
Qed.

Theorem _inlineSingle_Rule_map_Wf {f : DefMethT} {m : ModWf} (inMeths : In f (getAllMethods m)):
  WfMod (createHide (inlineSingle_Rule_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  eauto using inlineSingle_Rule_map_Wf.
Qed.

Theorem _inlineSingle_Meth_map_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  WfMod (createHide (inlineSingle_Meth_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  eauto using inlineSingle_Meth_map_Wf.
Qed.

Theorem _inlineSingle_Rule_map_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)):
  TraceInclusion m (inlineSingle_Rule_map_ModWf inMeths).
Proof.
  eauto using inlineSingle_Rule_map_TraceInclusion.
Qed.

Theorem _inlineSingle_Meth_map_TraceInclusion {m : ModWf}  {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Meth_map_ModWf inMeths).
Proof.
  eauto using inlineSingle_Meth_map_TraceInclusion.
Qed.

Theorem _inlineSingle_Module_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  WfMod (inlineSingle_Module f m).
Proof.
  eauto using inlineSingle_Module_Wf.
Qed.

Theorem _inlineSingle_BaseModule_TraceInclusion {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Module_ModWf inMeths).
Proof.
  eauto using inlineSingle_BaseModule_TraceInclusion.
Qed.

Theorem _inlineSingle_BaseModule_nth_Meth_Wf {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod
    (createHide
       (inlineSingle_BaseModule_nth_Meth f (getAllRegisters m) 
                                         (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  eauto using inlineSingle_BaseModule_nth_Meth_Wf.
Qed.

Theorem _inlineSingle_BaseModule_nth_Meth_TraceInclusion {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Meth_ModWf inMeths xs).
Proof.
  eauto using inlineSingle_BaseModule_nth_Meth_TraceInclusion.
Qed.

Theorem _inlineSingle_BaseModule_nth_Rule_Wf {m : ModWf} {f : DefMethT}
        (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod
    (createHide
       (inlineSingle_BaseModule_nth_Rule f (getAllRegisters m) 
                                         (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  eauto using inlineSingle_BaseModule_nth_Rule_Wf.
Qed.

Theorem _inlineSingle_BaseModule_nth_Rule_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Rule_ModWf inMeths xs).
Proof.
  eauto using inlineSingle_BaseModule_nth_Rule_TraceInclusion.
Qed.

Theorem _inlineAll_Rules_Wf (m : ModWf):
  WfMod (inlineAll_Rules_Mod m).
Proof.
  eauto using inlineAll_Rules_Wf.
Qed.

Theorem _inlineAll_Rules_TraceInclusion (m : ModWf) :
  TraceInclusion m (inlineAll_Rules_ModWf m).
Proof.
  eauto using inlineAll_Rules_TraceInclusion.
Qed.

Theorem _inlineAll_Meths_Wf (m : ModWf) :
  WfMod (inlineAll_Meths_Mod m).
Proof.
  eauto using inlineAll_Meths_Wf.
Qed.

Theorem _inlineAll_Meths_TraceInclusion (m : ModWf) :
  TraceInclusion m (inlineAll_Meths_ModWf m).
Proof.
  eauto using inlineAll_Meths_TraceInclusion.
Qed.

Theorem _flatten_inline_remove_Wf (m : ModWf) :
  WfMod (flatten_inline_remove m).
Proof.
  eauto using flatten_inline_remove_Wf.
Qed.

Theorem _removeHides_createHide_TraceInclusion (m : BaseModuleWf) (l : list string)
        (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (removeHidesModWf m l) (createHideModWf m subList).
Proof.
  eauto using removeHides_createHide_TraceInclusion.
Qed.

Theorem _createHide_removeHides_TraceInclusion (m : BaseModuleWf) (l : list string)
        (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (createHideModWf m subList) (removeHidesModWf m l).
Proof.
  eauto using createHide_removeHides_TraceInclusion.
Qed.

Theorem _flatten_inline_remove_TraceInclusion (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_everything m) (flatten_inline_remove_ModWf m).
Proof.
  eauto using flatten_inline_remove_TraceInclusion.
Qed.