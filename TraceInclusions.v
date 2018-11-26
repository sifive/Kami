Require Import Kami.Syntax.
Import ListNotations.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Kami.PPlusProperties.
(*
Properties.v:  Theorem simulationZeroAction:
*)
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