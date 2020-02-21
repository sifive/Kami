Require Import Kami.All.

Definition EffectfulRelation {k: Kind} (R: RegsT -> RegsT -> Prop) (a_i a_s: ActionT type k): Prop :=
  forall o_i o_s,
    R o_i o_s ->
    forall calls reads_i upds_i retval,
      SemAction o_i a_i reads_i upds_i calls retval ->
        exists reads_s upds_s,
          (SemAction o_s a_s reads_s upds_s calls retval) /\
          R (doUpdRegs upds_i o_i) (doUpdRegs upds_s o_s).

Definition EffectlessRelation {k: Kind} (R: RegsT -> RegsT -> Prop) (a_i a_s: ActionT type k): Prop :=
  forall o_i o_s,
    R o_i o_s ->
    forall reads_i upds calls retval,
      SemAction o_i a_i reads_i upds calls retval ->
      (upds = [] /\
       calls = [] /\
       exists reads_s,
        (SemAction o_s a_s reads_s [] [] retval)).

Definition ActionWb {k} myRegs (act: ActionT type k): Prop :=
  forall o reads upds calls ret,
    NoDup (map fst o) ->
    SubList myRegs (getKindAttr o) ->
    SemAction o act reads upds calls ret ->
    ((exists o',
         SubList o' o
         /\ SubList reads o'
         /\ getKindAttr o' = myRegs
         /\ SemAction o' act reads upds calls ret
     ) /\
     SubList (getKindAttr upds) myRegs).
