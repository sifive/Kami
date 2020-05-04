Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
(*
 * kami_rewrites_reflection.v
 *
 * Code to perform all the rewrites in kami_rewrites_db by reflection
 *)
Inductive KRTyp : Type :=
  | KRTypModuleElt: KRTyp
  | KRTypRegInitT: KRTyp
  | KRTypAttributeActionVoid: KRTyp
  | KRTypDefMethT: KRTyp
  | KRList: KRTyp -> KRTyp.

Fixpoint KRrealizeType (t: KRTyp) :=
  match t with
  | KRTypModuleElt => ModuleElt
  | KRTypRegInitT => RegInitT
  | KRTypAttributeActionVoid => Attribute (Action Void)
  | KRTypDefMethT => DefMethT
  | KRList t => list (KRrealizeType t)
  end.

Inductive KRExp: KRTyp -> Type :=
  | KRNil t : @KRExp (KRList t)
  | KRVar t : KRrealizeType t -> @KRExp t
  | KRCons t : @KRExp t -> @KRExp (KRList t) -> @KRExp (KRList t)
  | KRApp t : @KRExp (KRList t) -> @KRExp (KRList t) -> @KRExp (KRList t)
  | KRMERegister : @KRExp KRTypRegInitT -> @KRExp KRTypModuleElt
  | KRRegisters : @KRExp (KRList KRTypRegInitT)-> @KRExp (KRList KRTypModuleElt)
  | KRMERule : @KRExp KRTypAttributeActionVoid -> @KRExp KRTypModuleElt
  | KRMEMeth : @KRExp KRTypDefMethT -> @KRExp KRTypModuleElt
  | KRMakeModule_rules : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypAttributeActionVoid)
  | KRMakeModule_regs : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypRegInitT)
  | KRMakeModule_meths : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypDefMethT).

(*Fixpoint KRExpType (e: KRExp) :=
  match e in KRExp return KRTyp with
  | KRNil t => match t with
               | KRTypModuleElt => KRList KRTypModuleElt
               | KRTypRegInitT => KRList KRTypRegInitT
               | _ => KRList KRTypDefMethT
               end
  | KRVar t e => t
  | KRCons t a b => (KRList t)
  | KRApp t a b => (KRList t)
  | KRMERegister e => KRTypModuleElt
  | KRRegisters l => (KRList KRTypModuleElt)
  | KRMERule r => KRTypModuleElt
  | KRMEMeth m => KRTypModuleElt
  | KRMakeModule_rules r => KRList KRTypAttributeActionVoid
  | KRMakeModule_regs r => KRList KRTypDefMethT
  | KRMakeModule_meths m => KRList KRTypModuleElt
  end.*)

Fixpoint KRRealizeExp {typ} (e: KRExp typ) :=
  match e in KRExp typ return (@KRrealizeType typ) with
  | KRNil t => @nil (KRrealizeType t)
  | KRVar t e => e
  | KRCons t a b => @cons (@KRrealizeType t) (@KRRealizeExp t a) (@KRRealizeExp (KRList t) b)
  | KRApp t a b => @app (@KRrealizeType t) (@KRRealizeExp (KRList t) a) (@KRRealizeExp (KRList t) b)
  | KRMERegister e => MERegister (@KRRealizeExp KRTypRegInitT e)
  | KRMERule r => MERule (@KRRealizeExp KRTypAttributeActionVoid r)
  | KRMEMeth m => MEMeth (@KRRealizeExp KRTypDefMethT m)
  | KRMakeModule_rules r => makeModule_rules (KRRealizeExp r)
  | KRMakeModule_regs r => makeModule_regs (KRRealizeExp r)
  | KRMakeModule_meths m =>makeModule_meths (KRRealizeExp m)
  | KRRegisters l => Registers (KRRealizeExp l)
  end.

Ltac KRReifyExp e t :=
  match e with
  | nil => constr:(@KRNil t)
  | cons ?F nil => match t with
                  | KRList ?T => let fr :=ltac:(KRReifyExp F T) in
                                 constr:(@KRCons T fr (@KRNil T))
                  | ?T => constr:(@KRVar t e)
                  end
  | cons ?F ?R => match t with
                  | KRList ?T => let fr :=ltac:(KRReifyExp F T) in
                                 let re:=ltac:(KRReifyExp R t) in
                                 constr:(@KRCons T fr re)
                  | ?T => constr:(@KRVar t e)
                  end
  | app ?F ?R => let x1 := ltac:(KRReifyExp F t) in
                 let x2 := ltac:(KRReifyExp R t) in
                 match t with
                 | KRList ?T => constr:(@KRApp T x1 x2)
                 | ?T => constr:(@KRVar t e)
                 end
  | MERegister ?E => let x := ltac:(KRReifyExp E KRTypRegInitT) in
                         constr:(@KRMERegister x)
  | Registers ?E => let x := ltac:(KRReifyExp E (KRList KRTypRegInitT)) in
                       constr:(@KRRegisters x)
  | MERule ?E => let  x := ltac:(KRReifyExp E KRTypAttributeActionVoid) in
                     constr:(@KRMERule x)
  | MEMeth ?E => let x := ltac:(KRReifyExp E KRTypDefMethT) in
                     constr:(@KRMEMeth x)
  | makeModule_rules ?E => let x := ltac:(KRReifyExp E (KRList KRTypModuleElt)) in
                               constr:(@KRMakeModule_rules x)
  | makeModule_regs ?X => let x := ltac:(KRReifyExp X (KRList KRTypModuleElt)) in
                              constr:(@KRMakeModule_regs x)
  | makeModule_meths ?E => let x := ltac:(KRReifyExp E (KRList KRTypModuleElt)) in 
                              constr:(@KRMakeModule_meths x)
  | ?X => constr:(@KRVar t X)
  end.

Fixpoint KRSimplifyTopMakeModule_regs (x:KRExp (KRList KRTypModuleElt)) :=
  match x in KRExp (KRList KRTypModuleElt) return KRExp (KRList KRTypRegInitT) with
  (*| @KRApp tp a b => match tp in KRTyp return KRTyp with
                     | KRTypModuleElt => @KRApp KRTypRegInitT (KRMakeModule_regs a) (KRMakeModule_regs b)
                     | _ => @KRMakeModule_regs x
                     end*)
  (*| @KRCons KRTypRegInitT aa  b => match aa in (KRExp KRTypRegInitT) with
                                   | KRMERegister a => @KRCons KRTypRegInitT a (KRMakeModule_regs b)
                                   | _ => @KRMakeModule_regs x
                                   end*)
  | @KRNil tp => @KRNil KRTyPRegInitT
  | q => @KRMakeModule_regs x
  end.

Fixpoint KRSimplifyTop {t} (e : KRExp t) :=
  match e in KRExp t return KRExp t with
  | @KRApp KRTypModuleElt f c => match f with
                                 | @KRCons KRTypModuleElt a b => @KRCons KRTypModuleElt a (@KRApp KRTypModuleElt b c)
                                 | _ => @KRApp KRTypModuleElt f c
                                 end
  | KRRegisters x => match x with
                     | @KRApp KRTypRegInitT a b => @KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)
                     | @KRCons KRTypRegInitT a b => @KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
                     | KRNil KRTypModuleElt => KRNil KRTypModuleElt
                     | e => KRRegisters e
                     end
  | KRMakeModule_regs x => match x in KRExp (KRList KRTypModuleElt) with
                           | @KRApp KRTypRegInitT a b => @KRApp KRTypModuleElt (KRMakeModule_regs a) (KRMakeModule_regs b)
                           | @KRCons KRTypRegInitT aa  b => match aa in (KRExp KRTypRegInitT) with
                                                            | KRMERegister a => @KRCons KRTypRegInitT a (KRMakeModule_regs b)
                                                            | _ => e
                                                            end
                           | @KRNil KRTypModuleElt => @KRNil KRTypRegInitT
                           | q => @KRMakeModule_regs x
                           end
  | e => e
  end.

Fixpoint KRSimplify {t} (e: KRExp t) :=
  match e in KRExp t return KRExp t with
  | @KRCons t a b => KRSimplifyTop (@KRCons t (KRSimplify a) (KRSimplify b))
  | @KRApp t a b => KRSimplifyTop (@KRApp t (KRSimplify a) (KRSimplify b))
  | @KRMERegister a => KRSimplifyTop (@KRMERegister (KRSimplify a))
  | @KRRegisters a => KRSimplifyTop (@KRRegisters (KRSimplify a))
  | @KRMEMeth a => KRSimplifyTop (@KRMEMeth (KRSimplify a))
  | @KRMERule a => KRSimplifyTop (@KRMERule (KRSimplify a))
  | @KRMakeModule_rules a => KRSimplifyTop (@KRMakeModule_rules (KRSimplify a))
  | @KRMakeModule_regs a => KRSimplifyTop (@KRMakeModule_regs (KRSimplify a))
  | @KRMakeModule_meths a => KRSimplifyTop (@KRMakeModule_meths (KRSimplify a))
  | e => e
  end.


Theorem KRSimplifySound: forall t e, @KRRealizeExp t e = @KRRealizeExp t (@KRSimplify t e).
Admitted.

Ltac KRSimplifyTac t e :=
  match goal with
  | |- ?A = ?B =>
      let x := (ltac:(KRReifyExp e t)) in
          replace A with (KRRealizeExp x);[(rewrite KRSimplifySound;cbv [KRRealizeExp]) | (cbv [KRSimplify KRSimplifyTop];reflexivity)]
  end.
  (*let x := ltac:(KRReifyExp e) in
      (replace e with (KRRealizeExp x);[cbv [KRSimplify KRSimplifySound];reflexivity | replace (KRRealizeExp x) with (KRRealizeExp (KRSimplify x));[rewrite KRSimplifySound;reflexivity | compute]]).
*)

Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRList KRTypRegInitT))) in
          replace A with (KRRealizeExp x);[(rewrite KRSimplifySound;cbv [KRRealizeExp KRSimplify KRSimplifyTop]) | cbv [KRRealizeExp];reflexivity]
  end.
  cbv [KRSimplify KRSimplifyTop KRRealizeExp].

Abort.

(*Fixpoint KRSimplifyTop {t} (e : KRExp t) :=
  match e in KRExp t return KRExp t with
  (*| KRApp KRTypModuleElt (KRCons KRTypModuleElt a b) c => @KRCons KRTypModuleElt a (@KRApp KRTypModuleElt b c)
  | KRRegisters (KRCons KRTypRegInitT a b) => @KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
  | KRRegisters (@KRApp KRTypRegInitT a b) => @KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)*)
  | @KRRegisters (@KRNil KRTypModuleElt) => @KRNil KRTypModuleElt
  | e => e
  end.*)

