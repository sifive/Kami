Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
(*
 * kami_rewrites_reflection.v
 *
 * Code to perform all the rewrites in kami_rewrites_db by reflection
 *)

Inductive KRElem: Type :=
| KRElemRegInitT : KRElem
| KRElemAttributeActionVoid : KRElem
| KRElemDefMethT : KRElem
| KRElemModuleElt: KRElem.

Inductive KRTyp : Type :=
  | KRTypElem: KRElem -> KRTyp
  | KRTypList: KRTyp -> KRTyp.

Fixpoint KRrealizeType (t: KRTyp) :=
  match t with
  | KRTypElem KRElemModuleElt => ModuleElt
  | KRTypElem KRElemRegInitT => RegInitT
  | KRTypElem KRElemAttributeActionVoid => Attribute (Action Void)
  | KRTypElem KRElemDefMethT => DefMethT
  | KRTypList t => list (KRrealizeType t)
  end.

Inductive KRExp: KRTyp -> Type :=
  | KRNil t : @KRExp (KRTypList t)
  | KRVar t : KRrealizeType t -> @KRExp t
  | KRCons t : @KRExp t -> @KRExp (KRTypList t) -> @KRExp (KRTypList t)
  | KRApp t : @KRExp (KRTypList t) -> @KRExp (KRTypList t) -> @KRExp (KRTypList t)
  | KRMERegister : @KRExp (KRTypElem KRElemRegInitT) -> @KRExp (KRTypElem KRElemModuleElt)
  | KRRegisters : @KRExp (KRTypList (KRTypElem KRElemRegInitT)) -> @KRExp (KRTypList (KRTypElem KRElemModuleElt))
  | KRMERule : @KRExp (KRTypElem KRElemAttributeActionVoid) -> @KRExp (KRTypElem KRElemModuleElt)
  | KRMEMeth : @KRExp (KRTypElem KRElemDefMethT) -> @KRExp (KRTypElem KRElemModuleElt)
  | KRMakeModule_rules : @KRExp (KRTypList (KRTypElem KRElemModuleElt)) -> @KRExp (KRTypList (KRTypElem KRElemAttributeActionVoid))
  | KRMakeModule_regs : @KRExp (KRTypList (KRTypElem KRElemModuleElt)) -> @KRExp (KRTypList (KRTypElem KRElemRegInitT))
  | KRMakeModule_meths : @KRExp (KRTypList (KRTypElem KRElemModuleElt)) -> @KRExp (KRTypList (KRTypElem KRElemDefMethT)).

Fixpoint KRRealizeExp {typ} (e: KRExp typ) :=
  match e in KRExp typ return (@KRrealizeType typ) with
  | KRNil t => @nil (KRrealizeType t)
  | KRVar t e => e
  | KRCons t a b => @cons (@KRrealizeType t) (@KRRealizeExp t a) (@KRRealizeExp (KRTypList t) b)
  | KRApp t a b => @app (@KRrealizeType t) (@KRRealizeExp (KRTypList t) a) (@KRRealizeExp (KRTypList t) b)
  | KRMERegister e => MERegister (@KRRealizeExp (KRTypElem KRElemRegInitT) e)
  | KRMERule r => MERule (@KRRealizeExp (KRTypElem KRElemAttributeActionVoid) r)
  | KRMEMeth m => MEMeth (@KRRealizeExp (KRTypElem KRElemDefMethT) m)
  | KRMakeModule_rules r => makeModule_rules (KRRealizeExp r)
  | KRMakeModule_regs r => makeModule_regs (KRRealizeExp r)
  | KRMakeModule_meths m =>makeModule_meths (KRRealizeExp m)
  | KRRegisters l => Registers (KRRealizeExp l)
  end.

Ltac KRReifyExp e t :=
  match e with
  | nil => constr:(@KRNil t)
  | cons ?F nil => match t with
                  | KRTypList ?T => let fr :=ltac:(KRReifyExp F T) in
                                    constr:(@KRCons T fr (@KRNil T))
                  | ?T => constr:(@KRVar t e)
                  end
  | cons ?F ?R => match t with
                  | KRTypList ?T => let fr :=ltac:(KRReifyExp F T) in
                                    let re:=ltac:(KRReifyExp R t) in
                                    constr:(@KRCons T fr re)
                  | ?T => constr:(@KRVar t e)
                  end
  | app ?F ?R => let x1 := ltac:(KRReifyExp F t) in
                 let x2 := ltac:(KRReifyExp R t) in
                 match t with
                 | KRTypList ?T => constr:(@KRApp T x1 x2)
                 | ?T => constr:(@KRVar t e)
                 end
  | MERegister ?E => let x := ltac:(KRReifyExp E (KRTypElem KRElemRegInitT)) in
                         constr:(@KRMERegister x)
  | Registers ?E => let x := ltac:(KRReifyExp E (KRTypList (KRTypElem KRElemRegInitT))) in
                       constr:(@KRRegisters x)
  | MERule ?E => let  x := ltac:(KRReifyExp E (KRTypElem KRElemAttributeActionVoid)) in
                     constr:(@KRMERule x)
  | MEMeth ?E => let x := ltac:(KRReifyExp E (KRTypElem KRElemDefMethT)) in
                     constr:(@KRMEMeth x)
  | makeModule_rules ?E => let x := ltac:(KRReifyExp E (KRTypList (KRTypElem KRElemModuleElt))) in
                               constr:(@KRMakeModule_rules x)
  | makeModule_rules [] => constr:(@KRMakeModule_rules (@KRNil (KRTypElem KRElemModuleElt)))
  | makeModule_regs [] => constr:(@KRMakeModule_regs (@KRNil (KRTypElem KRElemModuleElt)))
  | makeModule_regs ?X => let x := ltac:(KRReifyExp X (KRTypList (KRTypElem KRElemModuleElt))) in
                              constr:(@KRMakeModule_regs x)
  | makeModule_meths ?E => let x := ltac:(KRReifyExp E (KRTypList (KRTypElem KRElemModuleElt))) in 
                              constr:(@KRMakeModule_meths x)
  | makeModule_meths [] => constr:(@KRMakeModule_meths (@KRNil (KRTypElem KRElemModuleElt)))
  | ?X => constr:(@KRVar t X)
  end.

Axiom cheat: forall x, x.

Fixpoint KRSimplifyTop {t} (e : KRExp t) : KRExp t.
refine
  (match e in KRExp t return KRExp t with
  | @KRApp (KRTypElem KRElemModuleElt) f c => match f with
                                 | @KRCons (KRTypElem KRElemModuleElt) a b => @KRCons (KRTypElem KRElemModuleElt) a (@KRApp (KRTypElem KRElemModuleElt) b c)
                                 | _ => @KRApp (KRTypElem KRElemModuleElt) f c
                                 end
  | KRRegisters x => match x with
                     | @KRApp (KRTypElem KRElemRegInitT) a b => @KRApp (KRTypElem KRElemModuleElt) (KRRegisters a) (KRRegisters b)
                     | @KRCons (KRTypElem KRElemRegInitT) a b => @KRCons (KRTypElem KRElemModuleElt) (KRMERegister a) (KRRegisters b)
                     | KRNil (KRTypElem KRElemModuleElt) => KRNil (KRTypElem KRElemModuleElt)
                     | e => KRRegisters e
                     end
  | KRMakeModule_regs x => match x in KRExp (KRTypList (KRTypElem KRElemModuleElt)) with
                           | @KRApp (KRTypElem KRElemModuleElt) a b => @KRApp (KRTypElem KRElemRegInitT) (KRMakeModule_regs a) (KRMakeModule_regs b)
                           | @KRCons (KRTypElem KRElemModuleElt) aa  b => match aa in (KRExp (KRTypElem KRElemModuleElt)) with
                                                            | KRMERule a => KRMakeModule_regs b
                                                            | KRMEMeth a => KRMakeModule_regs b
                                                            | KRMERegister a => @KRCons (KRTypElem KRElemRegInitT) a (KRMakeModule_regs b)
                                                            | _ => _ (*@KRMakeModule_regs*)
                                                            end
                           | @KRNil (KRTypElem KRElemModuleElt) => @KRNil (KRTypElem KRElemRegInitT)
                           | q => _ (*@KRMakeModule_regs x*)
                           end
  | e => e
  end).
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - destruct k0.
    + apply idProp.
    + destruct k0.
      * destruct k0.
        ++ apply idProp.
        ++ apply idProp.
        ++ apply idProp.
        ++ apply (KRMakeModule_regs x).
      * apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - destruct k3.
    + destruct k3.
      * apply idProp.
      * apply idProp.
      * apply idProp.
      * apply (KRMakeModule_regs x).
    + apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply (KRMakeModule_regs x).
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
  - apply idProp.
Defined.

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
    let x := (ltac:(KRReifyExp e t)) in
        change e with (KRRealizeExp x);rewrite KRSimplifySound;cbv [KRSimplify KRSimplifyTop KRRealizeExp].

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  (*match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRTypList (KRTypElem KRElemRegInitT)))) in
          change A with (KRRealizeExp x);rewrite KRSimplifySound
  end.
  cbv [KRSimplify KRSimplifyTop KRRealizeExp].*)
Abort.

Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
  (*match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRTypList (KRTypElem KRElemRegInitT)))) in
          change A with (KRRealizeExp x);rewrite KRSimplifySound
  end.
  cbv [KRSimplify KRSimplifyTop KRRealizeExp].*)

Abort.

Goal forall e, makeModule_regs []=e.
  intros.
  (*match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRTypList (KRTypElem KRElemRegInitT)))) in
          change A with (KRRealizeExp x);rewrite KRSimplifySound
  end.
  cbv [KRSimplify KRSimplifyTop KRRealizeExp].*)
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac (KRTypList (KRTypElem KRElemRegInitT)) A
  end.
Abort.

