Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.

Inductive KRElem: Type :=
| KRElemRegInitT : KRElem
| KRElemRule : KRElem
| KRElemDefMethT : KRElem
| KRElemModuleElt: KRElem.

Definition KRElemDenote (t: KRElem) :=
  match t with
  | KRElemRegInitT => RegInitT
  | KRElemRule => Attribute (Action Void)
  | KRElemDefMethT => DefMethT
  | KRElemModuleElt => ModuleElt
  end.

Inductive KRType : Type :=
  | KRTypeElem: KRElem -> KRType
  | KRTypeList: KRType -> KRType.

Fixpoint KRTypeeDenote (t: KRType) :=
  match t with
  | KRTypeElem t' => KRElemDenote t'
  | KRTypeList t => list (KRTypeeDenote t)
  end.

Inductive KRExpr: KRType -> Type :=
  | KRNil t : @KRExpr (KRTypeList t)
  | KRVar t : KRTypeeDenote t -> @KRExpr t
  | KRCons t : @KRExpr t -> @KRExpr (KRTypeList t) -> @KRExpr (KRTypeList t)
  | KRApp t : @KRExpr (KRTypeList t) -> @KRExpr (KRTypeList t) -> @KRExpr (KRTypeList t)
  | KRMERegister : @KRExpr (KRTypeElem KRElemRegInitT) -> @KRExpr (KRTypeElem KRElemModuleElt)
  | KRRegisters : @KRExpr (KRTypeList (KRTypeElem KRElemRegInitT)) ->
                  @KRExpr (KRTypeList (KRTypeElem KRElemModuleElt))
  | KRMERule : @KRExpr (KRTypeElem KRElemRule) -> @KRExpr (KRTypeElem KRElemModuleElt)
  | KRMEMeth : @KRExpr (KRTypeElem KRElemDefMethT) -> @KRExpr (KRTypeElem KRElemModuleElt)
  | KRMakeModule_regs : @KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) ->
                        @KRExpr (KRTypeList (KRTypeElem KRElemRegInitT))
  | KRMakeModule_rules : @KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) ->
                         @KRExpr (KRTypeList (KRTypeElem KRElemRule))
  | KRMakeModule_meths : @KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) ->
                         @KRExpr (KRTypeList (KRTypeElem KRElemDefMethT)).

Definition KRTypeDenote {typ} (e: KRExpr typ) := typ.

Fixpoint KRExprDenote {typ} (e: KRExpr typ) :=
  match e in KRExpr typ return (@KRTypeeDenote typ) with
  | KRNil t => @nil (KRTypeeDenote t)
  | KRVar t e => e
  | KRCons t a b => @cons (@KRTypeeDenote t) (@KRExprDenote t a) (@KRExprDenote (KRTypeList t) b)
  | KRApp t a b => @app (@KRTypeeDenote t) (@KRExprDenote (KRTypeList t) a) (@KRExprDenote (KRTypeList t) b)
  | KRMERegister e => MERegister (@KRExprDenote (KRTypeElem KRElemRegInitT) e)
  | KRMERule r => MERule (@KRExprDenote (KRTypeElem KRElemRule) r)
  | KRMEMeth m => MEMeth (@KRExprDenote (KRTypeElem KRElemDefMethT) m)
  | KRMakeModule_regs r => makeModule_regs (KRExprDenote r)
  | KRMakeModule_rules r => makeModule_rules (KRExprDenote r)
  | KRMakeModule_meths m =>makeModule_meths (KRExprDenote m)
  | KRRegisters l => Registers (KRExprDenote l)
  end.

Ltac KRExprReify e t :=
  match e with
  | nil => match t with
           | KRTypeList ?t' => constr:(@KRNil t')
           end
  | cons ?F ?R => match t with
                  | KRTypeList ?T => let fr :=ltac:(KRExprReify F T) in
                                    let re:=ltac:(KRExprReify R t) in
                                    constr:(@KRCons T fr re)
                  | ?T => constr:(@KRVar t e)
                  end
  | app ?F ?R => let x1 := ltac:(KRExprReify F t) in
                 let x2 := ltac:(KRExprReify R t) in
                 match t with
                 | KRTypeList ?T => constr:(@KRApp T x1 x2)
                 | ?T => constr:(@KRVar t e)
                 end
  | MERegister ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemRegInitT)) in
                         constr:(@KRMERegister x)
  | Registers ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRegInitT))) in
                       constr:(@KRRegisters x)
  | MERule ?E => let  x := ltac:(KRExprReify E (KRTypeElem KRElemRule)) in
                     constr:(@KRMERule x)
  | MEMeth ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemDefMethT)) in
                     constr:(@KRMEMeth x)
  | makeModule_regs ?X => let x := ltac:(KRExprReify X (KRTypeList (KRTypeElem KRElemModuleElt))) in
                              constr:(@KRMakeModule_regs x)
  | makeModule_rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in
                               constr:(@KRMakeModule_rules x)
  | makeModule_meths ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                              constr:(@KRMakeModule_meths x)
  | ?X => constr:(@KRVar t X)
  end.

Axiom cheat: forall x, x.

(*Definition KRSimplifyTopTest t (e : KRExpr t) : KRExpr t.
  refine
    (match e in KRExpr t return KRExpr t with
     | @KRApp (KRTypeElem KRElemModuleElt) f c =>
       match f in KRExpr t' with
       | @KRCons (KRTypeElem KRElemModuleElt) a b =>
         @KRCons (KRTypeElem KRElemModuleElt) a (@KRApp (KRTypeElem KRElemModuleElt) b c)
       | _ => @KRApp (KRTypeElem KRElemModuleElt) f c
       end
     | KRRegisters x =>
       match x with
       | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemModuleElt)
       | @KRCons (KRTypeElem KRElemRegInitT) a b =>
         @KRCons (KRTypeElem KRElemModuleElt) (KRMERegister a) (KRRegisters b)
       | @KRApp (KRTypeElem KRElemRegInitT) a b =>
         @KRApp (KRTypeElem KRElemModuleElt) (KRRegisters a) (KRRegisters b)
       | e => KRRegisters e
       end
     | KRMakeModule_regs x => _
     | q => q
     end).    
  inversion x.
  - apply KRNil.
  - apply (KRMakeModule_regs x).
  - inversion X.
    + apply (KRMakeModule_regs x).
    + apply (KRCons X1 (KRMakeModule_regs X0)).
    + apply (KRMakeModule_regs X0).
    + apply (KRMakeModule_regs X0).
  - apply (KRApp (KRMakeModule_regs X) (KRMakeModule_regs X0)).
  - apply X.
Defined.

Theorem KRSimplifyTopTestSound:
  forall tp e, @KRExprDenote tp (@KRSimplifyTopTest tp e)=@KRExprDenote tp e.
Proof.
  intros.
  destruct e; simpl; auto.
  - destruct t; simpl; auto.
    destruct k; simpl; auto.
    dependent destruction e1; simpl; auto.
  - dependent destruction e;simpl;auto.
    rewrite Registers_dist_append.
    reflexivity.
  - dependent destruction e; simpl; auto.
    + dependent destruction e1; simpl; auto.
    + rewrite makeModule_regs_append.
      reflexivity.
    + rewrite makeModule_regs_Registers.
      reflexivity.
Qed.*)
      
Definition KRSimplifyTop' {t} (e : KRExpr t) : KRExpr t.
refine
  (match e in KRExpr t return KRExpr t with
   | @KRApp tp f c => _
     (*match f with
     | @KRCons (KRTypeElem KRElemModuleElt) a b =>
       @KRCons (KRTypeElem KRElemModuleElt) a (@KRApp (KRTypeElem KRElemModuleElt) b c)
     | @
     | _ => @KRApp (KRTypeElem KRElemModuleElt) f c
     end*)
   | KRRegisters x => _
     (*match x with
     | @KRApp (KRTypeElem KRElemRegInitT) a b =>
       @KRApp (KRTypeElem KRElemModuleElt) (KRRegisters a) (KRRegisters b)
     | @KRCons (KRTypeElem KRElemRegInitT) a b =>
       @KRCons (KRTypeElem KRElemModuleElt) (KRMERegister a) (KRRegisters b)
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemModuleElt)
     | e => KRRegisters e
     end*)
   | KRMakeModule_regs x => _
     (*match x in KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) with
     | @KRApp (KRTypeElem KRElemModuleElt) a b =>
       @KRApp (KRTypeElem KRElemRegInitT) (KRMakeModule_regs a) (KRMakeModule_regs b)
     | @KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa in (KRExpr (KRTypeElem KRElemModuleElt)) with
       | KRMERule a => KRMakeModule_regs b
       | KRMEMeth a => KRMakeModule_regs b
       | KRMERegister a => @KRCons (KRTypeElem KRElemRegInitT) a (KRMakeModule_regs b)
       | KRVar t val => cheat _
       | _ => _
       end
     | @KRNil (KRTypeElem KRElemModuleElt) => @KRNil (KRTypeElem KRElemRegInitT)
     | q => cheat _ (*@KRMakeModule_regs x*)
     end*)
   | KRMakeModule_rules x => _
      (*match x in KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) with
     | @KRApp (KRTypeElem KRElemModuleElt) a b =>
       @KRApp (KRTypeElem KRElemRule) (KRMakeModule_rules a) (KRMakeModule_rules b)
     | @KRCons (KRTypeElem KRElemModuleElt) aa  b =>
       match aa in (KRExpr (KRTypeElem KRElemModuleElt)) with
       | KRMERegister a => KRMakeModule_rules b
       | KRMEMeth a => KRMakeModule_rules b
       | KRMERule a => @KRCons (KRTypeElem KRElemRule) a (KRMakeModule_rules b)
       | _ => cheat _ (*@KRMakeModule_rules*)
       end
     | @KRNil (KRTypeElem KRElemModuleElt) => @KRNil (KRTypeElem KRElemRule)
     | qr => cheat _ (*@KRMakeModule_rules x*)
     end*)
   | KRMakeModule_meths x => _
     (*match x in KRExpr (KRTypeList (KRTypeElem KRElemModuleElt)) with
     | @KRApp (KRTypeElem KRElemModuleElt) a b =>
       @KRApp (KRTypeElem KRElemDefMethT) (KRMakeModule_meths a) (KRMakeModule_meths b)
     | @KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa in (KRExpr (KRTypeElem KRElemModuleElt)) with
       | KRMERule a => KRMakeModule_meths b
       | KRMERegister a => KRMakeModule_meths b
       | KRMEMeth a => @KRCons (KRTypeElem KRElemDefMethT) a (KRMakeModule_meths b)
       | _ => cheat _ (*@KRMakeModule_meths *)
       end
     | @KRNil (KRTypeElem KRElemModuleElt) => @KRNil (KRTypeElem KRElemDefMethT)
     | qm => cheat _ (*@KRMakeModule_meths x*)
     end*)
   | e => e
   end).
  - inversion f.
    + apply c.
    + apply (@KRApp tp f c).
    + apply (@KRCons tp X (@KRApp tp X0 c)).
    + apply (@KRApp tp f c).
    + subst.
      apply (@KRApp (KRTypeElem KRElemModuleElt) f c).
    + subst.
      apply (@KRApp (KRTypeElem KRElemRegInitT) f c).
    + subst.
      apply (@KRApp (KRTypeElem KRElemRule) f c).
    + subst.
      apply (@KRApp (KRTypeElem KRElemDefMethT) f c).
  - inversion x.
    + apply KRNil.
    + apply (KRRegisters x).
    + apply (KRCons (KRMERegister X) (KRRegisters X0)).
    + apply (KRApp (KRRegisters X) (KRRegisters X0)).
    + apply (KRRegisters x).
  - inversion x.
    + apply KRNil.
    + apply (KRMakeModule_regs x).
    + inversion X.
      * apply (KRMakeModule_regs x).
      * apply (KRCons X1 (KRMakeModule_regs X0)).
      * apply (KRMakeModule_regs X0).
      * apply (KRMakeModule_regs X0).
    + apply (KRApp (KRMakeModule_regs X) (KRMakeModule_regs X0)).
    + apply X.
  - inversion x.
    + apply KRNil.
    + apply (KRMakeModule_rules x).
    + inversion X.
      * apply (KRMakeModule_rules x).
      * apply (KRMakeModule_rules X0).
      * apply (KRCons X1 (KRMakeModule_rules X0)).
      * apply (KRMakeModule_rules X0).
    + apply (KRApp (KRMakeModule_rules X) (KRMakeModule_rules X0)).
    + apply (KRMakeModule_rules x).
  - inversion x.
    + apply KRNil.
    + apply (KRMakeModule_meths x).
    + inversion X.
      * apply (KRMakeModule_meths x).
      * apply (KRMakeModule_meths X0).
      * apply (KRMakeModule_meths X0).
      * apply (KRCons X1 (KRMakeModule_meths X0)).
    + apply (KRApp (KRMakeModule_meths X) (KRMakeModule_meths X0)).
    + apply (KRMakeModule_meths x).
Defined.

Definition KRSimplifyTop {t} e := ltac:(let x := eval cbv in (@KRSimplifyTop' t e) in exact x).

Fixpoint KRSimplify' {tp} (e: KRExpr tp) : KRExpr tp.
  inversion e.
  - apply KRNil.
  - subst.
    apply e.
  - subst.
    apply (@KRSimplifyTop (KRTypeList t) (@KRCons t (@KRSimplify' t X) (@KRSimplify' (KRTypeList t) X0))).
  - subst.
    apply (@KRSimplifyTop (KRTypeList t) (@KRApp t (@KRSimplify' (KRTypeList t) X) (@KRSimplify' (KRTypeList t) X0))).
  - apply (KRSimplifyTop (KRMERegister (KRSimplify' (KRTypeElem KRElemRegInitT) X))).
  - apply (KRSimplifyTop (KRRegisters (KRSimplify' (KRTypeList (KRTypeElem KRElemRegInitT)) X))).
  - apply (KRSimplifyTop (KRMERule (KRSimplify' (KRTypeElem KRElemRule) X))).
  - apply (KRSimplifyTop (KRMEMeth (KRSimplify' (KRTypeElem KRElemDefMethT) X))).
  - apply (KRSimplifyTop (KRMakeModule_regs (KRSimplify' (KRTypeList (KRTypeElem KRElemModuleElt)) X))).
  - apply (KRSimplifyTop (KRMakeModule_rules (KRSimplify' (KRTypeList (KRTypeElem KRElemModuleElt)) X))).
  - apply (KRSimplifyTop (KRMakeModule_meths (KRSimplify' (KRTypeList (KRTypeElem KRElemModuleElt)) X))).
Defined.

Definition KRSimplify t e := ltac:(let x := eval cbv in (@KRSimplify' t e) in exact x).

  (*refine (
      match e in KRExpr t return KRExpr t with
      | @KRCons tp2 a b => _
      | @KRApp t a b => _
      | @KRRegisters a => _
      | @KRMEMeth a => _
      | @KRMERule a => _
      | @KRMakeModule_rules a => _
      | @KRMakeModule_regs a => _
      | @KRMakeModule_meths a => _
      | e => e
      end).*)
  
(*Fixpoint KRSimplify {t} (e: KRExpr t) :=
  match e in KRExpr t return KRExpr t with
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
  end.*)

Theorem KRSimplifyTopSound: forall t e,
    @KRExprDenote t e = @KRExprDenote t (@KRSimplifyTop t e).
Proof.
  destruct e; simpl; auto.
  - destruct t; simpl; auto.
    dependent destruction e1; simpl; auto.
    dependent destruction e1; simpl; auto.
  - dependent destruction e; simpl; auto.
    rewrite Registers_dist_append.
    reflexivity.
  - dependent destruction e; simpl; auto.
    dependent destruction e1; simpl; auto.
    + rewrite makeModule_regs_append.
      reflexivity.
    + rewrite makeModule_regs_Registers.
      reflexivity.
  - dependent destruction e; simpl; auto.
    + dependent destruction e1; simpl; auto.
    + rewrite makeModule_rules_append.
      reflexivity.
  - dependent destruction e; simpl; auto.
    + dependent destruction e1; simpl; auto.
    + rewrite makeModule_meths_append.
      reflexivity.
Qed.

Opaque KRSimplifyTop.

Theorem KRSimplifySound: forall t e, @KRExprDenote t e = @KRExprDenote t (@KRSimplify t e).
Proof.
  intros.
  induction e.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - simpl.
    remember (KRSimplify e1).
    dependent destruction k;try (subst;simpl;simpl in IHe1;rewrite IHe1;simpl;rewrite <- IHe2;reflexivity).
  - simpl.
    rewrite <- IHe.
    reflexivity.
  - simpl.
    remember (KRSimplify e).
    dependent destruction k;try(simpl in IHe;rewrite IHe;reflexivity).
    + rewrite IHe.
      simpl.
      rewrite Registers_dist_append.
      reflexivity.
  - simpl.
    rewrite <- IHe.
    reflexivity.
  - simpl.
    rewrite <- IHe.
    reflexivity.
  - simpl.
    remember (KRSimplify e).
    dependent destruction k;try (simpl in IHe;rewrite IHe;reflexivity).
    + dependent destruction k1;try (rewrite IHe;simpl;reflexivity).
    + rewrite IHe.
      simpl.
      rewrite makeModule_regs_append.
      reflexivity.
    + rewrite IHe.
      simpl.
      rewrite makeModule_regs_Registers.
      reflexivity.
  - simpl.
    remember (KRSimplify e).
    dependent destruction k;try (simpl in IHe;rewrite IHe;reflexivity).
    + dependent destruction k1;try (rewrite IHe;simpl;reflexivity).
    + rewrite IHe.
      simpl.
      rewrite makeModule_rules_append.
      reflexivity.
  - simpl.
    remember (KRSimplify e).
    dependent destruction k;try (simpl in IHe;rewrite IHe;reflexivity).
    + dependent destruction k1;try (rewrite IHe;simpl;reflexivity).
    + rewrite IHe.
      simpl.
      rewrite makeModule_meths_append.
      reflexivity.
Qed.

Transparent KRSimplifyTop.

  (*induction e; simpl; auto.
  - rewrite <- IHe1.
    rewrite <- IHe2.
    reflexivity.
  - destruct t; simpl; auto.
    + destruct k; simpl; (try rewrite <- IHe1); (try rewrite <- IHe2);auto.
      remember (KRSimplify e1).
      dependent destruction k; simpl; (try rewrite IHe1); simpl; (try rewrite IHe2); auto.
    + rewrite <- IHe1.
      rewrite <- IHe2.
      reflexivity.
  - rewrite <- IHe.
    reflexivity.
  - dependent destruction e;simpl;auto.
    + simpl in IHe.
      injection IHe.
      intros.
      rewrite H.
      rewrite H0.
      reflexivity.
    + simpl in IHe.
      rewrite IHe.
      rewrite Registers_dist_append.
      reflexivity.
    + remember (KRSimplify e).
      dependent destruction k; simpl; auto.
      * simpl in IHe.
      
Admitted.*)


Ltac KRSimplifyTac e :=
  let x := (ltac:(KRExprReify e t)) in
  let t := eval compute in (KRTypeDenote x) in
  let xx := (ltac:(KRExprReify e t)) in
    change e with (KRExprDenote xx);
    repeat (rewrite KRSimplifySound;
            cbv [KRSimplify KRSimplifyTop]);cbv [KRExprDenote].

  (*match type of e with
  | ?t =>
    let x := (ltac:(KRExprReify e t)) in
    change e with (KRExprDenote x);
    rewrite KRSimplifySound;
    cbv [KRSimplify KRSimplifyTop KRExprDenote]
  end.*)

Ltac KRPrintReify e :=
  let x := (ltac:(KRExprReify e t)) in
  let t := eval compute in (KRTypeDenote x) in
  let xx := (ltac:(KRExprReify e t)) in
      idtac t;idtac x.

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A
  end.
Abort.
Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A
         end.
Abort.
Goal forall a b c d e, makeModule_rules [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A
         end.
Abort.
Goal forall a b c d e, makeModule_meths [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A
  end.
Abort.
Goal forall e, makeModule_regs []=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A
  end.
Abort.
