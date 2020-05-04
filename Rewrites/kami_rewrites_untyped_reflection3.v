Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.

Inductive KRElem: Type :=
| KRElemRegInitT : KRElem
| KRElemRule : KRElem
| KRElemDefMethT : KRElem
| KRElemModuleElt: KRElem
| KRElemMod : KRElem
| KRElemBaseModule : KRElem.

Definition KRElemDenote (t: KRElem) :=
  match t with
  | KRElemRegInitT => RegInitT
  | KRElemRule => Attribute (Action Void)
  | KRElemDefMethT => DefMethT
  | KRElemModuleElt => ModuleElt
  | KRElemMod => Mod
  | KRElemBaseModule => BaseModule
  end.

Fixpoint KRElem_decb (a:KRElem) (b:KRElem) :=
  match a,b with
  | KRElemRegInitT,KRElemRegInitT => true
  | KRElemRule,KRElemRule => true
  | KRElemDefMethT,KRElemDefMethT => true
  | KRElemModuleElt,KRElemModuleElt => true
  | KRElemMod,KRElemMod => true
  | KRElemBaseModule,KRElemBaseModule => true
  | _,_ => false
  end.

Theorem KRElem_decb_refl: forall a, KRElem_decb a a=true.
Proof.
  destruct a; reflexivity.
Qed.

Theorem KRElem_decb_eq: forall a b, true=KRElem_decb a b <-> a=b.
Proof.
  intros; destruct a; destruct b; simpl; split;intro H;inversion H;reflexivity.
Qed.

Theorem KRElem_dec (k1 k2 : KRElem): {k1 = k2} + {k1 <> k2}.
Proof.
  destruct (KRElem_decb k1 k2) eqn:G.
  left; abstract (apply eq_sym in G; rewrite KRElem_decb_eq in G; auto).
  right; abstract (intro;
                   rewrite <- KRElem_decb_eq in H;
                   rewrite <- H in G; discriminate).
Defined.

Inductive KRType : Type :=
  | KRTypeElem: KRElem -> KRType
  | KRTypeList: KRType -> KRType.


Fixpoint KRType_decb (a:KRType) (b:KRType) :=
  match a,b with
  | KRTypeElem a',KRTypeElem b' => KRElem_decb a' b'
  | KRTypeList a',KRTypeList b' => KRType_decb a' b'
  | _,_ => false
  end.

Theorem KRType_decb_eq: forall a b, true=KRType_decb a b <-> a=b.
Proof.
  intro a.
  induction a.
  - intros.
    destruct b.
    * simpl.
      split.
      ++ intros.
         rewrite KRElem_decb_eq in H.
         subst.
         reflexivity.
      ++ intros.
         inversion H.
         subst.
         rewrite KRElem_decb_eq.
         reflexivity.
    * simpl.
      split; intros; inversion H.
  - intros.
    destruct b.
    * simpl.
      split; intros; inversion H.
    * simpl.
      rewrite IHa.
      split.
      ++ intros.
         subst.
         reflexivity.
      ++ intros.
         inversion H.
         subst.
         reflexivity.
Qed.

Theorem KRType_decb_refl: forall x, KRType_decb x x=true.
Proof.
  intros.
  induction x.
  - simpl.
    rewrite KRElem_decb_refl.
    reflexivity.
  - apply IHx.
Qed.

Theorem KRType_dec (k1 k2 : KRType): {k1 = k2} + {k1 <> k2}.
Proof.
  destruct (KRType_decb k1 k2) eqn:G.
  left; abstract (apply eq_sym in G;rewrite KRType_decb_eq in G; auto).
  right; abstract (intro;
                   rewrite <- KRType_decb_eq in H;
                   rewrite <- H in G; discriminate).
Defined.

Fixpoint KRTypeDenote (t: KRType) :=
  match t with
  | KRTypeElem t' => KRElemDenote t'
  | KRTypeList t => list (KRTypeDenote t)
  end.

Inductive KRExpr: Type :=
  | KRNil : KRType -> KRExpr
  | KRVar : forall (t:KRType), KRTypeDenote t -> KRExpr
  | KRCons : KRType -> KRExpr -> KRExpr -> KRExpr
  | KRApp : KRType -> KRExpr -> KRExpr -> KRExpr
  | KRMERegister : KRExpr -> KRExpr
  | KRRegisters : KRExpr -> KRExpr
  | KRRules : KRExpr -> KRExpr
  | KRMethods : KRExpr -> KRExpr
  | KRMERule : KRExpr -> KRExpr
  | KRMEMeth : KRExpr -> KRExpr
  | KRgetRegisters : KRExpr -> KRExpr
  | KRgetAllRegisters : KRExpr -> KRExpr
  | KRgetRules : KRExpr -> KRExpr
  | KRgetAllRules : KRExpr -> KRExpr
  | KRgetMethods : KRExpr -> KRExpr
  | KRgetAllMethods : KRExpr -> KRExpr
  | KRMakeModule_regs : KRExpr -> KRExpr
  | KRMakeModule_rules : KRExpr -> KRExpr
  | KRMakeModule_meths : KRExpr -> KRExpr
  | KRMakeModule : KRExpr -> KRExpr
  | KRBaseMod : KRExpr -> KRExpr -> KRExpr -> KRExpr
  | KRBase : KRExpr -> KRExpr.

Definition KRExprType (e: KRExpr) :=
  match e with
  | KRNil tp => KRTypeList tp
  | KRVar tp val => tp
  | KRCons tp f r => KRTypeList tp
  | KRApp tp f r => KRTypeList tp
  | KRMERegister r => KRTypeElem KRElemModuleElt
  | KRRegisters r => KRTypeList (KRTypeElem KRElemModuleElt)
  | KRRules r => KRTypeList (KRTypeElem KRElemModuleElt)
  | KRMethods r => KRTypeList (KRTypeElem KRElemModuleElt)
  | KRMERule r => KRTypeElem KRElemModuleElt
  | KRMEMeth r => KRTypeElem KRElemModuleElt
  | KRgetRegisters r => KRTypeList (KRTypeElem KRElemRegInitT)
  | KRgetAllRegisters r => KRTypeList (KRTypeElem KRElemRegInitT)
  | KRgetRules r => KRTypeList (KRTypeElem KRElemRule)
  | KRgetAllRules r => KRTypeList (KRTypeElem KRElemRule)
  | KRgetMethods r => KRTypeList (KRTypeElem KRElemDefMethT)
  | KRgetAllMethods r => KRTypeList (KRTypeElem KRElemDefMethT)
  | KRMakeModule_regs r => KRTypeList (KRTypeElem KRElemRegInitT)
  | KRMakeModule_rules r => KRTypeList (KRTypeElem KRElemRule)
  | KRMakeModule_meths m => KRTypeList (KRTypeElem KRElemDefMethT)
  | KRBaseMod re ru me => KRTypeElem KRElemBaseModule
  | KRMakeModule l => KRTypeElem KRElemBaseModule
  | KRBase m => KRTypeElem KRElemMod
  end.

Inductive KRExprOption :=
| KROption_Some : forall (tp: KRType), (KRTypeDenote tp) -> KRExprOption
| KROption_None : KRExprOption.

Fixpoint KRExprDenote (e:KRExpr) : KRExprOption :=
  match e with
  | KRNil tp => KROption_Some (KRTypeList tp) nil
  | KRVar tp v => KROption_Some tp v
  | KRCons tp f r => match KRExprDenote f, KRExprDenote r with
                     | KROption_Some tp1 f', KROption_Some (KRTypeList tp2) r' =>
                       match KRType_dec tp1 tp2 with
                       | left isEq => match KRType_dec tp2 tp with
                                      | left _ => KROption_Some (KRTypeList tp2) (cons match isEq in _ = Y return KRTypeDenote Y with
                                                                                       | eq_refl => f'
                                                                                       end r')
                                      | right _ => KROption_None
                                      end
                       | right _ => KROption_None
                       end
                     | _,_ => KROption_None
                     end
  | KRApp tp f r => match KRExprDenote f, KRExprDenote r with
                     | KROption_Some (KRTypeList tp1) f', KROption_Some (KRTypeList tp2) r' =>
                       match KRType_dec tp1 tp2 with
                       | left isEq => match KRType_dec tp tp2 with
                                      | left _ => KROption_Some (KRTypeList tp2) (app match isEq in _ = Y return KRTypeDenote (KRTypeList Y) with
                                                                                      | eq_refl => f'
                                                                                      end r')
                                      | right _ => KROption_None
                                      end
                       | right _ => KROption_None
                       end
                     | _,_ => KROption_None
                     end
  | KRMERegister e => match KRExprDenote e with
                      | KROption_Some (KRTypeElem KRElemRegInitT) e' => KROption_Some (KRTypeElem KRElemModuleElt) (MERegister e')
                      | _ => KROption_None
                      end
  | KRMERule e => match KRExprDenote e with
                  | KROption_Some (KRTypeElem KRElemRule) e' => KROption_Some (KRTypeElem KRElemModuleElt) (MERule e')
                  | _ => KROption_None
                  end
  | KRMEMeth e => match KRExprDenote e with
                  | KROption_Some (KRTypeElem KRElemDefMethT) m' => KROption_Some (KRTypeElem KRElemModuleElt) (MEMeth m')
                  | _ => KROption_None
                  end
  | KRMakeModule_regs r => match KRExprDenote r with
                           | KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) r' => KROption_Some (KRTypeList (KRTypeElem KRElemRegInitT)) (makeModule_regs r')
                           | _ => KROption_None
                           end
  | KRMakeModule_rules r => match KRExprDenote r with
                            | KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) r' => KROption_Some (KRTypeList (KRTypeElem KRElemRule)) (makeModule_rules r')
                            | _ => KROption_None
                            end
  | KRMakeModule_meths m => match KRExprDenote m with
                            | KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) m' => KROption_Some (KRTypeList (KRTypeElem KRElemDefMethT)) (makeModule_meths m')
                            | _ => KROption_None
                            end
  | KRRegisters l => match KRExprDenote l with
                     | KROption_Some (KRTypeList (KRTypeElem KRElemRegInitT)) l' => KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) (Registers l')
                     | _ => KROption_None
                     end
  | KRMethods l => match KRExprDenote l with
                   | KROption_Some (KRTypeList (KRTypeElem KRElemDefMethT)) l' => KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) (Methods l')
                   | _ => KROption_None
                   end
  | KRRules l => match KRExprDenote l with
                 | KROption_Some (KRTypeList (KRTypeElem KRElemRule)) l' => KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) (Rules l')
                 | _ => KROption_None
                 end
  | KRgetRegisters m => match KRExprDenote m with
                        | KROption_Some (KRTypeElem KRElemBaseModule) m' => KROption_Some (KRTypeList (KRTypeElem KRElemRegInitT)) (getRegisters m')
                        | _ => KROption_None
                        end
  | KRgetAllRegisters m => match KRExprDenote m with
                           | KROption_Some (KRTypeElem KRElemMod) m' => KROption_Some (KRTypeList (KRTypeElem KRElemRegInitT)) (getAllRegisters m')
                           | _ => KROption_None
                           end
  | KRgetRules m => match KRExprDenote m with
                    | KROption_Some (KRTypeElem KRElemBaseModule) m' => KROption_Some (KRTypeList (KRTypeElem KRElemRule)) (getRules m')
                    | _ => KROption_None
                    end
  | KRgetAllRules m => match KRExprDenote m with
                       | KROption_Some (KRTypeElem KRElemMod) m' => KROption_Some (KRTypeList (KRTypeElem KRElemRule)) (getAllRules m')
                       | _ => KROption_None
                       end
  | KRgetMethods m => match KRExprDenote m with
                    | KROption_Some (KRTypeElem KRElemBaseModule) m' => KROption_Some (KRTypeList (KRTypeElem KRElemDefMethT)) (getMethods m')
                    | _ => KROption_None
                    end
  | KRgetAllMethods m => match KRExprDenote m with
                       | KROption_Some (KRTypeElem KRElemMod) m' => KROption_Some (KRTypeList (KRTypeElem KRElemDefMethT)) (getAllMethods m')
                       | _ => KROption_None
                       end
  | KRMakeModule l => match KRExprDenote l with
                      | KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) l' => KROption_Some (KRTypeElem KRElemBaseModule) (makeModule l')
                      | _ => KROption_None
                      end
  | KRBaseMod regs rules meths => match KRExprDenote regs,KRExprDenote rules,KRExprDenote meths with
                                  | KROption_Some (KRTypeList (KRTypeElem KRElemRegInitT)) regs',
                                    KROption_Some (KRTypeList (KRTypeElem KRElemRule)) rules',
                                    KROption_Some (KRTypeList (KRTypeElem KRElemDefMethT)) meths' => KROption_Some (KRTypeElem KRElemBaseModule) (BaseMod regs' rules' meths')
                                  | _,_,_ => KROption_None
                                  end
  | KRBase b => match KRExprDenote b with
                | KROption_Some (KRTypeElem KRElemBaseModule) b' => KROption_Some (KRTypeElem KRElemMod) (Base b')
                | _ => KROption_None
                end
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
  | getRegisters ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemBaseModule))) in
                       constr:(@KRgetRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                          constr:(@KRgetAllRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                          constr:(@KRgetAllRegisters (@KRBase x))
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                          constr:(@KRgetAllRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                          constr:(@KRgetAllRegisters (@KRBase x))
  | MERule ?E => let  x := ltac:(KRExprReify E (KRTypeElem KRElemRule)) in
                     constr:(@KRMERule x)
  | Rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRule))) in
                         constr:(@KRRules x)
  | getRules ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                   constr:(@KRgetRules x)
  | getAllRules ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                      constr:(@KRgetAllRules x)
  | MEMeth ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemDefMethT)) in
                     constr:(@KRMEMeth x)
  | Methods ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemDefMethT))) in
                           constr:(@KRMethods x)
  | getMethods ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                     constr:(@KRgetMethods x)
  | getAllMethods ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                        constr:(@KRgetAllMethods x)
  | makeModule_regs ?X => let x := ltac:(KRExprReify X (KRTypeList (KRTypeElem KRElemModuleElt))) in
                              constr:(@KRMakeModule_regs x)
  | makeModule_rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in
                               constr:(@KRMakeModule_rules x)
  | makeModule_meths ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                           constr:(@KRMakeModule_meths x)
  | makeModule ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                     constr:(@KRMakeModule x)
  | BaseMod ?R ?U ?M => let regs := ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegInitT))) in
                        let rules := ltac:(KRExprReify U (KRTypeList (KRTypeElem KRElemRule))) in
                        let meths := ltac:(KRExprReify M (KRTypeList (KRTypeElem KRElemDefMethT))) in
                        constr:(@KRBaseMod regs rules meths)
  | Base ?B => let m := ltac:(KRExprReify B (KRTypeElem KRElemBaseModule)) in
               constr:(@KRBase m)
  | ?X => constr:(@KRVar t X)
  end.

Axiom cheat: forall x, x.
      
Definition KRSimplifyTop (e : KRExpr) : KRExpr :=
  match e with
  | KRApp tp f c => match f with
                    | KRCons ttp ff rr => KRCons tp ff (KRApp tp rr c)
                    | KRNil ttp => c
                    | x => match c with
                           | KRNil ttp => c
                           | y => KRApp tp f c
                           end
                    end
  | KRRegisters x => match x with
                     | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRRegisters f) (KRRegisters r)
                     | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMERegister f) (KRRegisters r)
                     | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                     | _ => KRRegisters x
                     end
  | KRRules x => match x with
                 | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRRules f) (KRRules r)
                 | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMERule f) (KRRules r)
                 | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                 | _ => KRRules x
                 end
  | KRMethods x => match x with
                   | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRMethods f) (KRMethods r)
                   | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMEMeth f) (KRMethods r)
                   | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                   | _ => KRMethods x
                   end
   (*| KRgetRegisters x => _
   | KRgetAllRegisters x => _
   | KRgetRules x => _
   | KRgetAllRules x => _
   | KRgetMethods x => _
   | KRgetAllMethods x =>*)
   | KRMakeModule_regs x =>
     match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemRegInitT) (KRMakeModule_regs a) (KRMakeModule_regs b)
     | KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa with
       | KRMERule a => KRMakeModule_regs b
       | KRMEMeth a => KRMakeModule_regs b
       | KRMERegister a => KRCons (KRTypeElem KRElemRegInitT) a (KRMakeModule_regs b)
       | _ => KRMakeModule_regs x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemRegInitT)
     | _ => KRMakeModule_regs x
     end
   | KRMakeModule_rules x =>
      match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemRule) (KRMakeModule_rules a) (KRMakeModule_rules b)
     | KRCons (KRTypeElem KRElemModuleElt) aa  b =>
       match aa with
       | KRMERegister a => KRMakeModule_rules b
       | KRMEMeth a => KRMakeModule_rules b
       | KRMERule a => KRCons (KRTypeElem KRElemRule) a (KRMakeModule_rules b)
       | _ => KRMakeModule_rules x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemRule)
     | qr => KRMakeModule_rules x
     end
   | KRMakeModule_meths x =>
     match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemDefMethT) (KRMakeModule_meths a) (KRMakeModule_meths b)
     | KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa with
       | KRMERule a => KRMakeModule_meths b
       | KRMERegister a => KRMakeModule_meths b
       | KRMEMeth a => @KRCons (KRTypeElem KRElemDefMethT) a (KRMakeModule_meths b)
       | _ => KRMakeModule_meths x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemDefMethT)
     | qm => KRMakeModule_meths x
     end
   | e => e
   end.

Fixpoint KRSimplify e : KRExpr :=
  KRSimplifyTop (match e with
  | KRNil tp => KRNil tp
  | KRVar tp val => KRVar tp val
  | KRCons tp f r => KRCons tp (KRSimplify f) (KRSimplify r)
  | KRApp tp f r => KRApp tp (KRSimplify f) (KRSimplify r)
  | KRMERegister r => KRMERegister (KRSimplify r)
  | KRRegisters r => KRRegisters (KRSimplify r)
  | KRRules r => KRRules (KRSimplify r)
  | KRMethods r => KRMethods (KRSimplify r)
  | KRMERule r => KRMERule (KRSimplify r)
  | KRMEMeth r => KRMEMeth (KRSimplify r)
  | KRgetRegisters r => KRgetRegisters (KRSimplify r)
  | KRgetAllRegisters r => KRgetAllRegisters (KRSimplify r)
  | KRgetRules r => KRgetRules (KRSimplify r)
  | KRgetAllRules r => KRgetAllRules (KRSimplify r)
  | KRgetMethods r => KRgetMethods (KRSimplify r)
  | KRgetAllMethods r => KRgetAllMethods (KRSimplify r)
  | KRMakeModule_regs r => KRMakeModule_regs (KRSimplify r)
  | KRMakeModule_rules r => KRMakeModule_rules (KRSimplify r)
  | KRMakeModule_meths m => KRMakeModule_meths (KRSimplify m)
  | KRBaseMod re ru me => KRBaseMod (KRSimplify re) (KRSimplify ru) (KRSimplify me)
  | KRMakeModule l => KRMakeModule (KRSimplify l)
  | KRBase m => KRBase (KRSimplify m)
  end).

Theorem KRSimplifyTopSound: forall e,
    KRExprDenote e = KRExprDenote (KRSimplifyTop e).
Admitted.
(*  intros.
  inversion H;subst;clear H.
  induction e.
  - cbv [KRSimplifyTop KRSimplify].
    reflexivity.
  - cbv [KRSimplifyTop KRSimplify].
    reflexivity.
  - cbv [KRSimplifyTop KRSimplify].
    rewrite
Qed.*)

Theorem KRSimplifyCons:
  forall tp f r, KRSimplify (KRCons tp f r)=KRSimplifyTop (KRCons tp (KRSimplify f) (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyCons : KRSimplify_simplify.

Theorem KRSimplifyApp:
  forall tp f r, KRSimplify (KRApp tp f r)=KRSimplifyTop (KRApp tp (KRSimplify f) (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyApp : KRSimplify_simplify.

Theorem KRSimplifyMERegister:
  forall r, KRSimplify (KRMERegister r)=KRSimplifyTop (KRMERegister (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMERegister : KRSimplify_simplify.

Theorem KRSimplifyRegisters:
  forall r, KRSimplify (KRRegisters r)=KRSimplifyTop (KRRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyRegisters : KRSimplify_simplify.

Theorem KRSimplifyRules:
  forall r, KRSimplify (KRRules r)=KRSimplifyTop (KRRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyRules : KRSimplify_simplify.

Theorem KRSimplifyMethods:
  forall r, KRSimplify (KRMethods r)=KRSimplifyTop (KRMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMethods : KRSimplify_simplify.

Theorem KRSimplifyMERule:
  forall r, KRSimplify (KRMERule r)=KRSimplifyTop (KRMERule (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMERule : KRSimplify_simplify.

Theorem KRSimplifyMEMeth:
  forall r, KRSimplify (KRMEMeth r)=KRSimplifyTop (KRMEMeth (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMEMeth : KRSimplify_simplify.

Theorem KRSimplifygetRegisters:
  forall r, KRSimplify (KRgetRegisters r)=KRSimplifyTop (KRgetRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetRegisters : KRSimplify_simplify.

Theorem KRSimplifygetAllRegisters:
  forall r, KRSimplify (KRgetAllRegisters r)=KRSimplifyTop (KRgetAllRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllRegisters : KRSimplify_simplify.

Theorem KRSimplifygetRules:
  forall r, KRSimplify (KRgetRules r)=KRSimplifyTop (KRgetRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetRules : KRSimplify_simplify.

Theorem KRSimplifygetAllRules:
  forall r, KRSimplify (KRgetAllRules r)=KRSimplifyTop (KRgetAllRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllRules : KRSimplify_simplify.

Theorem KRSimplifygetMethods:
  forall r, KRSimplify (KRgetMethods r)=KRSimplifyTop (KRgetMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetMethods : KRSimplify_simplify.

Theorem KRSimplifygetAllMethods:
  forall r, KRSimplify (KRgetAllMethods r)=KRSimplifyTop (KRgetAllMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllMethods : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_regs:
  forall r, KRSimplify (KRMakeModule_regs r)=KRSimplifyTop (KRMakeModule_regs (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_regs : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_rules:
  forall r, KRSimplify (KRMakeModule_rules r)=KRSimplifyTop (KRMakeModule_rules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_rules : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_meths:
  forall r, KRSimplify (KRMakeModule_meths r)=KRSimplifyTop (KRMakeModule_meths (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_meths : KRSimplify_simplify.

Theorem KRSimplifyMakeModule:
  forall r, KRSimplify (KRMakeModule r)=KRSimplifyTop (KRMakeModule (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule : KRSimplify_simplify.

Theorem KRSimplifyBase:
  forall r, KRSimplify (KRBase r)=KRSimplifyTop (KRBase (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyBase : KRSimplify_simplify.


(*Theorem KRExprDenoteKRCons: forall k f r, KRExprDenote (KRCons k f r)=match (KRExprDenote f),(KRExprDenote r) with
                                                                                      | KRSome f',Some r' => Some (cons f' r')
                                                                                      | _,_ => None
                                                                                      end.*)
(*Proof.
  intros.
  remember (KRExprDenote' k f).
  destruct o.
  -  remember (KRExprDenote' (KRTypeList k) r).
     destruct o.
     + simpl.
       rewrite <- Heqo.
       rewrite <- Heqo0.
       erewrite beq_KRType_refl at 1.
       simpl.*)

Theorem KRSimplifySound: forall e, KRExprDenote e = KRExprDenote (KRSimplify e).
Proof.
  intros.
  induction e; try (autorewrite with KRSimplify_simplify; rewrite <- KRSimplifyTopSound; simpl [KRExprDenote]; repeat (rewrite <- IHe)).
Admitted.
 (* - reflexivity.
  - reflexivity.
  - rewrite KRSimplifyCons.
    rewrite <- KRSimplifyTopSound.
    destruct k.
    + destruct k; try (simpl; rewrite <- IHe1; rewrite <- IHe2; reflexivity).
    + destruct k.
      * destruct k; try (simpl; try (rewrite <- IHe1; rewrite <- IHe2); reflexivity).
      * simpl. rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  - rewrite KRSimplifyApp.
    rewrite <- KRSimplifyTopSound.
    destruct k.
    + destruct k; try (simpl; rewrite <- IHe1; rewrite <- IHe2; reflexivity).
    + destruct k.
      * destruct k; try (simpl; try (rewrite <- IHe1; rewrite <- IHe2); reflexivity).
      * simpl. rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - rewrite KRSimplifyRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyRules.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMethods.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMERule.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMEMeth.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  -
    
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
Admitted.*)

Theorem sum_elim: forall tp (x:tp) (y:tp), Some x=Some y -> x=y.
  intros.
  inversion H.
  subst.
  reflexivity.
Qed.

Goal forall (a:ModuleElt) (b:list ModuleElt) c, app (cons a b) c=cons a (app b c).
  intros.
  match goal with
  | |- ?A = ?B => let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                  let H := fresh in
                  assert (KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) A = (KRExprDenote (KRSimplify x))) as H ; [ rewrite <- KRSimplifySound;idtac | idtac ]
                      (*rewrite <- KRSimplifySound;[compute [KRExprDenote]; reflexivity |
                                                  simpl; reflexivity |
                                                  compute [KRExprDenote KRTypeDenote KRElemDenote KRExprType]; (*eapply ex_intro;reflexivity*) idtac] |
                                                  cbv [KRSimplify KRSimplifyTop KRExprDenote] in H]*)
  end.
  assert (KRExprDenote (KRApp (KRTypeElem KRElemModuleElt) (KRVar (KRTypeList (KRTypeElem KRElemModuleElt)) c) (KRVar (KRTypeList (KRTypeElem KRElemModuleElt)) b))=KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) []).
  simpl.
  
Abort.

(*  destruct H.
  constructor H.
  rewrite H.
  cbv [KRExprDenote] in H.
  simpl [KRSimplify KRSimplifyTop] in H.
  simpl in H.
  match goal with

  end.


  
  compute in H.
  destruct H.*)

Ltac KRSimplifyTac e tp :=
       let x := (ltac:(KRExprReify e tp)) in
       let H := fresh in
                (assert (Some e = (KRExprDenote tp x)) as H;
                 [cbv [KRExprDenote KRExprDenote'];reflexivity | idtac];
                 repeat (rewrite KRSimplifySound in H;[cbv [KRSimplify KRSimplifyTop] in H |
                                                       simpl; reflexivity | compute [KRExprDenote KRExprDenote' KRTypeDenote KRElemDenote KRExprType]; eapply ex_intro; reflexivity]);
                cbv [KRExprDenote KRExprDenote'] in H;apply sum_elim in H;rewrite H;clear H).

(*Ltac KRPrintReify e :=
  let x := (ltac:(KRExprReify e t)) in
  let t := eval compute in (KRTypeDenote x) in
  let xx := (ltac:(KRExprReify e t)) in
      idtac t;idtac x.
 *)

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  match goal with
  | |- ?A = ?B => KRSimplifyTac A (KRTypeList (KRTypeElem KRElemModuleElt))
  end.
Abort.
Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.
Goal forall a b c d e, makeModule_rules [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRule))
  end.
Abort.
Goal forall a b c d e, makeModule_meths [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemDefMethT))
  end.
Abort.
Goal forall e, makeModule_regs []=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.*)
