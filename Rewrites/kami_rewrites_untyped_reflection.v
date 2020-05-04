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

(*Fixpoint KRExprDenote' (tp:KRType) (e: KRExpr) : option (KRTypeDenote tp).
  refine (match e return option (KRTypeDenote tp) with
  (*| KRNil t => _
  | KRVar t e => _*)
  | KRCons t a b => match (KRExprDenote' t a),(KRExprDenote' (KRTypeList t) b) with
                    | Some a',Some b' => _
                    | _,_ => None
                    end
  (*| KRApp t a b => _
  | KRMERegister e => _
  | KRMERule r => _
  | KRMEMeth m => _
  | KRMakeModule_regs r => _
  | KRMakeModule_rules r => _
  | KRMakeModule_meths m => _
  | KRRegisters l => _
  | KRMethods l => _
  | KRRules l => _
  | KRgetRegisters l => _
  | KRgetAllRegisters l => _
  | KRgetRules l => _
  | KRgetAllRules l => _
  | KRgetMethods l => _
  | KRgetAllMethods l => _
  | KRMakeModule l => _
  | KRBaseMod regs rules meths => _
  | KRBase b => _*)
  | _ => None
  end).
  (* - assert ({KRTypeList t=tp}+{KRTypeList t<>tp}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        apply (Some (@nil (KRTypeDenote t))).
      * apply None.
  - assert ({t=tp}+{t<>tp}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        apply (Some e).
      * apply None. *)
  - remember (beq_KRType (KRTypeList t) tp).
    destruct b0.
    + apply beq_KRType_eq in Heqb0.
      subst.
      apply (Some (cons a' b')).
    + apply None.
  (*assert ({KRTypeList (KRExprType a)=tp}+{KRTypeList (KRExprType a)<>tp}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRExprType a=t}+{KRExprType a<>t}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              assert ({KRExprType b=KRTypeList (KRExprType a)}+{KRExprType b<>KRTypeList (KRExprType a)}).
              ** repeat (decide equality).
              ** destruct H.
                 --- apply (match (KRExprDenote' (KRExprType a) a),(KRExprDenote' (KRTypeList (KRExprType a)) b) with
                             | Some a',Some b' => Some (cons a' b')
                             | _,_ => None
                            end).
                 --- apply None.
           ++ apply None.
      * apply None.*)
  (* - assert ({KRExprType a=tp}+{KRExprType a<>tp}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRExprType b=KRExprType a}+{KRExprType b<>KRExprType a}).
        -- repeat (decide equality).
        -- destruct H.
           ++ assert ({KRExprType a=KRTypeList t}+{KRExprType a<>KRTypeList t}).
              ** repeat (decide equality).
              ** destruct H.
                 --- refine (match (KRExprDenote' (KRExprType a) a),(KRExprDenote' (KRExprType a) b) with
                             | Some a',Some b' => Some (_)
                             | _,_ => None
                             end).
                     rewrite e1 in a'.
                     rewrite e1 in b'.
                     rewrite e1.
                     apply (app a' b').
                 --- apply None.
           ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemRegInitT=KRExprType e}+{KRTypeElem KRElemRegInitT<>KRExprType e}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeElem KRElemModuleElt}+{tp<>KRTypeElem KRElemModuleElt}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeElem KRElemRegInitT) e with
                     | Some e' => Some (MERegister e')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemRegInitT)=KRExprType l}+{KRTypeList (KRTypeElem KRElemRegInitT)<>KRExprType l}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeList (KRTypeElem KRElemModuleElt)}+{tp<>KRTypeList (KRTypeElem KRElemModuleElt)}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemRegInitT)) l with
                     | Some e' => Some (Registers e')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemRule)=KRExprType l}+{KRTypeList (KRTypeElem KRElemRule)<>KRExprType l}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeList (KRTypeElem KRElemModuleElt)}+{tp<>KRTypeList (KRTypeElem KRElemModuleElt)}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemRule)) l with
                     | Some l' => Some (Rules l')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemDefMethT)=KRExprType l}+{KRTypeList (KRTypeElem KRElemDefMethT)<>KRExprType l}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeList (KRTypeElem KRElemModuleElt)}+{tp<>KRTypeList (KRTypeElem KRElemModuleElt)}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemDefMethT)) l with
                     | Some e' => Some (Methods e')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemRule=KRExprType r}+{KRTypeElem KRElemRule<>KRExprType r}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeElem KRElemModuleElt}+{tp<>KRTypeElem KRElemModuleElt}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeElem KRElemRule) r with
                     | Some r' => Some (MERule r')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemDefMethT=KRExprType m}+{KRTypeElem KRElemDefMethT<>KRExprType m}).
    + repeat (decide equality).
    + destruct H.
      * assert ({tp=KRTypeElem KRElemModuleElt}+{tp<>KRTypeElem KRElemModuleElt}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeElem KRElemDefMethT) m with
                     | Some m' => Some (MEMeth m')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRegInitT)}+{tp<>KRTypeList (KRTypeElem KRElemRegInitT)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemBaseModule) l with
                      | Some l' => Some (getRegisters l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRegInitT)}+{tp<>KRTypeList (KRTypeElem KRElemRegInitT)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemMod) l with
                      | Some l' => Some (getAllRegisters l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRule)}+{tp<>KRTypeList (KRTypeElem KRElemRule)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemBaseModule) l with
                      | Some l' => Some (getRules l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRule)}+{tp<>KRTypeList (KRTypeElem KRElemRule)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemMod) l with
                      | Some l' => Some (getAllRules l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemDefMethT)}+{tp<>KRTypeList (KRTypeElem KRElemDefMethT)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemBaseModule) l with
                      | Some l' => Some (getMethods l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemDefMethT)}+{tp<>KRTypeList (KRTypeElem KRElemDefMethT)}).
    + repeat (decide equality).
    + destruct H.
      * subst.
        assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
        -- repeat (decide equality).
        -- destruct H.
           ** refine (match KRExprDenote' (KRTypeElem KRElemMod) l with
                      | Some l' => Some (getAllMethods l')
                      | None => None
                      end).
           ** apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRegInitT)}+{tp<>KRTypeList (KRTypeElem KRElemRegInitT)}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType r}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType r}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemModuleElt)) r with
                     | Some r' => Some (makeModule_regs r')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemRule)}+{tp<>KRTypeList (KRTypeElem KRElemRule)}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType r}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType r}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemModuleElt)) r with
                     | Some r' => Some (makeModule_rules r')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({tp=KRTypeList (KRTypeElem KRElemDefMethT)}+{tp<>KRTypeList (KRTypeElem KRElemDefMethT)}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType m}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType m}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemModuleElt)) m with
                     | Some m' => Some (makeModule_meths m')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType l}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType l}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeElem KRElemBaseModule=tp}+{KRTypeElem KRElemBaseModule<>tp}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemModuleElt)) l with
                     | Some l' => Some (makeModule l')
                     | None => None
                     end).
           ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemBaseModule=tp}+{KRTypeElem KRElemBaseModule<>tp}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeList (KRTypeElem KRElemRegInitT)=KRExprType regs}+{KRTypeList (KRTypeElem KRElemRegInitT)<>KRExprType regs}).
        -- repeat (decide equality).
        -- destruct H.
           ++ assert ({KRTypeList (KRTypeElem KRElemRule)=KRExprType rules}+{KRTypeList (KRTypeElem KRElemRule)<>KRExprType rules}).
              ** repeat (decide equality).
              ** destruct H.
                 --- assert ({KRTypeList (KRTypeElem KRElemDefMethT)=KRExprType meths}+{KRTypeList (KRTypeElem KRElemDefMethT)<>KRExprType meths}).
                     +++ repeat (decide equality).
                     +++ destruct H.
                         *** subst.
                             apply (match KRExprDenote' (KRTypeList (KRTypeElem KRElemRegInitT)) regs,KRExprDenote' (KRTypeList (KRTypeElem KRElemRule)) rules,KRExprDenote' (KRTypeList (KRTypeElem KRElemDefMethT)) meths with
                                     | Some regs',Some rules',Some meths' => Some (BaseMod regs' rules' meths')
                                     | _,_,_ => None
                                     end).
                         *** apply None.
                --- apply None.
           ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemMod=tp}+{KRTypeElem KRElemMod<>tp}).
    + repeat (decide equality).
    + destruct H.
      * assert ({KRTypeElem KRElemBaseModule=KRExprType b}+{KRTypeElem KRElemBaseModule<>KRExprType b}).
        -- repeat (decide equality).
        -- destruct H.
           ++ subst.
              apply (match KRExprDenote' (KRTypeElem KRElemBaseModule) b with
                     | Some b' => Some (Base b')
                     | None => None
                     end).
           ++ apply None.
      * apply None. *)
Defined.

(*Opaque app.
Opaque map.
Opaque Registers.
Opaque KRTypeDenote.*)

Inductive KRExprOption :=
| KROption_Some : forall (tp: KRType), (KRTypeDenote tp) -> KRExprOption
| KROption_None : KRExprOption.

Fixpoint KRExprDenote (e:KRExpr) : KRExprOption :=
  match e with
  | KRNil tp => KROption_Some (KRTypeList tp) nil
  | KRVar tp v => KROption_Some tp v
  | KRCons tp f r => match KRExprDenote f,KRExprDenote r with
                     | KROption_Some tp1 f', KROption_ListModuleElt r' => KROption_ListModuleElt (cons f' r')
                     | _,_ => KROption_None
                     end
  (*| KRCons (KRTypeList (KRTypeElem KRElemModuleElt)) f r => match KRExprDenote f,KRExprDenote r with
                                                            | KROption_ListModuleElt f', KROption_ListListModuleElt r' => KROption_ListListModuleElt (cons f' r')
                                                            | _,_ => KROption_None
                                                            end*)
  | KRCons _ _ _ => KROption_None
  | KRApp _ _ _ =>  KROption_None
  | KRMERegister e => KROption_None
  | KRMERule r => KROption_None
  | KRMEMeth m => KROption_None
  | KRMakeModule_regs r => KROption_None
  | KRMakeModule_rules r => KROption_None
  | KRMakeModule_meths m => KROption_None
  | KRRegisters l => KROption_None
  | KRMethods l => KROption_None
  | KRRules l => KROption_None
  | KRgetRegisters l => KROption_None
  | KRgetAllRegisters l => KROption_None
  | KRgetRules l => KROption_None
  | KRgetAllRules l => KROption_None
  | KRgetMethods l => KROption_None
  | KRgetAllMethods l => KROption_None
  | KRMakeModule l => KROption_None
  | KRBaseMod regs rules meths => KROption_None
  | KRBase b => KROption_None
  end.*)

Inductive KRExprOption :=
  | KROption_ModuleElt : ModuleElt -> KRExprOption
  | KROption_RegInitT : RegInitT -> KRExprOption
  | KROption_Rule : Attribute (Action Void) -> KRExprOption
  | KROption_DefMethT : DefMethT -> KRExprOption
  | KROption_BaseModule : BaseModule -> KRExprOption
  | KROption_Mod : Mod -> KRExprOption
  | KROption_ListModuleElt : list ModuleElt -> KRExprOption
  | KROption_ListListModuleElt : list (list ModuleElt) -> KRExprOption
  | KROption_ListRegInitT : list RegInitT -> KRExprOption
  | KROption_ListRule : list (Attribute (Action Void)) -> KRExprOption
  | KROption_ListDefMethT : list DefMethT -> KRExprOption
  | KROption_ListBaseModule : list BaseModule -> KRExprOption
  | KROption_ListMod : list Mod -> KRExprOption
  | KROption_None : KRExprOption.

Fixpoint KRExprDenote (e:KRExpr) : KRExprOption :=
  match e with
  | KRNil t => match t with
               | (KRTypeElem KRElemModuleElt) => KROption_ListModuleElt nil
               | (KRTypeList (KRTypeElem KRElemModuleElt)) => KROption_ListListModuleElt nil
               | (KRTypeElem KRElemRegInitT) => KROption_ListRegInitT nil
               | (KRTypeElem KRElemRule) => KROption_ListRule nil
               | (KRTypeElem KRElemDefMethT) => KROption_ListDefMethT nil
               | _ => KROption_None
               end
  | KRVar (KRTypeElem KRElemModuleElt) e => KROption_ModuleElt e
  | KRVar (KRTypeElem KRElemRegInitT) e => KROption_RegInitT e
  | KRVar (KRTypeElem KRElemRule) e => KROption_Rule e
  | KRVar (KRTypeElem KRElemDefMethT) e => KROption_DefMethT e
  | KRVar (KRTypeElem KRElemBaseModule) e => KROption_BaseModule e
  | KRVar (KRTypeElem KRElemMod) e => KROption_Mod e
  | KRVar (KRTypeList (KRTypeElem KRElemModuleElt)) e => KROption_ListModuleElt e
  | KRVar (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) e => KROption_ListListModuleElt e
  | KRVar (KRTypeList (KRTypeElem KRElemRegInitT)) e => KROption_ListRegInitT e
  | KRVar (KRTypeList (KRTypeElem KRElemRule)) e => KROption_ListRule e
  | KRVar (KRTypeList (KRTypeElem KRElemDefMethT)) e => KROption_ListDefMethT e
  | KRVar (KRTypeList (KRTypeElem KRElemBaseModule)) e => KROption_ListBaseModule e
  | KRVar (KRTypeList (KRTypeElem KRElemMod)) e => KROption_ListMod e
  | KRVar _ _ => KROption_None
  | KRCons (KRTypeElem KRElemModuleElt) f r => match KRExprDenote f,KRExprDenote r with
                                               | KROption_ModuleElt f', KROption_ListModuleElt r' => KROption_ListModuleElt (cons f' r')
                                               | _,_ => KROption_None
                                               end
  | KRCons (KRTypeElem KRElemRegInitT) f r => match KRExprDenote f,KRExprDenote r with
                                              | KROption_RegInitT f', KROption_ListRegInitT r' => KROption_ListRegInitT (cons f' r')
                                              | _,_ => KROption_None
                                              end
  | KRCons (KRTypeElem KRElemRule) f r => match KRExprDenote f,KRExprDenote r with
                                          | KROption_Rule f', KROption_ListRule r' => KROption_ListRule (cons f' r')
                                          | _,_ => KROption_None
                                          end
  | KRCons (KRTypeElem KRElemDefMethT) f r => match KRExprDenote f,KRExprDenote r with
                                          | KROption_DefMethT f', KROption_ListDefMethT r' => KROption_ListDefMethT (cons f' r')
                                          | _,_ => KROption_None
                                          end
  | KRCons (KRTypeElem KRElemBaseModule) f r => match KRExprDenote f,KRExprDenote r with
                                          | KROption_BaseModule f', KROption_ListBaseModule r' => KROption_ListBaseModule (cons f' r')
                                          | _,_ => KROption_None
                                          end
  | KRCons (KRTypeElem KRElemMod) f r => match KRExprDenote f,KRExprDenote r with
                                         | KROption_Mod f', KROption_ListMod r' => KROption_ListMod (cons f' r')
                                         | _,_ => KROption_None
                                         end
  | KRCons (KRTypeList (KRTypeElem KRElemModuleElt)) f r => match KRExprDenote f,KRExprDenote r with
                                                            | KROption_ListModuleElt f', KROption_ListListModuleElt r' => KROption_ListListModuleElt (cons f' r')
                                                            | _,_ => KROption_None
                                                            end
  | KRCons _ _ _ => KROption_None
  | KRApp (KRTypeElem KRElemModuleElt) f r => match KRExprDenote f,KRExprDenote r with
                                              | KROption_ListModuleElt f', KROption_ListModuleElt r' => KROption_ListModuleElt (app f' r')
                                              | _,_ => KROption_None
                                              end
  | KRApp (KRTypeElem KRElemRegInitT) f r => match KRExprDenote f,KRExprDenote r with
                                             | KROption_ListRegInitT f', KROption_ListRegInitT r' => KROption_ListRegInitT (app f' r')
                                             | _,_ => KROption_None
                                             end
  | KRApp (KRTypeElem KRElemRule) f r => match KRExprDenote f,KRExprDenote r with
                                         | KROption_ListRule f', KROption_ListRule r' => KROption_ListRule (app f' r')
                                         | _,_ => KROption_None
                                         end
  | KRApp (KRTypeElem KRElemDefMethT) f r => match KRExprDenote f,KRExprDenote r with
                                             | KROption_ListDefMethT f', KROption_ListDefMethT r' => KROption_ListDefMethT (app f' r')
                                             | _,_ => KROption_None
                                             end
  | KRApp (KRTypeElem KRElemBaseModule) f r => match KRExprDenote f,KRExprDenote r with
                                               | KROption_ListBaseModule f', KROption_ListBaseModule r' => KROption_ListBaseModule (app f' r')
                                               | _,_ => KROption_None
                                               end
  | KRApp (KRTypeElem KRElemMod) f r => match KRExprDenote f,KRExprDenote r with
                                        | KROption_ListMod f', KROption_ListMod r' => KROption_ListMod (app f' r')
                                        | _,_ => KROption_None
                                        end
  | KRApp (KRTypeList (KRTypeElem KRElemModuleElt)) f r => match KRExprDenote f,KRExprDenote r with
                                                           | KROption_ListModuleElt f', KROption_ListListModuleElt r' => KROption_ListListModuleElt (cons f' r')
                                                           | _,_ => KROption_None
                                                           end
  | KRApp _ _ _ =>  KROption_None
  | KRMERegister r => match KRExprDenote r with
                      | KROption_RegInitT r' => KROption_ModuleElt (MERegister r')
                      | _ => KROption_None
                      end
  | KRMERule r => match KRExprDenote r with
                  | KROption_Rule r' => KROption_ModuleElt (MERule r')
                  | _ => KROption_None
                  end
  | KRMEMeth m => match KRExprDenote m with
                  | KROption_DefMethT m' => KROption_ModuleElt (MEMeth m')
                  | _ => KROption_None
                  end
  | KRMakeModule_regs r => match KRExprDenote r with
                           | KROption_ListModuleElt r' => KROption_ListRegInitT (makeModule_regs r')
                           | _ => KROption_None
                           end
  | KRMakeModule_rules r => match KRExprDenote r with
                            | KROption_ListModuleElt r' => KROption_ListRule (makeModule_rules r')
                            | _ => KROption_None
                            end
  | KRMakeModule_meths m => match KRExprDenote m with
                            | KROption_ListModuleElt m' => KROption_ListDefMethT (makeModule_meths m')
                            | _ => KROption_None
                            end
  | KRRegisters l => match KRExprDenote l with
                     | KROption_ListRegInitT l' => KROption_ListModuleElt (Registers l')
                     | _ => KROption_None
                     end
  | KRMethods l => match KRExprDenote l with
                   | KROption_ListDefMethT l' => KROption_ListModuleElt (Methods l')
                   | _ => KROption_None
                   end
  | KRRules l => match KRExprDenote l with
                 | KROption_ListRule l' => KROption_ListModuleElt (Rules l')
                 | _ => KROption_None
                 end
  | KRgetRegisters l => match KRExprDenote l with
                        | KROption_BaseModule b' => KROption_ListRegInitT (getRegisters b')
                        | _ => KROption_None
                        end
  | KRgetAllRegisters l => match KRExprDenote l with
                           | KROption_Mod m' => KROption_ListRegInitT (getAllRegisters m')
                           | _ => KROption_None
                           end
  | KRgetRules l => match KRExprDenote l with
                    | KROption_BaseModule b' => KROption_ListRule (getRules b')
                    | _ => KROption_None
                    end
  | KRgetAllRules l => match KRExprDenote l with
                       | KROption_Mod m' => KROption_ListRule (getAllRules m')
                       | _ => KROption_None
                       end
  | KRgetMethods l => match KRExprDenote l with
                      | KROption_BaseModule b' => KROption_ListDefMethT (getMethods b')
                      | _ => KROption_None
                      end
  | KRgetAllMethods l => match KRExprDenote l with
                         | KROption_Mod m' => KROption_ListDefMethT (getAllMethods m')
                         | _ => KROption_None
                         end
  | KRMakeModule l => match KRExprDenote l with
                      | KROption_ListModuleElt l' => KROption_Mod (makeModule l')
                      | _ => KROption_None
                      end
  | KRBaseMod regs rules meths => match KRExprDenote regs,KRExprDenote rules,KRExprDenote meths with
                                  | KROption_ListRegInitT regs',KROption_ListRule rules',KROption_ListDefMethT meths' => KROption_BaseModule (BaseMod regs' rules' meths')
                                  | _,_,_ => KROption_None
                                  end
  | KRBase b => match KRExprDenote b with
                | KROption_BaseModule b' => KROption_Mod (Base b')
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
     (*match f with
     | @KRCons (KRTypeElem KRElemModuleElt) a b =>
       @KRCons (KRTypeElem KRElemModuleElt) a (@KRApp (KRTypeElem KRElemModuleElt) b c)
     | @
     | _ => @KRApp (KRTypeElem KRElemModuleElt) f c
     end*)
  | KRRegisters x => match x with
                     | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRRegisters f) (KRRegisters r)
                     | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMERegister f) (KRRegisters r)
                     | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                     | _ => KRRegisters x
                     end
     (*match x with
     | @KRApp (KRTypeElem KRElemRegInitT) a b =>
       @KRApp (KRTypeElem KRElemModuleElt) (KRRegisters a) (KRRegisters b)
     | @KRCons (KRTypeElem KRElemRegInitT) a b =>
       @KRCons (KRTypeElem KRElemModuleElt) (KRMERegister a) (KRRegisters b)
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemModuleElt)
     | e => KRRegisters e
     end
   | KRRules x => _
   | KRMethods x => _
   | KRgetRegisters x => _
   | KRgetAllRegisters x => _
   | KRgetRules x => _
   | KRgetAllRules x => _
   | KRgetMethods x => _
   | KRgetAllMethods x => _
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
     end*)*)
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
  induction e.
  - reflexivity.
  - reflexivity.
  - rewrite KRSimplifyCons.
    rewrite <- KRSimplifyTopSound.
    destruct k.
    + destruct k; try (simpl; rewrite <- IHe1; rewrite <- IHe2; reflexivity).
    + destruct k.
      * destruct k; try (simpl; try (rewrite <- IHe1; rewrite <- IHe2); reflexivity).
      * reflexivity.
  -
Admitted.

Theorem sum_elim: forall tp (x:tp) (y:tp), Some x=Some y -> x=y.
  intros.
  inversion H.
  subst.
  reflexivity.
Qed.

(*Goal forall (a:ModuleElt) (b:list ModuleElt) c, app (cons a b) c=cons a (app b c).
  intros.
  match goal with
  | |- ?A = ?B => let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                  let H := fresh in
                  assert (Some A = (KRExprDenote (KRTypeList (KRTypeElem KRElemModuleElt)) (KRSimplify x))) as H;[
                      rewrite <- KRSimplifySound;[compute [KRExprDenote KRExprDenote']; reflexivity |
                                                  simpl; reflexivity |
                                                  compute [KRExprDenote KRExprDenote' KRTypeDenote KRElemDenote KRExprType]; (*eapply ex_intro;reflexivity*) idtac] |
                                                  cbv [KRSimplify KRSimplifyTop KRExprDenote KRExprDenote'] in H]
  end.
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
