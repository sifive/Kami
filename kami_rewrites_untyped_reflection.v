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

Inductive KRType : Type :=
  | KRTypeElem: KRElem -> KRType
  | KRTypeList: KRType -> KRType.

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


Fixpoint KRExprDenote' (e: KRExpr) : option (KRTypeDenote (KRExprType e)).
  refine (match e return option (KRTypeDenote (KRExprType e)) with
  | KRNil t => Some (@nil (KRTypeDenote t))
  | KRVar t e => Some e
  | KRCons t a b => _
  | KRApp t a b => _
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
  | KRBase b => _
  end).
  - assert ({KRExprType a=t}+{KRExprType a<>t}).
        repeat (decide equality).
      destruct H.
    + subst.
      assert ({KRTypeList (KRExprType a)=KRExprType b}+{KRTypeList (KRExprType a)<>KRExprType b}).
        repeat (decide equality).
      destruct H.
      * refine (match KRExprDenote' a,KRExprDenote' b with
               | Some a',Some b' => Some (_)
               | _,_ => None
               end).
        rewrite <- e0 in b'.
        apply (cons a' b').
      * apply None.
    + apply None.
  - assert ({KRExprType a=KRTypeList t}+{KRExprType a<>KRTypeList t}).
        repeat (decide equality).
      destruct H.
    + subst.
      assert ({KRExprType a=KRExprType b}+{KRExprType a<>KRExprType b}).
        repeat (decide equality).
      destruct H.
      * refine (match KRExprDenote' a,KRExprDenote' b with
               | Some a',Some b' => Some (_)
               | _,_ => None
                end).
        simpl.
        rewrite <- e1 in b'.
        rewrite e0 in a'.
        rewrite e0 in b'.
        apply (app a' b').
      * apply None.
    + apply None.
  - assert ({KRTypeElem KRElemRegInitT=KRExprType e}+{KRTypeElem KRElemRegInitT<>KRExprType e}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' e with
                | Some e' => _
                | None => None
                end).
        rewrite <- e1 in e'.
        simpl.
        simpl in e'.
        apply (Some (MERegister e')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemRegInitT)=KRExprType l}+{KRTypeList (KRTypeElem KRElemRegInitT)<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (Registers l')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemRule)=KRExprType l}+{KRTypeList (KRTypeElem KRElemRule)<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (Rules l')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemDefMethT)=KRExprType l}+{KRTypeList (KRTypeElem KRElemDefMethT)<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (Methods l')).
      * apply None.
  - assert ({KRTypeElem KRElemRule=KRExprType r}+{KRTypeElem KRElemRule<>KRExprType r}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' r with
                | Some r' => _
                | None => None
                end).
        rewrite <- e0 in r'.
        simpl.
        simpl in r'.
        apply (Some (MERule r')).
      * apply None.
  - assert ({KRTypeElem KRElemDefMethT=KRExprType m}+{KRTypeElem KRElemDefMethT<>KRExprType m}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' m with
                | Some m' => _
                | None => None
                end).
        rewrite <- e0 in m'.
        simpl.
        simpl in m'.
        apply (Some (MEMeth m')).
      * apply None.
  - assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getRegisters l')).
      * apply None.
  - assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getAllRegisters l')).
      * apply None.
  - assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getRules l')).
      * apply None.
  - assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getAllRules l')).
      * apply None.
  - assert ({KRTypeElem KRElemBaseModule=KRExprType l}+{KRTypeElem KRElemBaseModule<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getMethods l')).
      * apply None.
  - assert ({KRTypeElem KRElemMod=KRExprType l}+{KRTypeElem KRElemMod<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (getAllMethods l')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType r}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType r}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' r with
                | Some r' => _
                | None => None
                end).
        rewrite <- e0 in r'.
        simpl.
        simpl in r'.
        apply (Some (makeModule_regs r')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType r}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType r}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' r with
                | Some r' => _
                | None => None
                end).
        rewrite <- e0 in r'.
        simpl.
        simpl in r'.
        apply (Some (makeModule_rules r')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType m}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType m}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' m with
                | Some m' => _
                | None => None
                end).
        rewrite <- e0 in m'.
        simpl.
        simpl in m'.
        apply (Some (makeModule_meths m')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemModuleElt)=KRExprType l}+{KRTypeList (KRTypeElem KRElemModuleElt)<>KRExprType l}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' l with
                | Some l' => _
                | None => None
                end).
        rewrite <- e0 in l'.
        simpl.
        simpl in l'.
        apply (Some (makeModule l')).
      * apply None.
  - assert ({KRTypeList (KRTypeElem KRElemRegInitT)=KRExprType regs}+{KRTypeList (KRTypeElem KRElemRegInitT)<>KRExprType regs}).
      repeat (decide equality).
    + destruct H.
      * assert ({KRTypeList (KRTypeElem KRElemRule)=KRExprType rules}+{KRTypeList (KRTypeElem KRElemRule)<>KRExprType rules}).
          repeat (decide equality).
      -- destruct H.
         ++ assert ({KRTypeList (KRTypeElem KRElemDefMethT)=KRExprType meths}+{KRTypeList (KRTypeElem KRElemDefMethT)<>KRExprType meths}).
            repeat (decide equality).
         ** destruct H.
            --- refine (match KRExprDenote' regs,KRExprDenote' rules,KRExprDenote' meths with
                | Some regs',Some rules',Some meths' => _
                | _,_,_ => None
                end).
                rewrite <- e0 in regs'.
                rewrite <- e1 in rules'.
                rewrite <- e2 in meths'.
                simpl.
                simpl in regs'.
                simpl in rules'.
                simpl in meths'.
                apply (Some (BaseMod regs' rules' meths')).
            --- apply None.
         ++ apply None.
      * apply None.
  - assert ({KRTypeElem KRElemBaseModule=KRExprType b}+{KRTypeElem KRElemBaseModule<>KRExprType b}).
      repeat (decide equality).
    + destruct H.
      * refine (match KRExprDenote' b with
                | Some b' => _
                | None => None
                end).
        rewrite <- e0 in b'.
        simpl.
        simpl in b'.
        apply (Some (Base b')).
      * apply None.
Defined.

Definition KRExprDenote'' e := ltac:(let x := eval cbv in (@KRExprDenote' e) in exact x).

Fixpoint KRExprDenote (tp:KRType) (e:KRExpr) : option (KRTypeDenote tp).
  assert({tp=KRExprType e}+{tp<>KRExprType e}).
    repeat (decide equality).
  - destruct H.
    + subst.
      apply (KRExprDenote'' e).
    + apply None.
Defined.
    
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
   (*| KRRegisters x => _
     (*match x with
     | @KRApp (KRTypeElem KRElemRegInitT) a b =>
       @KRApp (KRTypeElem KRElemModuleElt) (KRRegisters a) (KRRegisters b)
     | @KRCons (KRTypeElem KRElemRegInitT) a b =>
       @KRCons (KRTypeElem KRElemModuleElt) (KRMERegister a) (KRRegisters b)
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemModuleElt)
     | e => KRRegisters e
     end*)
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
    (exists q, Some q=KRExprDenote (KRExprType e) e) -> KRExprDenote (KRExprType e) e = KRExprDenote (KRExprType e) (KRSimplifyTop e).
Admitted. (*Proof.
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
Qed.*)

(*Opaque KRSimplifyTop.

Theorem KRSimplifySound: forall t e, @KRExprDenote t e = @KRExprDenote t (@KRSimplify t e).
Admitted. (*Proof.
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
Qed.*)

Transparent KRSimplifyTop.

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
*)
