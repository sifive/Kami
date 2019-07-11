Require Import Syntax.

(* TODO: move to KamiStdLib? *)
(* Definition extractArbitraryRange ty sz (inst: Bit sz ## ty) (range: nat * nat): *)
(*   Bit (fst range + 1 - snd range) ## ty := *)
(*   (LETE i <- inst ; *)
(*      RetE (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range) *)
(*                         (ZeroExtendTruncLsb _ #i)))%kami_expr. *)
Definition extractArbitraryRange ty sz (inst: LetExprSyntax ty (Bit sz)) (range: nat * nat): LetExprSyntax ty (Bit (Init.Nat.sub (Init.Nat.add (fst range) (S O)) (snd range))) :=
  LetE inst
       (fun i : ty (Bit sz) =>
          NormExpr
            (ConstExtract (snd range) (Init.Nat.sub (Init.Nat.add (fst range) (S O)) (snd range))
                          (Init.Nat.sub (Init.Nat.sub sz (S O)) (fst range))
                          (ZeroExtendTruncLsb
                             (Init.Nat.add
                                (Init.Nat.add (snd range) (Init.Nat.sub (Init.Nat.add (fst range) (S O)) (snd range)))
                                (Init.Nat.sub (Init.Nat.sub sz (S O)) (fst range))) (Var ty (SyntaxKind (Bit sz)) i)))).

(* Useful Struct:
   TODO: move notation versions to StdLibKami*)
(* Definition Maybe k :=  STRUCT_TYPE { *)
(*                            "valid" :: Bool; *)
(*                            "data"  :: k }. *)
Definition Maybe k := getStruct [("valid", Bool);
                                    ("data", k)].

(* Definition Pair (A B: Kind) := STRUCT_TYPE { *)
(*                                    "fst" :: A; *)
(*                                    "snd" :: B }. *)
Definition Pair (A B: Kind) := getStruct [("fst", A);
                                            ("snd", B)].


(* Definition Invalid {ty: Kind -> Type} {k} := (STRUCT { "valid" ::= $$ false ; "data" ::= $$ (getDefaultConst k) })%kami_expr. *)
Definition Invalid {ty: Kind -> Type} {k} :=
  BuildStruct
  (fun
     i : t
           (Datatypes.length
              (map (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
                 (cons
                    (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                       (pair
                          (String (Ascii false true true false true true true false)
                             (String (Ascii true false false false false true true false)
                                (String (Ascii false false true true false true true false)
                                   (String (Ascii true false false true false true true false)
                                      (String (Ascii false false true false false true true false) EmptyString))))) Bool)
                       (Const ty false))
                    (cons
                       (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                          (pair
                             (String (Ascii false false true false false true true false)
                                (String (Ascii true false false false false true true false)
                                   (String (Ascii false false true false true true true false)
                                      (String (Ascii true false false false false true true false) EmptyString)))) k)
                          (Const ty (getDefaultConst k))) nil)))) =>
   snd
     (nth_Fin
        (map (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
           (cons
              (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                 (pair
                    (String (Ascii false true true false true true true false)
                       (String (Ascii true false false false false true true false)
                          (String (Ascii false false true true false true true false)
                             (String (Ascii true false false true false true true false)
                                (String (Ascii false false true false false true true false) EmptyString))))) Bool) 
                 (Const ty false))
              (cons
                 (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                    (pair
                       (String (Ascii false false true false false true true false)
                          (String (Ascii true false false false false true true false)
                             (String (Ascii false false true false true true true false)
                                (String (Ascii true false false false false true true false) EmptyString)))) k)
                    (Const ty (getDefaultConst k))) nil))) i))
  (fun
     j : t
           (Datatypes.length
              (map (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
                 (cons
                    (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                       (pair
                          (String (Ascii false true true false true true true false)
                             (String (Ascii true false false false false true true false)
                                (String (Ascii false false true true false true true false)
                                   (String (Ascii true false false true false true true false)
                                      (String (Ascii false false true false false true true false) EmptyString))))) Bool)
                       (Const ty false))
                    (cons
                       (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                          (pair
                             (String (Ascii false false true false false true true false)
                                (String (Ascii true false false false false true true false)
                                   (String (Ascii false false true false true true true false)
                                      (String (Ascii true false false false false true true false) EmptyString)))) k)
                          (Const ty (getDefaultConst k))) nil)))) =>
   fst
     (nth_Fin
        (map (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
           (cons
              (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                 (pair
                    (String (Ascii false true true false true true true false)
                       (String (Ascii true false false false false true true false)
                          (String (Ascii false false true true false true true false)
                             (String (Ascii true false false true false true true false)
                                (String (Ascii false false true false false true true false) EmptyString))))) Bool) 
                 (Const ty false))
              (cons
                 (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                    (pair
                       (String (Ascii false false true false false true true false)
                          (String (Ascii true false false false false true true false)
                             (String (Ascii false false true false true true true false)
                                (String (Ascii true false false false false true true false) EmptyString)))) k)
                    (Const ty (getDefaultConst k))) nil))) j))
  (fun
     k0 : t
            (Datatypes.length
               (map (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
                  (cons
                     (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                        (pair
                           (String (Ascii false true true false true true true false)
                              (String (Ascii true false false false false true true false)
                                 (String (Ascii false false true true false true true false)
                                    (String (Ascii true false false true false true true false)
                                       (String (Ascii false false true false false true true false) EmptyString))))) Bool)
                        (Const ty false))
                     (cons
                        (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                           (pair
                              (String (Ascii false false true false false true true false)
                                 (String (Ascii true false false false false true true false)
                                    (String (Ascii false false true false true true true false)
                                       (String (Ascii true false false false false true true false) EmptyString)))) k)
                           (Const ty (getDefaultConst k))) nil)))) =>
   nth_Fin_map2 (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
     (fun x : prod string Kind => Expr ty (SyntaxKind (snd x)))
     (cons
        (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
           (pair
              (String (Ascii false true true false true true true false)
                 (String (Ascii true false false false false true true false)
                    (String (Ascii false false true true false true true false)
                       (String (Ascii true false false true false true true false)
                          (String (Ascii false false true false false true true false) EmptyString))))) Bool) 
           (Const ty false))
        (cons
           (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
              (pair
                 (String (Ascii false false true false false true true false)
                    (String (Ascii true false false false false true true false)
                       (String (Ascii false false true false true true true false)
                          (String (Ascii true false false false false true true false) EmptyString)))) k) (Const ty (getDefaultConst k)))
           nil)) k0
     (projT2
        (nth_Fin
           (cons
              (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                 (pair
                    (String (Ascii false true true false true true true false)
                       (String (Ascii true false false false false true true false)
                          (String (Ascii false false true true false true true false)
                             (String (Ascii true false false true false true true false)
                                (String (Ascii false false true false false true true false) EmptyString))))) Bool) 
                 (Const ty false))
              (cons
                 (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                    (pair
                       (String (Ascii false false true false false true true false)
                          (String (Ascii true false false false false true true false)
                             (String (Ascii false false true false true true true false)
                                (String (Ascii true false false false false true true false) EmptyString)))) k)
                    (Const ty (getDefaultConst k))) nil))
           (cast k0
              (map_length_red (projT1 (P:=fun a : prod string Kind => Expr ty (SyntaxKind (snd a))))
                 (cons
                    (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                       (pair
                          (String (Ascii false true true false true true true false)
                             (String (Ascii true false false false false true true false)
                                (String (Ascii false false true true false true true false)
                                   (String (Ascii true false false true false true true false)
                                      (String (Ascii false false true false false true true false) EmptyString))))) Bool)
                       (Const ty false))
                    (cons
                       (existT (fun a : prod string Kind => Expr ty (SyntaxKind (snd a)))
                          (pair
                             (String (Ascii false false true false false true true false)
                                (String (Ascii true false false false false true true false)
                                   (String (Ascii false false true false true true true false)
                                      (String (Ascii true false false false false true true false) EmptyString)))) k)
                          (Const ty (getDefaultConst k))) nil))))))).
