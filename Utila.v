(*
  This library contains useful functions for generating Kami
  expressions.
 *)
Require Import Kami.Syntax Kami.Notations Kami.LibStruct.
Require Import List.
Import Word.Notations.
Require Import Kami.Lib.EclecticLib.
Import ListNotations.

Module EqIndNotations.
  Notation "A || B @ X 'by' E"
    := (eq_ind_r (fun X => B) A E) (at level 40, left associativity).

  Notation "A || B @ X 'by' <- H"
    := (eq_ind_r (fun X => B) A (eq_sym H)) (at level 40, left associativity).
End EqIndNotations.

Section utila.

  Open Scope kami_expr.

  Section defs.

    Variable ty : Kind -> Type.

    Fixpoint tagFrom val T (xs : list T) :=
      match xs with
      | nil => nil
      | y :: ys => (val, y) :: tagFrom (S val) ys
      end.

    Definition tag := @tagFrom 0.

    (* I. Kami Expression Definitions *)

    Definition msb
      (n m : nat)
      (width : Bit n @# ty)
      (x : Bit m @# ty)
      :  Bit m @# ty
      := x >> ($m - width).

    Definition lsb
      (n m : nat)
      (width : Bit n @# ty)
      (x : Bit m @# ty)
      :  Bit m @# ty
      := (x .& ~($$(wones m) << width)).

    Definition slice
      (n m k : nat)
      (offset : Bit n @# ty)
      (width : Bit m @# ty)
      (x : Bit k @# ty)
      :  Bit k @# ty
      := ((x >> offset) .& ~($$(wones k) << width)).

    Definition utila_opt_pkt
      (k : Kind)
      (x : k @# ty)
      (valid : Bool @# ty)
      :  Maybe k @# ty
      := STRUCT {
           "valid" ::= valid;
           "data"  ::= x
         }.

    Definition utila_opt_default
      (k : Kind)
      (default : k @# ty)
      (x : Maybe k @# ty)
      :  k @# ty
      := ITE (x @% "valid")
           (x @% "data")
           default.

    Definition utila_opt_bind
      (j k : Kind)
      (x : Maybe j @# ty)
      (f : j @# ty -> Maybe k @# ty)
      :  Maybe k @# ty
      := ITE (x @% "valid")
           (f (x @% "data"))
           (@Invalid ty k).

    Definition utila_all
      :  list (Bool @# ty) -> Bool @# ty
      (* := fold_right (fun x acc => x && acc) ($$true). *)
      := CABool And.

    Definition utila_any
      :  list (Bool @# ty) -> Bool @# ty
      (* := fold_right (fun x acc => x || acc) ($$false). *)
      := CABool Or.

    (*
      Note: [f] must only return true for exactly one value in
      [xs].
    *)
    Definition utila_find
      (k : Kind)
      (f : k @# ty -> Bool @# ty)
      (xs : list (k @# ty))
      :  k @# ty
      := unpack k (CABit Bor (map (fun x => IF f x then pack x else $0) xs)).

    (*
      Note: exactly one of the packets must be valid.
    *)
    Definition utila_find_pkt
      :  forall k : Kind, list (Maybe k @# ty) -> Maybe k @# ty
      := fun k => utila_find (fun x : Maybe k @# ty => x @% "valid").

    (*
      Note: the key match predicate must never return true for more
      than one entry in [entries].
    *)
    Definition utila_lookup_table
      (entry_type : Type)
      (entries : list entry_type)
      (result_kind : Kind)
      (entry_match : entry_type -> Bool @# ty)
      (entry_result : entry_type -> result_kind @# ty)
      :  Maybe result_kind @# ty
      := utila_find_pkt
           (map
             (fun entry
                => utila_opt_pkt 
                     (entry_result entry)
                     (entry_match entry))
             entries).

    (*
      Note: the key match predicate must never return true for more
      than one entry in [entries].
    *)
    Definition utila_lookup_table_default
      (entry_type : Type)
      (entries : list entry_type)
      (result_kind : Kind)
      (entry_match : entry_type -> Bool @# ty)
      (entry_result : entry_type -> result_kind @# ty)
      (default : result_kind @# ty)
      :  result_kind @# ty
      := utila_opt_default
           default
           (utila_lookup_table
              entries
              entry_match
              entry_result).

    (* II. Kami Monadic Definitions *)

    Structure utila_monad_type
      := utila_monad {
           utila_m
             : Kind -> Type;

           utila_mbind
             : forall (j k : Kind), utila_m j -> (ty j -> utila_m k) -> utila_m k;

           utila_munit
             : forall k : Kind, k @# ty -> utila_m k;

           utila_mite
             : forall k : Kind, Bool @# ty -> utila_m k -> utila_m k -> utila_m k
         }.

    Arguments utila_mbind {u} j k x f.

    Arguments utila_munit {u} k x.

    Arguments utila_mite {u} k b x y.

    Section monad_functions.

      Variable monad : utila_monad_type.

      Let m := utila_m monad.

      Let mbind := @utila_mbind monad.

      Let munit := @utila_munit monad.

      Let mite := @utila_mite monad.

      Definition utila_mopt_pkt
        (k : Kind)
        (x : k @# ty)
        (valid : Bool @# ty)
        :  m (Maybe k)
        := munit (utila_opt_pkt x valid).

      Definition utila_mopt_default
        (k : Kind)
        (default : k @# ty)
        (x_expr : m (Maybe k))
        :  m k
        := mbind k x_expr
             (fun x : ty (Maybe k)
                => mite k
                     ((Var ty (SyntaxKind (Maybe k)) x) @% "valid" : Bool @# ty)
                     (munit ((Var ty (SyntaxKind (Maybe k)) x) @% "data" : k @# ty))
                     (munit default)).

      Definition utila_mopt_bind
        (j k : Kind)
        (x_expr : m (Maybe j))
        (f : j @# ty -> m (Maybe k))
        :  m (Maybe k)
        := mbind (Maybe k) x_expr
             (fun x : ty (Maybe j)
               => mite (Maybe k)
                    ((Var ty (SyntaxKind (Maybe j)) x) @% "valid" : Bool @# ty)
                    (f ((Var ty (SyntaxKind (Maybe j)) x) @% "data"))
                    (munit (@Invalid ty k))).

      Definition utila_mfoldr
        (j k : Kind)
        (f : j @# ty -> k @# ty -> k @# ty)
        (init : k @# ty)
        :  list (m j) -> (m k)
        := fold_right
             (fun (x_expr : m j)
                  (acc_expr : m k)
                => mbind k x_expr
                     (fun x : ty j
                        => mbind k acc_expr
                             (fun acc : ty k
                                => munit
                                     (f (Var ty (SyntaxKind j) x)
                                        (Var ty (SyntaxKind k) acc)))))
             (munit init).

      Definition utila_mall
        :  list (m Bool) -> m Bool
        := utila_mfoldr (fun x acc => x && acc) (Const ty true).

      Definition utila_many
        :  list (m Bool) -> m Bool
        := utila_mfoldr (fun x acc => x || acc) (Const ty false).

      Definition utila_mfind
        (k : Kind)
        (f : k @# ty -> Bool @# ty)
        (x_exprs : list (m k))
        :  m k
        := mbind k
             (utila_mfoldr
               (fun (x : k @# ty) (acc : Bit (size k) @# ty)
                  => ((ITE (f x) (pack x) ($0)) .| acc))
               ($0)
               x_exprs)
             (fun (y : ty (Bit (size k)))
                => munit (unpack k (Var ty (SyntaxKind (Bit (size k))) y))).

      Definition utila_mfind_pkt
        (k : Kind)
        :  list (m (Maybe k)) -> m (Maybe k)
        := utila_mfind
             (fun (pkt : Maybe k @# ty)
                => pkt @% "valid").

    End monad_functions.

    Arguments utila_mopt_pkt {monad}.

    Arguments utila_mopt_default {monad}.

    Arguments utila_mopt_bind {monad}.

    Arguments utila_mfoldr {monad}.

    Arguments utila_mall {monad}.

    Arguments utila_many {monad}.

    Arguments utila_mfind {monad}.

    Arguments utila_mfind_pkt {monad}.

    (* III. Kami Let Expression Definitions *)

    Definition utila_expr_monad
      :  utila_monad_type
      := utila_monad (LetExprSyntax ty) (fun j k => @LetE ty k j) (@NormExpr ty)
           (fun (k : Kind) (b : Bool @# ty) (x_expr y_expr : k ## ty)
              => LETE x : k <- x_expr;
                 LETE y : k <- y_expr;
                 RetE (ITE b (#x) (#y))).

    Definition utila_expr_opt_pkt := @utila_mopt_pkt utila_expr_monad.

    Definition utila_expr_opt_default := @utila_mopt_default utila_expr_monad.

    Definition utila_expr_opt_bind := @utila_mopt_bind utila_expr_monad.

    Definition utila_expr_foldr := @utila_mfoldr utila_expr_monad.

    Definition utila_expr_all := @utila_mall utila_expr_monad.

    Definition utila_expr_any := @utila_many utila_expr_monad.

    (*
      Accepts a Kami predicate [f] and a list of Kami let expressions
      that represent values, and returns a Kami let expression that
      outputs the value that satisfies f.

      Note: [f] must only return true for exactly one value in
      [xs_exprs].
    *)
    Definition utila_expr_find
      (k : Kind)
      (f : k @# ty -> Bool @# ty)
      (xs_exprs : list (k ## ty))
      :  k ## ty
      := LETE y
         :  Bit (size k)
         <- (utila_expr_foldr
               (fun x acc => ((ITE (f x) (pack x) ($0)) .| acc))
               ($0)
               xs_exprs);
         RetE (unpack k (#y)).

    Arguments utila_expr_find {k} f xs_exprs.

    (*
      Accepts a list of Maybe packets and returns the packet whose
      valid flag equals true.

      Note: exactly one of the packets must be valid.
    *)
    Definition utila_expr_find_pkt
      (k : Kind)
      (pkt_exprs : list (Maybe k ## ty))
      :  Maybe k ## ty
      := utila_expr_find
           (fun (pkt : Maybe k @# ty)
            => pkt @% "valid")
           pkt_exprs.

    (*
      Generates a lookup table containing entries of type
      [result_kind].

      Note: the key match predicate must never return true for more
      than one entry in [entries].
    *)
    Definition utila_expr_lookup_table
      (entry_type : Type)
      (entries : list entry_type)
      (result_kind : Kind)
      (entry_match : entry_type -> Bool ## ty)
      (entry_result : entry_type -> result_kind ## ty)
      :  Maybe result_kind ## ty
      := utila_expr_find_pkt
           (map
             (fun entry : entry_type
                => LETE result
                     :  result_kind
                     <- entry_result entry;
                   LETE matched
                     :  Bool
                     <- entry_match entry;
                   utila_expr_opt_pkt #result #matched)
             entries).

    (*
      Generates a lookup table containing entries of type
      [result_kind]. Returns a default value for entries that do
      not exist.

      Note: the key match predicate must never return true for more
      than one entry in [entries].
    *)
    Definition utila_expr_lookup_table_default
      (entry_type : Type)
      (entries : list entry_type)
      (result_kind : Kind)
      (entry_match : entry_type -> Bool ## ty)
      (entry_result : entry_type -> result_kind ## ty)
      (default : result_kind @# ty)
      :  result_kind ## ty
      := utila_expr_opt_default
           default
           (utila_expr_lookup_table
              entries
              entry_match
              entry_result).

    (* IV. Kami Action Definitions *)

    Open Scope kami_action.

    Definition utila_act_monad
      :  utila_monad_type
      := utila_monad (@ActionT ty) (fun j k => @LetAction ty k j) (@Return ty)
           (fun k b (x y : ActionT ty k)
              => If b
                   then x
                   else y
                   as result;
                 Ret #result).

    Definition utila_acts_opt_pkt := @utila_mopt_pkt utila_act_monad.

    Definition utila_acts_opt_default := @utila_mopt_default utila_act_monad.

    Definition utila_acts_opt_bind := @utila_mopt_bind utila_act_monad.

    Definition utila_acts_foldr := @utila_mfoldr utila_act_monad.

    Definition utila_acts_all
      (xs : list (ActionT ty Bool))
      :  ActionT ty Bool
      := GatherActions xs as ys;
         Ret (CABool And ys).

    Definition utila_acts_any
      (xs : list (ActionT ty Bool))
      :  ActionT ty Bool
      := GatherActions xs as ys;
         Ret (CABool Or ys).

    Definition utila_acts_find
      (k : Kind)
      (f : k @# ty -> Bool @# ty)
      (xs : list (ActionT ty k))
      :  ActionT ty k
      := GatherActions xs as ys;
         Ret (utila_find f ys).

    Definition utila_acts_find_pkt
      (k : Kind)
      (xs : list (ActionT ty (Maybe k)))
      :  ActionT ty (Maybe k)
      := GatherActions xs as ys;
         Ret (utila_find_pkt ys).

    Close Scope kami_action.

  End defs.

  Arguments utila_mopt_pkt {ty} {monad} {k}.

  Arguments utila_mopt_default {ty} {monad} {k}.

  Arguments utila_mopt_bind {ty} {monad} {j} {k}.

  Arguments utila_mfoldr {ty} {monad} {j} {k}.

  Arguments utila_mall {ty} {monad}.

  Arguments utila_many {ty} {monad}.

  Arguments utila_mfind {ty} {monad} {k}.

  Arguments utila_mfind_pkt {ty} {monad} {k}.

  (* V. Correctness Proofs *)

  Section ver.

    Local Notation "{{ X }}" := (evalExpr X).

    Local Notation "X ==> Y" := (evalExpr X = Y) (at level 75).

    Local Notation "==> Y" := (fun x => evalExpr x = Y) (at level 75).

    Let utila_is_true (x : Bool @# type) := x ==> true.

    Lemma fold_left_andb_forall'
      :  forall (xs : list (Bool @# type)) a,
        fold_left andb (map (@evalExpr _)  xs) a = true <->
        Forall utila_is_true xs /\ a = true.
    Proof.
      induction xs; simpl; auto; split; intros; auto.
      - tauto.
      - rewrite IHxs in H.
        rewrite andb_true_iff in H.
        split; try tauto.
        constructor; simpl; tauto.
      - dest.
        inv H.
        unfold utila_is_true in *; simpl in *.
        pose proof (conj H4 H3).
        rewrite <- IHxs in H.
        auto.
    Qed.
        
    Theorem fold_left_andb_forall
      :  forall xs : list (Bool @# type),
        fold_left andb (map (@evalExpr _)  xs) true = true <->
        Forall utila_is_true xs.
    Proof.
      intros.
      rewrite fold_left_andb_forall'.
      tauto.
    Qed.
 
    Theorem utila_all_correct
      :  forall xs : list (Bool @# type),
        utila_all xs ==> true <-> Forall utila_is_true xs.
    Proof.
      apply fold_left_andb_forall.
    Qed.

    Theorem fold_left_andb_forall_false'
      :  forall (xs : list (Bool @# type)) a,
        fold_left andb (map (@evalExpr _)  xs) a = false <->
        Exists (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs \/ a = false.
    Proof.
      induction xs; simpl; auto; intros; split; try tauto.
      - intros; auto.
        destruct H; auto.
        inv H.
      - rewrite IHxs.
        intros.
        rewrite andb_false_iff in H.
        destruct H.
        + left.
          right; auto.
        + destruct H.
          * auto.
          * left.
            left.
            auto.
      - intros.
        rewrite IHxs.
        rewrite andb_false_iff.
        destruct H.
        + inv H; auto.
        + auto.
    Qed.
      
    Theorem fold_left_andb_forall_false
      :  forall xs : list (Bool @# type),
        fold_left andb (map (@evalExpr _)  xs) true = false <->
        Exists (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs.
    Proof.
      intros.
      rewrite fold_left_andb_forall_false'.
      split; intros.
      - destruct H; congruence.
      - auto.
    Qed.

    Theorem utila_all_correct_false
      :  forall xs : list (Bool @# type),
        utila_all xs ==> false <->
        Exists (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs.
    Proof.
      apply fold_left_andb_forall_false.
    Qed.

    Theorem fold_left_orb_exists'
      :  forall (xs : list (Bool @# type)) a,
        fold_left orb (map (@evalExpr _)  xs) a = true <->
          Exists utila_is_true xs \/ a = true.
    Proof.
      induction xs; simpl; auto; split; intros; try discriminate.
      - auto.
      - destruct H; auto.
        inv H.
      - rewrite IHxs in H.
        rewrite orb_true_iff in H.
        destruct H.
        + left.
          right.
          auto.
        + destruct H; auto.
      - assert (sth: Exists utila_is_true xs \/ (a0||evalExpr a)%bool = true). {
          destruct H.
          - inv H.
            + right.
              rewrite orb_true_iff.
              auto.
            + auto.
          - right.
            rewrite orb_true_iff.
            auto.
        }
        rewrite <- IHxs in sth.
        auto.
    Qed.
        

    Theorem fold_left_orb_exists
      :  forall xs : list (Bool @# type),
        fold_left orb (map (@evalExpr _)  xs) false = true <->
          Exists utila_is_true xs.
    Proof.
      intros.
      rewrite fold_left_orb_exists'.
      split; intros; auto.
      destruct H; congruence.
    Qed.
        

    Theorem utila_any_correct
      :  forall xs : list (Bool @# type),
        utila_any xs ==> true <-> Exists utila_is_true xs.
    Proof.
      apply fold_left_orb_exists.
    Qed.

    Theorem fold_left_orb_exists_false'
      :  forall (xs : list (Bool @# type)) a,
        fold_left orb (map (@evalExpr _)  xs) a = false <->
        Forall (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs /\ a = false.
    Proof.
      induction xs; simpl; split; auto; intros.
      - inv H; auto.
      - rewrite IHxs in H.
        rewrite orb_false_iff in H.
        split; try tauto.
        constructor; tauto.
      - dest.
        inv H.
        rewrite IHxs.
        rewrite orb_false_iff.
        repeat split; auto.
    Qed.

    Theorem fold_left_orb_exists_false
      :  forall xs : list (Bool @# type),
        fold_left orb (map (@evalExpr _)  xs) false = false <->
        Forall (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs.
    Proof.
      intros.
      rewrite fold_left_orb_exists_false'.
      split; intros; dest; auto.
    Qed.

    Lemma utila_any_correct_false:
      forall xs : list (Expr type (SyntaxKind Bool)),
        evalExpr (utila_any xs) = false <->
        Forall (fun x : Expr type (SyntaxKind Bool)
                 => evalExpr x = false) xs.
    Proof.
      apply fold_left_orb_exists_false.
    Qed.

  End ver.

  (* VI. Denotational semantics for monadic expressions. *)

  Structure utila_sem_type
    := utila_sem {
         utila_sem_m
           : utila_monad_type type;

         utila_sem_interp
           : forall k : Kind, utila_m utila_sem_m k -> type k;

         (*
           [[mbind x f]] = [[ f [[x]] ]]
         *)
         utila_sem_bind_correct
           : forall
               (j k : Kind)
               (x : utila_m utila_sem_m j)
               (f : type j -> utila_m utila_sem_m k),
               (utila_sem_interp k
                 (utila_mbind utila_sem_m j k x f)) =
               (utila_sem_interp k
                 (f (utila_sem_interp j x)));

         (*
           [[munit x]] = {{x}}
         *)
         utila_sem_unit_correct
           : forall (k : Kind) (x : k @# type),
               utila_sem_interp k (utila_munit (utila_sem_m) x) =
               evalExpr x;

         (*
           [[ mfoldr f init [] ]] = {{init}}
         *)
         utila_sem_foldr_nil_correct
           : forall (j k : Kind)
               (f : j @# type -> k @# type -> k @# type)
               (init : k @# type),
               (utila_sem_interp k
                  (utila_mfoldr f init nil) =
                evalExpr init);

         (*
           [[ mfoldr f init (x0 :: xs) ]] = {{ f #[[x0]] #[[mfoldr f init xs]] }}
         *)
         utila_sem_foldr_cons_correct
           :  forall (j k : Kind)
                (f : j @# type -> k @# type -> k @# type)
                (init : k @# type)
                (x0 : utila_m utila_sem_m j)
                (xs : list (utila_m utila_sem_m j)),
                (utila_sem_interp k
                   (utila_mfoldr f init (x0 :: xs)) =
                 (evalExpr
                    (f
                       (Var type (SyntaxKind j)
                          (utila_sem_interp j x0))
                       (Var type (SyntaxKind k)
                          (utila_sem_interp k
                             (utila_mfoldr f init xs))))))
       }.

  Arguments utila_sem_interp {u} {k} x.

  Arguments utila_sem_bind_correct {u} {j} {k} x f.

  Arguments utila_sem_unit_correct {u} {k} x.

  Arguments utila_sem_foldr_nil_correct {u} {j} {k}.

  Arguments utila_sem_foldr_cons_correct {u} {j} {k}.

  Section monad_ver.

    Import EqIndNotations.

    Variable sem : utila_sem_type.

    Let monad : utila_monad_type type := utila_sem_m sem.

    Let m := utila_m monad.

    Let mbind := utila_mbind monad.

    Let munit := utila_munit monad.

    Local Notation "{{ X }}" := (evalExpr X).

    Local Notation "[[ X ]]" := (@utila_sem_interp sem _ X).

    Local Notation "#{{ X }}" := (Var type (SyntaxKind _) {{X}}).

    Local Notation "#[[ X ]]" := (Var type (SyntaxKind _) [[X]]).

    Hint Rewrite 
      (@utila_sem_bind_correct sem)
      (@utila_sem_unit_correct sem)
      (@utila_sem_foldr_cons_correct sem)
      (@utila_sem_unit_correct sem)
      : utila_sem_rewrite_db.

    Let utila_is_true (x : m Bool)
      :  Prop
      := [[x]] = true.

    Lemma utila_mall_nil
      :  [[utila_mall ([] : list (m Bool))]] = true.
    Proof utila_sem_foldr_nil_correct
            (fun x acc => x && acc)
            (Const type true).

    Lemma utila_mall_cons
      :  forall (x0 : m Bool) (xs : list (m Bool)), [[utila_mall (x0 :: xs)]] = andb [[x0]] [[utila_mall xs]].
    Proof utila_sem_foldr_cons_correct
            (fun x acc => x && acc)
            (Const type true).

    Theorem utila_mall_correct
      :  forall xs : list (m Bool),
           [[utila_mall xs]] = true <-> Forall utila_is_true xs.
    Proof.
      intro.
      split.
        - induction xs.
          + intro; exact (Forall_nil utila_is_true).
          + intro H; assert (H0 : [[a]] = true /\ [[utila_mall xs]] = true).
            apply (@andb_prop [[a]] [[utila_mall xs]]).
            rewrite <- (utila_mall_cons a xs).
            assumption.
            apply (Forall_cons a).
            apply H0.
            apply IHxs; apply H0.
        - apply (Forall_ind (fun ys => [[utila_mall ys]] = true)).
          + apply utila_mall_nil.
          + intros y0 ys H H0 F.
            rewrite utila_mall_cons.
            apply andb_true_intro.
            auto.
      Qed.

    Lemma utila_many_nil
      :  [[utila_many ([] : list (m Bool)) ]] = false.
    Proof utila_sem_foldr_nil_correct
            (fun x acc => CABool Or [x; acc])
            (Const type false).

    Lemma utila_many_cons
      :  forall (x0 : m Bool) (xs : list (m Bool)), [[utila_many (x0 :: xs)]] = orb [[x0]] [[utila_many xs]].
    Proof utila_sem_foldr_cons_correct
            (fun x acc => CABool Or [x; acc])
            (Const type false).

    Theorem utila_many_correct
      :  forall xs : list (m Bool),
           [[utila_many xs]] = true <-> Exists utila_is_true xs.
    Proof
      fun xs
        => conj
             (list_ind
               (fun ys => [[utila_many ys]] = true -> Exists utila_is_true ys)
               (fun H : [[utila_many [] ]] = true
                 => let H0
                      :  false = true
                      := H || X = true  @X by <- utila_many_nil in
                    False_ind _ (diff_false_true H0))
               (fun y0 ys
                 (F : [[utila_many ys]] = true -> Exists utila_is_true ys)
                 (H : [[utila_many (y0 :: ys)]] = true)
                 => let H0
                      :  [[y0]] = true \/ [[utila_many ys]] = true
                      := orb_prop [[y0]] [[utila_many ys]]
                           (eq_sym
                             (utila_many_cons y0 ys
                              || X = _ @X by <- H)) in
                    match H0 with
                    | or_introl H1
                      => Exists_cons_hd utila_is_true y0 ys H1
                    | or_intror H1
                      => Exists_cons_tl y0 (F H1)
                    end)
               xs)
             (@Exists_ind
               (m Bool)
               utila_is_true
               (fun ys => [[utila_many ys]] = true)
               (fun y0 ys
                 (H : [[y0]] = true)
                 => orb_true_l [[utila_many ys]]
                    || orb X [[utila_many ys]] = true @X by H
                    || X = true                       @X by utila_many_cons y0 ys)
               (fun y0 ys
                 (H : Exists utila_is_true ys)
                 (F : [[utila_many ys]] = true)
                 => orb_true_r [[y0]]
                    || orb [[y0]] X = true @X by F
                    || X = true            @X by utila_many_cons y0 ys)
               xs).

    Definition utila_null (k : Kind)
      :  k @# type
      := unpack k (Var type (SyntaxKind (Bit (size k))) (natToWord (size k) 0)).

    Lemma utila_mfind_nil
      :  forall (k : Kind)
           (f : k @# type -> Bool @# type),
           [[utila_mfind f ([] : list (m k))]] = {{utila_null k}}.
    Proof
      fun k f
        => eq_refl {{utila_null k}}
           || X = {{utila_null k}}
              @X by utila_sem_unit_correct (unpack k (Var type (SyntaxKind (Bit (size k))) (natToWord (size k) 0)))
           || [[munit (unpack k (Var type (SyntaxKind (Bit (size k))) X))]] = {{utila_null k}}
              @X by utila_sem_foldr_nil_correct
                      (fun x acc => (ITE (f x) (pack x) ($0) .| acc))
                      ($0)
           || X = {{utila_null k}}
              @X by utila_sem_bind_correct
                      (utila_mfoldr
                         (fun x acc => (ITE (f x) (pack x) ($0) .| acc))
                         ($0)
                         [])
                      (fun y => munit (unpack k (Var type (SyntaxKind (Bit (size k))) y))).

    Lemma utila_mfind_tl
      :  forall (k : Kind)
           (f : k @# type -> Bool @# type)
           (x0 : m k)
           (xs : list (m k)),
           {{f #[[x0]]}} = false ->
           [[utila_mfind f (x0 :: xs)]] = [[utila_mfind f xs]].
    Proof.
      intros.
      unfold utila_mfind.
      autorewrite with utila_sem_rewrite_db.
      simpl.
      rewrite H.
      simpl.
      repeat (rewrite wor_wzero).
      reflexivity.

    Qed.

  End monad_ver.

  Section expr_ver.

    Import EqIndNotations.

    Local Notation "{{ X }}" := (evalExpr X).

    Local Notation "[[ X ]]" := (evalLetExpr X).

    Local Notation "#[[ X ]]" := (Var type (SyntaxKind _) [[X]]) (only parsing) : kami_expr_scope.

    Local Notation "X ==> Y" := (evalLetExpr X = Y) (at level 75).

    Local Notation "==> Y" := (fun x => evalLetExpr x = Y) (at level 75).

    Let utila_is_true (x : Bool ## type) := x ==> true.

    Let utila_expr_bind (j k : Kind) (x : j ## type) (f : type j -> k ## type)
      :  k ## type
      := @LetE type k j x f.

    Lemma utila_expr_bind_correct
      :  forall 
           (j k : Kind)
           (x : j ## type)
           (f : type j -> k ## type),
           [[utila_expr_bind x f]] = [[f [[x]] ]].
    Proof fun j k x f => (eq_refl [[utila_expr_bind x f]]).

    Lemma utila_expr_unit_correct
      :  forall (k : Kind) (x : k @# type), [[RetE x]] = {{x}}.
    Proof
       fun k x => eq_refl.

    Theorem utila_expr_foldr_correct_nil
      :  forall (j k : Kind) (f : j @# type -> k @# type -> k @# type) (init : k @# type),
        utila_expr_foldr f init nil ==> {{init}}.
    Proof
      fun j k f init
      => eq_refl ({{init}}).

    Theorem utila_expr_foldr_correct_cons
      :  forall (j k : Kind)
                (f : j @# type -> k @# type -> k @# type)
                (init : k @# type)
                (x0 : j ## type) (xs : list (j ## type)),
        [[utila_expr_foldr f init (x0 :: xs)]] =
        {{ f (Var type (SyntaxKind j) [[x0]])
             (Var type (SyntaxKind k) [[utila_expr_foldr f init xs]]) }}.
    Proof
      fun (j k : Kind)
          (f : j @# type -> k @# type -> k @# type)
          (init : k @# type)
          (x0 : j ## type)
          (xs : list (j ## type))
        => eq_refl.

    Definition utila_expr_sem
      :  utila_sem_type
      := utila_sem
           (utila_expr_monad type)
           evalLetExpr
           utila_expr_bind_correct
           utila_expr_unit_correct
           utila_expr_foldr_correct_nil
           utila_expr_foldr_correct_cons.

    Theorem utila_expr_all_correct
      :  forall xs : list (Bool ## type),
        utila_expr_all xs ==> true <-> Forall utila_is_true xs.
    Proof utila_mall_correct utila_expr_sem.

    Theorem utila_expr_any_correct
      :  forall xs : list (Bool ## type),
        utila_expr_any xs ==> true <-> Exists utila_is_true xs.
    Proof utila_many_correct utila_expr_sem.

    Lemma utila_ite_l
      :  forall (k : Kind) (x y : k @# type) (p : Bool @# type),
        {{p}} = true ->
        {{ITE p x y}} = {{x}}.
    Proof
      fun k x y p H
      => eq_ind
           true
           (fun q : bool => (if q then {{x}} else {{y}}) = {{x}})
           (eq_refl {{x}})
           {{p}}
           (eq_sym H).

    Lemma utila_ite_r
      :  forall (k : Kind) (x y : k @# type) (p : Bool @# type),
        {{p}} = false ->
        {{ITE p x y}} = {{y}}.
    Proof
      fun k x y p H
      => eq_ind
           false
           (fun q : bool => (if q then {{x}} else {{y}}) = {{y}})
           (eq_refl {{y}})
           {{p}}
           (eq_sym H).

    (*
      The following section proves that the utila_expr_find function
      is correct. To prove, this result we make three four intuitive
      conjectures and prove two lemmas about the expressions produced
      by partially reducing utila_expr_find.
    *)
    Section utila_expr_find.

      (* The clauses used in Kami switch expressions. *)
      Let case (k : Kind) (f : k @# type -> Bool @# type) (x : k @# type) (acc : Bit (size k) @# type)
        :  Bit (size k) @# type
        := (ITE (f x) (pack x) ($ 0) .| acc).

      Conjecture unpack_pack
        : forall (k : Kind)
            (x : k ## type),
            {{unpack k
                (Var type (SyntaxKind (Bit (size k)))
                   {{pack (Var type (SyntaxKind k) [[x]])}})}} =  
            [[x]].

      Conjecture kami_exprs_eq_dec
        : forall (k : Kind) (x y : k ## type),
          {x = y} + {x <> y}.

      Lemma kami_in_dec
        : forall (k : Kind) (x : k ## type) (xs : list (k ## type)),
          {In x xs} + {~ In x xs}.
      Proof
        fun k x xs
          => in_dec (@kami_exprs_eq_dec k) x xs.

      (*
        Note: submitted a pull request to the bbv repo to include this
        lemma in Word.v
      *)
      Lemma wor_idemp
        :  forall (n : nat) (x0 : word n), x0 ^| x0 = x0.
      Proof.
        (intros).
        (induction x0).
        reflexivity.
        (rewrite <- IHx0 at 3).
        (unfold wor).
        (simpl).
        (rewrite orb_diag).
        reflexivity.
      Qed.

      Lemma utila_expr_find_lm0
        :  forall (k : Kind)
                  (f : k @# type -> Bool @# type)
                  (init : Bit (size k) @# type)
                  (x0 : k ## type)
                  (xs : list (k ## type)),
          {{f (Var type (SyntaxKind k) [[x0]])}} = false ->
          [[utila_expr_foldr (case f) init (x0 :: xs)]] =
          [[utila_expr_foldr (case f) init xs]].
      Proof.
        (intros).
        (unfold evalLetExpr at 1).
        (unfold utila_expr_foldr at 1).
        (unfold utila_mfoldr).
        (intros).
        (simpl).
        (rewrite wor_wzero).
        (fold evalLetExpr).
        (fold utila_expr_foldr).
        (rewrite H).
        (rewrite wor_wzero).
        (unfold utila_expr_foldr).
        (unfold utila_mfoldr).
        (unfold utila_mbind).
        (simpl).
        reflexivity.
      Qed.

      Lemma utila_expr_find_lm1
        :  forall (k : Kind)
                  (f : k @# type -> Bool @# type)
                  (init : Bit (size k) @# type)
                  (xs : list (k ## type)),
          (forall x, In x xs -> {{f #[[x]]}} = false) ->
          [[utila_expr_foldr (case f) init xs]] = {{init}}.
      Proof
        fun (k : Kind)
            (f : k @# type -> Bool @# type)
            (init : Bit (size k) @# type)
        => list_ind
             (fun xs
              => (forall x, In x xs -> {{f #[[x]]}} = false) ->
                 [[utila_expr_foldr (case f) init xs]] = {{init}})
             (fun _
              => utila_expr_foldr_correct_nil (case f) init)
             (fun x0 xs
                  (F : (forall x, In x xs -> {{f #[[x]]}} = false) ->
                       [[utila_expr_foldr (case f) init xs]] = {{init}})
                  (H : forall x, In x (x0 :: xs) -> {{f #[[x]]}} = false)
              => let H0
                     :  forall x, In x xs -> {{f #[[x]]}} = false
                     := fun x H0
                        => H x (or_intror (x0 = x) H0) in
                 let H1
                     :  [[utila_expr_foldr (case f) init xs]] = {{init}}
                     := F H0 in
                 let H2
                     :  {{f #[[x0]]}} = false
                     := H x0 (or_introl (In x0 xs) (eq_refl x0)) in
                 utila_expr_find_lm0 f init x0 xs H2
                 || [[utila_expr_foldr (case f) init (x0 :: xs)]] = a
                                                                      @a by <- H1).

      (*
        This proof proceeds using proof by cases when [xs = y0 :: ys].
        There are four cases, either [x = y0] or [x <> y0] and either
        [In x ys] or [~ In x ys]. If [x = y0] then [{{case f y0}} = {{pack
        x0}}]. Otherwise [{{case f y0}} = {{$0}}]. Similarly, when [x]
        is in [ys], [[[utila_expr_fold _ _ ys]] = {{pack x}}]. Otherwise,
        it equals [{{$0}}]. The only case where the result would not
        equal [{{pack x}}] is when [y0 <> x] and [~ In x ys]. But this
        contradicts the assumption that [x] is in [(y0::ys)]. Hence, we
        conclude that [[[utila_expr_foldr _ _ (y0 :: ys)]] = {{pack x}}].
      *)
      Lemma utila_expr_find_lm2
        :  forall (k : Kind)
                  (f : k @# type -> Bool @# type)
                  (x : k ## type)
                  (xs : list (k ## type)),
          (unique (fun x => In x xs /\ {{f #[[x]]}} = true) x) ->
          [[utila_expr_foldr (case f) ($0) xs]] =
          {{pack #[[x]]}}.
      Proof
        fun (k : Kind)
            (f : k @# type -> Bool @# type)
            (x : k ## type)
        => list_ind
             (fun xs
              => unique (fun x => In x xs /\ {{f #[[x]]}} = true) x ->
                 [[utila_expr_foldr (case f) ($0) xs]] =
                 {{pack #[[x]]}})
             (* I. contradictory case. *)
             (fun H
              => False_ind _
                           (proj1 (proj1 H)))
             (* II. *)
             (fun x0 xs
                  (F : unique (fun x => In x xs /\ {{f #[[x]]}} = true) x ->
                       [[utila_expr_foldr (case f) ($0) xs]] =
                       {{pack #[[x]]}})
                  (H : unique (fun x => In x (x0 :: xs) /\ {{f #[[x]]}} = true) x)
              => let fx_true
                     :  {{f #[[x]]}} = true
                     := proj2 (proj1 H) in
                 let eq_x
                     :  forall y, (In y (x0 ::xs) /\ {{f #[[y]]}} = true) -> x = y
                     := proj2 H in
                 let eq_pack_x
                     :  In x xs ->
                        [[utila_expr_foldr (case f) ($0) xs]] =
                        {{pack #[[x]]}}
                     := fun in_x_xs
                        => F (conj 
                               (conj in_x_xs fx_true)
                               (fun y (H0 : In y xs /\ {{f #[[y]]}} = true)
                                 => eq_x y
                                      (conj
                                        (or_intror (x0 = y) (proj1 H0))
                                        (proj2 H0)))) in
                 sumbool_ind
                   (fun _
                      => [[utila_expr_foldr (case f) ($0) (x0 :: xs)]] =
                         {{pack #[[x]]}})
                   (* II.A *)
                   (fun eq_x0_x : x0 = x
                     => let fx0_true
                            :  {{f #[[x0]]}} = true
                            := fx_true || {{f #[[a]]}} = true @a by eq_x0_x in
                        let red0
                            :  [[utila_expr_foldr (case f) ($0) (x0 :: xs)]] =
                               {{pack #[[x]]}} ^|
                                               [[utila_expr_foldr (case f) _ xs]]
                            := utila_expr_foldr_correct_cons (case f) ($0) x0 xs
                               || _ = a ^| [[utila_expr_foldr (case f) _ xs]]
                                  @a by <- wor_wzero
                                             (if {{f #[[x0]]}}
                                               then {{pack #[[x0]]}}
                                               else $0)
                               || _ = (if a : bool then _ else _) ^| _
                                  @a by <- fx0_true 
                               || _ = {{pack #[[a]]}} ^| _
                                  @a by <- eq_x0_x in
                        sumbool_ind
                          (fun _
                           => [[utila_expr_foldr (case f) ($0) (x0 :: xs)]] =
                              {{pack #[[x]]}})
                          (* II.A.1 *)
                          (fun in_x_xs : In x xs
                           => red0
                              || _ = _ ^| a
                                 @a by <- eq_pack_x in_x_xs
                              || _ = a
                                 @a by <- wor_idemp {{pack #[[x]]}})
                          (* II.A.2 *)
                          (fun not_in_x_xs : ~ In x xs
                           => let eq_0
                                  :  [[utila_expr_foldr (case f) ($0) xs]] = {{$0}}
                                  := utila_expr_find_lm1
                                       f ($0) xs
                                       (fun y (in_y_xs : In y xs)
                                         => not_true_is_false {{f #[[y]]}}
                                              (fun fy_true : {{f #[[y]]}} = true
                                                => not_in_x_xs
                                                     (in_y_xs
                                                       || In a xs
                                                          @a by eq_x y (conj (or_intror _ in_y_xs) fy_true)))) in
                              red0
                              || _ = _ ^| a
                                 @a by <- eq_0
                              || _ = a
                                 @a by <- wzero_wor {{pack #[[x]]}})
                          (kami_in_dec x xs))
                   (* II.B *)
                   (fun not_eq_x0_x : x0 <> x
                     => let fx0_false
                            :  {{f #[[x0]]}} = false
                            := not_true_is_false {{f #[[x0]]}}
                                 (fun fx0_true : {{f #[[x0]]}} = true
                                   => not_eq_x0_x
                                        (eq_sym (eq_x x0 (conj (or_introl _ eq_refl) fx0_true)))) in
                        (* prove partial reduction - assume that x0 <> x *)
                        sumbool_ind
                          (fun _
                           => [[utila_expr_foldr (case f) ($0) (x0 :: xs)]] =
                              {{pack #[[x]]}})
                          (* II.B.1 *)
                          (fun in_x_xs : In x xs
                           => utila_expr_find_lm0 f ($0) x0 xs fx0_false
                              || _ = a @a by <- eq_pack_x in_x_xs)
                          (* II.B.2 contradictory case - x must be in x0 :: xs. *)
                          (fun not_in_x_xs : ~ In x xs
                           => False_ind _
                                        (or_ind
                                           not_eq_x0_x
                                           not_in_x_xs
                                           (proj1 (proj1 H))))
                          (kami_in_dec x xs))
                   (kami_exprs_eq_dec x0 x)).       

      Theorem utila_expr_find_correct
        : forall (k : Kind)
                 (f : k @# type -> Bool @# type)
                 (xs : list (k ## type))
                 (x : k ## type),
          (unique (fun y => In y xs /\ {{f #[[y]]}} = true) x) ->
          [[utila_expr_find f xs]] = [[x]].
      Proof.
        (intros).
        (unfold utila_expr_find).
        (unfold evalLetExpr at 1).
        (fold evalLetExpr).
        replace
          (fun (x0 : Expr type (SyntaxKind k))
               (acc : Expr type (SyntaxKind (Bit (size k))))
           => (IF f x0 then pack x0 else Const type ($0)%word .| acc))
          with (case f).
        (rewrite (utila_expr_find_lm2 f xs H)).
        (apply unpack_pack).
        (unfold case).
        reflexivity.
      Qed.

    End utila_expr_find.

    Theorem utila_expr_find_pkt_correct
      :  forall (k : Kind)
                (xs : list (Maybe k ## type))
                (x : Maybe k ## type),
        (unique (fun y => In y xs /\ {{#[[y]] @% "valid"}} = true) x) ->
        [[utila_expr_find_pkt xs]] = [[x]].
    Proof
      fun k xs
      => utila_expr_find_correct
           (fun y : Maybe k @# type => y @% "valid") xs.

    Close Scope kami_expr.

  End expr_ver.

  (* Conversions between list and Array *)
  Section ArrayList.
    Variable A: Kind.
    Notation ArrTy ty n := (Array n A @# ty).
    Local Open Scope kami_expr.

    Definition array_to_list' {ty n} (xs: ArrTy ty n) idxs : list (A @# ty) :=
      map (fun i => ReadArrayConst xs i) idxs.

    Definition array_to_list {ty n} (xs: ArrTy ty n) : list (A @#ty) :=
      array_to_list' xs (getFins n).

    Definition list_to_array {ty} (xs: list (A @# ty)) : ArrTy ty (length xs) :=
      BuildArray (fun i => nth_Fin xs i).

    Lemma array_to_list_len {ty} : forall n (xs: ArrTy ty n),
      n = length (array_to_list xs).
    Proof.
      intros; unfold array_to_list, array_to_list'.
      rewrite map_length, getFins_length; auto.
    Qed.

    Lemma array_to_list_id : forall (xs: list (A @# type)),
      map (@evalExpr _) (array_to_list (list_to_array xs)) = map (@evalExpr _) xs.
    Proof.
      unfold array_to_list, array_to_list'; intros.
      rewrite map_map; cbn.
      induction xs; cbn; auto.
      rewrite map_map, <- IHxs; auto.
    Qed.

    Lemma list_to_array_id : forall n (xs: ArrTy type n) (i: Fin.t n),
      let i' := Fin.cast i (array_to_list_len xs) in
      (evalExpr (list_to_array (array_to_list xs))) i' = (evalExpr xs) i.
    Proof.
      intros; cbn; subst i'.
      unfold array_to_list, array_to_list'.
      erewrite nth_Fin_nth.
      rewrite map_nth; cbn.
      rewrite fin_to_nat_cast, getFins_nth; auto.
      Unshelve.
      auto.
    Qed.

    Lemma array_to_list'_forall {ty} : forall n idxs (xs: ArrTy ty n),
      Forall2 (fun i v => v = ReadArrayConst xs i) idxs (array_to_list' xs idxs).
    Proof.
      induction idxs; cbn; intros *; constructor; eauto.
    Qed.

    Lemma array_to_list_forall {ty} : forall n (xs: ArrTy ty n),
      Forall2 (fun i v => v = ReadArrayConst xs i) (getFins n) (array_to_list xs).
    Proof.
      unfold array_to_list; intros; apply array_to_list'_forall.
    Qed.

    Lemma array_to_list_nth {ty} : forall n (xs: ArrTy ty n) (i: Fin.t n) i',
      i' = proj1_sig (Fin.to_nat i) ->
      nth_error (array_to_list xs) i' = Some (ReadArrayConst xs i).
    Proof.
      intros.
      assert (Hi': (i' < n)%nat).
      { destruct (Fin.to_nat i); subst; cbn; auto. }
      rewrite <- getFins_length in Hi'.
      pose proof (array_to_list_forall xs) as Hall.
      assert (Hlen: length (array_to_list xs) = n).
      { apply Forall2_length in Hall.
        rewrite getFins_length in Hall; auto.
      }
      assert (exists x, nth_error (array_to_list xs) i' = Some x) as (? & Hnth).
      { eapply nth_error_not_None.
        rewrite nth_error_Some.
        rewrite Hlen, <- getFins_length; auto.
      }
      pose proof (getFins_nth_error i) as Hnth'; cbn in Hnth'; subst.
      eapply Forall2_nth_error in Hall; eauto; subst; auto.
    Qed.

    Corollary in_array_to_list {ty} : forall n (arr : ArrTy ty n) i,
      In (ReadArrayConst arr i) (array_to_list arr).
    Proof.
      intros; eauto using nth_error_In, array_to_list_nth.
    Qed.

    Definition array_forall {ty n} (f: A @# ty -> Bool @# ty) (xs: ArrTy ty n) : Bool @# ty :=
      utila_all (map f (array_to_list xs)).

    Lemma array_forall_correct : forall f n (xs: ArrTy _ n),
      evalExpr (array_forall f xs) = true <->
      Forall (fun v => evalExpr (f v) = true) (array_to_list xs).
    Proof.
      unfold array_forall; intros.
      set (ys := array_to_list xs) in *; clearbody ys.
      rewrite utila_all_correct; split; intros Hall.
      - induction ys; constructor; inv Hall; auto.
      - induction ys; constructor; inv Hall; auto.
    Qed.

    Definition fin_to_bit {ty n} (i: Fin.t n) : Bit (Nat.log2_up n) @# ty :=
      Const _ (natToWord _ (proj1_sig (Fin.to_nat i))).

    Definition array_forall_except {ty n}
        (f: A @# ty -> Bool @# ty)
        (xs: ArrTy ty n)
        (j: Bit (Nat.log2_up n) @# ty)
        : Bool @# ty :=
      utila_all (map (fun vi => let '(v, i) := vi in (j == fin_to_bit i) || f v)
                     (List.combine (array_to_list xs) (getFins n)))%kami_expr.

    Lemma array_forall_except_correct : forall f n (xs: ArrTy _ n) j,
      evalExpr (array_forall_except f xs j) = true <->
      Forall2 (fun v i =>
          evalExpr (j == fin_to_bit i) = false -> evalExpr (f v) = true)
        (array_to_list xs) (getFins n).
    Proof.
      unfold array_forall_except; intros.
      assert (Hlen: length (getFins n) = length (array_to_list xs))
        by (eauto using Forall2_length, array_to_list_forall).
      rewrite getFins_length in Hlen.
      set (ys := array_to_list xs) in *; clearbody ys.
      rewrite utila_all_correct; split; intros Hall; subst.
      - rewrite Forall_map in Hall.
        rewrite <- Forall_combine by (rewrite getFins_length; auto).
        set (zs := List.combine _ _) in *; clearbody zs.
        induction zs as [| (? & ?) zs]; constructor; inv Hall; auto; cbn in *.
        rewrite orb_true_iff in *; intuition congruence.
      - rewrite Forall_map.
        rewrite <- Forall_combine in Hall by (rewrite getFins_length; auto).
        set (zs := List.combine _ _) in *; clearbody zs.
        induction zs as [| (? & ?) zs]; constructor; inv Hall; auto; cbn in *.
        rewrite orb_true_iff in *.
        destruct (getBool _); intuition.
    Qed.

  End ArrayList.

End utila.
