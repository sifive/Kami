Require Import String Fin Kami.All.

Class StringMap (M : Type -> Type) := {
  empty : forall {V}, M V;
  map_lookup : forall {V}, string -> M V -> option V;
  insert : forall {V}, string -> V -> M V -> M V
  }.

Class IsVector (V : nat -> Type -> Type) := {
  index : forall {X n}, Fin.t n -> V n X -> X;
  vec_map : forall {X Y n}, (X -> Y) -> V n X -> V n Y;
  vec_eq : forall {X n}, (X -> X -> bool) -> V n X -> V n X -> bool;
  vec_to_list : forall {X n}, V n X -> list X;
  make_vec : forall {X n}, (Fin.t n -> X) -> V n X;
  slice : forall {X n} (i m : nat), V n X -> (V m X);
  updates : forall {X n}, V n X -> list (nat * X) -> V n X
  }.

Class IsWord (W : nat -> Type) := {
  inv : forall {m}, W m -> W m;
  trunc_lsb : forall {m n}, W (m + n) -> W m;
  trunc_msb : forall {m n}, W (m + n) -> W n;
  uand : forall {m}, W m -> W 1;
  uor : forall {m}, W m -> W 1;
  uxor : forall {m}, W m -> W 1;

  sub : forall {m}, W m -> W m -> W m;
  div : forall {m}, W m -> W m -> W m;
  rem : forall {m}, W m -> W m -> W m;
  sll : forall {m n}, W m -> W n -> W m;
  srl : forall {m n}, W m -> W n -> W m;
  sra : forall {m n}, W m -> W n -> W m;
  concat : forall {m n}, W m -> W n -> W (n + m);

  add : forall {m}, list (W m) -> W m;
  mul : forall {m}, list (W m) -> W m;
  band : forall {m}, list (W m) -> W m;
  bor : forall {m}, list (W m) -> W m;
  bxor : forall {m}, list (W m) -> W m;

  wltb : forall {m}, W m -> W m -> bool;

  weqb : forall {m}, W m -> W m -> bool;

  word_to_nat : forall {m}, W m -> nat;
  nat_to_word : forall {m}, nat -> W m;
  
  print_word_bin : forall {m}, W m -> string;
  print_word_dec : forall {m}, W m -> string;
  print_word_hex : forall {m}, W m -> string
  }.

Class IOMonad{W V}`{IsWord W, IsVector V} (M : Type -> Type) := {
  ret : forall {X}, X -> M X;
  bind : forall {X Y}, M X -> (X -> M Y) -> M Y;
  error : forall {X}, string -> M X;
  print : string -> M unit;
  rand_bool : M bool;
  rand_word : forall n, M (W n);
  rand_vec : forall {X n}, M X -> M (V n X);
  exit : forall {X}, M X;
  }.

Notation "'io_do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).