Require Extraction.
Require Import String.
Require Import Kami.StdLib.Fin.
Require Import Kami.All.
Require Import Kami.Simulator.CoqSim.Misc.

Extraction Language Haskell.

(* We postulate Haskell's more efficient datatypes and extract them *)

(* Maps with string keys *)

Parameter Map : Type -> Type.

Parameter empty : forall {V}, Map V.
Parameter map_lookup : forall {V}, string -> Map V -> option V.
Parameter insert : forall {V}, string -> V -> Map V -> Map V.
Parameter map_of_list : forall {V}, list (string * V) -> Map V.

Axiom empty_lookup : forall V x, map_lookup x (empty : Map V) = None.
Axiom map_of_list_lookup : forall V x (ps : list (string * V)),
  map_lookup x (map_of_list ps) = lookup String.eqb x ps.
Axiom insert_lookup_hit : forall V x (v : V) m, map_lookup x (insert x v m) = Some v.
Axiom insert_lookup_miss : forall V x x' (v : V) m, x <> x' -> map_lookup x' (insert x v m) = map_lookup x' m.

Extract Constant Map "v" => "Data.Map.Strict.Map Prelude.String v".
Extract Constant empty => "Data.Map.Strict.empty".
Extract Constant map_lookup => "Data.Map.Strict.lookup".
Extract Constant insert => "Data.Map.Strict.insert".
Extract Constant map_of_list => "Data.Map.Strict.fromList".

(* Vectors *)

Parameter Vector : nat -> Type -> Type.

Parameter vector_index : forall {X n}, Fin n -> Vector n X -> X.
Parameter vector_map : forall {X Y n}, (X -> Y) -> Vector n X -> Vector n Y.
Parameter vector_eq : forall {X n}, (X -> X -> bool) -> Vector n X -> Vector n X -> bool.
Parameter vector_to_list : forall {X n}, Vector n X -> list X.
Parameter make_vector : forall {X n}, (Fin n -> X) -> Vector n X.
Parameter vector_slice : forall {X n} (i m : nat),  Vector n X -> Vector m X.
Parameter vector_updates : forall {X n}, Vector n X -> list (nat * X) -> Vector n X.

Fixpoint Fin_to_list{X n} : (Fin.t n -> X) -> list X :=
  match n with
  | 0 => fun _ => nil
  | S m => fun f => cons (f Fin.F1) (Fin_to_list (fun i => f (Fin.FS i)))
  end.

Extract Constant Vector "a" => "Data.Vector.Vector a".
Extract Constant vector_index => "(\_ (n,i) v -> v Data.Vector.! i)".
Extract Constant vector_map => "(\_ -> Data.Vector.map)".
Extract Constant vector_eq => "(\_ eqb v1 v2 -> Data.Vector.foldr (Prelude.&&) Prelude.True (Data.Vector.zipWith eqb v1 v2))".
Extract Constant vector_to_list => "(\ _ -> Data.Vector.toList)".
Extract Constant make_vector => "(\n f -> Data.Vector.fromList (coq_Fin_to_list n f))".
Extract Constant vector_slice => "(\_ i m v -> Data.Vector.slice i m v)".
Extract Constant vector_updates => "(\_ -> (Data.Vector.//))".

(* BVs *)

Parameter BV : nat -> Type.
Parameter bv_inv : forall {m}, BV m -> BV m.
Parameter bv_trunc_lsb : forall {m n}, BV (m + n) -> BV m.
Parameter bv_trunc_msb : forall {m n}, BV (m + n) -> BV n.
Parameter bv_uand : forall {m}, BV m -> BV 1.
Parameter bv_uor : forall {m}, BV m -> BV 1.
Parameter bv_uxor : forall {m}, BV m -> BV 1.
Parameter bv_sub : forall {m}, BV m -> BV m -> BV m.
Parameter bv_div : forall {m}, BV m -> BV m -> BV m.
Parameter bv_rem : forall {m}, BV m -> BV m -> BV m.
Parameter bv_sll : forall {m n}, BV m -> BV n -> BV m.
Parameter bv_srl : forall {m n}, BV m -> BV n -> BV m.
Parameter bv_sra : forall {m n}, BV m -> BV n -> BV m.
Parameter bv_concat : forall {m n}, BV m -> BV n -> BV (n + m).
Parameter bv_add : forall {m}, list (BV m) -> BV m.
Parameter bv_mul : forall {m}, list (BV m) -> BV m.
Parameter bv_band : forall {m}, list (BV m) -> BV m.
Parameter bv_bor : forall {m}, list (BV m) -> BV m.
Parameter bv_bxor : forall {m}, list (BV m) -> BV m.
Parameter bv_lt : forall {m}, BV m -> BV m -> bool.
Parameter bv_eq : forall {m}, BV m -> BV m -> bool.
Parameter bv_to_nat : forall {m}, BV m -> nat.
Parameter nat_to_bv : forall {m}, nat -> BV m.
Parameter print_bv_bin : forall {m}, BV m -> string.
Parameter print_bv_dec : forall {m}, BV m -> string.
Parameter print_bv_hex : forall {m}, BV m -> string.

Extract Constant BV => "Data.BitVector.BV".
Extract Constant bv_inv => "(\_ -> Data.BitVector.not)".
Extract Constant bv_trunc_lsb => "(\m _ -> if m Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.least m)".
Extract Constant bv_trunc_msb => "(\_ n -> if n Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.most n)".
Extract Constant bv_uand => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.&&) Prelude.True v))".
Extract Constant bv_uor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.||) Prelude.False v))".
Extract Constant bv_uxor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude./=) Prelude.False v))".
Extract Constant bv_sub => "(\_ -> (Prelude.-))".
Extract Constant bv_div => "(\_ -> Prelude.div)".
Extract Constant bv_rem => "(\_ -> Prelude.rem)".
Extract Constant bv_sll => "(\_ _ -> Data.BitVector.shl)".
Extract Constant bv_srl => "(\_ _ -> Data.BitVector.shr)".
Extract Constant bv_sra => "(\_ _ -> Data.BitVector.ashr)".
Extract Constant bv_concat => "(\_ _ -> (Data.BitVector.#))".
Extract Constant bv_add => "(\_ -> Prelude.foldr (Prelude.+) 0)".
Extract Constant bv_mul => "(\_ -> Prelude.foldr (Prelude.* ) 1)".
Extract Constant bv_band => "(\n -> Prelude.foldr (Data.Bits..&.) (Data.BitVector.ones n))".
Extract Constant bv_bor => "(\n -> Prelude.foldr (Data.Bits..|.) (Data.BitVector.zeros n))".
Extract Constant bv_bxor => "(\n -> Prelude.foldr Data.Bits.xor (Data.BitVector.zeros n))".
Extract Constant bv_lt => "(\_ -> (Data.BitVector.<.))".
Extract Constant bv_eq => "(\_ -> (Data.BitVector.==.))".
Extract Constant bv_to_nat => "(\_ x -> Prelude.fromIntegral (Data.BitVector.nat x))".
Extract Inlined Constant nat_to_bv => "Data.BitVector.bitVec".
Extract Constant print_bv_bin => "(\_ -> CustomExtract.bv_bin)".
Extract Constant print_bv_dec => "(\_ -> CustomExtract.bv_dec)".
Extract Constant print_bv_hex => "(\_ -> CustomExtract.bv_hex)".

(* IO *)

Require Import String.

Parameter IO : Type -> Type.
Parameter ret : forall {X}, X -> IO X.
Parameter bind : forall {X Y}, IO X -> (X -> IO Y) -> IO Y.
Parameter error : forall {X}, string -> IO X.
Parameter print : string -> IO unit.
Parameter rand_bool : IO bool.
Parameter rand_bv : forall n, IO (BV n).
Parameter rand_vector : forall {X n}, IO X -> IO (Vector n X).
Parameter exit : forall {X}, IO X.

Extract Constant IO "a" => "Prelude.IO a".
Extract Inlined Constant ret => "Prelude.return".
Extract Inlined Constant bind => "(GHC.Base.>>=)".
Extract Inlined Constant error => "Prelude.error".
(*Extract Constant Hprint => "(\str -> (GHC.Base.>>) (Prelude.putStrLn str) (System.IO.hFlush System.IO.stdout))". *)
Extract Inlined Constant print => "Prelude.putStr".
Extract Constant rand_bool => "Prelude.return Prelude.False". (*FIXME*)
Extract Constant rand_bv => "Prelude.undefined". (*FIXME*)
Extract Constant rand_vector => "Prelude.undefined". (*FIXME*)
Extract Constant exit => "System.Exit.exitSuccess".

Module Notations.

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

End Notations.

(* Arrays *)

Parameter Arr : Type -> Type.
Parameter arr_repl : forall {X}, nat -> X -> IO (Arr X).
Parameter arr_slice : forall {X} (i m : nat), Arr X -> IO (Vector m X).
Parameter arr_updates : forall {X}, Arr X -> list (nat * X) -> IO unit.
(* Parameter arr_new : forall {X}, nat -> IO (Array X).
 *)
(** does not work at the moment **)
(*Extract Constant HArray "a" => "Data.Array.IO.IOArray Prelude.Int a".
Extract Constant Harr_repl => "(\n x -> Data.Array.MArray.newArray (0, n Prelude.- 1) x)".
Extract Constant Harr_slice => "(\i m a -> Control.Monad.liftM Data.Vector.fromList (Prelude.sequence (Prelude.map (\j -> Data.Array.MArray.readArray a (j Prelude.+ i)) [0..(m Prelude.- 1)])))".
Extract Constant Harr_updates => "(\a ps -> Control.Monad.foldM (\_ (i,e) -> Data.Array.MArray.writeArray a i e) () ps)".*)


Extract Constant Arr "a" => "Data.Vector.Mutable.MVector (Control.Monad.Primitive.PrimState Prelude.IO) a".
Extract Constant arr_repl => "Data.Vector.Mutable.replicate".
Extract Constant arr_slice => "(\i m a -> Data.Vector.Generic.freeze (Data.Vector.Mutable.slice i m a))".
Extract Constant arr_updates => "(\a ps -> Control.Monad.foldM (\_ (i,x) -> Data.Vector.Mutable.write a i x) () ps)".
