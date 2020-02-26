Require Import Kami.Simulator.CoqSim.SimTypes.
Require Extraction.
Require Import String.

Extraction Language Haskell.

(* We postulate Haskell's more efficient datatypes and package them for extraction *)

(* Maps *)

Parameter HMap : Type -> Type.

Parameter Hempty : forall {V}, HMap V.
Parameter Hmap_lookup : forall {V}, string -> HMap V -> option V.
Parameter Hinsert : forall {V}, string -> V -> HMap V -> HMap V.

Instance HMapIsMap : StringMap HMap := {|
  empty := @Hempty;
  map_lookup := @Hmap_lookup;
  insert := @Hinsert
  |}.

Extract Constant HMap "v" => "Data.Map.Map Prelude.String v".
Extract Constant Hempty => "Data.Map.empty".
Extract Constant Hmap_lookup => "Data.Map.lookup".
Extract Constant Hinsert => "Data.Map.insert".

(* Vectors *)

Parameter HVec : nat -> Type -> Type.

Parameter Hindex : forall {X n}, Fin.t n -> HVec n X -> X.
Parameter Hmap : forall {X Y n}, (X -> Y) -> HVec n X -> HVec n Y.
Parameter Heq : forall {X n}, (X -> X -> bool) -> HVec n X -> HVec n X -> bool.
Parameter Hto_list : forall {X n}, HVec n X -> list X.
Parameter Hmake_vec : forall {X n}, (Fin.t n -> X) -> HVec n X.
Parameter Hslice : forall {X n} (i m : nat),  HVec n X -> HVec m X.
Parameter Hupdates : forall {X n}, HVec n X -> list (nat * X) -> HVec n X.

Instance HVecIsVec : IsVector HVec := {|
  SimTypes.index := @Hindex;
  vec_map := @Hmap;
  vec_eq := @Heq;
  vec_to_list := @Hto_list;
  make_vec := @Hmake_vec;
  slice := @Hslice;
  updates := @Hupdates
  |}.

Fixpoint Fin_to_list{X n} : (Fin.t n -> X) -> list X :=
  match n with
  | 0 => fun _ => nil
  | S m => fun f => cons (f Fin.F1) (Fin_to_list (fun i => f (Fin.FS i)))
  end.

Extract Constant HVec "a" => "Data.Vector.Vector a".
Extract Constant Hindex => "(\_ (n,i) v -> v Data.Vector.! i)".
Extract Constant Hmap => "(\_ -> Data.Vector.map)".
Extract Constant Heq => "(\_ eqb v1 v2 -> Data.Vector.foldr (Prelude.&&) Prelude.True (Data.Vector.zipWith eqb v1 v2))".
Extract Constant Hto_list => "(\ _ -> Data.Vector.toList)".
Extract Constant Hmake_vec => "(\n f -> Data.Vector.fromList (coq_Fin_to_list n f))".
Extract Constant Hslice => "(\_ i m v -> Data.Vector.slice i m v)".
Extract Constant Hupdates => "(\_ -> (Data.Vector.//))".

(* Words *)

Parameter HWord : nat -> Type.
Parameter Hinv : forall {m}, HWord m -> HWord m.
Parameter Htrunc_lsb : forall {m n}, HWord (m + n) -> HWord m.
Parameter Htrunc_msb : forall {m n}, HWord (m + n) -> HWord n.
Parameter Huand : forall {m}, HWord m -> HWord 1.
Parameter Huor : forall {m}, HWord m -> HWord 1.
Parameter Huxor : forall {m}, HWord m -> HWord 1.
Parameter Hsub : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hdiv : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hrem : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hsll : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hsrl : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hsra : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hconcat : forall {m n}, HWord m -> HWord n -> HWord (n + m).
Parameter Hadd : forall {m}, list (HWord m) -> HWord m.
Parameter Hmul : forall {m}, list (HWord m) -> HWord m.
Parameter Hband : forall {m}, list (HWord m) -> HWord m.
Parameter Hbor : forall {m}, list (HWord m) -> HWord m.
Parameter Hbxor : forall {m}, list (HWord m) -> HWord m.
Parameter Hwltb : forall {m}, HWord m -> HWord m -> bool.
Parameter Hweqb : forall {m}, HWord m -> HWord m -> bool.
Parameter Hword_to_nat : forall {m}, HWord m -> nat.
Parameter Hnat_to_word : forall {m}, nat -> HWord m.
Parameter Hprint_word_bin : forall {m}, HWord m -> string.
Parameter Hprint_word_dec : forall {m}, HWord m -> string.
Parameter Hprint_word_hex : forall {m}, HWord m -> string.

Instance HWordIsWord : IsWord HWord := {|
  inv := @Hinv;
  trunc_lsb := @Htrunc_lsb;
  trunc_msb := @Htrunc_msb;
  uand := @Huand;
  uor := @Huor;
  uxor := @Huxor;
  sub := @Hsub;
  div := @Hdiv;
  rem := @Hrem;
  sll := @Hsll;
  srl := @Hsrl;
  sra := @Hsra;
  SimTypes.concat := @Hconcat;
  add := @Hadd;
  mul := @Hmul;
  band := @Hband;
  bor := @Hbor;
  bxor := @Hbxor;
  wltb := @Hwltb;
  weqb := @Hweqb;
  word_to_nat := @Hword_to_nat;
  nat_to_word := @Hnat_to_word;
  print_word_bin := @Hprint_word_bin;
  print_word_dec := @Hprint_word_dec;
  print_word_hex := @Hprint_word_hex
  |}.

Extract Constant HWord => "Data.BitVector.BV".
Extract Constant Hinv => "(\_ -> Data.BitVector.not)".
Extract Constant Htrunc_lsb => "(\m _ -> if m Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.least m)".
Extract Constant Htrunc_msb => "(\_ n -> if n Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.most n)".
Extract Constant Huand => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.&&) Prelude.True v))".
Extract Constant Huor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.||) Prelude.False v))".
Extract Constant Huxor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude./=) Prelude.False v))".
Extract Constant Hsub => "(\_ -> (Prelude.-))".
Extract Constant Hdiv => "(\_ -> Prelude.div)".
Extract Constant Hrem => "(\_ -> Prelude.rem)".
Extract Constant Hsll => "(\_ _ -> Data.BitVector.shl)".
Extract Constant Hsrl => "(\_ _ -> Data.BitVector.shr)".
Extract Constant Hsra => "(\_ _ -> Data.BitVector.ashr)".
Extract Constant Hconcat => "(\_ _ -> (Data.BitVector.#))".
Extract Constant Hadd => "(\_ -> Prelude.foldr (Prelude.+) 0)".
Extract Constant Hmul => "(\_ -> Prelude.foldr (Prelude.*) 1)".
Extract Constant Hband => "(\n -> Prelude.foldr (Data.Bits..&.) (Data.BitVector.ones n))".
Extract Constant Hbor => "(\n -> Prelude.foldr (Data.Bits..|.) (Data.BitVector.zeros n))".
Extract Constant Hbxor => "(\n -> Prelude.foldr Data.Bits.xor (Data.BitVector.zeros n))".
Extract Constant Hwltb => "(\_ -> (Data.BitVector.<.))".
Extract Constant Hweqb => "(\_ -> (Data.BitVector.==.))".
Extract Constant Hword_to_nat => "(\_ x -> Prelude.fromIntegral (Data.BitVector.nat x))".
Extract Inlined Constant Hnat_to_word => "Data.BitVector.bitVec".
Extract Constant Hprint_word_bin => "(\_ -> CustomExtract.bv_bin)".
Extract Constant Hprint_word_dec => "(\_ -> CustomExtract.bv_dec)".
Extract Constant Hprint_word_hex => "(\_ -> CustomExtract.bv_hex)".

(* IO *)

Require Import String.

Parameter IO : Type -> Type.
Parameter Hret : forall {X}, X -> IO X.
Parameter Hbind : forall {X Y}, IO X -> (X -> IO Y) -> IO Y.
Parameter Herror : forall {X}, string -> IO X.
Parameter Hprint : string -> IO unit.
Parameter Hrand_bool : IO bool.
Parameter Hrand_word : forall n, IO (HWord n).
Parameter Hrand_vec : forall {X n}, IO X -> IO (HVec n X).
Parameter Hexit : forall {X}, IO X.

Instance IOPrintMonad : IOMonad IO := {|
  ret := @Hret;
  bind := @Hbind;
  error := @Herror;
  print := Hprint;
  rand_bool := Hrand_bool;
  rand_word := Hrand_word;
  rand_vec := @Hrand_vec;
  exit := @Hexit
  |}.

Extract Constant IO "a" => "Prelude.IO a".
Extract Constant Hret => "Prelude.return".
Extract Constant Hbind => "(GHC.Base.>>=)".
Extract Constant Herror => "Prelude.error".
(*Extract Constant Hprint => "(\str -> (GHC.Base.>>) (Prelude.putStrLn str) (System.IO.hFlush System.IO.stdout))". *)
Extract Constant Hprint => "Prelude.putStr".
Extract Constant Hrand_bool => "Prelude.return Prelude.False". (*FIXME*)
Extract Constant Hrand_word => "Prelude.undefined". (*FIXME*)
Extract Constant Hrand_vec => "Prelude.undefined". (*FIXME*)
Extract Constant Hexit => "System.Exit.exitSuccess".

(* Arrays *)

Parameter HArray : Type -> Type.
Parameter Hmake_arr : forall {X n}, (Fin.t n -> X) -> IO (HArray X).
Parameter Harr_slice : forall {X} (i m : nat), HArray X -> IO (HVec m X).
Parameter Harr_updates : forall {X}, HArray X -> list (nat * X) -> IO unit.
Parameter Harr_map : forall {X Y}, (X -> Y) -> HArray X -> IO (HArray Y).

Instance HArrayIsArray : IsArray HArray := {|
  make_arr := @Hmake_arr;
  arr_slice := @Harr_slice;
  arr_updates := @Harr_updates;
  arr_map := @Harr_map
  |}.

Extract Constant HArray "a" => "Data.Array.IO.IOArray Prelude.Int a".
Extract Constant Hmake_arr => "(\n f -> Data.Array.MArray.newListArray (0,n Prelude.- 1) (coq_Fin_to_list n f))".
Extract Constant Harr_slice => "(\i m a -> Control.Monad.liftM Data.Vector.fromList (Prelude.sequence (Prelude.map (\j -> Data.Array.MArray.readArray a (j Prelude.+ i)) [0..(m Prelude.- 1)])))".
Extract Constant Harr_updates => "(\a ps -> Prelude.return ())".
Extract Constant Harr_updates => "(\a ps -> Control.Monad.foldM (\_ (i,e) -> Data.Array.MArray.writeArray a i e) () ps)".
Extract Constant Harr_map => "Data.Array.MArray.mapArray".
