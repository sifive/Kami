Require Import String.
Require Import FinFun.

Require Import Kami.AllNotations.
Require Import Kami.Syntax.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.Simulator.CoqSim.SimTypes.

Section RegFile.

Context {V : nat -> Type -> Type}.
Context `{IsVector V}.

Context {W : nat -> Type}.
Context `{IsWord W}.

Context {M : Type -> Type}.
Context `{StringMap M}.

Context {IO : Type -> Type}.
Context `{IOMonad W V IO}.

Definition Val k := eval_Kind W V k.
Definition ValFK k := eval_FK W V k.

Inductive FileCall :=
  | AsyncRead : FileCall
  | ReadReq : string -> FileCall
  | ReadResp : string -> FileCall
  | WriteFC : FileCall.

Inductive FileUpd :=
  | IntRegWrite : string -> {k : Kind & Val k} -> FileUpd
  | ArrWrite : string -> forall k, list (nat * Val k) -> FileUpd.

Record RegFile := {
  file_name : string;
  is_wr_mask : bool;
  chunk_size : nat;
  readers : RegFileReaders;
  write : string;
  size : nat;
  kind : Kind;
  arr : V size (Val kind)
  }.

Record FileState := {
  methods : M (FileCall * string);
  int_regs : M {k : Kind & Val k};
  files : M RegFile;
  }.

Definition empty_state : FileState := {|
  methods := empty;
  int_regs := empty;
  files := empty
  |}.

Definition file_async_read(file : RegFile)(i : nat) : Val (Array (chunk_size file) (kind file)) :=
  slice i _ (arr file).

Definition isAddr(file : RegFile) : bool :=
  match readers file with
  | Sync isAddr _ => isAddr
  | _ => false
  end.

Definition file_sync_readreq(val : {k : Kind & Val k})(file : RegFile)(regName : string) : option {k : Kind & Val k}. refine
  match readers file with
  | Async _ => None
  | Sync true _ => if Kind_decb (projT1 val) (Bit (Nat.log2_up (size file))) then Some val else None
  | Sync false _ => _
  end.
Proof.
  (* isAddr = false *)
  destruct val as [k v].
  destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
  - rewrite Kind_decb_eq in Keq.
    rewrite Keq in v.
    apply Some.
    exists (Array (chunk_size file) (kind file)).
    exact (slice (word_to_nat v) (chunk_size file) (arr file)).
  - exact None.
Defined.

Definition file_sync_readresp(state : FileState)(file : RegFile)(regName : string) : option (Val (Array (chunk_size file) (kind file))). refine
  match map_lookup (M := M) regName (int_regs state) with
  | None => None
  | Some (existT k v) =>
      match readers file with
      | Async _ => None
      | Sync true _ => _
      | Sync false _ => _
      end
  end.
Proof.
  (* isAddr = true *)
  - destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact (Some (slice (word_to_nat v) (chunk_size file) (arr file))).
    * exact None.
  (* isAddr = false *)
  - destruct (Kind_decb k (Array (chunk_size file) (kind file))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact (Some v).
    * exact None.
Defined.

Definition file_writes_mask(file : RegFile)(i : nat)(mask : Val (Array (chunk_size file) Bool))(vals : Val (Array (chunk_size file) (kind file))) : list (nat * Val (kind file)) :=
  let mask_indices := filter (fun i => index i mask) (getFins _) in
    map (fun j => (i + Fin2Restrict.f2n j, index j vals)) mask_indices.

Definition file_writes_no_mask(file : RegFile)(i : nat)(vals : Val (Array (chunk_size file) (kind file))) : list (nat * Val (kind file)) :=
  map (fun j => (i + Fin2Restrict.f2n j, index j vals)) (getFins _).

Definition void_nil : {k : Kind & Val k} :=
  existT _ (Bit 0) (nat_to_word 0).

Definition coerce(v : {k : Kind & Val k})(k : Kind) : option (Val k).
  refine
    match v with
    | existT k' v' => _
    end.
Proof.
  destruct (Kind_dec k k').
  * rewrite e. exact (Some v').
  * exact None.
Defined.

Fixpoint Tup_lookup{n} : forall (i : Fin.t n)(ks : Fin.t n -> Kind), Tuple (fun i => Val (ks i)) -> {k : Kind & Val k} :=
  match n return forall (i : Fin.t n)(ks : Fin.t n -> Kind), Tuple (fun i => Val (ks i)) -> {k : Kind & Val k} with
  | 0 => fun i => case0 _ i
  | S m => fun i ks X => fin_case i _ (existT _ (ks F1) (fst X)) (fun j => (Tup_lookup  j _ (snd X)))
  end.

Definition  rf_methcall(state : FileState)(methName : string)(val : {k : Kind & Val k}) : option (option FileUpd * {k : Kind & Val k}). refine
  match map_lookup methName (methods state) with
  | None => None
  | Some (fc, fileName) => match map_lookup fileName (files state) with
                           | None => None
                           | Some file => match fc with
                                          | AsyncRead => _
                                          | ReadReq regName => match file_sync_readreq val file regName with
                                                               | None => None
                                                               | Some p => Some (Some (IntRegWrite regName p), void_nil)
                                                               end
                                          | ReadResp regName => match file_sync_readresp state file regName with
                                                                | None => None
                                                                | Some v => Some (None, existT _ _ v)
                                                                end
                                          | WriteFC => match is_wr_mask file with
                                                       | true => _
                                                       | false => _
                                                       end
                                          end
                           end
  end.
Proof.
  (* AsyncRead *)
  - destruct val as [k v].
    destruct k eqn:G.
    + exact None.
    + pose (i := word_to_nat v).
      exact (Some (None, existT _ _ (file_async_read file i))).
    + exact None.
    + exact None.
  (* WriteFC is_wr_mask = true *)
  - destruct val as [k v].
    destruct k eqn:G.
    + exact None.
    + exact None.
    + destruct n as [|[|[|]]]; [exact None | exact None | exact None | idtac]. (* n should be 3 *)
      exact (let addr := Tup_lookup F1 k0 v in
             let data_k := Tup_lookup (FS F1) k0 v in
             let mask := Tup_lookup (FS (FS F1)) k0 v in
             o_do addr' <- coerce addr (Bit (Nat.log2_up (size file)));
             o_do data' <- coerce data_k (Array (chunk_size file) (kind file));
             o_do mask' <- coerce mask (Array (chunk_size file) Bool);
             o_ret (Some (ArrWrite fileName _ (file_writes_mask file (word_to_nat addr') mask' data')), void_nil)).
    + exact None.
  (* WriteFC is_wr_mask = false *)
  - destruct val as [k v].
    destruct k eqn:G.
    + exact None.
    + exact None.
    + destruct n as [|[|]]; [exact None | exact None | idtac]. (* n should be 2 *)
      exact (let addr := Tup_lookup F1 k0 v in
             let data_k := Tup_lookup (FS F1) k0 v in
             o_do addr' <- coerce addr (Bit (Nat.log2_up (size file)));
             o_do data' <- coerce data_k (Array (chunk_size file) (kind file));
             o_ret (Some (ArrWrite fileName _ (file_writes_no_mask file (word_to_nat addr') data')), void_nil)).
    + exact None.
Defined.

Definition exec_file_update(u : FileUpd)(state : FileState) : FileState. refine
  match u with
  | IntRegWrite regName v =>
    {| methods := methods state;
       int_regs := insert regName v (int_regs state);
       files := files state
    |}
  | ArrWrite fileName k upds => 
    {| methods := methods state;
       int_regs := int_regs state;
       files := match map_lookup fileName (files state) with
                | None => files state
                | Some file => match Kind_dec k (kind file) with
                               | left pf => insert fileName 
                                    {|
                                      file_name := file_name file;
                                      is_wr_mask := is_wr_mask file;
                                      chunk_size := chunk_size file;
                                      readers := readers file;
                                      write := write file;
                                      size := size file;
                                      kind := kind file;
                                      arr := updates (arr file) _
                                    |} (files state)
                               | right _ => files state
                               end
                end
    |}
  end.
Proof.
  rewrite pf in upds.
  exact upds.
Defined.

Definition exec_file_updates := List.fold_right exec_file_update.

Axiom parseFile : forall (size idxNum : nat)(filepath : string), IO (V idxNum (W size)).

Definition initialize_file(args : list (string * string))(rfb : RegFileBase)(state : FileState) : IO FileState :=

  let array := match rfInit rfb with
               | RFNonFile None => ret (make_vec (fun (_ : Fin.t (rfIdxNum rfb)) => default_val (rfData rfb)))
               | RFNonFile (Some c) => ret (make_vec (fun _ => eval_ConstT c))
               | RFFile isAscii isArg file _ _ _ =>
                  let filepath := if isArg then match lookup String.eqb file args with
                                               | Some fp => ret fp
                                               | None => error ("File " ++ file ++ " not found!")
                                               end else ret file in
                  (io_do path <- filepath;
                   io_do words <- parseFile (Syntax.size (rfData rfb)) (rfIdxNum rfb) path;
                   ret (vec_map (@val_unpack W V _ _ _) words))
               end in
 (
  io_do new_arr <- array;

  let rf := {|
                file_name := rfDataArray rfb;
                is_wr_mask := rfIsWrMask rfb;
                chunk_size := rfNum rfb;
                readers := rfRead rfb;
                write := rfWrite rfb;
                size := rfIdxNum rfb;
                kind := rfData rfb;
                arr := new_arr
            |} in

  let reads := match rfRead rfb with
               | Async rs => map (fun r => (r, (AsyncRead, rfDataArray rfb))) rs
               | Sync b rs => map (fun r => (readReqName r, (ReadReq (readRegName r), rfDataArray rfb))) rs ++
                              map (fun r => (readResName r, (ReadResp (readRegName r), rfDataArray rfb))) rs
               end in

  let newmeths := (rfWrite rfb, (WriteFC, rfDataArray rfb)) :: reads in
  
  let newvals := match rfRead rfb with
                 | Async _ => []
                 | Sync b rs => let k := if b then Bit (Nat.log2_up (rfIdxNum rfb)) else rfData rfb in
                     map (fun r => (readRegName r, existT _ k (default_val k))) rs
                 end in 

  ret {|
    methods := fold_right (fun '(x,y) st => insert x y st) (methods state) newmeths;
    int_regs := fold_right (fun '(x,y) st => insert x y st) (int_regs state) newvals;
    files := insert (rfDataArray rfb) rf (files state)
    |}
  ).

Fixpoint initialize_files(args : list (string * string))(rfbs : list RegFileBase) : IO FileState :=
  match rfbs with
  | [] => ret empty_state
  | (file::files) => (
      io_do st <- initialize_files args files;
      initialize_file args file st)
  end.

End RegFile.

Extract Constant parseFile => "ParseExtract.parseFile".
