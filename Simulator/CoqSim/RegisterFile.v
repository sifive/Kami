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

Context {Arr : Type -> Type}.
Context `{IsArray W V IO Arr}.

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
  arr : Arr (Val kind)
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

Definition file_async_read(file : RegFile)(i : nat) : IO (Val (Array (chunk_size file) (kind file))) :=
  arr_slice i _ (arr file).

Definition isAddr(file : RegFile) : bool :=
  match readers file with
  | Sync isAddr _ => isAddr
  | _ => false
  end.

Definition file_sync_readreq(val : {k : Kind & Val k})(file : RegFile)(regName : string) : IO {k : Kind & Val k}. refine
  match readers file with
  | Async _ => error "Async file encountered while Sync file expected."
  | Sync true _ => if Kind_decb (projT1 val) (Bit (Nat.log2_up (size file))) then ret val else error "Kind mismatch."
  | Sync false _ => _
  end.
Proof.
  (* isAddr = false *)
  destruct val as [k v].
  destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
  - rewrite Kind_decb_eq in Keq.
    rewrite Keq in v.
    exact (io_do x <- arr_slice (word_to_nat v) (chunk_size file) (arr file);
           ret (existT _ (Array (chunk_size file) (kind file)) x)).
  - exact (error "Kind mismatch").
Defined.

Definition file_sync_readresp(state : FileState)(file : RegFile)(regName : string) : IO (Val (Array (chunk_size file) (kind file))). refine
  match map_lookup (M := M) regName (int_regs state) with
  | None => error "register not found."
  | Some (existT k v) =>
      match readers file with
      | Async _ => error "Async file encountered while Sync file expected."
      | Sync true _ => _
      | Sync false _ => _
      end
  end.
Proof.
  (* isAddr = true *)
  - destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact ((arr_slice (word_to_nat v) (chunk_size file) (arr file))).
    * exact (error "Kind mismatch.").
  (* isAddr = false *)
  - destruct (Kind_decb k (Array (chunk_size file) (kind file))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact (ret v).
    * exact (error "Kind mismatch.").
Defined.

Definition file_writes_mask(file : RegFile)(i : nat)(mask : Val (Array (chunk_size file) Bool))(vals : Val (Array (chunk_size file) (kind file))) : list (nat * Val (kind file)) :=
  let mask_indices := filter (fun i => index i mask) (getFins _) in
    map (fun j => (i + Fin2Restrict.f2n j, index j vals)) mask_indices.

Definition file_writes_no_mask(file : RegFile)(i : nat)(vals : Val (Array (chunk_size file) (kind file))) : list (nat * Val (kind file)) :=
  map (fun j => (i + Fin2Restrict.f2n j, index j vals)) (getFins _).

Definition void_nil : {k : Kind & Val k} :=
  existT _ (Bit 0) (nat_to_word 0).

Definition coerce(v : {k : Kind & Val k})(k : Kind) : IO (Val k).
  refine
    match v with
    | existT k' v' => _
    end.
Proof.
  destruct (Kind_dec k k').
  * rewrite e. exact (ret v').
  * exact (error "Kind mismatch.").
Defined.

Fixpoint Tup_lookup{n} : forall (i : Fin.t n)(ks : Fin.t n -> Kind), Tuple (fun i => Val (ks i)) -> {k : Kind & Val k} :=
  match n return forall (i : Fin.t n)(ks : Fin.t n -> Kind), Tuple (fun i => Val (ks i)) -> {k : Kind & Val k} with
  | 0 => fun i => case0 _ i
  | S m => fun i ks X => fin_case i _ (existT _ (ks F1) (fst X)) (fun j => (Tup_lookup  j _ (snd X)))
  end.

Definition rf_methcall(state : FileState)(methName : string)(val : {k : Kind & Val k}) : IO (option (option FileUpd * {k : Kind & Val k})). refine
  match map_lookup methName (methods state) with
  | None => ret None
  | Some (fc, fileName) => match map_lookup fileName (files state) with
                           | None => ret None
                           | Some file => match fc with
                                          | AsyncRead => _
                                          | ReadReq regName => (io_do p <- file_sync_readreq val file regName;
                                                                ret (Some (Some (IntRegWrite regName p), void_nil)))
                                          | ReadResp regName => (io_do v <- file_sync_readresp state file regName;
                                                                 ret (Some (None, existT _ _ v)))
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
    + exact (ret None).
    + pose (i := word_to_nat v).
      exact (io_do v <- file_async_read file i;
             ret (Some (None, existT _ _ v))).
    + exact (ret None).
    + exact (ret None).
  (* WriteFC is_wr_mask = true *)
  - destruct val as [k v].
    destruct k eqn:G.
    + exact (ret None).
    + exact (ret None).
    + destruct n as [|[|[|]]]; [ exact (error "Kind mismatch.")
                               | exact (error "Kind mismatch.")
                               | exact (error "Kind mismatch.")
                               | idtac ]. (* n should be 3 *)
      exact (let addr := Tup_lookup F1 k0 v in
             let data_k := Tup_lookup (FS F1) k0 v in
             let mask := Tup_lookup (FS (FS F1)) k0 v in
             io_do addr' <- coerce addr (Bit (Nat.log2_up (size file)));
             io_do data' <- coerce data_k (Array (chunk_size file) (kind file));
             io_do mask' <- coerce mask (Array (chunk_size file) Bool);
             ret (Some (Some (ArrWrite fileName _ (file_writes_mask file (word_to_nat addr') mask' data')), void_nil))).
    + exact (ret None).
  (* WriteFC is_wr_mask = false *)
  - destruct val as [k v].
    destruct k eqn:G.
    + exact (error "Kind mismatch.").
    + exact (error "Kind mismatch.").
    + destruct n as [|[|]]; [ exact (error "Kind mismatch.")
                            | exact (error "Kind mismatch.")
                            | idtac ]. (* n should be 2 *)
      exact (let addr := Tup_lookup F1 k0 v in
             let data_k := Tup_lookup (FS F1) k0 v in
             io_do addr' <- coerce addr (Bit (Nat.log2_up (size file)));
             io_do data' <- coerce data_k (Array (chunk_size file) (kind file));
             ret (Some (Some (ArrWrite fileName _ (file_writes_no_mask file (word_to_nat addr') data')), void_nil))).
    + exact (error "Kind mismatch.").
Defined.

Definition exec_file_update(u : FileUpd)(state : FileState) : IO FileState. refine
  match u with
  | IntRegWrite regName v => ret
    {| methods := methods state;
       int_regs := insert regName v (int_regs state);
       files := files state
    |}
  | ArrWrite fileName k upds => match map_lookup fileName (files state) with
                                | None => error "File not found."
                                | Some file => match Kind_dec k (kind file) with
                                               | left pf => io_do _ <- arr_updates (arr file) _; ret state
                                               | _ => error "Kind mismatch."
                                               end
                                end
  end.
Proof.
  rewrite pf in upds.
  exact upds.
Defined.

Fixpoint fold_right_m{A B}(f : B -> A -> IO A)(a : A)(bs : list B) : IO A :=
  match bs with
  | [] => ret a
  | b::bs' => io_do x <- f b a;
              fold_right_m f x bs'
  end.

Definition exec_file_updates := fold_right_m exec_file_update.

Axiom parseFile : forall (size idxNum : nat)(filepath : string), IO (list (nat * W size)).

Definition initialize_file(args : list (string * string))(rfb : RegFileBase)(state : FileState) : IO FileState :=

  let array := match rfInit rfb with
               | RFNonFile None => arr_repl (rfIdxNum rfb) (default_val (rfData rfb))
               | RFNonFile (Some c) => arr_repl (rfIdxNum rfb) (eval_ConstT c)
               | RFFile isAscii isArg file _ _ _ =>
                  let filepath := if isArg then match lookup String.eqb file args with
                                               | Some fp => ret fp
                                               | None => error ("File " ++ file ++ " not found!")
                                               end else ret file in
                  (io_do path <- filepath;
                   io_do pairs <- parseFile (Syntax.size (rfData rfb)) (rfIdxNum rfb) path;
                   io_do arr <- arr_repl (rfIdxNum rfb) (default_val (rfData rfb));
                   io_do _ <- arr_updates arr (List.map (fun '(i,w) => (i,@val_unpack W V _ _ _ w)) pairs);
                   ret arr)
               end in

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
  .

Fixpoint initialize_files(args : list (string * string))(rfbs : list RegFileBase) : IO FileState :=
  match rfbs with
  | [] => ret empty_state
  | (file::files) => (
      io_do st <- initialize_files args files;
      initialize_file args file st)
  end.

End RegFile.

Extract Constant parseFile => "ParseExtract.parseFile".
