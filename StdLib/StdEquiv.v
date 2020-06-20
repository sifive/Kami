Require Import Kami.StdLib.Fin.
Require Import Kami.StdLib.VectorDef.
Require Import Vector.

Fixpoint fin_to_fin_new {n} (i : Fin.t n) : Fin n :=
  match i with
  | Fin.F1 => F1
  | Fin.FS j => FS (fin_to_fin_new j)
  end.

Fixpoint fin_new_to_fin {n} (i : Fin n) : Fin.t n :=
  match n as n0 return (Fin n0 -> Fin.t n0) with
  | O => StdLib.Fin.case0 (fun _ => Fin.t 0)
  | S m =>
    (fun j =>
       match j with
       | inl _ => Fin.F1
       | inr k => Fin.FS (fin_new_to_fin k)
       end)
  end i.

Lemma F2FN_id {n} (i : Fin.t n) :
  fin_new_to_fin (fin_to_fin_new i) = i.
Proof. induction i; simpl; [|rewrite IHi]; reflexivity. Qed.

Lemma FN2F_id {n} (i : Fin n) :
  fin_to_fin_new (fin_new_to_fin i) = i.
Proof.
  induction n; destruct i; simpl.
  - destruct u; reflexivity.
  - rewrite IHn; reflexivity.
Qed.

Fixpoint vec_to_vec_new {A n} (v : Vector.t A n) : Vec A n :=
  match v with
  | Vector.nil _ => Kami.StdLib.VectorDef.nil _
  | Vector.cons _ h _ tl => Kami.StdLib.VectorDef.cons _ h _ (vec_to_vec_new tl)
  end.

Fixpoint vec_new_to_vec {A n} (v : Vec A n) : Vector.t A n :=
  match n as n0 return (Vec A n0 -> Vector.t A n0) with
  | O => StdLib.VectorDef.case0 (fun _ => Vector.t A 0) (Vector.nil _)
  | S m => (fun v' => Vector.cons _ (fst v') _ (vec_new_to_vec (snd v')))
  end v.

Lemma V2VN_id {A n} (v : Vector.t A n) :
  vec_new_to_vec (vec_to_vec_new v) = v.
Proof. induction v; simpl; [|rewrite IHv]; reflexivity. Qed.

Lemma VN2V_id {A n} (v : Vec A n) :
  vec_to_vec_new (vec_new_to_vec v) = v.
Proof.
  induction n; destruct v; simpl; auto.
  rewrite IHn; reflexivity.
Qed.
