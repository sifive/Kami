Require Export Lib.Word.
Require Export Lib.HexNotation.
Require Export Lib.Word.
Export Word.Notations.
Open Scope word_scope.
Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv.


Notation "'Ox' a" := (NToWord _ (hex a)) (at level 50).

Notation "sz ''h' a" := (NToWord sz (hex a)) (at level 50).

Goal 8'h"a" = zToWord 8 (wordVal _ (NToWord 4 10)).
Proof.
  reflexivity.
Qed.

Goal Ox"41" = zToWord 7 65.
Proof.
  reflexivity.
Qed.

Notation "sz ''b' a" := (zToWord sz (Z.of_nat (bin a))) (at level 50).

Notation "''b' a" := (zToWord _ (Z.of_nat (bin a))) (at level 50).

Goal 'b"00001010" = zToWord 8 (wordVal _ (NToWord 4 10)).
Proof.
  reflexivity.
Qed.

Goal 'b"1000001" = zToWord 7 65.
Proof.
  reflexivity.
Qed.
