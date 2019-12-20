Require Export Kami.Lib.Word.
Require Export Kami.Lib.HexNotation.
Open Scope word_scope.

Notation "'Ox' a" := (NToWord _ (hex a)) (at level 50).

Notation "sz ''h' a" := (NToWord sz (hex a)) (at level 50).

Goal 8'h"a" = ZToWord 8 (wordVal _ (NToWord 4 10)).
Proof.
  reflexivity.
Qed.

Goal Ox"41" = ZToWord 7 65.
Proof.
  reflexivity.
Qed.

Notation "sz ''b' a" := (ZToWord sz (Z.of_nat (bin a))) (at level 50).

Notation "''b' a" := (ZToWord _ (Z.of_nat (bin a))) (at level 50).

Goal 'b"00001010" = ZToWord 8 (wordVal _ (NToWord 4 10)).
Proof.
  reflexivity.
Qed.

Goal 'b"1000001" = ZToWord 7 65.
Proof.
  reflexivity.
Qed.
