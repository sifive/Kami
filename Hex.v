Require Import bbv.Word.

Notation "w ~ 'F'" := (WS true (WS true (WS true (WS true w))))
                        (at level 7, left associativity, (* format "w '~' 'F'"*) only parsing) : hex_scope.
Notation "w ~ 'E'" := (WS false (WS true (WS true (WS true w))))
                        (at level 7, left associativity, (*format "w '~' 'E'"*) only parsing) : hex_scope.
Notation "w ~ 'D'" := (WS true (WS false (WS true (WS true w))))
                        (at level 7, left associativity, (* format "w '~' 'D'"*) only parsing) : hex_scope.
Notation "w ~ 'C'" := (WS false (WS false (WS true (WS true w))))
                        (at level 7, left associativity, (* format "w '~' 'C'"*) only parsing) : hex_scope.
Notation "w ~ 'B'" := (WS true (WS false (WS false (WS true w))))
                        (at level 7, left associativity, (* format "w '~' 'B'"*) only parsing) : hex_scope.

Notation "'HO'" := (WO) : hex_scope.

Delimit Scope hex_scope with hex.

Open Scope hex.
Definition test := (HO~E~E~D~E)%hex.
Close Scope hex.
