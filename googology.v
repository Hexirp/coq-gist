Require Import Init.

(** 基礎原理

0 1 2 3 4
1 2 3 4 5
2 3 4 5 6
3 4 5 6 7
4 5 6 7 8

0 2 4 6 8
1 3 5 7 9
2 4 6 8
3 5 7 9
4 6 8

0 3 6 9
1 4 7
2 5 8
3 6 9
4 7

0 4 8
1 5 9
2 6
3 7
4 8

*)

Definition base (m n : nat) := m + n.

Definition new (f : nat -> nat -> nat) (m n : nat) := f m (m + n).

Definition example1 : new base 2 2 = 6.
Proof.
 apply eq_refl.
Qed.