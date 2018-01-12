Require Import Init.

(** 基礎原理

0 0 0 0 0
1 1 1 1 1
2 2 2 2 2
3 3 3 3 3
4 4 4 4 4

0 0 0 0 0
0 1 2 3 4
0 2 4 6 8
0 3 6 9 12
0 4 8 12 16

0 0 0 0 0
0 1 4 9 16
0 2 8 18 32
0 3 12 27 48
0 4 16 36 64

*)

Definition const (m n : nat) := n.

Definition new (f : nat -> nat -> nat) (m n : nat) := f m (m * n).

Definition example1 : new const 2 2 = 4.
Proof.
 apply eq_refl.
Qed.