Require Import Init Nat.

Module rbtree.
 Inductive tree : Type :=
 | ni : tree
 | bt : nat -> tree -> tree -> tree
 | rt : nat -> tree -> tree -> tree
 .
End rbtree.