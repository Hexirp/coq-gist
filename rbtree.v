Require Import Init Nat.

Module rbtree.
 Inductive tree : Type :=
 | ni : tree
 | bt : nat -> tree -> tree -> tree
 | rt : nat -> tree -> tree -> tree
 .

 Definition tree_func {r : Type} (nr : r) (br : nat -> r -> r -> r) (rr : nat -> r -> r -> r)
     : tree -> r :=
 fix go (t : tree) : r :=
  match t with
  | ni => nr
  | bt n tl tr => br n (go tl) (go tr)
  | rt n tl tr => rr n (go tl) (go tr)
  end
 .
End rbtree.