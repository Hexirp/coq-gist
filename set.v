Require Import Init Nat.

(*
Inductive listp A : (A -> listp A -> Prop) -> Type :=
| nlp : forall P, listp A P
| cnp : forall P (x : A) (xs : list A), P x xs -> listp A P.
*)

Definition inl : nat -> list nat -> bool.
Proof.
 intros x.
 fix go 1.
 intros y.
 case y; clear y.
 -
  apply true.
 -
  intros y ys.
  apply orb.
  +
   apply eqb.
   *
    apply x.
   *
    apply y.
  +
   apply go.
   apply ys.
Save.

Definition uniques : list nat -> bool.
Proof.
 fix go 1.
 intros x.
 case x; clear x.
 -
  apply true.
 -
  intros x xs.
  apply andb.
  +
   apply negb.
   apply inl.
   *
    apply x.
   *
    apply xs.
  +
   apply go.
   apply xs.
Save.

Definition set := { x : list nat | eq_true (uniques x) }.

Definition add_inner : nat -> list nat -> list nat.
Proof.
 intros x.
 fix go 1.
 intros y.
 case y; clear y.
 -
  apply nil.
 -
  intros y ys.
  case (eqb x y).
  +
   apply ys.
  +
   apply cons.
   *
    apply y.
   *
    apply go.
    apply ys.
Save.

Definition add : nat -> set -> set.
Proof.
 intros x y.
 case y; clear y.
 intros y yH.
 exists (add_inner x y).
Abort.