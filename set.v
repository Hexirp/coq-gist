Require Import Init Nat.

Fixpoint inl (n : nat) (a : list nat) : bool :=
 match a with
 | nil => true
 | cons x a' =>
  match eqb n x with
  | false => inl n a'
  | true => true
  end
 end
.

Fixpoint uniques (a : list nat) : bool :=
 match a with
 | nil => true
 | cons x a' =>
  match inl x a' with
  | false => uniques a'
  | true => false
  end
 end
.

Definition set := { x : list nat | eq_true (uniques x) }.

Definition add_inner : nat -> list nat -> list nat.
Proof.
 intros x.
 fix go 1.
 intros y.
 case y; clear y.
 -
  apply (cons x nil).
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
Defined.

Definition exmdl : forall x, x = true \/ x = false.
Proof.
 intros x.
 case x.
 -
  left.
  apply eq_refl.
 -
  right.
  apply eq_refl.
Defined.

Definition add : nat -> set -> set.
Proof.
 intros x y.
 case y; clear y.
 fix go 1.
 intros y yH.
 exists (add_inner x y).
 revert yH.
 case y; clear y.
 -
  intros _.
  apply is_eq_true.
 -
  intros y ys yH.
  unfold add_inner.
  case (exmdl (eqb x y)).
  +
   intros eqH.
   rewrite eqH.
   unfold uniques in yH.
   case (exmdl (negb (inl y ys))).
   *
    intros neH.
    rewrite neH in yH.
    unfold andb in yH.
    unfold uniques.
    unfold andb.
    apply yH.
   *
    intros neH.
    rewrite neH in yH.
    unfold andb in yH.
    generalize (eq_refl true).
    pattern true at 1.
    case yH.