Require Import Init Nat.

Axiom undefined : forall a, a.

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

Definition add (n : nat) (s : set) : set :=
 match s with
 | exist _ s' p =>
  match inl n s' with
  | false => exist _ s' (undefined (eq_true (uniques s')))
  | true => exist _ s' p
  end
 end
.