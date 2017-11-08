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

Definition new_p (n : nat) (s : list nat) (p : eq_true (uniques s)) (q : eq_true (inl n s))
    : eq_true (uniques (cons n s)) :=
 undefined (eq_true (uniques (cons n s))).

Definition add (n : nat) (s : set) : set :=
 match s with
 | exist _ s' p =>
  match inl n s' with
  | false => exist _ (cons n s') (new_p n s' p (undefined (eq_true (inl n s'))))
  | true => exist _ s' p
  end
 end
.