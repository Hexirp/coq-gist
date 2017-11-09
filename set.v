Require Import Init Nat.

Axiom undefined : forall a, a.

Fixpoint ninl (n : nat) (a : list nat) : bool :=
 match a with
 | nil => true
 | cons x a' =>
  match eqb n x with
  | false => ninl n a'
  | true => false
  end
 end
.

Fixpoint uniques (a : list nat) : bool :=
 match a with
 | nil => true
 | cons x a' =>
  match ninl x a' with
  | false => false
  | true => uniques a'
  end
 end
.

Definition set := { x : list nat | eq_true (uniques x) }.

Definition new_p (n : nat) (s : list nat) (p : eq_true (uniques s)) (q : eq_true (ninl n s))
    : eq_true (uniques (cons n s)) :=
 undefined (eq_true (uniques (cons n s))).

Definition add (n : nat) (s : set) : set :=
 match s with
 | exist _ s' p =>
  match ninl n s' with
  | false => exist _ (cons n s') (new_p n s' p (undefined (eq_true (ninl n s'))))
  | true => exist _ s' p
  end
 end
.