Require Import Init Nat.

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

Definition add_uniques (n : nat) (s : list nat) (p : eq_true (uniques s)) (q : eq_true (ninl n s))
    : eq_true (uniques (cons n s)).
Proof.
 unfold uniques.
 fold (uniques s).
 destruct (ninl n s).
 -
  apply p.
 -
  apply q.
Defined.

Definition if_eq_true {r : Type} (b : bool) (t : eq_true b -> r) (f : r) : r.
Proof.
 destruct b.
 -
  apply t.
  apply is_eq_true.
 -
  apply f.
Defined.

Definition add (n : nat) (s : set) : set :=
 match s with
 | exist _ s' p =>
  if_eq_true (ninl n s')
   (fun q => exist _ (cons n s') (add_uniques n s' p q))
   (exist _ s' p)
 end
.