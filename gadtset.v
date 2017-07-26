Require Import Coq.Lists.List.

Extraction Language Haskell.

Extract Inductive list => "([])" ["[]" "(:)"].

Inductive Product : list Type -> Type :=
 | nil_p : Product nil
 | cons_p : forall (x : Type) (xs : list Type), x -> Product xs -> Product (x :: xs).

Definition lookup_p : forall (x : Type) (xs : list Type), In x xs -> Product xs -> x.
Proof.
 intros x xs H R.
 induction xs.
 -
  contradiction.
 -
  apply IHxs.
  +
   case H.
   *
    intros refl.
    rewrite <- refl.
    assert (Product (a :: xs) -> a).

Extraction Product.