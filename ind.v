Require Import Init Basics.

Inductive composing (k : Type -> Type -> Type) (a b : Type) : Type :=
 | leaf : k a b -> composing k a b
 | tree : forall x, composing k a x -> composing k x b -> composing k a b.

Definition compose
 : forall k a b, (forall x y z, k x y -> k y z -> k x z) -> composing k a b -> k a b.
Proof.
 fix 5.
 intros k a b f x.
 case x.
 -
  intros xLeaf.
  apply xLeaf.
 -
  intros xImpl xLeft xRight.
  apply f with xImpl.
  +
   apply compose.
   apply f.
   apply xLeft.
  +
   apply compose.
   apply f.
   apply xRight.
Save.