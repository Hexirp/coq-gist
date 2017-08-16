Require Import Init.

Inductive coyoneda (f : Type -> Type) (a : Type) : Type :=
 cy : forall x, f x -> (x -> a) -> coyoneda f a.

Definition map_c : forall f a a', (a -> a') -> coyoneda f a -> coyoneda f a'.
Proof.
 intros f a a' F A.
 induction A.
 apply cy with x.
 -
  apply f0.
 -
  intros xv.
  apply F.
  apply a0.
  apply xv.
Defined.