Require Import Init.

Axiom yfix : forall {a : Type}, (a -> a) -> a.
Axiom yfix_def : forall a, forall (f : a -> a), yfix f = f (yfix f).

Definition object_f fx f g := forall a, f a -> g (prod a (fx f g)).

Definition object := yfix object_f.

Definition arr a b := a -> b.

Definition stream m a := object (arr a) m.

Load pipe.

Definition id : forall a b, pipe a b a b.
Proof.
 apply yfix.
 intros yf a b.
 apply await.
 -
  intros A.
  apply yield.
  apply A.
  apply yf.
 -
  intro B.
  apply done.
  apply B.
Defined.

Print id.