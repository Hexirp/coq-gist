Require Import Coq.Init.Prelude.

Definition pointwise_eq {A : Type} {B : A -> Type} (f g : forall x, B x) : Prop :=
 forall x, f x = g x.

Notation "f == g" := (pointwise_eq f g) (at level 70, no associativity) : type_scope.

Definition id {A : Type} : A -> A := fun x => x.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity)
 : function_scope.
