Require Import Init.

Inductive coyoneda (f : Type -> Type) (a : Type) : Type :=
 | mkcoyoneda : forall x, (x -> a) -> f x -> coyoneda f a.

Inductive object (f g : Type -> Type) : Type :=
 | mkobj : (forall x, f x -> coyoneda g (prod x (object f g))) -> object f g.