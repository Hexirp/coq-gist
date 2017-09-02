Require Import Init.

Inductive coyoneda (f : Type -> Type) (a : Type) : Type :=
 | mkcoyoneda : forall x, (x -> a) -> f x -> coyoneda f a.

Definition lift f a : f a -> coyoneda f a.
Proof.
 intros af.
 apply mkcoyoneda with a.
 -
  intros A.
  apply A.
 -
  apply af.
Save.

Definition map f a b : (a -> b) -> coyoneda f a -> coyoneda f b.
Proof.
 intros ba afCo.
 case afCo.
 intros x ax xf.
 apply mkcoyoneda with x.
 -
  intros X.
  apply ba.
  apply ax.
  apply X.
 -
  apply xf.
Save.

Inductive object (f g : Type -> Type) : Type :=
 | mkobj : (forall x, coyoneda f x -> coyoneda g (prod x (object f g))) -> object f g.

Axiom Fix : forall (a : Type), (a -> a) -> a.

Definition compose f g h : object g h -> object f g -> object f h.
Proof.
 apply Fix.
 intros go hgObj gfObj.
 apply mkobj.
 intros x xfCo.
 apply map with (prod (prod x (object g h)) (object f g)).