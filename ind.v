Require Import Init Basics.

Inductive composing (k : Type -> Type -> Type) (a b : Type) : Type :=
 | leaf : k a b -> composing k a b
 | tree : forall x, composing k a x -> composing k x b -> composing k a b.

Definition compose
 : forall k a b, (forall x y z, k x y -> k y z -> k x z) -> composing k a b -> k a b.
Proof.
 intros k.
 fix go 4.
 intros a b f x.
 case x.
 -
  intros xLeaf.
  apply xLeaf.
 -
  intros xImpl xLeft xRight.
  apply (f a xImpl b).
  +
   apply go.
   apply f.
   apply xLeft.
  +
   apply go.
   apply f.
   apply xRight.
Save.

Definition viewL
 : forall k a b r,
  composing k a b -> (k a b -> r) -> (forall x, k a x -> composing k x b -> r) -> r.
Proof.
 intros k a b r x fL fT.
 case x.
 -
  intros xLeft.
  apply fL.
  apply xLeft.
 -
  fix go 2.
  intros xImpl xLeft xRight.
  case xLeft.
  +
   intros xLeftLeaf.
   apply (fT xImpl).
   *
    apply xLeftLeaf.
   *
    apply xRight.
  +
   intros xLeftImpl xLeftLeft xLeftRight.
   apply (go xLeftImpl).
   *
    apply xLeftLeft.
   *
    apply (tree _ _ _ xImpl).
    --
     apply xLeftRight.
    --
     apply xRight.
Save.

Definition kleisli (m : Type -> Type) (a b : Type) : Type := a -> m b.

Inductive skeleton (t : Type -> Type) (a : Type) : Type :=
 | returnS : a -> skeleton t a
 | bindS : forall x, t x -> composing (kleisli (skeleton t)) x a -> skeleton t a.

Inductive monadic (t m : Type -> Type) (a : Type) :=
 | retn : a -> monadic t m a
 | bn : forall x, t x -> (x -> m a) -> monadic t m a.

Definition debone : forall t a, skeleton t a -> monadic t (skeleton t) a.
Proof.
 intros t a x.
 case x.
 -
  intros xRet.
  apply retn.
  apply xRet.
 -
  intros xImpl xValue xFunc.
  apply (bn _ _ _ xImpl).
  +
   apply xValue.
Admitted.