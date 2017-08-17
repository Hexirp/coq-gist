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
 case x; clear x.
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
 case x; clear x.
 -
  intros xLeft.
  apply fL.
  apply xLeft.
 -
  fix go 2.
  intros xImpl xLeft xRight.
  case xLeft; clear xLeft.
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

Axiom undefined : forall a, a.

Definition run_comp : forall t a b, composing (kleisli (skeleton t)) a b -> a -> skeleton t b.
Proof.
 intros t.
 fix go 3.
 intros a b f x.
 case f; clear f.
 -
  intros fLeaf.
  apply fLeaf.
  apply x.
 -
  fix go' 2.
  intros fImpl fLeft fRight.
  case fLeft; clear fLeft.
  +
   intros fLeftLeaf.
   case (fLeftLeaf x); clear fLeftLeaf.
   *
    intros fLeftLeafReturnS.
    apply (go _ _ fRight).
    apply fLeftLeafReturnS.
     (* This appliecation is based lazy evaluation. undefined is fLeftLeafReturnS. *)
   *
    intros fLeftLeafBindSImpl fLeftLeafBindSValue fLeftLeafBindSFunc.
    apply (bindS _ _ _ fLeftLeafBindSValue).
    apply (tree _ _ _ _ fLeftLeafBindSFunc).
    apply fRight.
  +
   intros fLeftImpl fLeftLeft fLeftRight.
   apply (go' _ fLeftLeft).
   apply (tree _ _ _ fImpl).
   *
    apply fLeftRight.
   *
    apply fRight.
Admitted. (* Because run_comp isn't stop. *)

Definition debone : forall t a, skeleton t a -> monadic t (skeleton t) a.
Proof.
 intros t a x.
 case x; clear.
 -
  intros xReturnS.
  apply retn.
  apply xReturnS.
 -
  intros xBindSImpl xBindSValue xBindSFunc.
  apply (bn _ _ _ xBindSImpl).
  +
   apply xBindSValue.
  +
   apply run_comp.
   apply xBindSFunc.
Save.