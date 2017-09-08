Require Import Init Basics.

Section category.
 Variable Cat : Type -> Type -> Type.
 Variable A : Type.

 Inductive cat : Type -> Type :=
 | idarrow : cat A
 | compose : forall B X, Cat X B -> cat X -> cat B.

 Definition cat_rect_simple (P : Type -> Type)
  : P A -> (forall (B X : Type), Cat X B -> P X -> P B) -> (forall (T : Type), cat T -> P T).
 Proof.
  intros.
  apply (cat_rect (fun x => fun _ => P x)).
  -
   apply X.
  -
   intros.
   apply X0 with X2.
   +
    apply c.
   +
    apply X3.
  -
   apply X1.
 Defined.

 Print cat_rect_simple.