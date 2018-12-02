Require Import Coq.Init.Prelude.


Class FGH (A : Type) := { fgh : nat -> nat } .

Instance FGH_Empty : FGH Empty_set := { fgh := S } .

Fixpoint iter {P : Type} (o : P) (s : P -> P) (n : nat) :=
  match n with
  | O => o
  | S np => s (iter o s np)
  end
.

Instance FGH_Succ (A : Type) `{FGH A} : FGH (sum unit A) := {
  fgh := fun n => iter n (fgh (A := A)) n
} .

Class FGH_forall {B : nat -> Type} :=
  fgh_forall : forall n, FGH (B n) .

Instance FGH_sum (B : nat -> Type) `{FGH_forall B} : FGH (sigT B) := {
  fgh := fun n => fgh (A := B n) (FGH := fgh_forall n) n
} .
