Require Import Init.
Require Import List.

Inductive pipe (i u o r : Type) : Type :=
 | await : (i -> pipe i u o r) -> (u -> pipe i u o r) -> pipe i u o r
 | yield : o -> pipe i u o r -> pipe i u o r
 | done  : r -> pipe i u o r.

Definition compose : forall i u x y o r, pipe x y o r -> pipe i u x y -> pipe i u o r.
Proof.
 intros i u x y o r A B.
 induction A.
 -
  induction B.
  +
   apply await.
   *
    intros iv.
    apply X1.
    apply iv.
   *
    intros uv.
    apply X2.
    apply uv.
  +
   apply IHB.
  +
   apply X0.
   apply r0.
 -
  apply IHA.
 -
  apply done.
  apply r0.
Defined.

Definition void : Type := Empty_set.

Definition run_p : forall r, pipe void unit void r -> r.
Proof.
 intros r A.
 induction A.
 -
  apply X0.
  apply tt.
 -
  apply IHA.
 -
  apply r0.
Defined.

Definition 