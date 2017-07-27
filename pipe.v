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
    apply X1.
   *
    apply X2.
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

Definition map_p : forall i u o r r', (r -> r') -> pipe i u o r -> pipe i u o r'.
Proof.
 intros i u o r r' f A.
 induction A.
 -
  apply await.
  +
   apply X.
  +
   apply X0.
 -
  apply IHA.
 -
  apply done.
  apply f.
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

Definition pipe_from_list : forall o, list o -> pipe void unit o unit.
Proof.
 intros o A.
 induction A.
 -
  apply done.
  apply tt.
 -
  apply yield.
  +
   apply a.
  +
   apply IHA.
Defined.

Definition test_1 : pipe void unit nat unit := pipe_from_list nat (0 :: 1 :: 2 :: 3 :: nil).
Definition test_2 : pipe nat unit nat unit.
Proof.
 apply await.
 -
  intros A.
  induction A.
  +
   apply done.
   apply tt.
  +
   apply IHA.
 -
  apply done.
Defined.
Definition test_3 : pipe void unit nat unit := compose _ _ _ _ _ _ test_2 test_1.

Eval cbv delta iota beta in test_1.
Print test_2.
Eval cbv delta iota beta in test_3.

Extraction Language Haskell.

Extraction pipe_rect.
Extraction compose.
Extraction map_p.
Extraction run_p.
Extraction pipe_from_list.