Require Import Init.

Definition State (s a : Type) : Type := s -> a * s.

(* 正しいバージョン *)
Definition bind : forall s a b, State s a -> (a -> State s b) -> State s b.
Proof.
 intros s a b A B sv.
 assert (a * s -> b * s).
 -
  intros H.
  destruct H as [Ha Hs].
  apply B.
  +
   apply Ha.
  +
   apply Hs.
 -
  apply X.
  apply A.
  apply sv.
Defined.

(* 間違ったバージョン *)
Definition bind' : forall s a b, State s a -> (a -> State s b) -> State s b.
Proof.
 intros s a b A B sv.
 apply B.
 -
  assert (a * s -> a).
  +
   apply fst.
  +
   apply X.
   apply A.
   apply sv.
 -
  apply sv.
Defined.

Print bind.
Print bind'.