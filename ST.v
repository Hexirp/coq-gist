Require Import Coq.Init.Prelude Coq.Init.Specif.

Definition STMap (s : Type) : Type := { f : nat -> Type & forall n : nat, f n }.

Definition ST (s : Type) (a : Type) : Type := STMap s -> STMap s * a.
