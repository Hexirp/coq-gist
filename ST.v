Require Import Coq.Init.Prelude Coq.Init.Specif.

(* 関数を Map として見做す。これは STRef が参照する値を保存することが出来る。型レベルでも保存できる。 *)
Definition STMap : Type := { f : nat -> Type & forall n : nat, f n }.

(* s として STMap を取ることを想定している。 *)
Definition ST (s : Type) (a : Type) : Type := s -> s * a.
