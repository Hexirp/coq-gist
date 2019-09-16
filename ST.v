Require Import Coq.Init.Prelude Coq.Init.Specif.

(* 自然数をアドレスと考える。アドレス n に型が入っていなければ、値も入っていない。
   型が入っていれば値も必ず入っている。当然、値が入っていれば型も入っている。 *)
Definition STMapValue (f : nat -> option Type) (x : nat) : Type :=
    match f x with
    | Some t => t
    | None => unit
    end.

(* 関数を Map として見做す。これは STRef が参照する値を保存することが出来る。型レベルでも保存できる。 *)
Definition STMap (s : Type) : Type := { f : nat -> option Type & forall n : nat, STMapValue f n }.

(* s として STMap を取ることを想定している。 *)
Definition ST (s : Type) (a : Type) : Type := s -> s * a.
