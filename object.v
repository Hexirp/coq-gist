Require Import Init.

(** この定義は出来ない。prodはcoqでのタプル。 *)
Fail Inductive object (F G : Type -> Type) : Type :=
| obj_C : (forall A, F A -> G (prod A (object F G))) -> object F G.

(** 上記の定義ができない理由を示す。

もしこの型が定義出来てしまうと以下のような関数が書けてしまう。

Definition Ω (x : wrong) : nat :=
 match x with
 | wrong_C f => f x
 end.

これは停止しない。Coqは停止しない関数を定義することが出来ないように作られているからこれはいけない。

上記の型に対しても同様で、Gをうまく選ぶとwrongと同様に停止しない関数を定義することが出来てしまう。

*)
Fail Inductive wrong : Type :=
| wrong_C : (wrong -> nat) -> wrong.