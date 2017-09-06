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

(** 上記の減少を防ぐ方法を提案する。

上記の型が帰納的に使われている位置を見てみると、これはcontravariantな位置である。
つまり、functorな位置であればこの問題は発生しないことになる。
つまり、objectの場合ではGがfunctorしか受け取れないようにすればよい。
coyonedaを使ってたとえcontravariantな型が渡されても無理やりfunctorに変えればよい。

*)
Inductive coyoneda (F : Type -> Type) (A : Type) : Type :=
| coyoneda_C : forall X, (X -> A) -> F X -> coyoneda F A.

Definition coyoneda_map F A B : (A -> B) -> coyoneda F A -> coyoneda F B.
Proof.
 intros f [X g x].
 apply coyoneda_C with X; auto.
Defined.

(** coyonedaを使ってもまだ問題があることを示す。

重複した名前を使いたいため、Moduleを使う。

*)
Module WObject.
 (** coyonedaによる問題の解決 *)
 Inductive object (F G : Type -> Type) : Type :=
 | object_C : (forall A, F A -> coyoneda G (A * object F G)) -> object F G.

 Definition object_run F G A : object F G -> F A -> coyoneda G (A * object F G).
 Proof.
  intros [f].
  apply f.
 Defined.