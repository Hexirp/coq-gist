Require Import Init.

(** 全ての関数はこのような型を取る *)
Definition from (a : Type) := a -> nat.

(** シンプルな帰納法 *)
Definition nat_rect_simple : forall (R : Type), R -> (R -> R) -> nat -> R.
Proof.
 intros R case_O case_S n.
 apply (nat_rect (fun _ => R)).
 -
  apply case_O.
 -
  intros _.
  apply case_S.
 -
  apply n.
Defined.

(** おそらく最小の関数 *)
Definition null : from nat.
Proof.
 intros _.
 apply O.
Defined.

(** nullを一般化する。 *)
Definition const (n : nat) : from nat.
Proof.
 intros _.
 apply n.
Defined.

(** 恒等関数 *)
Definition id : from nat.
Proof.
 intros n.
 apply const.
 -
  apply n.
 -
  apply n.
Defined.

(** 後者関数 *)
Definition succ : from nat.
Proof.
 intros n.
 apply const.
 -
  apply S.
  apply n.
 -
  apply n.
Defined.

(** 加算 *)
Definition plus (n : nat) : from nat.
Proof.
 revert n.
 apply nat_rect_simple.
 -
  apply id.
 -
  intros f n.
  apply S.
  apply f.
  apply n.
Defined.

(** 二倍する *)
Definition dual : from nat.
Proof.
 intros n.
 apply plus.
 -
  apply n.
 -
  apply n.
Defined.

(** 三倍する *)
Definition trip : from nat.
Proof.
 intros n.
 apply plus.
 -
  apply n.
 -
  apply plus.
  +
   apply n.
  +
   apply n.
Defined.

(** 乗算 *)
Definition mult (n : nat) : from nat.
Proof.
 revert n.
 apply nat_rect_simple.
 -
  apply null.
 -
  intros f n.
  apply plus.
  +
   apply n.
  +
   apply f.
   apply n.
Defined.

(** ハイパー演算子 *)
Fixpoint hype (n : nat) : from (from nat) :=
 match n with
 | O => fun f => f O
 | S n' => fun f => f (hype n' f)
 end.