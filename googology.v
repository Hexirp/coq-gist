Require Import Init.

(** 全ての関数はこのような型を取る *)
Definition from (a : Type) := a -> nat.

(** おそらく最小の関数 *)
Definition null : from nat := fun _ => O.

(** nullを一般化する。 *)
Definition const (n : nat) : from nat := fun _ => n.

(** 恒等関数 *)
Definition idfunc : from nat := fun x => x.

(** 後者関数 *)
Definition succ : from nat := fun x => S x.

(** 加算 *)
Fixpoint plus (n : nat) : from nat :=
 match n with
 | O => idfunc
 | S n' => fun n => succ (plus n' n)
 end.

(** 二倍する *)
Definition dual : from nat := fun n => plus n n.

(** 三倍する *)
Definition trip : from nat := fun n => plus n (plus n n).

(** 乗算 *)
Fixpoint mult (n : nat) : from nat :=
 match n with
 | O => null
 | S n' => fun n => plus n (mult n' n)
 end.

(** ハイパー演算子 *)
Fixpoint hype (n : nat) : from (from nat) :=
 match n with
 | O => fun f => f O
 | S n' => fun f => f (hype n' f)
 end.