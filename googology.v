Require Import Init.

(** * 前提 *)

Definition gen (a : Type) := a -> nat.

(** * 関数群 *)

Definition null : gen nat := fun _ => O.

Definition const (n : nat) : gen nat := fun _ => n.

Definition idea : gen nat := fun x => x.
Definition succ : gen nat := fun x => S x.

Fixpoint plus (n : nat) : gen nat :=
 match n with
 | O => idea
 | S n' => fun n => S (plus n' n)
 end.

Definition dual : gen nat := fun n => plus n n.
Definition trip : gen nat := fun n => plus n (plus n n).

Fixpoint mult (n : nat) : gen nat :=
 match n with
 | O => null
 | S n' => fun n => plus n (mult n' n)
 end.

Fixpoint hype (n : nat) : gen (gen nat) :=
 match n with
 | O => fun f => f O
 | S n' => fun f => f (hype n' f)
 end.