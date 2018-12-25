(** * 超絶技巧演習問題 - Coq *)

Require Import Coq.Init.Prelude Coq.Init.Nat.

Open Scope nat_scope.

(** フェルマーの最終定理 *)

Definition felmat
  : forall n : nat, 2 < n -> ~ exists x y z, 0 < x /\ 0 < y /\ 0 < z /\ x ^ n + y ^ n = z ^ n.
Proof.
  (* [Admitted] を [Qed] に取り換えて、この空欄を埋めよ *)
Admitted.

(** カタラン予想 *)

Definition catalanic a b x y := 1 < a /\ 1 < b /\ 1 < x /\ 1 < y /\ x ^ a = 1 + y ^ b.

Definition catalan
  : forall a b x y, catalanic a b x y -> x = 3 /\ a = 2 /\ y = 2 /\ b = 3.
Proof.
  (* [Admitted] を [Qed] に取り換えて、この空欄を埋めよ *)
Admitted.

(** バウデットの予想 *)
Definition baudetic (P : nat -> bool) a b c n := forall p, p < n -> P (a + b * p) = c.

Definition baudet
  : forall P, exists c, forall n, exists a b, baudetic P a b c n.
Proof.
  (* [Admitted] を [Qed] に取り換えて、この空欄を埋めよ *)
Admitted.

(** コラッツの問題 *)
Definition collatzic n := if even n then div2 n else n * 3 + 1.

Definition collatz
  : forall n, n <> 0 -> exists p, iter p collatzic n = 1.
Proof.
  (* [Admitted] を [Qed] に取り換えて、この空欄を埋めよ *)
Admitted.
