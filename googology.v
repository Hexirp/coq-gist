Require Import Coq.Init.Prelude.


Class FGH (A : Type) := { fgh : nat -> nat } .

Instance FGH_Empty : FGH Empty_set := { fgh := S } .

Fixpoint iter {P : Type} (o : P) (s : P -> P) (n : nat) :=
  match n with
  | O => o
  | S np => s (iter o s np)
  end
.

Instance FGH_Succ (A : Type) `{FGH A} : FGH (sum unit A) := {
  fgh := fun n => iter n (fgh (A := A)) n
} .

Class FGH_forall (B : nat -> Type) :=
  fgh_forall : forall n, FGH (B n) .

Instance FGH_sum (B : nat -> Type) `{FGH_forall B} : FGH (sigT B) := {
  fgh := fun n => fgh (A := B n) (FGH := fgh_forall n) n
} .


(* fgh {0} n = n + 1 *)
Eval compute in fgh (A := Empty_set) 2 . (* 3 *)
Eval compute in fgh (A := Empty_set) 3 . (* 4 *)
Eval compute in fgh (A := Empty_set) 4 . (* 5 *)

(* fgh {1} n = 2 * n *)
Eval compute in fgh (A := sum unit Empty_set) 2 . (* 4 *)
Eval compute in fgh (A := sum unit Empty_set) 3 . (* 6 *)
Eval compute in fgh (A := sum unit Empty_set) 4 . (* 8 *)

(* fgh {2} n = (2 ^ n) * n *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 2 . (* 8 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 3 . (* 24 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 4 . (* 64 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 5 . (* 160 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 6 . (* 384 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 7 . (* 896 *)

(* fgh {3} n := ??? > 2 ^^ n *)
Eval compute in fgh (A := sum unit (sum unit (sum unit Empty_set))) 2 . (* 2048 *)
(* Eval compute in fgh (A := sum unit (sum unit (sum unit Empty_set))) 3 . *) (* 計算しようとすると落ちる *)


(* ここまでの極限を求める *)

Definition omega_ : nat -> Type := iter Empty_set (sum unit) .

Instance FGH_forall_omega_ : FGH_forall omega_ .
Proof.
 intros n.
 induction n.
 -
  exact _.
 -
  exact _.
Defined.

Definition omega : Type := sigT omega_ .

Instance FGH_omega : FGH omega := _ .

(* fgh {ω} n > Ack(n, n) *)
Eval compute in fgh (A := omega) 1 . (* 1 *)
Eval compute in fgh (A := omega) 2 . (* 8 *)
(* Eval compute in fgh (A := omega) 3 . *) (* 計算しようとすると落ちる *)


Definition omega_p_omega_ : nat -> Type := iter omega (sum unit) .

Instance FGH_forall_omega_p_omega_ : FGH_forall omega_p_omega_ .
Proof.
 intro n.
 induction n.
 -
  exact _.
 -
  exact _.
Defined.

Definition omega_p_omega : Type := sigT omega_p_omega_ .

(* fgh {ω+ω} ≈ 爆発 (http://ja.googology.wikia.com/wiki/%E7%88%86%E7%99%BA) *)
Eval compute in fgh (A := omega_p_omega) 1 . (* 2 *)
(* Eval compute in fgh (A := omega_p_omega) 2 . *) (* 計算しようとすると落ちる *)


(* さらに極限を取る。 *)

(* Empty_set, (sigT (iter Empty_set (sum unit))), (sigT (iter (sigT (iter Empty_set (sum unit))) (sum unit))), ... *)

Definition omega_m_omega_ : nat -> Type .
Proof.
 apply iter.
 -
  exact Empty_set .
 -
  intro A.
  refine (sigT (A := nat) _) .
  apply iter.
  +
   exact A.
  +
   exact (sum unit).
Defined.

Instance FGH_forall_omega_m_omega_ : FGH_forall omega_m_omega_ .
Proof.
 intro n.
 induction n.
 -
  exact _.
 -
  apply FGH_sum.
  intro m.
  induction m.
  +
   exact _.
  +
   exact _.
Defined.

Definition omega_m_omega : Type := sigT omega_m_omega_ .

(* fgh {ω*ω} ≈ チェーン表記 *)
Eval compute in fgh (A := omega_m_omega) 1 . (* 2 *)


(* さらに極限を取る。 *)

Definition omega_e_omega_ : nat -> Type.
Proof.
 apply iter.
 -
  exact Empty_set.
 -
  intro A.
  refine (sigT (A := nat) _).
Defined.
