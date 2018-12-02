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

Class FGH_forall {B : nat -> Type} :=
  fgh_forall : forall n, FGH (B n) .

Instance FGH_sum (B : nat -> Type) `{FGH_forall B} : FGH (sigT B) := {
  fgh := fun n => fgh (A := B n) (FGH := fgh_forall n) n
} .


(* fgh {0} n := n + 1 *)
Eval compute in fgh (A := Empty_set) 2 . (* 3 *)
Eval compute in fgh (A := Empty_set) 3 . (* 4 *)
Eval compute in fgh (A := Empty_set) 4 . (* 5 *)

(* fgh {1} n := 2 * n *)
Eval compute in fgh (A := sum unit Empty_set) 2 . (* 4 *)
Eval compute in fgh (A := sum unit Empty_set) 3 . (* 6 *)
Eval compute in fgh (A := sum unit Empty_set) 4 . (* 8 *)

(* fgh {2} n := (2 ^ n) * n *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 2 . (* 8 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 3 . (* 24 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 4 . (* 64 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 5 . (* 160 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 6 . (* 384 *)
Eval compute in fgh (A := sum unit (sum unit Empty_set)) 7 . (* 896 *)
