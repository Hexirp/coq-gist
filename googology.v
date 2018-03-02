Require Import Init.

Definition f := O.

Definition f0 := S f.

Definition f00 := S f0.

Definition f000 := S f00.

Definition f0000 := S f000.

Definition ind P (cO : P) (cS : P -> P) : nat -> P :=
 fix go (x : nat) : P :=
  match x with
  | O => cO
  | S xp => cS (go xp)
  end
.

Definition f01 := ind nat O S.

Definition compose {A B C} : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

Definition f010 := compose S f01.

Definition f0100 := compose S f010.

Definition f0101 := ind (nat -> nat) f01 (compose S).

Definition f01010 := compose (compose S) f0101.

Definition f010100 := compose (compose S) f01010.

Definition f010101 := ind (nat -> nat -> nat) f0101 (compose (compose S)).

Definition f0101010 := compose (compose (compose S)) f010101.

Definition f01010100 := compose (compose (compose S)) f0101010.

Definition t A := nat -> A.

Definition s0 : nat -> nat := S.

Definition s00 : t nat -> t nat := compose S.

Definition s000 : t (t nat) -> t (t nat) := compose (compose S).

Definition t01 : nat -> Type := ind Type nat t.

Definition indD P (cO : P O) (cS : forall n, P n -> P (S n)) : forall n, P n :=
 fix go (x : nat) : P x :=
  match x with
  | O => cO
  | S xp => cS xp (go xp)
  end
.

Definition s01 : forall n, t01 n -> t01 n.
Proof.
 apply (indD (fun n => t01 n -> t01 n)).
 -
  cbn.
  apply S.
 -
  intros x IH.
  cbn.
  unfold t.
  apply compose.
  apply IH.
Defined.