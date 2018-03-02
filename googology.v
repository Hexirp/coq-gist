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
