Require Import Init.

Definition f0 := O.

Definition f1 := S O.

Definition f2 := S (S O).

Definition f3 := S (S (S O)).

Definition f4 := S (S (S (S O))).

Definition ind P (cO : P) (cS : P -> P) : nat -> P :=
 fix go (x : nat) : P :=
  match x with
  | O => cO
  | S xp => cS (go xp)
  end
.

Definition fo := ind nat O S.

Definition compose {A B C} : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

Definition fo1 := compose S fo.

Definition fo2 := compose S fo1.
