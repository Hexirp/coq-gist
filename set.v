Require Import Init Nat.

(*
Inductive listp A : (A -> listp A -> Prop) -> Type :=
| nlp : forall P, listp A P
| cnp : forall P (x : A) (xs : list A), P x xs -> listp A P.
*)

Definition uniques : list nat -> bool.
Proof.
 intros x.
 induction x.
 - (* nil *)
  apply true.
 - (* cons *)
Abort.