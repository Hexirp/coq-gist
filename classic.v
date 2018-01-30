Require Import Init.

Goal (forall p q, ((p -> q) -> p) -> p) -> (forall a, a \/ ~ a).
Proof.
 intros peirce a.
 apply peirce with False.
 intros H.
 right.
 intros an.
 apply H.
 left.
 apply an.
Defined  peirce_to_excluded_middle.