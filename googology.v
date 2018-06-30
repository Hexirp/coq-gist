Require Import Coq.Init.Prelude.

Definition u : Type -> Type := fun A => nat -> A.

Definition v : Type := nat.

Definition c {A : Type} : (A -> A) -> (nat -> A) -> (nat -> A) := fun f g x => f (g x).

Definition i {A : Type} : A -> (A -> A) -> (nat -> A) := fun x f => fix i n :=
 match n with
 | O => x
 | S np => f (i np)
 end
.

Definition t : Type := v.

Definition s : t -> t := S.

Definition o : t := O.

Definition f : t := o.

Definition f0 : t := s f.

Definition f00 :t := s f.

Definition t0 : Type := u t.

Definition s0 : t0 -> t0 := c s.

Definition o0 : t0 := i o s.

Definition f01 : t0 := o0.

Definition f010 : t0 := s0 f01.

Definition f0100 : t0 := s0 f010.

Definition t00 : Type := u t0.

Definition s00 : t00 -> t00 := c s0.

Definition o00 : t00 := i o0 s0.

Definition f0101 : t00 := o00.

Definition f01010 : t00 := s00 f0101.

Definition f010100 : t00 := s00 f01010.

