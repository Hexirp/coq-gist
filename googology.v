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

Definition c0 {A : nat -> Type} : (forall n, A n -> A n) -> (forall n, A n) -> (forall n, A n).
Proof.
 intros f g x.
 apply f.
 apply g.
Defined.

Definition i0 {A : nat -> Type} : A O -> (forall n, A n -> A (S n)) -> forall n, A n.
Proof.
 intros x f.
 fix i0 1.
 intros [ | np ].
 -
  apply x.
 -
  apply f.
  apply i0.
Defined.

Definition w : nat -> Type := i v u.

Definition t01 : Type := forall n, w n.

Definition r : forall n, w n -> w n.
Proof.
 apply (@i0 (fun n => w n -> w n)).
 -
  apply S.
 -
  intros n.
  change ((w n -> w n) -> (nat -> w n) -> (nat -> w n)).
  apply c.
Defined.

Definition s01 : t01 -> t01 := c0 r.

Definition o01 : t01.
Proof.
 change (forall n, w n).
 apply i0.
 -
  apply O.
 -
  intros n p.
  change (nat -> w n).
  apply i.
  +
   apply p.
  +
   apply r.
Defined.

Definition f011 : t01 := o01.

Definition f0110 : t01 := s01 f011.

Definition f01100 : t01 := s01 f0110.

Definition t010 : Type := u t01.

Definition s010 : t010 -> t010 := c s01.

Definition o010 : t010 := i o01 s01.

Definition f01101 : t010 := o010.

Definition f011010 : t010 := s010 f01101.

Definition f0110100 : t010 := s010 f011010.

Definition w0 : nat -> Type := i t01 u.

Definition t0101 : Type := forall n, w0 n.

Definition r0 : forall n, w0 n -> w0 n.
Proof.
 apply (@i0 (fun n => w0 n -> w0 n)).
 -
  apply s01.
 -
  intros n.
  change ((w0 n -> w0 n) -> (nat -> w0 n) -> (nat -> w0 n)).
  apply c.
Defined.

Definition s0101 : t0101 -> t0101 := c0 r0.

Definition o0101 : t0101.
Proof.
 change (forall n, w0 n).
 apply i0.
 -
  apply o01.
 -
  intros n p.
  change (nat -> w0 n).
  apply i.
  +
   apply p.
  +
   apply r0.
Defined.

Definition f011011 : t0101 := o0101.

Definition f0110110 : t0101 := s0101 f011011.

Definition w01 : nat -> Type.
Proof.
 apply i.
 -
  apply v.
 -
  intros p.
  apply (forall n, i p u n).
Defined.

Definition t011 : Type := forall n, w01 n.

Definition q {A : Type} : (A -> A) -> (forall m, i A u m -> i A u m).
Proof.
 intros f.
 apply (@i0 (fun m => i A u m -> i A u m)).
 -
  apply f.
 -
  intros n.
  change ((i A u n -> i A u n) -> (nat -> i A u n) -> (nat -> i A u n)).
  apply c.
Defined.

Definition r01 : forall n, w01 n -> w01 n.
Proof.
 apply (@i0 (fun n => w01 n -> w01 n)).
 -
  apply S.
 -
  intros n.
  change ((w01 n -> w01 n) -> (forall m, i (w01 n) u m) -> forall m, i (w01 n) u m).
  intros f g x.
  apply q.
  +
   apply f.
  +
   apply g.
Defined.

Definition s011 : t011 -> t011 := c0 r01.

Definition o011 : t011.
Proof.
 change (forall n, w01 n).
 apply i0.
 -
  apply O.
 -
  intros n p.
  change (forall m, i (w01 n) u m).
  apply i0.
  +
   apply p.
  +
   intros m p'.
   