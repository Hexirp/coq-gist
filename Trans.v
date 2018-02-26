Require Import Init.Prelude.

Inductive path (A : Type) (a : A) : A -> Type :=
| idpath : path A a a
.

Inductive and A B : Type :=
| conj : A -> B -> and A B
.

Definition proj1 A B : and A B -> A := fun x => match x with conj _ _ x _ => x end.
Definition proj2 A B : and A B -> B := fun x => match x with conj _ _ _ x => x end.

Definition iff A B := and (A -> B) (B -> A).

Inductive False : Type :=
.

Inductive or A B : Type :=
| or_introl : A -> or A B
| or_intror : B -> or A B
.

Definition both A : or A A -> A
    := fun x => match x with or_introl _ _ x => x | or_intror _ _ x => x end.

Axiom ord : Type.
Axiom elem : ord -> ord -> Type.

Axiom extensionality
    : forall A B, (forall x, iff (elem x A) (elem x B)) -> path ord A B.

Axiom empty_set : forall P, (forall x, (forall y, elem y x -> False) -> P) -> P.

Axiom pairing : forall P A B,
        (forall x, (forall y, iff (elem y x) (or (path ord y A) (path ord y B))) -> P) -> P.

Axiom transitivity : forall A B C, elem A B -> elem B C -> elem A C.

Definition contradiction : False.
Proof.
 apply empty_set.
 intros e eH.
 apply pairing with e e.
 intros es esH.
 apply pairing with es es.
 intros ess essH.
 cut (path ord es e).
 -
  intros p.
  apply eH with e.
  refine (match p in path _ _ e' return elem e e' with idpath _ _ => _ end).
  cut (or (path ord e e) (path ord e e)).
  +
   apply proj2 with (elem e es -> or (path ord e e) (path ord e e)).
   fold (iff (elem e es) (or (path ord e e) (path ord e e))).
   apply esH.
  +
   apply or_introl.
   apply idpath.
 -
  cut (elem e ess).
  +
   intros H.
   cut (path ord e es).
   *
    intros p.
    destruct p.
    apply idpath.
   *
    apply both.
    cut (elem e ess).
    --
     apply proj1 with (or (path ord e es) (path ord e es) -> elem e ess).
     fold (iff (elem e ess) (or (path ord e es) (path ord e es))).
     apply essH.
    --
     apply H.
  +
   apply transitivity with es.
   *
    cut (or (path ord e e) (path ord e e)).
    --
     apply proj2 with (elem e es -> or (path ord e e) (path ord e e)).
     fold (iff (elem e es) (or (path ord e e) (path ord e e))).
     apply esH.
    --
     apply or_introl.
     apply idpath.
   *
    cut (or (path ord es es) (path ord es es)).
    --
     apply proj2 with (elem es ess -> or (path ord es es) (path ord es es)).
     fold (iff (elem es ess) (or (path ord es es) (path ord es es))).
     apply essH.
    --
     apply or_introl.
     apply idpath.
Defined.
