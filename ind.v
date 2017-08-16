Require Import Init Basics.

Extraction Language Haskell.

Inductive exist (p : Type -> Type) : Type :=
 | exist_mk : forall x, p x -> exist p.

Definition run_exist p r : (forall x, p x -> r) -> exist p -> r.
Proof.
 intros f.
 intros x.
 destruct x as [X x].
 apply (f X).
 apply x.
Defined.

Print run_exist.

Inductive cat (k : Type -> Type -> Type) (a b : Type) : Type :=
 | leaf : k a b -> cat k a b
 | tree : (exist (fun x => cat k a x * cat k x b)%type) -> cat k a b.

Definition run_cat k a b r : (k a b -> r) -> ((exist (fun x => cat k a x * cat k x b)%type) -> r) -> cat k a b -> r.
Proof.
 intros emp rec.
 intros x.
 destruct x as [lea | tre].
 -
  apply emp.
  apply lea.
 -
  apply rec.
  apply tre.
Save.

Definition run_cat' k a b r : (k a b -> r) -> (forall x, (cat k a x * cat k x b)%type -> r) -> cat k a b -> r.
Proof.
 intros emp rec.
 intros x.
 apply (run_cat k a b r).
 -
  apply emp.
 -
  apply run_exist.
  apply rec.
 -
  apply x.
Save.