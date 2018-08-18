Require Import Coq.Init.Prelude.

Definition pointwise_eq {A B : Type} (f g : A -> B) : Prop := forall x, f x = g x.

Notation "f == g" := (pointwise_eq f g) (at level 70, no associativity) : type_scope.

Definition id {A : Type} : A -> A := fun x => x.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity)
 : function_scope.

Definition inv_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := g o f == id.

Definition mono {A B : Type} (f : A -> B) : Prop
 := forall (Z : Type) (g₁ g₂ : Z -> A), f o g₁ == f o g₂ -> g₁ == g₂.

Definition left_inv_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := inv_rel f g.

Definition left_inv {A B : Type} (f : A -> B) : Prop := ex (left_inv_rel f).

Definition split_mono {A B : Type} (h : A -> B) : Prop := left_inv h /\ mono h.

Definition epi {A B : Type} (f : A -> B) : Prop
 := forall (C : Type) (g₁ g₂ : B -> C), g₁ o f == g₂ o f -> g₁ == g₂.

Definition right_inv_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := inv_rel g f.

Definition right_inv {A B : Type} (f : A -> B) : Prop := ex (right_inv_rel f).

Definition split_epi {A B : Type} (h : A -> B) : Prop := right_inv h /\ epi h.
