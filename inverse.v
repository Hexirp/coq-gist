Require Import Coq.Init.Prelude.

(** 点ごとに等しい *)
Definition pointwise_eq {A B : Type} (f g : A -> B) : Prop := forall x, f x = g x.

Notation "f == g" := (pointwise_eq f g) (at level 70, no associativity) : type_scope.

(** 恒等射 *)
Definition id {A : Type} : A -> A := fun x => x.

(** 射の合成 *)
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity)
 : function_scope.


(** [f] は単射である *)
Definition mono {A B : Type} (f : A -> B) : Prop
 := forall (Z : Type) (g₁ g₂ : Z -> A), f o g₁ == f o g₂ -> g₁ == g₂.

(** [f] に対して [g] は左逆射である *)
Definition left_inv_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := g o f == id.

(** [f] は左逆射を持つ *)
Definition left_inv {A B : Type} (f : A -> B) : Prop := ex (left_inv_rel f).

(** [h] は分裂単射である *)
Definition split_mono {A B : Type} (h : A -> B) : Prop := left_inv h /\ mono h.

(** [f] は全射である *)
Definition epi {A B : Type} (f : A -> B) : Prop
 := forall (C : Type) (g₁ g₂ : B -> C), g₁ o f == g₂ o f -> g₁ == g₂.

(** [f] に対して [g] は右逆射である *)
Definition right_inv_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := f o g == id.

(** [f] は右逆射を持つ *)
Definition right_inv {A B : Type} (f : A -> B) : Prop := ex (right_inv_rel f).

(** [f] は分裂全射である *)
Definition split_epi {A B : Type} (h : A -> B) : Prop := right_inv h /\ epi h.

(** [f] は全単射／双射である *)
Definition bi {A B : Type} (f : A -> B) : Prop := mono f /\ epi f.

(** [f] と [g] は逆射の関係である *)
Definition iso_rel {A B : Type} (f : A -> B) (g : B -> A) : Prop := g o f == id /\ f o g == id.

(** [f] は同型射である *)
Definition iso {A B : Type} (f : A -> B) : Prop := ex (iso_rel f).
