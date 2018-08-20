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


(** [f] が左逆射を持つならば [f] は単射である *)
Definition mono_left_inv {A B : Type} (f : A -> B) : left_inv f -> mono f.
Proof.
 intros P.
 unfold left_inv in P.
 destruct P as [ g P ].
 unfold left_inv_rel in P.
 unfold mono.
 intros Z g₁ g₂ Q.
 unfold pointwise_eq.
 intros x.
 change (id (g₁ x) = id (g₂ x)).
 unfold pointwise_eq in P.
 rewrite <- P with (g₁ x).
 rewrite <- P with (g₂ x).
 unfold compose.
 apply f_equal.
 unfold pointwise_eq in Q.
 unfold compose in Q.
 apply Q.
Defined.

(** [f] が右逆射を持つならば [f] は全射である *)
Definition epi_right_inv {A B : Type} (f : A -> B) : right_inv f -> epi f.
Proof.
 intros P.
 unfold right_inv in P.
 destruct P as [ g P ].
 unfold right_inv_rel in P.
 unfold epi.
 intros C g₁ g₂ Q.
 unfold pointwise_eq.
 intros x.
 change (g₁ (id x) = g₂ (id x)).
 unfold pointwise_eq in P.
 rewrite <- P with x.
 unfold compose.
 unfold pointwise_eq in Q.
 unfold compose in Q.
 apply Q.
Defined.

(** [f] が同型射であるのならば [f] は左逆射を持ち、右逆射を持つ *)
Definition left_right_inv_iso {A B : Type} (f : A -> B) : iso f -> left_inv f /\ right_inv f.
Proof.
 intros P.
 unfold iso in P.
 destruct P as [ g P ].
 unfold iso_rel in P.
 destruct P as [ left_P right_P ].
 split.
 -
  unfold left_inv.
  exists g.
  unfold left_inv_rel.
  apply left_P.
 -
  unfold right_inv.
  exists g.
  unfold right_inv_rel.
  apply right_P.
Defined.

(** [f] が同型射であるのならば [f] は双射である *)
Definition bi_iso {A B : Type} (f : A -> B) : iso f -> bi f.
Proof.
 intros P.
 apply left_right_inv_iso in P.
 destruct P as [ left_P right_P ].
 unfold bi.
 split.
 -
  apply mono_left_inv.
  apply left_P.
 -
  apply epi_right_inv.
  apply right_P.
Defined.
