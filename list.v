Inductive List (a : Type) : Type := Nil : List a | Cons : a -> List a -> List a.

Arguments Nil {a}.
Arguments Cons {a} x xs.

Definition pointwise_eq {a : Type} {p : a -> Type} (f g : forall x : a, p x) : Prop :=
 forall x : a, f x = g x.

Notation "f == g" := (pointwise_eq f g) (at level 70, no associativity) : type_scope.

Definition id {A : Type} (x : A) : A := x.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f 'o' g" := (compose f g) (at level 40, left associativity) : type_scope.

Fixpoint fmap {a b : Type} (f : a -> b) (x : List a) : List b :=
 match x with Nil => Nil | Cons x xs => Cons (f x) (fmap f xs) end.

Module Type Functor.
 Parameter f : Type -> Type.
 Parameter fmap : forall a b, (a -> b) -> f a -> f b.
 Arguments fmap {a b} f x.

 Axiom functor_law_1 : forall a, @id (f a) == fmap (@id a).
 Axiom functor_law_2 : forall a b c, forall (f_ : b -> c) (g_ : a -> b),
  fmap f_ o fmap g_ == fmap (f_ o g_).
End Functor.

Module Functor_List <: Functor.
 Definition f := List.
 Definition fmap := @fmap.
 Arguments fmap {a b} f x.

 Theorem functor_law_1 : forall a, @id (f a) == fmap (@id a).
 Proof.
  intros a.
  intros x.
  induction x.
  -
   apply eq_refl.
  -
   simpl.
   case IHx.
   apply eq_refl.
 Qed.

 Theorem functor_law_2 : forall a b c, forall (f_ : b -> c) (g_ : a -> b),
  fmap f_ o fmap g_ == fmap (f_ o g_).
 Proof.
  intros a b c f_ g_.
  intros x.
  induction x.
  -
   apply eq_refl.
  -
   simpl.
   case IHx.
   apply eq_refl.
 Qed.
End Functor_List.

Module Type Monad (Functor_Instance : Functor).
 Export Functor_Instance.

 Parameter pure : forall a, a -> f a.
 Parameter join : forall a, f (f a) -> f a.
 Arguments pure {a} x.
 Arguments join {a} x.

 Axiom monad_law_1 : forall a, @id (f a) == join o pure.
 Axiom monad_law_2 : forall a, @id (f a) == join o fmap pure.
 Axiom monad_law_3 : forall a, @join (f a) o join == join o fmap join.
End Monad.

Module Free_Lunch (Monad_Instance : Monad Functor_List).
 Export Monad_Instance.

 Theorem join_nil_to_nil : ~ ~ forall a, @Nil a = join Nil.
 Proof.
  intros ng.
  assert (forall a, exists x xs, @Cons a x xs = join Nil).
  -
   intros a.
   generalize (ng a).
   destruct (join Nil).
   +
    
