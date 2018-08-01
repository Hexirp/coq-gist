Inductive List (a : Type) : Type := Nil : List a | Cons : a -> List a -> List a.

Arguments Nil {a}.
Arguments Cons {a} x xs.

Definition pointwise_eq {a : Type} {p : a -> Type} (f g : forall x : a, p x) : Prop :=
 forall x : a, f x = g x.

Notation "f == g" := (pointwise_eq f g) (at level 70, no associativity) : type_scope.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f 'o' g" := (compose f g) (at level 40, left associativity) : type_scope.

Fixpoint fmap {a b : Type} (f : a -> b) (x : List a) : List b :=
 match x with Nil => Nil | Cons x xs => Cons (f x) (fmap f xs) end.
