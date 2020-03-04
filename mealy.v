Require Import Prelude.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive Duple@{i k j} (a : Type@{i}) (b : Type@{k}) : Type@{j} :=
  mkDuple : a -> b -> Duple a b.

CoInductive Mealy@{i k j} (a : Type@{i}) (b : Type@{k}) : Type@{j} :=
  mkMealy : (a -> Duple@{k j j} b (Mealy a b)) -> Mealy a b.

Definition deMealy@{i k j} (a : Type@{i}) (b : Type@{k}) (x : Mealy@{i k j} a b)
  : a -> Duple@{k j j} b (Mealy@{i k j} a b)
  := match x with mkMealy _ _ x' => x' end.

Definition id_Mealy@{i k} (a : Type@{i}) : Mealy@{i i k} a a :=
  cofix go : Mealy@{i i k} a a :=
    mkMealy a a (fun x_a => mkDuple@{i k k} a (Mealy@{i i k} a a) x_a go).
