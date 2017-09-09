Inductive fin : nat -> Type :=
| fin_O : forall n, fin n
| fin_S : forall n, fin n -> fin (S n).

Inductive lambda : nat -> Type :=
| var : forall n, fin n -> lambda (S n)
| abs : forall n, lambda (S n) -> lambda n
| app : forall n, lambda n -> lambda n -> lambda n.

Definition closed := lambda 0.