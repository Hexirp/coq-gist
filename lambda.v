Inductive fin : nat -> Type :=
| fin_O : forall n, fin n
| fin_S : forall n, fin n -> fin (S n).

Inductive lambda : nat -> Type :=
| var : forall n, fin n -> lambda (S n)
| abs : forall n, lambda (S n) -> lambda n
| app : forall n, lambda n -> lambda n -> lambda n.

Definition closed := lambda 0.

Definition lambda_bet : forall n, lambda n -> lambda (S n).
Proof.
 apply (lambda_rect (fun n _ => lambda (S n))).
 -
  intros n x_var.
  apply var.
  revert n x_var.
  apply (fin_rect (fun n _ => fin (S n))).
  +
   intros n.
   apply fin_S.
   apply fin_O.
  +
   intros n _ x_var.
   apply fin_S.
   apply x_var.
 -
  intros n _ x_abs.
  apply abs.
  apply x_abs.
 -
  intros n _ x_app_1 _ x_app_2.
  apply app.
  +
   apply x_app_1.
  +
   apply x_app_2.
Defined.

Definition lambda_app : forall n, lambda n -> lambda n -> lambda n.
Proof.
 apply (lambda_rect (fun n _ => lambda n -> lambda n)).
 -
  intros n x_var y.
  apply app.
  +
   apply var.
   apply x_var.
  +
   apply y.
 -
  intros n _ y_abs y.
  Abort.