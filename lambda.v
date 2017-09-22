Inductive fin : nat -> Type :=
| fin_O : forall n, fin n
| fin_S : forall n, fin n -> fin (S n).

Inductive lambda : nat -> Type :=
| var : forall n, fin n -> lambda (S n)
| abs : forall n, lambda (S n) -> lambda n
| app : forall n, lambda n -> lambda n -> lambda n.

Definition lambda_b_s_case_var : forall n, fin n -> lambda n -> lambda n.
Proof.
 intros n f y.
 induction f.
 -
  apply y.
 -
  apply var.
  apply f.
Defined.

Definition lambda_beta_simplfy : forall n, lambda (S n) -> lambda n -> lambda n.
Proof.
 intros n x y.
 induction x.
 -
  apply lambda_b_s_case_var.
 -
  induction y.
  +
   
 intros m h x y.
 revert m x h y.
 apply (lambda_rect (fun o _ => o = S n -> lambda n -> lambda n)).
 -
  intros m x_var h.
  replace n with m.
  +
   clear n h.
   revert m x_var.
   apply (fin_rect (fun m _ => lambda m -> lambda m)).
   *
    intros n y.
    apply y.
   *
    intros n x_var _ _.
    apply var.
    apply x_var.
  +
   apply eq_add_S.
   apply h.
 -
  Abort.

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