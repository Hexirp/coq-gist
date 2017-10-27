Inductive fin : nat -> Type :=
| fin_O : forall n, fin n
| fin_S : forall n, fin n -> fin (S n).

Inductive fin' (n : nat) : Type :=
| fin'_O : fin' n
| fin'_S : forall m, S m = n -> fin' m -> fin' n.

Definition fin_S' : forall n, fin' n -> fin' (S n).
Proof.
 intros n x.
 apply fin'_S with n.
 -
  apply eq_refl.
 -
  apply x.
Defined.

Definition fin_to : forall (n : nat), fin n -> fin' n.
Proof.
 apply fin_rect.
 -
  apply fin'_O.
 -
  intros n _ x.
  apply fin_S'.
  apply x.
Defined.

Definition fin'_to : forall (n : nat), fin' n -> fin n.
Proof.
 apply fin'_rect.
 -
  apply fin_O.
 -
  intros n m h _ x.
  apply eq_rect with (S m).
  +
   apply fin_S.
   apply x.
  +
   apply h.
Defined.

Inductive lambda : nat -> Type :=
| var : forall n, fin n -> lambda (S n)
| abs : forall n, lambda (S n) -> lambda n
| app : forall n, lambda n -> lambda n -> lambda n.

Inductive lambda' (n : nat) : Type :=
| var' : forall (m : nat), S m = n -> fin' m -> lambda' n
| abs' : lambda' (S n) -> lambda' n
| app' : lambda' n -> lambda' n -> lambda' n.

Definition var'' : forall n, fin' n -> lambda' (S n).
Proof.
 intros n x.
 apply var' with n.
 -
  apply eq_refl.
 -
  apply x.
Defined.

Definition lambda_to : forall n, lambda n -> lambda' n.
Proof.
 apply lambda_rect.
 -
  intros n x.
  apply var''.
  apply fin_to.
  apply x.
 -
  intros n _ x.
  apply abs'.
  apply x.
 -
  intros n _ x _ y.
  apply app'.
  +
   apply x.
  +
   apply y.
Defined.

Definition lambda'_to : forall n, lambda' n -> lambda n.
Proof.
 apply lambda'_rect.
 -
  intros n m h x.
  apply eq_rect with (S m).
  +
   apply var.
   apply fin'_to.
   apply x.
  +
   apply h.
 -
  intros n _ x.
  apply abs.
  apply x.
 -
  intros n _ x _ y.
  apply app.
  +
   apply x.
  +
   apply y.
Defined.

Definition beta_var : forall n, fin' n -> lambda' n -> lambda' n.
Proof.
 intros n fn x.
 case fn; clear fn.
 -
  apply x.
 -
  intros m h fm.
  apply eq_rect with (S m).
  +
   apply var''.
   apply fm.
  +
   apply h.
Defined.

Definition beta_abs_var : nat -> forall n, fin' n -> fin' (S n).
Proof.
 fix go 3.
 intros m n fn.
 case fn; clear fn.
 -
  apply fin'_O.
 -
  intros o h x.
  apply fin_S'.
  case m; clear m.
  +
   apply fin'_S with o.
   *
    apply h.
   *
     apply x.
  +
   intros m.
   apply eq_rect with (S o).
   *
    apply go.
    --
     apply m.
    --
     apply x.
   *
    apply h.
Defined.

Definition beta_abs (m : nat) : forall n, lambda' n -> lambda' (S n).
Proof.
 fix go 2.
 intros n x.
 case x; clear x.
 -
  intros o h fo.
  apply var' with (S o).
  +
   apply f_equal.
   apply h.
  +
   apply beta_abs_var.
   *
    apply m.
   *
    apply fo.
 -
  intros x.
  apply abs'.
  apply go.
  apply x.
 -
  intros x y.
  apply app'.
  +
   apply go.
   apply x.
  +
   apply go.
   apply x.
Defined.

Definition beta : forall n, lambda' (S n) -> lambda' n -> lambda' n.
Proof.
 fix go 2.
 intros n x y.
 case x; clear x.
 -
  intros m h fm.
  apply beta_var.
  +
   apply eq_rect with m.
   *
    apply fm.
   *
    apply eq_add_S.
    apply h.
  +
   apply y.
 -
  intros x.
  apply abs'.
  apply go.
  +
   apply x.
  +
   apply beta_abs.
   *
    apply n.
   *
    apply y.
 -
  intros x1 x2.
  apply app'.
  +
   apply go.
   *
    apply x1.
   *
    apply y.
  +
   apply go.
   *
    apply x2.
   *
    apply y.
Defined.

Notation "'λ' x" := (abs' _ x) (at level 75, right associativity).
Notation "x '$' y" := (app' _ x y) (at level 70, right associativity).

Eval compute in beta 0 (abs' 1 (var' 2 1 eq_refl (fin_O' 1))) (abs' 0 (var' 1 0 eq_refl (fin_O' 0))).