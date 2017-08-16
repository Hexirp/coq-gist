Require Import Init.

Definition file : Type := nat.
Definition file_path : Type := nat.
Definition files : Type := list file.

Inductive sing (a : Type) : a -> Type :=
 | sig : forall (x : a), sing a x.

Definition resource (i : files) (j : files) (a : Type) : Type
 := sing files i -> (sing files j * a).

Definition open : forall (i : files) (n : file_path),
 resource i (cons n i) unit.
Proof.
 intros i n A.
 split.
 -
  apply sig.
 -
  apply tt.
Defined.

Definition close : forall (i : files) (n : file_path),
 resource (cons n i) i unit.
Proof.
 intros i n A.
 split.
 -
  apply sig.
 -
  apply tt.
Defined.

Definition run : forall (a : Type), resource nil nil a -> a.
Proof.
 intros a A.
 assert (s := sig files nil).
 apply A in s.
 destruct s as [_ av].
 apply av.
Defined.

Definition dive : forall (i : files) (j : files) (x : file) (a : Type),
 resource i j a -> resource (cons x i) (cons x j) a.
Proof.
 intros i j x a A B.
 split.
 -
  apply sig.
 -
  assert (s := sig files i).
  apply A in s.
  destruct s as [_ av].
  apply av.
Defined.