Require Import Coq.Init.Prelude.


Class FGH (A : Type) := { fgh : nat -> nat } .

Instance FGH_Empty : FGH Empty := { fgh := S } .
