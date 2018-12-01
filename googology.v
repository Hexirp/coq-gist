Require Import Coq.Init.Prelude.


Class FGH (A : Type) := { fgh : nat -> nat } .

Instance FGH_Empty : FGH Empty_set := { fgh := S } .

Instance FGH_Succ {A : Type} : FGH (sum unit A) := { fgh := S } .
