Require Import Coq.Init.Prelude.

Definition f0 := O.

Definition f00 := S O.

Definition f00 := S (S 0).

Definition f01 := fix f01 n := match n with O => O | S np => S np.

Definition f010 := fun n => S (f01 n).

Definition f0100 := fun n => S (f010 n).
