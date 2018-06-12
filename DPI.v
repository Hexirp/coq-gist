(* https://x80.org/rhino-hott/ でチェックした *)

From HoTT Require Import Basics.
From HoTT Require Import Types.
From HoTT Require Import HProp TruncType.

Context `{Univalence}.

Definition dec_paths_ishset := forall A : Type, IsHSet A -> DecidablePaths A.

Axiom DPI : dec_paths_ishset.

Definition dec_paths_hprop_unit : forall P : hProp, Decidable (P = Unit_hp).
Proof.
 intros P.
 pose (DP_hprop := DPI hProp isset_hProp).
 apply dec_paths.
Qed.

Definition lem : forall P : Type, IsHProp P -> P + ~P.
Proof.
 intros P ishprop_P.
 pose (P_hp := BuildhProp P).
 pose (dec_P := dec_paths_hprop_unit P_hp).
 destruct (dec (P_hp = Unit_hp)) as [ l | r ].
 -
  apply inl.
  unfold P_hp, Unit_hp in l.
  pose (l_type := ap trunctype_type l).
  unfold trunctype_type in l_type.
  rewrite l_type.
  apply tt.
 -
  apply inr.
  intros p.
  apply r.
  apply path_iff_hprop_uncurried.
  split.
  +
   intros ?; apply tt.
  +
   intros ?; apply p.
Qed.
