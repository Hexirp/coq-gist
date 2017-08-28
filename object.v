Require Import Init.

Axiom object_wrong : (Type -> Type) -> (Type -> Type) -> Type.
Axiom mkobj_wrong : forall f g,
 (forall x, f x -> g (prod x (object_wrong f g))) -> object_wrong f g.
Axiom object_wrong_rect : forall f g (P : object_wrong f g -> Type),
 (forall p, P (mkobj_wrong f g p)) -> forall o, P o.
Axiom object_wrong_ind : forall f g (P : object_wrong f g -> Prop),
 (forall p, P (mkobj_wrong f g p)) -> forall o, P o.
Axiom object_wrong_rec : forall f g (P : object_wrong f g -> Set),
 (forall p, P (mkobj_wrong f g p)) -> forall o, P o.

Definition run_object_wrong (f g : Type -> Type)
 : object_wrong f g -> forall x, f x -> g (prod x (object_wrong f g)).
Proof.
 intros o x xf.
 revert o.
 apply object_wrong_rect.
 intros p.
 apply p.
 apply xf.
Save.

Definition wrong (f g : Type -> Type) (x : Type)
 : (forall a, g a -> a -> x) -> x -> f x -> object_wrong f g -> x.
Proof.
 intros get xv xf o.
 apply get with (prod x (object_wrong f g)).
 -
  apply (run_object_wrong f g).
  +
   apply o.
  +
   apply xf.
 -
  split.
  +
   apply xv.
  +
   apply o.
Save.

Print wrong.

Inductive object (f g : Type -> Type) : Type :=
 | mkobj : (forall x, f x -> prod x (object f g)) -> object f g.

Check object_rect.