Inductive paths {A : Type} (a : A) : A -> Type :=
| idpath : paths a a
.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Definition dep_paths {A : Type} (P : A -> Type) {x y : A} : x = y -> P x -> P y -> Type.
Proof.
 intros [].
 apply paths.
Defined.

Definition dep_paths_const {A B : Type} {x y : A} (p : x = y) (z : B)
    : dep_paths (fun _ => B) p z z.
Proof.
 destruct p as [].
 cbv.
 apply idpath.
Defined.

Definition apD {A : Type} (P : A -> Type) (f : forall a : A, P a) {x y : A} (p : x = y)
    : dep_paths P p (f x) (f y).
Proof.
 destruct p as [].
 cbv.
 apply idpath.
Defined.

Private Inductive II : Type :=
| st : II
| en : II
.

Axiom seg : st = en.

Section II_elim.
 Variable P : II -> Type.
 Variable c_st : P st.
 Variable c_en : P en.
 Variable c_seg : dep_paths P seg c_st c_en.

 Definition II_ind : forall x : II, P x.
 Proof.
  refine (fun x => match x return _ -> P x with | st => fun p => _ | en => fun p => _ end _).
  -
   apply c_st.
  -
   apply c_en.
  -
   apply c_seg.
 Defined.

 Definition II_ind_st : c_st = II_ind st.
 Proof.
  cbv.
  apply idpath.
 Defined.

 Definition II_ind_en : c_en = II_ind en.
 Proof.
  cbv.
  apply idpath.
 Defined.

 Axiom II_ind_seg : c_seg = apD P II_ind seg.
End II_elim.

Definition II_rec (A : Type) := II_ind (fun _ => A).

Definition Path (A : Type) (x y : A) : Type.
Proof.
 refine (forall P : Type, (forall f : II -> A, f st = x -> f en = y -> P) -> P).
Defined.

Definition idPath (A : Type) (a : A) : Path A a a.
Proof.
 cbv.
 intros P c_Path.
 refine (let f := II_rec A a a (dep_paths_const seg a) : II -> A in _).
 apply c_Path with f.
 -
  cbv.
  apply idpath.
 -
  cbv.
  apply idpath.
Defined.

Definition stPath (A : Type) (x y : A) (p : Path A x y) : A.
Proof.
 apply p.
 intros f f_st f_en.
 apply (f st).
Defined.

Definition enPath (A : Type) (x y : A) (p : Path A x y) : A.
Proof.
 apply p.
 intros f f_st f_en.
 apply (f en).
Defined.

Definition eq_stPath (A : Type) (x y : A) (p : Path A x y) : stPath A x y p = x.
Proof.
Admitted.

Definition eq_enPath (A : Type) (x y : A) (p : Path A x y) : enPath A x y p = y.
Proof.
Admitted.

Definition funext {A B : Type} (f g : A -> B) (p : forall x : A, Path B (f x) (g x))
    : Path (A -> B) f g.
Proof.
 intros P c_Path.
 assert (pi : II -> A -> B).
 -
  refine (II_rec (A -> B) (fun x : A => stPath  _ _).
  