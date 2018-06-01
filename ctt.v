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

Definition dep_paths_fun {A B : Type} {x y : A} (p : x = y) (f : A -> B)
    : dep_paths (fun _ => B) p (f x) (f y).
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

Inductive Path (A : Type) (x y : A) : Type :=
| mkPath : forall f : II -> A, f st = x -> f en = y -> Path A x y
.

Definition idPath_internal (A : Type) (a : A) : II -> A.
Proof.
 apply II_rec with a a.
 apply dep_paths_const.
Defined.

Definition idPath (A : Type) (a : A) : Path A a a.
Proof.
 apply mkPath with (idPath_internal A a).
 -
  cbv.
  apply idpath.
 -
  cbv.
  apply idpath.
Defined.

Definition apPath {A : Type} {x y : A} : Path A x y -> II -> A.
Proof.
 intros p.
 destruct p as [pi pi_st pi_en].
 apply pi.
Defined.

Definition stPath (A : Type) (x y : A) (p : Path A x y) : A.
Proof.
 destruct p as [pi pi_st pi_en].
 apply (pi st).
Defined.

Definition enPath (A : Type) (x y : A) (p : Path A x y) : A.
Proof.
 destruct p as [pi pi_st pi_en].
 apply (pi en).
Defined.

Definition eq_stPath (A : Type) (x y : A) (p : Path A x y) : stPath A x y p = x.
Proof.
 destruct p as [pi pi_st pi_en].
 cbv.
 apply pi_st.
Defined.

Definition eq_enPath (A : Type) (x y : A) (p : Path A x y) : enPath A x y p = y.
Proof.
 destruct p as [pi pi_st pi_en].
 cbv.
 apply pi_en.
Defined.

Definition funext_internal {A B : Type} (f g : A -> B) (p : forall x : A, Path B (f x) (g x))
    : II -> (A -> B).
Proof.
 refine (
  II_rec (A -> B)
   (fun x => apPath (p x) st)
   (fun x => apPath (p x) en)
   _
 ).
 apply (dep_paths_fun seg (fun i : II => fun x : A => apPath (p x) i)).
Defined.

Definition funext {A B : Type} (f g : A -> B) (p : forall x : A, Path B (f x) (g x))
    : Path (A -> B) f g.
Proof.
 apply mkPath with (funext_internal f g p).
 -
  cbv.
