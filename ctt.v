Inductive paths {A : Type} (a : A) : A -> Type :=
| idpath : paths a a
.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} : x = y -> P x -> P y.
Proof.
 intros [].
 refine (fun x => x).
Defined.

Notation "p # x" := (transport _ p x) (right associativity, at level 65).

Definition apD
    {A : Type} {B : A -> Type} (f : forall a : A, B a)
    {x y : A} (p : x = y)
        : p # f x = f y.
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
 Variable c_seg : seg # c_st = c_en.

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

 Axiom II_ind_seg : c_seg = apD II_ind seg.
End II_elim.

Definition Path (A : Type) : Type := II -> A.

Definition idPath (A : Type) (a b : A) : Path A.
Proof.
 cbv.
 refine (@II_ind (fun _ => A) a b _).
 apply .