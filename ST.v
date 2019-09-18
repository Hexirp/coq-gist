Require Import Coq.Init.Prelude Coq.Init.Specif Coq.Init.Nat.

(* 自然数をアドレスと考える。アドレス n に型が入っていなければ、値も入っていない。
   型が入っていれば値も必ず入っている。当然、値が入っていれば型も入っている。 *)
Definition STMapValue (f : nat -> option Type) (x : nat) : Type :=
    match f x with
    | Some t => t
    | None => unit
    end.

(* STMap に値がどれぐらい入っているかのカウンタの性質を記述する。例えばカウンタが 0 であれば、何も
   入っていない。 *)
Definition STMapProp (i : nat) (f : nat -> option Type) : Prop :=
    forall n, i <= n -> f n = None.

(* 関数を Map として見做す。これは STRef が参照する値を保存することが出来る。型レベルでも保存できる。 *)
Inductive STMap (s : Type) : Type :=
    | cSTMap :
        forall i : nat,
        forall f : nat -> option Type,

              STMapProp i f * (forall n : nat, STMapValue f n) ->

                  STMap s.

(* 内部では nat だが、そうではないように見える。 *)
Inductive STRef (s : Type) (a : Type) : Type :=
    | cSTRef : nat -> STRef s a.

(* s として STMap を取ることを想定している。 *)
Definition ST (s : Type) (a : Type) : Type := STMap s -> STMap s * a.

(* ### STMap と STRef は分解してはならない ### *)


(* 初期値。 *)
Definition emptySTMap (s : Type) : STMap s.
Proof.
  refine (cSTMap s 0 (fun _ => None) (pair _ _)).
  - intros n np.
    reflexivity.
  - refine (fun n => _).
    unfold STMapValue.
    exact tt.
Defined.

Definition newSTRef (s : Type) (a : Type) (x : a) : ST s (STRef s a).
Proof.
  refine (fun st => _).
  refine (match st with cSTMap _ st_i st_f st_pv => _ end).
  refine (match st_pv with pair st_p st_v => _ end).
  refine (let st_i' := st_i + 1 in _).
  refine (let st_f' := fun n => if eqb n st_i then Some a else st_f n in _).
  assert (st_p' : STMapProp st_i' st_f').
  - intros n np.
    unfold st_f'.
    assert (H : forall q p, q + 1 <= p -> eqb p q = false).
    + intros q p.
      induction p.
      * intros H.
        inversion H.
        Abort.
