Require Import Coq.Init.Prelude Coq.Init.Specif.

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
    forall n, n < i -> f n = None.

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


Definition emptySTMap (s : Type) : STMap s.
Proof.
 refine (cSTMap s 0 (fun _ => None) (pair _ _)).
 - Abort.
