Require Import Init.

(*

直観主義命題論理と古典命題論理の任意の式が常に正しいか判定できる。
それを実装したプログラムがある。ある人がパースの公理と排中律の関係を知りたくてこのような式を与えた。

(P \/ ~ P) -> (((P -> Q) -> P) -> P)

結果は「正しい」となった。次に逆であるこの式を与えた。

(((P -> Q) -> P) -> P) -> (P \/ ~ P)

すると結果は「誤っている」となった。なぜか？

*)

Goal (forall p q : Prop, ((p -> q) -> p) -> p) -> (forall a : Prop, a \/ ~ a).
Proof.
 intros peirce a.
 apply peirce with False.
 intros H.
 right.
 intros A.
 apply H.
 left.
 apply A.
Defined peirce_to_excluded_middle.

Goal (forall a : Prop, a \/ ~ a) -> (forall p q : Prop, ((p -> q) -> p) -> p).
Proof.
 intros exmi p q H.
 destruct (exmi p) as [P | Pn].
 -
  apply P.
 -
  apply H.
  intros P.
  exfalso.
  apply Pn.
  apply P.
Defined excluded_middle_to_peirce.

(*

誤りは上のように全称量化が必要なこと。最初の時はなぜ正しかったのか？

excluded_middle_to_peirceの証明を見ると引数exmiにpを渡している。
exmi p : p \/ ~ pとなり、一般のexmiがなくてもこれだけあればよいことになる。
こうして置き換えたものはちょうど最初に与えた式に一致する。

*)

(*

Thank

https://github.com/suharahiromichi/coq/blob/2aedd465c255a6aac1466258041d4930211460d9/coq_classical.v

.

*)
