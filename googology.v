Require Import Init.

(** 基礎原理

0 1 2 3 4
1 2 3 4 5
2 3 4 5 6
3 4 5 6 7
4 5 6 7 8

0 2 4 6 8
1 3 5 7 9
2 4 6 8
3 5 7 9
4 6 8

0 3 6 9
1 4 7
2 5 8
3 6 9
4 7

0 4 8
1 5 9
2 6
3 7
4 8

*)
Fixpoint base1 (m n : nat) {struct m} :=
 match m with
 | O => n
 | S mp => S (base1 mp n)
 end
.

(** 対角化 *)
Definition sq (f : nat -> nat -> nat) (m n : nat) := f m (m + n).

Fixpoint base2 (m n o : nat) {struct m} :=
 match m with
 | O => base1 n o
 | S mp => sq (base2 mp) n o
 end
.

(** 三次元への拡張

0 1 2 3  0 2 4 6  0 3 6 9   0 4 8 12
1 2 3 4  1 3 5 7  1 4 7 10  1 5 9 13
2 3 4 5  2 4 6 8  2 5 8 11  2 6 10 14
3 4 5 6  3 5 7 9  3 6 9 12  3 7 11 15

f m (m + n) (m + n + o)

0 2 4 6  3 6 9 12   8 12 16 20   15 20 25 30
1 3 5 7  4 7 10 13  9 13 17 21   16 21 26 31
2 4 6 8  5 8 11 14  10 14 18 22  17 22 27 32
3 5 7 9  6 9 12 15  11 15 19 23  18 23 28 33

0 3 6 9   7 11 15 19   18 23 28 33  33 39 45 51
1 4 7 10  8 12 16 20   19 24 29 34  34 40 46 52
2 5 8 11  9 13 17 21   20 25 30 35  35 41 47 53
3 6 9 12  10 14 18 22  21 26 31 36  36 42 48 54

f m (m + n) (m + o)

0 1 2 3  3 5 7 9    8 11 14 17
1 2 3 4  4 6 8 9    9 12 15 18
2 3 4 5  5 7 9 10   10 13 16 19
3 4 5 6  6 8 10 12  11 14 17 20

f m (m + n) o

0 1 2 3  2 4 6 8   6 9 12 15
1 2 3 4  3 5 7 9   7 10 13 16
2 3 4 5  4 6 8 10  8 11 14 17
3 4 5 6  5 7 9 11  9 12 15 18

f m (m + n) (n + o)

0 1 2 3  2 5 8 11   6 10 14 18
1 2 3 4  3 6 9 12   7 11 15 19
2 3 4 5  4 7 10 13  8 12 16 20
3 4 5 6  5 8 11 14  9 13 17 21

match m with
| O => f m n o
| S mp => f m (mp + n) (S o)
end

0 1 2 3  1 3 5 7   4 7 10 13   9 13 17 21
1 2 3 4  2 4 6 8   5 8 11 16   10 14 18 22
2 3 4 5  3 5 7 9   6 9 12 17   11 15 19 23
3 4 5 6  4 6 8 10  7 10 13 18  12 16 20 24

*)
Definition sq2 (f : nat -> nat -> nat -> nat) (m n o : nat) := f m (m + n) (m + n + o).

Fixpoint base3 (m n o p : nat) {struct m} :=
 match m with
 | O => base2 n o p
 | S mp => sq2 (base3 mp) n o p
 end
.

Definition sq3 (f : nat -> nat -> nat -> nat -> nat) (m n o p : nat)
    := f m (m + n) (m + n + o) (m + n + o + p).

Fixpoint base4 (m n o p q : nat) {struct m} :=
 match m with
 | O => base3 n o p q
 | S mp => sq3 (base4 mp) n o p q
 end
.

Inductive nats : nat -> Type :=
| No : nats O
| Ns : forall n, nat -> nats n -> nats (S n)
.

Fixpoint update (m : nat) (n : nats m) {struct n} :=
 match n in nats m' return m = m' -> nats m' with
 | No => fun _ => No
 | Ns mp nn np => fun nH => _
 end (eq_refl m)
.

Definition spn (f : forall m, nats m -> nat) (m : nat) (n : nats m)
    := f m (update m n)

Require Import List.

Definition l := cons 0 (cons 1 (cons 2 (cons 3 nil))).
Definition view (f : nat -> nat -> nat) := map (fun f => map f l) (map f l).

Eval cbv in map (fun n => base4 n n n n n) l.
(**

4x4の表が4x3の表に並べられている。横x縦であり、大きな方の座標を(n, o)として小さな方の座標を(q, p)とする。
それらが縦に並べられ、mの変化を表す。

0 1 2 3  0 2 4 6  0 3 6 9   0 4 8 12
1 2 3 4  1 3 5 7  1 4 7 10  1 5 9 13
2 3 4 5  2 4 6 8  2 5 8 11  2 6 10 14
3 4 5 6  3 5 7 9  3 6 9 12  3 7 11 15

0 2 4 6  3 6 9 12   8 12 16 20   15 20 25 30
1 3 5 7  4 7 10 13  9 13 17 21   16 21 26 31
2 4 6 8  5 8 11 14  10 14 18 22  17 22 27 32
3 5 7 9  6 9 12 15  11 15 19 23  18 23 28 33

0 3 6 9   7 11 15 19   18 23 28 33  33 39 45 51
1 4 7 10  8 12 16 20   19 24 29 34  34 40 46 52
2 5 8 11  9 13 17 21   20 25 30 35  35 41 47 53
3 6 9 12  10 14 18 22  21 26 31 36  36 42 48 54


0 2 4 6  3 6 9 12   8 12 16 20   15 20 25 30
1 3 5 7  4 7 10 13  9 13 17 21   16 21 26 31
2 4 6 8  5 8 11 14  10 14 18 22  17 22 27 32
3 5 7 9  6 9 12 15  11 15 19 23  18 23 28 33

7 11 15 19   18 23 28 33  33 39 45 51  52 59 66 73
8 12 16 20   19 24 29 34  34 40 46 52  53 60 67 74
9 13 17 21   20 15 30 35  35 41 47 53  54 61 68 75
10 14 18 22  21 26 31 36  36 42 48 54  55 62 69 76

30 36 42 48  54 61 68 75  84 92 100 108  120 129 138 147
31 37 43 49  55 62 69 76  85 93 101 109  121 130 139 148
32 38 44 50  56 63 69 76  86 94 102 110  122 131 140 149
33 39 45 51  56 63 70 77  87 95 103 111  123 132 141 150

*)
