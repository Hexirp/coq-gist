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
| O => f m

*)
Definition sq2 (f : nat -> nat -> nat -> nat) (m n o : nat) := f m (m + n) (m + n + o).

Fixpoint base3 (m n o p : nat) {struct m} :=
 match m with
 | O => base2 n o p
 | S mp => sq2 (base3 mp) n o p
 end
.

Eval cbv in base3 2 4 3 0.