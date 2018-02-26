Require Import Init.

Inductive path (A : Type) (a : A) : A -> Type :=
| idpath : path A a a
.

Definition bool_idempotence (f : bool -> bool) (x : bool) : path bool (f (f (f x))) (f x).
Proof.
 refine (match x with true => _ | false => _ end); clear x.
 -
  refine (_ (idpath bool (f true))).
  refine (
   match f true as f' return path bool f' (f true) -> path bool (f (f f')) f' with
   | true => _
   | false => _
   end
  ).
  +
   refine (fun p => _).
   refine (match p with idpath _ _ => _ end).
   refine (match p with idpath _ _ => _ end).
   refine (idpath bool true).
  +
   refine (fun p => _).
   refine (_ (idpath bool (f false))).
   refine (
    match f false as f' return path bool f' (f false) -> path bool (f f') false with
    | true => _
    | false => _
    end
   ).
   *
    refine (fun q => _).
    refine (match p with idpath _ _ => _ end).
    refine (idpath bool false).
   *
    refine (fun q => _).
    refine (match q with idpath _ _ => _ end).
    refine (idpath bool false).
 -
  refine (_ (idpath bool (f false))).
  refine (
   match f false as f' return path bool f' (f false) -> path bool (f (f f')) f' with
   | true => _
   | false => _
   end
  ).
  +
   refine (fun p => _).
   refine (_ (idpath bool (f true))).
   refine (
    match f true as f' return path bool f' (f true) -> path bool (f f') true with
    | true => _
    | false => _
    end
   ).
   *
    refine (fun q => _).
    refine (match q with idpath _ _ => _ end).
    refine (idpath bool true).
   *
    refine (fun q => _).
    refine (match p with idpath _ _ => _ end).
    refine (idpath bool true).
  +
   refine (fun p => _).
   refine (match p with idpath _ _ => _ end).
   refine (match p with idpath _ _ => _ end).
   refine (idpath bool false).
Defined.
