Module Main.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Module Path.

Inductive T (A : Type) (x : A) : A -> Type
  :=
    id : T A x x
.

End Path.

Module Dependent_Function.

Inductive T_
  (A : Type)
  (A_ : A -> A -> Type)
  (B : A -> Type)
  (B_ : forall x : A, forall y : A, A_ x y -> B x -> B y -> Type)
  (f : forall x : A, B x)
  (g : forall x : A, B x)
  : Type
  :=
    value_
      :
          (forall x : A, forall y : A, forall p : A_ x y, B_ x y p (f x) (g y))
        ->
          T_ A A_ B B_ f g
.

Inductive T__
  (A : Type)
  (A_ : A -> A -> Type)
  (A__ : forall x : A, forall y : A, A_ x y -> A_ x y -> Type)
  (B : A -> Type)
  (B_ : forall x : A, forall y : A, A_ x y -> B x -> B y -> Type)
  (
    B__
      :
        forall
          x : A
        ,
        forall
          y : A
        ,
        forall
          p : A_ x y
        ,
        forall
          q : A_ x y
        ,
          A__ x y p q
        ->
        forall
          i : B x
        ,
        forall
          j : B y
        ,
          B_ x y p i j
        ->
          B_ x y q i j
        ->
          Type
  )
  (f : forall x : A, B x)
  (g : forall x : A, B x)
  (x : T_ A A_ B B_ f g)
  (y : T_ A A_ B B_ f g)
  : Type
  :=
    value__
      :
        forall
          x_v : forall x : A, forall y : A, forall p : A_ x y, B_ x y p (f x) (g y)
        ,
        forall
          y_v : forall x : A, forall y : A, forall p : A_ x y, B_ x y p (f x) (g y)
        ,
          (
            forall
              x : A
            ,
            forall
              y : A
            ,
            forall
              p : A_ x y
            ,
            forall
              q : A_ x y
            ,
            forall
              r : A__ x y p q
            ,
              B__ x y p q r (f x) (g y) (x_v x y p) (y_v x y q)
          )
        ->
          T__ A A_ A__ B B_ B__ f g x y
.

End Dependent_Function.

Module Function.

Inductive T_
  (A : Type)
  (A_ : A -> A -> Type)
  (B : Type)
  (B_ : B -> B -> Type)
  (f : A -> B)
  (g : A -> B)
  : Type
  :=
    value_
      :
          (forall x : A, forall y : A, A_ x y -> B_ (f x) (g y))
        ->
          T_ A A_ B B_ f g
.

Inductive T__
  (A : Type)
  (A_ : A -> A -> Type)
  (A__ : forall x : A, forall y : A, A_ x y -> A_ x y -> Type)
  (B : Type)
  (B_ : B -> B -> Type)
  (B__ : forall x : B, forall y : B, B_ x y -> B_ x y -> Type)
  (f : A -> B)
  (g : A -> B)
  (x : T_ A A_ B B_ f g)
  (y : T_ A A_ B B_ f g)
  : Type
  :=
    value__
      :
        forall
          x_v : forall x : A, forall y : A, A_ x y -> B_ (f x) (g y)
        ,
        forall
          y_v : forall x : A, forall y : A, A_ x y -> B_ (f x) (g y)
        ,
          (
            forall
              x : A
            ,
            forall
              y : A
            ,
            forall
              p : A_ x y
            ,
            forall
              q : A_ x y
            ,
              A__ x y p q
            ->
              B__ (f x) (g y) (x_v x y p) (y_v x y q)
          )
        ->
          Path.T (T_ A A_ B B_ f g) x (value_ A A_ B B_ f g x_v)
        ->
          Path.T (T_ A A_ B B_ f g) x (value_ A A_ B B_ f g y_v)
        ->
          T__ A A_ A__ B B_ B__ f g x y
.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C
  := fun x : A => f (g x).

Definition id {A : Type} : A -> A := fun x : A => x.

End Function.

Module TYPE.

Inductive T_
  (R : forall A : Type, A -> A -> Type)
  (
    R_id
      :
        forall
          A : Type
        ,
        forall
          B : Type
        ,
        forall
          f : A -> B
        ,
          Function.T_ A (R A) B (R B) f f
  )
  (
    R_compose
      :
        forall
          A : Type
        ,
        forall
          B : Type
        ,
        forall
          C : Type
        ,
        forall
          f0 : B -> C
        ,
        forall
          f1 : B -> C
        ,
        forall
          g0 : A -> B
        ,
        forall
          g1 : A -> B
        ,
          Function.T_ B (R B) C (R C) f0 f1
        ->
          Function.T_ A (R A) B (R B) g0 g1
        ->
          Function.T_ A (R A) C (R C) (Function.compose f0 g0) (Function.compose f1 g1)
  )
  (A : Type)
  (B : Type)
  : Type
  :=
    value_
      :
        forall
          f : A -> B
        ,
        forall 
          g : B -> A
        ,
        forall
          r
            :
              Function.T_ B (R B) B (R B) (Function.compose f g) Function.id
        ,
        forall
          s
            :
              Function.T_ A (R A) A (R A) (Function.compose g f) Function.id
        ,
          Function.T__
            A
            (R A)
            (fun x : A => fun y : A => R (R A x y))
            B
            (R B)
            (fun x : B => fun y : B => R (R B x y))
            (Function.compose f (Function.compose g f))
            f
            (R_compose A B B (Function.compose f g) Function.id f f r (R_id A B f))
            (R_compose A A B f f (Function.compose g f) Function.id (R_id A B f) s)
        ->
          T_ R R_id R_compose A B
.

End TYPE.

Module Name.

Variant Tag : Type
  :=
      variable : Tag
    |
      module : Tag
.

End Name.

Module Expression.

Inductive T (X : Name.Tag -> Type) : Type
  :=
      variable : X Name.variable -> T X
    |
      abstraction : X Name.variable -> T X -> T X -> T X
    |
      application : T X -> T X -> T X
    |
      type_type : T X
    |
      type_function : X Name.variable -> T X -> T X -> T X
.

Inductive T_
  (X : Name.Tag -> Type)
  (X_ : forall tag : Name.Tag,  X tag -> X tag -> Type)
  (x : T X)
  (y : T X)
  : Type
  :=
      variable_
        :
          forall
            x_v : X Name.variable
          ,
          forall
            y_v : X Name.variable
          ,
            X_ Name.variable x_v y_v
          ->
            Path.T (T X) x (variable X x_v)
          ->
            Path.T (T X) y (variable X y_v)
          ->
            T_ X X_ x y
    |
      application_
        :
          forall
            x_t : T X
          ,
          forall
            x_u : T X
          ,
          forall
            y_t : T X
          ,
          forall
            y_u : T X
          ,
            T_ X X_ x_t y_t
          ->
            T_ X X_ x_u y_u
          ->
            Path.T (T X) x (application X x_t x_u)
          ->
            Path.T (T X) y (application X y_t y_u)
          ->
            T_ X X_ x y
    |
      abstraction_
        :
          forall
            x_x : X Name.variable
          ,
          forall
            x_A : T X
          ,
          forall
            x_t : T X
          ,
          forall
            y_x : X Name.variable
          ,
          forall
            y_A : T X
          ,
          forall
            y_t : T X
          ,
            X_ Name.variable x_x y_x
          ->
            T_ X X_ x_A y_A
          ->
            T_ X X_ x_t y_t
          ->
            Path.T (T X) x (abstraction X x_x x_A x_t)
          ->
            Path.T (T X) y (abstraction X y_x x_A x_t)
          ->
            T_ X X_ x y
    |
      type_type_
        :
            Path.T (T X) x (type_type X)
          ->
            Path.T (T X) y (type_type X)
          ->
            T_ X X_ x y
    |
      type_function_
        :
          forall
            x_x : X Name.variable
          ,
          forall
            x_A : T X
          ,
          forall
            x_B : T X
          ,
          forall
            y_x : X Name.variable
          ,
          forall
            y_A : T X
          ,
          forall
            y_B : T X
          ,
            X_ Name.variable x_x y_x
          ->
            T_ X X_ x_A y_A
          ->
            T_ X X_ x_B y_B
          ->
            Path.T (T X) x (type_function X x_x x_A x_B)
          ->
            Path.T (T X) y (type_function X y_x y_A y_B)
          ->
            T_ X X_ x y
  .

End Expression.

End Main.
