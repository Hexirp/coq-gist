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

Module Expression.

Inductive T (X : Type) : Type
  :=
    variable : X -> T X
  |
    application : T X -> T X -> T X
  |
    abstraction : T X -> (X -> T X) -> T X
  |
    definition : T X -> T X -> (X -> T X) -> T X
  |
    (* Type : Type *)
    type : T X
  |
    function : T X -> (X -> T X) -> T X
  |
    recursion : T X -> (X -> T X) -> T X
  |
    (* _≡_ : (A : Type) -> (x : A) -> (y : A) -> Type *)
    congruence : T X -> T X -> T X -> T X
  |
    (* cast : (A : Type) -> (B : Type) -> (p : _≡_ Type A B) -> (x : A) -> B *)
    casting : T X -> T X -> T X -> T X -> T X
  .

Inductive T_ (X : Type) (X_ : X -> X -> Type) (x : T X) (y : T X) : Type
  :=
    variable_
      :
        forall
          x_v : X
        ,
        forall
          y_v : X
        ,
          X_ x_v y_v
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
          x_f : T X
        ,
        forall
          x_x : T X
        ,
        forall
          y_f : T X
        ,
        forall
          y_x : T X
        ,
          T_ X X_ x_f y_f
        ->
          T_ X X_ x_x y_x
        ->
          Path.T (T X) x (application X x_f x_x)
        ->
          Path.T (T X) y (application X y_f y_x)
        ->
          T_ X X_ x y
  |
    abstraction_
      :
        forall
          x_t : T X
        ,
        forall
          x_f : X -> T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_f : X -> T X
        ,
          T_ X X_ x_t y_t
        ->
          Dependent_Function.T_
            X
            X_
            (fun x : X => T X)
            (fun x : X => fun y : X => fun p : X_ x y => T_ X X_)
            x_f
            y_f
        ->
          Path.T (T X) x (abstraction X x_t x_f)
        ->
          Path.T (T X) y (abstraction X y_t y_f)
        ->
          T_ X X_ x y
  |
    definition_
      :
        forall
          x_t : T X
        ,
        forall
          x_x : T X
        ,
        forall
          x_f : X -> T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_x : T X
        ,
        forall
          y_f : X -> T X
        ,
          T_ X X_ x_t y_t
        ->
          T_ X X_ x_x y_x
        ->
          Dependent_Function.T_
            X
            X_
            (fun x : X => T X)
            (fun x : X => fun y : X => fun p : X_ x y => T_ X X_)
            x_f
            y_f
        ->
          Path.T (T X) x (definition X x_t x_x x_f)
        ->
          Path.T (T X) y (definition X y_t y_x y_f)
        ->
          T_ X X_ x y
  |
    type_
      :
          Path.T (T X) x (type X)
        ->
          Path.T (T X) y (type X)
        ->
          T_ X X_ x y
  |
    function_
      :
        forall
          x_t : T X
        ,
        forall
          x_p : X -> T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_p : X -> T X
        ,
          T_ X X_ x_t y_t
        ->
          Dependent_Function.T_
            X
            X_
            (fun x : X => T X)
            (fun x : X => fun y : X => fun p : X_ x y => T_ X X_)
            x_p
            y_p
        ->
          Path.T (T X) x (function X x_t x_p)
        ->
          Path.T (T X) y (function X y_t y_p)
        ->
          T_ X X_ x y
  |
    recursion_
      :
        forall
          x_t : T X
        ,
        forall
          x_f : X -> T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_f : X -> T X
        ,
          T_ X X_ x_t y_t
        ->
          Dependent_Function.T_
            X
            X_
            (fun x : X => T X)
            (fun x : X => fun y : X => fun p : X_ x y => T_ X X_)
            x_f
            y_f
        ->
          Path.T (T X) x (recursion X x_t x_f)
        ->
          Path.T (T X) y (recursion X y_t y_f)
        ->
          T_ X X_ x y
  |
    congruence_
      :
        forall
          x_t : T X
        ,
        forall
          x_x : T X
        ,
        forall
          x_y : T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_x : T X
        ,
        forall
          y_y : T X
        ,
          T_ X X_ x_t y_t
        ->
          T_ X X_ x_x y_x
        ->
          T_ X X_ x_y y_y
        ->
          Path.T (T X) x (congruence X x_t x_x x_y)
        ->
          Path.T (T X) y (congruence X y_t y_x y_y)
        ->
          T_ X X_ x y
  |
    casting_
      :
        forall
          x_t : T X
        ,
        forall
          x_s : T X
        ,
        forall
          x_p : T X
        ,
        forall
          x_x : T X
        ,
        forall
          y_t : T X
        ,
        forall
          y_s : T X
        ,
        forall
          y_p : T X
        ,
        forall
          y_x : T X
        ,
          T_ X X_ x_t y_t
        ->
          T_ X X_ x_s y_s
        ->
          T_ X X_ x_p y_p
        ->
          T_ X X_ x_x y_x
        ->
          Path.T (T X) x (casting X x_t x_s x_p x_x)
        ->
          Path.T (T X) y (casting X y_t y_s y_p y_x)
        ->
          T_ X X_ x y
  .

End Expression.

Definition flatten (X : Type) (x : Expression.T (Expression.T X)) : Expression.T X
  :=
    let
      func
        :=
          fix func (x : Expression.T (Expression.T X)) {struct x} : Expression.T X
            :=
              match x with
                Expression.variable _ x_v => x_v
              |
                Expression.application _ x_f x_x
                  =>
                    Expression.application X (func x_f) (func x_x)
              |
                Expression.abstraction _ x_t x_f
                  =>
                    Expression.abstraction
                      X
                      (func x_t)
                      (fun x_v : X => func (x_f (Expression.variable X x_v)))
              |
                Expression.definition _ x_t x_x x_f
                  =>
                    Expression.definition
                      X
                      (func x_t)
                      (func x_x)
                      (fun x_v : X => func (x_f (Expression.variable X x_v)))
              |
                Expression.type _ => Expression.type X
              |
                Expression.function _ x_t x_p
                  =>
                    Expression.function
                      X
                      (func x_t)
                      (fun x_v : X => func (x_p (Expression.variable X x_v)))
              |
                Expression.recursion _ x_t x_f
                  =>
                    Expression.recursion
                      X
                      (func x_t)
                      (fun x_v : X => func (x_f (Expression.variable X x_v)))
              |
                Expression.congruence _ x_t x_x x_y
                  =>
                    Expression.congruence X (func x_t) (func x_x) (func x_y)
              |
                Expression.casting _ x_t x_s x_p x_x
                  =>
                    Expression.casting X (func x_t) (func x_s) (func x_p) (func x_x)
              end
    in
      func x
  .

Definition substitute
  (x : forall X : Type, Expression.T X)
  (y : forall X : Type, X -> Expression.T X)
  : forall X : Type, Expression.T X
  :=
    fun (X : Type) => flatten X (y (Expression.T X) (x X))
  .

Module Is_Typed.

Inductive T
  (X : Type)
  (R : X -> Expression.T X -> Type)
  (x : Expression.T X)
  (t : Expression.T X)
  : Type
  :=
    variable
      :
        forall
          x_v : X
        ,
          R x_v t
        ->
          Path.T (Expression.T X) x (Expression.variable X x_v)
        ->
          T X R x t
  .

End Is_Typed.

End Main.
