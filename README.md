# datatt

datatt is an implementation of a dependent type theory with user defined datatypes.
Check out the library directory for some fun stuff. In `hott.dtt` I've translated an Agda proof of Hedberg's Theorem, that any type `A` with decidable equality is a Set, meaning that all proofs of equality between elements of `A` are themselves equal.

I took a lot of inspiration for this project from trying (and sometimes succeeding) to read the source code of [redtt](https://github.com/RedPRL/redtt).

## Building

You can build datatt by installing `dune` and then running `Make` in the datatt directory.

## Features

* Dependent functions.
  ```
  def f : (x : A) -> B x => \x => e
  def f (x : A) : B x => e
* Dependent pairs.
  ```
  def p : (x : A) * B x => (fst , snd) 
  def p_fst : A => p.1
  def p_snd : B p.1 => p.2

* Identity types, with the J eliminator.
  ```
  -- Nice identity type syntax : x = y
  def reflexivity (A : Type) (x : A) : x = x => refl
  
  -- Uglier syntax, but provides a type to check against: Id A x y
  def reflexivity' (A : Type) (x : A) : Id A x x => refl
  
  def symmetry (A : Type) (x y : A) (p : x = y) : y = x =>
    match p with
      | refl i => refl
* User defined, parametric datatypes. Constructors can be overloaded, but their types cannot be synthesized, only checked. When declaring a datatype, recursive references to the type being defined are left unapplied to their parameters, as can be seen in the definition of `List`.
  ```
  data Nat => 
    | zero
    | suc (n : Nat)
   
  data (A : Type) List => 
    | nil 
    | cons (x : A) (xs : List)
   
  -- Elaboration error!
  def z => zero
  
  -- All good
  def z : Nat => zero
  
  def xs : List Nat => cons zero (cons (suc zero) nil)
  
* Dependent elimination for datatypes.
  ```
  -- Eliminate a variable in the context
  def + (n m : Nat) : Nat => elim n with
    | zero => m
    | suc (m' / ih) => suc ih
   
  -- Elimination lambda
  def +-zero : (n : Nat) -> + n zero = n => \elim
    | zero => refl
    | suc (n' / ih) => match ih with refl i => refl
* First class dependent records.
  ```
  def Iso (A B : Type) : Type => sig
    | f : A -> B
    | g : B -> A
    | gf : (x : A) -> g (f x) = x
    | fg : (y : B) -> f (g y) = y
  
  def iso-refl (A : Type) : Iso A A => struct
    | f x => x
    | g x => x
    | gf _ => refl
    | fg _ => refl

  def iso-refl-f : Nat -> Nat =>
    let r = iso-refl Nat in
    r.f 
* Record Extension (if there are duplicate fields, we simply keep the first one).
  ```
  def Functor (F : Type -> Type) : Type => sig
    | map : (A B : Type) -> F A -> F B
  
  def Applicative (F : Type -> Type) : Type => sig extends Functor f
    | pure : (A : Type) -> A -> F A
    | <*> : (A B : Type) -> F (A -> B) -> F A -> F B

  def Functor-Maybe : Functor Maybe => struct
    | map A B f => (\elim none => none | some x => some (f x))
  
  def Applicative-Maybe : Applicative Maybe => struct extends Functor-Maybe
    | pure x => some x
    | <*> A B => \elim
      | none => \ _ => none
      | some f => \elim
        | none => none
        | some x => some (f x)
  
* A countable, cumulative hierachy of strict Russel-style universes.
  ````
  def a : Type^1 => Type
  def b : Type^2 => Type
  def c : Type^2 => Type^1

* Basic level polymorphism via McBride's "crude but effective stratification", where top-level definitions may be lifted to a higher universe.
  ```
  def xs : List^1 Type => cons Nat nil
  def f (x : Type) : Type => x
  def g : Type^2 -> Type^2 => f^2
* A (very basic) "module" system, allowing definitions to be imported from other files. There are no actual modules, and an import simply brings all definitions    from the imported file into scope, unqualified.
  ```
  import nat
  import bool
  
  def p : Nat * Bool => (zero,tt)
* Holes. Terms containing holes will be defined even if you don't fill them, they just won't compute to anything.
  ```
  def trans (A : Type) (x y z : A) (p : x = y) : y = z -> x = z => ?
  
  > ./datatt file.dtt
  > Hole ?0 at 1.66-1.67:
      A : Type
      p : x = y
      x : A
      y : A
      z : A

    ⊢ y = z → x = z

  


## Known Parsing Annoyance
Because of how parsing is implemented, function application with parentheses will not parse properly. The parser thinks it's looking at a depedent function type with multiple arguments and gets confused when it can't find a `:`. To remedy this, just parenthesize the first argument: `(f x).proj ==> (f (x)).proj`. Having to do this is very silly, and I'd like to fix it. My next language will probably use a recursive descent parser.

  
