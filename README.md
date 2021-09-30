# datatt

datatt is an implementation of a dependent type theory with user defined datatypes.
Check out the library directory for some fun stuff.

## Features

* Dependent functions:
  ```
  def f : (x : A) -> B x => \x => e
  def f (x : A) : B x => e
* Dependent sums:
  ```
  def p : (x : A) * B x = (fst , snd) 
  def p_fst : A = p.1
  def p_snd : B p.1 = p.2

* Identity types, with the J eliminator:
  ```
  def reflexivity (A : Type) (x : A) : x = x => refl
  def symmetry (A : Type) (x y : A) (p : x = y) : y = x =>
    match p with
      | refl i => refl
* User defined, parametric datatypes : 
  ```
  data Nat => 
    | zero
    | suc (n : Nat)
   
  data (A : Type) List => 
    | nil 
    | cons (x : A) (xs : List)
* Dependent elimination for datatypes:
  ```
  -- Eliminate a variable in the context
  def + (n m : Nat) : Nat => elim n with
    | zero => m
    | suc (m' / ih) => suc ih
   
  -- Elimination lambda
  def +-zero : (n : Nat) -> + n zero = n => \elim
    | zero => refl
    | suc (n' / ih) => match ih with refl i => refl
* First class dependent records:
  ```
  def Iso (A B : Type) : Type = sig
    | f : A -> B
    | g : B -> A
    | gf : (x : A) -> g (f x) = x
    | fg : (y : B) -> f (g y) = y
  
  def iso-refl (A : Type) : Iso A A = struct
    | f x => x
    | g x => x
    | gf _ => refl
    | fg _ => refl
* A countable, cumulative hierachy of strict Russel-style universes: 
  ````
  def a : Type^1 = Type
  def b : Type^2 = Type
  def c : Type^2 = Type^1

* Basic level polymorphism via McBride's "crude but effective stratification" : 
  ```
  def xs : List^1 Type = cons Nat nil
  def f (x : Type) : Type = x
  def g : Type^2 -> Type^2 = f^2

  
