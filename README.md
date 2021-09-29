# datatt

datatt is an implementation of a dependent type theory with user defined datatypes.
Check out the library directory for some fun stuff.

## Features

* Dependent products : `(x : A) -> B x`
* Dependent sums : `(x : A) * B x`
* Identity types, with the J eliminator : `Id A m n` or `m = n`
* User defined, parametric datatypes : 
  ```
  data Nat => 
    | zero
    | suc (n : Nat)
   
  data (A : Type) List => 
    | nil 
    | cons (x : A) (xs : List)
* Top-level definitions : `def one : Nat = suc zero`
* Dependent elimination for datatypes :
  ```
  def + (n m : Nat) : Nat => elim n with
    | zero => m
    | suc (m' / ih) => suc ih
   
  def +-zero : (n : Nat) -> + n zero = n => \elim
    | zero => refl
    | suc (n' / ih) => match ih with refl i => refl
* First class dependent records : `(struct fst = zero | snd = refl) : (sig fst : Nat | snd : fst = zero)`
* A countable, cumulative hierachy of strict Russel-style universes : `Type : Type^1`, `Type : Type^2`,`Type^1 : Type^2`, etc
* Basic level polymorphism via McBride's "crude but effective stratification" : 
  ```
  def xs : List^1 Type = cons Nat nil
  def f (x : Type) : Type = x
  def g : Type^2 -> Type^2 = f^2

  
