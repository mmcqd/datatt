type 'a spine =
  | Nil
  | Snoc of 'a spine * 'a
  [@@deriving show { with_path = false }]

let rec spine_to_list_ acc = function
  | Nil -> acc
  | Snoc (xs,x) -> spine_to_list_ (x::acc) xs

let spine_to_list s = spine_to_list_ [] s

let rec list_to_spine_ acc = function
  | [] -> acc
  | x::xs -> list_to_spine_ (Snoc (acc,x)) xs

let list_to_spine xs = list_to_spine_ Nil xs

type 'a bnd = (string * 'a)
  [@@deriving show]

type t_ =
  | Hole
  | Var of string
  | Lift of {name : string ; lvl : int}
  | U of Level.t
  | Pi of t bnd list * t
  | Lam of string list * t
  | Spine of t * t spine
  | Sg of t bnd list * t
  | Tuple of t list
  | Fst of t
  | Snd of t
  | Elim of {mot : t bnd option ; scrut : t ; arms : ([`Rec of string * string | `Arg of string] list * t) bnd list}
  | ElimFun of ([`Rec of string * string | `Arg of string] list * t) bnd list
  | Id of t * t * t
  | Refl
  | J of {mot : (string * string * string * t) option ; scrut : t ; body : string * t}
  | Ascribe of {tm : t ; tp : t}
  | Let of t bnd * t
  | Absurd
  [@@deriving show]

and t = t_ Mark.t

let show (cs,_) = show_t_ cs

type cmd =
  | Eval of t
  | Def of string * t
  | Axiom of string * t
  | Data of {name : string ; cons : (t bnd list) bnd list ; params : t bnd list}
