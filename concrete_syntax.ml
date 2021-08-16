type 'a spine =
  | Nil
  | Snoc of 'a spine * 'a
  [@@deriving show]

let rec spine_to_list_ acc = function
  | Nil -> acc
  | Snoc (xs,x) -> spine_to_list_ (x::acc) xs

let spine_to_list s = spine_to_list_ [] s

type 'a bnd = (string * 'a)
  [@@deriving show]

type t =
  | Hole
  | Var of string
  | U of Level.t
  | Pi of t bnd list * t
  | Lam of string list * t
  | Spine of t * t spine
  | Elim of {mot : t bnd option ; scrut : t ; arms : ([`Rec of string * string | `Arg of string] list * t) bnd list}
  | Id of t * t * t
  | Refl
  | J of {mot : (string * string * string * t) option ; scrut : t ; body : string * t}
  | Ascribe of {tm : t ; tp : t}
  [@@deriving show]

type cmd =
  | Eval of t
  | Def of string * t
  | Data of {name : string ; cons : (t bnd list) bnd list}