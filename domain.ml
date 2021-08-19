open Core

module Map =
  struct
    include String.Map
    let pp _ _ _ = ()
    let show _ = "env"
  end

type 'a bnd = string * 'a
  [@@deriving show]

(* Disabling warning 30 so I can have records with duplicate field names *)
[@@@ocaml.warning "-30"]
type t =
  | U of Level.t
  | Lam of clos
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Data of desc
  | Intro of {name : string ; args : t list}
  | Id of t * t * t
  | Refl of t
  | Neutral of {tp : t ; ne : ne}
  [@@deriving show {with_path = false}]

and ne =
  | Var of string
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | Elim of {mot : clos ; arms : arm_clos bnd list ; scrut : ne ; desc : desc}
  | J of {mot : clos3 ; body : clos ; scrut : ne ; tp : t}
  [@@deriving show {with_path = false}]

and nf = {tm : t ; tp : t}
  [@@deriving show {with_path = false}]

and clos = {name : string ; tm : Syntax.t ; env : env}
  [@@deriving show {with_path = false}]

and clos3 = {names : string * string * string ; tm : Syntax.t ; env : env }
  [@@deriving show {with_path = false}]

and arm_clos = {names : [`Rec of string * string | `Arg of string] list ; arm : Syntax.t ; env : env}
  [@@deriving show {with_path = false}]

and env = t Map.t

and spec = 
  | Rec
  | Tp of Syntax.t

and 'a tele =
  | Nil
  | One of 'a
  | Cons of 'a bnd * 'a tele

and desc = {name : string ; cons : spec tele bnd list ; env : env}

[@@@ocaml.warning "+30"]
