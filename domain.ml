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

let rec lift i = function
  | Lam clos -> Lam (lift_clos i clos)
  | Pi (d,clos) -> Pi (lift i d, lift_clos i clos)
  | Sg (d,clos) -> Sg (lift i d, lift_clos i clos)
  | Pair (x,y) -> Pair (lift i x,lift i y)
  | U Omega -> U Omega
  | U (Const j) -> U (Const (j + i))
  | Id (a,x,y) -> Id (lift i a,lift i x, lift i y)
  | Refl x -> Refl (lift i x)
  | Data d -> Data d (* this might be wrong lol *)
  | Intro {name ; args} -> Intro {name ; args = List.map ~f:(lift i) args}
  | Neutral {tp ; ne} -> Neutral {tp = lift i tp ; ne = lift_ne i ne}

and lift_clos i clos =
  {clos with tm = Syntax.lift i clos.tm}

and lift_clos3 i (clos : clos3) =
  {clos with tm = Syntax.lift i clos.tm}

and lift_arm_clos i clos =
  {clos with arm = Syntax.lift i clos.arm}


and lift_ne i = function
  | Var x -> Var x
  | Ap (ne, {tp ; tm}) -> Ap (lift_ne i ne, {tp = lift i tp; tm = lift i tm})
  | J {mot ; body ; scrut ; tp} -> J {mot = lift_clos3 i mot ; body = lift_clos i body ; scrut = lift_ne i scrut ; tp = lift i tp}
  | Elim {mot ; arms ; scrut ; desc } -> Elim { mot = lift_clos i mot ; arms = List.map ~f:(fun (con,clos) -> (con,lift_arm_clos i clos)) arms ; scrut = lift_ne i scrut ; desc}
  | Fst p -> Fst (lift_ne i p)
  | Snd p -> Snd (lift_ne i p)