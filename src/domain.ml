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
  | Data of {desc : desc ; params : t list}
  | Intro of {name : string ; args : t list}
  | RecordTy of Syntax.t bnd list * env
  | Record of t bnd list
  | Id of t * t * t
  | Refl of t
  | Neutral of {tp : t ; ne : ne}
  [@@deriving show {with_path = false}]

and dom = t

and ne =
  | Var of string
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | Proj of string * ne
  | Elim of {mot : clos ; arms : arm_clos bnd list ; scrut : ne ; desc : desc ; params : t list}
  | J of {mot : clos3 ; body : clos ; scrut : ne ; tp : t}
  | Hole of {name : string ; tp : t}
  [@@deriving show {with_path = false}]

and nf = {tm : t ; tp : t}
  [@@deriving show {with_path = false}]

and clos = {name : string ; tm : Syntax.t ; env : env}
  [@@deriving show {with_path = false}]

and clos3 = {names : string * string * string ; tm : Syntax.t ; env : env }
  [@@deriving show {with_path = false}]

and arm_clos = {names : [`Rec of string * string | `Arg of string] list ; arm : Syntax.t ; env : env}
  [@@deriving show {with_path = false}]

and env_entry =
  | Desc of desc
  | Def of {tm : t ; tp : t}
  | Tm of t

and env = env_entry Map.t

and spec = 
  | Rec
  | Tp of Syntax.t


and desc = {name : string ; cons : spec bnd list bnd list ; params : Syntax.t bnd list ; env : env ; lvl : Level.t}

[@@@ocaml.warning "+30"]


let rec params_to_pi lvl = function
  | [] -> Syntax.U lvl
  | (x,t)::ps -> Syntax.Pi ((x,t),params_to_pi lvl ps)


let rec params_to_lam name acc = function
  | [] -> Syntax.Data {name ; params = List.rev acc}
  | (x,_)::ps -> Syntax.Lam (x,params_to_lam name (Var x::acc) ps )

let params_to_dlam env (desc : desc) = function
  | [] -> Data {desc ; params = []}
  | (x,_)::ps -> Lam {name = x ; env = env ; tm = params_to_lam desc.name [Var x] ps}


module Env =
  struct
    type t = env

    let set env ~key ~data = String.Map.set env ~key ~data:(Tm data)
  
    let set_data env ~var ~(data : desc) = String.Map.set env ~key:var ~data:(Desc data)

    let find_exn (env : env) (s : string) : dom =
      match String.Map.find_exn env s with
        | Tm tm -> tm
        | Def {tm;_} -> tm
        | Desc d -> params_to_dlam env d d.params

    let find_def_exn (env : env) (s : string) : nf =
      match String.Map.find_exn env s with
        | Def {tm ; tp} -> {tm ; tp}
        | _ -> failwith "find_def_exn"

    let find_data_exn (env : env) (s : string) : desc =
      match String.Map.find_exn env s with
        | Tm _ | Def _ -> failwith "find_data_exn - env"
        | Desc d -> d

    let key_set = String.Map.key_set
  end
(* 

let rec lift i = function
  | Lam clos -> Lam (lift_clos i clos)
  | Pi (d,clos) -> Pi (lift i d, lift_clos i clos)
  | Sg (d,clos) -> Sg (lift i d, lift_clos i clos)
  | Pair (x,y) -> Pair (lift i x,lift i y)
  | U Omega -> U Omega
  | U (Const j) -> U (Const (j + i))
  | Id (a,x,y) -> Id (lift i a,lift i x, lift i y)
  | Refl x -> Refl (lift i x)
  | Data {desc ; params} -> Data {desc ; params = List.map ~f:(lift i) params}
  | Intro {name ; args} -> Intro {name ; args = List.map ~f:(lift i) args}
  | RecordTy (fs,env) -> RecordTy (List.map ~f:(fun (f,tp) -> (f,Syntax.lift i tp)) fs,env)
  | Record fs -> Record (List.map ~f:(fun (f,tm) -> (f,lift i tm)) fs)
  | Neutral {tp ; ne} -> Neutral {tp = lift i tp ; ne = lift_ne i ne}


(* Wrong because the closure might contain toplevel vars that should be expanded *)
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
  | Elim {mot ; arms ; scrut ; desc ; params} -> 
    Elim { mot = lift_clos i mot ; arms = List.map ~f:(fun (con,clos) -> (con,lift_arm_clos i clos)) arms ; scrut = lift_ne i scrut ; desc ; params = List.map ~f:(lift i) params}
  | Fst p -> Fst (lift_ne i p)
  | Snd p -> Snd (lift_ne i p)
  | Proj (f,ne) -> Proj (f,lift_ne i ne)
  | Hole {name ; tp} -> Hole {name ; tp = lift i tp} *)