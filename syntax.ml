open Core

type 'a bnd = string * 'a
  [@@deriving show]

type t =
  | Var of string
  | U of Level.t
  | Pi of t bnd * t
  | Lam of string * t
  | Ap of t * t
  | Data of string
  | Intro of {name : string ; args : t list}
  | Elim of {mot : t bnd ; arms : ([`Rec of string * string | `Arg of string] list * t) bnd list ; scrut : t}
  | Id of t * t * t
  | Refl of t
  | J of {mot : string * string * string * t ; scrut : t ; body : string * t}

let rec_map (f : t -> t) = function
  | Var x -> Var x
  | Pi ((x,d),r) -> Pi ((x,f d), f r)
  | Lam (x,e) -> Lam (x,f e)
  | Ap (g,e) -> Ap (f g, f e)
  | U i -> U i
  | Data d -> Data d
  | Intro {name ; args} -> Intro {name ; args = List.map ~f args}
  | Elim {mot = (x,m) ; scrut ; arms} -> Elim {mot = (x,f m) ; scrut = f scrut ; arms = List.map arms ~f:(fun (con,(vs,e)) -> (con, (vs,f e)))}
  | Id (a,x,y) -> Id (f a, f x, f y)
  | Refl x -> Refl (f x)
  | J {mot = (x,y,p,m) ; body = (z,e) ; scrut} -> J {mot = (x,y,p,f m) ; body = (z,f e) ; scrut = f scrut}

let rec bottom_up f x = x |> rec_map (bottom_up f) |> f

let lift i = bottom_up (function U (Const j) -> U (Const (j + i)) | x -> x)

let rec pp_term (e : t) : string =
  match e with
    | Lam (x,e) -> sprintf "λ %s ⇒ %s" x (pp_term e)
    | Pi (("_",(Pi _ as d)),r) -> sprintf "(%s) → %s" (pp_term d) (pp_term r)
    | Pi (("_",d),r) -> sprintf "%s → %s" (pp_term d) (pp_term r)
    | Pi ((x,d),r) -> sprintf "(%s : %s) → %s" x (pp_term d) (pp_term r)
    | Ap ((Lam _ | J _ | Elim _) as e1,e2) -> sprintf "(%s) %s" (pp_term e1) (pp_term e2)
    | Ap (e1,(Ap _ as e2)) -> sprintf "%s (%s)" (pp_term e1) (pp_term e2)
    | Ap (e1,e2) -> sprintf "%s %s" (pp_term e1) (pp_atomic e2)
    | Intro {name ; args} -> sprintf "%s %s" name (pp_args args)
    | Elim {mot = _ ; arms ; scrut} ->
      sprintf "elim %s with %s" (pp_term scrut) (pp_arms arms)
    | Id (a,x,y) -> sprintf "Id %s %s %s" (pp_atomic a) (pp_atomic x) (pp_atomic y)
    | J {mot = _; body = (a,case) ; scrut} -> 
      sprintf "match %s with refl %s ⇒ %s" (pp_term scrut) a (pp_term case)
    | _ -> pp_atomic e 

and pp_args = function
  | [] -> ""
  | [x] -> pp_atomic x
  | x::xs -> pp_atomic x ^ " " ^ pp_args xs  

and pp_arms = function
  | [] -> ""
  | arm::arms -> sprintf "%s\n%s" (pp_arm arm) (pp_arms arms)

and pp_arm (con,(args,arm)) =
  sprintf "| %s %s=> %s" con (pp_arm_args args) (pp_term arm)

and pp_arm_args = function
  | [] -> " "
  | `Arg x::args -> sprintf "%s %s" x (pp_arm_args args)
  | `Rec (x,r)::args -> sprintf "(%s / %s) %s" x r (pp_arm_args args)


and pp_atomic (e : t) : string =
  match e with
    | Var x -> x
    | U Omega -> "Type^ω"
    | U (Const 0) -> "Type"
    | U (Const i) -> sprintf "Type^%i" i
    | Data name -> name
    | Intro {name ; args = []} -> name
    | Refl x -> sprintf "refl %s" (pp_atomic x)
    | _ -> sprintf "(%s)" (pp_term e)

let show = pp_term