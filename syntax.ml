open Core

type 'a bnd = string * 'a
  [@@deriving show]

type t =
  | Var of string
  | Lift of {name : string ; lvl : int}
  | U of Level.t
  | Pi of t bnd * t
  | Lam of string * t
  | Ap of t * t
  | Sg of t bnd * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Data of string
  | Intro of {name : string ; args : t list}
  | Elim of {mot : t bnd ; arms : ([`Rec of string * string | `Arg of string] list * t) bnd list ; scrut : t}
  | Id of t * t * t
  | Refl of t
  | J of {mot : string * string * string * t ; scrut : t ; body : string * t}
  [@@deriving show]

let rec flatten_arm_args = function
  | [] -> []
  | `Arg x::args -> x::flatten_arm_args args
  | `Rec (x,r)::args -> x::r::flatten_arm_args args

let rec_map (f : t -> t) = function
  | Var x -> Var x
  | Lift x -> Lift x
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
  | Sg ((x,d),r) -> Sg ((x,f d),f r)
  | Pair (x,y) -> Pair (f x, f y)
  | Fst p -> Fst (f p)
  | Snd p -> Snd (f p)



let rec bottom_up f x = x |> rec_map (bottom_up f) |> f
let rec top_down f x = x |> f |> rec_map (top_down f)

let lift i = bottom_up (function U (Const j) -> U (Const (j + i)) | x -> x)

let rec pp_term (e : t) : string =
  match e with
    | Lam (x,e) -> sprintf "λ %s ⇒ %s" x (pp_term e)
    | Pi (("_",(Pi _ as d)),r) -> sprintf "(%s) → %s" (pp_term d) (pp_term r)
    | Pi (("_",d),r) -> sprintf "%s → %s" (pp_term d) (pp_term r)
    | Pi ((x,d),r) -> sprintf "(%s : %s) → %s" x (pp_term d) (pp_term r)
    | Sg (("_",t),e) -> sprintf "%s × %s" (pp_atomic t) (pp_atomic e)
    | Sg ((x,t),e) -> sprintf "(%s : %s) × %s" x (pp_term t) (pp_atomic e)
    | Ap ((Lam _ | J _ | Elim _) as e1,e2) -> sprintf "(%s) %s" (pp_term e1) (pp_term e2)
    | Ap (e1,(Ap _ as e2)) -> sprintf "%s (%s)" (pp_term e1) (pp_term e2)
    | Ap (e1,e2) -> sprintf "%s %s" (pp_term e1) (pp_atomic e2)
    | Intro {name ; args = arg::args} -> sprintf "%s %s" name (pp_args (arg::args))
    | Elim {mot = _ ; arms ; scrut} ->
      sprintf "elim %s with %s" (pp_atomic scrut) (pp_arms arms)
    | Id (a,x,y) -> sprintf "Id %s %s %s" (pp_atomic a) (pp_atomic x) (pp_atomic y)
    | J {mot = (x,y,p,m); body = (a,case) ; scrut} -> 
      sprintf "match %s at %s %s %s => %s with refl %s ⇒ %s" (pp_atomic scrut) x y p (pp_term m) a (pp_term case)
    | Refl x -> sprintf "refl %s" (pp_atomic x)
    | _ -> pp_atomic e 

and pp_args = function
  | [] -> ""
  | [x] -> pp_atomic x
  | x::xs -> pp_atomic x ^ " " ^ pp_args xs  

and pp_arms = function
  | [] -> ""
  | arm::arms -> sprintf "%s %s" (pp_arm arm) (pp_arms arms)

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
    | Pair (e1,e2) -> sprintf "(%s,%s)" (pp_term e1) (pp_term e2)
    | Fst e -> sprintf "%s.1" (pp_atomic e)
    | Snd e -> sprintf "%s.2" (pp_atomic e)
    | Data d -> d
    | Intro {name ; args = []} -> name
    | _ -> sprintf "(%s)" (pp_term e)

let show = pp_term


let (++) m (key,data) = String.Map.set m ~key ~data

let equal (e1 : t) (e2 : t) : bool =
  let rec go (i : int) (g1 : int String.Map.t) (e1 : t) (g2 : int String.Map.t) (e2 : t) : bool =
    match e1,e2 with
      | Var x,Var y ->
        begin
        match String.Map.find g1 x,String.Map.find g2 y with
          | Some i, Some j -> i = j
          | None,None -> String.equal x y
          | _ -> false
        end
      | Lift l1,Lift l2 -> l1.lvl = l2.lvl && String.equal l1.name l2.name
      | Ap (e1,e2),Ap (e1',e2') ->
        go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | Lam (x,e), Lam (y,e') ->
        go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Pi ((x,t),e),Pi ((y,t'),e') | Sg ((x,t),e),Sg ((y,t'),e') -> 
        go i g1 t g2 t' && go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Pair (x,y), Pair (x',y') ->
        go i g1 x g2 x' && go i g1 y g2 y'
      | U Omega, U Omega -> true
      | U Const i, U Const j -> i = j 
      | Refl e, Refl e' | Fst e, Fst e' | Snd e, Snd e' ->
        go i g1 e g2 e' 
      | Id (t,e1,e2), Id (t',e1',e2') ->
        go i g1 t g2 t' && go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | J {mot = (x,y,z,mot) ; body = (a,case) ; scrut = scrut},J {mot = (x',y',z',mot') ; body = (a',case') ; scrut = scrut'} ->
        go (i+3) (g1 ++ (x,i) ++ (y,i+1) ++ (z,i+2)) mot (g2 ++ (x',i) ++ (y',i+1) ++ (z',i+2)) mot' &&
        go (i+1) (g1 ++ (a,i)) case (g2 ++ (a',i)) case' &&
        go i g1 scrut g2 scrut'
      | Data d, Data d' -> String.equal d d'
      | Intro con, Intro con' -> String.equal con.name con'.name && List.equal (fun e1 e2 -> go i g1 e1 g2 e2) con.args con'.args
      | Elim e, Elim e' ->
        let (x,m),(x',m') = e.mot,e'.mot in
        go (i+1) (g1 ++ (x,i)) m (g2 ++ (x',i)) m' &&
        go i g1 e.scrut g2 e'.scrut &&
        begin
        match List.for_all2 ~f:(fun (con1,(args1,arm1)) (con2,(args2,arm2)) -> 
          String.equal con1 con2 && equal_arm i g1 (flatten_arm_args args1,arm1) g2 (flatten_arm_args args2,arm2)) e.arms e'.arms with
          | Ok b -> b
          | _ -> false
        end
      | _ -> false
  and equal_arm i g1 (args1,arm1) g2 (args2,arm2) =
    match args1,args2 with
      | [],[] -> go i g1 arm1 g2 arm2
      | arg1::args1,arg2::args2 -> equal_arm (i+1) (g1++(arg1,i)) (args1,arm1) (g2++(arg2,i)) (args2,arm2)
      | _ -> false
  in 
  go 0 String.Map.empty e1 String.Map.empty e2

(* This is definitely wrong because it can cause variable capture *)
let subst (subst : t) (fr : t) : t -> t =
  top_down (fun x -> if equal fr x then subst else x)


let rec to_concrete (e : t) : Concrete_syntax.t = Mark.naked @@ to_concrete_ e

and to_concrete_ (e : t) : Concrete_syntax.t_ = let open Concrete_syntax in
  match e with
    | Var x -> Var x
    | Lift {name ; lvl} -> Lift {name ; lvl}
    | U i -> U i
    | Pi ((x,d),r) -> Pi ([(x,to_concrete d)],to_concrete r)
    | Lam (x,e) -> Lam ([x],to_concrete e)
    | Ap (f,e) -> Spine (to_concrete f,Snoc (Nil,to_concrete e))
    | Sg ((x,d),r) -> Sg ([(x,to_concrete d)],to_concrete r)
    | Pair (x,y) -> Tuple [to_concrete x;to_concrete y]
    | Fst p -> Fst (to_concrete p)
    | Snd p -> Snd (to_concrete p)
    | Data d -> Var d
    | Intro {name ; args} -> Spine (to_concrete (Var name),args |> List.map ~f:to_concrete |> list_to_spine)
    | Elim {mot = (x,m) ; scrut ; arms} -> Elim {mot = Some (x,to_concrete m) ; scrut = to_concrete scrut ; arms = List.map ~f:(fun (con,(vs,arm)) -> (con,(vs,to_concrete arm))) arms}
    | Id (a,m,n) -> Id (to_concrete a,to_concrete m,to_concrete n)
    | Refl _ -> Refl
    | J {mot = (x,y,p,m) ; body = (z,e) ; scrut} -> J {mot = Some (x,y,p,to_concrete m) ; body = (z,to_concrete e) ; scrut = to_concrete scrut} 