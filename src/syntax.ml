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
  | RecordTy of (string * t) list
  | Record of (string * t) list
  | Proj of string * t
  | Data of {name : string ; params : t list}
  | Intro of {name : string ; args : t list}
  | Elim of {mot : t bnd ; arms : ([`Rec of string * string | `Arg of string] list * t) bnd list ; scrut : t}
  | Id of t * t * t
  | Refl of t
  | J of {mot : string * string * string * t ; scrut : t ; body : string * t}
  | Let of t bnd * t
  | Hole of {name : string ; tp : t}
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
  | RecordTy fs -> RecordTy (List.map ~f:(fun (field,tp) -> (field,f tp)) fs)
  | Record fs -> Record (List.map ~f:(fun (field,tm) -> (field,f tm)) fs)
  | Proj (field,t) -> Proj (field,f t)
  | Data {name ; params} -> Data {name ; params = List.map ~f params}
  | Intro {name ; args} -> Intro {name ; args = List.map ~f args}
  | Elim {mot = (x,m) ; scrut ; arms} -> Elim {mot = (x,f m) ; scrut = f scrut ; arms = List.map arms ~f:(fun (con,(vs,e)) -> (con, (vs,f e)))}
  | Id (a,x,y) -> Id (f a, f x, f y)
  | Refl x -> Refl (f x)
  | J {mot = (x,y,p,m) ; body = (z,e) ; scrut} -> J {mot = (x,y,p,f m) ; body = (z,f e) ; scrut = f scrut}
  | Sg ((x,d),r) -> Sg ((x,f d),f r)
  | Pair (x,y) -> Pair (f x, f y)
  | Fst p -> Fst (f p)
  | Snd p -> Snd (f p)
  | Let ((x,e1),e2) -> Let ((x,f e1),f e2)
  | Hole {name ; tp} -> Hole {name ; tp = f tp}



let rec bottom_up f x = x |> rec_map (bottom_up f) |> f
let rec top_down f x = x |> f |> rec_map (top_down f)

let lift i = bottom_up (function 
  | U (Const j) -> U (Const (j + i)) 
  | x -> x)

let rec pp_term (e : t) : string =
  match e with
    | Lam (x,e) -> sprintf "λ %s => %s" x (pp_term e)
    | Pi (("_",(Pi _ | Sg _ as d)),r) -> sprintf "(%s) → %s" (pp_term d) (pp_term r)
    | Pi (("_",d),r) -> sprintf "%s → %s" (pp_term d) (pp_term r)
    | Pi ((x,d),r) -> sprintf "(%s : %s) → %s" x (pp_term d) (pp_term r)
    | Sg (("_",t),(Sg _ as e)) -> sprintf "%s × %s" (pp_atomic t) (pp_term e)
    | Sg (("_",t),e) -> sprintf "%s × %s" (pp_atomic t) (pp_atomic e)
    | Sg ((x,t),(Sg _ as e)) -> sprintf "(%s : %s) × %s" x (pp_term t) (pp_term e)
    | Sg ((x,t),e) -> sprintf "(%s : %s) × %s" x (pp_term t) (pp_atomic e)
    | Ap ((Lam _ | J _ | Elim _) as e1,e2) -> sprintf "(%s) %s" (pp_term e1) (pp_term e2)
    | Ap (e1,(Ap _ as e2)) -> sprintf "%s (%s)" (pp_term e1) (pp_term e2)
    | Ap (e1,e2) -> sprintf "%s %s" (pp_term e1) (pp_atomic e2)
    | Intro {name ; args = arg::args} -> sprintf "%s %s" name (pp_args (arg::args))
    | Data {name ; params = p::ps} -> sprintf "%s %s" name (pp_args (p::ps))
    | Elim {mot = _ ; arms = [] ; scrut} ->
      sprintf "elim %s with" (pp_atomic scrut)
    | Elim {mot = _ ; arms ; scrut} ->
      sprintf "elim %s with %s" (pp_atomic scrut) (pp_arms arms)
    | Id (_,x,y) -> sprintf "%s == %s" (pp_term x) (pp_term y)
    | J {mot = _; body = (a,case) ; scrut} -> 
      sprintf "match %s with refl %s ⇒ %s" (pp_atomic scrut) a (pp_term case)
    | Refl x -> sprintf "refl %s" (pp_atomic x)
    | Let ((x,e1),e2) -> sprintf "let %s = %s in %s" x (pp_term e1) (pp_term e2)
    | RecordTy (f::fs) -> "sig "^pp_record ":" (f::fs)
    | Record (f::fs) -> "struct "^pp_record "=" (f::fs)
    | _ -> pp_atomic e 

and pp_record sep = function
  | [] -> ""
  | [(f,t)] -> sprintf "%s %s %s" f sep (pp_term t)
  | (f,t)::fs -> sprintf "%s %s %s | %s" f sep (pp_term t) (pp_record sep fs)

and pp_args = function
  | [] -> ""
  | [x] -> pp_atomic x
  | x::xs -> pp_atomic x ^ " " ^ pp_args xs  

and pp_arms = function
  | [] -> ""
  | arm::arms -> sprintf "%s %s" (pp_arm arm) (pp_arms arms)

and pp_arm (con,(args,arm)) =
  match args with
    | [] -> sprintf "| %s => %s" con (pp_term arm)
    | _  -> sprintf "| %s %s => %s" con (pp_arm_args args) (pp_term arm)

and pp_arm_arg = function
  | `Arg x -> x
  | `Rec (x,r) -> sprintf "(%s / %s)" x r

and pp_arm_args = function
  | [] -> ""
  | [x] -> pp_arm_arg x
  | x::xs -> pp_arm_arg x ^ " " ^ pp_arm_args xs

and pp_atomic (e : t) : string =
  match e with
    | Var x -> x
    | Hole {name;_} -> name
    | U Omega -> "Type^ω"
    | U (Const 0) -> "Type"
    | U (Const i) -> sprintf "Type^%i" i
    | Pair (e1,e2) -> sprintf "(%s,%s)" (pp_term e1) (pp_term e2)
    | Fst e -> sprintf "%s.1" (pp_atomic e)
    | Snd e -> sprintf "%s.2" (pp_atomic e)
    | Proj (f,t) -> sprintf "%s.%s" (pp_atomic t) f
    | Data {name ; params = []} -> name
    | Intro {name ; args = []} -> name
    | Record [] -> "struct"
    | RecordTy [] -> "sig"
    | _ -> sprintf "(%s)" (pp_term e)

let show = pp_term


let (++) m (key,data) = String.Map.set m ~key ~data

let rec equal (i : int) (g1 : int String.Map.t) (e1 : t) (g2 : int String.Map.t) (e2 : t) : bool =
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
      equal i g1 e1 g2 e1' && equal i g1 e2 g2 e2'
    | Lam (x,e), Lam (y,e') ->
      equal (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
    | Pi ((x,t),e),Pi ((y,t'),e') | Sg ((x,t),e),Sg ((y,t'),e') | Let ((x,t),e),Let ((y,t'),e') -> 
      equal i g1 t g2 t' && equal (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
    | Pair (x,y), Pair (x',y') ->
      equal i g1 x g2 x' && equal i g1 y g2 y'
    | U Omega, U Omega -> true
    | U Const i, U Const j -> i = j 
    | Refl e, Refl e' | Fst e, Fst e' | Snd e, Snd e' ->
      equal i g1 e g2 e' 
    | Id (t,e1,e2), Id (t',e1',e2') ->
      equal i g1 t g2 t' && equal i g1 e1 g2 e1' && equal i g1 e2 g2 e2'
    | J {mot = (x,y,z,mot) ; body = (a,case) ; scrut = scrut},J {mot = (x',y',z',mot') ; body = (a',case') ; scrut = scrut'} ->
      equal (i+3) (g1 ++ (x,i) ++ (y,i+1) ++ (z,i+2)) mot (g2 ++ (x',i) ++ (y',i+1) ++ (z',i+2)) mot' &&
      equal (i+1) (g1 ++ (a,i)) case (g2 ++ (a',i)) case' &&
      equal i g1 scrut g2 scrut'
    | Data d, Data d' -> String.equal d.name d'.name && List.equal (fun e1 e2 -> equal i g1 e1 g2 e2) d.params d'.params
    | Intro con, Intro con' -> String.equal con.name con'.name && List.equal (fun e1 e2 -> equal i g1 e1 g2 e2) con.args con'.args
    | Elim e, Elim e' ->
      let (x,m),(x',m') = e.mot,e'.mot in
      equal (i+1) (g1 ++ (x,i)) m (g2 ++ (x',i)) m' &&
      equal i g1 e.scrut g2 e'.scrut &&
      begin
      match List.for_all2 ~f:(fun (con1,(args1,arm1)) (con2,(args2,arm2)) -> 
        String.equal con1 con2 && equal_arm i g1 (flatten_arm_args args1,arm1) g2 (flatten_arm_args args2,arm2)) e.arms e'.arms with
        | Ok b -> b
        | _ -> false
      end
    | Record [], Record [] 
    | RecordTy [], RecordTy [] -> true
    | RecordTy ((f1,tp1)::fs1), RecordTy ((f2,tp2)::fs2) -> String.equal f1 f2 && equal i g1 tp1 g2 tp2 && equal (i+1) (g1++(f1,i)) (RecordTy fs1) (g2++(f2,i)) (RecordTy fs2) 
    | Record ((f1,tm1)::fs1), Record ((f2,tm2)::fs2) -> String.equal f1 f2 && equal i g1 tm1 g2 tm2 && equal i g1 (Record fs1) g2 (Record fs2) 
    | Proj (f1,e1),Proj (f2,e2) -> String.equal f1 f2 && equal i g1 e1 g2 e2
    | Hole h1, Hole h2 -> String.equal h1.name h2.name && equal i g1 h1.tp g2 h2.tp
    | _ -> false

and equal_arm i g1 (args1,arm1) g2 (args2,arm2) =
  match args1,args2 with
    | [],[] -> equal i g1 arm1 g2 arm2
    | arg1::args1,arg2::args2 -> equal_arm (i+1) (g1++(arg1,i)) (args1,arm1) (g2++(arg2,i)) (args2,arm2)
    | _ -> false


let subst (sub : t) (fr : t) (e : t) : t =
  let rec go i g e = if equal i g e String.Map.empty fr then sub else
    match e with
      | Ap (e1,e2) -> Ap (go i g e1,go i g e2)
      | Lam (x,e) -> Lam (x,go (i+1) (g++(x,i)) e)
      | Pi ((x,d),r) -> Pi ((x,go i g d),go (i+1) (g++(x,i)) r)
      | Sg ((x,d),r) -> Sg ((x,go i g d),go (i+1) (g++(x,i)) r)
      | Fst e -> Fst (go i g e)
      | Snd e -> Snd (go i g e)
      | Let ((x,d),r) -> Let ((x,go i g d),go (i+1) (g++(x,i)) r)
      | Pair (e1,e2) -> Pair (go i g e1,go i g e2)
      | Refl e -> Refl (go i g e)
      | Hole {name ; tp} -> Hole {name ; tp = go i g tp}
      | Id (a,m,n) -> Id (go i g a,go i g m,go i g n)
      | J { mot = (x,y,p,m) ; body = (z,e) ; scrut} -> J {mot = (x,y,p,go (i+3) (g++(x,i)++(y,i+1)++(p,i+2)) m) ; body = (z,go (i+1) (g++(z,i)) e) ; scrut = go i g scrut}
      | Intro {name;args} -> Intro {name ; args = List.map ~f:(go i g) args}
      | Data {name;params} -> Data {name ; params = List.map ~f:(go i g) params}
      | Elim {mot = (x,m) ; arms ; scrut} -> 
        Elim {mot = (x,go (i+1) (g++(x,i)) m) ; scrut = go i g scrut ; arms = List.map ~f:(fun (con,(vs,arm)) -> (con,(vs,go_arm i g (flatten_arm_args vs) arm))) arms}
      | RecordTy fs -> RecordTy (go_fields i g fs)
      | Record fs -> Record (List.map ~f:(fun (f,tm) -> (f,go i g tm)) fs)
      | Proj (f,e) -> Proj (f,go i g e)
      | Var x -> Var x
      | Lift x -> Lift x
      | U l -> U l

  and go_arm i g args arm = 
    match args with
      | [] -> go i g arm
      | x::xs -> go_arm (i+1) (g++(x,i)) xs arm

  and go_fields i g fs = 
    match fs with
      | [] -> []
      | (f,t)::fs -> (f,go i g t)::go_fields (i+1) (g++(f,i)) fs

in go 0 String.Map.empty e



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
    | Data {name ; params} -> Spine (to_concrete (Var name),params |> List.map ~f:to_concrete |> list_to_spine)
    | Intro {name ; args} -> Spine (to_concrete (Var name),args |> List.map ~f:to_concrete |> list_to_spine)
    | Elim {mot = (x,m) ; scrut ; arms} -> Elim {mot = Some (x,to_concrete m) ; scrut = to_concrete scrut ; arms = List.map ~f:(fun (con,(vs,arm)) -> (con,(vs,to_concrete arm))) arms}
    | RecordTy fs -> RecordTy {extends = [] ; fields = List.map ~f:(fun (f,tp) -> (f,to_concrete tp)) fs}
    | Record fs -> Record {extends = [] ; fields = List.map ~f:(fun (f,tm) -> (f,to_concrete tm)) fs}
    | Proj (f,e) -> Proj (f,to_concrete e)
    | Id (a,m,n) -> Id (to_concrete a,to_concrete m,to_concrete n)
    | Refl _ -> Refl
    | J {mot = (x,y,p,m) ; body = (z,e) ; scrut} -> J {mot = Some (x,y,p,to_concrete m) ; body = (z,to_concrete e) ; scrut = to_concrete scrut} 
    | Let ((x,d),r) -> Let ((x,to_concrete d),to_concrete r)
    | Hole {name;_} -> Hole name