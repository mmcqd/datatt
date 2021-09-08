open Core

module Syn = Syntax
module Dom = Domain


exception EquateError of string

let error s = raise (EquateError s)

let var x tp = Dom.Neutral {ne = Var x ; tp}

let rec eval (env : Dom.env) (s : Syn.t) : Dom.t =
  (* printf "EVAL %s\n" (Syn.show s); *)
  match s with
    | Var x -> Dom.Env.find_exn env x
    | Lift {name ; lvl} -> Dom.lift lvl (Dom.Env.find_exn env name)
    | U i -> U i
    | Pi ((x,d),r) -> Pi (eval env d,{name = x ; tm = r ; env})
    | Lam (x,s) -> Lam {name = x ; tm = s ; env}
    | Ap (f,s) -> do_ap (eval env f) (eval env s)
    | Sg ((x,f),s) -> Sg (eval env f,{name = x ; tm = s ; env})
    | Pair (a,b) -> Pair (eval env a, eval env b)
    | Fst p -> do_fst (eval env p)
    | Snd p -> do_snd (eval env p)
    | Data {name ; params} -> Data {desc = Dom.Env.find_data_exn env name ; params = List.map ~f:(eval env) params}
    | Intro {name ; args} -> Intro {name ; args = List.map ~f:(eval env) args}
    | Elim {mot = (x,m) ; arms ; scrut} -> do_elim Dom.{name = x ; tm = m ; env} arms (eval env scrut) env
    | Id (a,m,n) -> Id (eval env a,eval env m,eval env n)
    | Refl x -> Refl (eval env x)
    | J {mot = (x,y,p,m); body = (z,e) ; scrut} -> do_j Dom.{names = (x,y,p) ; tm = m ; env} Dom.{name = z ; tm = e ; env} (eval env scrut)
    | Let ((x,e1),e2) -> eval (Dom.Env.set env ~key:x ~data:(eval env e1)) e2 
    | Hole {name ; tp} -> let tp = eval env tp in Neutral {ne = Hole {name ; tp} ; tp}

and do_clos ({name ; tm ; env } : Dom.clos) (arg : Dom.t) : Dom.t =
  eval (Dom.Env.set env ~key:name ~data:arg) tm


and do_clos3 ({names = (x,y,z) ; tm ; env } : Dom.clos3) (a : Dom.t) (b : Dom.t) (c : Dom.t) : Dom.t =
  eval (env |> Dom.Env.set ~key:x ~data:a |> Dom.Env.set ~key:y ~data:b |> Dom.Env.set ~key:z ~data:c) tm


and do_ap (f : Dom.t) (arg : Dom.t) : Dom.t =
  match f with
    | Lam clos -> do_clos clos arg
    | Neutral {tp = Pi (d,clos) ; ne} ->
      Neutral {tp = do_clos clos arg ; ne = Ap (ne,{tm = arg ; tp = d})}
    | _ -> failwith "do_ap"

and do_fst (p : Dom.t) : Dom.t =
  match p with
    | Pair (f,_) -> f
    | Neutral {tp = Sg (a,_) ; ne} -> Neutral {tp = a ; ne = Fst ne}
    | _ -> failwith "do_fst"

and do_snd (p : Dom.t) : Dom.t =
  match p with
    | Pair (_,s) -> s
    | Neutral {tp = Sg (_,clos) ; ne} -> Neutral {tp = do_clos clos (do_fst p) ; ne = Snd ne}
    | _ -> failwith "do_snd"

and do_elim mot arms scrut env_s =
  match scrut with
    | Intro {name ; args} ->
      let (vars,body) = List.Assoc.find_exn arms ~equal:String.equal name in
      let env = List.fold2_exn args vars ~init:env_s ~f:(fun env arg -> function
        | `Arg x -> env |> Dom.Env.set ~key:x ~data:arg
        | `Rec (x,r) -> env |> Dom.Env.set ~key:x ~data:arg |> Dom.Env.set ~key:r ~data:(do_elim mot arms arg env_s)) in
      eval env body
    | Neutral {tp = Data {desc ; params} ; ne} -> 
      Neutral { tp = do_clos mot scrut
              ; ne = Elim { mot
                          ; arms = List.map arms ~f:(fun (con,(vs,body)) -> con,Dom.{names = vs ; arm = body ; env = env_s})
                          ; scrut = ne
                          ; desc
                          ; params
                          }
              } 
    | _ -> failwith "do_elim"


and do_j (mot : Dom.clos3) (body : Dom.clos) (scrut : Dom.t) : Dom.t = 
  match scrut with
    | Refl x -> do_clos body x
    | Neutral {tp = Id (a,e1,e2) ; ne} ->
      Neutral {tp = do_clos3 mot e1 e2 scrut; 
               ne = J {mot ; body ; tp = a ; scrut = ne}
              }
    | d -> failwith (sprintf "do_j - %s" (Dom.show d))

let fresh used x = if String.equal x "_" then x,used else
  let rec go x = 
    if String.Set.mem used x then go (x ^ "'") else x
  in let y = go x in
  y,String.Set.add used y

let fresh3 used (x,y,z) =
  let x,used = fresh used x in
  let y,used = fresh used y in
  let z,used = fresh used z in
  (x,y,z,used)


let resolve_name used (f : Dom.t) (x : string) =
  match f,x with
    | Lam clos,"_" -> clos.name,used
    | _,"_" -> fresh used "x"
    | _ -> fresh used x

let resolve_arg_tp (desc,params) : Dom.spec -> Dom.t = function
  | Rec -> Data {desc ; params}
  | Tp tp -> eval desc.env tp

let rec apply_params (desc : Dom.desc) param_tps ps =
  match param_tps,ps with
    | [],[] -> desc
    | (x,_)::param_tps,p::ps ->
      apply_params {desc with env = Dom.Env.set desc.env ~key:x ~data:p} param_tps ps
    | _ -> failwith "apply_params"


let rec equate (used : String.Set.t) ?(subtype = false) (e1 : Dom.t) (e2 : Dom.t) (tp : Dom.t) : Syn.t =
  (* printf "-----\nEQUATING\n%s\nWITH\n%s\nAT\n%s\n-----\n" (Dom.show e1) (Dom.show e2) (Dom.show tp); *)
  match e1,e2,tp with
    | U i, U j, U _ -> 
      if subtype then 
        if Level.(<=) i j then U i else error (sprintf "Level Error: %s !<= %s" (Level.show i) (Level.show j))
      else
        if Level.equal i j then U i else error (sprintf "Level Error: %s !<= %s" (Level.show i) (Level.show j))
    | f1,f2, Pi (d,clos) -> 
      let x,used = resolve_name used f1 (clos.name) in
      Lam (x,equate used (do_ap f1 (var x d)) (do_ap f2 (var x d)) (do_clos clos (var x d)))
    | Pi (d1,clos1), Pi (d2,clos2), U i ->
      let d = equate used d2 d1 (U i) in
      let x,used = fresh used clos1.name in
      Pi ((x,d),equate used (do_clos clos1 (var x d1)) (do_clos clos2 (var x d2)) (U i))
    | Sg (d1,clos1), Sg (d2,clos2), U i ->
      let d = equate used d2 d1 (U i) in
      let x,used = fresh used clos1.name in
      Sg ((x,d),equate used (do_clos clos1 (var x d1)) (do_clos clos2 (var x d2)) (U i))
    | p1,p2, Sg (f,clos) ->
      let fst_p1 = do_fst p1 in
      Pair (equate used fst_p1 (do_fst p2) f, equate used (do_snd p1) (do_snd p2) (do_clos clos fst_p1)) 
    | Data d1, Data d2, U _ ->
      if String.equal d1.desc.name d2.desc.name
      then Data {name = d1.desc.name ; params = equate_params used d1.params d2.params d1.desc.params d1.desc.env} 
      else error (sprintf "%s != %s" d1.desc.name d2.desc.name)
    | Intro i1, Intro i2, Data {desc ; params} ->
      if not (String.equal i1.name i2.name) then error (sprintf "%s != %s" i1.name i2.name) else
      let args = equate_intro_args used i1.args i2.args (List.Assoc.find_exn ~equal:String.equal desc.cons i1.name) (apply_params desc desc.params params,params) in
      Intro {name = i1.name ; args}
    | Id (a1,m1,n1),Id (a2,m2,n2), U i ->
      Id (equate used a1 a2 (U i),equate used m1 m2 a1,equate used n1 n2 a1)
    | Refl x1, Refl x2, Id (a,_,_) ->
      Refl (equate used x1 x2 a)
    | Neutral n1,Neutral n2,_ -> equate_ne used n1.ne n2.ne
    | _ -> error (sprintf "equate - Inputs not convertible - %s != %s at %s" (Dom.show e1) (Dom.show e2) (Dom.show tp))

and equate_intro_args used args1 args2 dtele (desc,params) =
  match args1,args2,dtele with
    | [],[],[] -> []
    | arg1::args1,arg2::args2,(x,s)::dtele ->
      let arg = equate used arg1 arg2 (resolve_arg_tp (desc,params) s) in
      arg::equate_intro_args used args1 args2 dtele ({desc with env = Dom.Env.set desc.env ~key:x ~data:arg1},params)
    | _ -> error "Intro argument mismatch"
    
and equate_params used args1 args2 dtele env =
  match args1,args2,dtele with
    | [],[],[] -> []
    | arg1::args1,arg2::args2,(x,tp)::dtele ->
      let arg = equate used arg1 arg2 (eval env tp) in
      arg::equate_params used args1 args2 dtele (Dom.Env.set env ~key:x ~data:arg1)
    | _ -> error "Intro argument mismatch"

and equate_ne used ne1 ne2 =
  match ne1,ne2 with
    | Var x,Var y -> if String.equal x y then Var x else error (sprintf "%s != %s" x y)
    | Ap (f1,nf1),Ap (f2,nf2) -> Ap (equate_ne used f1 f2,equate used nf1.tm nf2.tm nf1.tp)
    | Fst ne1, Fst ne2 -> Fst (equate_ne used ne1 ne2)
    | Snd ne1, Snd ne2 -> Snd (equate_ne used ne1 ne2)
    | Elim e1,Elim e2 ->
      let x,used = fresh used e1.mot.name in
      Elim { mot = (x,equate used (do_clos e1.mot (var x (Data {desc = e1.desc ; params = e1.params}))) (do_clos e2.mot (var x (Data {desc=e2.desc;params=e2.params}))) (U Omega))
           ; arms = List.map2_exn e1.arms e2.arms ~f:(fun (con1,clos1) (_,clos2) ->
            let dtele = List.Assoc.find_exn e1.desc.cons ~equal:String.equal con1 in
            let args,env1 = collect_elim_args e1.mot clos1.names dtele (apply_params e1.desc e1.desc.params e1.params,e1.params) clos1.env in
            let _,env2 = collect_elim_args e2.mot clos2.names dtele (apply_params e2.desc e2.desc.params e2.params,e2.params) clos2.env in
            (con1,(clos1.names,equate used (eval env1 clos1.arm) (eval env2 clos2.arm) (do_clos e1.mot (Intro {name = con1 ; args}))))
           )
           ; scrut = equate_ne used e1.scrut e2.scrut
           }
    | J j1, J j2 ->
      let tp = j1.tp in
      let x,y,p,usedM = fresh3 used (j1.mot.names) in
      let z,usedB = fresh used (j1.body.name) in
      let mot = equate usedM (do_clos3 j1.mot (var x tp) (var y tp) (var p (Id (tp,var x tp, var y tp)))) 
                             (do_clos3 j2.mot (var x tp) (var y tp) (var p (Id (tp,var x tp, var y tp))))
                             (U Omega) in
      J { mot = (x,y,p,mot) 
        ; body = (z,equate usedB (do_clos j1.body (var z tp)) (do_clos j2.body (var z tp)) (do_clos3 j1.mot (var z tp) (var z tp) (Refl (var z tp)))) 
        ; scrut = equate_ne used j1.scrut j2.scrut
        }
    | Hole h1, Hole h2 when String.equal h1.name h2.name -> Hole {name = h1.name ; tp = equate used h1.tp h2.tp (U Omega)}
    | _ -> error "equate_ne - Inputs not convertible"

and collect_elim_args mot args dtele (desc,params) env =
  let f tp = function
    | `Arg x ->  
      let arg = var x tp in
      arg,Dom.Env.set env ~key:x ~data:arg
    | `Rec (x,r) -> 
      let arg = var x tp in
      let arg_r = var r (do_clos mot arg) in
      arg,env |> Dom.Env.set ~key:x ~data:arg |> Dom.Env.set ~key:r ~data:arg_r
  in 
  match args,dtele with
    | [],[] -> [],env
    | arg::args,(y,s)::dtele -> 
      let tp = resolve_arg_tp (desc,params) s in
      let arg,env = f tp arg in
      let args,env = collect_elim_args mot args dtele ({desc with env = Dom.Env.set desc.env ~key:y ~data:tp},params) env in
      arg::args,env
    | _ -> error "collect_elim_args NBE"


and read_back used e tp = equate used e e tp

and convertible used e1 e2 tp = (fun _ -> ()) (equate ~subtype:true used e1 e2 tp)

let convertible_b used e1 e2 tp = 
  try convertible used e1 e2 tp; true with
    | _ -> false
