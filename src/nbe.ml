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
    | Lift {name ; lvl} -> 
        let Dom.{tm;tp} = Dom.Env.find_def_exn env name in
        eval env (Syn.lift lvl (read_back (Dom.Env.key_set env) tm tp))
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
    | RecordTy fs -> RecordTy (fs,env)
    | Record fs -> Record (eval_record env fs)
    | Proj (f,e) -> do_proj f (eval env e)
    | Id (a,m,n) -> Id (eval env a,eval env m,eval env n)
    | Refl x -> Refl (eval env x)
    | J {mot = (x,y,p,m); body = (z,e) ; scrut} -> do_j Dom.{names = (x,y,p) ; tm = m ; env} Dom.{name = z ; tm = e ; env} (eval env scrut)
    | Let ((x,e1),e2) -> eval (Dom.Env.set env ~key:x ~data:(eval env e1)) e2 
    | Hole {name ; tp} -> let tp = eval env tp in Neutral {ne = Hole {name ; tp} ; tp}

and do_clos ({name ; tm ; env } : Dom.clos) (arg : Dom.t) : Dom.t =
  eval (Dom.Env.set env ~key:name ~data:arg) tm


and do_clos3 ({names = (x,y,z) ; tm ; env } : Dom.clos3) (a : Dom.t) (b : Dom.t) (c : Dom.t) : Dom.t =
  eval (env |> Dom.Env.set ~key:x ~data:a |> Dom.Env.set ~key:y ~data:b |> Dom.Env.set ~key:z ~data:c) tm

and eval_record env = function
  | [] -> []
  | (f,e)::fs -> 
    let e = eval env e in
    (f,e)::eval_record (Dom.Env.set env ~key:f ~data:e) fs

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

and do_proj (f : string) (r : Dom.t) : Dom.t =
  match r with
    | Record fs -> List.Assoc.find_exn ~equal:String.equal fs f
    | Neutral {tp = RecordTy (fs,env) ; ne} -> Neutral {tp = do_proj_tp f fs env ; ne = Proj (f,ne) }
    | _ -> failwith "do_proj"

and do_proj_tp f fs env =
  match fs with
    | [] -> failwith "do_proj_tp"
    | (f',tp)::fs -> if String.equal f f' then eval env tp else
      do_proj_tp f fs (Dom.Env.set env ~key:f' ~data:(var f' (eval env tp)))

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

and fresh used x = if String.equal x "_" then x,used else
  let rec go x = 
    if String.Set.mem used x then go (x ^ "'") else x
  in let y = go x in
  y,String.Set.add used y

and fresh3 used (x,y,z) =
  let x,used = fresh used x in
  let y,used = fresh used y in
  let z,used = fresh used z in
  (x,y,z,used)


and resolve_name used (f : Dom.t) (x : string) =
  match f,x with
    | Lam clos,"_" -> clos.name,used
    | _,"_" -> fresh used "x"
    | _ -> fresh used x

and resolve_arg_tp (desc,params) : Dom.spec -> Dom.t = function
  | Rec -> Data {desc ; params}
  | Tp tp -> eval desc.env tp

and apply_params (desc : Dom.desc) param_tps ps =
  match param_tps,ps with
    | [],[] -> desc
    | (x,_)::param_tps,p::ps ->
      apply_params {desc with env = Dom.Env.set desc.env ~key:x ~data:p} param_tps ps
    | _ -> failwith "apply_params"


and equate ?(subtype = false) (used : String.Set.t) (e1 : Dom.t) (e2 : Dom.t) (tp : Dom.t) : Syn.t =
  (* printf "-----\nEQUATING\n%s\nWITH\n%s\nAT\n%s\n-----\n" (Dom.show e1) (Dom.show e2) (Dom.show tp); *)
  match e1,e2,tp with
    | U i, U j, U _ -> 
      if subtype then 
        if Level.(<=) i j then U i else error (sprintf "Level Error: %s !<= %s" (Level.show i) (Level.show j))
      else
        if Level.equal i j then U i else error (sprintf "Level Error: %s !<= %s" (Level.show i) (Level.show j))
    | f1,f2, Pi (d,clos) -> 
      let x,used = resolve_name used f1 (clos.name) in
      Lam (x,equate ~subtype used (do_ap f1 (var x d)) (do_ap f2 (var x d)) (do_clos clos (var x d)))
    | Pi (d1,clos1), Pi (d2,clos2), U i ->
      let d = equate ~subtype used d2 d1 (U i) in
      let x,used = fresh used clos1.name in
      Pi ((x,d),equate ~subtype used (do_clos clos1 (var x d1)) (do_clos clos2 (var x d2)) (U i))
    | Sg (d1,clos1), Sg (d2,clos2), U i ->
      let d = equate ~subtype used d2 d1 (U i) in
      let x,used = fresh used clos1.name in
      Sg ((x,d),equate ~subtype used (do_clos clos1 (var x d1)) (do_clos clos2 (var x d2)) (U i))
    | RecordTy (fs1,env1), RecordTy (fs2,env2), U i -> 
      let q = List.fold2 fs1 fs2 ~init:([],env1,env2) ~f:(fun (r,env1,env2) (f1,tp1) (f2,tp2) -> 
        if not (String.equal f1 f2) then error "non_equal fields" else
        let tp1 = eval env1 tp1 in
        let tp2 = eval env2 tp2 in
        (f1,equate ~subtype used tp1 tp2 (U i))::r,Dom.Env.set env1 ~key:f1 ~data:(var f1 tp1),Dom.Env.set env2 ~key:f2 ~data:(var f2 tp2)
      ) in
      begin
      match q with
        | Ok (fs,_,_) -> RecordTy (List.rev fs)
        | Unequal_lengths -> error "unequal length records"
      end
    | r1,r2, RecordTy (fs,env) ->
        let q = List.fold fs ~init:([],env) ~f:(fun (r,env) (f,tp) -> 
        let p1 = do_proj f r1 in
        let p = equate ~subtype used p1 (do_proj f r2) (eval env tp) in
        ((f,p)::r,Dom.Env.set env ~key:f ~data:p1)
      ) in Record (List.rev @@ fst q)
    | p1,p2, Sg (f,clos) ->
      let fst_p1 = do_fst p1 in
      Pair (equate ~subtype used fst_p1 (do_fst p2) f, equate ~subtype used (do_snd p1) (do_snd p2) (do_clos clos fst_p1)) 
    | Data d1, Data d2, U _ ->
      if String.equal d1.desc.name d2.desc.name
      then Data {name = d1.desc.name ; params = equate_params ~subtype used d1.params d2.params d1.desc.params d1.desc.env} 
      else error (sprintf "%s != %s" d1.desc.name d2.desc.name)
    | Intro i1, Intro i2, Data {desc ; params} ->
      if not (String.equal i1.name i2.name) then error (sprintf "%s != %s" i1.name i2.name) else
      let args = equate_intro_args ~subtype used i1.args i2.args (List.Assoc.find_exn ~equal:String.equal desc.cons i1.name) (apply_params desc desc.params params,params) in
      Intro {name = i1.name ; args}
    | Id (a1,m1,n1),Id (a2,m2,n2), U i ->
      Id (equate ~subtype used a1 a2 (U i),equate ~subtype used m1 m2 a1,equate ~subtype used n1 n2 a1)
    | Refl x1, Refl x2, Id (a,_,_) ->
      Refl (equate ~subtype used x1 x2 a)
    | Neutral n1,Neutral n2,_ -> equate_ne ~subtype used n1.ne n2.ne
    | _ -> error (sprintf "equate - Inputs not convertible - %s != %s at %s" (Dom.show e1) (Dom.show e2) (Dom.show tp))

and equate_intro_args ~subtype used args1 args2 dtele (desc,params) =
  match args1,args2,dtele with
    | [],[],[] -> []
    | arg1::args1,arg2::args2,(x,s)::dtele ->
      let arg = equate ~subtype used arg1 arg2 (resolve_arg_tp (desc,params) s) in
      arg::equate_intro_args ~subtype used args1 args2 dtele ({desc with env = Dom.Env.set desc.env ~key:x ~data:arg1},params)
    | _ -> error (sprintf "Intro argument mismatch - %s %s" (List.to_string ~f:Dom.show args1) (List.to_string ~f:Dom.show args2))
    
and equate_params ~subtype used args1 args2 dtele env =
  match args1,args2,dtele with
    | [],[],[] -> []
    | arg1::args1,arg2::args2,(x,tp)::dtele ->
      let arg = equate ~subtype used arg1 arg2 (eval env tp) in
      arg::equate_params ~subtype used args1 args2 dtele (Dom.Env.set env ~key:x ~data:arg1)
    | _ -> error (sprintf "Param argument mismatch - %s %s" (List.to_string ~f:Dom.show args1) (List.to_string ~f:Dom.show args2))

and equate_ne ~subtype used ne1 ne2 =
  match ne1,ne2 with
    | Var x,Var y -> if String.equal x y then Var x else error (sprintf "%s != %s" x y)
    | Ap (f1,nf1),Ap (f2,nf2) -> Ap (equate_ne ~subtype used f1 f2,equate ~subtype used nf1.tm nf2.tm nf1.tp)
    | Fst ne1, Fst ne2 -> Fst (equate_ne ~subtype used ne1 ne2)
    | Snd ne1, Snd ne2 -> Snd (equate_ne ~subtype used ne1 ne2)
    | Proj (f1,ne1), Proj (f2,ne2) -> if String.equal f1 f2 then Proj (f1,equate_ne ~subtype used ne1 ne2) else error (sprintf "Different projections: %s != %s" f1 f2)
    | Elim e1,Elim e2 ->
      let x,used = fresh used e1.mot.name in
      Elim { mot = (x,equate ~subtype used (do_clos e1.mot (var x (Data {desc = e1.desc ; params = e1.params}))) (do_clos e2.mot (var x (Data {desc=e2.desc;params=e2.params}))) (U Omega))
           ; arms = List.map2_exn e1.arms e2.arms ~f:(fun (con1,clos1) (_,clos2) ->
            let dtele = List.Assoc.find_exn e1.desc.cons ~equal:String.equal con1 in
            let args,env1 = collect_elim_args e1.mot clos1.names dtele (apply_params e1.desc e1.desc.params e1.params,e1.params) clos1.env in
            let _,env2 = collect_elim_args e2.mot clos2.names dtele (apply_params e2.desc e2.desc.params e2.params,e2.params) clos2.env in
            (con1,(clos1.names,equate ~subtype used (eval env1 clos1.arm) (eval env2 clos2.arm) (do_clos e1.mot (Intro {name = con1 ; args}))))
           )
           ; scrut = equate_ne ~subtype used e1.scrut e2.scrut
           }
    | J j1, J j2 ->
      let tp = j1.tp in
      let x,y,p,usedM = fresh3 used (j1.mot.names) in
      let z,usedB = fresh used (j1.body.name) in
      let mot = equate ~subtype usedM (do_clos3 j1.mot (var x tp) (var y tp) (var p (Id (tp,var x tp, var y tp)))) 
                             (do_clos3 j2.mot (var x tp) (var y tp) (var p (Id (tp,var x tp, var y tp))))
                             (U Omega) in
      J { mot = (x,y,p,mot) 
        ; body = (z,equate ~subtype usedB (do_clos j1.body (var z tp)) (do_clos j2.body (var z tp)) (do_clos3 j1.mot (var z tp) (var z tp) (Refl (var z tp)))) 
        ; scrut = equate_ne ~subtype used j1.scrut j2.scrut
        }
    | Hole h1, Hole h2 when String.equal h1.name h2.name -> Hole {name = h1.name ; tp = equate ~subtype used h1.tp h2.tp (U Omega)}
    | _ -> error "equate_ne - Inputs not convertible"



and collect_elim_args mot args dtele (desc,params) env =
  match args,dtele with
    | [],[] -> [],env
    | arg::args,(y,s)::dtele ->
      begin
      match arg with
        | `Arg x ->
          let tp = resolve_arg_tp (desc,params) s in
          let arg = var x tp in
          let env = Dom.Env.set env ~key:x ~data:arg in
          let args,env = collect_elim_args mot args dtele ({desc with env = Dom.Env.set desc.env ~key:y ~data:tp},params) env in
          arg::args,env
        | `Rec (x,ih) ->
          let tp = resolve_arg_tp (desc,params) s in
          let arg = var x tp in
          let arg_ih = var ih (do_clos mot arg) in
          let env = env |> Dom.Env.set ~key:x ~data:arg |> Dom.Env.set ~key:ih ~data:arg_ih in
          let args,env = collect_elim_args mot args dtele ({desc with env = Dom.Env.set desc.env ~key:y ~data:tp},params) env in
          arg::args,env
      end
    | _ -> error "collect_elim_args NBE"


and read_back used e tp = equate used e e tp

and convertible used e1 e2 tp = (fun _ -> ()) (equate ~subtype:true used e1 e2 tp)

let convertible_b used e1 e2 tp = 
  try convertible used e1 e2 tp; true with
    | _ -> false

