open Core

module CSyn = Concrete_syntax
open CSyn
module Syn = Syntax
module Dom = Domain

exception TypeError of string
exception Hole of {goal : string ; ctx : string ; pos : string}

let error s = raise (TypeError s)

let r = ref 0
let fresh () = r := !r + 1 ; "@"^Int.to_string !r 


let sort_cons = List.sort ~compare: (fun (c1,_) (c2,_) -> String.compare c1 c2)

let rec check (ctx : Ctx.t) (cs : CSyn.t) (tp : Dom.t) : Syn.t =
  (* printf "CHECK %s AT %s\n" (CSyn.show cs) (Syn.show @@ Nbe.read_back (Ctx.to_names ctx) tp (U Omega)); *)
  match Mark.data cs,tp with
    | Hole name,tp -> 
    (* raise (Hole {goal = Syn.show (Nbe.read_back (Ctx.to_names ctx) tp (U Omega)) ; ctx = Ctx.to_string ctx ; pos = Mark.show cs}) *)
    let goal = Nbe.read_back (Ctx.to_names ctx) tp (U Omega) in
    printf "Hole %s at %s:%s\n\n⊢ %s\n\n" name (Mark.show cs) (Ctx.to_string ctx) (Syn.show goal);
    Hole {name ; tp = goal}

    | U Omega,U Omega -> U Omega (* VERY SUS but technically ok because user can't create terms of type U Omega *)
    | U i,U j when Level.(<) i j -> U i
    | U i, U j -> error (sprintf "%s - %s too large to be contained in %s" (Mark.show cs) (Syn.show (U i)) (Syn.show (U j)))
    | Pi ([],r), U i -> check ctx r (U i)
    | Pi ((x,d)::tele,r), U i ->
      let d = check ctx d (U i) in
      let pi = check (Ctx.add_syn ctx ~var:x ~tp:d) (Mark.naked @@ Pi (tele,r)) (U i) in
      Pi ((x,d),pi)
    | Sg ([],r), U i -> check ctx r (U i)
    | Sg ((x,d)::tele,r), U i ->
      let d = check ctx d (U i) in
      let sg = check (Ctx.add_syn ctx ~var:x ~tp:d) (Mark.naked @@ Sg (tele,r)) (U i) in
      Sg ((x,d),sg)
    | Let ((x,e1),e2),tp ->
      let e1_tp,e1' = synth ctx e1 in
      let e2' = check (Ctx.add_let ctx ~var:x ~def:(Nbe.eval (Ctx.to_env ctx) e1') ~tp:e1_tp) e2 tp in
      Let ((x,e1'),e2')
    | Lam ([],e),tp -> check ctx e tp
    | Lam (x::xs,e),Pi (d,clos) -> 
      Lam (x,check (Ctx.add ctx ~var:x ~tp:d) (Mark.naked @@ Lam (xs,e)) (Nbe.do_clos clos (Nbe.var x d)))
    (* | Fun {name ; args = x::xs ; body},Pi (d,clos) ->
      Fun (name,x,check (ctx |> Ctx.add ~var:name ~tp |> Ctx.add ~var:x ~tp:d) (Mark.naked @@ Lam (xs,body)) (Nbe.do_clos clos (Nbe.var x d))) *)
    | Tuple [x],tp -> check ctx x tp
    | Tuple (x::xs),Sg (f,clos) -> 
      let x' = check ctx x f in
      Pair (x',check ctx (Mark.naked @@ Tuple xs) (Nbe.do_clos clos (Nbe.eval (Ctx.to_env ctx) x')))
    | Var d,U _ when (match Ctx.find_data ctx d with Some _ -> true | _ -> false) -> Data {name = d ; params = []}
    | Spine (f,args),U _ ->
      begin
      match Mark.data f with
        | Var d -> 
          begin
          match Ctx.find_data ctx d with
            | Some desc -> Data {name = d ; params = check_params ctx (CSyn.spine_to_list args) desc.params desc }
            | _ -> mode_switch ctx cs tp
          end 
        | _ -> mode_switch ctx cs tp
      end
    | Var con,Data {desc ; params} when (match Ctx.find_tp ctx con with Some _ -> false | _ -> true) ->
      begin
      match List.Assoc.find ~equal:String.equal desc.cons con with
        | None -> error (sprintf "%s - %s is not a constructor for type %s" (Mark.show cs) con (Syn.show (Nbe.read_back (Ctx.to_names ctx) tp (U Omega))))
        | Some dtele -> Intro {name = con ; args = check_intro_args ctx [] dtele (Nbe.apply_params desc desc.params params,params)}
      end
    | Spine (f,args),Data {desc ; params} -> 
      begin
      match Mark.data f with
        | Var con when (match Ctx.find_tp ctx con with Some Pi _ -> false | _ -> true) ->
          begin
          match List.Assoc.find ~equal:String.equal desc.cons con with
            | None -> error (sprintf "%s - %s is not a constructor for type %s" (Mark.show cs) con desc.name)
            | Some dtele -> 
              try Intro {name = con ; args = check_intro_args ctx (CSyn.spine_to_list args) dtele (Nbe.apply_params desc desc.params params,params)} with
                | TypeError s -> error (sprintf "%s - %s" (Mark.show cs) s)
          end
        | _ -> mode_switch ctx cs tp
      end
    | Id (a,x,y), U i ->
      let a = check ctx a (U i) in
      let a' = Nbe.eval (Ctx.to_env ctx) a in
      Id (a,check ctx x a',check ctx y a')
    | Refl, Id (a,x,y) ->
      begin
      try Refl (Nbe.equate (Ctx.to_names ctx) x y a) with
        | Nbe.EquateError _ -> 
          let used = Ctx.to_names ctx in
          error (sprintf "%s - %s !<= %s" (Mark.show cs) (Syn.show @@ Nbe.read_back used x a) (Syn.show @@ Nbe.read_back used y a))
      end
    | ElimFun arms, Pi (Data {desc;params},clos) ->
      let arms = sort_cons arms in
      if not (List.equal String.equal (List.map ~f:fst desc.cons) (List.map ~f:fst arms)) then error (sprintf "%s - Elim arms don't match constructors" (Mark.show cs))else
      let x = match clos.name with "_" -> fresh () | x -> x in
      Lam (x,Elim { mot = (x,Nbe.read_back (Ctx.to_names ctx) (Nbe.do_clos clos (Nbe.var x (Data {desc;params}))) (U Omega))
            ; scrut = Var x
            ; arms = List.map2_exn arms desc.cons ~f:(fun (con,(args,arm)) (_,dtele) -> 
              let dom_args,ctx = collect_elim_args (Mark.show cs) clos args dtele (Nbe.apply_params desc desc.params params,params) ctx in
                 (con,(args,check ctx arm (Nbe.do_clos clos (Intro {name = con ; args = dom_args})))))
            })
    | Elim {mot = None ; scrut ; arms}, tp ->
      let arms = sort_cons arms in
      begin
      match synth ctx scrut with
        | Data {desc;params},scrut ->
          if not (List.equal String.equal (List.map ~f:fst desc.cons) (List.map ~f:fst arms)) then error (sprintf "%s - Elim arms don't match constructors" (Mark.show cs)) else
          let used = Ctx.to_names ctx in
          let tp_syn = Nbe.read_back used tp (U Omega) in
          let x = fresh () in
          let mot_body = Syn.subst (Var x) scrut tp_syn in
          (* print_endline (sprintf "GUSSED MOT: %s => %s" x (Syn.show mot_body)); *)
          let ctx' = ctx |> Ctx.add ~var:x ~tp:(Data {desc;params}) in
          (try const () @@ check ctx' (Syn.to_concrete mot_body) (U Omega) with TypeError s -> error (sprintf "%s - In guessed motive: %s" (Mark.show cs) s));
          let mot_clos = Dom.{name = x ; tm = mot_body ; env = Ctx.to_env ctx} in
          Elim { mot = (x,mot_body) 
               ; scrut 
               ; arms = List.map2_exn arms desc.cons ~f:(fun (con,(args,arm)) (_,dtele) -> 
                 let dom_args,ctx = collect_elim_args (Mark.show cs) mot_clos args dtele (Nbe.apply_params desc desc.params params,params) ctx in
                 let arm_tp = Nbe.do_clos mot_clos (Intro {name = con ; args = dom_args}) in
                 (* print_endline ("ARM_TYPE: "^Dom.show arm_tp);
                 print_endline ("ARM: "^CSyn.show arm); *)
                 (con,(args,check ctx arm arm_tp)))}
        | _,scrut' -> error (sprintf "%s - %s is not a datatype, it cannot be eliminated" (Mark.show scrut) (Syn.show scrut'))
      end
    | J {mot = None ; body = (z,e) ; scrut}, tp ->
      begin
      match synth ctx scrut with
        | Id (a,e1,e2),scrut ->
          let used = Ctx.to_names ctx in
          let tp_syn = Nbe.read_back used tp (U Omega) in
          let p,y,x = fresh (), fresh (), fresh () in
          let e1',e2' = Nbe.read_back used e1 a,Nbe.read_back used e2 a in
          (* mot_body needs to be typechecked in case we guessed a type-incorrect motive *)
          let mot_body = tp_syn 
                        |> Syn.subst (Var x) e1'
                        (* e2' might contain e1', so we have to perform the same substitution inside of e2'. This seems sus *)
                        |> Syn.subst (Var y) (Syn.subst (Var x) e1' e2')
                        |> Syn.subst (Var p) scrut in
          (* print_endline (sprintf "GUSSED MOT: %s" (Syn.show mot_body)); *)
          let ctx' = ctx |> Ctx.add ~var:x ~tp:a |> Ctx.add ~var:y ~tp:a |> Ctx.add ~var:p ~tp:(Id (a,Nbe.var x a,Nbe.var y a)) in
          (try const () @@ check ctx' (Syn.to_concrete mot_body) (U Omega) with TypeError s -> error (sprintf "%s - In guessed motive %s: %s" (Mark.show cs) (Syn.show mot_body) s));
          let body_tp = Nbe.do_clos3 Dom.{names = (x,y,p) ; tm = mot_body ; env = Ctx.to_env ctx} (Nbe.var z a) (Nbe.var z a) (Refl (Nbe.var z a)) in
          let body = (z,check (Ctx.add ctx ~var:z ~tp:a) e body_tp ) in
          J {mot = (x,y,p,mot_body) ; body ; scrut}

        | _,scrut -> error (sprintf "%s - %s is not an equality proof, it cannot be matched on" (Mark.show cs) (Syn.show scrut))
      end 
    | Absurd, Pi (Id (Data _,Intro i1, Intro i2) as id,r) ->
      let used = Ctx.to_names ctx in
      if String.equal i1.name i2.name then error (sprintf "%s - fn () can only derive absurdity from non-equal outermost constructors, %s is not an absurd equality" (Mark.show cs) (Syn.show (Nbe.read_back used id (U Omega)))) 
      else Lam (r.name,Var r.name)
    | _ -> mode_switch ctx cs tp

and check_intro_args ctx args dtele (desc,params) =
  match args,dtele with
    | [],[]   -> []
    | arg::args,(x,tp)::dtele ->
      let arg = check ctx arg (Nbe.resolve_arg_tp (desc,params) tp) in
      arg::check_intro_args ctx args dtele ({desc with env = Dom.Env.set desc.env ~key:x ~data:(Nbe.eval (Ctx.to_env ctx) arg)},params)
    | _ -> error "Incorrect number of args provided to constructor"

and check_params ctx args dtele desc =
  match args,dtele with
    | [],[]   -> []
    | arg::args,(x,tp)::dtele ->
      let tp = Nbe.eval desc.env tp in
      let arg = check ctx arg tp in
      arg::check_params ctx args dtele {desc with env = Dom.Env.set desc.env ~key:x ~data:(Nbe.eval (Ctx.to_env ctx) arg)}
    | _ -> error "Incorrect number of args provided to data"

and mode_switch ctx cs tp =
  let used = Ctx.to_names ctx in
  let tp',s = synth ctx cs in
  (try Nbe.convertible used tp' tp (U Omega) with
    | Nbe.EquateError _ -> error (sprintf "%s - %s !<= %s" (Mark.show cs) (Syn.show @@ Nbe.read_back used tp' (U Omega)) (Syn.show @@ Nbe.read_back used tp (U Omega))));
  s


and synth (ctx : Ctx.t) (cs : CSyn.t) : Dom.t * Syn.t =
  (* printf "SYNTH %s\n" (CSyn.show cs); *)
  match Mark.data cs with
    | Var x ->
      begin
      match Ctx.find_tp ctx x with
        | None -> error (sprintf "%s - Unbound var `%s`" (Mark.show cs) x)
        | Some tp -> tp, Var x
      end
    | Lift {name ; lvl} ->
      begin
      match Ctx.find_def_tp ctx name with
        | None -> error (sprintf "%s - Cannot lift non-toplevel definition `%s`" (Mark.show cs) name)
        | Some tp -> Dom.lift lvl tp, Lift {name ; lvl}
      end
    | Spine (e,Nil) -> synth ctx e
    | Spine (e,Snoc (spine,arg)) ->
      begin
      match synth ctx (Mark.naked @@ Spine (e,spine)) with
        | Pi (d,clos),spine -> 
          let arg = check ctx arg d in
          Nbe.do_clos clos (Nbe.eval (Ctx.to_env ctx) arg), Ap (spine,arg)
        | _,spine-> error (sprintf "%s - %s is not a function, it cannot be applied" (Mark.show cs) (Syn.show spine))
      end
    | Ascribe {tm ; tp} ->
      let tp = Nbe.eval (Ctx.to_env ctx) (check ctx tp (U Omega)) in
      tp, check ctx tm tp
    | Let ((x,e1),e2) ->
      let e1_tp,e1' = synth ctx e1 in
      let e2_tp,e2' = synth (Ctx.add_let ctx ~var:x ~def:(Nbe.eval (Ctx.to_env ctx) e1') ~tp:e1_tp) e2 in
      e2_tp,Let ((x,e1'),e2')  
    | Fst p ->
      begin
      match synth ctx p with
        | Sg (f,_),p -> f,Fst p
        | _,p -> error (sprintf "%s - %s is not a pair, it cannot be projected from" (Mark.show cs) (Syn.show p))
      end
    | Snd p ->
      begin
      match synth ctx p with
        | Sg (_,clos),p -> Nbe.do_clos clos (Nbe.do_fst (Nbe.eval (Ctx.to_env ctx) p)),Snd p
        | _,p -> error (sprintf "%s - %s is not a pair, it cannot be projected from" (Mark.show cs) (Syn.show p))
      end
    | Elim {mot = Some (x,mot) ; scrut ; arms} ->
      let arms = sort_cons arms in
      begin
      match synth ctx scrut with
        | Data {desc;params},scrut ->
          if not (List.equal String.equal (List.map ~f:fst desc.cons) (List.map ~f:fst arms)) then error (sprintf "%s - Elim arms don't match constructors" (Mark.show cs)) else
          let env = Ctx.to_env ctx in
          let mot_body = check (Ctx.add ctx ~var:x ~tp:(Data {desc;params})) mot (U Omega) in
          let mot_clos = Dom.{name = x ; tm = mot_body ; env} in
          Nbe.do_clos mot_clos (Nbe.eval env scrut),
          Elim { mot = (x,mot_body) 
               ; scrut 
               ; arms = List.map2_exn arms desc.cons ~f:(fun (con,(args,arm)) (_,dtele) -> 
                 let dom_args,ctx = collect_elim_args (Mark.show cs) mot_clos args dtele (Nbe.apply_params desc desc.params params,params) ctx in
                 (con,(args,check ctx arm (Nbe.do_clos mot_clos (Intro {name = con ; args = dom_args})))))}
        | _,scrut' -> error (sprintf "%s - %s is not a datatype, it cannot be eliminated" (Mark.show scrut) (Syn.show scrut'))
      end
    | J {mot = Some (x,y,p,m) ; body = (z,e) ; scrut} ->
      begin
      match synth ctx scrut with
        | Id (a,e1,e2),scrut ->
          let env = Ctx.to_env ctx in
          let mot_body = check (ctx |> Ctx.add ~var:x ~tp:a |> Ctx.add ~var:y ~tp:a |> Ctx.add ~var:p ~tp:(Id (a,Nbe.var x a,Nbe.var y a))) m (U Omega) in
          let body_tp = Nbe.do_clos3 Dom.{names = (x,y,p) ; tm = mot_body ; env} (Nbe.var z a) (Nbe.var z a) (Refl (Nbe.var z a)) in
          let body = (z,check (Ctx.add ctx ~var:z ~tp:a) e body_tp) in
          Nbe.do_clos3 Dom.{names = (x,y,p) ; tm = mot_body ; env} e1 e2 (Nbe.eval env scrut), J {mot = (x,y,p,mot_body) ; body ; scrut}
        | _,scrut' -> error (sprintf "%s - %s is not a datatype, it cannot be eliminated" (Mark.show scrut) (Syn.show scrut'))
      end   
    | _ -> error (sprintf "%s - Failed to synth/elaborate" (Mark.show cs))



and collect_elim_args pos mot args dtele (desc,params) ctx =
  let f tp = function
    | `Arg x ->  
      let arg = Nbe.var x tp in
      arg,Ctx.add ctx ~var:x ~tp
    | `Rec (x,r) -> 
      match tp with
        | Data d' when String.equal d'.desc.name desc.name ->
          let arg = Nbe.var x tp in
          arg,ctx |> Ctx.add ~var:x ~tp |> Ctx.add ~var:r ~tp:(Nbe.do_clos mot arg)
        | _ -> error (sprintf "%s - %s does not have type %s, it cannot be recursively eliminated" pos x desc.name)
  in 
  match args,dtele with
    | [],[] -> [],ctx
    | arg::args,(y,s)::dtele -> 
      let tp = Nbe.resolve_arg_tp (desc,params) s in
      let arg,ctx = f tp arg in
      let args,ctx = collect_elim_args pos mot args dtele ({desc with env = Dom.Env.set desc.env ~key:y ~data:arg},params) ctx in
      arg::args,ctx
    | _ -> error (sprintf "%s - Elim arm has incorrect number of args" pos)


let rec elab_data ctx dname (cons : CSyn.t bnd list bnd list) (params : CSyn.t bnd list) : Dom.desc =
  let ps,pctx = elab_params ctx params in
  { name = dname 
  ; env = Ctx.to_env ctx 
  ; params = ps
  ; cons = sort_cons @@ 
           List.map ~f:(fun (con,args) -> con,elab_con (Ctx.add pctx ~var:dname ~tp:(U (Const 0))) dname args) cons }


and elab_params ctx = function
  | [] -> [],ctx
  | (x,tp)::ps ->
    let tp = check ctx tp (U Omega) in
    let ps,ctx = elab_params (Ctx.add_syn ctx ~var:x ~tp) ps in
    (x,tp)::ps,ctx

and resolve_spec ctx dname arg =
  match Mark.data arg with
    | CSyn.Var x when String.equal x dname -> Dom.Rec
    | _ -> Tp (check ctx arg (U Omega))

and elab_con ctx dname args =
  match args with
    | [] -> []
    | (x,arg)::args -> 
      let arg = resolve_spec ctx dname arg in
      let tp = match arg with Tp tp -> tp | Rec -> Var dname in
      (x,arg)::elab_con (Ctx.add_syn ctx ~var:x ~tp) dname args

