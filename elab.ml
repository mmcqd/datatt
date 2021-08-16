open Core

module CSyn = Concrete_syntax
module Syn = Syntax
module Dom = Domain

exception TypeError of string
exception Hole of {goal : string ; ctx : string}

let error s = raise (TypeError s)

let r = ref 0
let fresh () = r := !r + 1 ; "@"^Int.to_string !r 

let rec check (ctx : Ctx.t) (cs : CSyn.t) (tp : Dom.t) : Syn.t =
  (* printf "CHECK %s\n" (CSyn.show cs); *)
  match cs,tp with
    | Hole,tp -> raise (Hole {goal = Syn.show (Nbe.read_back (Ctx.to_names ctx) tp (U Omega)) ; ctx = Ctx.to_string ctx})
    | U i,U j when Level.(<) i j -> U i
    | U i, U j -> error (sprintf "Type^%s too large to be contained in Type^%s" (Level.show i) (Level.show j))
    | Pi ([],r), U i -> check ctx r (U i)
    | Pi ((x,d)::tele,r), U i ->
      let d = check ctx d (U i) in
      let pi = check (Ctx.add_syn ctx ~var:x ~tp:d) (Pi (tele,r)) (U i) in
      Pi ((x,d),pi)
    | Lam ([],e),tp -> check ctx e tp
    | Lam (x::xs,e),Pi (d,clos) -> 
      Lam (x,check (Ctx.add ctx ~var:x ~tp:d) (Lam (xs,e)) (Nbe.do_clos clos (Nbe.var x d)))
    | Var d,U _ when (match Ctx.find_data ctx d with Some _ -> true | _ -> false) -> Data d
    | Var con,Data desc when (match Ctx.find_tp ctx con with Some _ -> false | _ -> true) ->
      begin
      match List.Assoc.find ~equal:String.equal desc.cons con with
        | None -> error (sprintf "%s is not a constructor for type %s" con desc.name)
        | Some dtele -> Intro {name = con ; args = check_intro_args ctx [] dtele desc}
      end
    | Spine (Var con,args),Data desc when (match Ctx.find_tp ctx con with Some Pi _ -> false | _ -> true) -> 
      begin
      match List.Assoc.find ~equal:String.equal desc.cons con with
        | None -> error (sprintf "%s is not a constructor for type %s" con desc.name)
        | Some dtele -> Intro {name = con ; args = check_intro_args ctx (CSyn.spine_to_list args) dtele desc}
      end
    | Id (a,x,y), U i ->
      let a = check ctx a (U i) in
      let a' = Nbe.eval (Ctx.to_env ctx) a in
      Id (a,check ctx x a', check ctx y a')
    | Refl, Id (a,x,y) ->
      let x' = Nbe.equate (Ctx.to_names ctx) x y a in
      Refl x'
    | ElimFun arms, Pi (Data desc,clos) ->
      if not (List.equal String.equal (List.map ~f:fst desc.cons) (List.map ~f:fst arms)) then error "Elim arms don't match constructors" else
      let x = clos.name in
      Lam (x,Elim { mot = (x,clos.tm)
            ; scrut = Var x
            ; arms = List.map2_exn arms desc.cons ~f:(fun (con,(args,arm)) (_,dtele) -> 
              let dom_args,ctx = collect_elim_args clos args dtele desc ctx in
                 (con,(args,check ctx arm (Nbe.do_clos {clos with env = Ctx.to_env ctx} (Intro {name = con ; args = dom_args})))))
            })
    | _ ->
      let used = Ctx.to_names ctx in
      let tp',s = synth ctx cs in
      Nbe.convertible used tp' tp (U Omega);
      s

and check_intro_args ctx args dtele desc =
  match args,dtele with
    | [],Dom.Nil   -> []
    | [arg],One tp -> [check ctx arg (Nbe.resolve_arg_tp desc tp)]
    | arg::args,Cons ((x,tp),dtele) ->
      let arg = check ctx arg (Nbe.resolve_arg_tp desc tp) in
      arg::check_intro_args ctx args dtele {desc with env = String.Map.set desc.env ~key:x ~data:(Nbe.eval (Ctx.to_env ctx) arg)}
    | _ -> error "Incorrect number of args provided to constructor"

and synth (ctx : Ctx.t) (cs : CSyn.t) : Dom.t * Syn.t =
  (* printf "SYNTH %s\n" (CSyn.show cs); *)
  match cs with
    | Var x ->
      begin
      match Ctx.find_tp ctx x with
        | None -> error (sprintf "Unbound var `%s`" x)
        | Some tp -> tp, Var x
      end
    | Spine (e,Nil) -> synth ctx e
    | Spine (e,Snoc (spine,arg)) ->
      begin
      match synth ctx (Spine (e,spine)) with
        | Pi (d,clos),spine -> 
          let arg = check ctx arg d in
          Nbe.do_clos clos (Nbe.eval (Ctx.to_env ctx) arg), Ap (spine,arg)
        | _,spine-> error (sprintf "%s is not a function, it cannot be applied" (Syn.show spine))
      end
    | Ascribe {tm ; tp} ->
      let tp = Nbe.eval (Ctx.to_env ctx) (check ctx tp (U Omega)) in
      tp, check ctx tm tp
    | Elim {mot = Some (x,mot) ; scrut ; arms} ->
      begin
      match synth ctx scrut with
        | Data desc,scrut ->
          if not (List.equal String.equal (List.map ~f:fst desc.cons) (List.map ~f:fst arms)) then error "Elim arms don't match constructors" else
          let env = Ctx.to_env ctx in
          let mot_body = check (Ctx.add ctx ~var:x ~tp:(Data desc)) mot (U Omega) in
          let mot_clos = Dom.{name = x ; tm = mot_body ; env} in
          Nbe.do_clos mot_clos (Nbe.eval env scrut),
          Elim { mot = (x,mot_body) 
               ; scrut 
               ; arms = List.map2_exn arms desc.cons ~f:(fun (con,(args,arm)) (_,dtele) -> 
                 let dom_args,ctx = collect_elim_args mot_clos args dtele desc ctx in
                 (con,(args,check ctx arm (Nbe.do_clos {name = x ; tm = mot_body ; env = Ctx.to_env ctx} (Intro {name = con ; args = dom_args})))))}
        | _,scrut -> error (sprintf "%s is not a datatype, it cannot be eliminated" (Syn.show scrut))
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
        | _,scrut -> error (sprintf "%s is not an equality proof, it cannot be matched on" (Syn.show scrut))
      end   
    | _ -> error "Failed to synth/elaborate"



and collect_elim_args mot args dtele desc ctx =
  let f tp = function
    | `Arg x ->  
      let arg = Nbe.var x tp in
      arg,Ctx.add ctx ~var:x ~tp
    | `Rec (x,r) -> 
      match tp with
        | Data desc' when String.equal desc'.name desc.name ->
          let arg = Nbe.var x tp in
          arg,ctx |> Ctx.add ~var:x ~tp |> Ctx.add ~var:r ~tp:(Nbe.do_clos mot arg)
        | _ -> error (sprintf "%s does not have type %s, it cannot be recursively eliminated" x desc.name)
  in 
  match args,dtele with
    | [],Dom.Nil -> [],ctx
    | [arg],One s ->
      let tp = Nbe.resolve_arg_tp desc s in
      let arg,ctx = f tp arg in
      [arg],ctx
    | arg::args,Cons ((y,s),dtele) -> 
      let tp = Nbe.resolve_arg_tp desc s in
      let arg,ctx = f tp arg in
      let args,ctx = collect_elim_args mot args dtele {desc with env = String.Map.set desc.env ~key:y ~data:tp} ctx in
      arg::args,ctx
    | _ -> error "elim arm has incorrect number of args"


let rec elab_data ctx dname cons : Dom.desc =
  {name = dname ; env = Ctx.to_env ctx ; cons = List.map ~f:(fun (con,args) -> con,elab_con ctx dname args) cons }

and resolve_spec ctx dname = function
  | CSyn.Var x when String.equal x dname -> Dom.Rec
  | tp -> Tp (check ctx tp (U Omega))

and elab_con ctx dname args =
  match args with
    | [] -> Dom.Nil
    | [(_,arg)] -> One (resolve_spec ctx dname arg)
    | (x,arg)::args -> Cons ((x,resolve_spec ctx dname arg),elab_con (Ctx.add_syn ctx ~var:x ~tp:(check ctx arg (U Omega))) dname args)
