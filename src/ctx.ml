open Core
module Dom = Domain
module Syn = Syntax


type entry = 
  | Def of {tm : Dom.t ; tp : Dom.t}
  | Let of {tm : Dom.t ; tp : Dom.t}
  | Var of Dom.t
  | Data of Dom.desc

type t = entry String.Map.t

let empty = String.Map.empty


let to_env : t -> Dom.Env.t = String.Map.mapi ~f:(fun ~key ~data -> 
  match data with 
    | Var tp -> Dom.Tm (Dom.Neutral {ne = Var key ; tp})
    | Def {tm ; tp} -> Def {tm ; tp} 
    | Let {tm ; _} -> Tm tm
    | Data desc -> Desc desc)

let to_names = String.Map.key_set

let to_string c = 
  let used = to_names c in
  String.Map.fold c ~init:"" ~f:(fun ~key ~data s -> 
    match data with 
      | Var tp | Let {tp ; _}-> sprintf "%s\n  %s : %s" s key (Syntax.show (Nbe.read_back used tp (U Omega))) 
      | _ -> s
  )


let find_tp ctx x = 
  match String.Map.find ctx x with
    | None -> None
    | Some ((Var tp) | Def {tp ; _} | Let {tp ; _}) -> Some tp
    | Some (Data d) -> Some (Nbe.eval (to_env ctx) d.tp)

let find_def_tp ctx x = 
  match String.Map.find ctx x with
    | Some (Def {tp ; _}) -> Some tp
    | Some (Data d) -> Some (Nbe.eval (to_env ctx) d.tp)
    | _ -> None

let find_data ctx d =
  match String.Map.find ctx d with
    | Some (Data d) -> Some d
    | _ -> None

let find_data_exn ctx d = 
  match String.Map.find ctx d with
    | Some (Data d) -> d
    | _ -> failwith "find_data_exn"

let is_data ctx d =
  match String.Map.find ctx d with
    | Some (Data _) -> true
    | _ -> false


let add ctx ~var ~tp = String.Map.set ctx ~key:var ~data:(Var tp)
let add_syn ctx ~var ~tp = String.Map.set ctx ~key:var ~data:(Var (Nbe.eval (to_env ctx) tp))
let add_def ctx ~var ~def ~tp = String.Map.set ctx ~key:var ~data:(Def {tm = def ; tp})
let add_let ctx ~var ~def ~tp = String.Map.set ctx ~key:var ~data:(Let {tm = def ; tp})

let add_data ctx (d : Domain.desc) = String.Map.set ctx ~key:d.name ~data:(Data d)