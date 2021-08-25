open Core
open! Concrete_syntax

module Syn = Syntax
module Dom = Domain

exception ParseError of string

type loc = {line : int ; col : int}

let of_position (pos : Lexing.position) : loc =
  Lexing.{ line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 (* 1-indexed *) }

let show_loc {line ; col} = sprintf "%i:%i" line col

let parse s = 
  let lexbuf = Lexing.from_string s in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s-%s" (show_loc s) (show_loc e))

let parse_file s =
  let p = Stdlib.open_in s in
  let lexbuf = Lexing.from_channel p in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s:%s" (show_loc s) (show_loc e))


let normalize ~tm ~tp ~ctx =
  Nbe.read_back (Ctx.to_names ctx) (Nbe.eval (Ctx.to_env ctx) tm) tp


let run_stm ctx = function
  | Eval e ->
    let tp,tm = Elab.synth ctx e in 
    printf "_ : %s\n" (Syn.show (Nbe.read_back (Ctx.to_names ctx) tp (U Omega)));
    printf "_ = %s\n\n" (Syn.show (normalize ~tm ~tp ~ctx));
    ctx
  | Def (x,e) -> 
    let tp,e = Elab.synth ctx e in
    let e = Nbe.eval (Ctx.to_env ctx) e in
    printf "def %s\n\n" x;
    Ctx.add_def ctx ~var:x ~def:e ~tp
  | Axiom (x,tp) ->
    let tp = Nbe.eval (Ctx.to_env ctx) @@ Elab.check ctx tp (U Omega) in
    printf "axiom %s\n\n" x;
    Ctx.add_def ctx ~var:x ~def:(Nbe.var x tp) ~tp
  | Data {name ; cons ; params} -> 
    let desc = Elab.elab_data ctx name cons params in
    printf "data %s\n\n" name;
    Ctx.add_data ctx desc


let rec repl ctx = 
  print_string "-- ";
  let txt = Stdlib.read_line () in
  if String.equal txt "" then repl ctx;
  try repl @@ List.fold (parse txt) ~init:ctx ~f:run_stm with 
    | Elab.TypeError e -> printf "Type Error: %s\n" e;repl ctx
    | ParseError e -> printf "Parse Error: %s\n" e; repl ctx
    | Elab.Hole {goal ; ctx ; pos} ->
      printf "\nHole at %s:%s\n\n%s\n  %s\n" pos ctx (String.init ~f:(const '-') 45) goal;
      () 




let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl Ctx.empty;
  let s = parse_file args.(1) in
  try repl @@ List.fold s ~init:Ctx.empty ~f:run_stm with 
      | Elab.TypeError e -> printf "Type Error: %s\n" e
      | ParseError e -> printf "Parse Error: %s\n" e
      | Elab.Hole {goal ; ctx ; pos} ->
        printf "\nHole at %s:%s\n\n%s\n  %s\n" pos ctx (String.init ~f:(const '-') 45) goal;
        ()
