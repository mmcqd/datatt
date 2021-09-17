%{

open Core.List

let rec args_to_tele = function
  | [] -> []
  | (xs,t)::args -> map xs ~f:(fun x -> (x,t)) @ args_to_tele args

let func_syntax (args,t,e) =
  let tele = args_to_tele args in
  (Mark.naked @@ Concrete_syntax.Lam (map ~f:fst tele,e), Mark.naked @@ Concrete_syntax.Pi (tele,t))

(*
let rec_func_syntax (name,args,t,e) =
  let tele = args_to_tele args in
  (Mark.naked @@ Concrete_syntax.Fun {name ; args = map ~f:fst tele ; body = e},Mark.naked @@ Concrete_syntax.Pi (tele,t))
*)

let hole_count = ref (-1)
let new_hole () = hole_count := (!hole_count) + 1; Int.to_string (!hole_count)

%}

%token Eof
%token Import
%token Question_mark
%token L_paren R_paren L_angle R_angle
%token Lambda Thick_arrow Arrow
%token Comma DotOne DotTwo Star
%token Dot Sig Struct Extends
%token Let In
%token Type Caret
%token Colon Semicolon
%token Underbar
%token Id Refl
%token Match With Bar At
%token Data Elim F_slash
%token Def Equal Axiom
%token <string> Ident
%token <int> Dec_const


%right Arrow
%right Star

%type <Concrete_syntax.cmd list> init

%start init

%%


let m(x) :=
  | x = x; { Mark.mark x (Mark.of_positions $startpos(x) $endpos(x))}
  

let paren(x) == L_paren; ~ = x; R_paren; <>

let init := ~ = nonempty_list(cmd); Eof; <>


let cmd := 
  | Def; ~ = bound_name; Equal; ~ = m(term); <Concrete_syntax.Def>
  | Def; x = bound_name; Colon; tp = m(term); Equal; tm = m(term); { Concrete_syntax.Def (x, Mark.naked @@ Concrete_syntax.Ascribe {tp ; tm}) } 
  | Def; x = bound_name; args = nonempty_list(paren(annot_args)); Colon; t = m(term); Equal; e = m(term); 
    { let tm,tp = func_syntax (args,t,e) in
      Concrete_syntax.Def (x,Mark.naked @@ Concrete_syntax.Ascribe {tm ; tp}) 
    }
  | Axiom; x = bound_name; Colon; tp = m(term); { Concrete_syntax.Axiom (x,tp) }
  | data_def
  | Import; f = Ident; { Concrete_syntax.Import f }
  | ~ = m(term); <Concrete_syntax.Eval>

let data_def :=
  | Data; params = list(paren(annot_args)); name = bound_name; lvl = data_def_lvl; 
    { Concrete_syntax.Data {name ; cons = [] ; params = args_to_tele params ; lvl}}
  | Data; params = list(paren(annot_args)); name = bound_name; lvl = data_def_lvl; Equal;
    option(Bar); cons = separated_nonempty_list(Bar,con);
      { Concrete_syntax.Data {name ; cons ; params = args_to_tele params ; lvl}}

let data_def_lvl :=
  | { Level.Const 0 }
  | Colon; Type; { Level.Const 0 }
  | Colon; Type; Caret; n = Dec_const; { Level.Const n }

let con :=
  name = bound_name; args = list(paren(annot_args));
    { (name,args_to_tele args) }

let bound_name :=
  | Ident
  | Underbar; { "_" }

let hole :=
  | Ident
  | { new_hole () }

let annot_args :=
  | ~ = nonempty_list(bound_name); Colon ; ~ = m(term) ; <>



let atomic :=
  | paren(term)
  | Question_mark; x = hole; { Concrete_syntax.Hole ("?" ^ x) }
  | x = Ident; { Concrete_syntax.Var x }
  | name = Ident; Caret; lvl = Dec_const; { Concrete_syntax.Lift {name ; lvl} }
  | ~ = paren(separated_list(Comma,m(term))); <Concrete_syntax.Tuple>
  | ~ = m(atomic); DotOne; <Concrete_syntax.Fst>
  | ~ = m(atomic); DotTwo; <Concrete_syntax.Snd>
  | e = m(atomic); Dot; f = Ident; { Concrete_syntax.Proj (f,e) }
  | Type; Caret; i = Dec_const; { Concrete_syntax.U (Const i) }
  | Type; { Concrete_syntax.U (Const 0) }
  | Refl; { Concrete_syntax.Refl }
  | Lambda; L_paren; R_paren; { Concrete_syntax.Absurd }

let spine :=
  | { Concrete_syntax.Nil }
  | ~ = spine; ~ = m(atomic); <Concrete_syntax.Snoc>

let nonempty_spine :=
  | ~ = spine; ~ = m(atomic); <Concrete_syntax.Snoc>

let record_term :=
  | f = Ident; xs = list(bound_name); Equal; e = m(term); 
    { match xs with
        | [] -> (f,e)
        | _  -> (f, Mark.mark_opt (Concrete_syntax.Lam (xs,e)) (Mark.src_span e)) 
    }

let record_type :=
  | f = Ident; Colon; e = m(term); { (f,e) }


let term :=
  | atomic
  | ~ = m(atomic); ~ = nonempty_spine; <Concrete_syntax.Spine>
  | Lambda; xs = nonempty_list(bound_name); Thick_arrow; e = m(term); <Concrete_syntax.Lam>
  | args = nonempty_list(paren(annot_args)); Arrow; e = m(term); { Concrete_syntax.Pi (args_to_tele args,e) }
  | t1 = m(term); Arrow; t2 = m(term); { Concrete_syntax.Pi ([("_",t1)],t2) }
  | args = nonempty_list(paren(annot_args)); Star; e = m(term); { Concrete_syntax.Sg (args_to_tele args,e) }
  | t1 = m(term); Star; t2 = m(term); { Concrete_syntax.Sg ([("_",t1)],t2) }
  | Id; t = m(atomic); e1 = m(atomic); e2 = m(atomic); <Concrete_syntax.Id>
  | Sig; option(Bar); fs = separated_list(Bar,record_type); { Concrete_syntax.RecordTy {extends = None ; fields = fs} }
  | Sig; Extends; e = m(term); Bar; fs = separated_list(Bar,record_type); { Concrete_syntax.RecordTy {extends = Some e ; fields = fs}}
  | Struct; option(Bar); fs = separated_list(Bar,record_term); { Concrete_syntax.Record {extends = None ; fields = fs} }
  | Struct; Extends; e = m(term); Bar; fs = separated_list(Bar,record_term); { Concrete_syntax.Record {extends = Some e ; fields = fs}}

  | Let; x = bound_name; Equal; e1 = m(term); In; e2 = m(term);
     {Concrete_syntax.Let ((x,e1),e2) }

  | Let; x = bound_name; Colon; t = m(term); Equal; e1 = m(term); In; e2 = m(term); 
    { Concrete_syntax.Let ((x,Mark.naked @@ Concrete_syntax.Ascribe {tm = e1 ; tp = t}),e2) } 

  | Let; x = bound_name; args = nonempty_list(paren(annot_args)); Colon; t = m(term); Equal; e = m(term); In; e2 = m(term);
    { let tm,tp = func_syntax (args,t,e) in
      Concrete_syntax.Let ((x,Mark.naked @@ Concrete_syntax.Ascribe {tm ; tp}),e2) 
    }

  | Lambda; Elim;
    option(Bar); arms = separated_list(Bar,arm);
    { Concrete_syntax.ElimFun arms}
  
  | Elim; scrut = m(term); At; x = bound_name; Thick_arrow; mot = m(term); With;
    option(Bar); arms = separated_list(Bar,arm);
    { Concrete_syntax.Elim {mot = Some (x,mot) ; scrut ; arms}}

  | Elim; scrut = m(term); With;
    option(Bar); arms = separated_list(Bar,arm);
    { Concrete_syntax.Elim {mot = None ; scrut ; arms}}

  | Match; scrut = m(term); With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = m(term);
    { Concrete_syntax.J {mot = None ; body = (a,case) ; scrut } }

  | Match; scrut = m(term); At; x = bound_name; y = bound_name; z = bound_name; Thick_arrow; mot = m(term); With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = m(term);
    { Concrete_syntax.J {mot = Some (x,y,z,mot) ; body = (a,case) ; scrut} }

let arm :=
  | con = Ident; args = list(arm_pat); Thick_arrow; body = m(term); { (con,(args,body)) }

let arm_pat :=
  | ~ = bound_name; <`Arg>
  | L_paren; x = bound_name; F_slash; y = bound_name; R_paren; <`Rec> 