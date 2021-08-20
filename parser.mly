%{

open Core.List

let rec args_to_tele = function
  | [] -> []
  | (xs,t)::args -> map xs ~f:(fun x -> (x,t)) @ args_to_tele args

let func_syntax (args,t,e) =
  let tele = args_to_tele args in
  Mark.naked @@ Concrete_syntax.Ascribe {tm = Mark.naked @@ Concrete_syntax.Lam (map ~f:fst tele,e); tp = Mark.naked @@ Concrete_syntax.Pi (tele,t) }


%}

%token Eof
%token Question_mark
%token L_paren R_paren
%token Lambda Thick_arrow Arrow
%token Comma DotOne DotTwo Star
%token Let In
%token Type Caret
%token Colon
%token Underbar
%token Id Refl 
%token Match With Bar At
%token Data Elim F_slash
%token Def Equal
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
  | Def; x = bound_name; args = nonempty_list(paren(annot_args)); Colon; t = m(term); Equal; e = m(term); { Concrete_syntax.Def (x,func_syntax (args,t,e)) }
  | data_def
  | ~ = m(term); <Concrete_syntax.Eval>

let data_def :=
  Data; name = bound_name; Equal;
  option(Bar); cons = separated_list(Bar,con);
    { Concrete_syntax.Data {name ; cons}}

let con :=
  name = bound_name; args = list(paren(annot_args));
    { (name,args_to_tele args) }

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = m(term) ; <>



let atomic :=
  | paren(term)
  | Question_mark; { Concrete_syntax.Hole }
  | x = Ident; { Concrete_syntax.Var x }
  | name = Ident; Caret; lvl = Dec_const; { Concrete_syntax.Lift {name ; lvl} }
  | ~ = paren(separated_list(Comma,m(term))); <Concrete_syntax.Tuple>
  | ~ = m(atomic); DotOne; <Concrete_syntax.Fst>
  | ~ = m(atomic); DotTwo; <Concrete_syntax.Snd>
  | Type; Caret; i = Dec_const; { Concrete_syntax.U (Const i) }
  | Type; { Concrete_syntax.U (Const 0) }
  | Refl; { Concrete_syntax.Refl }

let spine :=
  | { Concrete_syntax.Nil }
  | ~ = spine; ~ = m(atomic); <Concrete_syntax.Snoc>

let nonempty_spine :=
  | ~ = spine; ~ = m(atomic); <Concrete_syntax.Snoc>

let term :=
  | atomic
  | ~ = m(atomic); ~ = nonempty_spine; <Concrete_syntax.Spine>
  | Lambda; xs = nonempty_list(bound_name); Thick_arrow; e = m(term); <Concrete_syntax.Lam>
  | args = nonempty_list(paren(annot_args)); Arrow; e = m(term); { Concrete_syntax.Pi (args_to_tele args,e) }
  | t1 = m(term); Arrow; t2 = m(term); { Concrete_syntax.Pi ([("_",t1)],t2) }
  | args = nonempty_list(paren(annot_args)); Star; e = m(term); { Concrete_syntax.Sg (args_to_tele args,e) }
  | t1 = m(term); Star; t2 = m(term); { Concrete_syntax.Sg ([("_",t1)],t2) }
  | Id; t = m(atomic); e1 = m(atomic); e2 = m(atomic); <Concrete_syntax.Id>
  
  | Let; x = bound_name; Equal; e1 = m(term); In; e2 = m(term);
     {Concrete_syntax.Let ((x,e1),e2) }
  | Let; x = bound_name; Colon; t = m(term); Equal; e1 = m(term); In; e2 = m(term); 
    { Concrete_syntax.Let ((x,Mark.naked @@ Concrete_syntax.Ascribe {tm = e1 ; tp = t}),e2) } 

  | Elim; With;
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