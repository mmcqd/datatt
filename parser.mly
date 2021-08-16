%{

open Core.List

let rec args_to_tele = function
  | [] -> []
  | (xs,t)::args -> map xs ~f:(fun x -> (x,t)) @ args_to_tele args

let func_syntax (args,t,e) =
  let tele = args_to_tele args in
  Concrete_syntax.Ascribe {tm = Concrete_syntax.Lam (map ~f:fst tele,e); tp = Concrete_syntax.Pi (tele,t) }


%}

%token Eof
%token Question_mark
%token L_paren R_paren
%token Lambda Thick_arrow Arrow
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


%type <Concrete_syntax.cmd list> init

%start init

%%

let paren(x) == L_paren; ~ = x; R_paren; <>

let init := ~ = nonempty_list(cmd); Eof; <>


let cmd := 
  | Def; ~ = bound_name; Equal; ~ = term; <Concrete_syntax.Def>
  | Def; x = bound_name; Colon; tp = term; Equal; tm = term; { Concrete_syntax.Def (x, Concrete_syntax.Ascribe {tp ; tm}) } 
  | Def; x = bound_name; args = nonempty_list(paren(annot_args)); Colon; t = term; Equal; e = term; { Concrete_syntax.Def (x,func_syntax (args,t,e)) }
  | data_def
  | ~ = term; <Concrete_syntax.Eval>

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
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = term ; <>



let atomic :=
  | paren(term)
  | Question_mark; { Concrete_syntax.Hole }
  | x = Ident; { Concrete_syntax.Var x }
  | L_paren; tm = term; Colon; tp = term; R_paren; { Concrete_syntax.Ascribe {tp ; tm} }
  | Type; Caret; i = Dec_const; { Concrete_syntax.U (Const i) }
  | Type; { Concrete_syntax.U (Const 0) }
  | Refl; { Concrete_syntax.Refl }

let spine :=
  | { Concrete_syntax.Nil }
  | ~ = spine; ~ = atomic; <Concrete_syntax.Snoc>

let nonempty_spine :=
  | ~ = spine; ~ = atomic; <Concrete_syntax.Snoc>

let term :=
  | atomic
  | ~ = atomic; ~ = nonempty_spine; <Concrete_syntax.Spine>
  | Lambda; xs = nonempty_list(bound_name); Thick_arrow; e = term; <Concrete_syntax.Lam>
  | args = nonempty_list(paren(annot_args)); Arrow; e = term; { Concrete_syntax.Pi (args_to_tele args,e) }
  | t1 = term; Arrow; t2 = term; { Concrete_syntax.Pi ([("_",t1)],t2) }
  | Id; t = atomic; e1 = atomic; e2 = atomic; <Concrete_syntax.Id>
  

  | Elim; With;
    arms = list(arm);
    { Concrete_syntax.ElimFun arms}
  
  | Elim; scrut = term; At; x = bound_name; Thick_arrow; mot = term; With;
    arms = list(arm);
    { Concrete_syntax.Elim {mot = Some (x,mot) ; scrut ; arms}}

  | Match; scrut = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Concrete_syntax.J {mot = None ; body = (a,case) ; scrut } }

  | Match; scrut = term; At; x = bound_name; y = bound_name; z = bound_name; Thick_arrow; mot = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Concrete_syntax.J {mot = Some (x,y,z,mot) ; body = (a,case) ; scrut} }

let arm :=
  | Bar; con = Ident; args = list(arm_pat); Thick_arrow; body = term; { (con,(args,body)) }

let arm_pat :=
  | ~ = bound_name; <`Arg>
  | L_paren; x = bound_name; F_slash; y = bound_name; R_paren; <`Rec> 