{

open Core
open Parser

}

let ident = [^ '(' ')' '\\' ':' ',' '=' ' ' '\t' '\n' '^' ';' '|' '?' '.' ]+
let dec_num = ("0" | ['1'-'9'](['0'-'9']*))

let whitespace = [' ' '\t' '\r']

rule initial = parse
  | whitespace+ { initial lexbuf }
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | '(' { L_paren }
  | ')' { R_paren }
  | ';' { Semicolon }
  | ',' { Comma }
  | ".1" { DotOne }
  | ".2" { DotTwo }
  | '.' { Dot }
  | '*' | "×" { Star }
  | '\\' | "λ" { Lambda }
  | "->" | "→" { Arrow }
  | "=>" { Thick_arrow }
  | "let" { Let }
  | "in" { In }
  | "sig" { Sig }
  | "struct" { Struct }
  | "data" { Data }
  | "elim" { Elim }
  | "import" { Import }
  | '^' { Caret }
  | ':' { Colon }
  | '_' { Underbar }
  | "?" { Question_mark }
  | '/' { F_slash }
  | "Type" { Type }
  | "def" { Def }
  | "axiom" { Axiom }
  | "=" { Equal }
  | "refl" { Refl }
  | "Id" { Id }
  | "match" { Match }
  | '|' { Bar }
  | "with" { With }
  | "at" { At }
  | dec_num as d { Dec_const (Int.of_string d) }
  | "{-" { comment 1 lexbuf }
  | "-}" { failwith "Unbalanced comments" }
  | "--" { comment_line lexbuf }
  | ident as name { Ident name }
  | eof { Eof }
  | _ as x { failwith ("illegal char: " ^ (Char.to_string x)) }


and comment nesting = parse
  | '\n' { Lexing.new_line lexbuf; comment nesting lexbuf }
  | "{-" { comment (nesting + 1) lexbuf }
  | "-}" { match nesting - 1 with | 0 -> initial lexbuf | n' -> comment n' lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment nesting lexbuf }

and comment_line = parse
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment_line lexbuf }
