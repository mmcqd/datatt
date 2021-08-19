open Core

type src_loc =
  { line : int
  ; col : int
  }
[@@deriving show]


type src_span =
  { start_loc : src_loc
  ; end_loc : src_loc
  }
[@@deriving show]


let of_position (pos : Lexing.position) : src_loc =
  Lexing.{ line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 (* 1-indexed *) }
;;

let of_positions (pos_start : Lexing.position) (pos_end : Lexing.position) =
  { start_loc = of_position pos_start
  ; end_loc = of_position pos_end
  }
;;


type 'a t = 'a * src_span option
  [@@deriving show]

let mark (data : 'a) (span : src_span) : 'a t = data, Some span
let data : 'a t -> 'a = fst
let naked (data : 'a) : 'a t = data, None
let src_span : 'a t -> src_span option = snd

let show : 'a t -> string =
  let show_src_loc = function
    | { line; col = 0 } -> string_of_int line
    | { line; col } -> string_of_int line ^ "." ^ string_of_int col
  in
  function 
    | _,Some span -> sprintf "%s-%s" (show_src_loc span.start_loc) (show_src_loc span.end_loc)
    | _,None -> ""
