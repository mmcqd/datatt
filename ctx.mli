
open Core

type t


val empty : t
val to_env : t -> Domain.env
val to_names : t -> String.Set.t
val to_string : t -> string
val find_tp : t -> string -> Domain.t option
val find_def_tp : t -> string -> Domain.t option
val find_data : t -> string -> Domain.desc option
val find_data_exn : t -> string -> Domain.desc
val is_data : t -> string -> bool
val add : t -> var:string -> tp:Domain.t -> t
val add_syn : t -> var:string -> tp:Syntax.t -> t
val add_def : t -> var:string -> def:Domain.t -> tp:Domain.t -> t
val add_data : t -> Domain.desc -> t