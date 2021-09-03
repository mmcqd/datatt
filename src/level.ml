open Core

type t =
  | Const of int
  | Omega
  [@@deriving show,equal]

let (+) l1 l2 =
  match l1,l2 with
    | Const i,Const j -> Const (i + j)
    | _ -> Omega

let (<) l1 l2 =
  match l1,l2 with
    | Const i, Const j -> i < j
    | Omega,_ -> false
    | _,Omega -> true

let (<=) l1 l2 =
  match l1,l2 with
    | Const i, Const j -> i <= j
    | Omega,Omega -> true
    | Omega,Const _ -> false
    | _,Omega -> true
