
(* monotype *)
type ty =
  | TInt
  | TBool
  | TFun of ty * ty
  | TVar of string

module VarSet = Set.Make(String)

type ty_scheme = Forall of VarSet.t * ty

type expr =
  | Var of string
  | Num of int
  | Fun of string * expr
  | Add of expr * expr
  | Eq of expr * expr
  | If of expr * expr * expr
  | App of expr * expr
  | Let of string * expr * expr

type prog = (string * expr) list

module Env = Map.Make(String)

type dyn_env = value Env.t
and value =
  | VBool of bool
  | VNum of int
  | VClos of string * expr * dyn_env

let rename (Forall (bvs, ty) : ty_scheme) : ty =
  let count = ref 96 in
  let gen_letter () =
    let _ = count := !count + 1 in
    TVar (String.init 1 (fun _ -> char_of_int !count))
  in
  let ty_subst ty x =
    let rec go = function
      | TInt -> TInt
      | TBool -> TBool
      | TFun (t1, t2) -> TFun (go t1, go t2)
      | TVar y -> if x = y then ty else TVar y
    in go
  in
  VarSet.fold
    (fun v acc -> ty_subst (gen_letter ()) v acc)
    bvs
    ty

let string_of_ty_scheme (Forall (bvs, ty)) =
  let rec go = function
    | TInt -> "int"
    | TBool -> "bool"
    | TVar a -> "\'" ^ a
    | TFun (t1, t2) -> go_paren t1 ^ " -> " ^ go t2
  and go_paren = function
    | TFun (t1, t2) -> "(" ^ go (TFun (t1, t2)) ^ ")"
    | ty -> go ty
  in
  let ty = rename (Forall (bvs, ty)) in
  go ty
