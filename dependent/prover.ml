(** Import the definitions of expressions *)
open Expr

(** Construct an expression from a string *)
let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(** Provides the string representation of an expression *)
let rec to_string = function
  | Type -> "Set"
  | Var x -> x
  | App (t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(%s %s)" s1 s2
  | Abs (x, t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(λ (%s : %s) → %s)" x s1 s2
  | Pi (x, t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(Π (%s : %s) → %s)" x s1 s2
  | Nat -> failwith "todo"
  | Z -> failwith "todo"
  | S _t -> failwith "todo"
  | Ind (_t1, _t2, _t3, _t4) -> failwith "todo"
  | Eq (_t1, _t2) -> failwith "todo"
  | Refl _t -> failwith "todo"
  | J (_t1, _t2, _t3, _t4, _t5) -> failwith "todo"

(** Returns a fresh variable name at each call *)
let fresh_var =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Format.sprintf "x%d" !cpt

(** Provide the term obtained by replacing the variable x by t in u *)
let rec subst x t = function
  | Type -> Type
  | Var v when v = x -> t
  | Var _ as u -> u
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (v, ty, u) ->
    let x' = fresh_var () in
    let u' = subst v (Var x') u in
    Abs (x', ty, subst x t u')
  | Pi (v, ty, u) ->
    let x' = fresh_var () in
    let u' = subst v (Var x') u in
    Pi (x', ty, subst x t u')
  | _ -> assert false

(** Provide the string representation of a context *)
let string_of_context (ctx : context) =
  let content_to_string (x, (ty, value_opt)) =
    let s = to_string ty in
    match value_opt with
    | None -> Format.sprintf "%s : %s" x s
    | Some value -> Format.sprintf "%s : %s = %s" x s (to_string value)
  in
  ctx |> List.rev |> List.map content_to_string |> String.concat ", "
