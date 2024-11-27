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
  | _ -> failwith "to_string todo"

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
  | App (u1, u2) ->
    let u1' = subst x t u1 in
    let u2' = subst x t u2 in
    App (u1', u2')
  | Abs (v, ty, u) ->
    let x' = fresh_var () in
    let ty' = subst v (Var x') ty in
    let u' = subst v (Var x') u in
    Abs (x', subst x t ty', subst x t u')
  | Pi (v, ty, u) ->
    let x' = fresh_var () in
    let ty' = subst v (Var x') ty in
    let u' = subst v (Var x') u in
    Pi (x', subst x t ty', subst x t u')
  | _ -> failwith "subst todo"

(** Provide the string representation of a context *)
let string_of_context (ctx : context) =
  let content_to_string (x, (ty, value_opt)) =
    let s = to_string ty in
    match value_opt with
    | None -> Format.sprintf "%s : %s" x s
    | Some value -> Format.sprintf "%s : %s = %s" x s (to_string value)
  in
  ctx |> List.rev |> List.map content_to_string |> String.concat ", "

(** Computes the normal form of an expression *)
let ctx_lookup (ctx : context) x =
  match List.assoc_opt x ctx with
  | None -> None
  | Some (_, value) -> value

let rec normalize (ctx : context) = function
  | Type -> Type
  | Var x as t -> begin
    match ctx_lookup ctx x with
    | None -> t
    | Some value -> normalize ctx value
  end
  | App (t1, t2) -> begin
    let t1' = normalize ctx t1 in
    let t2' = normalize ctx t2 in
    match t1' with
    | Abs (x, _, tm) -> normalize ctx (subst x t2' tm)
    | _ -> App (t1', t2')
  end
  | Abs (x, ty, tm) ->
    let ty' = normalize ctx ty in
    let tm' = normalize ctx tm in
    Abs (x, ty', tm')
  | Pi (x, ty, tm) ->
    let ty' = normalize ctx ty in
    let tm' = normalize ctx tm in
    Pi (x, ty', tm')
  | _ -> failwith "normalize todo"

(** Tests whether two terms are α-convertible *)
let rec alpha t1 t2 =
  match (t1, t2) with
  | Type, Type -> true
  | Var x, Var x' -> x = x'
  | App (t, u), App (t', u') -> alpha t t' && alpha u u'
  | Abs (x1, ty1, tm1), Abs (x2, ty2, tm2)
  | Pi (x1, ty1, tm1), Pi (x2, ty2, tm2) ->
    let x = Var (fresh_var ()) in

    let ty1' = subst x1 x ty1 in
    let tm1' = subst x1 x tm1 in

    let ty2' = subst x2 x ty2 in
    let tm2' = subst x2 x tm2 in

    alpha ty1' ty2' && alpha tm1' tm2'
  | Nat, Nat
  | Z, Z
  | S _, S _
  | Ind _, Ind _
  | Eq _, Eq _
  | Refl _, Refl _
  | J _, J _ ->
    failwith "alpha todo"
  | _ -> false

(** Determines whether two terms are αβ-convertible *)
let conv (ctx : context) t1 t2 =
  let t1' = normalize ctx t1 in
  let t2' = normalize ctx t2 in
  alpha t1' t2'

(** Raise an type error with a message *)
let raise_error tm =
  let msg = Format.sprintf "Term %s is not of the right type." (to_string tm) in
  raise @@ Type_error msg

let raise_not_found x =
  let msg = Format.sprintf "Variable %s not found in context" x in
  raise @@ Type_error msg

let raise_type_error tm ty =
  let s1, s2 = (to_string tm, to_string ty) in
  let msg = Format.sprintf "Term %s is not of type %s." s1 s2 in
  raise @@ Type_error msg

(** Infers the type of an expression in a given context *)
let rec infer (ctx : context) = function
  | Type -> Type
  | Var x -> begin
    match List.assoc_opt x ctx with
    | None -> raise_not_found x
    | Some (ty, _) -> infer ctx ty
  end
  | App (t1, t2) as tm -> begin
    match infer ctx t1 with
    | Pi (_, ty1, ty2) ->
      check ctx t2 ty1;
      ty2
    | _ -> raise_error tm
  end
  | Abs (x, ty, tm) ->
    let ctx' = (x, (ty, None)) :: ctx in
    Pi (x, infer ctx' ty, infer ctx' tm)
  | Pi (x, ty, tm) ->
    check ((x, (ty, None)) :: ctx) tm Type;
    Type
  | _ -> failwith "infer todo"

(** Check the type of an expression in a given context *)
and check ctx tm ty =
  if not @@ conv ctx (infer ctx tm) ty then raise_type_error tm ty
