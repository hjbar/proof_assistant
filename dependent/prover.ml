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
  | Nat -> "ℕ"
  | Z -> "0"
  | S tm -> string_of_suc tm
  | Ind (t1, t2, t3, t4) ->
    let s1, s2, s3, s4 =
      (to_string t1, to_string t2, to_string t3, to_string t4)
    in
    Format.sprintf "(Ind %s %s %s %s)" s1 s2 s3 s4
  | Eq (t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(%s = %s)" s1 s2
  | Refl tm -> Format.sprintf "(Refl %s)" @@ to_string tm
  | J (t1, t2, t3, t4, t5) ->
    let s1, s2, s3, s4, s5 =
      (to_string t1, to_string t2, to_string t3, to_string t4, to_string t5)
    in
    Format.sprintf "(J %s %s %s %s %s)" s1 s2 s3 s4 s5

(** Provides a number of a term of form S S S S S Z *)
and string_of_suc t =
  let rec loop t n =
    match t with
    | Z -> Some n
    | S t -> loop t (n + 1)
    | _ -> None
  in
  match loop t 1 with
  | None -> Format.sprintf "(Suc %s)" @@ to_string t
  | Some n -> string_of_int n

(** Returns a fresh variable name at each call *)
let fresh_var =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Format.sprintf "x%d" !cpt

(** Return true if the term has free variables, false otherwise *)
let rec has_fv x = function
  | Type
  | Nat
  | Z ->
    false
  | S tm
  | Refl tm ->
    has_fv x tm
  | App (t1, t2)
  | Eq (t1, t2) ->
    has_fv x t1 || has_fv x t2
  | Ind (t1, t2, t3, t4) ->
    has_fv x t1 || has_fv x t2 || has_fv x t3 || has_fv x t4
  | J (t1, t2, t3, t4, t5) ->
    has_fv x t1 || has_fv x t2 || has_fv x t3 || has_fv x t4 || has_fv x t5
  | Var v -> v = x
  | Abs (v, t1, t2)
  | Pi (v, t1, t2) ->
    if v = x then false else has_fv x t1 || has_fv x t2

(** Provide the term obtained by replacing the variable x by t in u *)
let rec subst x t = function
  | Type -> Type
  | Var v when v = x -> t
  | Var _ as u -> u
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (v, _, _) as u when v = x -> u
  | Abs (v, u1, u2) when has_fv v t ->
    let x' = fresh_var () in
    let u1 = subst v (Var x') u1 in
    let u2 = subst v (Var x') u2 in
    Abs (x', subst x t u1, subst x t u2)
  | Abs (v, u1, u2) -> Abs (v, subst x t u1, subst x t u2)
  | Pi (v, _, _) as u when v = x -> u
  | Pi (v, u1, u2) when has_fv v t ->
    let x' = fresh_var () in
    let u1 = subst v (Var x') u1 in
    let u2 = subst v (Var x') u2 in
    Pi (x', subst x t u1, subst x t u2)
  | Pi (v, u1, u2) -> Pi (v, subst x t u1, subst x t u2)
  | Nat -> Nat
  | Z -> Z
  | S u -> S (subst x t u)
  | Ind (u1, u2, u3, u4) ->
    Ind (subst x t u1, subst x t u2, subst x t u3, subst x t u4)
  | Eq (u1, u2) -> Eq (subst x t u1, subst x t u2)
  | Refl u -> Refl (subst x t u)
  | J (u1, u2, u3, u4, u5) ->
    J (subst x t u1, subst x t u2, subst x t u3, subst x t u4, subst x t u5)

(** Provide the string representation of a context *)
let string_of_context (ctx : context) =
  let content_to_string (x, (ty, value_opt)) =
    let s = to_string ty in
    match value_opt with
    | None -> Format.sprintf "%s : %s" x s
    | Some value -> Format.sprintf "%s : %s = %s" x s (to_string value)
  in
  ctx |> List.rev |> List.map content_to_string |> String.concat ", "

(** Gives the value of a variable in the conetxt if it exists *)
let ctx_lookup (ctx : context) x =
  match List.assoc_opt x ctx with
  | None -> None
  | Some (_, value_opt) -> value_opt

(** Computes the normal form of an expression *)
let rec normalize (ctx : context) = function
  | Type -> Type
  | Var x as t -> begin
    match ctx_lookup ctx x with
    | None -> t
    | Some value -> normalize ctx value
  end
  | App (t1, t2) -> begin
    let t1 = normalize ctx t1 in
    let t2 = normalize ctx t2 in

    match t1 with
    | Abs (x, _, tm) -> normalize ctx @@ subst x t2 tm
    | _ -> App (t1, t2)
  end
  | Abs (x, t1, t2) -> Abs (x, normalize ctx t1, normalize ctx t2)
  | Pi (x, t1, t2) -> Pi (x, normalize ctx t1, normalize ctx t2)
  | Nat -> Nat
  | Z -> Z
  | S tm -> S (normalize ctx tm)
  | Ind (p, z, s, n) -> begin
    let p = normalize ctx p in
    let z = normalize ctx z in
    let s = normalize ctx s in
    let n = normalize ctx n in

    match n with
    | Z -> normalize ctx z
    | S n -> normalize ctx @@ App (App (s, n), Ind (p, z, s, n))
    | _ -> Ind (p, z, s, n)
  end
  | Eq (t1, t2) -> Eq (normalize ctx t1, normalize ctx t2)
  | Refl tm -> Refl (normalize ctx tm)
  | J (p, r, x, y, e) -> begin
    let p = normalize ctx p in
    let r = normalize ctx r in
    let x = normalize ctx x in
    let y = normalize ctx y in
    let e = normalize ctx e in

    match e with
    | Refl z when x = y && y = z -> normalize ctx @@ App (r, z)
    | _ -> J (p, r, x, y, e)
  end

(** Tests whether two terms are α-convertible *)
let rec alpha t1 t2 =
  match (t1, t2) with
  | Type, Type -> true
  | Var x, Var x' -> x = x'
  | App (t1, t2), App (t1', t2') -> alpha t1 t1' && alpha t2 t2'
  | Nat, Nat -> true
  | Z, Z -> true
  | S t1, S t2 -> alpha t1 t2
  | Ind (t1, t2, t3, t4), Ind (t1', t2', t3', t4') ->
    alpha t1 t1' && alpha t2 t2' && alpha t3 t3' && alpha t4 t4'
  | Eq (t1, t2), Eq (t1', t2') -> alpha t1 t1' && alpha t2 t2'
  | Refl t1, Refl t2 -> alpha t1 t2
  | J (t1, t2, t3, t4, t5), J (t1', t2', t3', t4', t5') ->
    alpha t1 t1' && alpha t2 t2' && alpha t3 t3' && alpha t4 t4' && alpha t5 t5'
  | Abs (x, t1, t2), Abs (x', t1', t2')
  | Pi (x, t1, t2), Pi (x', t1', t2') ->
    let v = Var (fresh_var ()) in

    let t1 = subst x v t1 in
    let t2 = subst x v t2 in
    let t1' = subst x' v t1' in
    let t2' = subst x' v t2' in

    alpha t1 t1' && alpha t2 t2'
  | _ -> false

(** Determines whether two terms are αβ-convertible *)
let conv (ctx : context) t1 t2 = alpha (normalize ctx t1) (normalize ctx t2)

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
    | Some (ty, _) -> ty
  end
  | App (t1, t2) as tm -> begin
    match infer ctx t1 with
    | Pi (x, u1, u2) ->
      check ctx t2 u1;
      subst x t2 u2
    | _ -> raise_error tm
  end
  | Abs (x, ty, tm) ->
    check ctx ty Type;
    let tm = infer ((x, (ty, None)) :: ctx) tm in
    Pi (x, ty, tm)
  | Pi (x, ty, tm) ->
    check ctx ty Type;
    check ((x, (ty, None)) :: ctx) tm Type;
    Type
  | Nat -> Type
  | Z -> Nat
  | S tm ->
    check ctx tm Nat;
    Nat
  | Ind (p, z, s, n) ->
    let p_val = Pi ("n", Nat, Type) in
    let z_val = App (p, Z) in
    let s_val =
      Pi ("n", Nat, Pi ("e", App (p, Var "n"), App (p, S (Var "n"))))
    in
    let n_val = Nat in

    check ctx p p_val;
    check ctx z z_val;
    check ctx s s_val;
    check ctx n n_val;

    App (p, n)
  | Eq (t1, t2) ->
    let t1 = infer ctx t1 in
    let t2 = infer ctx t2 in

    if not @@ conv ctx t1 t2 then raise_type_error t1 t2;
    Type
  | Refl tm ->
    infer ctx tm |> ignore;
    Eq (tm, tm)
  | J (p, r, x, y, e) ->
    let x_typ = infer ctx x in
    check ctx y x_typ;

    let p_val =
      Pi ("x", x_typ, Pi ("y", x_typ, Pi ("e", Eq (Var "x", Var "y"), Type)))
    in
    let r_val =
      Pi ("x", x_typ, App (App (App (p, Var "x"), Var "x"), Refl (Var "x")))
    in
    let e_val = Eq (x, y) in

    check ctx p p_val;
    check ctx r r_val;
    check ctx e e_val;

    App (App (App (p, x), y), e)

(** Check the type of an expression in a given context *)
and check ctx tm ty =
  if not @@ conv ctx (infer ctx tm) ty then raise_type_error tm ty
