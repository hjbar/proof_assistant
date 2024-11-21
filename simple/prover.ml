(** Import the definitions of terms and types *)
open Expr

(** Construct a type from a string *)
let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

(** Construct a term from a string *)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

(** Gives a string representation of a type *)
let rec string_of_ty = function
  | True -> "⊤"
  | False -> "⊥"
  | TVar x -> x
  | And (t1, t2) ->
    let s1, s2 = (string_of_ty t1, string_of_ty t2) in
    Format.sprintf "(%s ∧ %s)" s1 s2
  | Or (t1, t2) ->
    let s1, s2 = (string_of_ty t1, string_of_ty t2) in
    Format.sprintf "(%s ∨ %s)" s1 s2
  | Imp (t1, t2) ->
    let s1, s2 = (string_of_ty t1, string_of_ty t2) in
    Format.sprintf "(%s ⇒ %s)" s1 s2
  | Nat -> "ℕ"

(** Gives a string representation of a term *)
let rec string_of_tm = function
  | Unit -> "()"
  | Absurd (tm, ty) ->
    let s1, s2 = (string_of_tm tm, string_of_ty ty) in
    Format.sprintf "(prove (absurd : %s) → %s)" s1 s2
  | Var x -> x
  | App (t1, t2) ->
    let s1, s2 = (string_of_tm t1, string_of_tm t2) in
    Format.sprintf "(%s %s)" s1 s2
  | Abs (x, ty, tm) ->
    let s1, s2, s3 = (x, string_of_ty ty, string_of_tm tm) in
    Format.sprintf "(λ (%s : %s) → %s)" s1 s2 s3
  | Pair (t1, t2) ->
    let s1, s2 = (string_of_tm t1, string_of_tm t2) in
    Format.sprintf "(%s, %s)" s1 s2
  | Fst tm -> Format.sprintf "(π₁ %s)" (string_of_tm tm)
  | Snd tm -> Format.sprintf "(π₂ %s)" (string_of_tm tm)
  | Left (tm, ty) ->
    let s1, s2 = (string_of_ty ty, string_of_tm tm) in
    Format.sprintf "(ιₗ (right : %s) → %s)" s1 s2
  | Right (ty, tm) ->
    let s1, s2 = (string_of_ty ty, string_of_tm tm) in
    Format.sprintf "(ιᵣ (left : %s) → %s)" s1 s2
  | Case (t1, t2, t3) ->
    let s1, s2, s3 = (string_of_tm t1, string_of_tm t2, string_of_tm t3) in
    Format.sprintf "(case %s of %s | %s)" s1 s2 s3
  | Zero -> "0"
  | Suc tm -> Format.sprintf "(suc %s)" (string_of_tm tm)
  | Rec (t1, t2, t3) ->
    let s1, s2, s3 = (string_of_tm t1, string_of_tm t2, string_of_tm t3) in
    Format.sprintf "(rec %s %s %s)" s1 s2 s3

(** Infers the type of a term t in a given context Γ *)
let rec infer_type env = function
  | Unit -> True
  | Absurd (tm, ty) ->
    check_type env tm False;
    ty
  | Var x -> begin
    match List.assoc_opt x env with
    | None -> raise Type_error
    | Some ty -> ty
  end
  | App (t1, t2) -> begin
    match infer_type env t1 with
    | Imp (ty1, ty2) ->
      check_type env t2 ty1;
      ty2
    | _ -> raise Type_error
  end
  | Abs (x, ty, tm) -> Imp (ty, infer_type ((x, ty) :: env) tm)
  | Pair (t1, t2) -> And (infer_type env t1, infer_type env t2)
  | Fst tm -> begin
    match infer_type env tm with
    | And (ty, _) -> ty
    | _ -> raise Type_error
  end
  | Snd tm -> begin
    match infer_type env tm with
    | And (_, ty) -> ty
    | _ -> raise Type_error
  end
  | Left (tm, ty) -> Or (infer_type env tm, ty)
  | Right (ty, tm) -> Or (ty, infer_type env tm)
  | Case (t1, t2, t3) -> begin
    match (infer_type env t1, infer_type env t2, infer_type env t3) with
    | Or (ty_l, ty_r), Imp (ty1, ty2), Imp (ty3, ty4)
      when ty_l = ty1 && ty_r = ty3 && ty2 = ty4 ->
      ty4
    | _ -> raise Type_error
  end
  | Zero -> Nat
  | Suc tm ->
    check_type env tm Nat;
    Nat
  | Rec (t1, t2, t3) -> begin
    match (infer_type env t1, infer_type env t2, infer_type env t3) with
    | Nat, ty1, Imp (Nat, Imp (ty2, ty3)) when ty1 = ty2 && ty2 = ty3 -> ty3
    | _ -> raise Type_error
  end

(** Checks whether a term has a given type *)
and check_type env tm ty = if infer_type env tm <> ty then raise Type_error

(** Gives the string representation of a context *)
let string_of_ctx (ctx : context) =
  ctx |> List.rev
  |> List.map (fun (x, ty) -> Format.sprintf "%s : %s" x (string_of_ty ty))
  |> String.concat ", "

(** Gives the string representation of a sequent *)
let string_of_seq ((ctx, ty) : sequent) =
  Format.sprintf "%s ⊢ %s" (string_of_ctx ctx) (string_of_ty ty)
