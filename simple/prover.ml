(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of string
  | TPair of ty * ty
  | Arr of ty * ty

(** Lambda terms *)
type tm =
  | Var of string
  | App of tm * tm
  | Abs of string * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm

(** Gives a string representation of a type *)
let rec string_of_ty = function
  | TVar x -> x
  | TPair (t1, t2) ->
    Format.sprintf "(%s ∧ %s)" (string_of_ty t1) (string_of_ty t2)
  | Arr (t1, t2) ->
    Format.sprintf "(%s ⇒ %s)" (string_of_ty t1) (string_of_ty t2)

(** Gives a string representation of a term *)
let rec string_of_tm = function
  | Var x -> x
  | App (t1, t2) -> Format.sprintf "(%s %s)" (string_of_tm t1) (string_of_tm t2)
  | Abs (x, ty, tm) ->
    Format.sprintf "(fun (%s : %s) -> %s)" x (string_of_ty ty) (string_of_tm tm)
  | Pair (t1, t2) ->
    Format.sprintf "(%s ∧ %s)" (string_of_tm t1) (string_of_tm t2)
  | Fst tm -> Format.sprintf "(π₁ %s)" (string_of_tm tm)
  | Snd tm -> Format.sprintf "(π₂ %s)" (string_of_tm tm)

(** Type for typing contexts *)
type context = (var * ty) list

(** Exception for typing error *)
exception Type_error

(** Infers the type of a term t in a given context Γ *)
let rec infer_type env = function
  | Var x -> begin
    match List.assoc_opt x env with None -> raise Type_error | Some ty -> ty
  end
  | App (t1, t2) -> begin
    match infer_type env t1 with
    | Arr (ty1, ty2) ->
      check_type env t2 ty1;
      ty2
    | _ -> raise Type_error
  end
  | Abs (x, ty, tm) -> Arr (ty, infer_type ((x, ty) :: env) tm)
  | Pair (t1, t2) -> TPair (infer_type env t1, infer_type env t2)
  | Fst tm -> begin
    match infer_type env tm with TPair (ty, _) -> ty | _ -> raise Type_error
  end
  | Snd tm -> begin
    match infer_type env tm with TPair (_, ty) -> ty | _ -> raise Type_error
  end

(** checks whether a term has a given type *)
and check_type env tm ty = if infer_type env tm <> ty then raise Type_error
