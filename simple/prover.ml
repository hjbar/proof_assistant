let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TUnit
  | TBot
  | TVar of string
  | TPair of ty * ty
  | TCoprod of ty * (ty, ty) Either.t
  | Arr of ty * ty

(** Lambda terms *)
type tm =
  | Unit
  | Bot of ty * tm
  | Var of string
  | App of tm * tm
  | Abs of string * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Left of ty * tm
  | Right of ty * tm
  | Case of tm * tm * tm

(** Gives a string representation of a type *)
let rec string_of_ty = function
  | TUnit -> "⊤"
  | TBot -> "⊥"
  | TVar x -> x
  | TPair (t1, t2) ->
    Format.sprintf "(%s ∧ %s)" (string_of_ty t1) (string_of_ty t2)
  | TCoprod (ty1, Left ty2) ->
    Format.sprintf "(%s ∨ %s)" (string_of_ty ty2) (string_of_ty ty1)
  | TCoprod (ty1, Right ty2) ->
    Format.sprintf "(%s ∨ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | Arr (t1, t2) ->
    Format.sprintf "(%s ⇒ %s)" (string_of_ty t1) (string_of_ty t2)

(** Gives a string representation of a term *)
let rec string_of_tm = function
  | Unit -> "⊤"
  | Bot _ -> "⊥"
  | Var x -> x
  | App (t1, t2) -> Format.sprintf "(%s %s)" (string_of_tm t1) (string_of_tm t2)
  | Abs (x, ty, tm) ->
    Format.sprintf "(fun (%s : %s) -> %s)" x (string_of_ty ty) (string_of_tm tm)
  | Pair (t1, t2) ->
    Format.sprintf "(%s ∧ %s)" (string_of_tm t1) (string_of_tm t2)
  | Fst tm -> Format.sprintf "(π₁ %s)" (string_of_tm tm)
  | Snd tm -> Format.sprintf "(π₂ %s)" (string_of_tm tm)
  | Left (ty, tm) ->
    Format.sprintf "(ιₗ (Right : %s) -> %s)" (string_of_ty ty) (string_of_tm tm)
  | Right (ty, tm) ->
    Format.sprintf "(ιᵣ (Left : %s) -> %s)" (string_of_ty ty) (string_of_tm tm)
  | Case (t1, t2, t3) ->
    Format.sprintf "(case %s, %s, %s)" (string_of_tm t1) (string_of_tm t2)
      (string_of_tm t3)

(** Type for typing contexts *)
type context = (var * ty) list

(** Exception for typing error *)
exception Type_error

let ty_eq t1 t2 =
  match (t1, t2) with
  | TCoprod (ty1, Left ty2), TCoprod (ty3, Left ty4) -> ty2 = ty4 && ty1 = ty3
  | TCoprod (ty1, Left ty2), TCoprod (ty3, Right ty4) -> ty2 = ty3 && ty1 = ty4
  | TCoprod (ty1, Right ty2), TCoprod (ty3, Left ty4) -> ty1 = ty4 && ty2 = ty3
  | TCoprod (ty1, Right ty2), TCoprod (ty3, Right ty4) -> ty1 = ty3 && ty2 = ty4
  | ty1, ty2 -> ty1 = ty2

(** Infers the type of a term t in a given context Γ *)
let rec infer_type env = function
  | Unit -> TUnit
  | Bot (ty, tm) ->
    check_type env tm TBot;
    ty
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
  | Left (ty, tm) -> TCoprod (ty, Left (infer_type env tm))
  | Right (ty, tm) -> TCoprod (ty, Right (infer_type env tm))
  | Case (t1, t2, t3) -> begin
    match (infer_type env t1, infer_type env t2, infer_type env t3) with
    | TCoprod (ty_r, Left ty_l), Arr (ty1, ty2), Arr (ty3, ty4)
      when ty_eq ty_l ty1 && ty_eq ty_r ty3 && ty_eq ty2 ty4 ->
      ty4
    | TCoprod (ty_l, Right ty_r), Arr (ty1, ty2), Arr (ty3, ty4)
      when ty_l = ty1 && ty_r = ty3 && ty2 = ty4 ->
      ty4
    | _ -> raise Type_error
  end

(** checks whether a term has a given type *)
and check_type env tm ty =
  if not @@ ty_eq (infer_type env tm) ty then raise Type_error
