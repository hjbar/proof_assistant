(** Type variables *)
type tvar = string

(** Term variables *)
type var = string

(** Types *)
type ty =
  | True
  | False
  | TVar of tvar
  | And of ty * ty
  | Or of ty * ty
  | Imp of ty * ty
  | Nat

(** Lambda terms *)
type tm =
  | Unit
  | Absurd of tm * ty
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * tm * tm
  | Zero
  | Suc of tm
  | Rec of tm * tm * tm

(** Type for typing contexts *)
type context = (var * ty) list

(** Exception for typing error *)
exception Type_error

(** Type for sequent *)
type sequent = context * ty
