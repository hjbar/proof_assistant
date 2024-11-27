(** Variables *)
type var = string

(** Expressions *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

(** Context *)
type context = (var * (expr * expr option)) list

(** Exception for typing error *)
exception Type_error of string
