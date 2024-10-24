(** Type variables *)
type tvar = string

(** Term variables *)
type var = string

(** Types *)
type ty =
  | True
  | False
  | TVar of string
  | And of ty * ty
  | Or of ty * ty
  | Imp of ty * ty

(** Lambda terms *)
type tm =
  | Unit
  | Absurd of tm * ty
  | Var of string
  | App of tm * tm
  | Abs of string * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * tm * tm
