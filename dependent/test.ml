(** Import some stuff *)

open Expr
open Prover

(** Functions of test *)

let test_to_string () =
  let res = to_string Type in
  let obj = "Set" in
  assert (res = obj);

  let res = to_string @@ Var "x" in
  let obj = "x" in
  assert (res = obj);

  let res = to_string @@ App (Var "x", Type) in
  let obj = "(x Set)" in
  assert (res = obj);

  let res = to_string @@ Abs ("x", Type, App (Var "f", Var "x")) in
  let obj = "(λ (x : Set) → (f x))" in
  assert (res = obj);

  let res = to_string @@ Pi ("x", Type, Type) in
  let obj = "(Π (x : Set) → Set)" in
  assert (res = obj)

let test_subst () =
  let res =
    subst "x"
      (Abs ("x", Var "A", Var "x"))
      (App (Var "x", Abs ("y", Var "B", Var "x")))
  in

  let obj =
    App
      ( Abs ("x", Var "A", Var "x")
      , Abs ("x1", Var "B", Abs ("x", Var "A", Var "x")) )
  in
  assert (res = obj);

  let res = subst "x" (Var "y") (Abs ("y", Var "B", Var "x")) in
  let not_obj = Abs ("x1", Var "B", Var "x1") in
  assert (res <> not_obj)

let test_string_of_context () =
  let res = string_of_context [] in
  let obj = "" in
  assert (res = obj);

  let res = string_of_context [ ("x", (Var "A", None)) ] in
  let obj = "x : A" in
  assert (res = obj);

  let res = string_of_context [ ("x", (Var "A", Var "x" |> Option.some)) ] in
  let obj = "x : A = x" in
  assert (res = obj);

  let res =
    string_of_context
      [ ("y", (Type, None)); ("x", (Var "A", Var "x" |> Option.some)) ]
  in
  let obj = "x : A = x, y : Set" in
  assert (res = obj)

(** General testing function *)

let test_all_functions () =
  Format.printf "\n\nTests for dependent prover :\n%!";

  test_to_string ();
  test_subst ();
  test_string_of_context ();

  Format.printf "\nDependent prover : OK\n\n%!"
