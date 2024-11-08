(** Import the definitions of terms and types *)
open Expr

(** Import utility functions on terms and types *)
open Prover

(** The prove function for the interactive prover *)
let rec prove env a =
  print_endline @@ string_of_seq (env, a);
  print_string "? ";
  flush_all ();

  let error e =
    print_endline e;
    prove env a
  in

  let cmd, arg =
    let cmd = input_line stdin in
    let n =
      try String.index cmd ' ' with
      | Not_found -> String.length cmd
    in

    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in

    (c, a)
  in

  match cmd with
  | "intro" -> begin
    match a with
    | Imp (a, b) ->
      if arg = "" then error "Please provide an argument for intro."
      else
        let x = arg in
        let t = prove ((x, a) :: env) b in
        Abs (x, a, t)
    | _ -> error "Don't know how to introduce this."
  end
  | "elim" -> begin
    let ty_opt = List.assoc_opt arg env in
    if Option.is_none ty_opt then error "This variable is not in the context."
    else
      match Option.get ty_opt with
      | Imp (a, _b) ->
        let t = prove env a in
        App (Var arg, t)
      | _ -> error "Don't know how to eliminate this."
  end
  | "exact" ->
    let t = tm_of_string arg in
    if Option.is_none @@ List.assoc_opt arg env then
      error "This variable is not in the context."
    else if infer_type env t <> a then error "Not the right type."
    else t
  | cmd -> error @@ "Unknown command: " ^ cmd

(** Main function of the interactive prover *)
let main () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in

  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";

  print_endline "Proof term is";
  print_endline (string_of_tm t);

  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] t = a);

  print_endline "ok."
