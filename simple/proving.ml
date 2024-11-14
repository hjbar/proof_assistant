(** Import the definitions of terms and types *)
open Expr

(** Import utility functions on terms and types *)
open Prover

(** The prove function for the interactive prover *)
let rec prove env a out_c =
  print_endline @@ string_of_seq (env, a);
  print_string "? ";
  flush_all ();

  let error e =
    print_endline e;
    prove env a out_c
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

  let write_cmd () = output_string out_c @@ Format.sprintf "%s %s\n" cmd arg in

  match cmd with
  | "intro" -> begin
    match a with
    | Imp (a, b) ->
      if arg = "" then error "Please provide an argument for intro."
      else begin
        write_cmd ();

        let x = arg in
        let t = prove ((x, a) :: env) b out_c in
        Abs (x, a, t)
      end
    | And (a, b) ->
      if arg <> "" then
        error "Please provide no argument for intro conjonction."
      else begin
        write_cmd ();

        let t1 = prove env a out_c in
        let t2 = prove env b out_c in
        Pair (t1, t2)
      end
    | True ->
      write_cmd ();

      Unit
    | _ -> error "Don't know how to introduce this."
  end
  | "elim" -> begin
    let ty_opt = List.assoc_opt arg env in
    if Option.is_none ty_opt then error "This variable is not in the context."
    else
      match Option.get ty_opt with
      | Imp (a, _b) ->
        write_cmd ();

        let t = prove env a out_c in
        App (Var arg, t)
      | Or (l, r) ->
        write_cmd ();

        let t1 = prove env (Imp (l, a)) out_c in
        let t2 = prove env (Imp (r, a)) out_c in
        Case (Var arg, t1, t2)
      | False ->
        write_cmd ();

        Absurd (Var arg, a)
      | _ -> error "Don't know how to eliminate this."
  end
  | "cut" -> begin
    match a with
    | Imp _ ->
      write_cmd ();

      let x = ty_of_string arg in
      let t2 = prove env (Imp (x, a)) out_c in
      let t1 = prove env x out_c in
      App (t1, t2)
    | _ -> error "Don't know how to cut this"
  end
  | "left" -> begin
    match a with
    | Or (a, b) ->
      write_cmd ();

      let t = prove env a out_c in
      Left (t, b)
    | _ -> error "Don't know how to left this"
  end
  | "right" -> begin
    match a with
    | Or (a, b) ->
      write_cmd ();

      let t = prove env b out_c in
      Right (a, t)
    | _ -> error "Don't know how to left this"
  end
  | "exact" ->
    let t = tm_of_string arg in
    if Option.is_none @@ List.assoc_opt arg env then
      error "This variable is not in the context."
    else if infer_type env t <> a then error "Not the right type."
    else begin
      write_cmd ();
      t
    end
  | "fst" -> begin
    let ty_opt = List.assoc_opt arg env in
    if Option.is_none ty_opt then error "This variable is not in the context."
    else
      match Option.get ty_opt with
      | And (a, _b) ->
        let t = Fst (tm_of_string arg) in
        if infer_type env t <> a then error "Not the right type"
        else begin
          write_cmd ();
          t
        end
      | _ -> error "Don't know how to snd this."
  end
  | "snd" -> begin
    let ty_opt = List.assoc_opt arg env in
    if Option.is_none ty_opt then error "This variable is not in the context."
    else
      match Option.get ty_opt with
      | And (_a, b) ->
        let t = Snd (tm_of_string arg) in
        if infer_type env t <> b then error "Not the right type"
        else begin
          write_cmd ();
          t
        end
      | _ -> error "Don't know how to snd this."
  end
  | cmd -> error @@ "Unknown command: " ^ cmd

(** Main function of the interactive prover *)
let main () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in

  let () =
    try Sys.mkdir "tmp" 0o775 with
    | _ -> ()
  in
  let out_c =
    open_out_gen [ Open_creat; Open_trunc; Open_wronly ] 0o664 "tmp/tmp.proof"
  in

  print_endline "Let's prove it.";
  output_string out_c @@ Format.sprintf "%s\n" (string_of_ty a);
  let t = prove [] a out_c in
  print_endline "done.";

  close_out out_c;

  print_endline "Proof term is";
  print_endline (string_of_tm t);

  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] t = a);

  print_endline "ok."
