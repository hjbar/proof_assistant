open Prover

(* Functions of test *)

let test_string_of_ty () =
  let res =
    string_of_ty @@ Arr (Arr (TVar "A", TVar "B"), Arr (TVar "A", TVar "C"))
  in
  let obj = "((A ⇒ B) ⇒ (A ⇒ C))" in
  assert (res = obj)

let test_string_of_tm () =
  let res =
    string_of_tm
    @@ Abs
         ( "f"
         , Arr (TVar "A", TVar "B")
         , Abs ("x", TVar "A", App (Var "f", Var "x")) )
  in
  let obj = "(fun (f : (A ⇒ B)) -> (fun (x : A) -> (f x)))" in
  assert (res = obj)

let test_infer_type () =
  let res =
    infer_type []
    @@ Abs
         ( "f"
         , Arr (TVar "A", TVar "B")
         , Abs
             ( "g"
             , Arr (TVar "B", TVar "C")
             , Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let obj =
    Arr
      ( Arr (TVar "A", TVar "B")
      , Arr (Arr (TVar "B", TVar "C"), Arr (TVar "A", TVar "C")) )
  in
  assert (res = obj);

  let () =
    try
      infer_type [] @@ Abs ("f", TVar "A", Var "x") |> ignore;
      assert false
    with
    | Type_error -> assert true
    | _ -> assert false
  in

  let () =
    try
      infer_type []
      @@ Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x")))
      |> ignore;
      assert false
    with
    | Type_error -> assert true
    | _ -> assert false
  in

  let () =
    try
      infer_type []
      @@ Abs
           ( "f"
           , Arr (TVar "A", TVar "B")
           , Abs ("x", TVar "B", App (Var "f", Var "x")) )
      |> ignore;
      assert false
    with
    | Type_error -> assert true
    | _ -> assert false
  in

  ()

let test_check_type () =
  let () =
    try
      check_type [] (Abs ("x", TVar "A", Var "x")) (Arr (TVar "A", TVar "A"));
      assert true
    with _ -> assert false
  in

  let () =
    try
      check_type [] (Abs ("x", TVar "A", Var "x")) (Arr (TVar "B", TVar "B"));
      assert false
    with
    | Type_error -> assert true
    | _ -> assert false
  in

  let () =
    try
      check_type [] (Var "x") (TVar "A");
      assert false
    with
    | Type_error -> assert true
    | _ -> assert false
  in

  ()

let test_conjonction () =
  (* The and_comm term *)
  let res =
    string_of_ty @@ infer_type []
    @@ Abs ("p", TPair (TVar "A", TVar "B"), Pair (Snd (Var "p"), Fst (Var "p")))
  in
  let obj = "((A ∧ B) ⇒ (B ∧ A))" in
  assert (res = obj)

(* General function of test *)

let test () =
  List.iter
    (fun f -> f ())
    [ test_string_of_ty
    ; test_string_of_tm
    ; test_infer_type
    ; test_check_type
    ; test_conjonction
    ]

(* Main *)

let () =
  test ();
  print_endline "OK"
