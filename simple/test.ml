(** Import some stuff *)

open Expr
open Prover

(** Functions of test *)

let test_string_of_ty () =
  let res =
    string_of_ty @@ Imp (Imp (TVar "A", TVar "B"), Imp (TVar "A", TVar "C"))
  in
  let obj = "((A ⇒ B) ⇒ (A ⇒ C))" in
  assert (res = obj)

let test_string_of_tm () =
  let res =
    string_of_tm
    @@ Abs
         ( "f"
         , Imp (TVar "A", TVar "B")
         , Abs ("x", TVar "A", App (Var "f", Var "x")) )
  in
  let obj = "(λ (f : (A ⇒ B)) → (λ (x : A) → (f x)))" in
  assert (res = obj)

let test_infer_type () =
  let res =
    infer_type []
    @@ Abs
         ( "f"
         , Imp (TVar "A", TVar "B")
         , Abs
             ( "g"
             , Imp (TVar "B", TVar "C")
             , Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let obj =
    Imp
      ( Imp (TVar "A", TVar "B")
      , Imp (Imp (TVar "B", TVar "C"), Imp (TVar "A", TVar "C")) )
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
           , Imp (TVar "A", TVar "B")
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
      check_type [] (Abs ("x", TVar "A", Var "x")) (Imp (TVar "A", TVar "A"));
      assert true
    with
    | _ -> assert false
  in

  let () =
    try
      check_type [] (Abs ("x", TVar "A", Var "x")) (Imp (TVar "B", TVar "B"));
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
  let and_comm =
    Abs ("p", And (TVar "A", TVar "B"), Pair (Snd (Var "p"), Fst (Var "p")))
  in
  let res = string_of_ty @@ infer_type [] and_comm in
  let obj = "((A ∧ B) ⇒ (B ∧ A))" in
  assert (res = obj)

let test_truth () =
  let proof = Abs ("f", Imp (True, TVar "A"), App (Var "f", Unit)) in
  let res = string_of_ty @@ infer_type [] proof in
  let obj = "((⊤ ⇒ A) ⇒ A)" in
  assert (res = obj)

let test_disjunction () =
  let res =
    string_of_ty @@ infer_type []
    @@ Abs
         ( "c"
         , Or (TVar "A", TVar "B")
         , Case
             ( Var "c"
             , Abs ("x", TVar "A", Right (TVar "B", Var "x"))
             , Abs ("x", TVar "B", Left (Var "x", TVar "A")) ) )
  in
  let obj = "((A ∨ B) ⇒ (B ∨ A))" in
  assert (res = obj)

let test_bot () =
  let proof =
    string_of_ty @@ infer_type []
    @@ Abs
         ( "x"
         , And (TVar "A", Imp (TVar "A", False))
         , Absurd (App (Snd (Var "x"), Fst (Var "x")), TVar "B") )
  in
  let res = "((A ∧ (A ⇒ ⊥)) ⇒ B)" in
  assert (proof = res)

let test_nat () =
  let res = infer_type [] Zero in
  let obj = Nat in
  assert (res = obj);

  let res = infer_type [] @@ Suc Zero in
  let obj = Nat in
  assert (res = obj);

  let res =
    infer_type []
    @@ Abs
         ( "z"
         , TVar "A"
         , Rec (Zero, Var "z", Abs ("x", Nat, Abs ("y", TVar "A", Var "y"))) )
  in
  let obj = Imp (TVar "A", TVar "A") in
  assert (res = obj)

let test_parsing () =
  let l =
    [ ("A => B", "(A ⇒ B)")
    ; ("A ⇒ B", "(A ⇒ B)")
    ; ("A /\\ B", "(A ∧ B)")
    ; ("A ∧ B", "(A ∧ B)")
    ; ("A \\/ B", "(A ∨ B)")
    ; ("A ∨ B", "(A ∨ B)")
    ; ("not A", "(A ⇒ ⊥)")
    ; ("¬ A", "(A ⇒ ⊥)")
    ; ("T", "⊤")
    ; ("⊤", "⊤")
    ; ("_", "⊥")
    ; ("⊥", "⊥")
    ; ("(A => B) => A => B", "((A ⇒ B) ⇒ (A ⇒ B))")
    ; ("Nat", "ℕ")
    ; ("ℕ", "ℕ")
    ]
  in

  List.iter
    begin
      fun (s, obj) ->
        let res = s |> ty_of_string |> string_of_ty in
        if res = obj then assert true
        else begin
          Format.printf "We had %s instead of %s\n%!" res obj;
          assert false
        end
    end
    l;

  let l =
    [ ("fst(t)", "(π₁ t)")
    ; ("π₁ t", "(π₁ t)")
    ; ("snd(t)", "(π₂ t)")
    ; ("π₂ t", "(π₂ t)")
    ; ("()", "()")
    ; ("(t , u)", "(t, u)")
    ; ("left(t,B)", "(ιₗ (right : B) → t)")
    ; ("right(A,t)", "(ιᵣ (left : A) → t)")
    ; ("absurd(t,A)", "(prove (absurd : t) → A)")
    ; ("t u v", "((t u) v)")
    ; ("fun (x : A) -> t", "(λ (x : A) → t)")
    ; ("fun (x : A) → t", "(λ (x : A) → t)")
    ; ("λ (x : A) -> t", "(λ (x : A) → t)")
    ; ("λ (x : A) → t", "(λ (x : A) → t)")
    ; ( "case t of fun (x : A) -> u | fun (y : B) -> v"
      , "(case t of (λ (x : A) → u) | (λ (y : B) → v))" )
    ; ( "case t of fun (x : A) → u | fun (y : B) → v"
      , "(case t of (λ (x : A) → u) | (λ (y : B) → v))" )
    ; ( "case t of λ (x : A) -> u | λ (y : B) -> v"
      , "(case t of (λ (x : A) → u) | (λ (y : B) → v))" )
    ; ( "case t of λ (x : A) → u | λ (y : B) → v"
      , "(case t of (λ (x : A) → u) | (λ (y : B) → v))" )
    ; ("zero", "0")
    ; ("0", "0")
    ; ("suc zero", "1")
    ; ("suc 0", "1")
    ; ("S zero", "1")
    ; ("S 0", "1")
    ; ( "rec (0, z, λ (x : Nat) → λ (y : A) → y)"
      , "(rec 0 z (λ (x : ℕ) → (λ (y : A) → y)))" )
    ]
  in

  List.iter
    begin
      fun (s, obj) ->
        let res = s |> tm_of_string |> string_of_tm in
        if res = obj then assert true
        else begin
          Format.printf "We had %s instead of %s\n%!" res obj;
          assert false
        end
    end
    l

let test_string_of_ctx () =
  let res =
    string_of_ctx
      [ ("z", True)
      ; ("y", And (TVar "A", TVar "B"))
      ; ("x", Imp (TVar "A", TVar "B"))
      ]
  in
  let obj = "x : (A ⇒ B), y : (A ∧ B), z : ⊤" in
  assert (res = obj)

let test_string_of_seq () =
  let res =
    string_of_seq
      ([ ("y", TVar "A"); ("x", Imp (TVar "A", TVar "B")) ], TVar "B")
  in
  let obj = "x : (A ⇒ B), y : A ⊢ B" in
  assert (res = obj)

(** General testing function *)

let test_all_functions () =
  Format.printf "\n\nTests for simple prover :\n%!";

  test_string_of_ty ();
  test_string_of_tm ();
  test_infer_type ();
  test_check_type ();
  test_conjonction ();
  test_truth ();
  test_disjunction ();
  test_bot ();
  test_nat ();
  test_parsing ();
  test_string_of_ctx ();
  test_string_of_seq ();

  Format.printf "\nSimple prover : OK\n\n%!"
