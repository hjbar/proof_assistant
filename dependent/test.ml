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
  assert (res = obj);

  let res = to_string Nat in
  let obj = "ℕ" in
  assert (res = obj);

  let res = to_string Z in
  let obj = "0" in
  assert (res = obj);

  let res = to_string @@ S Z in
  let obj = "1" in
  assert (res = obj);

  let res = to_string @@ S (S Z) in
  let obj = "2" in
  assert (res = obj);

  let res = to_string @@ S (S (S Z)) in
  let obj = "3" in
  assert (res = obj);

  let res = to_string @@ S (Var "x") in
  let obj = "(Suc x)" in
  assert (res = obj);

  let p = App (Var "n", Type) in
  let z = App (p, Z) in
  let s = Pi ("x", Nat, App (App (p, Var "n"), App (p, S (Var "n")))) in
  let n = S (S Z) in
  let res = to_string @@ Ind (p, z, s, n) in
  let obj =
    "(Ind (n Set) ((n Set) 0) (Π (x : ℕ) → (((n Set) n) ((n Set) (Suc n)))) 2)"
  in
  assert (res = obj);

  let res = to_string @@ Eq (Var "x", Var "y") in
  let obj = "(x = y)" in
  assert (res = obj);

  let res = to_string @@ Refl (Var "x") in
  let obj = "(Refl x)" in
  assert (res = obj);

  let p =
    Pi ("x", Var "A", Pi ("y", Var "A", App (Eq (Var "x", Var "y"), Type)))
  in
  let r =
    Pi
      ("x", Var "A", App (App (App (Var "p", Var "x"), Var "x"), Refl (Var "x")))
  in
  let x = Var "x" in
  let y = Var "y" in
  let e = Eq (Var "x", Var "y") in
  let res = to_string @@ J (p, r, x, y, e) in
  let obj =
    "(J (Π (x : A) → (Π (y : A) → ((x = y) Set))) (Π (x : A) → (((p x) x) \
     (Refl x))) x y (x = y))"
  in
  assert (res = obj)

let test_subst () =
  let res = subst "x" (Var "y") Type in
  let obj = Type in
  assert (alpha res obj);

  let res = subst "x" (Var "y") (Var "x") in
  let obj = Var "y" in
  assert (alpha res obj);

  let res = subst "x" (Var "y") (Var "z") in
  let obj = Var "z" in
  assert (alpha res obj);

  let res = subst "x" (Var "y") (App (Var "x", Var "z")) in
  let obj = App (Var "y", Var "z") in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Abs ("z", Var "x", App (Var "z", Var "x")) in
  let obj = Abs ("x", Var "y", App (Var "x", Var "y")) in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Abs ("x", Var "x", App (Var "x", Var "z")) in
  let obj = Abs ("x", Var "x", App (Var "x", Var "z")) in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Pi ("x", Var "x", App (Var "x", Var "z")) in
  let obj = Pi ("x", Var "x", App (Var "x", Var "z")) in
  assert (alpha res obj);

  let res =
    subst "x"
      (Abs ("x", Var "A", Var "x"))
      (App (Var "x", Abs ("y", Var "B", Var "x")))
  in
  let obj =
    App
      ( Abs ("x", Var "A", Var "x")
      , Abs ("y", Var "B", Abs ("x", Var "A", Var "x")) )
  in
  assert (alpha res obj);

  let res = subst "x" (Var "y") (Abs ("y", Var "B", Var "x")) in
  let obj = Abs ("x", Var "B", Var "y") in
  assert (alpha res obj);

  let res = subst "x" (Var "y") Nat in
  let obj = Nat in
  assert (alpha res obj);

  let res = subst "x" (Var "y") Z in
  let obj = Z in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ S (Var "x") in
  let obj = S (Var "y") in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Ind (Var "x", Z, S (Var "x"), Var "z") in
  let obj = Ind (Var "y", Z, S (Var "y"), Var "z") in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Eq (Var "x", S (Var "x")) in
  let obj = Eq (Var "y", S (Var "y")) in
  assert (alpha res obj);

  let res = subst "x" (Var "y") @@ Refl (Var "x") in
  let obj = Refl (Var "y") in
  assert (alpha res obj);

  let res =
    subst "x" (Var "y")
    @@ J (Var "x", Z, S (Var "x"), Eq (Var "x", Z), Refl (Var "x"))
  in
  let obj = J (Var "y", Z, S (Var "y"), Eq (Var "y", Z), Refl (Var "y")) in
  assert (alpha res obj)

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

let test_normalize () =
  let res = normalize [] Type in
  let obj = Type in
  assert (res = obj);

  let res = normalize [] @@ Var "x" in
  let obj = Var "x" in
  assert (res = obj);

  let res = normalize [ ("x", (Type, Some (Var "y"))) ] @@ Var "x" in
  let obj = Var "y" in
  assert (res = obj);

  let res = normalize [] @@ App (Var "f", Var "x") in
  let obj = App (Var "f", Var "x") in
  assert (res = obj);

  let res =
    normalize
      [ ("id", (Pi ("x", Type, Var "x"), Some (Abs ("x", Type, Var "x")))) ]
    @@ App (Var "id", Var "z")
  in
  let obj = Var "z" in
  assert (res = obj);

  let res = normalize [] @@ Abs ("x", Type, Var "x") in
  let obj = Abs ("x", Type, Var "x") in
  assert (res = obj);

  let res = normalize [] @@ Pi ("x", Type, Var "x") in
  let obj = Pi ("x", Type, Var "x") in
  assert (res = obj);

  let res =
    normalize [ ("A", (Type, Some (Var "B"))) ] @@ Pi ("x", Var "A", Var "x")
  in
  let obj = Pi ("x", Var "B", Var "x") in
  assert (res = obj);

  let res =
    normalize [] @@ App (Abs ("x", Var "A", App (Var "x", Var "x")), Type)
  in
  let obj = App (Type, Type) in
  assert (res = obj);

  let res =
    normalize []
    @@ App
         ( Abs ("x", Var "A", App (Abs ("y", Var "B", Var "y"), Var "x"))
         , Var "z" )
  in
  let obj = Var "z" in
  assert (res = obj);

  let res = normalize [] Nat in
  let obj = Nat in
  assert (res = obj);

  let res = normalize [] Z in
  let obj = Z in
  assert (res = obj);

  let res = normalize [ ("x", (Nat, Some Z)) ] @@ S (Var "x") in
  let obj = S Z in
  assert (res = obj);

  let res = normalize [] @@ Ind (Nat, Z, Abs ("x", Nat, S (Var "x")), S Z) in
  let obj = App (S Z, Z) in
  assert (res = obj);

  let res = normalize [ ("x", (Nat, Some Z)) ] @@ Eq (S (Var "x"), S Z) in
  let obj = Eq (S Z, S Z) in
  assert (res = obj);

  let res = normalize [ ("x", (Nat, Some Z)) ] @@ Refl (S (Var "x")) in
  let obj = Refl (S Z) in
  assert (res = obj);

  let p =
    Pi ("x", Var "A", Pi ("x", Var "A", App (Eq (Var "x", Var "x"), Type)))
  in
  let r =
    Pi
      ("x", Var "A", App (App (App (Var "p", Var "x"), Var "x"), Refl (Var "x")))
  in
  let x = Var "x" in
  let y = Var "x" in
  let e = Refl (Var "x") in
  let res = normalize [ ("x", (Nat, Some Z)) ] @@ J (p, r, x, y, e) in
  let obj =
    App (Pi ("x", Var "A", App (App (App (Var "p", Z), Z), Refl Z)), Z)
  in
  assert (res = obj)

let test_alpha () =
  let res = alpha Type Type in
  let obj = true in
  assert (res = obj);

  let res = alpha (Var "x") (Var "x") in
  let obj = true in
  assert (res = obj);

  let res = alpha (Var "x") (Var "y") in
  let obj = false in
  assert (res = obj);

  let res = alpha (App (Var "f", Var "x")) (App (Var "f", Var "x")) in
  let obj = true in
  assert (res = obj);

  let res = alpha (App (Var "f", Var "x")) (App (Var "f", Var "y")) in
  let obj = false in
  assert (res = obj);

  let res = alpha (Abs ("x", Type, Var "x")) (Abs ("y", Type, Var "y")) in
  let obj = true in
  assert (res = obj);

  let res = alpha (Abs ("x", Type, Var "x")) (Abs ("x", Var "A", Var "x")) in
  let obj = false in
  assert (res = obj);

  let res =
    alpha (Abs ("x", Type, Var "x")) (Abs ("x", Type, App (Var "x", Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res = alpha (Pi ("x", Type, Var "x")) (Pi ("y", Type, Var "y")) in
  let obj = true in
  assert (res = obj);

  let res = alpha (Pi ("x", Type, Var "x")) (Pi ("x", Var "A", Var "x")) in
  let obj = false in
  assert (res = obj);

  let res =
    alpha (Pi ("x", Type, Var "x")) (Pi ("x", Type, App (Var "x", Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res =
    alpha
      (App (Abs ("x", Type, Var "x"), Var "y"))
      (App (Abs ("z", Type, Var "z"), Var "y"))
  in
  let obj = true in
  assert (res = obj);

  let res =
    alpha
      (Abs ("x", Pi ("y", Type, Var "y"), Var "x"))
      (Abs ("w", Pi ("w", Type, Var "w"), Var "w"))
  in
  let obj = true in
  assert (res = obj);

  let res = alpha Nat Nat in
  let obj = true in
  assert (res = obj);

  let res = alpha Z Z in
  let obj = true in
  assert (res = obj);

  let res = alpha (S (Var "x")) (S (Var "y")) in
  let obj = false in
  assert (res = obj);

  let res = alpha (S (Abs ("x", Nat, Var "x"))) (S (Abs ("y", Nat, Var "y"))) in
  let obj = true in
  assert (res = obj);

  let res =
    alpha
      (Ind (Nat, Z, Abs ("x", Nat, S (Var "x")), S Z))
      (Ind (Nat, Z, Abs ("y", Nat, S (Var "y")), S Z))
  in
  let obj = true in
  assert (res = obj);

  let res =
    alpha
      (Ind (Nat, Z, Abs ("x", Nat, S (Var "x")), S Z))
      (Ind (Nat, Z, Abs ("x", Nat, Z), S Z))
  in
  let obj = false in
  assert (res = obj);

  let res = alpha (Eq (Var "x", S (Var "x"))) (Eq (Var "y", S (Var "y"))) in
  let obj = false in
  assert (res = obj);

  let res =
    alpha
      (Eq (Abs ("x", Nat, Var "x"), Abs ("y", Nat, Var "y")))
      (Eq (Abs ("z", Nat, Var "z"), Abs ("w", Nat, Var "w")))
  in
  let obj = true in
  assert (res = obj);

  let res =
    alpha (Refl (Abs ("x", Nat, Var "x"))) (Refl (Abs ("y", Nat, Var "y")))
  in
  let obj = true in
  assert (res = obj);

  let res =
    alpha
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl (Var "x")))
      (J (Nat, Z, Abs ("y", Nat, S (Var "y")), Eq (Var "y", Z), Refl (Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res =
    alpha
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl (Var "x")))
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl Z))
  in
  let obj = false in
  assert (res = obj)

let test_conv () =
  let res = conv [] Type Type in
  let obj = true in
  assert (res = obj);

  let res = conv [] (Var "x") (Var "x") in
  let obj = true in
  assert (res = obj);

  let res = conv [] (Var "x") (Var "y") in
  let obj = false in
  assert (res = obj);

  let res = conv [] (App (Var "f", Var "x")) (App (Var "f", Var "x")) in
  let obj = true in
  assert (res = obj);

  let res = conv [] (App (Var "f", Var "x")) (App (Var "f", Var "y")) in
  let obj = false in
  assert (res = obj);

  let res = conv [] (Abs ("x", Type, Var "x")) (Abs ("y", Type, Var "y")) in
  let obj = true in
  assert (res = obj);

  let res = conv [] (Abs ("x", Type, Var "x")) (Abs ("x", Var "A", Var "x")) in
  let obj = false in
  assert (res = obj);

  let res =
    conv [] (Abs ("x", Type, Var "x")) (Abs ("x", Type, App (Var "x", Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res = conv [] (Pi ("x", Type, Var "x")) (Pi ("y", Type, Var "y")) in
  let obj = true in
  assert (res = obj);

  let res = conv [] (Pi ("x", Type, Var "x")) (Pi ("x", Var "A", Var "x")) in
  let obj = false in
  assert (res = obj);

  let res =
    conv [] (Pi ("x", Type, Var "x")) (Pi ("x", Type, App (Var "x", Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res =
    conv []
      (App (Abs ("x", Type, Var "x"), Var "y"))
      (App (Abs ("z", Type, Var "z"), Var "y"))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (Abs ("x", Pi ("y", Type, Var "y"), Var "x"))
      (Abs ("z", Pi ("w", Type, Var "w"), Var "z"))
  in
  let obj = true in
  assert (res = obj);

  let res = conv [] (App (Abs ("x", Type, Var "x"), Type)) Type in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (App (Abs ("x", Pi ("y", Type, Var "y"), Var "x"), Type))
      (App (Abs ("z", Pi ("w", Type, Var "w"), Var "z"), Type))
  in
  let obj = true in
  assert (res = obj);

  let res = conv [] (App (Abs ("x", Type, Var "x"), Type)) Type in
  let obj = true in
  assert (res = obj);

  let res =
    conv [] (App (Abs ("x", Type, App (Var "x", Type)), Type)) (App (Type, Type))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv [] (App (Abs ("x", Pi ("y", Type, Var "y"), Var "x"), Type)) Type
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (App (Abs ("x", Type, Abs ("y", Type, Var "x")), Type))
      (Abs ("y", Type, Type))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (App (Abs ("x", Type, App (Abs ("y", Type, Var "y"), Var "x")), Type))
      (App (Abs ("y", Type, Var "y"), Type))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (App (Abs ("x", Pi ("y", Type, Var "y"), Abs ("z", Type, Var "z")), Type))
      (Abs ("z", Type, Var "z"))
  in
  let obj = true in
  assert (res = obj);

  let res = conv [] Nat Nat in
  let obj = true in
  assert (res = obj);

  let res = conv [] Z Z in
  let obj = true in
  assert (res = obj);

  let res = conv [ ("x", (Nat, None)) ] (S (Var "x")) (S (Var "x")) in
  let obj = true in
  assert (res = obj);

  let res =
    conv [ ("x", (Nat, None)); ("y", (Nat, None)) ] (S (Var "x")) (S (Var "y"))
  in
  let obj = false in
  assert (res = obj);

  let res =
    conv []
      (Ind (Nat, Z, Abs ("x", Nat, S (Var "x")), S Z))
      (Ind (Nat, Z, Abs ("y", Nat, S (Var "y")), S Z))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv []
      (Ind (Nat, Z, Abs ("x", Nat, S (Var "x")), S Z))
      (Ind (Nat, Z, Abs ("x", Nat, Z), S Z))
  in
  let obj = false in
  assert (res = obj);

  let res =
    conv
      [ ("x", (Nat, None)) ]
      (Eq (Var "x", S (Var "x")))
      (Eq (Var "x", S (Var "x")))
  in
  let obj = true in
  assert (res = obj);

  let res =
    conv [ ("x", (Nat, None)) ] (Eq (Var "x", S (Var "x"))) (Eq (Var "x", Z))
  in
  let obj = false in
  assert (res = obj);

  let res =
    conv [] (Refl (Abs ("x", Nat, Var "x"))) (Refl (Abs ("y", Nat, Var "y")))
  in
  let obj = true in
  assert (res = obj);

  let res = conv [] (Refl (Abs ("x", Nat, Var "x"))) (Refl Z) in
  let obj = false in
  assert (res = obj);

  let res =
    conv
      [ ("x", (Nat, None)); ("y", (Nat, None)) ]
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl (Var "x")))
      (J (Nat, Z, Abs ("y", Nat, S (Var "y")), Eq (Var "y", Z), Refl (Var "y")))
  in
  let obj = false in
  assert (res = obj);

  let res =
    conv
      [ ("x", (Nat, None)) ]
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl (Var "x")))
      (J (Nat, Z, Abs ("x", Nat, S (Var "x")), Eq (Var "x", Z), Refl Z))
  in
  let obj = false in
  assert (res = obj)

let test_infer () =
  let () =
    try
      let res = infer [] Type in
      let obj = Type in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res = infer [ ("x", (Type, None)) ] @@ Var "x" in
      let obj = Type in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res = infer [] @@ Abs ("x", Type, Var "x") in
      let obj = Pi ("x", Type, Type) in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res = infer [] @@ App (Abs ("x", Type, Var "x"), Type) in
      let obj = Type in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res = infer [] @@ Pi ("x", Type, Var "x") in
      let obj = Type in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res = infer [ ("y", (Type, None)) ] @@ Abs ("x", Var "y", Var "x") in
      let obj = Pi ("x", Var "y", Var "y") in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      let res =
        infer [ ("y", (Type, None)) ] @@ App (Abs ("x", Var "y", Var "x"), Type)
      in
      let obj = Var "y" in
      ignore (res = obj);
      assert false
    with
    | Type_error _ -> assert true
  in

  let () =
    try
      let res =
        infer [ ("y", (Type, None)) ]
        @@ Pi ("x", Var "y", Pi ("z", Var "y", Var "x"))
      in
      let obj = Type in
      ignore (res, obj);
      assert false
    with
    | Type_error _ -> assert true
  in

  let () =
    try
      let res = infer [ ("y", (Type, None)) ] @@ Abs ("x", Type, Var "y") in
      let obj = Pi ("x", Type, Type) in
      assert (res = obj)
    with
    | Type_error _ -> assert false
  in

  ()

let test_check () =
  let () =
    try
      check [] Type Type;
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check [ ("x", (Type, None)) ] (Var "x") Type;
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check [] (Abs ("x", Type, Var "x")) (Pi ("x", Type, Type));
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check [] (App (Abs ("x", Type, Var "x"), Type)) Type;
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check [] (Pi ("x", Type, Var "x")) Type;
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check
        [ ("y", (Type, None)) ]
        (Abs ("x", Var "y", Var "x"))
        (Pi ("x", Var "y", Var "y"));
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check
        [ ("y", (Type, None)) ]
        (App (Abs ("x", Var "y", Var "x"), Type))
        (Var "y");
      assert false
    with
    | Type_error _ -> assert true
  in

  let () =
    try
      check [] (Pi ("x", Type, Pi ("y", Var "x", Var "x"))) Type;
      assert true
    with
    | Type_error _ -> assert false
  in

  let () =
    try
      check [] (Abs ("x", Type, Var "y")) (Pi ("x", Type, Type));
      assert false
    with
    | Type_error _ -> assert true
  in

  let () =
    try
      check
        [ ("A", (Type, None)); ("B", (Type, None)) ]
        (App
           ( Abs ("f", Pi ("x", Var "A", Var "B"), Var "f")
           , Abs ("x", Var "A", Var "x") ) )
        (Pi ("x", Var "A", Var "B"));
      assert false
    with
    | Type_error _ -> assert true
  in

  ()

(** General testing function *)

let test_all_functions () =
  Format.printf "\n\nTests for dependent prover :\n%!";

  test_to_string ();
  test_subst ();
  test_string_of_context ();
  test_normalize ();
  test_alpha ();
  test_conv ();
  test_infer ();
  test_check ();

  Format.printf "\nDependent prover : OK\n\n%!"
