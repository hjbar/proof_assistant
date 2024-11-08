(** Config *)

let () = Printexc.record_backtrace true

(** Main *)

let () =
  if Array.length Sys.argv = 1 then Proving.main ()
  else if Array.length Sys.argv = 2 && Sys.argv.(1) = "--tests" then
    Test.test_all_functions ()
  else begin
    Format.eprintf
      "usage: %s (run the interactive prover)@\n\
       usage: %s --debug (run the tests)@\n"
      Sys.argv.(0) Sys.argv.(0);
    exit 1
  end
