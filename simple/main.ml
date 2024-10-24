(** Config *)

let () = Printexc.record_backtrace true

(** Main *)

let () =
  Test.all_test ();
  Format.printf "simple : OK\n%!"
