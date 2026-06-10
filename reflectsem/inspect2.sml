val cakemldir =
  case OS.Process.getEnv "CAKEMLDIR" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/CakeML");
val () = loadPath :=
  map (fn d => OS.Path.concat (cakemldir, d))
      ["semantics", "semantics/ffi", "misc", "basis/pure"] @ !loadPath;
val () = load "evaluateTheory";
open HolKernel boolLib;

(* all stored names mentioning do_eq / evaluate / pmatch *)
val () = List.app
  (fn (thy, pat) =>
    (print ("\n--- " ^ thy ^ " names containing '" ^ pat ^ "' ---\n");
     List.app (fn ((_,nm),_) =>
         if String.isSubstring pat nm then print ("  " ^ nm ^ "\n") else ())
       (DB.thy thy)))
  [("semanticPrimitives","do_eq"), ("evaluate","evaluate"),
   ("semanticPrimitives","pmatch"), ("ast","pat_bindings"),
   ("ast","every_exp")];

(* the shape of one *_def_primitive *)
val th = DB.fetch "semanticPrimitives" "v_to_list_def_primitive";
val () = (print "\n=== v_to_list_def_primitive ===\n";
          print (Parse.thm_to_string th ^ "\n"));
