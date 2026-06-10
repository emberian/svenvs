(* inspect the TFL primitive definitions of cone functions: do their WFREC
   functionals extract cleanly (RESTRICT? guards?) for the fueled mirror *)
val cakemldir =
  case OS.Process.getEnv "CAKEMLDIR" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/CakeML");
val () = loadPath :=
  map (fn d => OS.Path.concat (cakemldir, d))
      ["semantics", "semantics/ffi", "misc", "basis/pure"] @ !loadPath;
val () = load "evaluateTheory";
open HolKernel boolLib;

fun try_show thy nm =
  (case Lib.total (DB.fetch thy) nm of
     SOME th =>
       (print ("\n=== " ^ thy ^ "$" ^ nm ^ " ===\n");
        print (Parse.thm_to_string th ^ "\n"))
   | NONE => print ("\n=== " ^ thy ^ "$" ^ nm ^ " : ABSENT ===\n"));

(* what's stored for do_eq? *)
val () = List.app (fn n => try_show "semanticPrimitives" n)
  ["do_eq_tupled_primitive_def", "do_eq_curried_def", "do_eq_primitive_def"];
(* names of everything matching primitive in the two theories *)
val () = List.app
  (fn thy =>
    (print ("\n--- " ^ thy ^ " definitions matching primitive/curried ---\n");
     List.app (fn (nm,_) => print ("  " ^ nm ^ "\n"))
       (List.filter (fn (nm,_) =>
          String.isSubstring "primitive" nm orelse
          String.isSubstring "curried" nm)
          (map (fn ((_,nm),x) => (nm,x)) (DB.thy thy)))))
  ["semanticPrimitives", "evaluate", "ast"];
