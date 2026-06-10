val cakemldir =
  case OS.Process.getEnv "CAKEMLDIR" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/CakeML");
val svenvs =
  case OS.Process.getEnv "SVENVS_ROOT" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/svenvs");
val () = loadPath :=
  map (fn d => OS.Path.concat (cakemldir, d))
      ["semantics", "semantics/ffi", "misc", "basis/pure"]
  @ [OS.Path.concat (svenvs, "reflectsem")] @ !loadPath;
val () = load "fueledSemTheory";
open HolKernel boolLib;

(* type + a few clauses of eval_n *)
val d = DB.fetch "fueledSem" "eval_n_def";
val cjs = strip_conj (concl d);
val () = print ("eval_n clauses: " ^ Int.toString (length cjs) ^ "\n");
val () = print ("eval_n type: " ^
  Hol_pp.type_to_string (type_of (fst (strip_comb
    (fst (dest_eq (snd (strip_forall (hd cjs)))))))) ^ "\n");
val () = print ("=== clause 1 (base) ===\n" ^
  Parse.term_to_string (hd cjs) ^ "\n");
val () = print ("=== clause 4 (Lit?) ===\n" ^
  Parse.term_to_string (List.nth (cjs, 3)) ^ "\n");
val () = print ("=== do_eq_n type ===\n" ^
  Hol_pp.type_to_string (type_of (fst (strip_comb (fst (dest_eq (snd (strip_forall
    (hd (strip_conj (concl (DB.fetch "fueledSem" "do_eq_n_def"))))))))))) ^ "\n");
val () = print "INSPECT_FUELED_OK\n";
