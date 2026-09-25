(* =========================================================================
   reflectsem/check_fueled.sml — report every ORIGINAL constant of a fueled
   group that still occurs on the rhs of a generated fueled definition in
   the built fueledSemTheory (fueledSemScript also asserts this at build
   time; this re-checks the stored theory).

   Run on a host with the built CakeML semantics, after building fueledSem:
     cd $CAKEMLDIR/semantics && $HOLDIR/bin/hol < <svenvs>/reflectsem/check_fueled.sml
   ========================================================================= *)
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
      ["semantics", "semantics/ffi", "misc"]
  @ [OS.Path.concat (svenvs, "reflectsem")] @ !loadPath;
val () = load "fueledSemTheory";
val () = load "fueledGenLib";

val bad = fueledGenLib.report_leftovers (
  map (fn (nm, (thy, orig)) =>
         (nm, DB.fetch thy orig, DB.fetch "fueledSem" nm))
  [("pat_bindings_n_def", ("ast", "pat_bindings_def")),
   ("every_exp_n_def", ("ast", "every_exp_def")),
   ("one_con_check_n_def", ("semanticPrimitives", "one_con_check_def")),
   ("do_eq_n_def", ("semanticPrimitives", "do_eq_def")),
   ("pmatch_n_def", ("semanticPrimitives", "pmatch_def")),
   ("v_to_list_n_def", ("semanticPrimitives", "v_to_list_def")),
   ("v_to_char_list_n_def", ("semanticPrimitives", "v_to_char_list_def")),
   ("vs_to_string_n_def", ("semanticPrimitives", "vs_to_string_def")),
   ("concrete_v_n_def", ("semanticPrimitives", "concrete_v_def")),
   ("can_pmatch_all_n_def", ("semanticPrimitives", "can_pmatch_all_def")),
   ("do_test_n_def", ("semanticPrimitives", "do_test_def")),
   ("v_to_word8_list_n_def", ("semanticPrimitives", "v_to_word8_list_def")),
   ("v_to_word64_list_n_def", ("semanticPrimitives", "v_to_word64_list_def")),
   ("compiler_agrees_n_def", ("semanticPrimitives", "compiler_agrees_def")),
   ("do_app_n_def", ("semanticPrimitives", "do_app_def")),
   ("do_eval_n_def", ("semanticPrimitives", "do_eval_def")),
   ("do_eval_res_n_def", ("evaluate", "do_eval_res_def")),
   ("eval_n_def", ("evaluate", "full_evaluate_def"))]);
val () = print (if null bad then "CHECK_FUELED_OK\n" else "CHECK_FUELED_FAIL\n");
