(* =========================================================================
   reflectsem/fueledSem — FUELED MIRRORS of the recursive functions in the
   cone of CakeML's evaluate.

   Each group below is GENERATED from its stored (pattern-compiled) defining
   theorem by fueledGenLib.define_fueled: a single dispatcher, primitive
   recursion on a fuel argument, recursive/infected calls at fuel-1, ARB at
   fuel 0. These are the definitions exported into the live Candle kernel
   (HOL Light's define cannot take the original nested/clocked recursions);
   the bridge theory proves each mirror agrees with the original for
   sufficient fuel, so a candle theorem about *_n IS a theorem about the
   real CakeML semantics.

   The fuel-infection order below is load-bearing: a group's `ext`
   environment must contain every already-fueled function its body calls.
   ========================================================================= *)
Theory fueledSem
Ancestors
  ast namespace ffi semanticPrimitives evaluate
Libs
  fueledGenLib

val ext0 : fueledGenLib.fuel_env = [];

(* --- pat/exp structural groups (nested recursion through lists) --- *)
val (pat_bindings_n_def, env1) =
  fueledGenLib.define_fueled "pat_bindings_n" ext0 astTheory.pat_bindings_def;

val (every_exp_n_def, env2) =
  fueledGenLib.define_fueled "every_exp_n" ext0 astTheory.every_exp_def;

val (one_con_check_n_def, env3) =
  fueledGenLib.define_fueled "one_con_check_n" ext0
    semanticPrimitivesTheory.one_con_check_def;

(* --- v-recursive groups --- *)
val (do_eq_n_def, env4) =
  fueledGenLib.define_fueled "do_eq_n" ext0
    semanticPrimitivesTheory.do_eq_def;

val (pmatch_n_def, env5) =
  fueledGenLib.define_fueled "pmatch_n" ext0
    semanticPrimitivesTheory.pmatch_def;

val (v_to_list_n_def, env6) =
  fueledGenLib.define_fueled "v_to_list_n" ext0
    semanticPrimitivesTheory.v_to_list_def;

val (v_to_char_list_n_def, env7) =
  fueledGenLib.define_fueled "v_to_char_list_n" ext0
    semanticPrimitivesTheory.v_to_char_list_def;

val (vs_to_string_n_def, env8) =
  fueledGenLib.define_fueled "vs_to_string_n" ext0
    semanticPrimitivesTheory.vs_to_string_def;

val (concrete_v_n_def, env9) =
  fueledGenLib.define_fueled "concrete_v_n" ext0
    semanticPrimitivesTheory.concrete_v_def;

val env_v = List.concat [env1, env2, env3, env4, env5, env6, env7, env8, env9];

(* --- infected (callers of fueled functions; possibly non-recursive) --- *)
val (can_pmatch_all_n_def, env10) =
  fueledGenLib.define_fueled "can_pmatch_all_n" env_v
    semanticPrimitivesTheory.can_pmatch_all_def;

val (do_test_n_def, env11) =
  fueledGenLib.define_fueled "do_test_n" env_v
    semanticPrimitivesTheory.do_test_def;

val env_t = env_v @ env10 @ env11;

val (v_to_word8_list_n_def, env12) =
  fueledGenLib.define_fueled "v_to_word8_list_n" env_t
    semanticPrimitivesTheory.v_to_word8_list_def;

val (v_to_word64_list_n_def, env13) =
  fueledGenLib.define_fueled "v_to_word64_list_n" env_t
    semanticPrimitivesTheory.v_to_word64_list_def;

val env_w = env_t @ env12 @ env13;

(* non-recursive, but calls v_to_word8/64_list and concrete_v: infected *)
val (compiler_agrees_n_def, env_ca) =
  fueledGenLib.define_fueled "compiler_agrees_n" env_w
    semanticPrimitivesTheory.compiler_agrees_def;

val (do_app_n_def, env14) =
  fueledGenLib.define_fueled "do_app_n" env_w
    semanticPrimitivesTheory.do_app_def;

val (do_eval_n_def, env15) =
  fueledGenLib.define_fueled "do_eval_n" (env_w @ env_ca)
    semanticPrimitivesTheory.do_eval_def;

val env_e = env_w @ env14 @ env15;

val (do_eval_res_n_def, env16) =
  fueledGenLib.define_fueled "do_eval_res_n" env_e
    evaluateTheory.do_eval_res_def;

val env_all = env_e @ env16;

(* --- THE EVALUATE GROUP (clocked mutual; fix_clock form) --- *)
val (eval_n_def, env_eval) =
  fueledGenLib.define_fueled "eval_n" env_all
    evaluateTheory.full_evaluate_def;

(* --- no original of any fueled group survives on a generated rhs --- *)
val fueled_groups = [
  ("pat_bindings_n_def", astTheory.pat_bindings_def, pat_bindings_n_def),
  ("every_exp_n_def", astTheory.every_exp_def, every_exp_n_def),
  ("one_con_check_n_def", semanticPrimitivesTheory.one_con_check_def,
   one_con_check_n_def),
  ("do_eq_n_def", semanticPrimitivesTheory.do_eq_def, do_eq_n_def),
  ("pmatch_n_def", semanticPrimitivesTheory.pmatch_def, pmatch_n_def),
  ("v_to_list_n_def", semanticPrimitivesTheory.v_to_list_def, v_to_list_n_def),
  ("v_to_char_list_n_def", semanticPrimitivesTheory.v_to_char_list_def,
   v_to_char_list_n_def),
  ("vs_to_string_n_def", semanticPrimitivesTheory.vs_to_string_def,
   vs_to_string_n_def),
  ("concrete_v_n_def", semanticPrimitivesTheory.concrete_v_def,
   concrete_v_n_def),
  ("can_pmatch_all_n_def", semanticPrimitivesTheory.can_pmatch_all_def,
   can_pmatch_all_n_def),
  ("do_test_n_def", semanticPrimitivesTheory.do_test_def, do_test_n_def),
  ("v_to_word8_list_n_def", semanticPrimitivesTheory.v_to_word8_list_def,
   v_to_word8_list_n_def),
  ("v_to_word64_list_n_def", semanticPrimitivesTheory.v_to_word64_list_def,
   v_to_word64_list_n_def),
  ("compiler_agrees_n_def", semanticPrimitivesTheory.compiler_agrees_def,
   compiler_agrees_n_def),
  ("do_app_n_def", semanticPrimitivesTheory.do_app_def, do_app_n_def),
  ("do_eval_n_def", semanticPrimitivesTheory.do_eval_def, do_eval_n_def),
  ("do_eval_res_n_def", evaluateTheory.do_eval_res_def, do_eval_res_n_def),
  ("eval_n_def", evaluateTheory.full_evaluate_def, eval_n_def)];

val () =
  if null (fueledGenLib.report_leftovers fueled_groups) then ()
  else raise Fail "fueledSem: original constants left on generated rhs";
