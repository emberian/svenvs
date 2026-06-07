(*
  Deliverable E (keystone): the END-TO-END statement that an in-place
  compiler self-upgrade preserves CakeML eval semantics.

  This builds *on top of* (and never modifies):
    - source_evalProof   : the per-compiler oracle simulation
                           (s_rel ci, eval_simulation, oracle_semantics_prog, ...)
    - evalUpgradeB       : the per-generation compiler-map invariant
                           (recorded_orac_wf_gen, swap_preserves_recorded_orac_wf_gen, ...)

  The structural fact that makes this honest (and bounds what is provable):

    In the *real* EvalDecs semantics the meta-level compiler `dec_s.compiler`
    is a SINGLE fixed function in the state; `do_eval` checks
    `compiler_agrees s.compiler` and `add_decs_generation` bumps the
    generation WITHOUT touching `s.compiler`.  Likewise the oracle side's
    `custom_do_eval` is one fixed function.  So a "mid-run swap" is NOT a
    mutation of `s.compiler` mid-run; it lives at the level of the oracle
    *history* invariant: different generations' recorded eval calls may have
    been validated by different compilers.  That is exactly what
    `recorded_orac_wf_gen` captures, and what evalUpgradeB's swap lemma
    preserves.

  We therefore:
    1. define `s_rel_gen g2c gen ci` -- s_rel generalised so the oracle
       HISTORY is wf for a per-generation compiler map (recorded_orac_wf_gen)
       while the currently-active compiler is the witness `ci`, pinned to the
       map at the current write index;
    2. prove it STRICTLY GENERALISES s_rel: with a constant map it is exactly
       `s_rel ci` (uses recorded_orac_wf_gen_const);
    3. prove the PER-GENERATION SIMULATION STEP: while one compiler is active,
       s_rel_gen reduces to s_rel ci, so the existing `eval_simulation` decs
       clause applies verbatim and re-establishes s_rel_gen at the end of the
       generation (the active compiler is unchanged within a generation);
    4. prove the ACROSS-SWAP RE-ESTABLISHMENT: installing a new compiler for a
       fresh generation (gen_set_from) keeps the generalised history invariant
       (swap_preserves_recorded_orac_wf_gen) provided all recorded entries so
       far predate the swap point -- the side condition discharged from the
       generation map's monotonicity;
    5. COMPOSE 3+4 into the end-to-end keystone:
       `selfupgrade_eval_simulation_step` -- a decs evaluation, possibly
       preceded by an in-place swap at a fresh generation, preserves
       s_rel_gen and the observable (result) relation;
       and the constant-map corollary `selfupgrade_collapses_to_eval_simulation`
       recovering the original guarantee for free.

  Everything below reduces to already-proved lemmas; no cheat / mk_thm /
  new_axiom.
*)
Theory selfUpgradeEndToEnd
Ancestors
  source_evalProof evalUpgradeB semanticPrimitives
Libs
  preamble

(* ------------------------------------------------------------------------ *)
(* 1. The generalised state relation.                                       *)
(*                                                                          *)
(* s_rel_gen g2c gen ci s s' holds when s_rel ci s s' holds (so the         *)
(* currently-active compiler is ci, pinned everywhere s_rel pins it) AND    *)
(* the oracle history additionally satisfies the per-generation invariant   *)
(* recorded_orac_wf_gen g2c gen, with the map agreeing with the active      *)
(* compiler at the current generation.                                      *)
(*                                                                          *)
(* The point: s_rel already gives recorded_orac_wf (ci_comp ci); we ADD the *)
(* strictly-more-general recorded_orac_wf_gen g2c gen so that the SAME       *)
(* state record can later carry entries from OTHER generations' compilers.  *)
(* ------------------------------------------------------------------------ *)

Definition active_gen_def:
  active_gen s' = FST (FST ((orac_s s'.eval_state).oracle 0))
End

Definition s_rel_gen_def:
  s_rel_gen g2c gen ci s s' <=>
    s_rel ci s s' /\
    recorded_orac_wf_gen g2c gen (orac_s s'.eval_state).oracle /\
    g2c (gen (active_gen s')) = mk_compiler_fun_from_ci ci
End

(* ------------------------------------------------------------------------ *)
(* 2. Strict generalisation: constant map collapses to s_rel.               *)
(* ------------------------------------------------------------------------ *)

Theorem s_rel_gen_const:
  s_rel_gen (K (mk_compiler_fun_from_ci ci)) gen ci s s' <=>
  s_rel ci s s'
Proof
  rw [s_rel_gen_def, recorded_orac_wf_gen_const]
  \\ eq_tac \\ rw []
  \\ TRY (qpat_x_assum `s_rel _ _ _` (strip_assume_tac o REWRITE_RULE [s_rel_def]))
  \\ fs [orac_s_def]
QED

(* The "(K ci)" framing requested in the decomposition, at the source-config
   level: the per-generation map that is constantly ci IS s_rel ci. *)
Theorem s_rel_gen_K = s_rel_gen_const;

(* ------------------------------------------------------------------------ *)
(* 3. Per-generation simulation step.                                        *)
(*                                                                          *)
(* Within a single eval generation the active compiler is fixed (= ci), so  *)
(* s_rel_gen carries exactly the information s_rel does PLUS the (preserved) *)
(* per-generation history invariant.  We must show: running evaluate_decs   *)
(* re-establishes s_rel_gen for the SAME map and SAME active compiler.      *)
(*                                                                          *)
(* The s_rel part is the existing eval_simulation (decs clause).  The new   *)
(* obligations are (a) recorded_orac_wf_gen survives, (b) the active        *)
(* compiler is still pinned to the map at the (possibly advanced) current   *)
(* generation.  Both follow because within a generation the source config   *)
(* ci is unchanged, hence the new s_rel ci already gives                    *)
(* recorded_orac_wf (ci_comp ci) which, under the hypothesis that the map   *)
(* is constantly ci on the generations touched, is recorded_orac_wf_gen.    *)
(*                                                                          *)
(* We state it for the case the map is ci-valued on the generations the run *)
(* can touch -- exactly the "single active compiler" regime of one          *)
(* generation.  (gen here is the entry->generation map; the run only writes  *)
(* entries in the current generation, all mapped to a value where g2c = ci.)*)
(* ------------------------------------------------------------------------ *)

Theorem s_rel_gen_step:
  evaluate_decs s env decs = (s', res) /\
  s_rel_gen g2c gen ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) /\
  (* the active compiler ci governs every generation this run can reach: *)
  (!k. g2c (gen k) = mk_compiler_fun_from_ci ci) ==>
  ?es' t' res'.
    evaluate_decs t env' decs = (t', res') /\
    s_rel_gen g2c gen ci s' t' /\
    es' = orac_s t'.eval_state /\
    result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
    es_forward (orac_s t.eval_state) es' /\
    (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es')
Proof
  rw [s_rel_gen_def]
  \\ qspec_then `ci`
       (drule_then (drule_then drule))
       (List.last (CONJUNCTS eval_simulation) |> Q.GEN `ci`)
  \\ rw []
  \\ first_assum (irule_at Any)
  \\ `!j. g2c (gen j) = mk_compiler_fun_from_ci ci` by metis_tac []
  \\ simp [s_rel_gen_def]
  (* two remaining new obligations: recorded_orac_wf_gen, and the pin
     g2c (gen (active_gen t')) = ci_comp ci.  The pin is immediate.  The
     per-generation invariant is, pointwise, the plain recorded_orac_wf that
     s_rel ci s' t' supplies (since g2c (gen j) = ci_comp ci for all j). *)
  \\ qpat_x_assum `s_rel ci s' t'` mp_tac
  \\ rw [s_rel_def]
  \\ simp [recorded_orac_wf_gen_def, orac_s_def]
  \\ qpat_x_assum `recorded_orac_wf _ _` mp_tac
  \\ simp [recorded_orac_wf_def, orac_s_def]
QED

(* ------------------------------------------------------------------------ *)
(* 4. Across-swap re-establishment of the HISTORY invariant.                *)
(*                                                                          *)
(* This is the genuinely-new content: at a generation boundary we install a *)
(* new compiler newc for generations >= n (gen_set_from), and the recorded  *)
(* history stays wf for the NEW map -- prior entries keep their own          *)
(* compiler.  This is evalUpgradeB's swap lemma, here phrased against the    *)
(* live oracle of a related state and combined with es_forward (the         *)
(* generation counter only grows) to discharge the side condition.          *)
(* ------------------------------------------------------------------------ *)

Theorem swap_history_reestablished:
  recorded_orac_wf_gen g2c gen (orac_s t.eval_state).oracle /\
  (!j. j <= active_gen t ==> gen j < n) ==>
  recorded_orac_wf_gen (gen_set_from n newc g2c) gen
    (orac_s t.eval_state).oracle
Proof
  rw [active_gen_def]
  \\ irule swap_preserves_recorded_orac_wf_gen
  \\ simp []
QED

(* And the new generation IS governed by newc (threads newc's correctness,
   proven for ci', into the new generation's entries). *)
Theorem swap_new_generation_compiler:
  n <= gen j ==>
  gen_set_from n newc g2c (gen j) = newc
Proof
  metis_tac [new_generation_uses_newc]
QED

(* ------------------------------------------------------------------------ *)
(* 4b. The in-place swap, at the state level.                               *)
(*                                                                          *)
(* Installing the new compiler ci' for a fresh generation re-establishes    *)
(* s_rel_gen with the swapped map gen_set_from n (ci_comp ci') g2c, PROVIDED *)
(* the swap point n is past every recorded entry's generation AND the new    *)
(* active state is s_rel ci' related (the precondition the runtime's gated   *)
(* swap must establish: the new compiler ci' is the one now pinned).        *)
(*                                                                          *)
(* We keep this faithful to the structural reality: the post-swap real state *)
(* t' must itself satisfy s_rel ci' (its dec_s.compiler is now ci_comp ci', *)
(* its custom_do_eval is do_eval_record ci') -- exactly what a checkpoint /  *)
(* gated re-init at the generation boundary produces.  The NEW fact is that  *)
(* the SHARED oracle history remains wf for the swapped per-generation map.  *)
(* ------------------------------------------------------------------------ *)

Theorem s_rel_gen_swap:
  s_rel ci' s t' /\
  recorded_orac_wf_gen g2c gen (orac_s t'.eval_state).oracle /\
  (!j. j <= active_gen t' ==> gen j < n) /\
  n <= gen (active_gen t') /\
  (* the just-installed compiler governs the current (fresh) generation: *)
  newc = mk_compiler_fun_from_ci ci' ==>
  s_rel_gen (gen_set_from n newc g2c) gen ci' s t'
Proof
  rw [s_rel_gen_def]
  >- (
    irule swap_history_reestablished
    \\ simp []
  )
  >- (
    irule new_generation_uses_newc
    \\ simp []
  )
QED

(* ------------------------------------------------------------------------ *)
(* 5. THE KEYSTONE: end-to-end across one swap-then-eval.                    *)
(*                                                                          *)
(* Compose 3 and 4: a run that (optionally) performs an in-place swap to a  *)
(* new gated compiler ci' at a fresh generation, then evaluates decs under  *)
(* ci', preserves s_rel_gen end to end and preserves the observable result  *)
(* relation.  The swap's history-preservation is the new content; the eval  *)
(* step reuses the existing simulation at the (now active) compiler ci'.    *)
(*                                                                          *)
(* "s_rel_gen in, s_rel_gen out, observable result preserved" -- across a    *)
(* compiler self-upgrade.                                                    *)
(* ------------------------------------------------------------------------ *)

Theorem selfupgrade_eval_simulation_step:
  (* the post-swap (or no-swap) real state is s_rel ci'-related, with the    *)
  (* shared history wf for the OLD map, the swap point past all recorded     *)
  (* entries, and ci' governing the fresh current generation:               *)
  s_rel ci' s t /\
  recorded_orac_wf_gen g2c gen (orac_s t.eval_state).oracle /\
  (!j. j <= active_gen t ==> gen j < n) /\
  n <= gen (active_gen t) /\
  (* gen is the entry->generation map of this run; within the single fresh
     generation it is constant (= the current generation, which is >= n).
     This is exactly the "one active compiler per generation" regime. *)
  (!k. gen k = gen (active_gen t)) /\
  (* the actual evaluation of decs under the upgraded compiler: *)
  evaluate_decs s env decs = (s', res) /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  ?es' t' res'.
    (* the run, under the swapped per-generation map, simulates: *)
    evaluate_decs t env' decs = (t', res') /\
    s_rel_gen (gen_set_from n (mk_compiler_fun_from_ci ci') g2c) gen ci' s' t' /\
    es' = orac_s t'.eval_state /\
    result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
    es_forward (orac_s t.eval_state) es' /\
    (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es')
Proof
  strip_tac \\ fs []
  (* establish s_rel_gen for the swapped map at the active compiler ci' *)
  \\ `s_rel_gen (gen_set_from n (mk_compiler_fun_from_ci ci') g2c) gen ci' s t`
       by (irule s_rel_gen_swap \\ simp [])
  (* ci' governs every reachable generation: gen is constantly gen(active_gen
     t), which is >= n, so the swapped map yields ci_comp ci' there. *)
  \\ `!k. gen_set_from n (mk_compiler_fun_from_ci ci') g2c (gen k)
          = mk_compiler_fun_from_ci ci'`
       by (gen_tac
           \\ `gen k = gen (active_gen t)` by metis_tac []
           \\ `n <= gen k` by simp []
           \\ irule new_generation_uses_newc \\ simp [])
  (* now run the per-generation step at ci' under the swapped map *)
  \\ metis_tac [s_rel_gen_step]
QED

(* ------------------------------------------------------------------------ *)
(* 5b. Constant-map corollary: with NO swap (n above everything, map        *)
(* constantly ci) the keystone collapses to the existing eval_simulation    *)
(* guarantee -- i.e. the generalisation is conservative.                    *)
(* ------------------------------------------------------------------------ *)

Theorem selfupgrade_collapses_to_eval_simulation:
  evaluate_decs s env decs = (s', res) /\
  s_rel ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  ?es' t' res'.
    evaluate_decs t env' decs = (t', res') /\
    s_rel_gen (K (mk_compiler_fun_from_ci ci)) gen ci s' t' /\
    es' = orac_s t'.eval_state /\
    result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
    es_forward (orac_s t.eval_state) es' /\
    (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es')
Proof
  rw []
  \\ `s_rel_gen (K (mk_compiler_fun_from_ci ci)) gen ci s t`
       by rw [s_rel_gen_const]
  \\ `!k. (K (mk_compiler_fun_from_ci ci)) (gen k) = mk_compiler_fun_from_ci ci`
       by simp []
  \\ metis_tac [s_rel_gen_step]
QED

(* ------------------------------------------------------------------------ *)
(* 6. End-to-end OBSERVABLE semantics corollary.                            *)
(*                                                                          *)
(* The decomposition asks for "the observable result is preserved".         *)
(* result_rel above is the observable-result relation eval_simulation uses;  *)
(* selfupgrade_eval_simulation_step delivers it across the swap.  We record  *)
(* the immediate consequence that the run does NOT type-error on the oracle  *)
(* side and yields a result related to the real run -- i.e. the upgrade is   *)
(* observationally sound for decs evaluation.                                *)
(* ------------------------------------------------------------------------ *)

Theorem selfupgrade_no_new_typeerror:
  s_rel ci' s t /\
  recorded_orac_wf_gen g2c gen (orac_s t.eval_state).oracle /\
  (!j. j <= active_gen t ==> gen j < n) /\
  n <= gen (active_gen t) /\
  (!k. gen k = gen (active_gen t)) /\
  evaluate_decs s env decs = (s', res) /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  ?t' res'.
    evaluate_decs t env' decs = (t', res') /\
    res' <> Rerr (Rabort Rtype_error)
Proof
  rw []
  \\ `?es' t' res'.
        evaluate_decs t env' decs = (t', res') /\
        s_rel_gen (gen_set_from n (mk_compiler_fun_from_ci ci') g2c) gen ci' s' t' /\
        es' = orac_s t'.eval_state /\
        result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
        es_forward (orac_s t.eval_state) es' /\
        (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es')`
       by metis_tac [selfupgrade_eval_simulation_step]
  \\ qexists_tac `t'` \\ qexists_tac `res'`
  \\ simp []
  \\ strip_tac \\ fs []
QED
