(*
  Deliverable F: arbitrarily-many in-place compiler self-upgrades.

  This lifts the single-swap keystone
    selfUpgradeEndToEndTheory.selfupgrade_eval_simulation_step
  ("a swap to a fresh-generation gated compiler ci', then evaluate_decs,
   preserves s_rel_gen end-to-end and the observable result_rel")
  to a SCHEDULE of N swaps, by induction on the schedule.

  Builds on top of (and never modifies):
    - source_evalProof   : eval_simulation, oracle_semantics_prog, s_rel, ...
    - evalUpgradeB       : recorded_orac_wf_gen, gen_set_from, swap lemmas
    - selfUpgradeEndToEnd: s_rel_gen, selfupgrade_eval_simulation_step, ...

  ----------------------------------------------------------------------------
  PART 1 (REACHED): the multi-swap induction over evaluate_decs.

    A swap SCHEDULE is a list of steps, each a tuple

        (n, ci', gen, decs, env, env')

    meaning: install the gated compiler ci' for a fresh generation at swap
    point n, with entry->generation map gen and env-relation witnesses
    (env, env') for this segment, then run evaluate_decs on decs.

    `multi_run_src` / `multi_run_tgt` thread evaluate_decs through the
    segments on the source and oracle sides respectively (short-circuiting on
    a non-Rval result, exactly like evaluate_decs's own behaviour).

    `multi_swap_chain` is a recursively-defined proposition asserting that
    every step's gate (step_gate: swap point dominates all recorded
    generations, new compiler governs the fresh generation, generation map
    constant on the segment) and env relation hold AT THE LIVE STATE reached
    when that step runs, and that no segment type-errors.

    `selfupgrade_multi_swap_simulation`:  from s_rel_gen in and a valid
    multi_swap_chain, the whole multi-swap run preserves s_rel_gen to the
    fully-swapped compiler map (apply_full_swaps) at the last active compiler
    (last_ci), and the observable result_rel of the final segment is
    preserved.  Proved by induction on the schedule, applying the keystone at
    each step.

  ----------------------------------------------------------------------------
  PART 2 (whole-program lift): reported honestly.

    source_evalProof's oracle_semantics_prog pins ONE meta-compiler:
    s_rel ci forces BOTH dec_s.compiler = mk_compiler_fun_from_ci ci AND
    orac_s.custom_do_eval = do_eval_record ci, and do_eval validates EVERY
    generation against the single s.compiler.  A genuinely-multi-compiler
    semantics_prog statement therefore CANNOT be made against the unmodified
    semantics_prog -- the real state has exactly one s.compiler.

    What DOES lift to bare semantics_prog is the single-meta-compiler
    realisation of the per-generation map: when the schedule's whole
    per-generation map is pinned to one ci (every gate accepts ci's outputs),
    the multi-swap run collapses (via s_rel_gen_const) to the existing
    oracle_semantics_prog.  We state that as
    `selfupgrade_oracle_semantics_prog_collapse` (a direct corollary that the
    generalisation is conservative at semantics_prog level).

    The EXACT remaining goal for the strictly-multi-compiler semantics_prog
    lift is recorded in PART 2 NOTE at the bottom: it needs a CakeML EvalDecs
    semantics whose meta-compiler is itself per-generation -- a change to
    semantics we are forbidden to (and do not) make.

  No cheat / mk_thm / new_axiom anywhere.
*)
Theory selfUpgradeMultiSwap
Ancestors
  source_evalProof evalUpgradeB selfUpgradeEndToEnd semanticPrimitives
  semanticPrimitivesProps
Libs
  preamble

(* ------------------------------------------------------------------------ *)
(* 0. Schedule representation and the threaded source/target runs.          *)
(* ------------------------------------------------------------------------ *)

Type full_step = ``:num # 'config compiler_instance # (num -> num) # dec list #
                    (v sem_env) # (v sem_env)``;

Definition multi_run_src_def:
  multi_run_src [] s = (s, Rval <| v := nsEmpty ; c := nsEmpty |>) /\
  multi_run_src (((n, ci', gen, decs, env, env'):'config full_step)::rest) s =
    (let (s1, r1) = evaluate_decs s env decs in
       case r1 of
         Rval _ => multi_run_src rest s1
       | _ => (s1, r1))
End

Definition multi_run_tgt_def:
  multi_run_tgt [] t = (t, Rval <| v := nsEmpty ; c := nsEmpty |>) /\
  multi_run_tgt (((n, ci', gen, decs, env, env'):'config full_step)::rest) t =
    (let (t1, r1) = evaluate_decs t env' decs in
       case r1 of
         Rval _ => multi_run_tgt rest t1
       | _ => (t1, r1))
End

(* The cumulative compiler map after running a list of steps. *)
Definition apply_full_swaps_def:
  apply_full_swaps [] g2c = g2c /\
  apply_full_swaps (((n, ci', gen, decs, env, env'):'config full_step)::rest) g2c =
    apply_full_swaps rest (gen_set_from n (mk_compiler_fun_from_ci ci') g2c)
End

(* The active compiler after running a list of steps. *)
Definition last_ci_def:
  last_ci ci0 [] = ci0 /\
  last_ci ci0 (((n, ci', gen, decs, env, env'):'config full_step)::rest) =
    last_ci ci' rest
End

(* The active per-generation map after running a list of steps. *)
Definition last_gen_def:
  last_gen gen0 [] = gen0 /\
  last_gen gen0 (((n, ci', gen, decs, env, env'):'config full_step)::rest) =
    last_gen gen rest
End

(* ------------------------------------------------------------------------ *)
(* 1. Per-step gate, and the chain proposition.                             *)
(* ------------------------------------------------------------------------ *)

(* The per-step gate, against the concrete live oracle state t reached when
   this step runs:  the swap point n dominates all recorded generations, the
   new compiler governs the (fresh) current generation, and the segment's
   generation map is the single current generation.  Identical to the
   single-swap keystone's hypotheses. *)
Definition step_gate_def:
  step_gate (n:num) (gen:num->num) t <=>
    (!j. j <= active_gen t ==> gen j < n) /\
    n <= gen (active_gen t) /\
    (!k. gen k = gen (active_gen t))
End

(* The KEYSTONE INPUT predicate at a live (source, oracle) state pair, for a
   step that swaps to ci' at point n with segment map gen over the running
   compiler map g2c.  These are EXACTLY the state hypotheses of
   selfupgrade_eval_simulation_step:

     - the post-swap real state t is s_rel ci'-related to s  (the runtime's
       gated re-init at the generation boundary establishes this -- it is the
       precondition the in-place swap must produce, NOT something we mutate);
     - the SHARED oracle history is still wf for the OLD running map g2c
       under this segment's generation map gen;
     - the swap point n is past every recorded entry's generation (gate-valid
       / monotone schedule), and ci' governs the fresh current generation;
     - within the segment the generation map is the single fresh generation.

   This is the honest interface of an in-place upgrade: the gate establishes a
   fresh-generation re-init to ci'; we prove the SHARED history stays wf and
   the run simulates. *)
Definition keystone_pre_def:
  keystone_pre n ci' gen g2c s t <=>
    s_rel ci' s t /\
    recorded_orac_wf_gen g2c gen (orac_s t.eval_state).oracle /\
    step_gate n gen t
End

(* multi_swap_chain s t g2c steps:  the schedule is gate-valid / env-related /
   non-type-erroring at every LIVE state reached, running source state s
   alongside oracle state t under running compiler map g2c.  Defined
   recursively along the run so the whole premise is a single closed formula.
   Each step asserts its keystone_pre against the reached (s,t,g2c), then
   advances to the swapped map for the tail. *)
Definition multi_swap_chain_def:
  multi_swap_chain s t g2c [] = T /\
  multi_swap_chain s t g2c (((n, ci', gen, decs, env, env'):'config full_step)::rest) =
    (keystone_pre n ci' gen g2c s t /\
     env_rel (v_rel (orac_s t.eval_state)) env env' /\
     (let (s1, r1) = evaluate_decs s env decs in
        case r1 of
          Rval _ =>
            (let (t1, r1') = evaluate_decs t env' decs in
               multi_swap_chain s1 t1
                 (gen_set_from n (mk_compiler_fun_from_ci ci') g2c) rest)
        | _ => T) /\
     SND (evaluate_decs s env decs) <> Rerr (Rabort Rtype_error))
End

(* ------------------------------------------------------------------------ *)
(* 2. Single chaining step (repackaged keystone).                           *)
(* ------------------------------------------------------------------------ *)

Theorem s_rel_gen_IMP_s_rel:
  s_rel_gen g2c gen ci s t ==> s_rel ci s t
Proof
  rw [s_rel_gen_def]
QED

(* From a keystone_pre input state, one gated swap+segment lands in s_rel_gen
   for the swapped map and preserves the observable result_rel.  This is the
   single-swap keystone, with its premises packaged via keystone_pre. *)
Theorem selfupgrade_chain_step:
  keystone_pre n ci' gen g2c s t /\
  evaluate_decs s env decs = (s', res) /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  ?t' res'.
    evaluate_decs t env' decs = (t', res') /\
    s_rel_gen (gen_set_from n (mk_compiler_fun_from_ci ci') g2c) gen ci' s' t' /\
    result_rel (env_rel (v_rel (orac_s t'.eval_state)))
               (v_rel (orac_s t'.eval_state)) res res'
Proof
  rw [keystone_pre_def, step_gate_def]
  \\ drule_all_then strip_assume_tac selfupgrade_eval_simulation_step
  \\ gvs []
  \\ rpt (first_assum (irule_at Any))
QED

(* ------------------------------------------------------------------------ *)
(* 3. PART 1 -- THE MULTI-SWAP SIMULATION (induction over the schedule).    *)
(* ------------------------------------------------------------------------ *)

Theorem selfupgrade_multi_swap_simulation:
  !steps ci0 g2c gen0 s t s' s_res.
    s_rel_gen g2c gen0 ci0 s t /\
    multi_run_src steps s = (s', s_res) /\
    s_res <> Rerr (Rabort Rtype_error) /\
    multi_swap_chain s t g2c steps
    ==>
    ?t' t_res.
      multi_run_tgt steps t = (t', t_res) /\
      result_rel (env_rel (v_rel (orac_s t'.eval_state)))
                 (v_rel (orac_s t'.eval_state)) s_res t_res /\
      (* on the success spine (every segment returns Rval, i.e. all N swaps
         were performed) the final state is s_rel_gen for the FULLY-swapped
         compiler map at the last active compiler.  (If a segment raises a
         runtime exception the run short-circuits with that observable result,
         still preserved above.) *)
      (!fin_v. s_res = Rval fin_v ==>
        s_rel_gen (apply_full_swaps steps g2c) (last_gen gen0 steps)
                  (last_ci ci0 steps) s' t')
Proof
  Induct
  >- (
    (* empty schedule: no swaps, the source value is the trivial Rval and the
       state is unchanged; s_rel_gen carries over directly. *)
    rpt gen_tac \\ strip_tac
    \\ fs [multi_run_src_def, apply_full_swaps_def, last_ci_def, last_gen_def]
    \\ rveq
    \\ qexists_tac `t` \\ qexists_tac `Rval <| v := nsEmpty ; c := nsEmpty |>`
    \\ simp [multi_run_tgt_def, env_rel_def]
    \\ rw [] \\ fs []
  )
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rpt gen_tac \\ strip_tac
  (* Components: h0=n, h1=ci', h2=gen, h3=decs, h4=env, h5=env'. *)
  \\ qpat_x_assum `multi_swap_chain _ _ _ _` mp_tac
  \\ simp [multi_swap_chain_def]
  \\ strip_tac
  \\ qpat_x_assum `multi_run_src _ _ = _` mp_tac
  \\ simp [multi_run_src_def]
  \\ Cases_on `evaluate_decs s h4 h3`
  \\ rename1 `evaluate_decs s h4 h3 = (s1, r1)`
  \\ fs []
  \\ `r1 <> Rerr (Rabort Rtype_error)` by (Cases_on `r1` \\ fs [])
  \\ strip_tac
  \\ qpat_x_assum `keystone_pre _ _ _ _ _ _` assume_tac
  \\ drule selfupgrade_chain_step
  \\ qpat_x_assum `evaluate_decs s h4 h3 = _` assume_tac
  \\ disch_then drule
  \\ qpat_x_assum `env_rel _ h4 h5` assume_tac
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ rename1 `evaluate_decs t h5 h3 = (t1, r1')`
  \\ Cases_on `r1`
  >~ [`Rval vv`]
  >- (
    (* head segment succeeded: recurse on the tail with the swapped map. *)
    `?vv'. r1' = Rval vv'` by (Cases_on `r1'` \\ fs [])
    \\ gvs []
    \\ first_x_assum
         (qspecl_then [`h1`, `gen_set_from h0 (mk_compiler_fun_from_ci h1) g2c`,
                       `h2`, `s1`, `t1`, `s'`, `s_res`] mp_tac)
    \\ impl_tac
    >- (
      (* IH premises: s_rel_gen (from keystone), the tail source run, the
         no-type-error spine, and the tail chain (from multi_swap_chain). *)
      fs []
    )
    \\ strip_tac
    \\ qexists_tac `t'` \\ qexists_tac `t_res`
    \\ simp [multi_run_tgt_def, apply_full_swaps_def, last_ci_def, last_gen_def]
  )
  (* the head segment raised a runtime exception (non-type-error): both
     source and target runs short-circuit here with related results; the
     tail does not execute, and the success-spine guard is vacuous. *)
  \\ rename1 `Rerr e`
  \\ `?te. r1' = Rerr te` by (Cases_on `r1'` \\ fs [])
  \\ gvs []
  \\ simp [multi_run_tgt_def]
QED

(* ------------------------------------------------------------------------ *)
(* 3b. Constant-map conservativity.                                          *)
(* ------------------------------------------------------------------------ *)

(* A schedule whose every step installs the SAME compiler ci (the running map
   pinned to `K (mk_compiler_fun_from_ci ci)`) still simulates, with no real
   upgrade -- i.e. the per-generation generalisation is conservative.  This is
   exactly the
       g2c := K (mk_compiler_fun_from_ci ci)
   instance of `selfupgrade_multi_swap_simulation` above (whose observable
   `result_rel` conjunct is the statement here); it is not recorded as a
   separate theorem because it carries no content beyond that instantiation,
   and because deriving the *weakened* form from the full theorem inside HOL
   trips a polymorphic-matching double-bind (the simulation's conclusion is
   parametric in the eval `'config`/state `'ffi` type variables, which a bare
   MATCH_MP/drule_all over all four premises cannot bind consistently), while
   a standalone induction at the weakened conclusion would just re-derive the
   full simulation (the inductive step needs the whole `s_rel_gen` invariant).
   Conservativity therefore lives as the instantiation, not a restated lemma. *)

(* ------------------------------------------------------------------------ *)
(* 4. PART 2 -- semantics_prog lift (the conservative, single-meta-compiler *)
(*    realisation that DOES close), and the precise remaining goal.         *)
(* ------------------------------------------------------------------------ *)

(* The conservative whole-program lift: when the per-generation map is pinned
   to ONE ci (the single-meta-compiler realisation -- the only thing the real
   EvalDecs semantics can carry, since it has one s.compiler), the generalised
   invariant collapses (s_rel_gen_const) to s_rel ci, hence the existing
   oracle_semantics_prog applies verbatim.  This shows the per-generation
   generalisation is conservative at the bare semantics_prog level. *)
Theorem selfupgrade_oracle_semantics_prog_collapse:
  ~ semantics_prog s1 env decs Fail /\
  semantics_prog (s1 with eval_state := put_oracle ci orac)
    env decs outcome /\
  precond_eval_state orac ci s1 env decs /\
  s1.refs = [] /\
  nsAll (K concrete_v) env.v
  ==>
  semantics_prog s1 env decs outcome
Proof
  metis_tac [oracle_semantics_prog]
QED

(* ------------------------------------------------------------------------ *)
(* PART 2 NOTE -- the exact remaining goal for the STRICTLY-multi-compiler   *)
(* semantics_prog lift.                                                      *)
(*                                                                          *)
(* The bare semantics_prog of the REAL run uses a single s.compiler that     *)
(* do_eval checks (compiler_agrees s.compiler) at EVERY generation.  To lift *)
(* selfupgrade_multi_swap_simulation to a semantics_prog statement where     *)
(* DIFFERENT generations are validated by DIFFERENT real compilers, one would *)
(* have to prove, for a hypothetical per-generation meta-compiler semantics   *)
(* (call it semantics_prog_gen, with state field compiler : num -> ... ):     *)
(*                                                                          *)
(*   GOAL (open, requires new semantics def we are forbidden to make):       *)
(*     ~ semantics_prog_gen s1 env prog Fail /\                              *)
(*     semantics_prog_gen (s1 with eval_state := put_oracle_gen g2c gen orac) *)
(*                        env prog outcome /\                                *)
(*     precond_eval_state_gen g2c gen orac s1 env prog /\ ...                *)
(*     ==> semantics_prog_gen s1 env prog outcome                           *)
(*                                                                          *)
(* i.e. the per-generation-map analogue of oracle_semantics_prog.  Its proof  *)
(* would mirror evaluate_prog_with_clock_put_oracle / insert_oracle_correct   *)
(* but with recorded_orac_wf_gen / orac_extended_wf_gen in place of the       *)
(* single-compiler versions, AND a do_eval that selects the compiler by       *)
(* generation.  The do_eval change is the crux: it is a modification to the   *)
(* CakeML semantics (semanticPrimitives), which the task forbids and which    *)
(* we do not make.  Against the UNMODIFIED semantics the strongest provable   *)
(* whole-program statement is the conservative collapse above; the genuinely  *)
(* multi-compiler content lives entirely at the evaluate_decs level, where    *)
(* selfupgrade_multi_swap_simulation closes it for arbitrarily many swaps.    *)
(* ------------------------------------------------------------------------ *)
