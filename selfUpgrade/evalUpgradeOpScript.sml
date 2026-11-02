(*
  IMPLEMENT + EXPOSE: the concrete per-generation eval operation.

  The history-preserving in-place compiler self-upgrade was proved sound at the
  abstract per-generation-compiler-map level (evalUpgradeB, selfUpgradeEndToEnd,
  selfUpgradeMultiSwap).  This theory makes the operation CONCRETE: it defines

      do_eval_record_gen g2c decode

  -- an actual `custom_do_eval` value (the field the EvalOracle eval-state
  already carries; NO core-semantics edit) that dispatches the compiler by the
  *calling env's generation* (the generation is `FST env_id`, assigned by
  add_env_generation and validated by lookup_env), records the call exactly as
  source_evalProof's `do_eval_record`, and so realises the per-generation map
  g2c operationally.

  Results:
  - do_eval_record_gen_const : with g2c pinned to one compiler it is *exactly*
    source_evalProof's do_eval_record -- the op strictly generalises the
    existing semantics (conservativity at the do_eval level).
  - do_eval_record_gen_dispatch / _records : the operational read-off (which
    compiler gates a call, and the recorded-oracle shape).
  - do_eval_record_gen_preserves_wf : a step of the op PRESERVES the
    per-generation oracle-wellformedness invariant recorded_orac_wf_gen -- the
    concrete operational counterpart of evalUpgradeB's abstract swap lemma.
  - install_compiler / repl_upgrade : the EXPOSED upgrade entry point (install a
    new compiler for the next generation) and its soundness
    (repl_upgrade_preserves_recorded_orac_wf_gen) -- the swap a self-upgradable
    root performs, reduced to evalUpgradeB's swap_preserves lemma.

  Honestly bounded: this is the EvalOracle-level realisation (the mode the
  compiler proof uses); carrying it as the running EvalDecs root is the
  re-bootstrap step, still open.

  No cheat / mk_thm / new_axiom.
*)
Theory evalUpgradeOp
Ancestors
  source_evalProof evalUpgradeB semanticPrimitives certifier compilerOpt cv_std
Libs
  preamble cv_transLib

(* ------------------------------------------------------------------------ *)
(* The concrete per-generation custom_do_eval.                              *)
(* ------------------------------------------------------------------------ *)

(* Identical to source_evalProof$do_eval_record, except the agreement gate
   uses the compiler for THIS call's generation, g2c (FST env_id), instead of
   a single pinned compiler; and the source-dec decoder `decode` is taken as a
   parameter (shared across generations, as in the running root). *)
Definition do_eval_record_gen_def:
  do_eval_record_gen (g2c:num->compiler_fun) decode vs (orac : eval_oracle_fun) =
    case vs of
    | [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] =>
      (let ((i, _), st, _) = orac 0 in
       case (v_to_env_id env_id_v, decode decs_v) of
       | (SOME env_id, SOME decs) =>
         if compiler_agrees (g2c (FST env_id)) (env_id, st_v, decs)
              (st_v2, bs_v, ws_v) /\ st_v = st
         then
           (let orac' = (\j. if j = 0 then ((i + 1, 0), st_v2, [])
                             else if j = SUC i then (env_id, st, decs)
                             else orac j)
            in SOME (env_id, orac', decs))
         else NONE
       | _ => NONE)
    | _ => NONE
End

(* CONSERVATIVITY: pinned to one compiler ci (and ci's dec decoder), the op is
   exactly the existing do_eval_record ci.  So the per-generation op strictly
   generalises CakeML's eval-record semantics. *)
Theorem do_eval_record_gen_const:
  do_eval_record_gen (K (mk_compiler_fun_from_ci ci))
                     (v_fun_abs ci.decs_dom ci.decs_v) =
  do_eval_record ci
Proof
  rw [FUN_EQ_THM, do_eval_record_gen_def, do_eval_record_def]
  \\ rpt (TOP_CASE_TAC \\ fs [])
QED

(* DISPATCH read-off: when the op accepts a call, the compiler that gated it is
   the one for the calling env's generation, and the gate is exactly
   agreement of that compiler with the claimed output. *)
Theorem do_eval_record_gen_dispatch:
  do_eval_record_gen g2c decode
      [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] orac =
      SOME (env_id, orac', decs) ==>
  v_to_env_id env_id_v = SOME env_id /\ decode decs_v = SOME decs /\
  compiler_agrees (g2c (FST env_id)) (env_id, st_v, decs) (st_v2, bs_v, ws_v) /\
  st_v = FST (SND (orac 0))
Proof
  strip_tac
  \\ qabbrev_tac `o0 = orac 0` \\ PairCases_on `o0`
  \\ gvs [do_eval_record_gen_def, AllCaseEqs()]
QED

(* RECORD read-off: the oracle the op installs (entry 0 advanced, the call
   written at the fresh index, all prior entries untouched). *)
Theorem do_eval_record_gen_records:
  do_eval_record_gen g2c decode
      [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] orac =
      SOME (env_id, orac', decs) ==>
  orac' 0 = ((FST (FST (orac 0)) + 1, 0), st_v2, []) /\
  orac' (SUC (FST (FST (orac 0)))) = (env_id, FST (SND (orac 0)), decs) /\
  (!j. j <> 0 /\ j <> SUC (FST (FST (orac 0))) ==> orac' j = orac j)
Proof
  strip_tac
  \\ qabbrev_tac `o0 = orac 0` \\ PairCases_on `o0`
  \\ gvs [do_eval_record_gen_def, AllCaseEqs()]
  \\ rw [] \\ gvs []
QED

(* ------------------------------------------------------------------------ *)
(* OPERATIONAL PRESERVATION of the per-generation invariant.                *)
(* ------------------------------------------------------------------------ *)

(* A step of do_eval_record_gen PRESERVES recorded_orac_wf_gen, provided the
   fresh entry's generation map value agrees with the calling env's generation
   (gen (i+1) = FST env_id) -- the natural consistency between the entry->gen
   map and the generation the call was made in.  This is the concrete
   operational counterpart of evalUpgradeB's abstract swap-preservation: the op
   never disturbs the wellformedness of any previously recorded call and
   discharges the new one with the new generation's compiler. *)
Theorem do_eval_record_gen_preserves_wf:
  do_eval_record_gen g2c decode
      [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] orac =
      SOME (env_id, orac', decs) /\
  recorded_orac_wf_gen g2c gen orac /\
  gen (FST (FST (orac 0)) + 1) = FST env_id ==>
  recorded_orac_wf_gen g2c gen orac'
Proof
  strip_tac
  \\ qabbrev_tac `o0 = orac 0` \\ PairCases_on `o0`
  \\ gvs [do_eval_record_gen_def, AllCaseEqs()]
  \\ qpat_x_assum `recorded_orac_wf_gen g2c gen _` mp_tac
  \\ simp [recorded_orac_wf_gen_def, compiler_agrees_def]
  \\ simp [GSYM ADD1, prim_recTheory.LESS_THM]
  \\ every_case_tac \\ fs []
  \\ rw [] \\ fs []
  \\ qpat_x_assum `compiler_agrees _ _ _` mp_tac
  \\ simp [compiler_agrees_def]
  \\ every_case_tac \\ rw [] \\ gvs []
QED

(* ------------------------------------------------------------------------ *)
(* TIE-IN: the op drives the REAL do_eval.                                   *)
(* ------------------------------------------------------------------------ *)

(* An actual CakeML `do_eval` step on an EvalOracle state whose custom_do_eval
   IS our op preserves the per-generation invariant.  do_eval routes the call
   through `s'.custom_do_eval vs s'.oracle` and then `add_env_generation`, which
   touches generation/envs but NOT the oracle -- so the resulting eval-state's
   oracle is exactly the op's output oracle, and preservation reduces to
   do_eval_record_gen_preserves_wf.  This connects the concrete op to the eval
   semantics the running system actually executes. *)
Theorem do_eval_oracle_gen_step_preserves_wf:
  s'.custom_do_eval = do_eval_record_gen g2c decode /\
  do_eval [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] (SOME (EvalOracle s')) =
    SOME (env, decs, es') /\
  recorded_orac_wf_gen g2c gen s'.oracle /\
  v_to_env_id env_id_v = SOME env_id /\
  gen (FST (FST (s'.oracle 0)) + 1) = FST env_id ==>
  recorded_orac_wf_gen g2c gen (orac_s es').oracle
Proof
  rw [do_eval_def]
  \\ gvs [AllCaseEqs()]
  \\ gvs [orac_s_def, add_env_generation_def]
  \\ imp_res_tac do_eval_record_gen_dispatch
  \\ gvs []
  \\ drule do_eval_record_gen_preserves_wf
  \\ rpt (disch_then drule)
  \\ simp []
QED

(* ------------------------------------------------------------------------ *)
(* EXPOSE: the upgrade entry point and its soundness.                       *)
(* ------------------------------------------------------------------------ *)

(* The exposed operation a self-upgradable root invokes: install a new compiler
   newc for the generations from n onward (n = the next, fresh generation).  At
   the per-generation-map level this is evalUpgradeB's gen_set_from. *)
Definition install_compiler_def:
  install_compiler n newc g2c = gen_set_from n newc g2c
End

(* The running-root view: upgrade to compiler instance ci' for the generation
   after the current one (gen_now), keeping every earlier generation's
   compiler. *)
Definition repl_upgrade_def:
  repl_upgrade ci' gen_now g2c =
    install_compiler (gen_now + 1) (mk_compiler_fun_from_ci ci') g2c
End

(* SOUNDNESS of the exposed upgrade: installing ci' for generation gen_now+1
   preserves the per-generation oracle-wellformedness invariant, provided every
   already-recorded call lives in a generation <= gen_now (a fresh generation,
   the gate's monotone-schedule condition).  Directly evalUpgradeB's
   swap_preserves lemma, instantiated at the exposed operation. *)
Theorem repl_upgrade_preserves_recorded_orac_wf_gen:
  recorded_orac_wf_gen g2c gen orac /\
  (!j. j <= FST (FST (orac 0)) ==> gen j <= gen_now) ==>
  recorded_orac_wf_gen (repl_upgrade ci' gen_now g2c) gen orac
Proof
  rpt strip_tac
  \\ simp [repl_upgrade_def, install_compiler_def]
  \\ irule swap_preserves_recorded_orac_wf_gen
  \\ rw []
  \\ res_tac \\ simp []
QED

(* And the upgraded generation IS governed by the new compiler ci': any future
   call recorded into generation gen_now+1 (or later) has its wf obligation
   discharged by mk_compiler_fun_from_ci ci'. *)
Theorem repl_upgrade_uses_new_compiler:
  gen_now + 1 <= gen j ==>
  repl_upgrade ci' gen_now g2c (gen j) = mk_compiler_fun_from_ci ci'
Proof
  rw [repl_upgrade_def, install_compiler_def]
  \\ irule new_generation_uses_newc
  \\ simp []
QED

(* CONSERVATIVITY of the exposed op: upgrading to the SAME compiler the current
   generation already runs is the identity on the per-generation map at every
   generation up to gen_now. *)
Theorem repl_upgrade_no_op_below:
  k <= gen_now ==> repl_upgrade ci' gen_now g2c k = g2c k
Proof
  rw [repl_upgrade_def, install_compiler_def, gen_set_from_def]
QED

(* ------------------------------------------------------------------------ *)
(* The running loop's STEP: upgrade, then evaluate in the new generation.   *)
(* ------------------------------------------------------------------------ *)

(* The operational heart of the running self-upgrade: install ci' for the next
   generation (update the live custom_do_eval to dispatch the upgraded map),
   then a REAL do_eval in that fresh generation both (a) preserves the
   per-generation oracle-wellformedness invariant AND (b) is gated by the NEW
   compiler ci'.  Composes repl_upgrade_preserves_recorded_orac_wf_gen (the swap
   keeps the invariant), do_eval_oracle_gen_step_preserves_wf (a real do_eval
   step with the upgraded op preserves it), and repl_upgrade_uses_new_compiler
   (the new generation runs ci').  This is one turn of the proof-gated
   recompile->install->resume loop, at the verified eval semantics. *)
Theorem repl_upgrade_then_eval_preserves_wf:
  recorded_orac_wf_gen g2c gen s'.oracle /\
  (!j. j <= FST (FST (s'.oracle 0)) ==> gen j <= gen_now) /\
  do_eval [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v]
    (SOME (EvalOracle (s' with custom_do_eval :=
       do_eval_record_gen (repl_upgrade ci' gen_now g2c) decode))) =
    SOME (env, decs, es') /\
  v_to_env_id env_id_v = SOME env_id /\
  gen (FST (FST (s'.oracle 0)) + 1) = FST env_id /\
  gen_now + 1 <= FST env_id ==>
  recorded_orac_wf_gen (repl_upgrade ci' gen_now g2c) gen (orac_s es').oracle /\
  repl_upgrade ci' gen_now g2c (FST env_id) = mk_compiler_fun_from_ci ci'
Proof
  strip_tac
  \\ qmatch_asmsub_abbrev_tac `EvalOracle st2`
  \\ `st2.custom_do_eval =
        do_eval_record_gen (repl_upgrade ci' gen_now g2c) decode /\
      st2.oracle = s'.oracle` by simp [Abbr `st2`]
  \\ `recorded_orac_wf_gen (repl_upgrade ci' gen_now g2c) gen st2.oracle`
       by (simp []
           \\ irule repl_upgrade_preserves_recorded_orac_wf_gen \\ simp [])
  \\ conj_tac
  >| [
    irule do_eval_oracle_gen_step_preserves_wf
    \\ rpt (first_assum (irule_at Any)) \\ simp [],
    irule repl_upgrade_uses_new_compiler \\ simp []
  ]
QED

(* ------------------------------------------------------------------------ *)
(* ARBITRARILY MANY exposed upgrades, all sound.                            *)
(* ------------------------------------------------------------------------ *)

(* Fold a schedule of in-place upgrades (each (ci, gen_now)) over the map. *)
Definition apply_repl_upgrades_def:
  apply_repl_upgrades [] g2c = g2c /\
  apply_repl_upgrades ((ci,gen_now)::rest) g2c =
    apply_repl_upgrades rest (repl_upgrade ci gen_now g2c)
End

(* Arbitrarily many in-place upgrades ALL preserve the per-generation
   oracle-wellformedness invariant, provided each installs for a fresh
   generation (every already-recorded entry's generation <= that turn's
   gen_now).  The inductive lift of repl_upgrade_preserves_recorded_orac_wf_gen
   -- the verified counterpart of the 64-generation bulk run in
   candle/compiler_cell_upgrade.cml.  (Evaluation between upgrades is covered by
   repl_upgrade_then_eval_preserves_wf.) *)
Theorem apply_repl_upgrades_preserves_wf:
  !ups g2c.
    recorded_orac_wf_gen g2c gen orac /\
    EVERY (\cg. !j. j <= FST (FST (orac 0)) ==> gen j <= SND cg) ups
    ==>
    recorded_orac_wf_gen (apply_repl_upgrades ups g2c) gen orac
Proof
  Induct
  >- rw [apply_repl_upgrades_def]
  \\ rpt strip_tac
  \\ PairCases_on `h`
  \\ fs [apply_repl_upgrades_def]
  \\ first_x_assum irule
  \\ fs []
  \\ irule repl_upgrade_preserves_recorded_orac_wf_gen
  \\ fs []
QED

(* ------------------------------------------------------------------------ *)
(* THEOREM-GATED PER-GENERATION COMPILER CELL (`certified_repl_upgrade` &   *)
(* `gated_pass_upgrade`) + IN-KERNEL `cv_eval` MULTI-GENERATION TRACE.      *)
(* ------------------------------------------------------------------------ *)

Definition certified_repl_upgrade_def:
  certified_repl_upgrade (cert:bool) ci' gen_now g2c =
    cgate cert g2c (repl_upgrade ci' gen_now g2c)
End

Theorem certified_repl_upgrade_installs:
  cert /\ gen_now + 1 <= gen j ==>
  certified_repl_upgrade cert ci' gen_now g2c (gen j) =
    mk_compiler_fun_from_ci ci'
Proof
  rw [certified_repl_upgrade_def, cgate_def]
  \\ irule repl_upgrade_uses_new_compiler
  \\ simp []
QED

Theorem certified_repl_upgrade_rejects:
  ~cert ==> certified_repl_upgrade cert ci' gen_now g2c = g2c
Proof
  rw [certified_repl_upgrade_def, cgate_def]
QED

Theorem certified_repl_upgrade_preserves_wf:
  recorded_orac_wf_gen g2c gen orac /\
  (cert ==> !j. j <= FST (FST (orac 0)) ==> gen j <= gen_now) ==>
  recorded_orac_wf_gen (certified_repl_upgrade cert ci' gen_now g2c) gen orac
Proof
  rw [certified_repl_upgrade_def, cgate_def]
  \\ irule repl_upgrade_preserves_recorded_orac_wf_gen
  \\ simp []
QED

Definition pass_map_correct_def:
  pass_map_correct (g2pass : num -> (bvl$exp -> bvl$exp)) <=>
    !g. ccorrect (g2pass g)
End

Definition gated_pass_upgrade_def:
  gated_pass_upgrade (cert:bool) (new_pass:bvl$exp -> bvl$exp)
                     (gen_now:num) (g2pass:num -> (bvl$exp -> bvl$exp)) =
    cgate cert g2pass (\k. if k < gen_now + 1 then g2pass k else new_pass)
End

Theorem gated_pass_upgrade_preserves_correct:
  sound_certifier chk sem /\
  (sem ob ==> ccorrect new_pass) /\
  pass_map_correct g2pass ==>
  pass_map_correct (gated_pass_upgrade (chk ob) new_pass gen_now g2pass)
Proof
  rw [gated_pass_upgrade_def, cgate_def, sound_certifier_def, pass_map_correct_def]
  \\ rw []
QED

Theorem sound_certifier_iff_gated_pass_upgrade_safe:
  sound_certifier chk sem <=>
    !ob new_pass gen_now g2pass.
      pass_map_correct g2pass /\ (sem ob ==> ccorrect new_pass) ==>
      pass_map_correct (gated_pass_upgrade (chk ob) new_pass gen_now g2pass)
Proof
  eq_tac
  >- metis_tac [gated_pass_upgrade_preserves_correct]
  \\ rw [sound_certifier_def] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspecl_then [`ob`, `bad_bvl_pass`, `0`, `K bvl_fold`] mp_tac)
  \\ impl_tac
  >- simp [pass_map_correct_def, bvl_fold_is_ccorrect]
  \\ simp [gated_pass_upgrade_def, cgate_def, pass_map_correct_def]
  \\ qexists_tac `1`
  \\ simp [bad_bvl_pass_not_ccorrect]
QED

Definition dispatch_bvl_pass_def:
  dispatch_bvl_pass (pid:num) (e:bvl$exp) =
    if pid = 0 then e
    else if pid = 1 then optimise e
    else if pid = 2 then bvl_fold e
    else bad_bvl_pass e
End

Definition cert_bvl_pass_id_def:
  cert_bvl_pass_id (pid:num) <=> pid <= 2
End

Theorem cert_bvl_pass_id_sound:
  !pid. cert_bvl_pass_id pid <=> ccorrect (dispatch_bvl_pass pid)
Proof
  gen_tac \\ simp [cert_bvl_pass_id_def]
  \\ Cases_on `pid = 0`
  >- (`dispatch_bvl_pass 0 = (\e. e)` by rw [FUN_EQ_THM, dispatch_bvl_pass_def]
      \\ gvs [id_is_ccorrect])
  \\ Cases_on `pid = 1`
  >- (`dispatch_bvl_pass 1 = optimise` by rw [FUN_EQ_THM, dispatch_bvl_pass_def]
      \\ gvs [optimise_is_ccorrect])
  \\ Cases_on `pid = 2`
  >- (`dispatch_bvl_pass 2 = bvl_fold` by rw [FUN_EQ_THM, dispatch_bvl_pass_def]
      \\ gvs [bvl_fold_is_ccorrect])
  \\ `dispatch_bvl_pass pid = bad_bvl_pass` by rw [FUN_EQ_THM, dispatch_bvl_pass_def]
  \\ `~(pid <= 2)` by decide_tac
  \\ gvs [bad_bvl_pass_not_ccorrect]
QED

Definition lookup_gen_pass_def:
  lookup_gen_pass [] (g:num) = 0n /\
  lookup_gen_pass ((g_start, pid)::rest) g =
    let prev = lookup_gen_pass rest g in
    cgate (cert_bvl_pass_id pid /\ g_start <= g) prev pid
End

Theorem lookup_gen_pass_ccorrect:
  !sched g. ccorrect (dispatch_bvl_pass (lookup_gen_pass sched g))
Proof
  simp [GSYM cert_bvl_pass_id_sound]
  \\ Induct \\ simp [lookup_gen_pass_def, cgate_def, FORALL_PROD]
  >- simp [cert_bvl_pass_id_def]
  \\ rw []
QED

Theorem dispatch_lookup_gen_pass_step_eq_compiler_pass_gate:
  !g_start pid rest g.
    dispatch_bvl_pass (lookup_gen_pass ((g_start, pid)::rest) g) =
    compiler_pass_gate (cert_bvl_pass_id pid /\ g_start <= g)
      (dispatch_bvl_pass (lookup_gen_pass rest g))
      (dispatch_bvl_pass pid)
Proof
  rw [lookup_gen_pass_def, compiler_pass_gate_def, cgate_def]
QED

Theorem dispatch_lookup_gen_pass_eq_gated_pass_upgrade:
  !gen_now pid rest.
    (\g. dispatch_bvl_pass (lookup_gen_pass ((gen_now + 1, pid)::rest) g)) =
    gated_pass_upgrade (cert_bvl_pass_id pid) (dispatch_bvl_pass pid) gen_now
      (\g. dispatch_bvl_pass (lookup_gen_pass rest g))
Proof
  rw [FUN_EQ_THM, lookup_gen_pass_def, gated_pass_upgrade_def, cgate_def]
  \\ rw [] \\ fs []
QED

Definition eval_gen_bvl_trace_def:
  eval_gen_bvl_trace sched (gens:num list) (e:bvl$exp) =
    MAP (\g. (g, lookup_gen_pass sched g,
              cost (dispatch_bvl_pass (lookup_gen_pass sched g) e),
              dispatch_bvl_pass (lookup_gen_pass sched g) e)) gens
End

val () = cv_auto_trans cgate_def;
val () = cv_auto_trans bad_bvl_pass_def;
val () = cv_auto_trans dispatch_bvl_pass_def;
val () = cv_auto_trans cert_bvl_pass_id_def;
val () = cv_auto_trans lookup_gen_pass_def;
val () = cv_auto_trans eval_gen_bvl_trace_def;

Definition demo_gen_bvl_exp_def:
  demo_gen_bvl_exp : bvl$exp =
    Let []
      (If (Let [] (Op (BlockOp (Cons (bool_to_tag T))) []))
          (Let [] (Op (IntOp Add)
                     [Op (IntOp (Const 20)) [];
                      Op (IntOp (Const 22)) []]))
          (Raise (Var 0)))
End

val () = cv_auto_trans demo_gen_bvl_exp_def;

Theorem eval_gen_bvl_trace_cv_benchmark:
  eval_gen_bvl_trace [(3, 3); (2, 2); (1, 1)] [0; 1; 2; 3] demo_gen_bvl_exp =
    [(0, 0, 10, demo_gen_bvl_exp);
     (1, 1, 7,
      If (Op (BlockOp (Cons (bool_to_tag T))) [])
         (Op (IntOp Add) [Op (IntOp (Const 20)) []; Op (IntOp (Const 22)) []])
         (Raise (Var 0)));
     (2, 2, 1, Op (IntOp (Const 42)) []);
     (3, 2, 1, Op (IntOp (Const 42)) [])]
Proof
  CONV_TAC cv_eval
QED


(* ------------------------------------------------------------------------ *)
(* PROOF-GATED COMPILER SWAP: connecting repl_upgrade to certifier$cgate.   *)
(* ------------------------------------------------------------------------ *)

Definition proof_gated_repl_upgrade_def:
  proof_gated_repl_upgrade (yes:bool) ci' gen_now g2c =
    certified_repl_upgrade yes ci' gen_now g2c
End

Theorem proof_gated_repl_upgrade_preserves_wf:
  !yes ci' gen_now g2c gen orac.
    recorded_orac_wf_gen g2c gen orac /\
    (!j. j <= FST (FST (orac 0)) ==> gen j <= gen_now) ==>
    recorded_orac_wf_gen (proof_gated_repl_upgrade yes ci' gen_now g2c) gen orac
Proof
  rw [proof_gated_repl_upgrade_def]
  \\ irule certified_repl_upgrade_preserves_wf
  \\ simp []
QED

Theorem proof_gated_repl_upgrade_keeps_good:
  !chk sem ob good ci' gen_now g2c.
    sound_certifier chk sem /\
    (sem ob ==> good (repl_upgrade ci' gen_now g2c)) /\
    good g2c ==>
    good (proof_gated_repl_upgrade (chk ob) ci' gen_now g2c)
Proof
  rw [proof_gated_repl_upgrade_def, certified_repl_upgrade_def]
  \\ irule cgate_safe
  \\ metis_tac []
QED

Theorem sound_certifier_iff_repl_upgrade_safe:
  !chk sem good a b.
    good a /\ ~good b ==>
    (sound_certifier chk sem <=>
     !ob old new. good old /\ (sem ob ==> good new) ==> good (cgate (chk ob) old new))
Proof
  metis_tac [sound_certifier_iff_cgate_safe]
QED


