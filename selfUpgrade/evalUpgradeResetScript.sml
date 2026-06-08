(*
  Deliverable A (RESET model), MACHINE-CHECKED.

  A compiler SELF-UPGRADE at CakeML's real eval semantics, proven sound
  against the real backend: re-initialising the running eval_state to a fresh
  compiler instance ci' keeps eval-correctness, as a corollary of the
  parametric backendProof$source_eval_to_flat_semantics at ev := SOME ci'.

  This is the heap-preserving (store/ffi untouched), checkpoint-restart upgrade
  model -- the eval-environment history is reset, the heap survives.  It is the
  EvalDecs-level operation a self-upgradable root exposes when it does not need
  to preserve the eval-env namespace across the swap.  (The history-PRESERVING
  in-place swap is evalUpgradeB / selfUpgradeEndToEnd / selfUpgradeMultiSwap.)

  Was documentation-only (selfUpgrade/RESET_MODEL.md) because it needs the full
  backendProof chain; promoted here to a checked theory (the selfUpgrade
  Holmakefile already carries backendProof on INCLUDES).
*)
Theory evalUpgradeReset
Ancestors
  backendProof source_evalProof semanticPrimitives backend
Libs
  preamble

(* Upgrading the running compiler to ci' = re-initialising the eval state to
   mk_init_eval_state ci'.  The store/refs/ffi of s are preserved; the
   eval-environment history is reset.  This is exactly add_eval_state for
   ev = SOME ci'. *)
Definition eval_upgrade_def:
  eval_upgrade ci' s = add_eval_state (SOME ci') s
End

Theorem eval_upgrade_thm:
  eval_upgrade ci' s =
    s with eval_state := SOME (mk_init_eval_state ci')
Proof
  rw [eval_upgrade_def, add_eval_state_def]
QED

(* The store and ffi are untouched by the upgrade (the heap survives). *)
Theorem eval_upgrade_ffi:
  (eval_upgrade ci' s).ffi = s.ffi
Proof
  rw [eval_upgrade_def, add_eval_state_ffi]
QED

Theorem eval_upgrade_refs:
  (eval_upgrade ci' s).refs = s.refs
Proof
  rw [eval_upgrade_thm]
QED

(* The headline: a program run from the UPGRADED state is governed by
   eval-correctness AT ci'.  Specialise the parametric eval-correctness theorem
   at ev := SOME ci'.  Upgrading to ANY ci' that is well-formed for the target
   (opt_eval_config_wf) keeps eval sound: the source semantics from the upgraded
   state is reproduced by the compiled flat semantics with the cake oracle for
   ci'. *)
Theorem eval_upgrade_preserves_semantics:
  ~ semantics_prog (eval_upgrade ci' s0) env prog Fail /\
  compile asm_conf (c : config) prog = SOME (b,bm,c') /\
  source_to_flat$compile prim_src_config (source_to_source$compile prog) = (src_c', p') /\
  THE (prim_sem_env (ffi:'ffi ffi_state)) = (s0, env) /\
  opt_eval_config_wf asm_conf c' (SOME ci') /\
  c.source_conf = prim_src_config ==>
  ? syntax_oracle.
  semantics_prog (eval_upgrade ci' s0) env prog (flatSem$semantics
    (mk_flat_install_conf
        (backend_from_flat_tuple_cc asm_conf c)
        (cake_orac asm_conf c' syntax_oracle (SND o config_tuple1) (\ps. ps.flat_prog)))
    s0.ffi p')
Proof
  rw [eval_upgrade_def]
  \\ irule source_eval_to_flat_semantics
  \\ rpt (first_assum (irule_at Any))
  \\ fs []
QED

(* And the reset upgrade is conservative w.r.t. "no upgrade": eval_upgrade to
   the SAME init instance the state already carries is the identity on the
   eval_state's compiler/config (it re-inits to mk_init_eval_state ci', so two
   successive upgrades to ci', ci'' compose as a single upgrade to ci''). *)
Theorem eval_upgrade_idem:
  eval_upgrade ci2 (eval_upgrade ci1 s) = eval_upgrade ci2 s
Proof
  rw [eval_upgrade_thm]
QED
