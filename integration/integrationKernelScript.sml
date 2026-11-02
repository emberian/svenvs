(*
  integrationKernelScript — the kernel-self-upgrade CROWN of the tower.

  Companion to integrationScript.  Composed by the IDENTICAL keystone
  (specNegTheory.invariant_transports_to_meta): the kernel-self-upgrade
  layer (kernelUpgradeTheory.self_improving_kernel_is_safe) guarantees
  the *negotiated* spec; that transports to the fixed meta-invariant.

  This crown is separated only because its slice pulls the Tier-2 Candle
  set-theoretic semantics (it is NOT pure HOL4 like integrationScript).
  It carries kernelUpgrade's two encoding seams, `encodes_soundness` and
  `encodes_obligation`, plus the Candle derivation, VERBATIM — the
  honest gap (the soundness witness for K') is in the theorem statement,
  exactly as in the slice, never hidden. No reflection principle is
  assumed.
*)
open HolKernel boolLib bossLib BasicProvers
     specNegTheory kernelUpgradeTheory
     compilerOptTheory fueledBridgeTheory
     evalUpgradeBTheory evalUpgradeOpTheory selfUpgradeEndToEndTheory;

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

val _ = new_theory "integrationKernel";

(* The kernel-self-upgrade crown reaches the fixed meta-invariant, for
   any inhabitant, given a soundness witness for K' (a Candle derivation of
   s in sthy with encodes_soundness) and the obligation encoding — carried
   verbatim. The policy upgrade is decided by the upgraded kernel K' through
   the operational gate `kgate`, so every hypothesis is load-bearing: the
   derivation and the soundness encoding make K' sound
   (kernelUpgradeTheory.certificate_without_reflection_can_breach,
   reflection_without_certificate_can_breach), and K''s soundness plus the
   obligation encoding make its yes safe
   (kernel_unsound_certificate_can_breach,
   embeddedGateTheory.unfaithful_encoding_can_breach). *)
Theorem svenvs_tower_with_kernel_upgrade:
  spec_refines curspec meta /\
  is_set_theory ^mem /\
  candle_kernel sthy s /\
  encodes_soundness ^mem sthy s K' /\
  encodes_obligation ^mem thy obl step curspec oldp newp /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !ctrl.
    invariant step init
      (enveloped (kgate K' thy obl oldp newp) shield ctrl) meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (kgate K' thy obl oldp newp) shield ctrl) curspec`
    by metis_tac[self_improving_kernel_is_safe] >>
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  The Fused Compiler + Prover Self-Upgrade Crown:                   *)
(*  Composes the Tier-2 kernel-self-upgrade crown                     *)
(*  (`svenvs_tower_with_kernel_upgrade`) with:                        *)
(*    - verified BVL optimization passes (`optimise`, `bvl_fold`) and *)
(*      their `cv_eval`-verified benchmark (`bvl_fold_prog`),         *)
(*    - the fueled AST evaluator (`eval_n`) + `ofold` optimizer and   *)
(*      its `cv_eval`-verified benchmark (`ofold_cv_benchmark`),      *)
(*    - the theorem-gated per-generation `Eval` compiler swap         *)
(*      (`lookup_gen_pass_ccorrect`, `eval_gen_bvl_trace_cv_benchmark`). *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_compiler_self_upgrade:
  spec_refines curspec meta /\
  is_set_theory ^mem /\
  candle_kernel sthy s /\
  encodes_soundness ^mem sthy s K' /\
  encodes_obligation ^mem thy obl step curspec oldp newp /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  (!ctrl.
     invariant step init
       (enveloped (kgate K' thy obl oldp newp) shield ctrl) meta) /\
  ccorrect optimise /\
  ccorrect bvl_fold /\
  (!sched g. ccorrect (dispatch_bvl_pass (lookup_gen_pass sched g))) /\
  (bvl_fold_prog demo_bvl_fold_prog =
     [(0, 1, bvl$Op (closLang$IntOp (closLang$Const 42)) []);
      (1, 1, bvl$Op (closLang$IntOp (closLang$Const 42)) [])]) /\
  (ofold demo_ouro_exp = OSub (OLit 10) OVar /\
   ocost demo_ouro_exp = 22 /\
   ocost (ofold demo_ouro_exp) = 3 /\
   ofuel demo_ouro_exp = 14 /\
   ofuel (ofold demo_ouro_exp) = 3) /\
  (eval_gen_bvl_trace [(3, 3); (2, 2); (1, 1)] [0; 1; 2; 3] demo_gen_bvl_exp =
     [(0, 0, 10, demo_gen_bvl_exp);
      (1, 1, 7,
       bvl$If (bvl$Op (closLang$BlockOp (closLang$Cons (backend_common$bool_to_tag T))) [])
              (bvl$Op (closLang$IntOp closLang$Add)
                      [bvl$Op (closLang$IntOp (closLang$Const 20)) [];
                       bvl$Op (closLang$IntOp (closLang$Const 22)) []])
              (bvl$Raise (bvl$Var 0)));
      (2, 2, 1, bvl$Op (closLang$IntOp (closLang$Const 42)) []);
      (3, 2, 1, bvl$Op (closLang$IntOp (closLang$Const 42)) [])])
Proof
  strip_tac >>
  conj_tac
  >- metis_tac[svenvs_tower_with_kernel_upgrade] >>
  simp[optimise_is_ccorrect, bvl_fold_is_ccorrect,
       lookup_gen_pass_ccorrect, bvl_fold_prog_cv_benchmark,
       ofold_cv_benchmark, ocost_def, ofuel_def, arithmeticTheory.MAX_DEF,
       eval_gen_bvl_trace_cv_benchmark]
QED

(* ------------------------------------------------------------------ *)
(*  The Theorem-Gated Per-Generation Compiler Swap Crown:             *)
(*  Combines the iff necessity laws for `compiler_pass_gate` and      *)
(*  `gated_pass_upgrade` with `dispatch_lookup_gen_pass_eq_gated_pass_upgrade`, *)
(*  `bvl_fold_prog_semantics`, `certified_eval_compiler_swap`, and    *)
(*  `ofold_eval_n_fuel_preserves`.                                    *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_certified_compiler_swap_crown:
  (certifier$sound_certifier chk sem <=>
     !ob old_pass new_pass.
       ccorrect old_pass /\ (sem ob ==> ccorrect new_pass) ==>
       ccorrect (compiler_pass_gate (chk ob) old_pass new_pass)) /\
  (certifier$sound_certifier chk sem <=>
     !ob new_pass gen_now g2pass.
       pass_map_correct g2pass /\ (sem ob ==> ccorrect new_pass) ==>
       pass_map_correct (gated_pass_upgrade (chk ob) new_pass gen_now g2pass)) /\
  (!gen_now pid rest.
     (\g. dispatch_bvl_pass (lookup_gen_pass ((gen_now + 1, pid)::rest) g)) =
     gated_pass_upgrade (cert_bvl_pass_id pid) (dispatch_bvl_pass pid) gen_now
       (\g. dispatch_bvl_pass (lookup_gen_pass rest g))) /\
  (!(ffi:'ffi ffi_state) prog co cc start.
     bvlSem$semantics ffi (fromAList prog) co (bvl_fold_cc cc) start <> Fail ==>
     bvlSem$semantics ffi (fromAList (bvl_fold_prog prog))
       ((I ## MAP (I ## I ## bvl_fold)) o co) cc start =
     bvlSem$semantics ffi (fromAList prog) co (bvl_fold_cc cc) start) /\
  (!cert g2c gen ci ci' gen_now s t s' t' g2c'.
     gen_eval_inv g2c gen ci s t /\
     (cert ==>
        (!j. j <= active_gen t ==> gen j <= gen_now) /\
        gen_now + 1 <= gen (active_gen t + 1)) /\
     certified_eval_compiler_swap cert ci' gen_now g2c (s, t) = (s', t', g2c') ==>
     gen_eval_inv g2c' gen (cgate cert ci ci') s' t' /\
     (dec_s s'.eval_state).compiler = mk_compiler_fun_from_ci (cgate cert ci ci') /\
     g2c' (gen (active_gen t' + 1)) = mk_compiler_fun_from_ci (cgate cert ci ci') /\
     recorded_orac_wf_gen g2c' gen (orac_s t'.eval_state).oracle) /\
  (!p (st:'ffi semanticPrimitives$state) env x_val k.
     namespace$nsLookup env.v (namespace$Short «x») =
       SOME (semanticPrimitives$Litv (ast$IntLit x_val)) /\
     ofuel p <= k ==>
     fueledSem$eval_n k (INL (st, env, [oemb (ofold p)])) =
       fueledSem$eval_n k (INL (st, env, [oemb p])) /\
     fueledSem$eval_n k (INL (st, env, [oemb (ofold p)])) =
       INL (st, semanticPrimitives$Rval [semanticPrimitives$Litv (ast$IntLit (oexp_eval x_val p))]) /\
     ofuel (ofold p) <= ofuel p)
Proof
  rpt conj_tac
  >| [
    simp[Once sound_certifier_iff_compiler_pass_gate_safe],
    simp[Once sound_certifier_iff_gated_pass_upgrade_safe],
    ACCEPT_TAC dispatch_lookup_gen_pass_eq_gated_pass_upgrade,
    rw[bvl_fold_prog_semantics],
    rpt gen_tac >> strip_tac >>
      drule_then (drule_at (Pos last))
        certified_eval_compiler_swap_transitions_gen_eval_inv >>
      simp[],
    rpt gen_tac >> strip_tac >>
      drule_all ofold_eval_n_fuel_preserves >>
      disch_then (qspec_then `st` strip_assume_tac) >>
      fs[]
  ]
QED

val _ = export_theory();
