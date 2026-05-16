(*
  integrationKernelScript — the kernel-self-upgrade CROWN of the tower.

  Companion to integrationScript.  Composed by the IDENTICAL keystone
  (specNegTheory.invariant_transports_to_meta): the kernel-self-upgrade
  layer (kernelUpgradeTheory.self_improving_kernel_is_safe) guarantees
  the *negotiated* spec; that transports to the fixed meta-invariant.

  This crown is separated only because its slice pulls the Tier-2 Candle
  set-theoretic semantics (it is NOT pure HOL4 like integrationScript).
  It carries kernelUpgrade's labelled `loeb_reflection` and
  `encodes_obligation` hypotheses VERBATIM — the honest gap is in the
  theorem statement, exactly as in the slice, never hidden.
*)
open HolKernel boolLib bossLib BasicProvers
     specNegTheory kernelUpgradeTheory;

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

val _ = new_theory "integrationKernel";

(* The kernel-self-upgrade crown reaches the fixed meta-invariant,
   for any inhabitant, under exactly kernelUpgrade's labelled seams
   (loeb_reflection + encodes_obligation) — carried verbatim. *)
Theorem svenvs_tower_with_kernel_upgrade:
  spec_refines curspec meta /\
  is_set_theory ^mem /\
  loeb_reflection ^mem candle_kernel K' sound_stmt /\
  (!thy. candle_kernel thy (sound_stmt thy)) /\
  K' thy obl /\
  encodes_obligation ^mem thy obl step curspec oldp newp /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !ctrl.
    invariant step init
      (enveloped (admit step curspec oldp newp) shield ctrl) meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (admit step curspec oldp newp) shield ctrl) curspec`
    by metis_tac[self_improving_kernel_is_safe] >>
  metis_tac[invariant_transports_to_meta]
QED

val _ = export_theory();
