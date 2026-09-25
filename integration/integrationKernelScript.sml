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
     specNegTheory kernelUpgradeTheory;

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

val _ = export_theory();
