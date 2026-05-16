(*
  amendmentScript — constitutional amendment: a MOVABLE meta-invariant
  over an ETERNAL bedrock (Pillar B of the bigger vision).

  Until now `meta` was the immovable root of the spec tower (specNeg):
  the inhabitant could negotiate the policy, the prover build, the kernel,
  and the spec — but never the meta-invariant itself. Honest, but it is
  also what made svenvs feel like a constitution someone fixed forever.

  This file lifts the SAME discipline ONE more level. There is now an
  eternal `bedrock` (the genuinely immovable floor — e.g. "the inhabitant
  can never make the frozen kernel accept a false soundness statement").
  The meta-invariant becomes itself amendable, gated by a checked proof
  that the proposed `meta'` still refines `bedrock` and is a genuine
  change. The crucial point: this needs NO new machinery — specNeg's gate
  (`spec_admit` / `spec_admit_all` / `spec_admissible`) is already
  meta-agnostic, so we instantiate it VERBATIM with `bedrock` as the fixed
  root and `meta` as the negotiated object. Anti-fragmentation by
  construction: a new layer that is literally the old gate, reused.

  Proved here (pure light HOL4, reusing specNegTheory verbatim; NO new
  `cheat`/axiom/oracle; NO Löb/reflection assumption — the asymmetry
  "FIXED bedrock vouches for a MUTABLE meta" is specNeg's no-Löb argument
  one level up):

   * bedrock_is_eternal — no adversarial stream of meta-amendments can
     ever drop the meta-invariant below the bedrock floor.
   * meta_amendment_safe — THE HEADLINE: with the meta itself amended by
     an arbitrary admitted stream, AND the spec negotiated under the
     amended meta, the running enveloped system still keeps `bedrock`
     for ANY inhabitant. Composed by the IDENTICAL keystone
     (specNegTheory.invariant_transports_to_meta).
   * amendment_subsumes_fixed_meta — specNeg's fixed-meta headline
     (`spec_negotiation_is_safe`, the heart of `svenvs_tower_unconditional`)
     is recovered as a COROLLARY of meta_amendment_safe with an empty
     amendment stream and `bedrock := meta`. The fixed-meta tower is a
     special case of the amendable one — not a separate shard.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory specNegTheory;

val _ = new_theory "amendment";

(* The meta actually in force after an adversarial stream of proposed
   meta-amendments, each gated by specNeg's admission gate at the eternal
   bedrock level. This is `spec_admit_all` reused verbatim, one level up:
   `bedrock` is the fixed root, `meta0` the genesis meta. *)
Definition amended_meta_def:
  amended_meta (bedrock:'s spec) (meta0:'s spec) mproposals =
    spec_admit_all bedrock meta0 mproposals
End

(* The bedrock floor is eternal: starting from any genesis meta that
   refines bedrock, NO admitted stream of meta-amendments — adversarial or
   not — yields a meta that escapes bedrock. (specNeg's
   `spec_admit_all_keeps_refining`, one level up.) *)
Theorem bedrock_is_eternal:
  spec_refines meta0 bedrock ⇒
  ∀mproposals.
    spec_refines (amended_meta bedrock meta0 mproposals) bedrock
Proof
  rw[amended_meta_def] >> metis_tac[spec_admit_all_keeps_refining]
QED

(* THE HEADLINE. The meta-invariant is itself negotiated by an arbitrary
   admitted stream `mproposals`; UNDER that amended meta the inhabitant
   also negotiates the spec; and the envelope is set up for whatever spec
   ends up in force. Then for EVERY inhabitant the running system never
   leaves `bedrock`. `bedrock`, `mproposals`, `newspec`, `ctrl` are all
   universally quantified — bedrock is the only thing never proposable. *)
Theorem meta_amendment_safe:
  spec_refines meta0 bedrock /\
  spec_refines curspec (amended_meta bedrock meta0 mproposals) /\
  envelope_ok_for_spec step init shield pol
     (spec_admit (amended_meta bedrock meta0 mproposals) curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) bedrock
Proof
  rpt strip_tac >>
  (* (a) spec negotiation keeps the (amended) meta, for any inhabitant —
         specNeg's headline reused verbatim at meta := amended_meta. *)
  `!ctrl. invariant step init (enveloped pol shield ctrl)
            (amended_meta bedrock meta0 mproposals)`
    by metis_tac[spec_negotiation_is_safe] >>
  (* (b) the amended meta still refines the eternal bedrock. *)
  `spec_refines (amended_meta bedrock meta0 mproposals) bedrock`
    by metis_tac[bedrock_is_eternal] >>
  (* (c) the IDENTICAL transport keystone: (a) (+) (b) ==> bedrock. *)
  metis_tac[invariant_transports_to_meta]
QED

(* Anti-fragmentation, made precise: specNeg's fixed-meta headline — the
   theorem at the heart of `integration:svenvs_tower_unconditional` — is
   exactly meta_amendment_safe with an EMPTY amendment stream and the
   bedrock taken to be that same meta. The fixed-meta tower is a COROLLARY
   of the amendable one. *)
Theorem amendment_subsumes_fixed_meta:
  spec_refines curspec meta /\
  envelope_ok_for_spec step init shield pol
     (spec_admit meta curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) meta
Proof
  rpt strip_tac >>
  `amended_meta meta meta [] = meta`
    by rw[amended_meta_def, spec_admit_all_def] >>
  `spec_refines meta meta` by rw[spec_refines_refl] >>
  metis_tac[meta_amendment_safe]
QED

val _ = export_theory ();
