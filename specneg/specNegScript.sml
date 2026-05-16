(*
  specNeg — SPEC-LEVEL negotiation, anchored to an immovable META-INVARIANT.

  --------------------------------------------------------------------------
  THE PROBLEM

  In the core (systemTheory / safetyTheory / upgradeTheory) the safety
  specification `safe : 's -> bool` is FIXED: every theorem reasons about one
  immovable predicate, and the inhabitant may only negotiate the *policy*
  (upgradeTheory) or *prover build* (selfProverScript) underneath that fixed
  spec. This file lifts negotiation ONE LEVEL UP: the inhabitant may now
  propose to change the SAFETY SPEC ITSELF (what counts as "safe"), e.g.
  relax an over-conservative invariant to gain operating envelope.

  Letting the spec move is exactly the seam where Löbian self-reference could
  sneak in (changing the very predicate the proofs reason about). The
  discipline — identical in shape to selfProverScript's frozen HOL4 root and
  kernel/kernelUpgradeScript's frozen Candle kernel — is:

      anchor every negotiable spec to a SEPARATE, FIXED, NON-NEGOTIABLE
      meta-invariant `meta_safe`, and admit a proposed spec ONLY if it
      carries a checked proof that it REFINES `meta_safe`.

  `meta_safe` is the immovable bottom turtle of the SPEC tower. It is a plain
  HOL4 constant-parameter that NOTHING in this theory (or anything the
  inhabitant can reach) ever varies, redefines, or proposes a replacement
  for. There is no `meta_safe'`. The asymmetry "a FIXED meta-property
  vouching for a MUTABLE spec" is NOT "a spec vouching for itself", so this
  layer needs NO reflection principle and NO `loeb_reflection`. The precise
  argument is §5; it is the spec-level analogue of selfProverScript's
  no-Löb capstone.

  --------------------------------------------------------------------------
  WHAT IS PROVED vs ASSUMED

  EVERYTHING here is PROVED outright in pure light HOL4, reusing the built
  generic core (systemTheory / envelopeTheory / safetyTheory /
  sv_weakeningTheory / upgradeTheory) verbatim — the core is NOT re-proved.
  There is NO `cheat`, NO `new_axiom`, NO oracle, and — see §5 — NO labelled
  Löb/reflection assumption is needed at this layer (this is itself one of
  the deliverables: we show the obligation does not arise, rather than
  hiding or assuming it). The single modelling abstraction is that a
  "checked refinement proof" is represented by the HOL4 proposition
  `spec_refines newspec meta_safe` actually holding — i.e. the gate is a
  real proof obligation, exactly as `admissible` is in upgradeTheory.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory;

val _ = new_theory "specNeg";

(* --------------------------------------------------------------------- *)
(* 1. The immovable META-INVARIANT and SPEC REFINEMENT.                   *)
(* --------------------------------------------------------------------- *)

(* A "spec" is just a state predicate — the same type as the core's `safe`.
   The inhabitant negotiates objects of this type; `meta_safe` (below) is a
   distinguished, FIXED one that is never negotiated. *)
Type spec = “:'s -> bool”;

(* `spec_refines newspec meta` : every state the proposed spec `newspec`
   counts as safe also satisfies the meta-invariant `meta`. This is the
   closure that makes the envelope's guarantee TRANSPORT: if the running
   system keeps `newspec` invariant, refinement carries that down to `meta`.

   It is exactly `weaker`-shaped (sv_weakeningTheory.weaker for policies is
   `∀s a. q s a ⇒ p s a`); here it is the state-predicate analogue
   `∀s. newspec s ⇒ meta s`. So `newspec` must be AT LEAST AS STRONG as the
   meta-invariant: relaxing the spec is allowed only down to the meta floor. *)
Definition spec_refines_def:
  spec_refines (newspec:'s spec) (meta:'s spec) ⇔
    ∀s. newspec s ⇒ meta s
End

Theorem spec_refines_refl:
  spec_refines meta meta
Proof
  rw[spec_refines_def]
QED

Theorem spec_refines_trans:
  spec_refines a b ∧ spec_refines b c ⇒ spec_refines a c
Proof
  rw[spec_refines_def] >> metis_tac[]
QED

(* The KEY TRANSPORT lemma: if the running enveloped system keeps the
   (negotiated) spec invariant, and that spec refines the meta-invariant,
   then the system keeps the META-invariant too. This is where a guarantee
   about a MUTABLE spec is converted into a guarantee about the FIXED
   meta-property — the whole point of the architecture. Pure, unconditional,
   directly from systemTheory.invariant_def. *)
Theorem invariant_transports_to_meta:
  invariant step init sel spec ∧ spec_refines spec meta ⇒
  invariant step init sel meta
Proof
  rw[invariant_def, spec_refines_def] >> metis_tac[]
QED

(* --------------------------------------------------------------------- *)
(* 2. NON-VACUITY: a proposed spec must be a GENUINE change.             *)
(* --------------------------------------------------------------------- *)

(* Mirrors upgradeTheory/sv_weakeningTheory's discipline that a self-proposed
   policy upgrade must be a REAL weakening (`weaker newp oldp`), not a no-op.
   Here the analogous "real change" requirement is: the proposed spec must
   not be (extensionally) the meta-invariant itself — relaxing the spec all
   the way down to the bare meta floor is the trivial/vacuous move and is
   rejected, just as proposing `oldp` for `oldp` grants no authority.

   `genuine_spec_change newspec meta` : `newspec` refines `meta` AND is not
   pointwise-equal to `meta` (there is some state `meta` admits that the
   proposed, more conservative spec still excludes — the inhabitant has
   actually committed to *more* than the bare floor). *)
Definition genuine_spec_change_def:
  genuine_spec_change (newspec:'s spec) (meta:'s spec) ⇔
    spec_refines newspec meta ∧ (newspec ≠ meta)
End

Theorem genuine_spec_change_not_meta:
  genuine_spec_change newspec meta ⇒ newspec ≠ meta
Proof
  rw[genuine_spec_change_def]
QED

(* --------------------------------------------------------------------- *)
(* 3. THE SPEC-ADMISSION GATE.                                           *)
(* --------------------------------------------------------------------- *)

(* The proof obligation a self-proposed SPEC must discharge to be installed.
   `meta` is the FIXED meta-invariant (the immovable root); it appears as a
   parameter that is NEVER itself a proposable object. A proposed `newspec`
   is admissible iff it carries a checked proof that it refines `meta` AND is
   a genuine, non-vacuous change. Exactly the shape of
   upgradeTheory.admissible (sound_policy ∧ weaker), one level up. *)
Definition spec_admissible_def:
  spec_admissible (meta:'s spec) (newspec:'s spec) ⇔
    spec_refines newspec meta ∧ genuine_spec_change newspec meta
End

(* The gate: install `newspec` iff it discharged the obligation, otherwise
   keep the current spec `curspec`. An unproven proposal can never move the
   spec. (Analogue of upgradeTheory.admit.) *)
Definition spec_admit_def:
  spec_admit (meta:'s spec) (curspec:'s spec) (newspec:'s spec) =
    if spec_admissible meta newspec then newspec else curspec
End

(* INVARIANT OF THE GATE: any spec the gate ever yields, starting from a spec
   that already refines the meta-invariant, STILL refines the meta-invariant.
   The meta floor is never breached by the gate, accepted or not. *)
Theorem spec_admit_keeps_refining:
  spec_refines curspec meta ⇒
  spec_refines (spec_admit meta curspec newspec) meta
Proof
  rw[spec_admit_def, spec_admissible_def, genuine_spec_change_def]
QED

(* Iterated: fold a whole adversarial STREAM of proposed spec changes through
   the gate. Each is independently obligation-checked; "refines meta" is a
   loop invariant. (Analogue of upgradeTheory.admit_all.) *)
Definition spec_admit_all_def:
  spec_admit_all (meta:'s spec) s0 proposals =
    FOLDL (spec_admit meta) s0 proposals
End

Theorem spec_admit_all_keeps_refining:
  ∀proposals s0.
    spec_refines s0 meta ⇒
    spec_refines (spec_admit_all meta s0 proposals) meta
Proof
  Induct >> rw[spec_admit_all_def] >>
  fs[GSYM spec_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[spec_admit_keeps_refining]
QED

(* --------------------------------------------------------------------- *)
(* 4. THE HEADLINE: spec negotiation never violates the meta-invariant.  *)
(* --------------------------------------------------------------------- *)

(* For the running system to actually enforce the *negotiated* spec we need
   the envelope to be sound for whatever the current spec is. We package the
   core's three premises RELATIVE TO A SPEC: this is a verbatim reuse of the
   core predicates (init_safe / sound_policy / safe_shield) instantiated at
   that spec — no core predicate is redefined. *)
Definition envelope_ok_for_spec_def:
  envelope_ok_for_spec step init shield pol (spec:'s spec) ⇔
    init_safe init spec ∧
    sound_policy step spec pol ∧
    safe_shield step spec shield
End

(* Core reuse, stated once: if the envelope is set up correctly for a spec,
   then for ANY controller the enveloped system keeps THAT spec invariant.
   This is `safetyTheory.safety_preservation` applied verbatim — the core is
   NOT re-proved, only instantiated. *)
Theorem envelope_keeps_its_spec:
  envelope_ok_for_spec step init shield pol spec ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl) spec
Proof
  rw[envelope_ok_for_spec_def] >>
  irule safety_preservation >> fs[]
QED

(*
  THE HEADLINE THEOREM.

  For ANY controller and ANY single inhabitant-proposed spec change, where
  the change is admitted ONLY via the refinement proof (`spec_admit`), the
  enveloped running system NEVER violates the immovable meta-invariant
  `meta` — whether the proposal was accepted or rejected.

  Premises:
    * `spec_refines curspec meta` : the spec currently in force already sits
      above the meta floor (true at genesis, preserved by the gate — §3).
    * `envelope_ok_for_spec ... (spec_admit meta curspec newspec)` : the
      envelope is sound FOR THE SPEC THAT WILL ACTUALLY BE IN FORCE after the
      gate decides (the inhabitant must pay the core premises for whatever
      spec it negotiates — the envelope still does its job at that spec).

  Conclusion: every reachable state of the enveloped system satisfies
  `meta`. `meta` is universally quantified at the front and NEVER appears as
  a proposable object: it is the fixed root, not negotiable. `ctrl` and
  `newspec` are both fully adversarial (∀, never constrained, never
  inspected). *)
Theorem spec_negotiation_is_safe:
  ∀meta step init shield pol curspec newspec.
    spec_refines curspec meta ∧
    envelope_ok_for_spec step init shield pol
        (spec_admit meta curspec newspec) ⇒
    ∀ctrl.
      invariant step init
        (enveloped pol shield ctrl)
        meta
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac ‘invariant step init _ meta’ >>
  ‘∀ctrl. invariant step init (enveloped pol shield ctrl)
            (spec_admit meta curspec newspec)’
    by metis_tac[envelope_keeps_its_spec] >>
  ‘spec_refines (spec_admit meta curspec newspec) meta’
    by metis_tac[spec_admit_keeps_refining] >>
  metis_tac[invariant_transports_to_meta]
QED

(* Spelled-out corollary: every reachable state is meta-safe, for an
   arbitrary controller and an arbitrary admitted spec proposal. *)
Theorem spec_negotiation_states_meta_safe:
  spec_refines curspec meta ∧
  envelope_ok_for_spec step init shield pol
      (spec_admit meta curspec newspec) ∧
  reach step init (enveloped pol shield ctrl) s ⇒
  meta s
Proof
  metis_tac[spec_negotiation_is_safe, invariant_def]
QED

(*
  THE FULLY ADVERSARIAL, UNBOUNDED HEADLINE.

  For ANY controller and ANY adversarial *sequence* of inhabitant-proposed
  spec changes — each accepted ONLY via its own refinement proof through the
  iterated gate — the enveloped system NEVER violates the immovable
  meta-invariant. This is the spec-level analogue of
  upgradeTheory.self_improvement_is_safe (which it does NOT re-prove: the
  core's `safety_preservation` is reused once, via
  `envelope_keeps_its_spec`).

  Note `meta` is ∀-quantified and fixed; `proposals : 's spec list` and
  `ctrl` are fully adversarial; `pol`/`shield` are whatever the envelope is
  configured with for the finally-negotiated spec. *)
Theorem spec_negotiation_unbounded_is_safe:
  ∀meta step init shield pol s0 proposals.
    spec_refines s0 meta ∧
    envelope_ok_for_spec step init shield pol
        (spec_admit_all meta s0 proposals) ⇒
    ∀ctrl.
      invariant step init (enveloped pol shield ctrl) meta
Proof
  rpt strip_tac >>
  ‘∀ctrl. invariant step init (enveloped pol shield ctrl)
            (spec_admit_all meta s0 proposals)’
    by metis_tac[envelope_keeps_its_spec] >>
  ‘spec_refines (spec_admit_all meta s0 proposals) meta’
    by metis_tac[spec_admit_all_keeps_refining] >>
  metis_tac[invariant_transports_to_meta]
QED

(* The meta-invariant is GENUINELY THE IMMOVABLE ROOT: it is not itself
   negotiable. We make this precise as a theorem about the gate — the gate
   only ever ranges over specs that refine `meta`; it can never yield a spec
   that the inhabitant could use to *escape* `meta`, no matter what is
   proposed. (i.e. there is no proposal whose admission drops the meta
   floor.) This is the formal content of "meta is the bottom turtle". *)
Theorem meta_floor_is_never_negotiated:
  ∀meta s0 proposals.
    spec_refines s0 meta ⇒
    ∀s. (spec_admit_all meta s0 proposals) s ⇒ meta s
Proof
  rpt strip_tac >>
  ‘spec_refines (spec_admit_all meta s0 proposals) meta’
    by metis_tac[spec_admit_all_keeps_refining] >>
  fs[spec_refines_def]
QED

(* An un-refining (or vacuous) proposal is INERT: it is dropped by the gate,
   the previously-in-force spec is retained, and the meta guarantee holds via
   the SAME path. (Spec-level analogue of selfProverScript's
   `unvouched_prover_swap_is_inert`.) *)
Theorem unrefining_spec_proposal_is_inert:
  ¬ spec_admissible meta newspec ⇒
  spec_admit meta curspec newspec = curspec
Proof
  rw[spec_admit_def]
QED

(* --------------------------------------------------------------------- *)
(* 5. THE NO-LÖB ARGUMENT (precise) — a deliverable, stated in source.    *)
(* --------------------------------------------------------------------- *)

(*
  Claim: this layer needs NO reflection principle and NO `loeb_reflection`,
  and the obligation genuinely does NOT arise (it is not hidden, not
  assumed-away — we exhibit its absence).

  WHERE LÖB *WOULD* BITE. Self-reference would sneak in if the predicate the
  soundness proof reasons about were ALSO the thing the inhabitant gets to
  re-choose, with the system using its own judgement to vouch for its own
  next judgement. That is precisely the shape of
  kernelUpgradeTheory.loeb_reflection:

      (∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K'

  K (current judge) certifies a statement about K' (its replacement) — judge
  and judged are the SAME KIND OF OBJECT on the SAME LEVEL; a sound K cannot
  prove that schema for free (Gödel/Löb), hence the LCA-discharged labelled
  hypothesis there.

  WHY IT DOES NOT BITE HERE. The negotiated object is the spec `newspec`.
  The thing that vouches for it is `meta` via `spec_refines newspec meta`.
  Three facts, structurally identical to selfProverScript §5 (a) (b) (c):

   (a) DIFFERENT ROLES / DIFFERENT LEVEL. `meta` is a FIXED state predicate
       supplied once (∀-quantified at the front of every headline theorem,
       never the subject of a proposal). `newspec` is the mutable artifact
       on the layer above. A fixed lower property vouching for a higher
       mutable artifact is ordinary refinement, not self-reference — exactly
       as `spec_refines` is just the state-predicate twin of the already-
       sound `sv_weakeningTheory.weaker` discipline.

   (b) THE ROOT NEVER MOVES. There is no `meta'`. Nothing in this theory,
       and nothing the inhabitant can reach, redefines / re-proposes /
       upgrades `meta`. `spec_admit`/`spec_admit_all` range ONLY over the
       `newspec`/`proposals` arguments; `meta` is a constant parameter of
       both. `meta_floor_is_never_negotiated` proves formally that no
       sequence of proposals can yield a spec escaping `meta`. So there is
       no fixed point of "the spec proving its own spec": the certifier
       (`meta`) is never the thing certified.

   (c) NO DIAGONALISATION / NO SELF-PROVING SPEC. The admission obligation
       is `spec_refines newspec meta` — a first-order implication between
       two state predicates, discharged by an ORDINARY HOL4 proof about
       states (see specNegEvalScript: `intLib`/`rw`-level, finite). It is
       NOT "the spec proves its own global soundness". The proofs that
       reason about safety (`safety_preservation`, reused verbatim) are
       carried out about the FIXED `meta` at the top — the mutable
       `newspec` only ever appears UNDER the `spec_refines _ meta`
       hypothesis, never as the thing a proof about itself is closed by.

  Therefore `spec_negotiation_is_safe` /
  `spec_negotiation_unbounded_is_safe` carry NO Löb/reflection hypothesis at
  all — strictly fewer assumptions than even selfProverScript (which carries
  the finite-replay `frozen_checker_sound`): here the meta-root is not a
  checker that must be trusted, it is a plain HOL4 predicate, and the
  refinement obligation is discharged by an ordinary in-logic proof. We
  checked the abstraction does not smuggle self-reference: `meta` and
  `newspec` inhabit the negotiation asymmetrically — `meta` is a fixed
  ∀-bound parameter, `newspec`/`proposals` are the only varied inputs, and
  `meta` is provably never produced-as-output of any admitted negotiation in
  a way that could close a proof about itself (it is only ever a *lower
  bound* the output must clear). This is the same asymmetry as the
  frozen-root capstone, one tower up. The genuinely self-referential
  kernel-replacing-itself seam remains the SEPARATE, already-labelled
  `kernelUpgradeTheory.loeb_reflection` turtle — untouched and unaffected by
  this layer.
*)

val _ = export_theory ();
