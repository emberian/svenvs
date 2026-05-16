(*
  specNegEval — a small CONCRETE instance of spec-level negotiation, run
  inside the logic with EVAL. Pure light HOL4 (intLib only).

  Scenario (integer pole, same plant family as cartpoleScript):

    state          : the pole offset (int; 0 = upright).

    META-INVARIANT : `meta_box a ⇔ -5 ≤ a ≤ 5`.
                     This is the IMMOVABLE root — the absolute physical
                     limit beyond which the pole has fallen. It is a fixed
                     HOL4 Definition; nothing here negotiates it, and no
                     `meta_box'` exists.

    current spec   : `spec_tight a ⇔ -2 ≤ a ≤ 2`.
                     An over-conservative invariant the inhabitant wants to
                     relax to gain operating envelope. It refines meta_box.

    PROPOSAL A     : `spec_relaxed a ⇔ -4 ≤ a ≤ 4`.
                     A REAL relaxation that STILL refines the meta floor
                     (everything ±4 is within ±5) and is a genuine change
                     (≠ meta_box). Expected: ADMITTED.

    PROPOSAL B     : `spec_overreach a ⇔ -9 ≤ a ≤ 9`.
                     Relaxes PAST the meta floor (±9 admits states ±5 calls
                     unsafe). Does NOT refine meta_box. Expected: REJECTED,
                     gate keeps the previous spec, meta floor intact.

  Every claim below is closed by `EVAL` / `intLib.ARITH_TAC` — computed, not
  asserted — reusing specNegTheory's gate verbatim.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     specNegTheory;

val _ = new_theory "specNegEval";

(* ---- the FIXED meta-invariant: the immovable root --------------------- *)
Definition meta_box_def:
  meta_box (a:int) ⇔ -5 ≤ a ∧ a ≤ 5
End

(* ---- the current (over-conservative) spec ----------------------------- *)
Definition spec_tight_def:
  spec_tight (a:int) ⇔ -2 ≤ a ∧ a ≤ 2
End

(* ---- proposal A: a genuine refining relaxation ------------------------ *)
Definition spec_relaxed_def:
  spec_relaxed (a:int) ⇔ -4 ≤ a ∧ a ≤ 4
End

(* ---- proposal B: an over-reaching, NON-refining relaxation ------------ *)
Definition spec_overreach_def:
  spec_overreach (a:int) ⇔ -9 ≤ a ∧ a ≤ 9
End

(* The current spec already sits above the meta floor. *)
Theorem tight_refines_meta:
  spec_refines spec_tight meta_box
Proof
  rw[spec_refines_def, spec_tight_def, meta_box_def] >> intLib.ARITH_TAC
QED

(* PROPOSAL A genuinely refines the meta floor. *)
Theorem relaxed_refines_meta:
  spec_refines spec_relaxed meta_box
Proof
  rw[spec_refines_def, spec_relaxed_def, meta_box_def] >> intLib.ARITH_TAC
QED

(* PROPOSAL A is a genuine (non-vacuous) change: not the bare meta floor.
   Witness: state 5 is meta_box-safe but NOT spec_relaxed-safe, so the two
   predicates differ. *)
Theorem relaxed_is_genuine_change:
  genuine_spec_change spec_relaxed meta_box
Proof
  rw[genuine_spec_change_def]
  >- (rw[spec_refines_def, spec_relaxed_def, meta_box_def] >>
      intLib.ARITH_TAC) >>
  (* spec_relaxed ≠ meta_box : they disagree at a = 5 *)
  simp[FUN_EQ_THM] >> qexists_tac ‘5’ >>
  rw[spec_relaxed_def, meta_box_def]
QED

(* Hence PROPOSAL A passes the admission gate. *)
Theorem relaxed_is_admissible:
  spec_admissible meta_box spec_relaxed
Proof
  rw[spec_admissible_def, relaxed_refines_meta, relaxed_is_genuine_change]
QED

(* ... and the gate actually INSTALLS it (real authority granted). *)
Theorem relaxed_is_installed:
  spec_admit meta_box spec_tight spec_relaxed = spec_relaxed
Proof
  rw[spec_admit_def, relaxed_is_admissible]
QED

(* PROPOSAL B does NOT refine the meta floor: state 9 escapes meta_box. *)
Theorem overreach_does_not_refine:
  ¬ spec_refines spec_overreach meta_box
Proof
  rw[spec_refines_def, spec_overreach_def, meta_box_def] >>
  qexists_tac ‘9’ >> intLib.ARITH_TAC
QED

(* Hence PROPOSAL B is NOT admissible ... *)
Theorem overreach_not_admissible:
  ¬ spec_admissible meta_box spec_overreach
Proof
  rw[spec_admissible_def] >> metis_tac[overreach_does_not_refine]
QED

(* ... so the gate REJECTS it and keeps the previously-in-force spec.
   The adversarial over-reach is inert; the meta floor is untouched. *)
Theorem overreach_is_rejected:
  spec_admit meta_box spec_relaxed spec_overreach = spec_relaxed
Proof
  metis_tac[unrefining_spec_proposal_is_inert, overreach_not_admissible]
QED

(* The end-to-end adversarial episode, COMPUTED:
   start tight, propose [relaxed ; overreach].
   Result: relaxed admitted, overreach rejected → final spec = spec_relaxed,
   which provably still refines the immovable meta floor. *)
Theorem episode_final_spec:
  spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]
    = spec_relaxed
Proof
  rw[spec_admit_all_def] >>
  ‘spec_admit meta_box spec_tight spec_relaxed = spec_relaxed’
    by rw[relaxed_is_installed] >>
  ‘spec_admit meta_box spec_relaxed spec_overreach = spec_relaxed’
    by rw[overreach_is_rejected] >>
  rw[]
QED

(* And the META FLOOR HOLDS after the whole adversarial episode: every
   state the finally-negotiated spec admits is still within the immovable
   meta_box. This is `meta_floor_is_never_negotiated` made concrete. *)
Theorem episode_meta_floor_intact:
  ∀a. (spec_admit_all meta_box spec_tight
          [spec_relaxed; spec_overreach]) a ⇒ meta_box a
Proof
  rpt strip_tac >>
  ‘spec_refines spec_tight meta_box’ by rw[tight_refines_meta] >>
  metis_tac[meta_floor_is_never_negotiated]
QED

(* Concrete sanity, by pure computation: state 4 is admitted by the final
   negotiated spec and is meta-safe; state 7 is meta-UNSAFE and the
   negotiated spec correctly never admits it (the inhabitant could not
   negotiate its way to 7). *)
Theorem episode_pointwise_check:
  (spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]) 4 ∧
  meta_box 4 ∧
  ¬ (spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]) 7 ∧
  ¬ meta_box 7
Proof
  rw[episode_final_spec, spec_relaxed_def, meta_box_def] >>
  intLib.ARITH_TAC
QED

val _ = export_theory ();
