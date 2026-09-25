(*
  certifierScript — the one theorem behind every svenvs gate, proved once.

  Every layer of svenvs has the same shape: a CERTIFIER answers yes/no on an
  obligation; a GATE installs the proposed successor iff it said yes; a
  JUDGE (the property worth keeping) is preserved along gated steps, over a
  single step, a finite fold of offers, or an unbounded stream. This theory
  states that shape abstractly and proves it, together with the matching
  NECESSITY results: certifier soundness is not merely sufficient for the
  gate to keep the judge, it is equivalent to it.

    sound_certifier chk sem ⇔ ∀ob. chk ob ⇒ sem ob
      chk : 'o -> bool     the certifier's verdict on obligation ob
      sem : 'o -> bool     what ob means (what a yes is supposed to certify)
    cgate yes old new = if yes then new else old
    ratchet J R        ⇔ ∀x y. J x ∧ R x y ⇒ J y
    follows R s        ⇔ ∀n. R (s n) (s (SUC n))
    cstep chk sem J    the step relation of the gate driven by chk:
                       stay put, or pass one offer (ob, y) whose meaning
                       would make y good (sem ob ⇒ J y) through cgate (chk ob)
    cgate_run chk x offers   the gate folded over a list of offers

  Main results:
    sound_certifier_iff_transfers   soundness ⇔ a yes transfers to every
                                    fact its obligation faithfully encodes
    cgate_safe                      sound certifier + faithful encoding ⇒
                                    the judge survives one gated step
    sound_certifier_iff_cgate_safe  … and conversely, given one good and one
                                    bad point of the judge
    unsound_certifier_breaches      the necessity corollary (∃-witness)
    ratchet_stream / ratchet_stream_iff   the stream theorem and its converse
    cstep_ratchet / sound_certifier_iff_cstep_ratchet
    sound_certifier_iff_stream_safe soundness ⇔ every stream of gated steps
                                    from a good genesis stays good
    cgate_run_follows               a fold of offers is a stream of csteps
    cgate_run_safe / cgate_run_safe_iff   the fold theorem and its converse

  THE INSTANCE TABLE (each layer's gate is cgate; each theorem named on the
  right is proved from the general one on the left):

   layer (theory)          chk (certifier)          sem (meaning)            J (judge)
   ----------------------  -----------------------  -----------------------  -----------------------
   upgrade: gate           I on the bool cert       I (cert ⇒ J newp given)  sound_policy step safe
     gate = cgate, gate_all = cgate_run I;
     gate_keeps_sound, gate_all_keeps_sound, gated_self_improvement_is_safe  ← cgate_keeps, cgate_fold_keeps;
     gate_all_keeps_sound_iff ← cgate_fold_safe_iff; gate_keeps_sound_iff (one step, direct)
   upgrade: any certifier  chk on 'o                sem, encoded by          sound_policy step safe
                                                    sem ob ⇒ admissible …
     certifier_gate_preserves_safety, sound_certifier_iff_policy_gate_safe  ← cgate_safe, sound_certifier_iff_cgate_safe
   upgrade: admit          admissible (oracle)      admissible               sound_policy step safe
   embeddedGate            UNCURRY (kernel_admits   kernel_meaning mem       sound_policy step safe
                            mem)                    ((thy,obl) ↦ (thy,[]) |= obl)
     kernel_admits_sound_certifier, encodes_obligation_is_encoding,
     embedded_admit_preserves_safety
   kernelUpgrade           UNCURRY K (any kernel)   kernel_meaning mem       sound_policy step safe
     kernel_sound ⇔ sound_certifier (UNCURRY K) (kernel_meaning mem):
     embeddedGate.kernel_soundness_is_sound_certifier (from sound_certifier_curried);
     kernel_sound_iff_gate_safe is embeddedGate.kernel_sound_certifier_iff_gate_safe,
     itself sound_certifier_iff_policy_gate_safe at ob := (thy,obl)
   selfProver              prover_certifier         prover_meaning           sound_policy step safe
                            (hol4_checks p B ∧ b)    (sound B ∧ b)
     frozen_checker_sound_iff_sound_certifier, prover_self_improvement_is_safe,
     frozen_checker_sound_iff_prover_gate_safe, prover_gate_all_is_cgate_run,
     prover_then_unbounded_policy_self_improvement_is_safe ← cgate_run_safe
   genealogy               λ(A,B). jsound A ∧       λ(A,B). jsound B         jsound
                            vouches A B
     vouch_sound = ratchet, forward_certified = follows,
     genealogy_sound ← ratchet_stream, vouch_sound_is_necessary ← ratchet_stream_iff
   selfRecompileGate       I on the kernel verdict  I                        impl_correct spec
     swap = cgate, run_loop = cgate_run I, loop_step = cstep I I …,
     gate_is_vouch_sound ← cstep_ratchet, loop_is_a_genealogy ← cgate_run_follows,
     self_recompile_loop_is_safe ← cgate_fold_keeps, cert_sound_iff_loop_safe ← cgate_fold_safe_iff
   apex                    (genealogy at apex_sound / apex_vouch)
     compiler_self_recompilation_stays_correct ← ratchet_stream

  Pure HOL4: list/pair/arithmetic only; no svenvs type appears here.
*)
open HolKernel boolLib bossLib BasicProvers listTheory;

val _ = new_theory "certifier";

(* ===================================================================== *)
(* 1. Certifier soundness.                                               *)
(* ===================================================================== *)

Definition sound_certifier_def:
  sound_certifier (chk:'o -> bool) (sem:'o -> bool) ⇔ ∀ob. chk ob ⇒ sem ob
End

(* Soundness is EXACTLY: the certifier's yes transfers to every fact P that
   the obligation faithfully encodes (sem ob ⇒ P). *)
Theorem sound_certifier_iff_transfers:
  sound_certifier chk sem ⇔ ∀ob P. chk ob ∧ (sem ob ⇒ P) ⇒ P
Proof
  rw[sound_certifier_def] >> eq_tac >> rpt strip_tac
  >- metis_tac[] >>
  first_x_assum (qspecl_then [‘ob’, ‘sem ob’] mp_tac) >> simp[]
QED

(* The same fact for a two-argument certifier (a kernel K : thy -> term ->
   bool with its entailment meaning), stated in the curried form lane B's
   kernel_sound takes: soundness of a curried certifier IS sound_certifier
   of its uncurrying, and IS transfer. *)
Theorem sound_certifier_curried:
  (∀a b. kchk a b ⇒ ksem a b) ⇔
  sound_certifier (UNCURRY kchk) (UNCURRY ksem)
Proof
  rw[sound_certifier_def, pairTheory.FORALL_PROD]
QED

Theorem curried_sound_iff_transfers:
  (∀a b. kchk a b ⇒ ksem a b) ⇔
  ∀a b P. kchk a b ∧ (ksem a b ⇒ P) ⇒ P
Proof
  eq_tac >> rpt strip_tac
  >- metis_tac[] >>
  first_x_assum (qspecl_then [‘a’, ‘b’, ‘ksem a b’] mp_tac) >> simp[]
QED

(* Two certifiers that are sound for free: the oracle (a certifier that
   consults the meaning itself) and the identity on a boolean verdict. *)
Theorem oracle_sound_certifier:
  sound_certifier sem sem
Proof
  rw[sound_certifier_def]
QED

Theorem identity_sound_certifier:
  sound_certifier (I:bool -> bool) I
Proof
  rw[sound_certifier_def]
QED

(* ===================================================================== *)
(* 2. The certified gate, over any space.                                *)
(* ===================================================================== *)

Definition cgate_def:
  cgate (yes:bool) (old:'x) new = if yes then new else old
End

Theorem cgate_installs:
  yes ⇒ cgate yes old new = new
Proof
  rw[cgate_def]
QED

Theorem cgate_rejects:
  ¬yes ⇒ cgate yes old new = old
Proof
  rw[cgate_def]
QED

(* The boolean core: whatever the verdict, the judge survives if a yes
   was only ever given to a good successor. *)
Theorem cgate_keeps:
  (yes ⇒ J new) ∧ J old ⇒ J (cgate yes old new)
Proof
  rw[cgate_def]
QED

(* THE GENERAL SAFETY THEOREM: a sound certifier plus a faithful encoding
   (the obligation's meaning makes the successor good) keeps the judge
   across one gated step. *)
Theorem cgate_safe:
  sound_certifier chk sem ∧ (sem ob ⇒ J new) ∧ J old ⇒
  J (cgate (chk ob) old new)
Proof
  rw[sound_certifier_def, cgate_def]
QED

(* THE GENERAL IFF. For a judge with a good point [a] and a bad point [b],
   soundness of the certifier is EQUIVALENT to the gate keeping the judge
   for every obligation and every faithfully-encoded proposal. The side
   conditions are needed: if every point is good or every point is bad the
   right-hand side holds for any certifier. *)
Theorem sound_certifier_iff_cgate_safe:
  J a ∧ ¬J b ⇒
  (sound_certifier chk sem ⇔
   ∀ob old new. J old ∧ (sem ob ⇒ J new) ⇒ J (cgate (chk ob) old new))
Proof
  strip_tac >> eq_tac
  >- metis_tac[cgate_safe] >>
  rw[sound_certifier_def] >> CCONTR_TAC >>
  first_x_assum (qspecl_then [‘ob’, ‘a’, ‘b’] mp_tac) >> simp[cgate_def]
QED

(* NECESSITY, as a corollary: an unsound certifier breaches some judge-
   keeping gated step, although the old point is good and the encoding is
   (vacuously) faithful. *)
Theorem unsound_certifier_breaches:
  ¬sound_certifier chk sem ∧ J a ∧ ¬J b ⇒
  ∃ob old new. J old ∧ (sem ob ⇒ J new) ∧ ¬J (cgate (chk ob) old new)
Proof
  metis_tac[sound_certifier_iff_cgate_safe]
QED

(* And that failure is exactly one yes without its meaning. *)
Theorem unsound_certifier_witness:
  ¬sound_certifier chk sem ⇔ ∃ob. chk ob ∧ ¬sem ob
Proof
  rw[sound_certifier_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* 3. The ratchet: a judge preserved along a relation, over streams.     *)
(* ===================================================================== *)

Definition ratchet_def:
  ratchet (J:'x -> bool) (R:'x -> 'x -> bool) ⇔ ∀x y. J x ∧ R x y ⇒ J y
End

Definition follows_def:
  follows (R:'x -> 'x -> bool) (s:num -> 'x) ⇔ ∀n. R (s n) (s (SUC n))
End

(* A ratchet is a certifier: the pair (x, y) with J x and R x y is
   certified to mean J y. *)
Theorem ratchet_is_sound_certifier:
  ratchet J R ⇔
  sound_certifier (λ(x,y). J x ∧ R x y) (λ(x,y). J y)
Proof
  rw[ratchet_def, sound_certifier_def, pairTheory.FORALL_PROD]
QED

(* THE STREAM THEOREM: a good genesis and a ratcheting relation keep the
   judge along every stream that follows the relation. *)
Theorem ratchet_stream:
  ∀J R s. ratchet J R ∧ J (s 0) ∧ follows R s ⇒ ∀n. J (s n)
Proof
  rw[ratchet_def, follows_def] >> Induct_on ‘n’ >> metis_tac[]
QED

(* ... and its converse, for a relation that always offers a successor:
   the ratchet is EXACTLY what keeps every such stream good. *)
Theorem ratchet_stream_iff:
  ∀J R. (∀x. ∃y. R x y) ⇒
        (ratchet J R ⇔ ∀s. J (s 0) ∧ follows R s ⇒ ∀n. J (s n))
Proof
  rpt strip_tac >> eq_tac
  >- metis_tac[ratchet_stream] >>
  rw[ratchet_def] >> CCONTR_TAC >>
  ‘∃f. ∀z. R z (f z)’ by (simp[GSYM SKOLEM_THM] >> metis_tac[]) >>
  qabbrev_tac ‘sq = λn. if n = 0 then x else FUNPOW f (n - 1) y’ >>
  ‘follows R sq’
    by (rw[follows_def, Abbr ‘sq’] >>
        Cases_on ‘n’ >> simp[arithmeticTheory.FUNPOW_SUC]) >>
  ‘J (sq 0) ∧ ¬J (sq 1)’ by simp[Abbr ‘sq’] >>
  metis_tac[]
QED

(* ===================================================================== *)
(* 4. The step relation a certifier induces, and its streams.            *)
(* ===================================================================== *)

(* One step of a gate driven by [chk]: stay put, or pass an offer (ob, y)
   whose meaning makes y good through cgate (chk ob). The stay-put case is
   what a rejected offer, or the end of a finite stream of offers, does. *)
Definition cstep_def:
  cstep (chk:'o -> bool) (sem:'o -> bool) (J:'x -> bool) old new ⇔
    new = old ∨ ∃ob y. (sem ob ⇒ J y) ∧ new = cgate (chk ob) old y
End

(* On boolean verdicts with the identity certifier, the stay-put case is
   the rejected offer: cstep is "some verdict, sound for its candidate". *)
Theorem cstep_bool:
  cstep I I J old new ⇔ ∃yes y. (yes ⇒ J y) ∧ new = cgate yes old y
Proof
  rw[cstep_def] >> eq_tac >> rw[]
  >- (qexistsl_tac [‘F’, ‘old’] >> simp[cgate_def])
  >> metis_tac[]
QED

Theorem cstep_ratchet:
  sound_certifier chk sem ⇒ ratchet J (cstep chk sem J)
Proof
  rw[ratchet_def, cstep_def] >> rw[] >> metis_tac[cgate_safe]
QED

Theorem sound_certifier_iff_cstep_ratchet:
  J a ∧ ¬J b ⇒
  (sound_certifier chk sem ⇔ ratchet J (cstep chk sem J))
Proof
  strip_tac >> eq_tac
  >- metis_tac[cstep_ratchet] >>
  strip_tac >> drule_all sound_certifier_iff_cgate_safe >>
  disch_then (fn th => rewrite_tac[th]) >>
  fs[ratchet_def, cstep_def] >> metis_tac[]
QED

Theorem cstep_total:
  ∀x. ∃y. cstep chk sem J x y
Proof
  rw[cstep_def] >> qexists_tac ‘x’ >> simp[]
QED

(* THE GENERAL STREAM THEOREM, both directions: a certifier is sound iff
   every stream of its gated steps from a good genesis stays good. *)
Theorem sound_certifier_iff_stream_safe:
  J a ∧ ¬J b ⇒
  (sound_certifier chk sem ⇔
   ∀s. J (s 0) ∧ follows (cstep chk sem J) s ⇒ ∀n. J (s n))
Proof
  strip_tac >>
  ‘∀x. ∃y. cstep chk sem J x y’ by rw[cstep_total] >>
  drule_all sound_certifier_iff_cstep_ratchet >>
  disch_then (fn th => rewrite_tac[th]) >>
  metis_tac[ratchet_stream_iff]
QED

(* ===================================================================== *)
(* 5. The gate folded over a finite list of offers.                      *)
(* ===================================================================== *)

Definition cgate_run_def:
  (cgate_run (chk:'o -> bool) (x:'x) [] = x) ∧
  (cgate_run chk x ((ob,y)::rest) = cgate_run chk (cgate (chk ob) x y) rest)
End

Theorem cgate_run_append:
  ∀x xs ys. cgate_run chk x (xs ++ ys) = cgate_run chk (cgate_run chk x xs) ys
Proof
  Induct_on ‘xs’ >> simp[cgate_run_def, pairTheory.FORALL_PROD]
QED

Theorem cgate_run_TAKE_SUC:
  n < LENGTH offers ⇒
  cgate_run chk x (TAKE (SUC n) offers) =
  cgate (chk (FST (EL n offers))) (cgate_run chk x (TAKE n offers))
        (SND (EL n offers))
Proof
  strip_tac >>
  ‘TAKE (SUC n) offers = TAKE n offers ++ [EL n offers]’
    by simp[GSYM rich_listTheory.SNOC_EL_TAKE, SNOC_APPEND] >>
  Cases_on ‘EL n offers’ >> simp[cgate_run_append, cgate_run_def]
QED

(* The successive versions of a fold form a stream of gated steps. So
   every fold theorem is an instance of the stream theorem. *)
Theorem cgate_run_follows:
  EVERY (λ(ob,y). sem ob ⇒ J y) offers ⇒
  follows (cstep chk sem J) (λn. cgate_run chk x (TAKE n offers))
Proof
  rw[follows_def, cstep_def, EVERY_EL] >>
  Cases_on ‘n < LENGTH offers’
  >- (disj2_tac >>
      qexistsl_tac [‘FST (EL n offers)’, ‘SND (EL n offers)’] >>
      first_x_assum drule >> Cases_on ‘EL n offers’ >>
      simp[cgate_run_TAKE_SUC]) >>
  disj1_tac >> simp[TAKE_LENGTH_TOO_LONG]
QED

(* THE FOLD THEOREM, proved through the stream theorem: every version the
   fold passes through, and the one it ends on, is good. *)
Theorem cgate_run_safe:
  ∀chk sem J offers x.
  sound_certifier chk sem ∧ EVERY (λ(ob,y). sem ob ⇒ J y) offers ∧ J x ⇒
  (∀n. J (cgate_run chk x (TAKE n offers))) ∧ J (cgate_run chk x offers)
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀n. J (cgate_run chk x (TAKE n offers))’
    by (‘ratchet J (cstep chk sem J)’ by metis_tac[cstep_ratchet] >>
        ‘follows (cstep chk sem J) (λn. cgate_run chk x (TAKE n offers))’
          by metis_tac[cgate_run_follows] >>
        qspecl_then [‘J’, ‘cstep chk sem J’,
                     ‘λn. cgate_run chk x (TAKE n offers)’]
                    mp_tac ratchet_stream >>
        simp[cgate_run_def, TAKE_0]) >>
  simp[] >>
  first_x_assum (qspec_then ‘LENGTH offers’ mp_tac) >>
  simp[TAKE_LENGTH_ID]
QED

(* The boolean-verdict form every concrete fold (gate_all, run_loop) is. *)
Theorem cgate_fold_keeps:
  EVERY (λ(yes,y). yes ⇒ J y) offers ∧ J x ⇒
  (∀n. J (cgate_run I x (TAKE n offers))) ∧ J (cgate_run I x offers)
Proof
  strip_tac >> irule cgate_run_safe >> simp[identity_sound_certifier] >>
  qexists_tac ‘I’ >> simp[identity_sound_certifier]
QED

(* The fold's converse: given a good point, a list of offers keeps every
   good genesis good at every prefix iff every yes in it went to a good
   candidate. *)
Theorem cgate_run_safe_iff:
  ∀J a chk offers. J a ⇒
  (EVERY (λ(ob,y). chk ob ⇒ J y) offers ⇔
   ∀x. J x ⇒ ∀n. J (cgate_run chk x (TAKE n offers)))
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- metis_tac[cgate_run_safe, oracle_sound_certifier] >>
  rw[EVERY_EL] >> Cases_on ‘EL n offers’ >> rw[] >>
  first_x_assum (qspec_then ‘a’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (qspec_then ‘SUC n’ mp_tac) >>
  simp[cgate_run_TAKE_SUC, cgate_def]
QED

Theorem cgate_fold_safe_iff:
  J a ⇒
  (EVERY (λ(yes,y). yes ⇒ J y) offers ⇔
   ∀x. J x ⇒ ∀n. J (cgate_run I x (TAKE n offers)))
Proof
  strip_tac >>
  qspecl_then [‘J’, ‘a’, ‘I’, ‘offers’] mp_tac cgate_run_safe_iff >>
  simp[]
QED

val _ = export_theory ();
