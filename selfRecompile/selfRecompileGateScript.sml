(*
  selfRecompileGateScript — the BRIDGE between the running loop and the proved
  spine.

  `candle/self_recompile.ml` RUNS, on the real `cake` binary, a proof-gated
  recompile -> swap -> resume loop: a compute routine behind a ref indirection
  is replaced, at runtime, by a freshly-compiled version (compiled to native by
  the in-binary CakeML compiler, installed via the verified `do_install`), but
  ONLY after the live Candle kernel certifies `|- !x. new x = spec x`. Swaps
  accumulate (path-dependent); an uncertifiable swap is rejected.

  Here the loop is modelled OPERATIONALLY, as the run executes it: the loop
  holds the running version f; offered a candidate g with a kernel verdict
  `cert` (the live kernel echoed |- !x. g x = spec x, or failed), it installs g
  iff cert (`swap`), folded over the stream of offers (`run_loop`). The loop
  itself never sees the spec. We show:
    * its safety is an INSTANCE of the proved genealogy
      (`genealogyTheory.genealogy_sound`): the loop step is `vouch_sound` for
      "implementation agrees with the spec", and the loop's successive
      versions form a forward-certified genealogy — so every version the loop
      ever runs is correct, for ANY path, PROVIDED the certificates are sound;
    * the reject branch keeps the running version (bad_gate_ok = false ⇒
      out_after_bad unchanged);
    * the premise is necessary: one unsound certificate installs a wrong
      version (`unsound_certificate_breaks_loop`) — the loop rests on the
      kernel's soundness, nothing else;
    * the concrete run of candle/self_recompile.ml (v0 → v1 → v2, bad
      rejected, output 5050 throughout) is an instance (`candle_run_modelled`).

  The install side (no running code is lost across a swap) is the separately-
  proved `loader/installLoaderScript : do_install_preserves_code`, over CakeML's
  real `closSem$do_install` — cited, not re-proved here.

  PROVED; pure light HOL4.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory listTheory
     pairTheory genealogyTheory;

val _ = new_theory "selfRecompileGate";

(* An implementation is CORRECT (w.r.t. a reference spec) iff it agrees with the
   spec on every input — the property `candle/self_recompile.ml`'s outputs witness. *)
Definition impl_correct_def:
  impl_correct (spec:'a->'b) (f:'a->'b) ⇔ ∀x. f x = spec x
End

(* ONE GATED SWAP, as the run executes it: `cert` is the kernel's verdict on
   the offered g (GATE1/GATE2 succeeded, or `bad_gate_ok = false`); the loop
   installs g iff cert, else keeps running f. *)
Definition swap_def:
  swap (cert:bool) (f:'a->'b) (g:'a->'b) = if cert then g else f
End

(* THE LOOP: fold the gated swap over the stream of (verdict, candidate)
   offers, starting from the genesis version. *)
Definition run_loop_def:
  (run_loop (f:'a->'b) [] = f) ∧
  (run_loop f ((cert,g)::offers) = run_loop (swap cert f g) offers)
End

(* CERTIFICATE SOUNDNESS — the kernel's soundness, as the loop needs it: a
   positive verdict is only ever issued for a candidate that meets the spec.
   This is the one premise; it is carried, never hidden. *)
Definition cert_sound_def:
  cert_sound (spec:'a->'b) (offers:(bool # ('a->'b)) list) ⇔
    EVERY (λ(cert,g). cert ⇒ impl_correct spec g) offers
End

(* The loop step as a vouching relation between running versions: f vouches
   for its successor if the successor is the result of a gated swap whose
   verdict was sound. *)
Definition loop_step_def:
  loop_step (spec:'a->'b) (f:'a->'b) (f':'a->'b) ⇔
    ∃cert g. (cert ⇒ impl_correct spec g) ∧ f' = swap cert f g
End

(* The GATE is a SOUND vouching for correctness: a certified swap installs a
   correct g (by certificate soundness); a rejected one keeps the running f
   (correct by hypothesis). Both branches are used. *)
Theorem gate_is_vouch_sound:
  vouch_sound (impl_correct spec) (loop_step spec)
Proof
  rw[vouch_sound_def, loop_step_def, swap_def] >> rw[]
QED

Theorem run_loop_append:
  ∀f xs ys. run_loop f (xs ++ ys) = run_loop (run_loop f xs) ys
Proof
  Induct_on ‘xs’ >> simp[run_loop_def, FORALL_PROD]
QED

(* The loop's n-th running version (after the first n offers). *)
Definition loop_version_def:
  loop_version (f0:'a->'b) offers n = run_loop f0 (TAKE n offers)
End

(* The versions the loop runs form a FORWARD-CERTIFIED genealogy under the
   loop step, given sound certificates (past the end of the stream the
   version is unchanged: the identity step, a rejected swap). *)
Theorem loop_is_a_genealogy:
  cert_sound spec offers ⇒
  forward_certified (loop_step spec) (loop_version f0 offers)
Proof
  rw[forward_certified_def, loop_version_def, loop_step_def,
     cert_sound_def, EVERY_EL] >>
  Cases_on ‘n < LENGTH offers’
  >- (qexistsl_tac [‘FST (EL n offers)’, ‘SND (EL n offers)’] >>
      first_x_assum drule >> Cases_on ‘EL n offers’ >> simp[] >>
      strip_tac >>
      ‘TAKE (SUC n) offers = TAKE n offers ++ [EL n offers]’
        by simp[GSYM rich_listTheory.SNOC_EL_TAKE, SNOC_APPEND] >>
      simp[run_loop_append, run_loop_def]) >>
  qexistsl_tac [‘F’, ‘ARB’] >> simp[swap_def, TAKE_LENGTH_TOO_LONG]
QED

(* THE BRIDGE. A correct genesis + sound certificates ⇒ the version the loop
   ends on, and EVERY version it runs on the way, is correct — for any
   stream, any path. Proved through `genealogy_sound`. *)
Theorem self_recompile_loop_is_safe:
  impl_correct spec f0 ∧ cert_sound spec offers ⇒
  impl_correct spec (run_loop f0 offers) ∧
  ∀n. impl_correct spec (loop_version f0 offers n)
Proof
  strip_tac >>
  ‘∀n. impl_correct spec (loop_version f0 offers n)’
    by (irule genealogy_sound >>
        metis_tac[gate_is_vouch_sound, loop_is_a_genealogy,
                  loop_version_def, TAKE_0, run_loop_def]) >>
  simp[] >>
  first_x_assum (qspec_then ‘LENGTH offers’ mp_tac) >>
  simp[loop_version_def, TAKE_LENGTH_ID]
QED

(* The observable consequence the run exhibits: no accepted swap, however
   many accumulate, changes an output — every version's results are pinned
   to the spec. (out_genesis = out_after1 = out_after2 = out_after_bad.) *)
Theorem self_recompile_preserves_outputs:
  impl_correct spec f0 ∧ cert_sound spec offers ⇒
  (∀x. run_loop f0 offers x = spec x) ∧
  ∀n x. loop_version f0 offers n x = spec x
Proof
  strip_tac >> drule_all self_recompile_loop_is_safe >>
  rw[impl_correct_def]
QED

(* THE REJECT CASE, as the loop runs it: a candidate without a certificate is
   not installed — the running version is kept, so its correctness is kept.
   (bad_gate_ok = false ⇒ no swap ⇒ out_after_bad unchanged.) *)
Theorem uncertified_swap_is_not_a_step:
  ¬cert ⇒
  swap cert f g = f ∧ (impl_correct spec f ⇒ impl_correct spec (swap cert f g))
Proof
  rw[swap_def]
QED

(* NECESSITY of certificate soundness: a positive verdict for a wrong
   candidate installs a wrong version, from a correct one. The loop's safety
   rests on the kernel's soundness and on nothing the loop itself checks. *)
Theorem unsound_certificate_breaks_loop:
  ∃(spec:num -> num) f0 g.
    impl_correct spec f0 ∧ ¬impl_correct spec g ∧
    ¬impl_correct spec (swap T f0 g) ∧
    ¬impl_correct spec (run_loop f0 [(T,g)]) ∧ ¬cert_sound spec [(T,g)]
Proof
  qexistsl_tac [‘I’, ‘I’, ‘SUC’] >>
  rw[impl_correct_def, swap_def, run_loop_def, cert_sound_def] >>
  qexists_tac ‘0’ >> simp[]
QED

(* ---- the concrete run of candle/self_recompile.ml ------------------- *)
(* sum 0..n: the genesis recursion (= the HOL spec `sum_spec`), the Gauss
   closed form (SWAP 1), the re-associated form (SWAP 2), the wrong
   "optimisation" that drops the + n (BAD SWAP). *)
Definition sum_spec_def:
  (sum_spec 0 = 0) ∧ (sum_spec (SUC n) = SUC n + sum_spec n)
End

Definition sum_v1_def:
  sum_v1 n = (n * (n + 1)) DIV 2
End

Definition sum_v2_def:
  sum_v2 n = (n * n + n) DIV 2
End

Definition sum_bad_def:
  sum_bad n = (n * n) DIV 2
End

(* The run's stream of offers with the kernel's verdicts: GATE1 proved,
   GATE2 proved, the bad gate failed (`bad_gate_ok = false`). *)
Definition candle_offers_def:
  candle_offers = [(T, sum_v1); (T, sum_v2); (F, sum_bad)]
End

Theorem sum_spec_twice:
  ∀n. 2 * sum_spec n = n * (n + 1)
Proof
  Induct >> simp[sum_spec_def, MULT_CLAUSES, LEFT_ADD_DISTRIB,
                 RIGHT_ADD_DISTRIB, ADD1]
QED

(* GATE1 and GATE2, in HOL4. *)
Theorem gate1:
  impl_correct sum_spec sum_v1
Proof
  ‘∀n. n * (n + 1) = sum_spec n * 2’ by metis_tac[sum_spec_twice, MULT_COMM] >>
  simp[impl_correct_def, sum_v1_def, MULT_DIV]
QED

Theorem gate2:
  impl_correct sum_spec sum_v2
Proof
  ‘sum_v2 = sum_v1’
    by rw[FUN_EQ_THM, sum_v1_def, sum_v2_def, LEFT_ADD_DISTRIB] >>
  simp[gate1]
QED

(* The bad candidate really is wrong (so a kernel that certified it would be
   unsound — exactly why `bad_gate_ok` must be false). *)
Theorem bad_gate_is_false:
  ¬impl_correct sum_spec sum_bad
Proof
  rw[impl_correct_def] >> qexists_tac ‘1’ >> EVAL_TAC
QED

(* The run, modelled: the verdicts are sound, the loop ends on v2 (the bad
   swap refused), and every version it runs returns sum_spec — at 100, 5050,
   as `out_genesis = out_after1 = out_after2 = out_after_bad = 5050`. *)
Theorem candle_run_modelled:
  cert_sound sum_spec candle_offers ∧
  run_loop sum_spec candle_offers = sum_v2 ∧
  (∀n. impl_correct sum_spec (loop_version sum_spec candle_offers n)) ∧
  (∀n. loop_version sum_spec candle_offers n 100 = 5050)
Proof
  ‘cert_sound sum_spec candle_offers’
    by simp[cert_sound_def, candle_offers_def, gate1, gate2] >>
  ‘impl_correct sum_spec sum_spec’ by simp[impl_correct_def] >>
  drule_all self_recompile_loop_is_safe >> strip_tac >>
  rw[] >- simp[candle_offers_def, run_loop_def, swap_def] >>
  ‘sum_spec 100 = 5050’ by EVAL_TAC >>
  fs[impl_correct_def]
QED

val _ = export_theory ();
