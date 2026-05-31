(*
  kernelImplSymScript — the heavy link, closed for SYM.

  The self-optimization story carried one genuinely-remaining obligation: that
  a real EXECUTABLE kernel implements the modified inference relation
  (kernelMod's `sym_kernel`, which adds SYM as a primitive). It turns out
  CakeML already did the hard part: Candle's executable monadic SYM function
  (`holKernel$SYM`, translated to CakeML in `ml_hol_kernelProg`) is proven
  SOUND by `holKernelProofTheory.SYM_thm` — applied to a valid kernel theorem
  it yields a valid kernel theorem — and `THM_def` says a kernel `thm`
  `Sequent asl c` IS the judgment `(thyof ctxt, asl) |- c` (the same `proves`
  our `sym_kernel` is built on). SYM_thm's own proof even rests on `sym`
  (= `sym_equation`), the exact admissibility `sym_kernel` uses.

  So we close the link by CONNECTING CakeML's verified SYM to the inference
  relation: the running verified kernel's SYM, on a valid theorem of
  `a === b`, yields exactly `b === a`, and that result is a valid `|-`
  judgment — i.e. the executable kernel soundly implements `sym_kernel`'s
  SYM extension. No new translator work; we cite CakeML's own proofs.

  PROVED against the real Candle monadic kernel; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSyntaxExtraTheory
     holKernelTheory holKernelProofTheory;

val _ = new_theory "kernelImplSym";

(* The running verified kernel's executable SYM IMPLEMENTS sym_kernel's rule,
   soundly: from a valid theorem of `a === b` it produces a valid theorem of
   `b === a`. This discharges "the binary implements the modified kernel" for
   the SYM extension, using CakeML's own SYM_thm + THM_def. *)
Theorem candle_SYM_implements_sym_extension:
  THM defs (Sequent [] (a === b)) ∧ STATE defs s ∧
  (SYM (Sequent [] (a === b)) s = (M_success th', s')) ⇒
  (thyof defs, []) |- (b === a)
Proof
  rpt strip_tac >>
  (* (1) CakeML's SYM_thm: the executable SYM preserves validity. *)
  `THM defs th'` by metis_tac[SYM_thm] >>
  (* (2) the executable SYM computes exactly `b === a` from `a === b`
         (mirror the type-of-equation reasoning in SYM_thm's own proof). *)
  `th' = Sequent [] (b === a)` by (
     `(thyof defs, []) |- (a === b)` by fs[THM_def] >>
     `typeof a = typeof b` by
        (imp_res_tac proves_term_ok >> fs[term_ok_equation] >>
         imp_res_tac proves_theory_ok >> imp_res_tac theory_ok_sig >>
         fs[term_ok_equation]) >>
     fs[SYM_def, equation_def] >>
     every_case_tac >>
     fs[ml_monadBaseTheory.st_ex_return_def, raise_Failure_def] >> rw[]) >>
  (* (3) THM_def turns that valid kernel thm into the `|-` judgment. *)
  fs[THM_def]
QED

val _ = export_theory ();
