(*
  symBinaryImplementsScript — strengthening the kernelImpl tie-in.

  kernelImplScript proved `candle_SYM_implements_sym_extension`: the executable
  monadic SYM, applied to a valid `a === b`, yields a result `th'` with
  `(thyof defs,[]) |- (b === a)`.  That theorem HIDES the actual output value
  `th'` (it only asserts the |- judgment).

  inplaceUpdateScript carried, as a labelled ABSTRACT premise,
    `binary_implements produces bin sym_kernel`
  i.e. a black-box `produces` relation that "the recompiled binary implements
  the modified kernel" — never discharged against a real executable.

  THIS FILE discharges that premise for the SYM rule using the ACTUAL CakeML
  executable monadic SYM, citing only CakeML's own SYM_thm/THM_def.  We:

   (1) STRENGTHEN the implements lemma to EXPOSE the computed value:
       executable SYM on a valid `a === b` returns EXACTLY `Sequent [] (b===a)`.
   (2) define the concrete `produces` relation of the running SYM-extended
       kernel: it outputs `obl` iff the base kernel proved it OR executable SYM
       turned a base-proved `a===b` into `obl = b===a`.
   (3) DISCHARGE `binary_implements <that concrete produces> sym_kernel` —
       no longer a carried premise but a theorem, against the real executable.

  `binary_implements`, `sym_kernel` are restated locally to match svenvs
  (inplaceUpdate/kernelMod) verbatim; the point is that the abstract `produces`
  of inplaceUpdate can be INSTANTIATED by the genuine CakeML monadic SYM and
  the carried premise then HOLDS as a theorem.

  Build kept LIGHT (syntax + monadic only, exactly kernelImpl's footprint): the
  discharge is a syntactic/implementation fact and does not need the semantics
  layer.  (Semantic soundness of the discharged kernel is already
  inplaceUpdate's `running_binary_sound`, now instantiable here.)

  PROVED against the real Candle monadic kernel; no `cheat`, no new_axiom.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSyntaxExtraTheory
     holKernelTheory holKernelProofTheory;

val _ = new_theory "symBinaryImplements";

(* (1) STRENGTHENED implements lemma (below): executable SYM computes EXACTLY
       `Sequent [] (b === a)` (value exposed in the conclusion), and that is a
       valid |- judgment.  Same proof skeleton as kernelImpl's
       candle_SYM_implements_sym_extension but the value equation is kept.

   Helper — fast, deterministic evaluation of the executable SYM on an equation:
   on `Sequent asl (a===b)` it computes `Sequent asl (b===a)` whenever the two
   sides are typeable to the same type — by direct rewriting, NO every_case_tac
   (the input's syntactic shape already selects SYM_def's first branch). *)
Theorem SYM_eval_equation[local]:
  (typeof a = typeof b) ==>
  (SYM (Sequent asl (a === b)) s = (M_success (Sequent asl (b === a)), s))
Proof
  strip_tac >>
  simp[SYM_def, equation_def, ml_monadBaseTheory.st_ex_return_def]
QED

Theorem candle_SYM_computes_sym_extension:
  THM defs (Sequent [] (a === b)) /\ STATE defs s /\
  (SYM (Sequent [] (a === b)) s = (M_success thr, s')) ==>
    (thr = Sequent [] (b === a)) /\ (thyof defs, []) |- (b === a)
Proof
  ntac 2 strip_tac >>
  `(thyof defs, []) |- (a === b)` by fs[THM_def] >>
  `typeof a = typeof b` by
     (imp_res_tac proves_term_ok >> fs[term_ok_equation] >>
      imp_res_tac proves_theory_ok >> imp_res_tac theory_ok_sig >>
      fs[term_ok_equation]) >>
  `SYM (Sequent [] (a === b)) s = (M_success (Sequent [] (b === a)), s)`
     by (irule SYM_eval_equation >> fs[]) >>
  `thr = Sequent [] (b === a)` by fs[] >>
  rw[] >>
  `THM defs (Sequent [] (b === a))` by metis_tac[SYM_thm] >>
  fs[THM_def]
QED

(* The svenvs predicates, restated verbatim (see inplaceUpdate / kernelMod).
   `produces bin thy obl` : the running binary `bin` outputs the obligation
   `obl` (over theory `thy`).  `sym_kernel` is the modified inference relation
   (SYM added as a primitive). *)
Definition binary_implements_def:
  binary_implements (produces:'bin->thy->term->bool) (bin:'bin)
                    (K:thy->term->bool) <=>
    !thy obl. produces bin thy obl ==> K thy obl
End

Definition sym_kernel_def:
  sym_kernel thy obl <=>
    (thy,[]) |- obl \/
    (?a b. obl = (b === a) /\ (thy,[]) |- (a === b))
End

(* (2) The CONCRETE `produces` relation realised by the running SYM-extended
       kernel, defined against the ACTUAL executable monadic SYM.  The binary
       `defs` (the kernel context) "produces" `obl` over `thyof defs` iff:
         - the base kernel already proves it as a thm (the |- disjunct), OR
         - executable SYM, run on some base-proved `a === b`, succeeds and the
           value it returns is exactly `Sequent [] obl`.
       This is the operational meaning of "the recompiled binary computes the
       modified kernel": every output is either a base thm or the genuine
       result of executing the new SYM primitive. *)
Definition sym_produces_def:
  sym_produces defs thy obl <=>
    (thy = thyof defs) /\
    ( (thy,[]) |- obl \/
      (?a b s s' thr.
         THM defs (Sequent [] (a === b)) /\ STATE defs s /\
         (SYM (Sequent [] (a === b)) s = (M_success thr, s')) /\
         thr = Sequent [] obl) )
End

(* (3) THE DISCHARGE.  The carried premise of inplaceUpdate
       (`binary_implements produces bin sym_kernel`) HOLDS for the concrete
       executable SYM: the running binary's outputs all lie in `sym_kernel`.
       Proved from the strengthened lemma + CakeML's SYM_thm/THM_def alone. *)
Theorem sym_produces_implements_sym_kernel:
  binary_implements sym_produces defs sym_kernel
Proof
  simp[binary_implements_def] >> rpt strip_tac >>
  fs[sym_produces_def]
  (* `fs` splits the sym_produces disjunction into two cases. *)
  >> rw[sym_kernel_def]
  (* In each resulting subgoal, ONE of these closes it:
       - base-proof case: hyp `(thyof defs,[]) |- obl` is the |- disjunct;
       - SYM case: candle_SYM_computes_sym_extension forces the output to be
         b===a with |- (b===a), the SYM disjunct (obl = b===a). *)
  >> TRY (metis_tac[])
  >> `Sequent [] obl = Sequent [] (b === a) /\ (thyof defs,[]) |- (b === a)`
       by metis_tac[candle_SYM_computes_sym_extension]
  >> `obl = (b === a)` by fs[]
  >> metis_tac[]
QED

val _ = export_theory ();
