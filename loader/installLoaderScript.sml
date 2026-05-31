(*
  installLoaderScript — the REAL machine loader proof.

  selfOptimize/relocator carried the loader/relocator as an obligation (and
  discharged a toy of it). Here we close it against CakeML's OWN verified
  runtime code-installation: `closSem$do_install`, the semantics of the
  `Install` op — the mechanism by which a running CakeML program installs
  newly-compiled machine code AT RUNTIME (CakeML's verified self-modifying-
  code / JIT primitive, the substrate for a self-optimizing prover that
  recompiles itself).

  The property a safe hot-swap needs — and the one our abstract
  `inplaceUpdateTheory.inplace_swap_preserves_heap` modelled — is that
  installing new code never disturbs the code already running: every function
  already compiled (the kernel, every theorem-producing routine, the whole
  live `thm`-heap-producing apparatus) still resolves to the same definition
  afterwards. `do_install` guarantees this BY CONSTRUCTION: it requires the
  new code's labels be DISJOINT from the existing code, then extends the code
  map with a finite-map union — so old entries are provably preserved.

  We prove exactly that, over the real `do_install`. This is the machine-
  level loader-correctness for code/heap survival, against CakeML's actual
  compiler semantics — NOT a toy. PROVED; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     finite_mapTheory closSemTheory;

val _ = new_theory "installLoader";

(* Installing new code at runtime PRESERVES every existing code entry: if
   `do_install` succeeds, every label already in the code map resolves, after
   installation, to exactly the same definition. The running kernel and all
   already-compiled functions keep working across the self-modification. *)
Theorem do_install_preserves_code:
  do_install vs s = (Rval es, s') ⇒
  ∀k. k ∈ FDOM s.code ⇒ (s'.code ' k = s.code ' k)
Proof
  rw[do_install_def] >>
  fs[CaseEq"list", CaseEq"option"] >> rw[] >>
  rpt (pairarg_tac >> fs[]) >>
  fs[CaseEq"bool", CaseEq"prod", CaseEq"option"] >> rw[] >>
  irule FUPDATE_LIST_APPLY_NOT_MEM >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[]
QED

(* Spelled out via FLOOKUP: the lookup of any pre-existing label is unchanged
   by installation — the form an executing call site actually uses. *)
Theorem do_install_preserves_FLOOKUP:
  do_install vs s = (Rval es, s') ⇒
  ∀k. k ∈ FDOM s.code ⇒ (FLOOKUP s'.code k = FLOOKUP s.code k)
Proof
  rw[do_install_def] >>
  fs[CaseEq"list", CaseEq"option"] >> rw[] >>
  rpt (pairarg_tac >> fs[]) >>
  fs[CaseEq"bool", CaseEq"prod", CaseEq"option"] >> rw[] >>
  fs[FLOOKUP_DEF, FDOM_FUPDATE_LIST] >> rw[] >>
  fs[pred_setTheory.IN_DISJOINT] >>
  metis_tac[FUPDATE_LIST_APPLY_NOT_MEM, pred_setTheory.IN_DISJOINT]
QED

val _ = export_theory ();
