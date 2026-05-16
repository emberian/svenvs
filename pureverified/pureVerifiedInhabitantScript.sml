(*
  ==================================================================
  PureCake as the svenvs inhabitant's REAL verified language.
  ==================================================================

  This SUPERSEDES `pure/pureInhabitantScript.sml` (#18), which entered
  PureLang as an *axiomatised abstract signature* (a `new_type pureprog`
  + `new_constant denote` + `new_constant safe_program`) and therefore
  only exercised the integration *point*, with NO link to the real
  verified PureCake compiler.

  Here the inhabitant program is a *real PureCake source string* `s`
  (exactly what the verified compiler `pure_compiler$compile` /
  `pure_compiler$compile_to_ast` consumes), its denotation is the REAL
  `pure_semantics$itree_of` interaction tree of the real `pure_cexp`
  the verified front-end produces, and the bridge to "the program that
  actually runs on the machine" is the REAL, machine-checked,
  oracle-free PureCake theorem

      pure_compilerProof$compiler_correctness
        compile_to_ast c s = SOME cake ⇒
          ∃pure_ce ns.
            string_to_cexp s = SOME (pure_ce,ns) ∧
            pure_semantics$safe_itree (itree_of (exp_of pure_ce)) ∧
            state_to_cakeProof$itree_rel
              (itree_of (exp_of pure_ce))
              (itree_semantics$itree_semantics cake) ∧
            itree_semantics$safe_itree
              state_to_cakeProof$ffi_convention
              (itree_semantics$itree_semantics cake)

  (found in ~/dev/pure/compiler/proofs/pure_compilerProofScript.sml;
  its per-pass backbone is `pure_to_cakeProof$pure_to_cake_correct`,
  and it is carried to the actual machine by
  `pure_end_to_endProof$end_to_end_correctness`, which closes the
  CakeML backend down to `machine_sem_itree`).

  The svenvs safety guarantee for ANY inhabitant program is then the
  GENERIC core reused verbatim — `safety$safety_preservation` and
  `upgrade$self_improvement_is_safe` instantiated at the controller
  that drives the PureCake program's interaction tree. Nothing in the
  safety core is reproved: that is the whole content of the
  opaque-controller decomposition.

  Cheat-free: no `cheat`, no `new_axiom`, no `mk_thm`, no oracle. The
  one place this file talks about the *world coupling* of an itree to
  an svenvs selector (`agent_of`) is a *plain total HOL function*
  (defined below, no axiom), and every theorem about safety quantifies
  over ALL controllers, so it holds for `agent_of` of EITHER the source
  itree OR the verified-compiled CakeML itree — `compiler_correctness`
  is precisely what certifies those two itrees are `itree_rel`-related,
  i.e. that "the program we proved safe is the program that runs".

  See CLAIMS.md in this directory for the honest proven/assumed split.
*)
open HolKernel boolLib bossLib BasicProvers;

(* svenvs generic core (reached via INCLUDES = ..) *)
open systemTheory envelopeTheory safetyTheory
     sv_weakeningTheory upgradeTheory;

(* REAL PureCake (reached via INCLUDES onto a built ~/dev/pure):
     pure_semantics  : itree_of, safe_itree, the interaction tree
     pure_cexp       : cexp, exp_of, cexp_wf, NestedCase_free
     pure_exp        : exp, closed, letrecs_distinct
     pure_compiler   : compile, compile_to_ast, string_to_cexp
     state_to_cakeProof : itree_rel, ffi_convention
     pure_compilerProof : compiler_correctness          (the bridge)
     pure_to_cakeProof  : pure_to_cake_correct          (per-pass backbone)
     pure_end_to_endProof : end_to_end_correctness       (down to the machine)
*)
open pure_semanticsTheory pure_cexpTheory pure_expTheory
     pure_compilerTheory state_to_cakeProofTheory
     pure_compilerProofTheory pure_to_cakeProofTheory
     pure_end_to_endProofTheory;

val _ = new_theory "pureVerifiedInhabitant";

(* ------------------------------------------------------------------ *)
(*  1. The inhabitant program is a REAL PureCake source program.       *)
(* ------------------------------------------------------------------ *)

(* A PureCake program is just the concrete source `s : string` the
   *verified* compiler consumes. We do not invent a language; this is
   exactly the input type of `pure_compiler$compile`. *)
Type pureprog = “:string”;

(* `runnable c s` : the verified front-end accepts `s` under config
   `c`, i.e. it really compiles to a CakeML AST. This is *exactly* the
   hypothesis of `pure_compilerProof$compiler_correctness` — we take on
   no side-condition the real theorem does not already discharge for
   us (it internally re-derives cexp_wf / closed / NestedCase_free /
   safe_itree / namespace_ok from `compile_to_ast c s = SOME cake`). *)
Definition runnable_def:
  runnable c (s:pureprog) ⇔ ∃cake. compile_to_ast c s = SOME cake
End

(* ------------------------------------------------------------------ *)
(*  2. World coupling: an interaction tree -> an svenvs selector.      *)
(*                                                                     *)
(*  svenvs is parametric over opaque world state 's and action 'a.     *)
(*  The Place fixes a deterministic protocol: at world state `s`, the  *)
(*  inhabitant is handed an encoding and must emit an action. A        *)
(*  PureCake program's observable behaviour is its `pure_semantics`    *)
(*  interaction tree (`itree_of (exp_of pure_ce)`), an itree of `Vis`  *)
(*  FFI actions resumed by environment responses. `agent_of` reads     *)
(*  that itree under the world coupling. It is a PLAIN TOTAL FUNCTION  *)
(*  (NOT an axiom): a diverging / erroring / silent program defaults   *)
(*  to a fixed `null_act`, which the policy/shield still gates.        *)
(*                                                                     *)
(*  We keep the *decoder* `read` abstract as an ordinary HOL function  *)
(*  parameter (NOT a new_constant): exactly which FFI byte string maps *)
(*  to which svenvs action is Place protocol, not svenvs-core content. *)
(*  Crucially every safety theorem below quantifies over ALL           *)
(*  controllers, so it holds for `agent_of read t` for ANY `read` and  *)
(*  ANY itree `t` — in particular the source itree AND, by             *)
(*  `compiler_correctness`'s `itree_rel`, the verified CakeML itree.   *)
(* ------------------------------------------------------------------ *)

(* The svenvs selector denoted by an interaction tree `t` under decoder
   `read : (α itree) -> 's -> 'a`. We do not need to case-split on the
   itree shape for the safety argument (the envelope never inspects the
   controller), so `agent_of` is simply the decoder applied to the
   program's itree — total because `read` is total. This is the precise
   slot where DESIGN.md §3's full reactive world-coupling
   (`enc`/`dec`/`first_act`, threading the (state,cont) resumption of
   `pure_semantics$interp` across ticks) is instantiated; doing so
   changes NO theorem in this file, because safety is controller-
   agnostic. *)
Definition agent_of_def:
  agent_of (read : 'itree -> 's -> 'a) (t:'itree) : 's -> 'a =
    read t
End

(* The svenvs controller of a runnable PureCake program: drive the
   interaction tree of the real cexp the *verified* front-end produces. *)
Definition pure_controller_def:
  pure_controller read c (s:pureprog) : 's -> 'a =
    agent_of read
      (itree_of (exp_of (FST (THE (string_to_cexp s)))))
End

(* ------------------------------------------------------------------ *)
(*  3. The verified-compilation bridge, stated for OUR programs.       *)
(*                                                                     *)
(*  This is `pure_compilerProof$compiler_correctness` specialised to   *)
(*  the runnable inhabitant programs. It is the REAL theorem, cited    *)
(*  (re-derived by `irule`), NOT re-proved and NOT assumed: for every  *)
(*  runnable program the verified compiler emits CakeML whose          *)
(*  itree_semantics is `itree_rel` to the *source* `pure_semantics`    *)
(*  itree and stays `safe_itree`. So the observable behaviour the      *)
(*  svenvs safety argument reasons about (the source itree) is, up to  *)
(*  the verified `itree_rel`, exactly the behaviour the trusted CakeML *)
(*  runtime (the same machine Candle runs on) actually exhibits.       *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_compilation_faithful:
  runnable c s ⇒
  ∃pure_ce ns cake.
    string_to_cexp s = SOME (pure_ce,ns) ∧
    compile_to_ast c s = SOME cake ∧
    pure_semantics$safe_itree (itree_of (exp_of pure_ce)) ∧
    state_to_cakeProof$itree_rel
      (itree_of (exp_of pure_ce))
      (itree_semantics$itree_semantics cake) ∧
    itree_semantics$safe_itree
      state_to_cakeProof$ffi_convention
      (itree_semantics$itree_semantics cake)
Proof
  rw[runnable_def] >>
  drule pure_compilerProofTheory.compiler_correctness >>
  strip_tac >>
  rpt $ goal_assum $ drule_at Any >> simp[]
QED

(* The denotation `pure_controller` is taken at exactly the cexp
   `compiler_correctness` certifies (`pure_ce = FST (THE (string_to_cexp
   s))`), so the itree the svenvs safety theorem reasons about IS the
   itree the verified compiler preserves. *)
Theorem pure_controller_is_certified_itree:
  runnable c s ⇒
  ∃pure_ce ns cake.
    string_to_cexp s = SOME (pure_ce,ns) ∧
    compile_to_ast c s = SOME cake ∧
    pure_controller read c s = agent_of read (itree_of (exp_of pure_ce)) ∧
    state_to_cakeProof$itree_rel
      (itree_of (exp_of pure_ce))
      (itree_semantics$itree_semantics cake)
Proof
  rw[] >>
  drule pure_inhabitant_compilation_faithful >> strip_tac >>
  rpt $ goal_assum $ drule_at Any >>
  simp[pure_controller_def]
QED

(* ------------------------------------------------------------------ *)
(*  4. HEADLINE: every PureCake inhabitant program is enveloped-safe,  *)
(*     end-to-end, with the verified compiler as the bridge.           *)
(*                                                                     *)
(*  Proven content:                                                    *)
(*   (a) safety:  the GENERIC `safety$safety_preservation`             *)
(*       instantiated at ctrl := pure_controller read c s — reused     *)
(*       verbatim, nothing reproved, holds for EVERY program;          *)
(*   (b) faithfulness: the REAL `compiler_correctness` guarantees the  *)
(*       compiled CakeML's itree is `itree_rel` to the very source     *)
(*       itree the safety argument is about, and stays `safe_itree`.   *)
(*  Together: the enveloped Place stays `safe` for any inhabitant      *)
(*  program, AND that guarantee is about the program the verified      *)
(*  PureCake -> CakeML toolchain actually runs.                        *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_verified_safe:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ∧
  runnable c s ⇒
    (* (a) the enveloped Place is safe for this PureCake inhabitant *)
    invariant step init
      (enveloped pol shield (pure_controller read c s)) safe ∧
    (* (b) and that inhabitant's observable behaviour is the verified
           compiler's: same itree (state_to_cakeProof$itree_rel),
           still safe_itree on the CakeML side. *)
    ∃pure_ce ns cake.
      string_to_cexp s = SOME (pure_ce,ns) ∧
      compile_to_ast c s = SOME cake ∧
      pure_controller read c s = agent_of read (itree_of (exp_of pure_ce)) ∧
      pure_semantics$safe_itree (itree_of (exp_of pure_ce)) ∧
      state_to_cakeProof$itree_rel
        (itree_of (exp_of pure_ce))
        (itree_semantics$itree_semantics cake) ∧
      itree_semantics$safe_itree
        state_to_cakeProof$ffi_convention
        (itree_semantics$itree_semantics cake)
Proof
  rpt strip_tac
  >- (* (a) safety: reuse the generic core, NOT reproved *)
   (irule safety_preservation >> metis_tac[])
  >- (* (b) faithfulness: the REAL PureCake compiler-correctness *)
   (drule pure_controller_is_certified_itree >>
    disch_then (qspec_then ‘read’ strip_assume_tac) >>
    drule pure_inhabitant_compilation_faithful >> strip_tac >>
    rpt $ goal_assum $ drule_at Any >> simp[])
QED

(* Spelled-out corollary: every reachable state of the Place inhabited
   by ANY verified PureCake program is safe. *)
Theorem pure_inhabitant_states_verified_safe:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ∧
  runnable c s ∧
  reach step init (enveloped pol shield (pure_controller read c s)) st ⇒
  safe st
Proof
  rpt strip_tac >>
  ‘invariant step init
     (enveloped pol shield (pure_controller read c s)) safe’
    by metis_tac[pure_inhabitant_verified_safe] >>
  metis_tac[invariant_def]
QED

(* ------------------------------------------------------------------ *)
(*  5. Verified-PureCake inhabitant under self-improvement.            *)
(*                                                                     *)
(*  A PureCake inhabitant that proposes an UNBOUNDED stream of         *)
(*  self-improvements to its own policy can never make the Place       *)
(*  unsafe: reuse `upgrade$self_improvement_is_safe` verbatim at the   *)
(*  PureCake controller, and faithfulness still holds (same proof).    *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_self_improvement_verified_safe:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ∧
  runnable c s ⇒
  ∀proposals.
    invariant step init
      (enveloped (admit_all step safe p0 proposals) shield
                 (pure_controller read c s)) safe ∧
    ∃pure_ce ns cake.
      string_to_cexp s = SOME (pure_ce,ns) ∧
      compile_to_ast c s = SOME cake ∧
      state_to_cakeProof$itree_rel
        (itree_of (exp_of pure_ce))
        (itree_semantics$itree_semantics cake) ∧
      itree_semantics$safe_itree
        state_to_cakeProof$ffi_convention
        (itree_semantics$itree_semantics cake)
Proof
  rpt strip_tac
  >- (irule self_improvement_is_safe >> metis_tac[])
  >- (drule pure_inhabitant_compilation_faithful >> strip_tac >>
      rpt $ goal_assum $ drule_at Any >> simp[])
QED

(* ------------------------------------------------------------------ *)
(*  6. End-to-end onto the actual machine.                             *)
(*                                                                     *)
(*  Citing `pure_end_to_endProof$end_to_end_correctness`, the verified *)
(*  CakeML backend carries the source itree all the way to the         *)
(*  machine's observable behaviour `machine_sem_itree`. Stating it for *)
(*  our inhabitant programs makes explicit that the safety guarantee   *)
(*  is about the behaviour of the *binary the machine executes*, not a *)
(*  source-level idealisation. (Pure citation/specialisation of the    *)
(*  real theorem; same hypotheses as `end_to_end_correctness`:         *)
(*  configs ok + code in memory.)                                      *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_runs_on_machine:
  runnable c s ∧
  backend$compile conf cake = SOME code ∧
  compile_to_ast c s = SOME cake ∧
  (λconf (mc,ms).
     backend_config_ok conf ∧ mc_conf_ok mc ∧ mc_init_ok conf mc) conf m ∧
  (λconf (bytes,bitmaps,c').
     λ(mc,ms).
       ∃cbspace data_sp.
         installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
           (backendProof$heap_regs conf.stack_conf.reg_names)
           mc c'.lab_conf.shmem_extra ms) code m ⇒
  ∃ce ns.
    string_to_cexp s = SOME (ce,ns) ∧
    (∃ct.
       state_to_cakeProof$itree_rel
         (pure_semantics$itree_of (exp_of ce)) ct ∧
       prune state_to_cakeProof$ffi_convention F ct (machine_sem_itree m))
Proof
  rpt strip_tac >>
  drule pure_end_to_endProofTheory.end_to_end_correctness >>
  rpt (disch_then drule) >> strip_tac >>
  rpt $ goal_assum $ drule_at Any >> simp[]
QED

val _ = export_theory ();
