(*
  Running the LLM tool-agent — and running its proof-carrying capability
  self-expansion loop.

  (a) A jailbroken/greedy "LLM" is *executed in-logic* via EVAL for many
      steps: bare it breaches immediately; firewalled it is provably
      contained — computed, not just asserted.

  (b) `admissible` (generic) quantifies over all states/actions, so it is
      not directly executable. We give a DECIDABLE checker `admissible_dec`
      for the allowlist family, prove it *implies* the generic `admissible`,
      and then the whole self-improvement episode — agent requests more
      capability, gate accepts the safe request and refuses the sandbox
      escape — literally RUNS under EVAL, with a theorem that any admitted
      sequence keeps the absolute safety guarantee for every agent.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory
     toolAgentTheory;

val _ = new_theory "toolAgentRun";

(* ---------- (a) execute adversarial "LLMs" in-logic ---------- *)

Definition evil_agent_def:
  evil_agent (w:world) = Exec "rm -rf /"
End

Definition greedy_agent_def:
  greedy_agent (w:world) = Write "/etc/passwd"
End

Definition w0_def:
  w0 = <| clock := 0; breached := F |>
End

Definition drive_def:
  drive A agent w = tstep w (enveloped (tool_pol A) tshield agent w)
End
Definition arun_def:
  arun A agent n = FUNPOW (drive A agent) n w0
End
Definition atrace_def:
  atrace A agent n = GENLIST (arun A agent) (n + 1)
End

Definition base_A_def:
  base_A = <| writes := ["/sandbox/a"]; hosts := ["corp.internal"] |>
End

(* Bare jailbroken agent breaches on the first tool call. *)
Theorem evil_bare_breaches:
  (FUNPOW (λw. tstep w (evil_agent w)) 1 w0).breached
Proof
  EVAL_TAC
QED

(* Firewalled, the SAME jailbroken agent is contained for 50 steps —
   executed in the logic. *)
Theorem evil_enveloped_runs_safe:
  EVERY tsafe (atrace base_A evil_agent 50)
Proof
  EVAL_TAC
QED

(* A sandbox-escape attempt is likewise contained. *)
Theorem greedy_enveloped_runs_safe:
  EVERY tsafe (atrace base_A greedy_agent 50)
Proof
  EVAL_TAC
QED

(* ---------- (b) decidable proof-carrying capability expansion ---------- *)

(* Decidable admission: the requested allowlist must stay within the
   ABSOLUTE spec and only ever add capability (monotone). *)
Definition admissible_dec_def:
  admissible_dec A1 A2 ⇔
    safe_allowlist A2 ∧
    EVERY (λp. MEM p A2.writes) A1.writes ∧
    EVERY (λh. MEM h A2.hosts)  A1.hosts
End

(* Monotone allowlists ⇒ the firewall genuinely weakens (more permissive). *)
Theorem allowlist_weaker:
  EVERY (λp. MEM p A2.writes) A1.writes ∧
  EVERY (λh. MEM h A2.hosts)  A1.hosts ⇒
  weaker (tool_pol A2) (tool_pol A1)
Proof
  rw[weaker_def, tool_pol_def] >>
  Cases_on ‘a’ >> fs[EVERY_MEM] >> metis_tac[]
QED

(* The decidable check soundly implies the generic admission obligation. *)
Theorem admissible_dec_sound:
  admissible_dec A1 A2 ⇒
  admissible tstep tsafe (tool_pol A1) (tool_pol A2)
Proof
  rw[admissible_dec_def, admissible_def] >>
  metis_tac[tool_pol_sound, allowlist_weaker]
QED

(* The executable gate: fold capability requests, keep the old allowlist
   when a request fails its proof obligation. *)
Definition admit_dec_def:
  admit_dec A reqs = FOLDL (λA r. if admissible_dec A r then r else A) A reqs
End

(* concrete episode: a legit expansion and a sandbox-escape attempt *)
Definition good_A_def:
  good_A = <| writes := ["/sandbox/a"; "/sandbox/b"]; hosts := ["corp.internal"] |>
End
Definition bad_A_def:
  bad_A = <| writes := ["/sandbox/a"; "/etc/passwd"]; hosts := ["corp.internal"] |>
End

(* The loop RUNS: base is safe; the escape request is refused, the legit
   capability expansion is admitted — all computed. *)
Theorem base_A_safe:
  safe_allowlist base_A
Proof
  EVAL_TAC
QED

Theorem episode_runs:
  admit_dec base_A [bad_A; good_A] = good_A
Proof
  EVAL_TAC
QED

(* Any admitted sequence keeps the absolute safety invariant for EVERY
   agent: a decidable gate over capability self-expansion that provably
   never lets any LLM escape the spec. *)
Theorem admit_dec_keeps_safe_allowlist:
  ∀reqs A. safe_allowlist A ⇒ safe_allowlist (admit_dec A reqs)
Proof
  Induct >> rw[admit_dec_def] >>
  fs[GSYM admit_dec_def] >> first_x_assum irule >>
  rw[] >> fs[admissible_dec_def]
QED

Theorem agent_self_improvement_safe:
  safe_allowlist A ⇒
  ∀reqs agent.
    invariant tstep tinit
      (enveloped (tool_pol (admit_dec A reqs)) tshield agent) tsafe
Proof
  rpt strip_tac >>
  ‘safe_allowlist (admit_dec A reqs)’ by metis_tac[admit_dec_keeps_safe_allowlist] >>
  metis_tac[agent_enveloped_safe]
QED

(* and concretely, post-episode, the jailbroken LLM is still contained *)
Theorem post_episode_evil_safe:
  invariant tstep tinit
    (enveloped (tool_pol (admit_dec base_A [bad_A; good_A])) tshield evil_agent)
    tsafe
Proof
  irule agent_self_improvement_safe >> EVAL_TAC
QED

val _ = export_theory ();
