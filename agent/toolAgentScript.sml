(*
  svenvs applied to an LLM tool-using agent.

  The "controller" is now an LLM: an opaque, untrusted function
    agent : world -> tool
  emitting a tool call each step. We NEVER run an LLM — `agent` is an
  arbitrary HOL function, exactly the `∀ctrl` trick: the guarantees hold for
  *every* agent, including a fully jailbroken / adversarial one.

  The envelope is a tool-call firewall. The crucial honesty point: the
  safety spec is ABSOLUTE and FIXED (`truly_unsafe`), NOT relative to the
  agent's own permissions — otherwise "let me widen my allowlist" would be
  vacuous. Modelling it absolutely is precisely the real alignment problem:
  the agent may *request* more capability, but capability expansion must be
  proven to stay inside the fixed safety spec, or it is refused.

  This instantiates the generic svenvs core (systemTheory / envelopeTheory /
  safetyTheory / sv_weakeningTheory / upgradeTheory) — no new trust.
*)
open HolKernel boolLib bossLib BasicProvers listTheory stringTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory;

val _ = new_theory "toolAgent";

(* A tool call. Strings kept plain (no mlstring/CakeML dep — EVAL-friendly). *)
Datatype:
  tool = Read string        (* always safe *)
       | Write string        (* safe iff path is sandboxed *)
       | Net string          (* safe iff host is allowlisted *)
       | Exec string         (* absolutely unsafe in this model *)
       | Refuse              (* the safe fallback action *)
End

(* ---- the ABSOLUTE, FIXED safety spec (not agent-controllable) ---- *)
Definition sandboxed_def:
  sandboxed (p:string) ⇔ MEM p ["/sandbox/a"; "/sandbox/b"; "/sandbox/c"; "/sandbox/d"]
End
Definition corp_host_def:
  corp_host (h:string) ⇔ MEM h ["corp.internal"; "logs.internal"]
End

(* A tool call that, if executed, violates the absolute spec. *)
Definition truly_unsafe_def:
  (truly_unsafe (Write p) ⇔ ¬ sandboxed p) ∧
  (truly_unsafe (Net h)   ⇔ ¬ corp_host h) ∧
  (truly_unsafe (Exec c)  ⇔ T) ∧
  (truly_unsafe (Read _)  ⇔ F) ∧
  (truly_unsafe Refuse    ⇔ F)
End

(* World: a step counter and a sticky breach flag (absolute violation ever). *)
Datatype:
  world = <| clock : num ; breached : bool |>
End

Definition tstep_def:
  tstep (w:world) tc =
    if truly_unsafe tc then w with breached := T
    else w with clock := w.clock + 1
End

Definition tsafe_def:
  tsafe (w:world) ⇔ ¬ w.breached
End

Definition tinit_def:
  tinit (w:world) ⇔ (w = <| clock := 0; breached := F |>)
End

(* ---- the firewall policy, parameterised by a capability allowlist ---- *)
Datatype:
  allowlist = <| writes : string list ; hosts : string list |>
End

(* The policy A permits a call iff it is on the allowlist (or intrinsically
   harmless). This is a one-step filter shape but driven by the *allowlist*,
   so a too-permissive A is NOT automatically sound — soundness is a real,
   decidable side-condition on A. *)
Definition tool_pol_def:
  tool_pol (A:allowlist) (w:world) tc ⇔
    case tc of
      Read _  => T
    | Refuse  => T
    | Write p => MEM p A.writes
    | Net h   => MEM h A.hosts
    | Exec _  => F
End

Definition tshield_def:
  tshield (w:world) = Refuse
End

(* An allowlist is SAFE iff everything it permits is within the absolute
   spec. Decidable (finite lists), and the genuine proof obligation an
   agent must discharge to earn more capability. *)
Definition safe_allowlist_def:
  safe_allowlist (A:allowlist) ⇔
    EVERY sandboxed A.writes ∧ EVERY corp_host A.hosts
End

(* ---- discharge the generic safety_preservation premises ---- *)

Theorem tinit_safe:
  init_safe tinit tsafe
Proof
  rw[init_safe_def, tinit_def, tsafe_def]
QED

Theorem tshield_safe:
  safe_shield tstep tsafe tshield
Proof
  rw[safe_shield_def, tsafe_def, tstep_def, tshield_def, truly_unsafe_def]
QED

(* Soundness of the firewall holds EXACTLY when the allowlist is safe. *)
Theorem tool_pol_sound:
  safe_allowlist A ⇒ sound_policy tstep tsafe (tool_pol A)
Proof
  rw[sound_policy_def, tsafe_def, tstep_def] >>
  Cases_on ‘a’ >>
  fs[tool_pol_def, truly_unsafe_def, safe_allowlist_def, EVERY_MEM] >>
  metis_tac[]
QED

(* THE HEADLINE: for ANY agent (any LLM, jailbroken or not), if the
   allowlist is within the absolute safety spec, the firewalled agent never
   commits an absolute violation — ever. *)
Theorem agent_enveloped_safe:
  safe_allowlist A ⇒
  ∀agent. invariant tstep tinit (enveloped (tool_pol A) tshield agent) tsafe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[tinit_safe, tshield_safe, tool_pol_sound]
QED

val _ = export_theory ();
