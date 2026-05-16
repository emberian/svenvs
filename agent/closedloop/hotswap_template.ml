(* ===================================================================== *)
(*  RUNTIME POLICY HOT-SWAP — OBLIGATION TEMPLATE                           *)
(*                                                                         *)
(*  The unconstrained inhabitant proposes a NEW allowlist at runtime. Before    *)
(*  the verified envelope is permitted to swap to it, the LIVE Candle       *)
(*  kernel must certify the swap is safe. This file mirrors the HOL4        *)
(*  self-improvement core into the num-only Candle dialect:                 *)
(*                                                                          *)
(*    sv_weakeningScript.sml : weaker / safe_weakening                      *)
(*    upgradeScript.sml      : admissible / admit_keeps_sound               *)
(*    toolAgentScript.sml    : safe_allowlist / tool_pol  (already loaded   *)
(*                             by obligation_template.ml — REUSED here)     *)
(*                                                                          *)
(*  Allowlists are given as two membership predicates over num codes:       *)
(*     in_writes : num->bool   in_hosts : num->bool                         *)
(*  (codes: /sandbox/a..d = 1..4 ; corp/logs = 11/12 ; non-allowlisted      *)
(*   path/host = a fresh code >=50, provably outside any sane allowlist).   *)
(*                                                                          *)
(*  Load order on persvati (hol.ml + obligation_template.ml already in):    *)
(*    #use "hotswap_template.ml";;     (* once per server lifetime *)       *)
(*  then per proposal the driver sends a tiny prove(...) + sentinel block.  *)
(* ===================================================================== *)

(* ---- weaker, mirrored from sv_weakeningScript.sml:weaker_def -----------
   For the allowlist family a policy weakening is exactly: every code the
   OLD allowlist permits is still permitted by the NEW one (pointwise the
   firewall becomes >= as permissive — authority is monotone).             *)
let pol_weaker = new_definition
  `pol_weaker (nw:num->bool) (nh:num->bool) (ow:num->bool) (oh:num->bool) <=>
     (!p. ow p ==> nw p) /\ (!h. oh h ==> nh h)`;;

(* ---- the runtime hot-swap obligation -----------------------------------
   Mirror of upgradeScript.sml:admissible_def for this family:
     admissible  <=>  sound_policy step safe newp  /\  weaker newp oldp
   Here `sound_policy (tool_pol NEW)` holds EXACTLY when `safe_allowlist
   NEW` holds (toolAgentScript.sml:tool_pol_sound — re-derived live as
   ADMIT_SOUND in obligation_template.ml). So the decidable obligation a
   proposed allowlist must discharge before the envelope may swap is:       *)
let swap_ok = new_definition
  `swap_ok (nw:num->bool) (nh:num->bool) (ow:num->bool) (oh:num->bool) <=>
     safe_allowlist nw nh /\ pol_weaker nw nh ow oh`;;

(* ---- soundness link, certified ONCE so a runtime swap MEANS something:
   if the kernel proves swap_ok for the proposed allowlist then (a) the new
   firewall is still within the ABSOLUTE spec and (b) the controller's
   authority only grew. This is the HOL-Light re-derivation of
   sv_weakeningScript.sml:safe_weakening + authority_monotone, specialised
   to the allowlist family. Candle proves it now, before any swap.          *)
let SWAP_SOUND = prove
 (`!nw nh ow oh.
     swap_ok nw nh ow oh
     ==> safe_allowlist nw nh /\ pol_weaker nw nh ow oh`,
  REWRITE_TAC[swap_ok] THEN MESON_TAC[]);;

(* A swap that keeps safe_allowlist keeps every admitted action in-spec:
   re-derivation of ADMIT_SOUND lifted through the swap. *)
let SWAP_KEEPS_SPEC = prove
 (`!nw nh ow oh kind arg.
     swap_ok nw nh ow oh /\ admit_ok nw nh kind arg
     ==> ~truly_unsafe kind arg`,
  REWRITE_TAC[swap_ok] THEN MESON_TAC[ADMIT_SOUND]);;

(* The template is loaded. Each runtime proposal is a tiny `prove`:
     let SW_<id> = prove(`swap_ok NW NH OW OH`, REWRITE/ARITH/MESON);;
   echoed by the REPL as `val SW_<id> = |- swap_ok ... : thm` — the kernel
   witness that the envelope is now ALLOWED to hot-swap. If the proposal is
   unsafe the prove fails (no theorem) and the OLD policy stays. *)
