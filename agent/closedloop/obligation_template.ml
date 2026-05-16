(* ===================================================================== *)
(*  CLOSED-LOOP OBLIGATION TEMPLATE                                         *)
(*                                                                         *)
(*  Mirror of svenvs/agent/toolAgentScript.sml into HOL Light, in the       *)
(*  num-only dialect that Candle's ARITH_TAC discharges rock-solidly        *)
(*  (memory: NO int `>`, NO Printf, :num + ARITH_TAC).                      *)
(*                                                                         *)
(*  This file defines the firewall ONCE. The closed loop then appends a     *)
(*  single concrete goal per Gemma action (a `prove(...)`), so the verified *)
(*  Candle kernel decides admissibility of THAT action at runtime.          *)
(*                                                                         *)
(*  Load order on the persvati server (hol.ml already preloaded):           *)
(*    #use "obligation_template.ml";;     (* once per server lifetime *)    *)
(*  then per action the loop sends a small prove(...) block + sentinel.     *)
(* ===================================================================== *)

(* ---- tool calls encoded as num (1:1 with toolAgentScript.sml:26) -------
     A tool call is a pair (kind, arg):
       kind: 0=Read 1=Write 2=Net 3=Exec 4=Refuse
       arg : a num code for the path/host (see closed_loop.py CODE table).
   Using num keeps every obligation inside Candle's ARITH_TAC sweet spot. *)

(* sandboxed_def:35  — sandbox path codes are 1..4 (/sandbox/a../sandbox/d) *)
let sandboxed = new_definition
  `sandboxed (p:num) <=> (1 <= p /\ p <= 4)`;;

(* corp_host_def:38  — allowlisted host codes are 11 (corp) and 12 (logs) *)
let corp_host = new_definition
  `corp_host (h:num) <=> (h = 11 \/ h = 12)`;;

(* truly_unsafe_def:43 — the ABSOLUTE, FIXED safety spec (not agent-set).
     kind 0 Read  -> safe
     kind 1 Write -> unsafe iff path not sandboxed
     kind 2 Net   -> unsafe iff host not corp
     kind 3 Exec  -> always unsafe
     kind 4 Refuse-> safe
   anything else  -> unsafe (envelope must catch the unknown). *)
let truly_unsafe = new_definition
  `truly_unsafe (kind:num) (arg:num) <=>
     if kind = 0 then F
     else if kind = 1 then ~sandboxed arg
     else if kind = 2 then ~corp_host arg
     else if kind = 3 then T
     else if kind = 4 then F
     else T`;;

(* ---- the firewall policy, parameterised by an allowlist ----------------
   The allowlist is given to each obligation as two explicit predicates
   over num codes:  in_writes : num->bool   in_hosts : num->bool .
   The closed loop instantiates them with the concrete BASE_A membership
   tests as lambdas, so a too-permissive allowlist is NOT vacuously sound. *)

(* tool_pol_def:79 *)
let tool_pol = new_definition
  `tool_pol (in_writes:num->bool) (in_hosts:num->bool) (kind:num) (arg:num) <=>
     if kind = 0 then T
     else if kind = 4 then T
     else if kind = 1 then in_writes arg
     else if kind = 2 then in_hosts arg
     else if kind = 3 then F
     else F`;;

(* safe_allowlist_def:96 — the allowlist only permits in-spec actions.
   Stated pointwise (decidable side condition), the genuine obligation. *)
let safe_allowlist = new_definition
  `safe_allowlist (in_writes:num->bool) (in_hosts:num->bool) <=>
     (!p. in_writes p ==> sandboxed p) /\
     (!h. in_hosts h ==> corp_host h)`;;

(* ---- the per-action verdict the kernel certifies ----------------------
   ADMIT  : the firewall passes the action AND it is genuinely in-spec.
            tool_pol .. kind arg  /\  ~truly_unsafe kind arg
   REFUSE : the firewall blocks it (must shield).
            ~tool_pol .. kind arg
   These are the two facts the closed loop asks Candle to prove. We expose
   them as definitions purely for readable goal statements. *)

let admit_ok = new_definition
  `admit_ok in_writes in_hosts kind arg <=>
     tool_pol in_writes in_hosts kind arg /\ ~truly_unsafe kind arg`;;

let refuse_ok = new_definition
  `refuse_ok in_writes in_hosts kind arg <=>
     ~tool_pol in_writes in_hosts kind arg`;;

(* ---- soundness link, certified ONCE so the runtime verdicts mean
   something: if the allowlist is safe then admit_ok implies the action is
   within the absolute spec. This is the HOL-Light re-derivation of
   tool_pol_sound (toolAgentScript.sml:116). Candle proves it now. *)
let ADMIT_SOUND = prove
 (`!in_writes in_hosts kind arg.
     safe_allowlist in_writes in_hosts /\
     admit_ok in_writes in_hosts kind arg
     ==> ~truly_unsafe kind arg`,
  REWRITE_TAC[admit_ok] THEN MESON_TAC[]);;

(* And: a refused action is exactly one the firewall does not pass, so the
   shield (Refuse, kind 4) takes over — and Refuse is always in-spec. *)
let SHIELD_SAFE = prove
 (`!arg. ~truly_unsafe 4 arg`,
  REWRITE_TAC[truly_unsafe] THEN ARITH_TAC);;

(* The template is loaded. Each runtime obligation is a tiny `prove`:
     let V_<id> = prove(`admit_ok  IW IH k a`, ARITH/MESON tactic);;
   or
     let V_<id> = prove(`refuse_ok IW IH k a`, ARITH/MESON tactic);;
   echoed by the REPL as `val V_<id> = |- ... : thm` — the kernel witness. *)
