(*
  encFaithScript.sml  —  FAITHFULNESS OF THE CLOSED-LOOP num-ENCODING.

  The closed-loop runtime (agent/closedloop/closed_loop.py) does NOT ship the
  string-based absolute spec of toolAgentScript.sml to the Candle kernel. The
  kernel works on a num-only dialect (obligation_template.ml), so Python
  performs a string->num encoding (the "~10-line trusted residue"):

      KIND : tool name -> num   (Read 0, Write 1, Net 2, Exec 3, Refuse 4)
      ARG  : path/host string -> num
             /sandbox/a..d -> 1..4 ; corp.internal/logs.internal -> 11/12 ;
             anything else -> a fresh code >= 50.

  The kernel then certifies the NUM spec:
      truly_unsafe_num kind arg  (obligation_template.ml truly_unsafe)
  whereas the proven HOL4 theorem (agent_enveloped_safe) is about the STRING
  spec  truly_unsafe : tool -> bool.

  TRUST GAP: even if Candle proves  ~truly_unsafe_num (kind a),  that only
  bounds the REAL action iff  truly_unsafe_num (enc kind a) <=> truly_unsafe
  (the string action).  THAT equivalence is exactly what the Python encoding
  silently assumes. This theory PROVES it, in HOL4, so the residue shrinks to
  "the Python table equals enc_arg / kind_code" — a finite, eyeball-checkable
  fact with NO logical content left unproven.

  Builds against toolAgentTheory (pure HOL4 core, no CakeML/candle).
  Holmakefile INCLUDES must contain the agent dir and the svenvs core dir.
*)
open HolKernel boolLib bossLib BasicProvers
     listTheory stringTheory arithmeticTheory optionTheory
     toolAgentTheory;

val _ = new_theory "encFaith";

(* ------------------------------------------------------------------ *)
(*  1. The NUM dialect, transcribed 1:1 from obligation_template.ml.   *)
(* ------------------------------------------------------------------ *)

(* obligation_template.ml :24  sandboxed (p:num) <=> 1 <= p /\ p <= 4 *)
Definition sandboxed_num_def:
  sandboxed_num (p:num) <=> (1 <= p /\ p <= 4)
End

(* obligation_template.ml :28  corp_host (h:num) <=> h = 11 \/ h = 12 *)
Definition corp_host_num_def:
  corp_host_num (h:num) <=> (h = 11 \/ h = 12)
End

(* obligation_template.ml :38  truly_unsafe on (kind,arg) num codes. *)
Definition truly_unsafe_num_def:
  truly_unsafe_num (kind:num) (arg:num) <=>
    if kind = 0 then F
    else if kind = 1 then ~sandboxed_num arg
    else if kind = 2 then ~corp_host_num arg
    else if kind = 3 then T
    else if kind = 4 then F
    else T
End

(* obligation_template.ml :54  tool_pol on num codes (allowlist membership
   given as predicates in_writes / in_hosts : num -> bool). *)
Definition tool_pol_num_def:
  tool_pol_num (in_writes:num->bool) (in_hosts:num->bool) (kind:num) (arg:num) <=>
    if kind = 0 then T
    else if kind = 4 then T
    else if kind = 1 then in_writes arg
    else if kind = 2 then in_hosts arg
    else if kind = 3 then F
    else F
End

(* ------------------------------------------------------------------ *)
(*  2. The ENCODING, defined IN HOL exactly as the Python bridge does. *)
(* ------------------------------------------------------------------ *)

(* closed_loop.py :56  ARG table for the six allowlisted strings. *)
Definition arg_table_def:
  arg_table (s:string) : num option =
    if s = "/sandbox/a" then SOME 1
    else if s = "/sandbox/b" then SOME 2
    else if s = "/sandbox/c" then SOME 3
    else if s = "/sandbox/d" then SOME 4
    else if s = "corp.internal" then SOME 11
    else if s = "logs.internal" then SOME 12
    else NONE
End

(* closed_loop.py :59 arg_code: table strings get their code; every OTHER
   string gets a fresh "bad" code >= 50 (counter _bad starts at 49 and
   pre-increments, so the first bad code returned is 50). *)
Definition is_bad_code_def:
  is_bad_code (c:num) <=> 50 <= c
End

(* enc_arg s c : c is a legitimate encoding of string s under the bridge.
   Table string -> its code; otherwise -> some fresh bad code. This relation
   captures EXACTLY the guarantee arg_code provides for ANY value its
   nondeterministic counter may emit. *)
Definition enc_arg_def:
  enc_arg (s:string) (c:num) <=>
    case arg_table s of
      SOME k => (c = k)
    | NONE   => is_bad_code c
End

(* enc_tool tc kc ac : (kc,ac) is a legitimate num-encoding of tool call tc.
   The kind code is fixed per constructor (closed_loop.py KIND); the arg
   code follows enc_arg of the relevant string. Refuse carries no string,
   so any arg code is fine (the kernel ignores arg when kind = 4). *)
Definition enc_tool_def:
  (enc_tool (Read s)  kc ac <=> (kc = 0n) /\ enc_arg s ac) /\
  (enc_tool (Write s) kc ac <=> (kc = 1n) /\ enc_arg s ac) /\
  (enc_tool (Net s)   kc ac <=> (kc = 2n) /\ enc_arg s ac) /\
  (enc_tool (Exec s)  kc ac <=> (kc = 3n) /\ enc_arg s ac) /\
  (enc_tool (Refuse)  kc ac <=> (kc = 4n))
End

(* ------------------------------------------------------------------ *)
(*  3. Structural facts about the table the bridge relies on.          *)
(* ------------------------------------------------------------------ *)

(* sandboxed (string spec) IFF the table code is a sandbox num code. *)
Theorem sandboxed_iff_table:
  !s. sandboxed s <=> ?k. arg_table s = SOME k /\ sandboxed_num k
Proof
  rw[sandboxed_def, arg_table_def, sandboxed_num_def] >>
  rw[] >> EQ_TAC >> rw[] >> fs[]
QED

(* corp_host (string spec) IFF the table code is a corp num code. *)
Theorem corp_host_iff_table:
  !s. corp_host s <=> ?k. arg_table s = SOME k /\ corp_host_num k
Proof
  rw[corp_host_def, arg_table_def, corp_host_num_def] >>
  rw[] >> EQ_TAC >> rw[] >> fs[]
QED

(* A bad code is never a sandbox or corp num code. *)
Theorem bad_not_sandboxed_num:
  !c. is_bad_code c ==> ~sandboxed_num c
Proof rw[is_bad_code_def, sandboxed_num_def]
QED

Theorem bad_not_corp_num:
  !c. is_bad_code c ==> ~corp_host_num c
Proof rw[is_bad_code_def, corp_host_num_def]
QED

(* Bridging lemma: for the encoded arg of a Write, the num sandbox test
   agrees with the string sandbox test. *)
Theorem sandboxed_num_enc:
  !s c. enc_arg s c ==> (sandboxed_num c <=> sandboxed s)
Proof
  rw[enc_arg_def] >> Cases_on `arg_table s` >> fs[]
  >- (rw[] >> metis_tac[sandboxed_iff_table, NOT_SOME_NONE,
                        bad_not_sandboxed_num])
  >- (metis_tac[sandboxed_iff_table, SOME_11])
QED

Theorem corp_host_num_enc:
  !s c. enc_arg s c ==> (corp_host_num c <=> corp_host s)
Proof
  rw[enc_arg_def] >> Cases_on `arg_table s` >> fs[]
  >- (rw[] >> metis_tac[corp_host_iff_table, NOT_SOME_NONE,
                        bad_not_corp_num])
  >- (metis_tac[corp_host_iff_table, SOME_11])
QED

(* ------------------------------------------------------------------ *)
(*  4. THE FAITHFULNESS THEOREM.                                       *)
(*     For ANY tool call and ANY legitimate encoding of its argument,  *)
(*     the NUM spec the Candle kernel checks agrees EXACTLY with the   *)
(*     STRING spec the HOL4 theorem agent_enveloped_safe is about.     *)
(* ------------------------------------------------------------------ *)

Theorem enc_truly_unsafe_faithful:
  !tc kc ac.
    enc_tool tc kc ac ==>
    (truly_unsafe_num kc ac <=> truly_unsafe tc)
Proof
  Cases >> rw[enc_tool_def, truly_unsafe_num_def, truly_unsafe_def] >>
  metis_tac[sandboxed_num_enc, corp_host_num_enc]
QED

(* ------------------------------------------------------------------ *)
(*  5. COROLLARY — the verdict the kernel returns MEANS what the loop  *)
(*     claims. If Candle certifies the num action safe, the REAL       *)
(*     (string) action is within the absolute spec.                    *)
(* ------------------------------------------------------------------ *)

(* A Candle `~truly_unsafe_num` certificate transfers to the string world. *)
Theorem candle_safe_transfers:
  !tc kc ac.
    enc_tool tc kc ac /\ ~truly_unsafe_num kc ac ==> ~truly_unsafe tc
Proof
  metis_tac[enc_truly_unsafe_faithful]
QED

(* Contrapositive: a genuinely unsafe REAL action can NEVER be certified
   safe by the kernel through this encoding — no encoding choice (incl. the
   counter's bad codes) lets an unsafe action slip past. *)
Theorem unsafe_never_certified:
  !tc kc ac.
    truly_unsafe tc /\ enc_tool tc kc ac ==> truly_unsafe_num kc ac
Proof
  metis_tac[enc_truly_unsafe_faithful]
QED

val _ = export_theory ();
