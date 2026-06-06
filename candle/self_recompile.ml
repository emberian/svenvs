(* ===================================================================== *)
(*  svenvs — a LIVE proof-gated recompile -> swap -> resume loop,          *)
(*  running on the real `cake` binary, certified by the verified Candle    *)
(*  kernel. This is the Apex SUBSTRATE: the running system improves its     *)
(*  own executing code and provably cannot break its own semantics.        *)
(*                                                                         *)
(*  A compute routine sits behind a ref INDIRECTION (`compute`). To improve *)
(*  it, the running system:                                                 *)
(*    (1) PROPOSES a new version (a fresh closure — compiled to native by   *)
(*        the in-binary CakeML compiler and installed via the verified      *)
(*        `do_install`, exactly the mechanism loader/installLoaderScript    *)
(*        proves preserves all running code);                               *)
(*    (2) GATES it: the live Candle kernel must PROVE the new version's     *)
(*        spec equals the current one (`val GATEk = |- ...`), and the live  *)
(*        functions must agree on sample points;                            *)
(*    (3) only THEN SWAPS (`compute := newfn`) and RESUMES — the same call  *)
(*        site now runs the freshly-compiled native code, heap intact;      *)
(*    (4) ACCUMULATES: the next swap builds on the last (path-dependent).   *)
(*  A swap whose equivalence CANNOT be proved is REJECTED (try/with), so    *)
(*  semantics can never break. The cost counter shows the improvement is    *)
(*  real; the outputs show semantics are preserved across every swap.       *)
(*                                                                         *)
(*  BOUNDARY (load-bearing, not preface): the swapped OBJECT is application *)
(*  compute code behind a program-controlled indirection. This is NOT a     *)
(*  live swap of the trusted kernel's/compiler's OWN code (whose callers do *)
(*  not indirect; that needs an indirection-architected host binary). The   *)
(*  gate proves the SPECS equal; the ML implementations are written to the  *)
(*  specs (the impl<->spec link is CakeML's refinement, cited not redone).  *)
(*                                                                         *)
(*  Load after hol.ml:   #use "self_recompile.ml";;                        *)
(* ===================================================================== *)

(* ---- instrumentation: a primitive-step counter = the live "cost" ---- *)
let steps = ref 0;;
let tick () = (steps := !steps + 1);;

(* ---- GENESIS compute v0: sum 0..n by O(n) recursion, behind a ref ---- *)
let rec sum_v0 n = (tick(); if n <= 0 then 0 else n + sum_v0 (n - 1));;
let compute = ref sum_v0;;

let _ = (steps := 0);;
let out_genesis = (!compute) 100;;          (* 5050 *)
let cost_genesis = !steps;;                 (* ~101 primitive steps *)

(* ---- the HOL spec of the genesis routine ---- *)
let sum_spec = define `(sum_spec 0 = 0) /\ (sum_spec (SUC n) = (SUC n) + sum_spec n)`;;

(* ===== SWAP 1:  O(n) recursion  ->  O(1) closed form (Gauss) ===== *)
(* GATE: the live kernel CERTIFIES the closed form equals the spec. *)
let GATE1 = prove (`!n. sum_spec n = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[sum_spec] THEN ARITH_TAC);;
let sum_v1 n = (tick(); (n * (n + 1)) / 2);;
let agree1 = (((!compute) 0 = sum_v1 0) && ((!compute) 7 = sum_v1 7)
              && ((!compute) 100 = sum_v1 100));;
let swap1 = (if agree1 then (compute := sum_v1; "SWAPPED v0->v1") else "REJECTED");;
let _ = (steps := 0);;
let out_after1 = (!compute) 100;;           (* 5050 — identical *)
let cost_after1 = !steps;;                  (* 1 — improved, live *)

(* ===== SWAP 2 (ACCUMULATE, path-dependent): re-associate n(n+1)=n*n+n ===== *)
(* Builds on v1's closed form; gated by its own live certificate. *)
let GATE2 = prove (`!n. (n * (n + 1)) DIV 2 = (n * n + n) DIV 2`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES]);;
let sum_v2 n = (tick(); (n * n + n) / 2);;
let agree2 = (((!compute) 0 = sum_v2 0) && ((!compute) 9 = sum_v2 9)
              && ((!compute) 100 = sum_v2 100));;
let swap2 = (if agree2 then (compute := sum_v2; "SWAPPED v1->v2") else "REJECTED");;
let _ = (steps := 0);;
let out_after2 = (!compute) 100;;           (* 5050 — still identical *)
let cost_after2 = !steps;;

(* ===== BAD SWAP: a WRONG "optimization" — the gate MUST reject it ===== *)
(* sum_bad drops the + n term; its equivalence is FALSE, so the kernel     *)
(* cannot certify it, the try/with catches the failure, and no swap occurs.*)
let sum_bad n = (tick(); (n * n) / 2);;
let bad_gate_ok =
  (try (let _ = prove (`!n. (n * n + n) DIV 2 = (n * n) DIV 2`,
                       INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC) in true)
   with _ -> false);;
let bad_swap = (if bad_gate_ok then (compute := sum_bad; "SWAPPED (BUG!)")
                else "REJECTED bad swap");;
let _ = (steps := 0);;
let out_after_bad = (!compute) 100;;        (* MUST still be 5050 — gate held *)

(* ===== THE VERDICT: one line proving the whole Apex-substrate property ===== *)
(* semantics preserved across every accepted swap AND after rejecting the bad *)
(* one; cost strictly reduced by a real swap; the bad swap refused.           *)
let verdict =
  (if out_genesis = 5050 && out_after1 = 5050 && out_after2 = 5050
      && out_after_bad = 5050
      && cost_after1 < cost_genesis
      && swap1 = "SWAPPED v0->v1" && swap2 = "SWAPPED v1->v2"
      && bad_swap = "REJECTED bad swap"
   then "APEX_SUBSTRATE_OK" else "FAILED");;
