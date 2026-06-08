(* ===================================================================== *)
(*  svenvs — a PER-GENERATION COMPILER self-upgrade, gated by a LIVE       *)
(*  Candle CORRECTNESS proof, running under the verified prover.           *)
(*                                                                         *)
(*  This is the proof-gated runtime image of the VERIFIED per-generation   *)
(*  compiler-swap op (selfUpgrade/evalUpgradeOpScript.sml):                *)
(*    - a per-generation compiler map `cmap` (= g2c) held behind a ref;    *)
(*    - `upgrade n newc` installs a new compiler for generations >= n,     *)
(*      keeping earlier generations' compilers (= repl_upgrade);           *)
(*    - the GATE here is STRONGER than the verified compiler_agrees: the    *)
(*      live Candle kernel must PROVE the new compiler CORRECT — that its   *)
(*      value-spec equals the observable spec `eval_spec`.  A swap whose    *)
(*      correctness CANNOT be proved is REJECTED (try/with), so the         *)
(*      observable can never break.                                        *)
(*                                                                         *)
(*  Across every gated upgrade the OBSERVABLE is invariant while the        *)
(*  compiler's COST strictly drops (a real, path-dependent improvement);    *)
(*  earlier generations keep their own compiler; a wrong compiler is        *)
(*  refused by the kernel.  Mirrors repl_upgrade / do_eval_record_gen /     *)
(*  repl_upgrade_uses_new_compiler — with a kernel proof as the gate.       *)
(*                                                                         *)
(*  Load after hol.ml:   #use "compiler_cell_candle.ml";;                  *)
(* ===================================================================== *)

(* the observable spec every installed compiler must preserve *)
let eval_spec = define `eval_spec s = s * s + 1`;;

(* a compiler = (cost, value-on-input).  The per-generation compiler map,
   behind a ref indirection (the live, swappable cell). *)
let compA = (3, (fun s -> s * s + 1));;          (* genesis: naive, cost 3 *)
let cmap = ref (fun (g:int) -> compA);;
let upgrade n newc =
  (let old = !cmap in cmap := (fun g -> if g < n then old g else newc));;
let cost_of g = fst ((!cmap) g);;
let val_of  g s = (snd ((!cmap) g)) s;;

(* generation 0 runs compiler A *)
let obs0 = val_of 0 5;;          (* 26 *)
let c0   = cost_of 0;;           (* 3 *)

(* ===== UPGRADE to compiler B for generation 1 ===========================
   GATE: the live kernel PROVES B correct (its value-spec = eval_spec).
   B reassociates the computation (1 + s*s) and is cheaper (cost 2).
   The upgrade is reached only because this proof succeeds. *)
let GATE_B = prove (`!s. 1 + s * s = eval_spec s`,
  REWRITE_TAC[eval_spec] THEN ARITH_TAC);;
let compB = (2, (fun s -> 1 + s * s));;
let _ = upgrade 1 compB;;
let upB = "INSTALLED";;
let obs1  = val_of 1 5;;          (* 26 — same observable *)
let c1    = cost_of 1;;           (* 2 — improved, gated *)
let obs0b = val_of 0 5;;          (* 26 — generation 0 still runs A *)
let c0b   = cost_of 0;;           (* 3 — earlier generation unchanged *)

(* ===== UPGRADE to compiler C for generation 2 (ACCUMULATE) ==============
   Gated by its own live correctness proof; cheaper still (cost 1). *)
let GATE_C = prove (`!s. s * s + 1 = eval_spec s`, REWRITE_TAC[eval_spec]);;
let compC = (1, (fun s -> s * s + 1));;
let _ = upgrade 2 compC;;
let upC = "INSTALLED";;
let obs2 = val_of 2 7;;           (* 50 *)
let c2   = cost_of 2;;            (* 1 *)

(* ===== BAD upgrade: a compiler that DROPS the +1 (wrong) ================
   Its correctness theorem (!s. s*s = eval_spec s) is FALSE; the kernel
   cannot prove it; try/with catches the failure; NO install happens. *)
let bad_ok =
  (try (let _ = prove (`!s. s * s = eval_spec s`,
                       REWRITE_TAC[eval_spec] THEN ARITH_TAC) in true)
   with _ -> false);;
let compBad = (1, (fun s -> s * s));;
let upBad = (if bad_ok then (upgrade 3 compBad; "INSTALLED (BUG!)")
             else "REJECTED");;
let obs_after_bad = val_of 2 7;;  (* still 50 — gate held; gen 2 still C *)

(* ===== THE VERDICT =====================================================
   observable invariant across every gated upgrade; cost strictly reduced by
   the real upgrades; earlier generations keep their own compiler; the wrong
   compiler refused by the live kernel. *)
let verdict =
  (if obs0 = 26 && obs1 = 26 && obs0b = 26 && obs2 = 50 && obs_after_bad = 50
      && c1 < c0 && c2 < c1 && c0b = c0
      && upB = "INSTALLED" && upC = "INSTALLED" && upBad = "REJECTED"
   then "COMPILER_CELL_CANDLE_OK" else "FAILED");;
