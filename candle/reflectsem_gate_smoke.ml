(* STATUS: GREEN on the live Candle kernel (hbox, 2026-09-25, driven by
   scripts/reflectsem-live.sh after the 45 exported datatypes and the
   exported function cone): gates 1-3 are proved, hypothesis-free, and the
   kernel echoes `val rs_thm1/2/3 = |- eval_n ... = INL (...)` and
   RS_SMOKE_VERDICT = "RS_SMOKE_OK: 3 gates proved". *)
(* ===================================================================== *)
(*  svenvs reflectsem — GATE SMOKE TEST: the live Candle kernel proves    *)
(*  its first theorems about the REAL CakeML semantics (the ported        *)
(*  eval_n = fueled full evaluate), by bounded rewriting + arithmetic.    *)
(*                                                                        *)
(*  Load AFTER reflectsem_datatypes.ml + reflectsem_functions.ml.         *)
(*  scripts/place-submit.sh candle/reflectsem_gate_smoke.ml RS_SMOKE_OK   *)
(* ===================================================================== *)

(* --- the rewrite base: EXACTLY the exported lists (case / record
       theorems of the 45 datatypes, and every rewrite-safe clause theorem
       of the function cone, each proved in this kernel from its
       definition), plus HOL Light list/sum/pair basics and the
       constructors' distinctness/injectivity --- *)
let rs_try f x = try f x with Failure _ -> [];;
let rs_ctor_thms =
  itlist (fun n acc -> rs_try (fun n -> [distinctness n]) n @
                       rs_try (fun n -> [injectivity n]) n @ acc)
         reflectsem_dt_names [];;
let RS_EXISTS_REFL2 = prove (`!a:A. ?x. a = x`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;
let rs_basic =
  [FST; SND; OUTL; OUTR; ALL; MAP; REVERSE; APPEND; LENGTH; HD; TL;
   NOT_SUC; PRE; LET_DEF; LET_END_DEF; EXISTS_REFL; RS_EXISTS_REFL2];;
let rs_thms = reflectsem_dt_thms @ reflectsem_fn_thms @ rs_basic @ rs_ctor_thms;;

(* one step: rewrite to normal form, then evaluate closed num/int arithmetic *)
let RS_STEP_CONV =
  REWRITE_CONV rs_thms THENC NUM_REDUCE_CONV THENC INT_REDUCE_CONV;;

(* iterate to a fixpoint, BOUNDED: fails loudly instead of running away *)
let rec RS_NORM_N k tm =
  if k = 0 then failwith "RS_NORM_BOUND_EXCEEDED" else
  let th = RS_STEP_CONV tm in
  let r = rand (concl th) in
  if aconv r tm then th else TRANS th (RS_NORM_N (k - 1) r);;
let RS_NORM_CONV = RS_NORM_N 40;;

(* fuel as a SUC tower (the fueled clauses match SUC, not numerals) *)
let rec rs_fuel n = if n = 0 then "0" else "SUC (" ^ rs_fuel (n-1) ^ ")";;

(* a minimal state at unit ffi: clock 0, no refs, failing oracle, no events,
   stamps 0, no eval state; the empty environment *)
let rs_st0 =
  "(state 0 [] (ffi_state (\\name. \\s. \\conf. \\bytes. Oracle_final FFI_failed) one []) 0 0 NONE)";;
let rs_env0 = "(sem_env nsEmpty nsEmpty)";;

(* ---- GATE 1: a literal evaluates to itself ---- *)
let rs_g1 = parse_term
  ("eval_n (" ^ rs_fuel 5 ^ ") (INL (" ^ rs_st0 ^ ", " ^ rs_env0 ^
   ", [Lit (IntLit (&5))])) = INL (" ^ rs_st0 ^ ", Rval [Litv (IntLit (&5))])");;
let rs_thm1 = prove (rs_g1, CONV_TAC (LAND_CONV RS_NORM_CONV) THEN REFL_TAC);;

(* ---- GATE 2: real arithmetic through the real semantics:
        App (Arith Add IntT) [Lit 3; Lit 4]  evaluates to  Litv 7 ---- *)
let rs_g2 = parse_term
  ("eval_n (" ^ rs_fuel 20 ^ ") (INL (" ^ rs_st0 ^ ", " ^ rs_env0 ^
   ", [App (Arith Add IntT) [Lit (IntLit (&3)); Lit (IntLit (&4))]])) = INL (" ^
   rs_st0 ^ ", Rval [Litv (IntLit (&7))])");;
let rs_thm2 = prove (rs_g2, CONV_TAC (LAND_CONV RS_NORM_CONV) THEN REFL_TAC);;

(* ---- GATE 3: a type error is a type error: adding an int to a string
        is rejected by the real semantics (Rabort Rtype_error) ---- *)
let rs_g3 = parse_term
  ("eval_n (" ^ rs_fuel 20 ^ ") (INL (" ^ rs_st0 ^ ", " ^ rs_env0 ^
   ", [App (Arith Add IntT) [Lit (IntLit (&3)); Lit (StrLit (implode []))]])) = INL (" ^
   rs_st0 ^ ", Rerr (Rabort Rtype_error))");;
let rs_thm3 = prove (rs_g3, CONV_TAC (LAND_CONV RS_NORM_CONV) THEN REFL_TAC);;

let RS_SMOKE_VERDICT = "RS_SMOKE_OK: 3 gates proved";;
