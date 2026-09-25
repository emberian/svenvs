(* STATUS: WIP, not yet run against the live kernel. Requires the exported
   reflectsem_datatypes.ml + reflectsem_functions.ml loaded into a
   place-server first; RS_SMOKE_VERDICT is unverified. *)
(* ===================================================================== *)
(*  svenvs reflectsem — GATE SMOKE TEST: the live Candle kernel proves    *)
(*  its first theorems about the REAL CakeML semantics (the ported        *)
(*  eval_n = fueled full evaluate), by pure rewriting/computation.        *)
(*                                                                        *)
(*  Load AFTER reflectsem_datatypes.ml + reflectsem_functions.ml.         *)
(*  scripts/place-submit.sh candle/reflectsem_gate_smoke.ml RS_SMOKE_OK   *)
(* ===================================================================== *)

(* --- the rewrite base: every reflectsem definition, recovered from the
       kernel's definition log (covers the anonymous accessor defines) --- *)
let rs_def_consts = ref ([] : string list);;

(* collect every definition theorem whose lhs head is one of our constants;
   cheap approximation: all definitions after the marker constant nsEmpty
   was born would also work, but filtering by current constants is robust *)
let rs_defs () = definitions ();;

(* fuel as a SUC tower (no numeral conversion needed in rewriting) *)
let rec rs_fuel n = if n = 0 then "0" else "SUC (" ^ rs_fuel (n-1) ^ ")";;

(* a minimal state at unit ffi: clock 0, no refs, dummy oracle, no events *)
let rs_st0 =
  "(state 0 [] (ffi_state (\\name. \\s. \\conf. \\bytes. Oracle_final FFI_failed) one []) 0 0 NONE)";;
let rs_env0 = "(sem_env nsEmpty nsEmpty)";;

(* ---- GATE 1: a literal evaluates to itself (one eval_n step) ---- *)
let rs_g1 = parse_term
  ("eval_n (" ^ rs_fuel 5 ^ ") (INL (" ^ rs_st0 ^ ", " ^ rs_env0 ^
   ", [Lit (IntLit (& 5))])) = INL (" ^ rs_st0 ^ ", Rval [Litv (IntLit (& 5))])");;

let RS_GATE_CONV =
  TOP_DEPTH_CONV (FIRST_CONV [NUM_RED_CONV; INT_RED_CONV])
  THENC REWRITE_CONV (rs_defs ());;

(* iterate rewriting + arithmetic until fixpoint *)
let rec RS_NORM_CONV tm =
  (REWRITE_CONV (rs_defs ())
   THENC TOP_DEPTH_CONV (FIRST_CONV [NUM_RED_CONV; INT_RED_CONV])
   THENC (fun t -> if t = tm then REFL t else RS_NORM_CONV t)) tm;;

let rs_thm1 = prove (rs_g1,
  CONV_TAC (LAND_CONV RS_NORM_CONV) THEN REWRITE_TAC (rs_defs ()));;

(* ---- GATE 2: real arithmetic through the real semantics:
        App (Arith Add IntT) [Lit 3; Lit 4]  ==>  Litv 7  ---- *)
let rs_lhs2 = parse_term
  ("eval_n (" ^ rs_fuel 20 ^ ") (INL (" ^ rs_st0 ^ ", " ^ rs_env0 ^
   ", [App (Arith Add IntT) [Lit (IntLit (& 3)); Lit (IntLit (& 4))]]))");;
let rs_thm2 = RS_NORM_CONV rs_lhs2;;
let rs_out2 = string_of_term (rand (concl rs_thm2));;

(* verdict: gate 1 proved; gate 2 must produce Rval [Litv (IntLit 7)] *)
let rs_ok2 =
  (try (let expected = parse_term
          ("INL (" ^ rs_st0 ^ ", Rval [Litv (IntLit (& 7))])") in
        aconv (rand (concl rs_thm2)) expected)
   with _ -> false);;

let RS_SMOKE_VERDICT = if rs_ok2 then "RS_SMOKE_OK" else "RS_SMOKE_PARTIAL";;
