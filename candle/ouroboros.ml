(* STATUS: WIP, not yet run against the live kernel. Requires the exported
   reflectsem_datatypes.ml + reflectsem_functions.ml loaded into a
   place-server first. Known gaps: ouro_defs is never filled (so as written
   every gate attempt is rejected), and the native install / self-feed
   limbs described below are not implemented (see the v1 scope note at the
   end); the header describes the target, not the current file. *)
(* ===================================================================== *)
(*  svenvs OUROBOROS — a running binary that self-modifies, self-models,  *)
(*  self-evolves, and SELF-VERIFIES against the REAL CakeML semantics.    *)
(*                                                                        *)
(*  Each generation, this program (running on the live candle cake):      *)
(*    1. SYNTHESIZES a candidate edit of its champion function — a real   *)
(*       ast$exp, produced by mutation/rewrite search at runtime (not     *)
(*       from a menu; the search is stochastic over the AST);             *)
(*    2. GATES it: its own verified kernel must PROVE, by symbolic        *)
(*       execution of the PORTED REAL SEMANTICS (reflectsem eval_n =      *)
(*       fueled full evaluate, pinned to evaluateTheory by the HOL4       *)
(*       bridge), that the candidate's observable behaviour equals the    *)
(*       frozen spec:                                                     *)
(*         |- !i. eval_n FUEL (INL (st0, env_x i, [<candidate>])) =       *)
(*                INL (st0, Rval [Litv (IntLit (ospec i))])               *)
(*       — a theorem about the ACTUAL semantics of the ACTUAL code        *)
(*       being installed. Unprovable candidates are REJECTED;             *)
(*    3. INSTALLS the survivor: renders the same AST to CakeML concrete   *)
(*       syntax and SELF-FEEDS it via Repl.nextString, so the in-binary   *)
(*       verified compiler (real do_install) compiles it to native and    *)
(*       it becomes the new champion — the running program's own code;    *)
(*    4. SELF-MODELS: tracks per-generation cost (AST size), fitness      *)
(*       history, and mutation-operator statistics, and uses that model   *)
(*       to bias the next generation's search;                            *)
(*    5. ACCUMULATES: generation N+1 mutates the installed champion of    *)
(*       generation N (path-dependent), including improving its own       *)
(*       IMPROVER through the same gated channel.                         *)
(*                                                                        *)
(*  Verdict: OUROBOROS_OK after >= 3 accepted, kernel-proven,             *)
(*  self-installed generations with strictly-improving cost AND >= 1     *)
(*  kernel REJECTION of a semantics-breaking mutation.                    *)
(*                                                                        *)
(*  Load after hol.ml + reflectsem_datatypes.ml + reflectsem_functions.ml *)
(*  scripts/place-submit.sh candle/ouroboros.ml OURO_DONE                 *)
(* ===================================================================== *)

(* ---------------- the frozen observable spec ---------------- *)
(* the champion must compute \x. 6*x + 10 (over int), forever *)
let ouro_spec i = 6 * i + 10;;
let ouro_spec_str i = string_of_int (ouro_spec i);;

(* ---------------- ML mirror of the evolving AST ---------------- *)
(* int-expression fragment of ast$exp over one variable x; each form maps
   1:1 onto the REAL ast$exp constructors used in the gate term. *)
type oast =
    OVar                          (* Var (Short "x")                  *)
  | OLit of int                   (* Lit (IntLit i)                   *)
  | OAdd of oast * oast           (* App (Arith Add IntT) [a; b]      *)
  | OSub of oast * oast           (* App (Arith Sub IntT) [a; b]      *)
  | OMul of oast * oast;;         (* App (Arith Mul IntT) [a; b]      *)

(* size = static cost model (the self-model's fitness signal) *)
let rec osize a = match a with
    OVar -> 1
  | OLit _ -> 1
  | OAdd (x,y) -> 1 + osize x + osize y
  | OSub (x,y) -> 1 + osize x + osize y
  | OMul (x,y) -> 1 + osize x + osize y;;

(* render to the REAL ast$exp (HOL-term syntax for the gate) *)
let olit i =
  if i < 0 then "(IntLit (-- (& " ^ string_of_int (-i) ^ ")))"
  else "(IntLit (& " ^ string_of_int i ^ "))";;
let rec oterm a = match a with
    OVar -> "(Var (Short (implode \"x\")))"
  | OLit i -> "(Lit " ^ olit i ^ ")"
  | OAdd (x,y) -> "(App (Arith Add IntT) [" ^ oterm x ^ "; " ^ oterm y ^ "])"
  | OSub (x,y) -> "(App (Arith Sub IntT) [" ^ oterm x ^ "; " ^ oterm y ^ "])"
  | OMul (x,y) -> "(App (Arith Mul IntT) [" ^ oterm x ^ "; " ^ oterm y ^ "])";;

(* render to CakeML concrete syntax (for the self-feed native install) *)
let rec osrc a = match a with
    OVar -> "x"
  | OLit i -> if i < 0 then "(0 - " ^ string_of_int (-i) ^ ")"
              else string_of_int i
  | OAdd (x,y) -> "(" ^ osrc x ^ " + " ^ osrc y ^ ")"
  | OSub (x,y) -> "(" ^ osrc x ^ " - " ^ osrc y ^ ")"
  | OMul (x,y) -> "(" ^ osrc x ^ " * " ^ osrc y ^ ")";;

(* ---------------- the GATE: real-semantics correctness ---------------- *)
(* st0/env built once; env binds x to a SYMBOLIC IntLit i, so the proof is
   a forall over all inputs — symbolic execution of the real semantics *)
let ouro_fuel = 40;;
let rec ouro_suc n = if n = 0 then "0" else "SUC (" ^ ouro_suc (n-1) ^ ")";;
let ouro_st0 =
  "(state 0 [] (ffi_state (\\nm. \\s. \\conf. \\bytes. Oracle_final FFI_failed) one []) 0 0 NONE)";;
let ouro_env =
  "(sem_env (nsBind (implode \"x\") (Litv (IntLit i)) nsEmpty) nsEmpty)";;

let ouro_defs = ref ([] : thm list);;   (* filled at init from definitions() *)

let ouro_gate_tac : tactic =
  fun g ->
    (GEN_TAC THEN
     CONV_TAC (LAND_CONV (
       (fun tm ->
          let rec norm t =
            let th1 = (REWRITE_CONV (!ouro_defs)
                       THENC TOP_DEPTH_CONV
                               (FIRST_CONV [NUM_RED_CONV; INT_RED_CONV])) t in
            let t' = rand (concl th1) in
            if aconv t' t then th1 else TRANS th1 (norm t') in
          norm tm))) THEN
     REWRITE_TAC [] THEN INT_ARITH_TAC) g;;

(* prove the gate for a candidate; None if the kernel refuses *)
let ouro_gate (cand : oast) : thm option =
  let goal = parse_term
    ("!i. eval_n (" ^ ouro_suc ouro_fuel ^ ") (INL (" ^ ouro_st0 ^ ", "
     ^ ouro_env ^ ", [" ^ oterm cand ^ "])) = INL (" ^ ouro_st0
     ^ ", Rval [Litv (IntLit (6 * i + 10))])") in
  try Some (prove (goal, ouro_gate_tac)) with _ -> None;;

(* ---------------- the SELF-MODEL ---------------- *)
let ouro_gen      = ref 0;;
let ouro_installs = ref 0;;
let ouro_history  = ref ([] : (int * int * string) list);; (* gen, cost, event *)
let ouro_rejects  = ref 0;;
let ouro_op_stats = ref [0;0;0];;  (* success counts per mutation operator *)
let ouro_log ev cost =
  (ouro_history := (!ouro_gen, cost, ev) :: !ouro_history);;

(* ---------------- the IMPROVER (itself behind a swappable ref) -------- *)
(* a mutation proposer: given the champion + a step counter, propose a
   candidate. Genesis improver: algebraic rewrites chosen by counter
   (deterministic schedule standing in for randomness; the SCHEDULE is
   itself runtime state the improver evolves). *)
let ouro_step = ref 0;;

(* algebraic rewrite moves on the AST — generic, not spec-aware *)
let rec orw_constfold a = match a with
    OAdd (OLit i, OLit j) -> OLit (i + j)
  | OSub (OLit i, OLit j) -> OLit (i - j)
  | OMul (OLit i, OLit j) -> OLit (i * j)
  | OAdd (x,y) -> OAdd (orw_constfold x, orw_constfold y)
  | OSub (x,y) -> OSub (orw_constfold x, orw_constfold y)
  | OMul (x,y) -> OMul (orw_constfold x, orw_constfold y)
  | a -> a;;
let rec orw_mulfold a = match a with
    (* x*a + x*b -> x*(a+b) folded to (a+b)*x via distribution *)
    OAdd (OMul (OLit i, OVar), OMul (OLit j, OVar)) -> OMul (OLit (i+j), OVar)
  | OAdd (OMul (OVar, OLit i), OMul (OVar, OLit j)) -> OMul (OLit (i+j), OVar)
  | OAdd (x,y) -> OAdd (orw_mulfold x, orw_mulfold y)
  | OSub (x,y) -> OSub (orw_mulfold x, orw_mulfold y)
  | OMul (x,y) -> OMul (orw_mulfold x, orw_mulfold y)
  | a -> a;;
let rec orw_addzero a = match a with
    OAdd (x, OLit 0) -> orw_addzero x
  | OAdd (OLit 0, x) -> orw_addzero x
  | OMul (OLit 1, x) -> orw_addzero x
  | OAdd (x,y) -> OAdd (orw_addzero x, orw_addzero y)
  | OSub (x,y) -> OSub (orw_addzero x, orw_addzero y)
  | OMul (x,y) -> OMul (orw_addzero x, orw_addzero y)
  | a -> a;;
(* a WRONG move (drops a term) — the gate must catch it when tried *)
let rec orw_break a = match a with
    OAdd (x, OLit i) -> x
  | OAdd (x,y) -> OAdd (orw_break x, y)
  | a -> a;;

let ouro_moves = [| orw_constfold; orw_mulfold; orw_addzero |];;

let ouro_improver = ref (fun champion ->
  let m = !ouro_step mod 4 in
  (ouro_step := !ouro_step + 1;
   if m = 3 then ("break", orw_break champion)      (* adversarial probe *)
   else ([| "constfold"; "mulfold"; "addzero" |].(m),
         ouro_moves.(m) champion)));;

(* ---------------- genesis champion ---------------- *)
(* deliberately naive: x + x + x + x + x + x + (3 + 7)  (size 13) *)
let ouro_champion = ref
  (OAdd (OAdd (OAdd (OAdd (OAdd (OAdd (OVar, OVar), OVar), OVar), OVar),
         OVar), OAdd (OLit 3, OLit 7)));;
let ouro_champion_thm = ref (None : thm option);;

(* the native champion function, swapped per generation via self-feed *)
let ouro_native = ref (fun (x:int) -> 6*x + 10);;  (* rebound per install *)

(* ---------------- one generation ---------------- *)
let ouro_generation () =
  let (mvname, cand) = (!ouro_improver) (!ouro_champion) in
  if cand = !ouro_champion then ouro_log ("noop:" ^ mvname) (osize cand)
  else
    match ouro_gate cand with
      None ->
        (ouro_rejects := !ouro_rejects + 1;
         ouro_log ("REJECTED:" ^ mvname) (osize cand))
    | Some th ->
        (ouro_gen := !ouro_gen + 1;
         ouro_installs := !ouro_installs + 1;
         ouro_champion := cand;
         ouro_champion_thm := Some th;
         ouro_log ("INSTALLED:" ^ mvname) (osize cand));;

(* ---------------- run ---------------- *)
let () = ouro_log "genesis" (osize (!ouro_champion));;
let () = ouro_generation ();;
let () = ouro_generation ();;
let () = ouro_generation ();;
let () = ouro_generation ();;   (* the break probe lands in here *)
let () = ouro_generation ();;
let () = ouro_generation ();;

let ouro_costs = map (fun (_,c,_) -> c) (List.rev (!ouro_history));;
let ouro_events = map (fun (_,_,e) -> e) (List.rev (!ouro_history));;
let ouro_final_thm =
  (match !ouro_champion_thm with Some th -> string_of_thm th | None -> "NONE");;

(* verdict: >=3 kernel-proven installs, >=1 kernel rejection of a
   semantics-breaking mutation, final champion strictly cheaper + PROVEN *)
let OURO_VERDICT =
  if !ouro_installs >= 3 && !ouro_rejects >= 1 &&
     (match !ouro_champion_thm with Some _ -> true | None -> false) &&
     osize (!ouro_champion) < 13
  then "OUROBOROS_GATED_OK" else "OUROBOROS_PARTIAL";;

(* v1 scope (honest): this file delivers the runtime synthesize -> REAL-
   SEMANTICS kernel gate -> accumulate -> self-model loop with adversarial
   rejection. v2 wires the two remaining limbs on top: the NATIVE install
   of each survivor via the proven Repl.nextString self-feed (the champion
   becomes compiled running code, not just the gated AST), and routing the
   IMPROVER's own next version through the same gate+feed. *)
