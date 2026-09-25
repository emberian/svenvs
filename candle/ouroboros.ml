(* STATUS: ONE generation GREEN on the live Candle kernel (hbox,
   2026-09-25, scripts/reflectsem-live.sh --ouroboros): the constant-folded
   candidate was proved for all i against eval_n, the term-dropping move
   was refused, the proved source was self-fed through Repl.nextString and
   its native code returned [52; -8; 10; 82] = the spec on the samples;
   verdict "OUROBOROS_ONE_GEN_OK...". Not built: several accumulating
   generations, the self-model, and gating the improver itself. Load after
   hol.ml + reflectsem_datatypes.ml + reflectsem_functions.ml. *)
(* ===================================================================== *)
(*  svenvs OUROBOROS — ONE generation of a running binary that edits its  *)
(*  own code, gated by its own kernel against the REAL CakeML semantics.  *)
(*                                                                        *)
(*  At runtime, on the live Candle cake, this program:                    *)
(*    1. SYNTHESIZES a candidate: a generic algebraic move (constant      *)
(*       folding) applied to the genesis champion, a real ast$exp;        *)
(*    2. GATES it: the kernel must PROVE, by symbolic execution of the    *)
(*       ported real semantics (eval_n = fueled full evaluate, pinned to  *)
(*       evaluateTheory by the HOL4 bridge eval_n_agrees), for ALL i:     *)
(*         |- !i. eval_n FUEL (INL (st0, env_x i, [<candidate>])) =       *)
(*                INL (st0, Rval [Litv (IntLit (&6 * i + &10))])          *)
(*       and must REFUSE a semantics-breaking move (it drops a term);     *)
(*    3. INSTALLS the proven candidate: renders the same AST to concrete  *)
(*       syntax and SELF-FEEDS it through Repl.nextString, so the in-     *)
(*       binary verified compiler compiles it to native code, which is    *)
(*       then CALLED on sample inputs.                                    *)
(*  The verdict is computed by the self-fed code itself, after the        *)
(*  install, so it cannot be printed unless all three steps happened.     *)
(*                                                                        *)
(*  scripts/place-submit.sh candle/ouroboros.ml OURO_DONE, then wait for  *)
(*  `val ouro_verdict = "OUROBOROS_ONE_GEN_OK..."` in the place log (the  *)
(*  self-fed declarations run when the REPL next reads, which may be      *)
(*  after the sentinel echo).                                             *)
(*                                                                        *)
(*  Not here yet: several accumulating generations, a self-model that     *)
(*  steers the search, and routing the improver itself through the gate.  *)
(* ===================================================================== *)

(* ---------------- the frozen observable spec ---------------- *)
(* the champion must compute \x. 6*x + 10 (over int), forever *)
let ouro_spec i = 6 * i + 10;;
let ouro_spec_str i = string_of_int (ouro_spec i);;

(* ---------------- the evolving AST IS a real ast$exp term ----------------
   The candidate is a HOL term of the exported type `exp` (the real CakeML
   AST): one int variable x = Var (Short (implode "x")), IntLit literals,
   and App (Arith Add|Sub|Mul IntT) [a; b]. Moves, cost and the concrete-
   syntax rendering all work on that term, so what the gate proves about
   and what gets installed are the same object. (Candle's REPL does not
   accept OCaml variant-type declarations, so there is no ML mirror.) *)
let ouro_add = `Arith Add IntT`;;
let ouro_sub = `Arith Sub IntT`;;
let ouro_mul = `Arith Mul IntT`;;
let ouro_x = `Var (Short (implode "x"))`;;
let ouro_app op a b =
  mk_comb (mk_comb (`App`, op), mk_list ([a; b], `:exp`));;
let ouro_lit n = mk_comb (`Lit`, mk_comb (`IntLit`, mk_intconst n));;

(* Some (op, a, b) for App op [a; b]; None otherwise *)
let ouro_dest_app t =
  try let (f, args) = strip_comb t in
      if fst (dest_const f) = "App" then
        (match args with
           [op; l] -> (match dest_list l with [a; b] -> Some (op, a, b) | _ -> None)
         | _ -> None)
      else None
  with Failure _ -> None;;
(* Some n for Lit (IntLit n) *)
let ouro_dest_lit t =
  try let (f, args) = strip_comb t in
      if fst (dest_const f) = "Lit" then
        (match args with
           [l] -> let (g, ls) = strip_comb l in
                  if fst (dest_const g) = "IntLit" then Some (dest_intconst (hd ls))
                  else None
         | _ -> None)
      else None
  with Failure _ -> None;;

(* size = static cost model *)
let rec osize t =
  match ouro_dest_app t with
    Some (op, a, b) -> 1 + osize a + osize b
  | None -> 1;;

(* render to CakeML concrete syntax (for the self-feed native install) *)
let rec osrc t =
  if aconv t ouro_x then "x"
  else (match ouro_dest_lit t with
          Some n -> osrc_num n
        | None -> osrc_app t)
and osrc_num n =
  if n </ Int 0 then "(0 - " ^ string_of_num (minus_num n) ^ ")"
  else string_of_num n
and osrc_app t =
  match ouro_dest_app t with
    Some (op, a, b) -> "(" ^ osrc a ^ osrc_op op ^ osrc b ^ ")"
  | None -> failwith "osrc: term outside the fragment"
and osrc_op op =
  if aconv op ouro_add then " + "
  else if aconv op ouro_sub then " - "
  else if aconv op ouro_mul then " * "
  else failwith "osrc: operator outside the fragment";;

(* ---------------- the rewrite base (the exported lists) ---------------- *)
let ouro_try f x = try f x with Failure _ -> [];;
let ouro_ctor_thms =
  itlist (fun n acc -> ouro_try (fun n -> [distinctness n]) n @
                       ouro_try (fun n -> [injectivity n]) n @ acc)
         reflectsem_dt_names [];;
let OURO_EXISTS_REFL2 = prove (`!a:A. ?x. a = x`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;
let ouro_defs =
  reflectsem_dt_thms @ reflectsem_fn_thms @ ouro_ctor_thms @
  [FST; SND; OUTL; OUTR; ALL; MAP; REVERSE; APPEND; LENGTH; HD; TL;
   NOT_SUC; PRE; LET_DEF; LET_END_DEF; EXISTS_REFL; OURO_EXISTS_REFL2;
   PAIR_EQ; CONS_11; injectivity "sum"];;

(* WEAK call-by-value normalisation with the exported rewrite base.
   Plain REWRITE_CONV rewrites everywhere, including inside the unapplied
   continuation lambdas of eval_n's case constants and ahead of their
   scrutinees (pair_CASE p f = f (FST p) (SND p) copies an UNevaluated p),
   which is exponential in the nesting depth of the evaluated program: it
   was fine for the smoke gates' closed one-App terms and ran away on a
   depth-7 symbolic one. Here: never rewrite under a lambda; for a case
   constant or COND evaluate only the scrutinee, then fire the clause;
   everything else is evaluated arguments-first. *)
let ouro_net =
  itlist (net_of_thm false)
    (itlist (mk_rewrites false) (ouro_defs @ basic_rewrites ()) [])
    empty_net;;
(* closed arithmetic, but never on SUC: fuel stays a SUC tower, which is
   what the fueled clauses match (NUM_RED_CONV would fold it to 40) *)
let OURO_NUM_CONV tm =
  if is_comb tm && is_const (rator tm) && fst (dest_const (rator tm)) = "SUC"
  then failwith "OURO_NUM_CONV: SUC" else NUM_RED_CONV tm;;
(* the one place a binder body is rewritten: an existential such as
   check_type's `?i'. Litv (IntLit E) = Litv (IntLit i')`, decided by
   constructor injectivity/distinctness and EXISTS_REFL *)
let OURO_EX_CONV tm =
  if is_exists tm then
    REWRITE_CONV (ouro_ctor_thms @ [EXISTS_REFL; OURO_EXISTS_REFL2]) tm
  else failwith "OURO_EX_CONV";;
let OURO_TOP_CONV =
  FIRST_CONV [REWRITES_CONV ouro_net; GEN_BETA_CONV;
              OURO_NUM_CONV; INT_RED_CONV; OURO_EX_CONV];;
let ouro_is_lazy h =
  is_const h &&
  (let n = fst (dest_const h) in
   n = "COND" ||
   (String.length n > 5 &&
    String.sub n (String.length n - 5) 5 = "_CASE"));;
let rec OURO_WEAK_CONV tm =
  if is_abs tm then REFL tm else
  if not (is_comb tm) then
    (* constants with a defining equation (nsEmpty, list_type_num, ...) *)
    (match (try Some (OURO_TOP_CONV tm) with Failure _ -> None) with
       None -> REFL tm
     | Some th -> if aconv (rand (concl th)) tm then REFL tm
                  else TRANS th (OURO_WEAK_CONV (rand (concl th))))
  else
  let (h, args) = strip_comb tm in
  let th1 =
    if ouro_is_lazy h then
      funpow (length args - 1) RATOR_CONV (RAND_CONV OURO_WEAK_CONV) tm
    else
      let (f, x) = dest_comb tm in MK_COMB (OURO_WEAK_CONV f, OURO_WEAK_CONV x) in
  let tm1 = rand (concl th1) in
  match (try Some (OURO_TOP_CONV tm1) with Failure _ -> None) with
    None -> th1
  | Some th2 ->
      (* a conversion that "succeeds" without changing the term (e.g. an
         arithmetic conv on a literal) is no progress: stop, don't loop *)
      if aconv (rand (concl th2)) tm1 then th1
      else TRANS th1 (TRANS th2 (OURO_WEAK_CONV (rand (concl th2))));;

(* ---------------- the GATE: real-semantics correctness, for all i ------ *)
let ouro_fuel = 40;;
let rec ouro_suc n = if n = 0 then "0" else "SUC (" ^ ouro_suc (n-1) ^ ")";;
let ouro_st0 =
  "(state 0 [] (ffi_state (\\nm. \\s. \\conf. \\bytes. Oracle_final FFI_failed) one []) 0 0 NONE)";;
let ouro_env =
  "(sem_env (nsBind (implode \"x\") (Litv (IntLit i)) nsEmpty) nsEmpty)";;

(* symbolic execution of eval_n, then the residual int identity *)
let ouro_gate_tac : tactic =
  GEN_TAC THEN CONV_TAC (LAND_CONV OURO_WEAK_CONV) THEN
  REWRITE_TAC ouro_defs THEN INT_ARITH_TAC;;

let ouro_goal_template =
  parse_term
    ("!i. eval_n (" ^ ouro_suc ouro_fuel ^ ") (INL (" ^ ouro_st0 ^ ", "
     ^ ouro_env ^ ", [ouro_e:exp])) = INL (" ^ ouro_st0
     ^ ", Rval [Litv (IntLit (&6 * i + &10))])");;
let ouro_goal cand = vsubst [cand, `ouro_e:exp`] ouro_goal_template;;

(* prove the gate for a candidate; None if the kernel refuses *)
let ouro_gate cand =
  try Some (prove (ouro_goal cand, ouro_gate_tac)) with Failure _ -> None;;

(* ---------------- moves (generic, not spec-aware) ---------------- *)
(* constant folding: App op [Lit a; Lit b] -> Lit (a op b), bottom-up *)
let rec orw_constfold t =
  match ouro_dest_app t with
    None -> t
  | Some (op, a0, b0) ->
    let a = orw_constfold a0 in
    let b = orw_constfold b0 in
    (match (ouro_dest_lit a, ouro_dest_lit b) with
       (Some m, Some n) ->
         if aconv op ouro_add then ouro_lit (m +/ n)
         else if aconv op ouro_sub then ouro_lit (m -/ n)
         else if aconv op ouro_mul then ouro_lit (m */ n)
         else ouro_app op a b
     | _ -> ouro_app op a b);;
(* a WRONG move (drops a literal summand): the gate must refuse it *)
let rec orw_break t =
  match ouro_dest_app t with
    None -> t
  | Some (op, a, b) ->
    if aconv op ouro_add then
      (match ouro_dest_lit b with Some _ -> a | None -> ouro_app op (orw_break a) b)
    else t;;

(* ---------------- genesis champion ---------------- *)
(* deliberately naive: x + x + x + x + x + x + (3 + 7)  (size 13) *)
let ouro_genesis =
  let s a b = ouro_app ouro_add a b in
  s (s (s (s (s (s ouro_x ouro_x) ouro_x) ouro_x) ouro_x) ouro_x)
    (s (ouro_lit (Int 3)) (ouro_lit (Int 7)));;

(* ---------------- generation 1 ---------------- *)
(* 1. synthesize *)
let ouro_cand = orw_constfold ouro_genesis;;
let ouro_cand_src = osrc ouro_cand;;
let ouro_cand_size = osize ouro_cand;;
(* 2. gate: the candidate must be proved; a term-dropping move must not *)
let ouro_thm = ouro_gate ouro_cand;;
let ouro_gate_ok = (match ouro_thm with Some _ -> true | None -> false);;
let ouro_thm_str =
  (match ouro_thm with Some th -> string_of_thm th | None -> "NONE");;
let ouro_bad = orw_break ouro_cand;;
let ouro_bad_src = osrc ouro_bad;;
let ouro_reject_ok =
  (not (aconv ouro_bad ouro_cand)) &&
  (match ouro_gate ouro_bad with Some _ -> false | None -> true);;

(* 3. install: only a PROVED candidate is fed; its native code is then
   called on sample inputs by the fed code itself, and the verdict is the
   last fed declaration *)
let ouro_inputs = [7; 0 - 3; 0; 12];;
let ouro_feed = ref
  (if ouro_gate_ok then
     ["let (ouro_native_champion, ouro_native_out) = " ^
      "let f = (fun x -> " ^ ouro_cand_src ^ ") in (f, map f ouro_inputs);;";
      "let ouro_verdict = if ouro_gate_ok && ouro_reject_ok && " ^
      "ouro_native_out = map ouro_spec ouro_inputs && ouro_cand_size < osize ouro_genesis " ^
      "then \"OUROBOROS_ONE_GEN_OK: proved for all i, refused the bad move, " ^
      "self-fed, native outputs match the spec\" " ^
      "else \"OUROBOROS_PARTIAL\";;"]
   else ["let ouro_verdict = \"OUROBOROS_PARTIAL: gate refused the candidate\";;"]);;
let ouro_saved = !Repl.readNextString;;
let () = Repl.readNextString := (fun () ->
  match !ouro_feed with
    [] -> (Repl.readNextString := ouro_saved; ouro_saved ())
  | s :: rest -> (ouro_feed := rest; Repl.nextString := s));;
