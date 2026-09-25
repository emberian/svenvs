(* STATUS: GREEN on the live Candle kernel (hbox, 2026-09-25,
   scripts/reflectsem-live.sh --ouroboros, twice from a clean start): 5
   accepted generations, cost (AST size) 19 -> 15 -> 13 -> 11 -> 7 -> 5,
   each champion proved for all i against eval_n, self-fed and run as
   native code that returns the spec on the samples; 2 kernel refusals of
   the semantics-breaking `drop`; the self-model stopped gating `drop`, the
   pruned improver v2 was refused, the deepened improver v3 passed its gate
   and was installed, v4 was refused; verdict "OUROBOROS_OK: 5 generations,
   cost 19 -> 5, 2 rejections, improver upgraded". The improver's fragment
   invariant is checked by ML code, not proved by the kernel. Load after
   hol.ml + reflectsem_datatypes.ml + reflectsem_functions.ml. *)
(* ===================================================================== *)
(*  svenvs OUROBOROS — a running binary that evolves its own code over    *)
(*  several ACCUMULATING generations, each gated by its own kernel        *)
(*  against the REAL CakeML semantics, with a self-model that steers the  *)
(*  search and an improver that is itself replaced through the channel.   *)
(*                                                                        *)
(*  Per generation n, on the live Candle cake:                            *)
(*    1. PARENT: the champion is read out of the kernel theorem that was  *)
(*       installed by generation n-1 (ouro_gen_<n-1>_thm), not from a     *)
(*       local variable: generations are path-dependent.                  *)
(*    2. SEARCH: the INSTALLED improver (ouro_improver_<v>, compiled from *)
(*       self-fed source) enumerates rewrite sequences over the champion  *)
(*       (constant folding, dead-subterm removal, strength reduction      *)
(*       x+x -> 2*x, collecting like terms, reassociation, and `drop`,    *)
(*       which deletes a summand and is sound only when it is zero).      *)
(*       Candidates that do not strictly lower the cost (AST size) are    *)
(*       discarded; the rest are ranked by (cost drop) x (op weights).    *)
(*    3. GATE: the kernel must PROVE, for ALL i,                          *)
(*         |- !i. eval_n FUEL (INL (st0, env_x i, [<candidate>])) =       *)
(*                INL (st0, Rval [Litv (IntLit (&6 * i + &10))])          *)
(*       by symbolic execution of the ported real semantics (eval_n,      *)
(*       pinned to evaluateTheory by the HOL4 bridge eval_n_agrees).      *)
(*       Refusals are recorded; at most ouro_budget gates per generation. *)
(*    4. INSTALL: the proved AST is rendered to concrete syntax and       *)
(*       self-fed through Repl.nextString as `let ouro_champion_<n> =     *)
(*       (fun x -> ...)`; its native code is called on sample inputs.     *)
(*    5. SELF-MODEL: per-op proposed/proved/refused counts give op        *)
(*       weights w = 1000(1+proved)/(1+proposed); only ops with w > 500   *)
(*       are gated; the cost history is kept; the model is echoed.        *)
(*  When a generation stalls, the self-model proposes a new IMPROVER      *)
(*  (prune ops the kernel keeps refusing, then deepen the search), as     *)
(*  source text; it is self-fed and compiled, then GATED: an invariant    *)
(*  check (every output on every past champion is a closed :exp over x,   *)
(*  int literals, + - *, labelled by known ops; checked by ML code, not   *)
(*  by the kernel) and a semantic check (its search on the current        *)
(*  champion yields a kernel-PROVED strictly cheaper candidate). Only     *)
(*  then is it installed (rebound as the live improver).                  *)
(*  The final verdict is a fed declaration evaluated over the installed   *)
(*  champions and certificates.                                           *)
(*                                                                        *)
(*  scripts/reflectsem-live.sh --ouroboros [--generations N]              *)
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

(* the gate, memoised: a term the kernel refused is never re-gated *)
let ouro_memo = ref ([] : (term * bool) list);;
let rec ouro_memo_find t l =
  match l with
    [] -> None
  | (u, b) :: r -> if aconv u t then Some b else ouro_memo_find t r;;
let ouro_gate_memo t =
  match ouro_memo_find t !ouro_memo with
    Some false -> None
  | _ -> (let r = ouro_gate t in
          ouro_memo := (t, (match r with Some _ -> true | None -> false)) :: !ouro_memo;
          r);;

(* reading a champion back out of its certificate *)
let ouro_champ_term th =
  let body = snd (dest_forall (concl th)) in
  let triple = rand (rand (lhs body)) in
  hd (dest_list (snd (dest_pair (snd (dest_pair triple)))));;
(* the theorem is hypothesis-free and states exactly the gate for its own candidate *)
let ouro_is_gate_thm th =
  hyp th = [] && aconv (concl th) (ouro_goal (ouro_champ_term th));;
let ouro_the r = match r with Some th -> th | None -> failwith "ouro: gate refused";;

(* ---------------- local rewrites (generic, not spec-aware) ------------- *)
let ouro_all_ops = ["fold"; "dead"; "double"; "collect"; "reassoc"; "drop"];;
let ouro_is_x t = aconv t ouro_x;;
let ouro_arith op m n =
  if aconv op ouro_add then m +/ n
  else if aconv op ouro_sub then m -/ n
  else if aconv op ouro_mul then m */ n
  else failwith "ouro_arith";;
let ouro_is_lit k t = (match ouro_dest_lit t with Some n -> n =/ Int k | None -> false);;
(* k*y as (k, y); anything else y as (1, y) *)
let ouro_coeff t =
  match ouro_dest_app t with
    Some (op, k, y) ->
      if aconv op ouro_mul then
        (match ouro_dest_lit k with Some n -> (n, y, true) | None -> (Int 1, t, false))
      else (Int 1, t, false)
  | None -> (Int 1, t, false);;
(* every result of one rewrite `nm` AT THE ROOT of t *)
let ouro_rw nm t =
  match ouro_dest_app t with
    None -> []
  | Some (op, a, b) ->
    if nm = "fold" then
      (match (ouro_dest_lit a, ouro_dest_lit b) with
         (Some m, Some n) -> [ouro_lit (ouro_arith op m n)]
       | _ -> [])
    else if nm = "dead" then
      (if aconv op ouro_add then
         (if ouro_is_lit 0 b then [a] else if ouro_is_lit 0 a then [b] else [])
       else if aconv op ouro_sub then (if ouro_is_lit 0 b then [a] else [])
       else if aconv op ouro_mul then
         (if ouro_is_lit 0 a || ouro_is_lit 0 b then [ouro_lit (Int 0)]
          else if ouro_is_lit 1 b then [a] else if ouro_is_lit 1 a then [b] else [])
       else [])
    else if nm = "double" then
      (if aconv op ouro_add && aconv a b then [ouro_app ouro_mul (ouro_lit (Int 2)) a] else [])
    else if nm = "collect" then
      (if aconv op ouro_add then
         (let (k, ya, ea) = ouro_coeff a in
          let (m, yb, eb) = ouro_coeff b in
          if (ea || eb) && aconv ya yb then [ouro_app ouro_mul (ouro_lit (k +/ m)) ya] else [])
       else [])
    else if nm = "reassoc" then
      (if aconv op ouro_add then
         (match ouro_dest_app a with
            Some (op2, a1, a2) ->
              if aconv op2 ouro_add then [ouro_app ouro_add a1 (ouro_app ouro_add a2 b)] else []
          | None -> []) @
         (match ouro_dest_app b with
            Some (op2, b1, b2) ->
              if aconv op2 ouro_add then [ouro_app ouro_add (ouro_app ouro_add a b1) b2] else []
          | None -> [])
       else [])
    else if nm = "drop" then
      (if aconv op ouro_add then [a] else [])
    else [];;
(* ... at exactly one position, preorder (root first) *)
let rec ouro_at nm t =
  let here = ouro_rw nm t in
  match ouro_dest_app t with
    None -> here
  | Some (op, a, b) ->
      here @ map (fun a1 -> ouro_app op a1 b) (ouro_at nm a)
           @ map (fun b1 -> ouro_app op a b1) (ouro_at nm b);;
(* all rewrite sequences of length 1..d over the ops, labelled *)
let rec ouro_expand ops d t =
  if d = 0 then [] else
  let step = itlist (fun nm acc -> map (fun t1 -> ([nm], t1)) (ouro_at nm t) @ acc) ops [] in
  step @ flat (map (fun (l, t1) -> map (fun (l2, t2) -> (l @ l2, t2)) (ouro_expand ops (d - 1) t1)) step);;

(* ---------------- the self-model ---------------- *)
(* op -> (proposed to the kernel, proved, refused) *)
let ouro_stats = ref ([] : (string * (int * int * int)) list);;
let ouro_stat nm = try assoc nm !ouro_stats with Failure _ -> (0, 0, 0);;
let ouro_note l dq dr =
  itlist (fun nm u ->
    let (p, q, r) = ouro_stat nm in
    ouro_stats := (nm, (p + 1, q + dq, r + dr)) ::
                  filter (fun (m, s) -> not (m = nm)) !ouro_stats) l ();;
(* predicted proof rate, per mille (Laplace) *)
let ouro_w nm = let (p, q, r) = ouro_stat nm in (1000 * (1 + q)) / (1 + p);;
let ouro_budget = 3;;
let ouro_hist = ref ([] : (int * int) list);;          (* (gen, cost), newest first *)
let ouro_champs = ref ([] : term list);;               (* installed champions *)
let ouro_refusals = ref ([] : string list);;
let ouro_discarded = ref 0;;
let ouro_imp_ver = ref 1;;
let ouro_imp_cfg = ref (ouro_all_ops, 1);;
let ouro_upgrades = ref 0;;
let ouro_tried = ref ([] : (string list * int) list);;

let rec ouro_join sep l =
  match l with [] -> "" | [s] -> s | s :: r -> s ^ sep ^ ouro_join sep r;;
let soi = string_of_int;;
let ouro_op_str nm =
  let (p, q, r) = ouro_stat nm in
  nm ^ " " ^ soi p ^ "/" ^ soi q ^ "/" ^ soi r ^ " w" ^ soi (ouro_w nm);;
let ouro_model_str n =
  let (ops, d) = !ouro_imp_cfg in
  "gen " ^ soi n ^ " | cost " ^ ouro_join " > " (map (fun (g, c) -> soi c) (rev !ouro_hist)) ^
  " | improver v" ^ soi !ouro_imp_ver ^ " depth " ^ soi d ^ " ops " ^ ouro_join "," ops ^
  " | op proposed/proved/refused weight: " ^ ouro_join ", " (map ouro_op_str ouro_all_ops) ^
  " | kernel refusals " ^ soi (length !ouro_refusals) ^
  ", nonimproving discarded " ^ soi !ouro_discarded ^
  " | next: gate only ops with w > 500 (now: " ^ ouro_join "," (filter (fun nm -> ouro_w nm > 500) ouro_all_ops) ^
  "), best (cost drop x weights) first, budget " ^ soi ouro_budget ^ " kernel gates";;
let ouro_record n th =
  let t = ouro_champ_term th in
  ouro_hist := (n, osize t) :: !ouro_hist;
  ouro_champs := t :: !ouro_champs;;

(* ---------------- the search (steered by the model) ---------------- *)
let ouro_found = ref (None : (string list * term * thm) option);;
let ouro_genlog = ref ([] : string list);;
let ouro_genrej = ref ([] : string list);;
let ouro_eligible (l, t) =
  forall (fun nm -> ouro_w nm > 500) l &&
  (match ouro_memo_find t !ouro_memo with Some false -> false | _ -> true);;
let ouro_score c0 (l, t) =
  itlist (fun nm s -> (s * ouro_w nm) / 1000) l ((c0 - osize t) * 1000);;
let rec ouro_pick c0 best l =
  match l with
    [] -> best
  | c :: r ->
      if not (ouro_eligible c) then ouro_pick c0 best r else
      (match best with
         None -> ouro_pick c0 (Some c) r
       | Some b -> if ouro_score c0 c > ouro_score c0 b then ouro_pick c0 (Some c) r
                   else ouro_pick c0 best r);;
(* the score is taken BEFORE the kernel's answer updates the model *)
let ouro_line c0 (l, t) =
  let pre = "[" ^ ouro_join ";" l ^ "] " ^ osrc t ^ " cost " ^ soi (osize t) ^
            " score " ^ soi (ouro_score c0 (l, t)) ^ " (w " ^
            ouro_join "," (map (fun nm -> soi (ouro_w nm)) l) ^ ") -> " in
  fun v -> pre ^ v;;
let rec ouro_search_loop c0 pool budget =
  if budget = 0 then () else
  match ouro_pick c0 None pool with
    None -> ()
  | Some (l, t) ->
      let ln = ouro_line c0 (l, t) in
      (match ouro_gate_memo t with
         Some th ->
           (ouro_note l 1 0;
            ouro_genlog := ln "PROVED by the kernel" :: !ouro_genlog;
            ouro_found := Some (l, t, th))
       | None ->
           (ouro_note l 0 1;
            ouro_genrej := ln "REFUSED by the kernel" :: !ouro_genrej;
            ouro_refusals := ln "REFUSED by the kernel" :: !ouro_refusals;
            ouro_genlog := ln "REFUSED by the kernel" :: !ouro_genlog;
            ouro_search_loop c0 pool (budget - 1)));;
let ouro_search imp champ =
  ouro_found := None; ouro_genlog := []; ouro_genrej := [];
  let c0 = osize champ in
  let all = (try imp champ with Failure _ -> []) in
  let pool = filter (fun (l, t) -> osize t < c0) all in
  ouro_discarded := !ouro_discarded + (length all - length pool);
  ouro_search_loop c0 pool ouro_budget;
  ("improver emitted " ^ soi (length all) ^ ", cheaper than " ^ soi c0 ^ ": " ^
   soi (length pool)) :: rev !ouro_genlog;;
let ouro_last_rejections () = rev !ouro_genrej;;
let ouro_found_thm () =
  match !ouro_found with Some (l, t, th) -> th | None -> failwith "ouro: nothing found";;
let ouro_found_ops () =
  match !ouro_found with Some (l, t, th) -> l | None -> [];;

(* ---------------- genesis champion ---------------- *)
(* deliberately naive: ((x+x+x+x+x+x) + (3 + 7)) + x * 0   (size 19) *)
let ouro_genesis =
  let s a b = ouro_app ouro_add a b in
  s (s (s (s (s (s (s ouro_x ouro_x) ouro_x) ouro_x) ouro_x) ouro_x)
       (s (ouro_lit (Int 3)) (ouro_lit (Int 7))))
    (ouro_app ouro_mul ouro_x (ouro_lit (Int 0)));;

(* ---------------- the improver, and its gate ---------------- *)
let ouro_ops_src ops = "[" ^ ouro_join "; " (map (fun s -> "\"" ^ s ^ "\"") ops) ^ "]";;
let ouro_improver_src ops d =
  "(fun t -> ouro_expand " ^ ouro_ops_src ops ^ " " ^ soi d ^ " t)";;
(* the fragment invariant (ML-checked, NOT a kernel theorem) *)
let rec ouro_frag t =
  ouro_is_x t ||
  (match ouro_dest_lit t with
     Some n -> true
   | None ->
     (match ouro_dest_app t with
        Some (op, a, b) ->
          (aconv op ouro_add || aconv op ouro_sub || aconv op ouro_mul) &&
          ouro_frag a && ouro_frag b
      | None -> false));;
let ouro_frag_ok t = type_of t = `:exp` && frees t = [] && ouro_frag t;;
let ouro_improver_invariant imp =
  try forall (fun p ->
        forall (fun (l, t) ->
          ouro_frag_ok t && not (l = []) && forall (fun nm -> mem nm ouro_all_ops) l)
          (imp p))
        (ouro_genesis :: !ouro_champs)
  with Failure _ -> false;;
(* the invariant check is not vacuous: an improver that emits a free
   variable y, or labels a step with an unknown op, fails it *)
let ouro_inv_selftest =
  not (ouro_improver_invariant (fun t -> [(["drop"], `Var (Short (implode "y"))`)])) &&
  not (ouro_improver_invariant (fun t -> [(["teleport"], ouro_x)])) &&
  not (ouro_improver_invariant (fun t -> [([], ouro_x)])) &&
  ouro_improver_invariant (fun t -> [(["fold"], ouro_x)]);;
let ouro_imp_passed = ref false;;
let ouro_imp_reason = ref "not gated";;
let ouro_improver_gate inv_ok imp champ =
  ouro_imp_passed := false;
  if not inv_ok then (ouro_imp_reason := "the fragment invariant failed"; ["invariant FAILED"]) else
  let lg = ouro_search imp champ in
  (match !ouro_found with
     Some _ -> (ouro_imp_passed := true; ouro_imp_reason := "passed")
   | None -> ouro_imp_reason := "invariant held, but its search yielded no kernel-proved strictly cheaper candidate");
  lg;;
let ouro_improver_reason () = !ouro_imp_reason;;
let ouro_improver_gate_passed () = !ouro_imp_passed;;
let ouro_improver_installed v ops d =
  ouro_imp_ver := v; ouro_imp_cfg := (ops, d); ouro_upgrades := !ouro_upgrades + 1;;
(* the self-model's proposals, cheapest first: prune ops the kernel keeps
   refusing (>= 1 refusal and w <= 500), then deepen the search (<= 3) *)
let ouro_next_ver = ref 2;;
let ouro_sort_ops ops =
  itlist (fun nm acc ->
    let (hi, lo) = partition (fun m -> ouro_w m > ouro_w nm) acc in
    hi @ [nm] @ lo) ops [];;
let ouro_propose () =
  let (ops, d) = !ouro_imp_cfg in
  let kept = filter (fun nm -> let (p, q, r) = ouro_stat nm in
                               not (r >= 1 && ouro_w nm <= 500)) (ouro_sort_ops ops) in
  let cands =
    (if length kept < length ops then [("prune the ops the kernel refuses", kept, d)] else []) @
    (if d < 3 then [("deepen the search", kept, d + 1)] else []) in
  let fresh = filter (fun (why, ops2, d2) -> not (mem (ops2, d2) !ouro_tried)) cands in
  match fresh with
    [] -> None
  | (why, ops2, d2) :: rest ->
      (ouro_tried := (ops2, d2) :: !ouro_tried;
       let v = !ouro_next_ver in
       ouro_next_ver := v + 1;
       Some (v, ops2, d2, why));;

(* ---------------- the verdict ---------------- *)
let rec ouro_decreasing l =
  match l with a :: b :: r -> b < a && ouro_decreasing (b :: r) | _ -> true;;
let ouro_verdict_of costs natives final_ok =
  let n = length costs - 1 in
  let k = length !ouro_refusals in
  if n >= 3 && ouro_decreasing costs && forall (fun b -> b) natives && final_ok &&
     k >= 1 && !ouro_upgrades >= 1 && ouro_inv_selftest
  then "OUROBOROS_OK: " ^ soi n ^ " generations, cost " ^ soi (hd costs) ^ " -> " ^
       soi (last costs) ^ ", " ^ soi k ^ " rejections, improver upgraded"
  else "OUROBOROS_PARTIAL: " ^ soi n ^ " generations, " ^ soi k ^ " rejections, " ^
       soi !ouro_upgrades ^ " improver upgrades";;

(* ---------------- the loop: a planner feeding the REPL ---------------- *)
(* Every fed string is one complete declaration; each runs before the next
   is planned, so a plan can depend on what installed code just computed.
   Fed code is raw CakeML (no quotations). *)
let ouro_max_gens = 8;;
let ouro_inputs = [7; 0 - 3; 0; 12];;
let ouro_state = ref (0, 0);;     (* 0 start | 1 search n | 2 decide n | 3 improver n | 4 finish | 5 done *)
let ouro_accepted = ref [0];;     (* accepted generations, newest first *)
let ouro_pending = ref (0, ([] : string list), 0);;
let ouro_g n = "ouro_gen_" ^ soi n;;
let ouro_escape s = ouro_join "" (map (fun c -> if c = "\"" then "\\\"" else c) (explode s));;
let ouro_quote s = "\"" ^ s ^ "\"";;
let ouro_batch_install n src =
  [ "let " ^ ouro_g n ^ "_cand_src = osrc (ouro_champ_term " ^ ouro_g n ^ "_thm);;";
    "let " ^ ouro_g n ^ "_gate_ok = ouro_is_gate_thm " ^ ouro_g n ^ "_thm;;";
    "let " ^ ouro_g n ^ "_cost = osize (ouro_champ_term " ^ ouro_g n ^ "_thm);;";
    "let ouro_champion_" ^ soi n ^ " = (fun x -> " ^ src ^ ");;";
    "let " ^ ouro_g n ^ "_native_out = map ouro_champion_" ^ soi n ^ " ouro_inputs;;";
    "let " ^ ouro_g n ^ "_native_ok = " ^ ouro_g n ^ "_gate_ok && " ^ ouro_g n ^ "_native_out = map ouro_spec ouro_inputs && " ^
      ouro_g n ^ "_cand_src = " ^ ouro_quote src ^ ";;";
    "let () = ouro_record " ^ soi n ^ " " ^ ouro_g n ^ "_thm;;";
    "let " ^ ouro_g n ^ "_model = ouro_model_str " ^ soi n ^ ";;" ];;
let ouro_batch_start () =
  ("let ouro_improver_1 = " ^ ouro_improver_src ouro_all_ops 1 ^ ";;") ::
  "let ouro_gen_0_thm = ouro_the (ouro_gate ouro_genesis);;" ::
  ouro_batch_install 0 (osrc ouro_genesis);;
let ouro_parent n = "(ouro_champ_term " ^ ouro_g (n - 1) ^ "_thm)";;
let ouro_batch_search n =
  [ "let " ^ ouro_g n ^ "_parent_src = osrc " ^ ouro_parent n ^ ";;";
    "let " ^ ouro_g n ^ "_search = ouro_search ouro_improver_" ^ soi !ouro_imp_ver ^ " " ^ ouro_parent n ^ ";;";
    "let " ^ ouro_g n ^ "_rejections = ouro_last_rejections ();;" ];;
let ouro_batch_accept n =
  match !ouro_found with
    Some (l, t, th) ->
      ("let " ^ ouro_g n ^ "_thm = ouro_found_thm ();;") ::
      ("let " ^ ouro_g n ^ "_ops = ouro_found_ops ();;") ::
      ouro_batch_install n (osrc t)
  | None -> [];;
let ouro_batch_improver n v ops d why =
  let iv = "ouro_improver_" ^ soi v in
  [ "let " ^ iv ^ "_proposal = " ^ ouro_quote ("gen " ^ soi n ^ " stalled under v" ^ soi !ouro_imp_ver ^
       "; the model proposes v" ^ soi v ^ ": " ^ why ^ " (ops " ^ ouro_join "," ops ^
       ", depth " ^ soi d ^ ")") ^ ";;";
    "let " ^ iv ^ "_src = " ^ ouro_quote (ouro_escape (ouro_improver_src ops d)) ^ ";;";
    "let ouro_improver_cand_" ^ soi v ^ " = " ^ ouro_improver_src ops d ^ ";;";
    "let " ^ iv ^ "_inv_ok = ouro_improver_invariant ouro_improver_cand_" ^ soi v ^ ";;";
    "let " ^ iv ^ "_gate = ouro_improver_gate " ^ iv ^ "_inv_ok ouro_improver_cand_" ^ soi v ^ " " ^ ouro_parent n ^ ";;";
    "let " ^ iv ^ "_gate_ok = ouro_improver_gate_passed ();;" ];;
let ouro_batch_finish () =
  let acc = rev !ouro_accepted in
  let k = hd !ouro_accepted in
  [ "let ouro_costs = [" ^ ouro_join "; " (map (fun n -> ouro_g n ^ "_cost") acc) ^ "];;";
    "let ouro_natives_ok = [" ^ ouro_join "; " (map (fun n -> ouro_g n ^ "_native_ok") acc) ^ "];;";
    "let ouro_final_src = " ^ ouro_g k ^ "_cand_src;;";
    "let ouro_final_native_out = map ouro_champion_" ^ soi k ^ " ouro_inputs;;";
    "let ouro_model_final = ouro_model_str " ^ soi k ^ ";;";
    "let ouro_verdict = ouro_verdict_of ouro_costs ouro_natives_ok " ^
      "(ouro_final_native_out = map ouro_spec ouro_inputs);;" ];;
let rec ouro_plan () =
  let (tag, n) = !ouro_state in
  if tag = 0 then (ouro_state := (1, 1); ouro_batch_start ())
  else if tag = 1 then
    (if n > ouro_max_gens then (ouro_state := (4, n); ouro_plan ())
     else (ouro_state := (2, n); ouro_batch_search n))
  else if tag = 2 then
    (match !ouro_found with
       Some _ -> (ouro_state := (1, n + 1); ouro_accepted := n :: !ouro_accepted;
                  ouro_batch_accept n)
     | None ->
       (match ouro_propose () with
          Some (v, ops, d, why) ->
            (ouro_pending := (v, ops, d); ouro_imp_passed := false;
             ouro_state := (3, n); ouro_batch_improver n v ops d why)
        | None -> (ouro_state := (4, n); ouro_plan ())))
  else if tag = 3 then
    (let (v, ops, d) = !ouro_pending in
     let iv = "ouro_improver_" ^ soi v in
     if !ouro_imp_passed then
       (ouro_state := (1, n + 1); ouro_accepted := n :: !ouro_accepted;
        [ "let " ^ iv ^ " = ouro_improver_cand_" ^ soi v ^ ";;";
          "let () = ouro_improver_installed " ^ soi v ^ " " ^ ouro_ops_src ops ^ " " ^ soi d ^ ";;";
          "let " ^ iv ^ "_installed = " ^ ouro_quote ("improver v" ^ soi v ^
             " passed its gate and is now the live improver") ^ ";;" ] @
        ouro_batch_accept n)
     else
       (ouro_state := (2, n);
        [ "let " ^ iv ^ "_rejected = " ^ ouro_quote ("improver v" ^ soi v ^ " refused, not installed: ") ^
            " ^ ouro_improver_reason ();;" ]))
  else if tag = 4 then (ouro_state := (5, n); ouro_batch_finish ())
  else [];;

let ouro_queue = ref ([] : string list);;
let ouro_saved = !Repl.readNextString;;
let rec ouro_hook () =
  match !ouro_queue with
    s :: rest -> (ouro_queue := rest; Repl.nextString := s)
  | [] ->
      let b = (try ouro_plan () with Failure _ ->
                (ouro_state := (5, 0); ["let ouro_plan_failed = true;;"])) in
      if b = [] then (Repl.readNextString := ouro_saved; ouro_saved ())
      else (ouro_queue := b; ouro_hook ());;
let () = Repl.readNextString := ouro_hook;;
