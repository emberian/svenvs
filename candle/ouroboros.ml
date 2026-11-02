(* STATUS: GREEN on the live Candle kernel (scripts/reflectsem-live.sh
   --ouroboros): 5 accepted generations, cost (AST size) 19 -> 15 -> 13 ->
   11 -> 7 -> 5, each champion proved for all i against eval_n, self-fed and
   run as native code that returns the spec on the samples; 2 kernel refusals
   of the semantics-breaking `drop`; the self-model stopped gating `drop`,
   the pruned improver v2 was refused, the deepened improver v3 passed its
   gate and was installed, v4 was refused. All 5 accepted generations are
   certified through the general kernel rewriter theorems of
   candle/ouroboros_rewrites.ml (ofold_preserves, orw_oeq, OEQ_DOUBLE,
   OEQ_COLLECT1, OEQ_COLLECT2, OEQ_REASSOC, OEQ_OFOLD, OEQ_ADD, OEQ_SUB,
   OEQ_MUL, OEQ_TRANS, oeq_preserves), by SPEC/MP and the parent's
   certificate, with zero per-candidate eval_n symbolic execution. The
   partial-composition route (orw_oeq + congruence + oeq_preserves) is also
   exercised on the genesis champion every run (ouro_rw_selftest). Verdict
   "OUROBOROS_OK: 5 generations, cost 19 -> 5, 2 rejections, improver
   upgraded, 5 via the rewriter theorem". The improver's fragment invariant
   is checked by ML code, not proved by the kernel (only the fold/dead
   rewriter's is a theorem, ofold_frag). Load after hol.ml +
   reflectsem_datatypes.ml + reflectsem_functions.ml + ouroboros_rewrites.ml. *)
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
(*       over the ported real semantics (eval_n, pinned to evaluateTheory *)
(*       by the HOL4 bridge eval_n_agrees).                               *)
(*       Refusals are recorded; at most ouro_budget gates per generation. *)
(*       Every candidate produced by the kernel-proved rewrites from the  *)
(*       champion (ofold champion, or any composition of fold, dead,      *)
(*       double, collect, reassoc steps at any positions) skips symbolic  *)
(*       execution: its gate theorem is derived from the general kernel   *)
(*       theorems of candle/ouroboros_rewrites.ml instantiated at the     *)
(*       champion and chained with the champion's certificate             *)
(*       (ouro_gen_<n>_route = "rewriter theorem").                       *)
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

(* the rewrite base (ouro_defs) and the weak call-by-value normaliser
   (OURO_WEAK_CONV) live in candle/ouroboros_rewrites.ml, which proves the
   rewriter theorems with them and is loaded before this file *)

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

(* ---------------- the REWRITER route (candle/ouroboros_rewrites.ml) ---- *)
(* A candidate that the kernel-proved rewrites produce from the champion
   needs no symbolic execution: its gate theorem is ofold_preserves (or,
   for any composition of fold/dead/double/collect/reassoc steps,
   orw_oeq + OEQ_DOUBLE + OEQ_COLLECT1 + OEQ_COLLECT2 + OEQ_REASSOC +
   OEQ_OFOLD + the congruences OEQ_ADD/OEQ_SUB/OEQ_MUL + OEQ_TRANS +
   oeq_preserves) instantiated at the champion, chained with the
   champion's own certificate. What is computed here in ML is only WHICH
   theorem instances to build; every step is a kernel inference, and the
   result must be literally the gate theorem for the candidate. *)
let ouro_fuel_tm = parse_term (ouro_suc ouro_fuel);;
let ouro_le_tm l = mk_comb (mk_comb (`(<=):num->num->bool`, l), ouro_fuel_tm);;
(* the fragment exp term -> the oexp term it should embed *)
let rec ouro_to_o t =
  if ouro_is_x t then `OX` else
  match ouro_dest_lit t with
    Some n -> mk_comb (`OLit`, rand (rand t))
  | None ->
    (match ouro_dest_app t with
       Some (op, a, b) ->
         let c = if aconv op ouro_add then `OAdd`
                 else if aconv op ouro_sub then `OSub`
                 else if aconv op ouro_mul then `OMul`
                 else failwith "ouro_to_o: operator outside the fragment" in
         mk_comb (mk_comb (c, ouro_to_o a), ouro_to_o b)
     | None -> failwith "ouro_to_o: term outside the fragment");;
(* |- oemb p = t, by the kernel, and literally t *)
let ouro_emb p t =
  let th = OEMB_CONV (mk_comb (`oemb`, p)) in
  if aconv (rand (concl th)) t then th else failwith "ouro_emb: not the term";;

(* prove the gate for a candidate via OEVAL (with symbolic execution fallback);
   None if the kernel refuses *)
let ouro_gate cand =
  match (try Some (let p = ouro_to_o cand in
                   let th_e = ouro_emb p cand in
                   let fuel_th = EQT_ELIM ((LAND_CONV OFUEL_CONV THENC NUM_REDUCE_CONV)
                                             (ouro_le_tm (mk_comb (`ofuel`, p)))) in
                   (p, th_e, fuel_th))
         with Failure _ -> None) with
    Some (p, th_e, fuel_th) ->
      (try let ev_th = SUBS [th_e] (MP (SPECL [p; ouro_fuel_tm; `i:int`] OEVAL) fuel_th) in
           let sem_eq = prove (mk_eq (mk_comb (mk_comb (`osem`, p), `i:int`), `&6 * (i:int) + &10`),
                               REWRITE_TAC [osem_def] THEN INT_ARITH_TAC) in
           let g = GEN `i:int` (CONV_RULE OURO_UNFOLD_CONV (SUBS [sem_eq] ev_th)) in
           if ouro_is_gate_thm g then Some g else None
       with Failure _ -> None)
  | None ->
      (try Some (prove (ouro_goal cand, ouro_gate_tac)) with Failure _ -> None);;

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

let ouro_obin t =
  try let (f, args) = strip_comb t in
      let n = fst (dest_const f) in
      (match args with
         [a; b] -> if n = "OAdd" || n = "OSub" || n = "OMul" then Some (n, a, b) else None
       | _ -> None)
  with Failure _ -> None;;
let ouro_ois_lit t =
  try is_comb t && fst (dest_const (rator t)) = "OLit"
  with Failure _ -> false;;
let ouro_ocoeff t =
  match ouro_obin t with
    Some ("OMul", k, y) -> if ouro_ois_lit k then Some (k, y) else None
  | _ -> None;;
(* fold the literal coefficient sum in OEQ_COLLECT1 / OEQ_COLLECT2 via OEQ_OFOLD *)
let ouro_fold_coeff th_col y =
  let lhs1 = lhand (concl th_col) in
  let k_add = lhand lhs1 in
  let th_eq = OFOLDO_CONV (mk_comb (`ofoldo`, k_add)) in
  let k1 = rand (concl th_eq) in
  let th_k = EQ_MP (AP_THM (AP_TERM `oeq` th_eq) k_add) (SPEC k_add OEQ_OFOLD) in
  let th_m = MATCH_MP OEQ_MUL (CONJ th_k (SPEC y OEQ_REFL)) in
  (mk_comb (mk_comb (`OMul`, k1), y), MATCH_MP OEQ_TRANS (CONJ th_m th_col));;
(* all 1-step kernel certificates (p1, |- oeq p1 p) at the root of p *)
let ouro_root_certs p =
  let rw_l =
    (try let th1 = ORW_CONV (mk_comb (`orw`, p)) in
         let p1 = rand (concl th1) in
         if aconv p1 p then []
         else [(p1, EQ_MP (AP_THM (AP_TERM `oeq` th1) p) (SPEC p orw_oeq))]
     with Failure _ -> []) in
  let alg_l =
    match ouro_obin p with
      Some ("OAdd", a, b) ->
        (if aconv a b then
           [(mk_comb (mk_comb (`OMul`, `OLit (&2)`), a), SPEC a OEQ_DOUBLE)]
         else []) @
        (match (ouro_ocoeff a, ouro_ocoeff b) with
           (Some (k, ya), Some (m, yb)) ->
             if aconv ya yb then [ouro_fold_coeff (SPECL [k; m; ya] OEQ_COLLECT2) ya] else []
         | (Some (k, ya), None) ->
             if aconv ya b then [ouro_fold_coeff (SPECL [k; ya] OEQ_COLLECT1) ya] else []
         | (None, Some (m, yb)) ->
             if aconv a yb then [ouro_fold_coeff (SPECL [m; yb] OEQ_COLLECT1_L) yb] else []
         | (None, None) -> []) @
        (match ouro_obin a with
           Some ("OAdd", a1, a2) ->
             [(mk_comb (mk_comb (`OAdd`, a1), mk_comb (mk_comb (`OAdd`, a2), b)),
               SPECL [a1; a2; b] OEQ_REASSOC_R);
              (mk_comb (mk_comb (`OAdd`, mk_comb (mk_comb (`OAdd`, a1), b)), a2),
               SPECL [a1; b; a2] OEQ_REASSOC)]
         | _ -> []) @
        (match ouro_obin b with
           Some ("OAdd", b1, b2) ->
             [(mk_comb (mk_comb (`OAdd`, mk_comb (mk_comb (`OAdd`, a), b1)), b2),
               SPECL [a; b1; b2] OEQ_REASSOC_L)]
         | _ -> [])
    | _ -> [] in
  rw_l @ alg_l;;
(* all 1-step kernel certificates (p1, |- oeq p1 p) at any position in p *)
let rec ouro_step_certs p =
  let here = ouro_root_certs p in
  match ouro_obin p with
    None -> here
  | Some (n, a, b) ->
      let op = rator (rator p) in
      let cg = if n = "OAdd" then OEQ_ADD
               else if n = "OSub" then OEQ_SUB else OEQ_MUL in
      let r_steps =
        map (fun (b1, thb) ->
               (mk_comb (mk_comb (op, a), b1),
                MATCH_MP cg (CONJ (SPEC a OEQ_REFL) thb)))
            (ouro_step_certs b) in
      let l_steps =
        map (fun (a1, tha) ->
               (mk_comb (mk_comb (op, a1), b),
                MATCH_MP cg (CONJ tha (SPEC b OEQ_REFL))))
            (ouro_step_certs a) in
      here @ r_steps @ l_steps;;
(* bounded multi-step certificate search: |- oeq c p *)
let rec ouro_ocert_steps d p c =
  if aconv p c then SPEC p OEQ_REFL else
  if d = 0 then failwith "ouro_ocert: depth bound" else
  let steps = ouro_step_certs p in
  match filter (fun (p1, _) -> aconv p1 c) steps with
    (_, th) :: _ -> th
  | [] ->
    if d = 1 then failwith "ouro_ocert: not 1-step" else
    let rec try_list l =
      match l with
        [] -> failwith "ouro_ocert: no path"
      | (p1, th1) :: r ->
          (try let th2 = ouro_ocert_steps (d - 1) p1 c in
               MATCH_MP OEQ_TRANS (CONJ th2 th1)
           with Failure _ -> try_list r) in
    try_list steps;;
(* |- oeq c p: c is reached from p by kernel-proved rewrites at any positions *)
let rec ouro_ocert p c =
  if aconv p c then SPEC p OEQ_REFL else
  try ouro_ocert_cong p c with Failure _ ->
  let th_fp = OFOLDO_CONV (mk_comb (`ofoldo`, p)) in
  if aconv (rand (concl th_fp)) c then
    EQ_MP (AP_THM (AP_TERM `oeq` th_fp) p) (SPEC p OEQ_OFOLD)
  else ouro_ocert_steps 2 p c
and ouro_ocert_cong p c =
  match (ouro_obin p, ouro_obin c) with
    (Some (n, a, b), Some (m, a2, b2)) ->
      if n = m then
        (let cg = if n = "OAdd" then OEQ_ADD
                  else if n = "OSub" then OEQ_SUB else OEQ_MUL in
         MATCH_MP cg (CONJ (ouro_ocert a a2) (ouro_ocert b b2)))
      else failwith "ouro_ocert: different operators"
  | _ -> failwith "ouro_ocert: not both applications";;

let ouro_via_cong = "orw_oeq+congruence, oeq_preserves";;

(* ---------------- Fused :cval compute + proof-gated compiler cell ------ *)
let rec ouro_to_cval t =
  if ouro_is_x t then `Cexp_pair (Cexp_num 0) (Cexp_num 0)` else
  match ouro_dest_lit t with
    Some n ->
      if n >=/ Int 0 then mk_comb (`Cexp_num`, mk_numeral n)
      else `Cexp_num 0`
  | None ->
    (match ouro_dest_app t with
       Some (op, a, b) ->
         let tag = if aconv op ouro_add then `Cexp_num 1`
                   else if aconv op ouro_sub then `Cexp_num 2`
                   else if aconv op ouro_mul then `Cexp_num 3`
                   else failwith "ouro_to_cval: op" in
         mk_comb (mk_comb (`Cexp_pair`, tag),
                  mk_comb (mk_comb (`Cexp_pair`, ouro_to_cval a), ouro_to_cval b))
     | None -> failwith "ouro_to_cval: term");;

let ouro_exec_orw e =
  let p = ouro_to_o e in
  let th = (RAND_CONV ORW_CONV THENC OEMB_CONV) (mk_comb (`oemb`, mk_comb (`orw`, p))) in
  rand (concl th);;
let ouro_exec_fold e =
  let p = ouro_to_o e in
  let th = (RAND_CONV OFOLDO_CONV THENC OEMB_CONV) (mk_comb (`oemb`, mk_comb (`ofoldo`, p))) in
  rand (concl th);;

let ouro_cval_check t =
  let cv = ouro_to_cval t in
  let p = ouro_to_o t in
  let th_nodes = ouro_kernel_compute (mk_comb (`cval_nodes`, cv)) in
  let th_fuel  = ouro_kernel_compute (mk_comb (`cval_fuel`, cv)) in
  let th_ofuel = OFUEL_CONV (mk_comb (`ofuel`, p)) in
  let th_fold  = ouro_kernel_compute (mk_comb (`cval_fold`, cv)) in
  let eval_at k =
    let th = ouro_kernel_compute
               (mk_comb (mk_comb (`cval_eval`, cv),
                        mk_comb (`Cexp_num`, mk_numeral (Int k)))) in
    hyp th = [] &&
    aconv (rand (concl th)) (mk_comb (`Cexp_num`, mk_numeral (Int (ouro_spec k)))) in
  hyp th_nodes = [] &&
  aconv (rand (concl th_nodes)) (mk_comb (`Cexp_num`, mk_numeral (Int (osize t)))) &&
  hyp th_fuel = [] &&
  aconv (rand (concl th_fuel)) (mk_comb (`Cexp_num`, rand (concl th_ofuel))) &&
  hyp th_fold = [] &&
  aconv (rand (concl th_fold)) (ouro_to_cval (ouro_exec_fold t)) &&
  eval_at 0 && eval_at 7 && eval_at 12;;

(* Proof-gated AST compiler cell: can ONLY be mutated by presenting an
   unforgeable kernel theorem `[] |- !e k i. ofrag e /\ efuel e <= k ==>
     eval_n k (INL (ost0, oenv i, [<pass> e])) = eval_n k (INL (ost0, oenv i, [e]))`
   for the real CakeML `eval_n` semantics. *)
let ouro_compiler_cell : (term -> term) ref = ref (fun e -> e);;
let active_pass e = (!ouro_compiler_cell) e;;
let ouro_compiler_cell_name = ref "id";;
let ouro_compiler_cell_const = ref `I:exp->exp`;;
let ouro_compiler_cell_gen = ref 0;;
let ouro_compiler_cell_thm = ref (None : thm option);;
let ouro_cmap : (int -> string * (term -> term)) ref =
  ref (fun _ -> ("id", (fun e -> e)));;
let ouro_pass_goal_template =
  `!e k i. ofrag e /\ efuel e <= k ==>
     eval_n k (INL (ost0, oenv i, [ouro_pass_var (e:exp)])) =
     eval_n k (INL (ost0, oenv i, [e]))`;;
let ouro_is_pass_thm pass_const (th : thm) =
  hyp th = [] &&
  aconv (concl th) (vsubst [pass_const, `ouro_pass_var:exp->exp`] ouro_pass_goal_template);;
let ouro_install_compiler_pass pass_name pass_const (th : thm) (pass_fn : term -> term) =
  if ouro_is_pass_thm pass_const th then
    (let g1 = !ouro_compiler_cell_gen + 1 in
     let prev = !ouro_cmap in
     ouro_compiler_cell := pass_fn;
     ouro_compiler_cell_name := pass_name;
     ouro_compiler_cell_const := pass_const;
     ouro_compiler_cell_gen := g1;
     ouro_compiler_cell_thm := Some th;
     ouro_cmap := (fun g -> if g = g1 then (pass_name, pass_fn) else prev g);
     true)
  else false;;
let ouro_init_cell_orw () =
  ouro_compiler_cell_gen := 0;
  ouro_cmap := (fun _ -> ("id", (fun e -> e)));
  ouro_install_compiler_pass "orw_exp" `orw_exp` orw_exp_preserves ouro_exec_orw;;
let ouro_upgrade_cell_to_fold () =
  ouro_install_compiler_pass "ofold" `ofold` ofold_preserves ouro_exec_fold;;
let ouro_pass_eq_conv pass_const oof_eq t =
  if aconv pass_const `ofold` then
    (REWRITE_CONV [ofold_def; oof_eq] THENC RAND_CONV OFOLDO_CONV THENC
     OEMB_CONV) (mk_comb (`ofold`, t))
  else if aconv pass_const `orw_exp` then
    (REWRITE_CONV [orw_exp_def; oof_eq] THENC RAND_CONV ORW_CONV THENC
     OEMB_CONV) (mk_comb (`orw_exp`, t))
  else failwith "ouro_pass_eq_conv: unknown pass_const";;

(* (which theorem, the gate theorem for c), or Failure *)
let ouro_rw_route cth c =
  let t = ouro_champ_term cth in
  let p = ouro_to_o t in
  let pc = ouro_to_o c in
  let th_t = ouro_emb p t in
  let th_c = ouro_emb pc c in
  let cell_cand = active_pass t in
  let (via, eq) =
    if aconv cell_cand c then
      (let pass_th = ouro_the !ouro_compiler_cell_thm in
       let pass_const = !ouro_compiler_cell_const in
       let pass_via = !ouro_compiler_cell_name ^ "_preserves" in
       let oof_eq = TRANS (AP_TERM `oof` (SYM th_t)) (SPEC p OOF_OEMB) in
       let frag = EQ_MP (SYM (SPEC t ofrag_oemb))
                    (EXISTS (mk_exists (`q:oexp`, mk_eq (t, mk_comb (`oemb`, `q:oexp`))), p)
                            (SYM th_t)) in
       let fuel = prove (ouro_le_tm (mk_comb (`efuel`, t)),
                    REWRITE_TAC [efuel_def; oof_eq] THEN
                    CONV_TAC (LAND_CONV OFUEL_CONV THENC NUM_REDUCE_CONV)) in
       let pass_t = ouro_pass_eq_conv pass_const oof_eq t in
       if not (aconv (rand (concl pass_t)) c) then failwith "ouro_rw_route: pass_t is not the candidate" else
       (pass_via,
        SUBS [pass_t] (MP (SPECL [t; ouro_fuel_tm; `i:int`] pass_th) (CONJ frag fuel))))
    else
      (let cert = ouro_ocert p pc in
       let fuel_c = EQT_ELIM ((LAND_CONV OFUEL_CONV THENC NUM_REDUCE_CONV)
                                (ouro_le_tm (mk_comb (`ofuel`, pc)))) in
       let fuel_p = EQT_ELIM ((LAND_CONV OFUEL_CONV THENC NUM_REDUCE_CONV)
                                (ouro_le_tm (mk_comb (`ofuel`, p)))) in
       (ouro_via_cong,
        SUBS [th_c; th_t]
          (MP (SPECL [ouro_fuel_tm; `i:int`] (MP (SPECL [pc; p] oeq_preserves) cert))
              (CONJ fuel_c fuel_p)))) in
  let g = GEN `i:int` (TRANS (CONV_RULE OURO_UNFOLD_CONV eq) (SPEC `i:int` cth)) in
  if ouro_is_gate_thm g then (via, g) else failwith "ouro_rw_route: not the gate theorem";;
(* exercised on the genesis champion every run: a PARTIAL composition
   (x * 0 -> 0 inside, the rest untouched) is certified by
   orw_oeq + congruence + oeq_preserves, and a semantics-breaking edit
   (dropping the summand 3 + 7) gets no theorem *)
let ouro_rw_selftest_of cth =
  let g = ouro_champ_term cth in
  match ouro_dest_app g with
    Some (op, l, r) ->
      let partial = ouro_app op l (ouro_lit (Int 0)) in
      let bad = (match ouro_dest_app l with Some (op2, l1, l2) -> ouro_app op l1 r | None -> g) in
      (try (match ouro_rw_route cth partial with (via, th) -> via = ouro_via_cong)
       with Failure _ -> false) &&
      (try (match ouro_rw_route cth bad with (via, th) -> false) with Failure _ -> true)
  | None -> false;;
(* the two routes: the rewriter theorem first, else the per-candidate gate *)
let ouro_route_rw = "rewriter theorem";;
let ouro_route_gate = "per-candidate proof";;
let ouro_certify cth t =
  match (try Some (ouro_rw_route cth t) with Failure _ -> None) with
    Some (via, th) -> Some (th, ouro_route_rw, via)
  | None ->
      (match ouro_gate_memo t with
         Some th -> Some (th, ouro_route_gate, "eval_n symbolic execution")
       | None -> None);;

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
  " | compiler_cell gen " ^ soi !ouro_compiler_cell_gen ^ " (" ^ fst ((!ouro_cmap) !ouro_compiler_cell_gen) ^ ")" ^
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
let ouro_found_route = ref ouro_route_gate;;
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
let rec ouro_search_loop cth c0 pool budget =
  if budget = 0 then () else
  match ouro_pick c0 None pool with
    None -> ()
  | Some (l, t) ->
      let ln = ouro_line c0 (l, t) in
      (match ouro_certify cth t with
         Some (th, route, via) ->
           (ouro_note l 1 0;
            ouro_genlog := ln ("PROVED by the kernel via the " ^ route ^ " (" ^ via ^ ")") :: !ouro_genlog;
            ouro_found := Some (l, t, th);
            ouro_found_route := route)
       | None ->
           (ouro_note l 0 1;
            ouro_genrej := ln "REFUSED by the kernel" :: !ouro_genrej;
            ouro_refusals := ln "REFUSED by the kernel" :: !ouro_refusals;
            ouro_genlog := ln "REFUSED by the kernel" :: !ouro_genlog;
            ouro_search_loop cth c0 pool (budget - 1)));;
(* One step of candidate generation: invoke active_pass (!ouro_compiler_cell)
   alongside the current improver's expansion pool. *)
let ouro_step imp champ =
  let pass_t = active_pass champ in
  let pool = (try imp champ with Failure _ -> []) in
  if aconv pass_t champ || exists (fun (_, t) -> aconv t pass_t) pool then pool
  else (["fold"], pass_t) :: pool;;
(* cth: the champion's certificate (the rewriter route builds on it) *)
let ouro_search imp cth =
  ouro_found := None; ouro_genlog := []; ouro_genrej := [];
  let champ = ouro_champ_term cth in
  let c0 = osize champ in
  let all = ouro_step imp champ in
  let pool = filter (fun (l, t) -> osize t < c0) all in
  ouro_discarded := !ouro_discarded + (length all - length pool);
  ouro_search_loop cth c0 pool ouro_budget;
  ("improver emitted " ^ soi (length all) ^ ", cheaper than " ^ soi c0 ^ ": " ^
   soi (length pool)) :: rev !ouro_genlog;;
let ouro_last_rejections () = rev !ouro_genrej;;
let ouro_found_thm () =
  match !ouro_found with Some (l, t, th) -> th | None -> failwith "ouro: nothing found";;
let ouro_found_ops () =
  match !ouro_found with Some (l, t, th) -> l | None -> [];;
let ouro_found_route_str () =
  match !ouro_found with Some _ -> !ouro_found_route | None -> failwith "ouro: nothing found";;

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
let ouro_improver_gate inv_ok imp cth =
  ouro_imp_passed := false;
  if not inv_ok then (ouro_imp_reason := "the fragment invariant failed"; ["invariant FAILED"]) else
  let lg = ouro_search imp cth in
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
let ouro_cval_selftest =
  let cv_gen = ouro_to_cval ouro_genesis in
  let cv_neg = ouro_to_cval (ouro_lit (Int (0 - 3))) in
  let th_raw = Kernel.compute (COMPUTE_INIT_THMS, ouro_cval_eqs)
                 (mk_comb (`cval_nodes`, cv_gen)) in
  let th_nodes = ouro_kernel_compute (mk_comb (`cval_nodes`, cv_gen)) in
  let th_neg_nodes = ouro_kernel_compute (mk_comb (`cval_nodes`, cv_neg)) in
  let th_fuel  = ouro_kernel_compute (mk_comb (`cval_fuel`, cv_gen)) in
  let th_eval7 = ouro_kernel_compute
                   (mk_comb (mk_comb (`cval_eval`, cv_gen), `Cexp_num 7`)) in
  hyp th_raw = [] && concl th_raw = concl th_nodes &&
  hyp th_nodes = [] && aconv (rand (concl th_nodes)) `Cexp_num 19` &&
  hyp th_neg_nodes = [] && aconv (rand (concl th_neg_nodes)) `Cexp_num 1` &&
  hyp th_fuel = [] && aconv (rand (concl th_fuel)) `Cexp_num 15` &&
  hyp th_eval7 = [] && aconv (rand (concl th_eval7)) `Cexp_num 52` &&
  ouro_cval_check ouro_genesis;;

let ouro_compiler_cell_selftest =
  let bad_refl = REFL `ouro_e:exp` in
  let r_bad = ouro_install_compiler_pass "bad" `I:exp->exp` bad_refl (fun _ -> ouro_x) in
  let g0 = !ouro_compiler_cell_gen in
  let r_orw = ouro_init_cell_orw () in
  let g1 = !ouro_compiler_cell_gen in
  let orw_gen = active_pass ouro_genesis in
  let folded_tm = ouro_exec_fold ouro_genesis in
  let pad_tm = ouro_app ouro_add folded_tm (ouro_lit (Int 0)) in
  let pad_th = ouro_the (ouro_gate pad_tm) in
  let orw_pad = active_pass pad_tm in
  let (via_orw, th_orw) = ouro_rw_route pad_th orw_pad in
  let r_fold = ouro_upgrade_cell_to_fold () in
  let g2 = !ouro_compiler_cell_gen in
  let folded_gen = active_pass ouro_genesis in
  let gen0_th = ouro_the (ouro_gate ouro_genesis) in
  let (via_fold, th_fold) = ouro_rw_route gen0_th folded_gen in
  let step_pool = ouro_step (fun _ -> []) ouro_genesis in
  let (nm1, fn1) = (!ouro_cmap) 1 in
  let (nm2, fn2) = (!ouro_cmap) 2 in
  not r_bad && g0 = 0 && r_orw && g1 = 1 && osize orw_gen = 19 && osize orw_pad = 13 &&
  via_orw = "orw_exp_preserves" && ouro_is_gate_thm th_orw &&
  r_fold && g2 = 2 && osize folded_gen = 13 &&
  via_fold = "ofold_preserves" && ouro_is_gate_thm th_fold &&
  length step_pool = 1 && osize (snd (hd step_pool)) = 13 &&
  nm1 = "orw_exp" && osize (fn1 ouro_genesis) = 19 &&
  nm2 = "ofold" && osize (fn2 ouro_genesis) = 13;;

let rec ouro_decreasing l =
  match l with a :: b :: r -> b < a && ouro_decreasing (b :: r) | _ -> true;;
let ouro_verdict_of costs natives final_ok routes rw_selftest =
  let n = length costs - 1 in
  let k = length !ouro_refusals in
  let r = length (filter (fun s -> s = ouro_route_rw) routes) in
  let rws = soi r ^ " via the rewriter theorem" in
  if n >= 3 && ouro_decreasing costs && forall (fun b -> b) natives && final_ok &&
     k >= 1 && !ouro_upgrades >= 1 && ouro_inv_selftest && r >= 1 && rw_selftest &&
     ouro_cval_selftest && ouro_compiler_cell_selftest &&
     length routes = length costs
  then "OUROBOROS_OK: " ^ soi n ^ " generations, cost " ^ soi (hd costs) ^ " -> " ^
       soi (last costs) ^ ", " ^ soi k ^ " rejections, improver upgraded, " ^ rws
  else "OUROBOROS_PARTIAL: " ^ soi n ^ " generations, " ^ soi k ^ " rejections, " ^
       soi !ouro_upgrades ^ " improver upgrades, " ^ rws;;

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
    "let " ^ ouro_g n ^ "_cval_ok = ouro_cval_check (ouro_champ_term " ^ ouro_g n ^ "_thm);;";
    "let " ^ ouro_g n ^ "_cell_ast = active_pass (ouro_champ_term " ^ ouro_g n ^ "_thm);;";
    "let " ^ ouro_g n ^ "_cell_cost = osize " ^ ouro_g n ^ "_cell_ast;;";
    "let ouro_champion_" ^ soi n ^ " = (fun x -> " ^ src ^ ");;";
    "let " ^ ouro_g n ^ "_native_out = map ouro_champion_" ^ soi n ^ " ouro_inputs;;";
    "let " ^ ouro_g n ^ "_native_ok = " ^ ouro_g n ^ "_gate_ok && " ^ ouro_g n ^ "_cval_ok && " ^
      ouro_g n ^ "_cell_cost <= " ^ ouro_g n ^ "_cost && " ^
      ouro_g n ^ "_native_out = map ouro_spec ouro_inputs && " ^
      ouro_g n ^ "_cand_src = " ^ ouro_quote src ^ ";;";
    "let () = ouro_record " ^ soi n ^ " " ^ ouro_g n ^ "_thm;;";
    "let " ^ ouro_g n ^ "_model = ouro_model_str " ^ soi n ^ ";;" ];;
let ouro_batch_start () =
  "let ouro_compiler_cell_init = ouro_init_cell_orw ();;" ::
  ("let ouro_improver_1 = " ^ ouro_improver_src ouro_all_ops 1 ^ ";;") ::
  "let ouro_gen_0_thm = ouro_the (ouro_gate ouro_genesis);;" ::
  "let ouro_gen_0_route = ouro_route_gate;;" ::
  "let ouro_rw_selftest = ouro_rw_selftest_of ouro_gen_0_thm;;" ::
  ouro_batch_install 0 (osrc ouro_genesis);;
let ouro_parent n = "(ouro_champ_term " ^ ouro_g (n - 1) ^ "_thm)";;
let ouro_parent_thm n = ouro_g (n - 1) ^ "_thm";;
let ouro_batch_search n =
  (if n = 2 then ["let ouro_compiler_cell_upgraded = ouro_upgrade_cell_to_fold ();;"] else []) @
  [ "let " ^ ouro_g n ^ "_parent_src = osrc " ^ ouro_parent n ^ ";;";
    "let " ^ ouro_g n ^ "_search = ouro_search ouro_improver_" ^ soi !ouro_imp_ver ^ " " ^ ouro_parent_thm n ^ ";;";
    "let " ^ ouro_g n ^ "_rejections = ouro_last_rejections ();;" ];;
let ouro_batch_accept n =
  match !ouro_found with
    Some (l, t, th) ->
      ("let " ^ ouro_g n ^ "_thm = ouro_found_thm ();;") ::
      ("let " ^ ouro_g n ^ "_ops = ouro_found_ops ();;") ::
      ("let " ^ ouro_g n ^ "_route = ouro_found_route_str ();;") ::
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
    "let " ^ iv ^ "_gate = ouro_improver_gate " ^ iv ^ "_inv_ok ouro_improver_cand_" ^ soi v ^ " " ^ ouro_parent_thm n ^ ";;";
    "let " ^ iv ^ "_gate_ok = ouro_improver_gate_passed ();;" ];;
let ouro_batch_finish () =
  let acc = rev !ouro_accepted in
  let k = hd !ouro_accepted in
  [ "let ouro_costs = [" ^ ouro_join "; " (map (fun n -> ouro_g n ^ "_cost") acc) ^ "];;";
    "let ouro_natives_ok = [" ^ ouro_join "; " (map (fun n -> ouro_g n ^ "_native_ok") acc) ^ "];;";
    "let ouro_routes = [" ^ ouro_join "; " (map (fun n -> ouro_g n ^ "_route") acc) ^ "];;";
    "let ouro_final_src = " ^ ouro_g k ^ "_cand_src;;";
    "let ouro_final_native_out = map ouro_champion_" ^ soi k ^ " ouro_inputs;;";
    "let ouro_model_final = ouro_model_str " ^ soi k ^ ";;";
    "let ouro_verdict = ouro_verdict_of ouro_costs ouro_natives_ok " ^
      "(ouro_final_native_out = map ouro_spec ouro_inputs) ouro_routes ouro_rw_selftest;;" ];;
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
let ouro_loop = ouro_hook;;
let () = Repl.readNextString := ouro_loop;;
