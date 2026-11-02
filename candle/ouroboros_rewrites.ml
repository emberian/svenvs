(* STATUS: GREEN on the live Candle kernel (scripts/reflectsem-live.sh
   --ouroboros): all theorems below are proved hypothesis-free and echoed,
   among them ofold_preserves, ofold_frag, ofold_cost, orw_oeq,
   odouble_preserves, ocollect1_preserves, ocollect2_preserves,
   oreassoc_preserves, OEQ_DOUBLE, OEQ_COLLECT1, OEQ_COLLECT2, OEQ_REASSOC,
   OEQ_OFOLD, OEQ_ADD, OEQ_SUB, OEQ_MUL, OEQ_TRANS, oeq_preserves,
   ofrag_oemb, EVAL_N_LET, EVAL_N_IF, OLET_NIL_EVAL, OIF_TRUE_EVAL, and
   OIF_FALSE_EVAL. Every improver rewrite rule (fold, dead, double, collect,
   reassoc) is proved as a general kernel theorem over oexp and lifted via
   oeq_preserves to the real CakeML eval_n semantics. *)
(* ===================================================================== *)
(*  svenvs OUROBOROS — the improver's rewrites as KERNEL THEOREMS.        *)
(*                                                                        *)
(*  Proved once in the live Candle kernel, against the exported real      *)
(*  CakeML semantics (eval_n), for every term of the fragment:            *)
(*    ofold_preserves  the constant-folding / dead-subterm rewriter keeps *)
(*                     the eval_n result, at any fuel >= efuel e;         *)
(*    ofold_frag       its output stays in the fragment;                  *)
(*    ofold_cost       its output is no larger;                           *)
(*    orw_oeq, OEQ_DOUBLE, OEQ_COLLECT1, OEQ_COLLECT2, OEQ_REASSOC,       *)
(*    OEQ_OFOLD, oeq_preserves (with the congruences OEQ_ADD, OEQ_SUB,    *)
(*    OEQ_MUL and OEQ_TRANS)                                              *)
(*                     every improver rewrite (fold, dead, double,        *)
(*                     collect, reassoc), lifted to any position and any  *)
(*                     composition;                                       *)
(*    EVAL_N_LET, EVAL_N_IF, OLET_NIL_EVAL, OIF_TRUE_EVAL, OIF_FALSE_EVAL *)
(*                     binding (Let NONE) and control-flow (If) theorems  *)
(*                     on the real eval_n.                                *)
(*  candle/ouroboros.ml then installs every generation's candidate by     *)
(*  SPEC/MP from these theorems instead of symbolic execution per         *)
(*  candidate.                                                            *)
(*                                                                        *)
(*  Representation (the stated boundary): the rewrites are HOL theorems   *)
(*  over an auxiliary binary type oexp (x, int literals, plus, minus,     *)
(*  times), not over the nested ast$exp directly; oemb embeds it into     *)
(*  the real exp, and                                                     *)
(*  ofrag_oemb proves that the image of oemb is EXACTLY ofrag, an         *)
(*  inductive predicate on the real exp. On exp, ofold e =                *)
(*  oemb (ofoldo (oof e)) with oof the (proved) inverse of oemb.          *)
(*                                                                        *)
(*  Load AFTER reflectsem_datatypes.ml + reflectsem_functions.ml and      *)
(*  BEFORE ouroboros.ml, once per server (define_type).                   *)
(* ===================================================================== *)

(* ---------------- the weak call-by-value normaliser ---------------- *)
(* (the gate's normaliser; ouroboros.ml uses it from here)
   WEAK call-by-value normalisation with the exported rewrite base.
   Plain REWRITE_CONV rewrites everywhere, including inside the unapplied
   continuation lambdas of eval_n's case constants and ahead of their
   scrutinees (pair_CASE p f = f (FST p) (SND p) copies an UNevaluated p),
   which is exponential in the nesting depth of the evaluated program: it
   was fine for the smoke gates' closed one-App terms and ran away on a
   depth-7 symbolic one. Here: never rewrite under a lambda; for a case
   constant or COND evaluate only the scrutinee, then fire the clause;
   everything else is evaluated arguments-first. *)
let ouro_try f x = try f x with Failure _ -> [];;
let ouro_ctor_thms =
  itlist (fun n acc -> ouro_try (fun n -> [distinctness n]) n @
                       ouro_try (fun n -> [injectivity n]) n @ acc)
         ("char" :: "option" :: "list" :: reflectsem_dt_names) [];;
let OURO_EXISTS_REFL2 = prove (`!a:A. ?x. a = x`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;
let ouro_defs =
  reflectsem_dt_thms @ reflectsem_fn_thms @ ouro_ctor_thms @
  [FST; SND; OUTL; OUTR; ALL; MAP; REVERSE; APPEND; LENGTH; HD; TL;
   NOT_SUC; PRE; LET_DEF; LET_END_DEF; EXISTS_REFL; OURO_EXISTS_REFL2;
   PAIR_EQ; CONS_11; NOT_CONS_NIL; injectivity "sum"];;
let ouro_net_of ths base =
  itlist (net_of_thm false) (itlist (mk_rewrites false) ths []) base;;
let ouro_net = ouro_net_of (ouro_defs @ basic_rewrites ()) empty_net;;
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
let ouro_top_of net =
  FIRST_CONV [REWRITES_CONV net; GEN_BETA_CONV;
              OURO_NUM_CONV; INT_RED_CONV; OURO_EX_CONV];;
let OURO_TOP_CONV = ouro_top_of ouro_net;;
let ouro_is_lazy h =
  is_const h &&
  (let n = fst (dest_const h) in
   n = "COND" ||
   (String.length n > 5 &&
    String.sub n (String.length n - 5) 5 = "_CASE"));;
(* the normaliser, parametric in its top-level step (so a proof can add
   its own hypotheses, e.g. induction hypotheses, as rewrites) *)
let rec ouro_weak top tm =
  if is_abs tm then REFL tm else
  if not (is_comb tm) then
    (* constants with a defining equation (nsEmpty, list_type_num, ...) *)
    (match (try Some (top tm) with Failure _ -> None) with
       None -> REFL tm
     | Some th -> if aconv (rand (concl th)) tm then REFL tm
                  else TRANS th (ouro_weak top (rand (concl th))))
  else
  let (h, args) = strip_comb tm in
  let th1 =
    if ouro_is_lazy h then
      funpow (length args - 1) RATOR_CONV (RAND_CONV (ouro_weak top)) tm
    else
      let (f, x) = dest_comb tm in MK_COMB (ouro_weak top f, ouro_weak top x) in
  let tm1 = rand (concl th1) in
  match (try Some (top tm1) with Failure _ -> None) with
    None -> th1
  | Some th2 ->
      (* a conversion that "succeeds" without changing the term (e.g. an
         arithmetic conv on a literal) is no progress: stop, don't loop *)
      if aconv (rand (concl th2)) tm1 then th1
      else TRANS th1 (TRANS th2 (ouro_weak top (rand (concl th2))));;
let OURO_WEAK_CONV tm = ouro_weak OURO_TOP_CONV tm;;

(* ---------------- the fixed evaluation context ---------------- *)
(* the gate's state and environment (x bound to the int i), as constants
   so the theorems read; unfolded they are literally the gate's terms *)
let ost0_def = new_definition
  `ost0 = state 0 [] (ffi_state (\nm. \s. \conf. \bytes. Oracle_final FFI_failed) one []) 0 0 NONE`;;
let oenv_def = new_definition
  `oenv i = sem_env (nsBind (implode "x") (Litv (IntLit i)) nsEmpty) nsEmpty`;;
let OURO_UNFOLD_CONV = REWRITE_CONV [ost0_def; oenv_def];;

(* ---------------- the real semantics on the fragment's shapes --------- *)
let OURO_FIN_TAC = REWRITE_TAC ouro_defs THEN TRY INT_ARITH_TAC;;
let ouro_base_prove g =
  prove (g, REPEAT GEN_TAC THEN
            CONV_TAC (OURO_UNFOLD_CONV THENC LAND_CONV OURO_WEAK_CONV) THEN
            OURO_FIN_TAC);;
(* a step lemma: the antecedents (the subterms' evaluations, symbolic
   subterms a b) join the rewrite net, normalised like everything else *)
let ouro_step_prove g =
  prove (g, REPEAT GEN_TAC THEN DISCH_THEN (fun hth ->
    let hs = map (fun h -> CONV_RULE (LAND_CONV OURO_WEAK_CONV)
                             (CONV_RULE OURO_UNFOLD_CONV h)) (CONJUNCTS hth) in
    let top = ouro_top_of (ouro_net_of hs ouro_net) in
    CONV_TAC (OURO_UNFOLD_CONV THENC LAND_CONV (ouro_weak top)) THEN
    OURO_FIN_TAC));;

let EVAL_VAR = ouro_base_prove
  `!f i. eval_n (SUC f) (INL (ost0, oenv i, [Var (Short (implode "x"))])) =
         INL (ost0, Rval [Litv (IntLit i)])`;;
let EVAL_LIT = ouro_base_prove
  `!f i n. eval_n (SUC f) (INL (ost0, oenv i, [Lit (IntLit n)])) =
           INL (ost0, Rval [Litv (IntLit n)])`;;
let EVAL_ADD = ouro_step_prove
  `!f i a b m n.
     eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit m)]) /\
     eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC (SUC f)) (INL (ost0, oenv i, [App (Arith Add IntT) [a; b]])) =
         INL (ost0, Rval [Litv (IntLit (m + n))])`;;
let EVAL_SUB = ouro_step_prove
  `!f i a b m n.
     eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit m)]) /\
     eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC (SUC f)) (INL (ost0, oenv i, [App (Arith Sub IntT) [a; b]])) =
         INL (ost0, Rval [Litv (IntLit (m - n))])`;;
let EVAL_MUL = ouro_step_prove
  `!f i a b m n.
     eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit m)]) /\
     eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC (SUC f)) (INL (ost0, oenv i, [App (Arith Mul IntT) [a; b]])) =
         INL (ost0, Rval [Litv (IntLit (m * n))])`;;

(* CakeML binding (Let NONE) and control-flow (If) evaluation theorems *)
let EVAL_LET = ouro_step_prove
  `!f i a b m n.
     eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit m)]) /\
     eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC f) (INL (ost0, oenv i, [Let NONE a b])) =
         INL (ost0, Rval [Litv (IntLit n)])`;;
let EVAL_IF_TRUE = ouro_step_prove
  `!f i c a b n.
     eval_n f (INL (ost0, oenv i, [c])) = INL (ost0, Rval [Boolv T]) /\
     eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC f) (INL (ost0, oenv i, [If c a b])) =
         INL (ost0, Rval [Litv (IntLit n)])`;;
let EVAL_IF_FALSE = ouro_step_prove
  `!f i c a b n.
     eval_n f (INL (ost0, oenv i, [c])) = INL (ost0, Rval [Boolv F]) /\
     eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
     ==> eval_n (SUC f) (INL (ost0, oenv i, [If c a b])) =
         INL (ost0, Rval [Litv (IntLit n)])`;;
let EVAL_IF = prove
  (`!f i c a b flag m n.
      eval_n f (INL (ost0, oenv i, [c])) = INL (ost0, Rval [Boolv flag]) /\
      eval_n f (INL (ost0, oenv i, [a])) = INL (ost0, Rval [Litv (IntLit m)]) /\
      eval_n f (INL (ost0, oenv i, [b])) = INL (ost0, Rval [Litv (IntLit n)])
      ==> eval_n (SUC f) (INL (ost0, oenv i, [If c a b])) =
          INL (ost0, Rval [Litv (IntLit (if flag then m else n))])`,
   REPEAT GEN_TAC THEN BOOL_CASES_TAC `flag:bool` THEN
   REWRITE_TAC [] THEN STRIP_TAC THENL
   [MATCH_MP_TAC EVAL_IF_TRUE THEN ASM_REWRITE_TAC [];
    MATCH_MP_TAC EVAL_IF_FALSE THEN ASM_REWRITE_TAC []]);;

let EVAL_N_VAR_X = EVAL_VAR;;
let EVAL_N_LIT = EVAL_LIT;;
let EVAL_N_ADD = EVAL_ADD;;
let EVAL_N_SUB = EVAL_SUB;;
let EVAL_N_MUL = EVAL_MUL;;
let EVAL_N_LET = EVAL_LET;;
let EVAL_N_IF_TRUE = EVAL_IF_TRUE;;
let EVAL_N_IF_FALSE = EVAL_IF_FALSE;;
let EVAL_N_IF = EVAL_IF;;

(* ---------------- the fragment: a binary type and its embedding -------- *)
let oexp_DT = define_type "oexp = OX | OLit int | OAdd oexp oexp | OSub oexp oexp | OMul oexp oexp";;
let oexp_INDUCT = fst oexp_DT;;
let oexp_CASES = cases "oexp";;
(* distinctness in BOTH orientations (HOL Light states one) *)
let ouro_ctor2 n =
  (try let th = distinctness n in [th; GSYM th] with Failure _ -> []) @
  (try [injectivity n] with Failure _ -> []);;
let oexp_ctor_thms = ouro_ctor2 "oexp";;
let ouro_exp_ctor_thms =
  flat (map ouro_ctor2 ["exp"; "id"; "lit"; "op"; "arith"; "prim_type"; "mlstring"]);;

let oemb_def = define
  `(oemb OX = Var (Short (implode "x"))) /\
   (oemb (OLit n) = Lit (IntLit n)) /\
   (oemb (OAdd a b) = App (Arith Add IntT) [oemb a; oemb b]) /\
   (oemb (OSub a b) = App (Arith Sub IntT) [oemb a; oemb b]) /\
   (oemb (OMul a b) = App (Arith Mul IntT) [oemb a; oemb b])`;;
(* the denotation, the fuel bound (depth), the static cost (AST size) *)
let osem_def = define
  `(osem OX i = i) /\ (osem (OLit n) i = n) /\
   (osem (OAdd a b) i = osem a i + osem b i) /\
   (osem (OSub a b) i = osem a i - osem b i) /\
   (osem (OMul a b) i = osem a i * osem b i)`;;
let oembed_def = oemb_def;;
let odenote_def = osem_def;;
let ofuel_def = define
  `(ofuel OX = 1) /\ (ofuel (OLit n) = 1) /\
   (ofuel (OAdd a b) = MAX (ofuel a) (ofuel b) + 2) /\
   (ofuel (OSub a b) = MAX (ofuel a) (ofuel b) + 2) /\
   (ofuel (OMul a b) = MAX (ofuel a) (ofuel b) + 2)`;;
let onodes_def = define
  `(onodes OX = 1) /\ (onodes (OLit n) = 1) /\
   (onodes (OAdd a b) = 1 + onodes a + onodes b) /\
   (onodes (OSub a b) = 1 + onodes a + onodes b) /\
   (onodes (OMul a b) = 1 + onodes a + onodes b)`;;

(* the fragment, as an inductive predicate on the REAL exp *)
let ofrag_ind = new_inductive_definition
  `ofrag (Var (Short (implode "x"))) /\
   (!n. ofrag (Lit (IntLit n))) /\
   (!a b. ofrag a /\ ofrag b ==> ofrag (App (Arith Add IntT) [a; b])) /\
   (!a b. ofrag a /\ ofrag b ==> ofrag (App (Arith Sub IntT) [a; b])) /\
   (!a b. ofrag a /\ ofrag b ==> ofrag (App (Arith Mul IntT) [a; b]))`;;
let ofrag_RULES = (match ofrag_ind with (r, i, c) -> r);;
let ofrag_INDUCT = (match ofrag_ind with (r, i, c) -> i);;

let OFRAG_OEMB1 = prove (`!p. ofrag (oemb p)`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [oemb_def] THEN
  MESON_TAC [ofrag_RULES]);;
let OFRAG_OEMB2 = prove (`!e. ofrag e ==> ?p. e = oemb p`,
  MATCH_MP_TAC ofrag_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MESON_TAC [oemb_def]);;
let ofrag_oemb = prove (`!e. ofrag e <=> ?p. e = oemb p`,
  MESON_TAC [OFRAG_OEMB1; OFRAG_OEMB2]);;

let OEMB_11 = prove (`!p q. oemb p = oemb q <=> p = q`,
  MATCH_MP_TAC oexp_INDUCT THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC (SPEC `q:oexp` oexp_CASES) THEN
  ASM_REWRITE_TAC ([oemb_def; CONS_11] @ ouro_exp_ctor_thms @ oexp_ctor_thms));;

(* ---------------- the core: the real eval_n computes osem ---------------- *)
let OURO_LE1 = prove (`!k. 1 <= k ==> ?f. k = SUC f`,
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `k - 1` THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;
let OURO_LE2 = prove
  (`!a b k. MAX a b + 2 <= k ==> ?f. k = SUC (SUC f) /\ a <= f /\ b <= f`,
  REPEAT GEN_TAC THEN REWRITE_TAC [MAX] THEN COND_CASES_TAC THEN
  DISCH_TAC THEN EXISTS_TAC `k - 2` THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let ouro_base_tac step =
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> X_CHOOSE_THEN `f:num` SUBST1_TAC (MATCH_MP OURO_LE1 th)) THEN
  REWRITE_TAC [step];;
let ouro_bin_tac step =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> X_CHOOSE_THEN `f:num`
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) (MATCH_MP OURO_LE2 th)) THEN
  MATCH_MP_TAC step THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];;

let OEVAL = prove
  (`!p k i. ofuel p <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb p])) = INL (ost0, Rval [Litv (IntLit (osem p i))])`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [ofuel_def; oemb_def; osem_def] THEN
  REPEAT CONJ_TAC THENL
   [ouro_base_tac EVAL_VAR; ouro_base_tac EVAL_LIT;
    ouro_bin_tac EVAL_ADD; ouro_bin_tac EVAL_SUB; ouro_bin_tac EVAL_MUL]);;

(* Let NONE and If evaluation over embedded fragment expressions *)
let OLET_NIL_EVAL = prove
  (`!a b k i. ofuel a <= k /\ ofuel b <= k ==>
       eval_n (SUC k) (INL (ost0, oenv i, [Let NONE (oemb a) (oemb b)])) =
       eval_n k (INL (ost0, oenv i, [oemb b]))`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`a:oexp`; `k:num`; `i:int`] OEVAL) THEN
   MP_TAC (SPECL [`b:oexp`; `k:num`; `i:int`] OEVAL) THEN
   ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EVAL_LET THEN EXISTS_TAC `osem a i` THEN ASM_REWRITE_TAC []);;

let OIF_TRUE_EVAL = prove
  (`!c a b k i.
       eval_n k (INL (ost0, oenv i, [c])) = INL (ost0, Rval [Boolv T]) /\
       ofuel a <= k
       ==> eval_n (SUC k) (INL (ost0, oenv i, [If c (oemb a) (oemb b)])) =
           eval_n k (INL (ost0, oenv i, [oemb a]))`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`a:oexp`; `k:num`; `i:int`] OEVAL) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EVAL_IF_TRUE THEN ASM_REWRITE_TAC []);;

let OIF_FALSE_EVAL = prove
  (`!c a b k i.
       eval_n k (INL (ost0, oenv i, [c])) = INL (ost0, Rval [Boolv F]) /\
       ofuel b <= k
       ==> eval_n (SUC k) (INL (ost0, oenv i, [If c (oemb a) (oemb b)])) =
           eval_n k (INL (ost0, oenv i, [oemb b]))`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`b:oexp`; `k:num`; `i:int`] OEVAL) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EVAL_IF_FALSE THEN ASM_REWRITE_TAC []);;

(* ---------------- the rewrites: fold + dead + algebraic rules ----------- *)
let oislit_def = define
  `(oislit OX = F) /\ (oislit (OLit n) = T) /\ (oislit (OAdd a b) = F) /\
   (oislit (OSub a b) = F) /\ (oislit (OMul a b) = F)`;;
let olv_def = define `olv (OLit n) = n`;;
let oadd_def = new_definition
  `oadd a b = if oislit a /\ oislit b then OLit (olv a + olv b)
              else if b = OLit (&0) then a
              else if a = OLit (&0) then b
              else OAdd a b`;;
let osub_def = new_definition
  `osub a b = if oislit a /\ oislit b then OLit (olv a - olv b)
              else if b = OLit (&0) then a
              else OSub a b`;;
let omul_def = new_definition
  `omul a b = if oislit a /\ oislit b then OLit (olv a * olv b)
              else if a = OLit (&0) then OLit (&0)
              else if b = OLit (&0) then OLit (&0)
              else if b = OLit (&1) then a
              else if a = OLit (&1) then b
              else OMul a b`;;
(* one rewrite at the root *)
let orw_def = define
  `(orw OX = OX) /\ (orw (OLit n) = OLit n) /\
   (orw (OAdd a b) = oadd a b) /\ (orw (OSub a b) = osub a b) /\
   (orw (OMul a b) = omul a b)`;;
(* the full bottom-up rewriter *)
let ofoldo_def = define
  `(ofoldo OX = OX) /\ (ofoldo (OLit n) = OLit n) /\
   (ofoldo (OAdd a b) = oadd (ofoldo a) (ofoldo b)) /\
   (ofoldo (OSub a b) = osub (ofoldo a) (ofoldo b)) /\
   (ofoldo (OMul a b) = omul (ofoldo a) (ofoldo b))`;;

(* size/fuel-shrinking refinement (for ofoldo) and semantic equivalence (oeq) *)
let orefines_def = new_definition
  `orefines p q <=> (!i. osem p i = osem q i) /\ ofuel p <= ofuel q /\ onodes p <= onodes q`;;
let oeq_def = new_definition
  `oeq p q <=> (!i. osem p i = osem q i)`;;

let OISLIT_SEM = prove (`!p i. oislit p ==> osem p i = olv p`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [oislit_def; osem_def; olv_def]);;
let OREFINES_REFL = prove (`!p. orefines p p`, REWRITE_TAC [orefines_def; LE_REFL]);;
let OREFINES_TRANS = prove (`!p q r. orefines p q /\ orefines q r ==> orefines p r`,
  REWRITE_TAC [orefines_def] THEN MESON_TAC [LE_TRANS]);;
let OREFINES_OEQ = prove (`!p q. orefines p q ==> oeq p q`,
  REWRITE_TAC [orefines_def; oeq_def] THEN SIMP_TAC []);;
let OURO_OREF_FIN_TAC =
  REWRITE_TAC [orefines_def; osem_def; ofuel_def; onodes_def] THEN
  ASM_SIMP_TAC [OISLIT_SEM] THEN REPEAT CONJ_TAC THEN
  FIRST [GEN_TAC THEN INT_ARITH_TAC; INT_ARITH_TAC;
         REWRITE_TAC [MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC];;
let ouro_op_oref g =
  prove (g, REPEAT GEN_TAC THEN REWRITE_TAC [oadd_def; osub_def; omul_def] THEN
            REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN OURO_OREF_FIN_TAC);;
let OADD_OREFINES = ouro_op_oref `!a b. orefines (oadd a b) (OAdd a b)`;;
let OSUB_OREFINES = ouro_op_oref `!a b. orefines (osub a b) (OSub a b)`;;
let OMUL_OREFINES = ouro_op_oref `!a b. orefines (omul a b) (OMul a b)`;;
let OREFINES_CONG = prove
  (`!a a' b b'. orefines a' a /\ orefines b' b ==>
      orefines (OAdd a' b') (OAdd a b) /\ orefines (OSub a' b') (OSub a b) /\
      orefines (OMul a' b') (OMul a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [orefines_def; osem_def; ofuel_def; onodes_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;
let ouro_rcong k = GEN_ALL (DISCH_ALL (el k (CONJUNCTS (UNDISCH (SPEC_ALL OREFINES_CONG)))));;
let OREFINES_CONG_ADD = ouro_rcong 0;;
let OREFINES_CONG_SUB = ouro_rcong 1;;
let OREFINES_CONG_MUL = ouro_rcong 2;;
let OFOLDO_OREFINES = prove (`!p. orefines (ofoldo p) p`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [ofoldo_def; OREFINES_REFL] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC [OREFINES_TRANS; OADD_OREFINES; OSUB_OREFINES; OMUL_OREFINES;
                 OREFINES_CONG_ADD; OREFINES_CONG_SUB; OREFINES_CONG_MUL]);;

let OEQ_REFL = prove (`!p. oeq p p`, REWRITE_TAC [oeq_def]);;
let OEQ_SYM = prove (`!p q. oeq p q ==> oeq q p`,
  REWRITE_TAC [oeq_def] THEN MESON_TAC []);;
let OEQ_TRANS = prove (`!p q r. oeq p q /\ oeq q r ==> oeq p r`,
  REWRITE_TAC [oeq_def] THEN MESON_TAC []);;

let OADD_OEQ = prove (`!a b. oeq (oadd a b) (OAdd a b)`,
  MESON_TAC [OADD_OREFINES; OREFINES_OEQ]);;
let OSUB_OEQ = prove (`!a b. oeq (osub a b) (OSub a b)`,
  MESON_TAC [OSUB_OREFINES; OREFINES_OEQ]);;
let OMUL_OEQ = prove (`!a b. oeq (omul a b) (OMul a b)`,
  MESON_TAC [OMUL_OREFINES; OREFINES_OEQ]);;

let orw_oeq = prove (`!p. oeq (orw p) p`,
  MATCH_MP_TAC oexp_INDUCT THEN
  REWRITE_TAC [orw_def; OEQ_REFL; OADD_OEQ; OSUB_OEQ; OMUL_OEQ]);;

let OEQ_CONG = prove
  (`!a a' b b'. oeq a' a /\ oeq b' b ==>
      oeq (OAdd a' b') (OAdd a b) /\ oeq (OSub a' b') (OSub a b) /\
      oeq (OMul a' b') (OMul a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [oeq_def; osem_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC []);;
let ouro_cong k = GEN_ALL (DISCH_ALL (el k (CONJUNCTS (UNDISCH (SPEC_ALL OEQ_CONG)))));;
let OEQ_CONG_ADD = ouro_cong 0;;
let OEQ_CONG_SUB = ouro_cong 1;;
let OEQ_CONG_MUL = ouro_cong 2;;
let OEQ_ADD = OEQ_CONG_ADD;;
let OEQ_SUB = OEQ_CONG_SUB;;
let OEQ_MUL = OEQ_CONG_MUL;;

let OFOLDO_OEQ = prove (`!p. oeq (ofoldo p) p`,
  MESON_TAC [OFOLDO_OREFINES; OREFINES_OEQ]);;
let OEQ_OFOLD = OFOLDO_OEQ;;

(* General kernel theorems for algebraic rewrites (double, collect, reassoc) *)
let odouble_preserves = prove
  (`!a i. osem (OMul (OLit (&2)) a) i = osem (OAdd a a) i`,
   REPEAT GEN_TAC THEN REWRITE_TAC [osem_def] THEN INT_ARITH_TAC);;
let ocollect1_preserves = prove
  (`!a x i. osem (OMul (OAdd a (OLit (&1))) x) i = osem (OAdd (OMul a x) x) i`,
   REPEAT GEN_TAC THEN REWRITE_TAC [osem_def; INT_ADD_RDISTRIB] THEN INT_ARITH_TAC);;
let ocollect2_preserves = prove
  (`!a b x i. osem (OMul (OAdd a b) x) i = osem (OAdd (OMul a x) (OMul b x)) i`,
   REPEAT GEN_TAC THEN REWRITE_TAC [osem_def; INT_ADD_RDISTRIB] THEN INT_ARITH_TAC);;
let oreassoc_preserves = prove
  (`!a b c i. osem (OAdd (OAdd a b) c) i = osem (OAdd (OAdd a c) b) i`,
   REPEAT GEN_TAC THEN REWRITE_TAC [osem_def] THEN INT_ARITH_TAC);;
let oreassoc_r_preserves = prove
  (`!a b c i. osem (OAdd a (OAdd b c)) i = osem (OAdd (OAdd a b) c) i`,
   REPEAT GEN_TAC THEN REWRITE_TAC [osem_def] THEN INT_ARITH_TAC);;

let OEQ_DOUBLE = prove
  (`!a. oeq (OMul (OLit (&2)) a) (OAdd a a)`,
   REWRITE_TAC [oeq_def; odouble_preserves]);;
let OEQ_COLLECT1 = prove
  (`!a x. oeq (OMul (OAdd a (OLit (&1))) x) (OAdd (OMul a x) x)`,
   REWRITE_TAC [oeq_def; ocollect1_preserves]);;
let OEQ_COLLECT1_L = prove
  (`!a x. oeq (OMul (OAdd (OLit (&1)) a) x) (OAdd x (OMul a x))`,
   REPEAT GEN_TAC THEN REWRITE_TAC [oeq_def; osem_def; INT_ADD_RDISTRIB] THEN INT_ARITH_TAC);;
let OEQ_COLLECT2 = prove
  (`!a b x. oeq (OMul (OAdd a b) x) (OAdd (OMul a x) (OMul b x))`,
   REWRITE_TAC [oeq_def; ocollect2_preserves]);;
let OEQ_REASSOC = prove
  (`!a b c. oeq (OAdd (OAdd a b) c) (OAdd (OAdd a c) b)`,
   REWRITE_TAC [oeq_def; oreassoc_preserves]);;
let OEQ_REASSOC_R = prove
  (`!a b c. oeq (OAdd a (OAdd b c)) (OAdd (OAdd a b) c)`,
   REWRITE_TAC [oeq_def; oreassoc_r_preserves]);;
let OEQ_REASSOC_L = prove
  (`!a b c. oeq (OAdd (OAdd a b) c) (OAdd a (OAdd b c))`,
   REPEAT GEN_TAC THEN MATCH_MP_TAC OEQ_SYM THEN REWRITE_TAC [OEQ_REASSOC_R]);;

(* ---------------- equivalence is invisible to the real semantics -------- *)
let oeq_preserves = prove
  (`!p q. oeq p q ==> !k i. ofuel p <= k /\ ofuel q <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb p])) = eval_n k (INL (ost0, oenv i, [oemb q]))`,
  REWRITE_TAC [oeq_def] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [OEVAL]);;
let OFOLDO_PRESERVES = prove
  (`!p k i. ofuel p <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb (ofoldo p)])) = eval_n k (INL (ost0, oenv i, [oemb p]))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `p:oexp` OFOLDO_OREFINES) THEN
  REWRITE_TAC [orefines_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ofuel (ofoldo p) <= k` ASSUME_TAC THENL
   [ASM_MESON_TAC [LE_TRANS];
    ASM_MESON_TAC [oeq_preserves; oeq_def]]);;

(* ---------------- the rewriter on the REAL exp ---------------- *)
let oof_def = new_definition `oof e = @p. oemb p = e`;;
let OOF_OEMB = prove (`!p. oof (oemb p) = p`,
  REWRITE_TAC [oof_def; OEMB_11; SELECT_REFL]);;
let orw_exp_def = new_definition `orw_exp e = oemb (orw (oof e))`;;
let ofold_def = new_definition `ofold e = oemb (ofoldo (oof e))`;;
let ocost_def = new_definition `ocost e = onodes (oof e)`;;
let efuel_def = new_definition `efuel e = ofuel (oof e)`;;

let ORW_OREFINES = prove (`!p. orefines (orw p) p`,
  MATCH_MP_TAC oexp_INDUCT THEN
  REWRITE_TAC [orw_def; OREFINES_REFL; OADD_OREFINES; OSUB_OREFINES; OMUL_OREFINES]);;
let ORW_PRESERVES = prove
  (`!p k i. ofuel p <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb (orw p)])) = eval_n k (INL (ost0, oenv i, [oemb p]))`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `p:oexp` ORW_OREFINES) THEN
   REWRITE_TAC [orefines_def] THEN STRIP_TAC THEN
   SUBGOAL_THEN `ofuel (orw p) <= k` ASSUME_TAC THENL
    [ASM_MESON_TAC [LE_TRANS];
     ASM_MESON_TAC [oeq_preserves; oeq_def]]);;
let orw_exp_preserves = prove
  (`!e k i. ofrag e /\ efuel e <= k ==>
       eval_n k (INL (ost0, oenv i, [orw_exp e])) = eval_n k (INL (ost0, oenv i, [e]))`,
  REWRITE_TAC [ofrag_oemb] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [efuel_def; OOF_OEMB]) THEN
  REWRITE_TAC [orw_exp_def; OOF_OEMB] THEN
  MATCH_MP_TAC ORW_PRESERVES THEN ASM_REWRITE_TAC []);;

let ofold_preserves = prove
  (`!e k i. ofrag e /\ efuel e <= k ==>
       eval_n k (INL (ost0, oenv i, [ofold e])) = eval_n k (INL (ost0, oenv i, [e]))`,
  REWRITE_TAC [ofrag_oemb] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [efuel_def; OOF_OEMB]) THEN
  REWRITE_TAC [ofold_def; OOF_OEMB] THEN
  MATCH_MP_TAC OFOLDO_PRESERVES THEN ASM_REWRITE_TAC []);;
let ofold_frag = prove (`!e. ofrag e ==> ofrag (ofold e)`,
  REWRITE_TAC [ofold_def; OFRAG_OEMB1]);;
let ofold_cost = prove (`!e. ofrag e ==> ocost (ofold e) <= ocost e`,
  REWRITE_TAC [ofrag_oemb] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [ofold_def; ocost_def; OOF_OEMB] THEN
  MESON_TAC [OFOLDO_OREFINES; orefines_def]);;

(* ---------------- computing with the rewriter, in the kernel ------------ *)
(* bounded fixpoint of a conversion (fails loudly instead of running away) *)
let rec ouro_fix n conv tm =
  if n = 0 then failwith "ouro_fix: bound exceeded" else
  let th = conv tm in
  let r = rand (concl th) in
  if aconv r tm then th else TRANS th (ouro_fix (n - 1) conv r);;
let ouro_odefs =
  [oadd_def; osub_def; omul_def; oislit_def; olv_def] @ oexp_ctor_thms;;
(* oadd/osub/omul on two VALUES *)
let OURO_OVAL_CONV = ouro_fix 50 (REWRITE_CONV ouro_odefs THENC INT_REDUCE_CONV);;
let ouro_is_oop r =
  let h = fst (strip_comb r) in
  is_const h && mem (fst (dest_const h)) ["oadd"; "osub"; "omul"];;
(* ofoldo p, bottom-up: children first, so nothing is evaluated twice *)
let rec OFOLDO_CONV tm =
  let th = GEN_REWRITE_CONV I [ofoldo_def] tm in
  let r = rand (concl th) in
  if ouro_is_oop r then
    TRANS th ((LAND_CONV OFOLDO_CONV THENC RAND_CONV OFOLDO_CONV THENC OURO_OVAL_CONV) r)
  else th;;
(* orw p: one root step *)
let ORW_CONV = GEN_REWRITE_CONV I [orw_def] THENC OURO_OVAL_CONV;;
(* oemb p -> the real exp *)
let OEMB_CONV = REWRITE_CONV [oemb_def];;
(* ofuel p -> a numeral, bottom-up *)
let rec OFUEL_CONV tm =
  let th = GEN_REWRITE_CONV I [ofuel_def] tm in
  let r = rand (concl th) in
  if is_numeral r then th else
  TRANS th ((LAND_CONV (LAND_CONV OFUEL_CONV THENC RAND_CONV OFUEL_CONV THENC
                        REWR_CONV MAX THENC NUM_REDUCE_CONV THENC REWRITE_CONV [])
             THENC NUM_REDUCE_CONV) r);;

(* ---------------- fast verified compute over :cval (Kernel.compute) ----- *)
(* Encodes oexp into Candle's built-in :cval compute domain:
     OLit (&n)  <-> Cexp_num n
     OX         <-> Cexp_pair (Cexp_num 0) (Cexp_num 0)
     OAdd a b   <-> Cexp_pair (Cexp_num 1) (Cexp_pair a b)
     OSub a b   <-> Cexp_pair (Cexp_num 2) (Cexp_pair a b)
     OMul a b   <-> Cexp_pair (Cexp_num 3) (Cexp_pair a b)
   and proves single-equation compute theorems (cval_nodes_c, cval_fuel_c,
   cval_eval_c, cval_fold_c) plus bridge theorems (CVO_NODES, CVO_FUEL)
   connecting :cval computation to onodes and ofuel. *)

let cval_ctor_thms = ouro_ctor2 "cval";;

let cval_2cases u vn vt vq =
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN vn SUBST_ALL_TAC)
    (X_CHOOSE_THEN vt (X_CHOOSE_THEN vq SUBST_ALL_TAC))
    (SPEC u (cases "cval"));;

let cval_3cases_tac defs =
  REPEAT GEN_TAC THEN
  cval_2cases `p:cval` `n:num` `t:cval` `q:cval` THENL
  [REWRITE_TAC (defs @ [cexp_ispair_def; cexp_if_def; cexp_fst_def; cexp_snd_def]);
   cval_2cases `q:cval` `m:num` `a:cval` `b:cval` THEN
   REWRITE_TAC (defs @ [cexp_ispair_def; cexp_if_def; cexp_fst_def; cexp_snd_def])];;

let cval_INDUCT3_LEMMA = prove
  (`!P. (!n. P (Cexp_num n)) /\
        (!t m. P (Cexp_pair t (Cexp_num m))) /\
        (!t a b. P a /\ P b ==> P (Cexp_pair t (Cexp_pair a b)))
        ==> !q. P q /\ (!a b. q = Cexp_pair a b ==> P a /\ P b)`,
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC cval_ctor_thms;
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
    [cval_2cases `a1:cval` `m:num` `a:cval` `b:cval` THENL
     [ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC];
     REWRITE_TAC cval_ctor_thms THEN REPEAT GEN_TAC THEN
     DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC []]]);;

let cval_INDUCT3 = prove
  (`!P. (!n. P (Cexp_num n)) /\
        (!t m. P (Cexp_pair t (Cexp_num m))) /\
        (!t a b. P a /\ P b ==> P (Cexp_pair t (Cexp_pair a b)))
        ==> !p. P p`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `P:cval->bool` cval_INDUCT3_LEMMA) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th -> REWRITE_TAC [th]));;

let cvo_def = define
  `(cvo (Cexp_num n) = OLit (&n)) /\
   (cvo (Cexp_pair t (Cexp_num m)) = OX) /\
   (cvo (Cexp_pair t (Cexp_pair a b)) =
      if t = Cexp_num 1 then OAdd (cvo a) (cvo b)
      else if t = Cexp_num 2 then OSub (cvo a) (cvo b)
      else OMul (cvo a) (cvo b))`;;

let cval_max_def = new_definition
  `cval_max (a:cval) (b:cval) = Cexp_if (Cexp_less a b) b a`;;

let cval_nodes_def = define
  `(cval_nodes (Cexp_num n) = Cexp_num 1) /\
   (cval_nodes (Cexp_pair t (Cexp_num m)) = Cexp_num 1) /\
   (cval_nodes (Cexp_pair t (Cexp_pair a b)) =
      Cexp_add (Cexp_num 1) (Cexp_add (cval_nodes a) (cval_nodes b)))`;;

let cval_nodes_c = prove
  (`cval_nodes p =
      Cexp_if (Cexp_ispair p)
        (Cexp_if (Cexp_ispair (Cexp_snd p))
          (Cexp_add (Cexp_num 1)
            (Cexp_add (cval_nodes (Cexp_fst (Cexp_snd p)))
                      (cval_nodes (Cexp_snd (Cexp_snd p)))))
          (Cexp_num 1))
        (Cexp_num 1)`,
   cval_3cases_tac [cval_nodes_def]);;

let cval_fuel_def = define
  `(cval_fuel (Cexp_num n) = Cexp_num 1) /\
   (cval_fuel (Cexp_pair t (Cexp_num m)) = Cexp_num 1) /\
   (cval_fuel (Cexp_pair t (Cexp_pair a b)) =
      Cexp_add (cval_max (cval_fuel a) (cval_fuel b)) (Cexp_num 2))`;;

let cval_fuel_c = prove
  (`cval_fuel p =
      Cexp_if (Cexp_ispair p)
        (Cexp_if (Cexp_ispair (Cexp_snd p))
          (Cexp_add (cval_max (cval_fuel (Cexp_fst (Cexp_snd p)))
                              (cval_fuel (Cexp_snd (Cexp_snd p))))
                    (Cexp_num 2))
          (Cexp_num 1))
        (Cexp_num 1)`,
   cval_3cases_tac [cval_fuel_def]);;

let cval_eval_def = define
  `(cval_eval (Cexp_num n) (x:cval) = Cexp_num n) /\
   (cval_eval (Cexp_pair t (Cexp_num m)) x = x) /\
   (cval_eval (Cexp_pair t (Cexp_pair a b)) x =
      Cexp_if (Cexp_eq t (Cexp_num 1))
        (Cexp_add (cval_eval a x) (cval_eval b x))
        (Cexp_if (Cexp_eq t (Cexp_num 2))
          (Cexp_sub (cval_eval a x) (cval_eval b x))
          (Cexp_mul (cval_eval a x) (cval_eval b x))))`;;

let cval_eval_c = prove
  (`cval_eval p x =
      Cexp_if (Cexp_ispair p)
        (Cexp_if (Cexp_ispair (Cexp_snd p))
          (Cexp_if (Cexp_eq (Cexp_fst p) (Cexp_num 1))
            (Cexp_add (cval_eval (Cexp_fst (Cexp_snd p)) x)
                      (cval_eval (Cexp_snd (Cexp_snd p)) x))
            (Cexp_if (Cexp_eq (Cexp_fst p) (Cexp_num 2))
              (Cexp_sub (cval_eval (Cexp_fst (Cexp_snd p)) x)
                        (cval_eval (Cexp_snd (Cexp_snd p)) x))
              (Cexp_mul (cval_eval (Cexp_fst (Cexp_snd p)) x)
                        (cval_eval (Cexp_snd (Cexp_snd p)) x))))
          x)
        p`,
   cval_3cases_tac [cval_eval_def]);;

let cval_oadd_def = new_definition
  `cval_oadd a b =
     Cexp_if (Cexp_ispair a)
       (Cexp_if (Cexp_eq b (Cexp_num 0)) a
         (Cexp_pair (Cexp_num 1) (Cexp_pair a b)))
       (Cexp_if (Cexp_ispair b)
         (Cexp_if (Cexp_eq a (Cexp_num 0)) b
           (Cexp_pair (Cexp_num 1) (Cexp_pair a b)))
         (Cexp_add a b))`;;

let cval_osub_def = new_definition
  `cval_osub a b =
     Cexp_if (Cexp_ispair a)
       (Cexp_if (Cexp_eq b (Cexp_num 0)) a
         (Cexp_pair (Cexp_num 2) (Cexp_pair a b)))
       (Cexp_if (Cexp_ispair b)
         (Cexp_pair (Cexp_num 2) (Cexp_pair a b))
         (Cexp_sub a b))`;;

let cval_omul_def = new_definition
  `cval_omul a b =
     Cexp_if (Cexp_ispair a)
       (Cexp_if (Cexp_eq b (Cexp_num 0)) (Cexp_num 0)
         (Cexp_if (Cexp_eq b (Cexp_num 1)) a
           (Cexp_pair (Cexp_num 3) (Cexp_pair a b))))
       (Cexp_if (Cexp_ispair b)
         (Cexp_if (Cexp_eq a (Cexp_num 0)) (Cexp_num 0)
           (Cexp_if (Cexp_eq a (Cexp_num 1)) b
             (Cexp_pair (Cexp_num 3) (Cexp_pair a b))))
         (Cexp_mul a b))`;;

let cval_fold_def = define
  `(cval_fold (Cexp_num n) = Cexp_num n) /\
   (cval_fold (Cexp_pair t (Cexp_num m)) = Cexp_pair t (Cexp_num m)) /\
   (cval_fold (Cexp_pair t (Cexp_pair a b)) =
      Cexp_if (Cexp_eq t (Cexp_num 1)) (cval_oadd (cval_fold a) (cval_fold b))
        (Cexp_if (Cexp_eq t (Cexp_num 2)) (cval_osub (cval_fold a) (cval_fold b))
          (cval_omul (cval_fold a) (cval_fold b))))`;;

let cval_fold_c = prove
  (`cval_fold p =
      Cexp_if (Cexp_ispair p)
        (Cexp_if (Cexp_ispair (Cexp_snd p))
          (Cexp_if (Cexp_eq (Cexp_fst p) (Cexp_num 1))
            (cval_oadd (cval_fold (Cexp_fst (Cexp_snd p)))
                       (cval_fold (Cexp_snd (Cexp_snd p))))
            (Cexp_if (Cexp_eq (Cexp_fst p) (Cexp_num 2))
              (cval_osub (cval_fold (Cexp_fst (Cexp_snd p)))
                         (cval_fold (Cexp_snd (Cexp_snd p))))
              (cval_omul (cval_fold (Cexp_fst (Cexp_snd p)))
                         (cval_fold (Cexp_snd (Cexp_snd p))))))
          p)
        p`,
   cval_3cases_tac [cval_fold_def]);;

let CVO_NODES = prove
  (`!p. cval_nodes p = Cexp_num (onodes (cvo p))`,
   MATCH_MP_TAC cval_INDUCT3 THEN
   REWRITE_TAC [cvo_def; onodes_def; cval_nodes_def] THEN
   REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC [onodes_def; cexp_add_def; ADD_ASSOC]);;

let CVO_MAX_LEMMA = prove
  (`!a b. Cexp_add (cval_max (Cexp_num a) (Cexp_num b)) (Cexp_num 2) =
          Cexp_num (MAX a b + 2)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [cval_max_def; cexp_less_def; MAX] THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [cexp_if_def; cexp_add_def] THEN
   AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let CVO_FUEL = prove
  (`!p. cval_fuel p = Cexp_num (ofuel (cvo p))`,
   MATCH_MP_TAC cval_INDUCT3 THEN
   REWRITE_TAC [cvo_def; ofuel_def; cval_fuel_def] THEN
   REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC [ofuel_def; CVO_MAX_LEMMA]);;

let ouro_cval_eqs =
  map SPEC_ALL
    [cval_max_def; cval_nodes_c; cval_fuel_c; cval_eval_c;
      cval_oadd_def; cval_osub_def; cval_omul_def; cval_fold_c];;

(* Execute a closed :cval expression directly via the verified Kernel.compute
   primitive (with zero fallback). *)
let ouro_kernel_compute tm =
  Kernel.compute (COMPUTE_INIT_THMS, ouro_cval_eqs) tm;;

let OURO_KERNEL_COMPUTE_PRIMITIVE_THM =
  Kernel.compute (COMPUTE_INIT_THMS, [])
    `Cexp_if (Cexp_pair (Cexp_num 1) (Cexp_num 2)) (Cexp_num 10) (Cexp_num 42)`;;

let ouro_cval_sample =
  `Cexp_pair (Cexp_num 2)
    (Cexp_pair
      (Cexp_pair (Cexp_num 1)
        (Cexp_pair
          (Cexp_pair (Cexp_num 1) (Cexp_pair (Cexp_num 3) (Cexp_num 7)))
          (Cexp_pair (Cexp_num 3)
            (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0)))))
      (Cexp_pair (Cexp_num 3)
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 1))))`;;

let OURO_CVAL_COMPUTE_THM =
  Kernel.compute (COMPUTE_INIT_THMS, ouro_cval_eqs)
    (mk_comb (`cval_fold`, ouro_cval_sample));;

(* ---------------- the kernel's own verdict on this file ---------------- *)
let ouro_rw_thms =
  [("ofrag_oemb", ofrag_oemb); ("orw_exp_preserves", orw_exp_preserves);
   ("ofold_preserves", ofold_preserves);
   ("ofold_frag", ofold_frag); ("ofold_cost", ofold_cost);
   ("orw_oeq", orw_oeq); ("oeq_preserves", oeq_preserves);
   ("odouble_preserves", odouble_preserves);
   ("ocollect1_preserves", ocollect1_preserves);
   ("ocollect2_preserves", ocollect2_preserves);
   ("oreassoc_preserves", oreassoc_preserves);
   ("OEQ_DOUBLE", OEQ_DOUBLE); ("OEQ_COLLECT1", OEQ_COLLECT1);
   ("OEQ_COLLECT2", OEQ_COLLECT2); ("OEQ_REASSOC", OEQ_REASSOC);
   ("OEQ_OFOLD", OEQ_OFOLD); ("OEQ_ADD", OEQ_ADD);
   ("OEQ_SUB", OEQ_SUB); ("OEQ_MUL", OEQ_MUL);
   ("OEQ_TRANS", OEQ_TRANS);
   ("EVAL_N_LET", EVAL_N_LET); ("EVAL_N_IF", EVAL_N_IF);
   ("OLET_NIL_EVAL", OLET_NIL_EVAL);
   ("OIF_TRUE_EVAL", OIF_TRUE_EVAL); ("OIF_FALSE_EVAL", OIF_FALSE_EVAL);
   ("cval_nodes_c", cval_nodes_c); ("cval_fuel_c", cval_fuel_c);
   ("cval_eval_c", cval_eval_c); ("cval_fold_c", cval_fold_c);
   ("CVO_NODES", CVO_NODES); ("CVO_FUEL", CVO_FUEL);
   ("OURO_KERNEL_COMPUTE_PRIMITIVE_THM", OURO_KERNEL_COMPUTE_PRIMITIVE_THM);
   ("OURO_CVAL_COMPUTE_THM", OURO_CVAL_COMPUTE_THM)];;
(* a sanity instance: the rewriter really rewrites ((3 + 7) + x * 0) - (x * 1) *)
let ouro_rw_example =
  OFOLDO_CONV `ofoldo (OSub (OAdd (OAdd (OLit (&3)) (OLit (&7))) (OMul OX (OLit (&0)))) (OMul OX (OLit (&1))))`;;
let OURO_RW_VERDICT =
  if forall (fun (n, th) -> hyp th = []) ouro_rw_thms &&
     aconv (rand (concl ouro_rw_example)) `OSub (OLit (&10)) OX` &&
     aconv (rand (concl OURO_KERNEL_COMPUTE_PRIMITIVE_THM)) `Cexp_num 42` &&
     aconv (rand (concl OURO_CVAL_COMPUTE_THM))
       `Cexp_pair (Cexp_num 2) (Cexp_pair (Cexp_num 10) (Cexp_pair (Cexp_num 0) (Cexp_num 0)))`
  then "OURO_RW_OK: " ^ string_of_int (length ouro_rw_thms) ^ " rewriter theorems, hypothesis-free"
  else "OURO_RW_FAILED";;
