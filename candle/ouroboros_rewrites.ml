(* STATUS: GREEN on the live Candle kernel (hbox, 2026-09-25,
   scripts/reflectsem-live.sh --ouroboros, twice from a clean start): all
   theorems below are proved hypothesis-free and echoed, among them
   ofold_preserves, ofold_frag, ofold_cost, orw_oeq, oeq_preserves and
   ofrag_oemb; OURO_RW_VERDICT = "OURO_RW_OK: 6 rewriter theorems,
   hypothesis-free". What is proved is about the fold/dead rewriter only;
   the improver's other moves (double, collect, reassoc, drop) are still
   gated per candidate, and the improver's own fragment invariant is still
   ML-checked. *)
(* ===================================================================== *)
(*  svenvs OUROBOROS — the improver's rewrites as KERNEL THEOREMS.        *)
(*                                                                        *)
(*  Proved once in the live Candle kernel, against the exported real      *)
(*  CakeML semantics (eval_n), for every term of the fragment:            *)
(*    ofold_preserves  the constant-folding / dead-subterm rewriter keeps *)
(*                     the eval_n result, at any fuel >= efuel e;         *)
(*    ofold_frag       its output stays in the fragment;                  *)
(*    ofold_cost       its output is no larger;                           *)
(*    orw_oeq, oeq_preserves (with the congruences)  the same for ONE     *)
(*                     rewrite at the root, lifted to any position and    *)
(*                     any composition.                                   *)
(*  candle/ouroboros.ml then installs such candidates by SPEC/MP from     *)
(*  these theorems instead of a fresh symbolic execution per candidate.   *)
(*                                                                        *)
(*  Representation (the stated boundary): the rewriter is a HOL function  *)
(*  over an auxiliary binary type oexp (x, int literals, plus, minus,    *)
(*  times), not over the nested ast$exp directly; oemb embeds it into   *)
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
         reflectsem_dt_names [];;
let OURO_EXISTS_REFL2 = prove (`!a:A. ?x. a = x`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;
let ouro_defs =
  reflectsem_dt_thms @ reflectsem_fn_thms @ ouro_ctor_thms @
  [FST; SND; OUTL; OUTR; ALL; MAP; REVERSE; APPEND; LENGTH; HD; TL;
   NOT_SUC; PRE; LET_DEF; LET_END_DEF; EXISTS_REFL; OURO_EXISTS_REFL2;
   PAIR_EQ; CONS_11; injectivity "sum"];;
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

(* ---------------- the real semantics on the fragment's three shapes ---- *)
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

(* ---------------- the rewrites: fold + dead-subterm removal ------------- *)
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

(* p refines q: same denotation, no more fuel, no larger *)
let oeq_def = new_definition
  `oeq p q <=> (!i. osem p i = osem q i) /\ ofuel p <= ofuel q /\ onodes p <= onodes q`;;

let OISLIT_SEM = prove (`!p i. oislit p ==> osem p i = olv p`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [oislit_def; osem_def; olv_def]);;
let OEQ_REFL = prove (`!p. oeq p p`, REWRITE_TAC [oeq_def; LE_REFL]);;
let OEQ_TRANS = prove (`!p q r. oeq p q /\ oeq q r ==> oeq p r`,
  REWRITE_TAC [oeq_def] THEN MESON_TAC [LE_TRANS]);;
let OURO_OEQ_FIN_TAC =
  REWRITE_TAC [oeq_def; osem_def; ofuel_def; onodes_def] THEN
  ASM_SIMP_TAC [OISLIT_SEM] THEN REPEAT CONJ_TAC THEN
  FIRST [GEN_TAC THEN INT_ARITH_TAC; INT_ARITH_TAC;
         REWRITE_TAC [MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC];;
let ouro_op_oeq g =
  prove (g, REPEAT GEN_TAC THEN REWRITE_TAC [oadd_def; osub_def; omul_def] THEN
            REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN OURO_OEQ_FIN_TAC);;
let OADD_OEQ = ouro_op_oeq `!a b. oeq (oadd a b) (OAdd a b)`;;
let OSUB_OEQ = ouro_op_oeq `!a b. oeq (osub a b) (OSub a b)`;;
let OMUL_OEQ = ouro_op_oeq `!a b. oeq (omul a b) (OMul a b)`;;

let orw_oeq = prove (`!p. oeq (orw p) p`,
  MATCH_MP_TAC oexp_INDUCT THEN
  REWRITE_TAC [orw_def; OEQ_REFL; OADD_OEQ; OSUB_OEQ; OMUL_OEQ]);;
let OEQ_CONG = prove
  (`!a a' b b'. oeq a' a /\ oeq b' b ==>
      oeq (OAdd a' b') (OAdd a b) /\ oeq (OSub a' b') (OSub a b) /\
      oeq (OMul a' b') (OMul a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [oeq_def; osem_def; ofuel_def; onodes_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;
let ouro_cong k = GEN_ALL (DISCH_ALL (el k (CONJUNCTS (UNDISCH (SPEC_ALL OEQ_CONG)))));;
let OEQ_CONG_ADD = ouro_cong 0;;
let OEQ_CONG_SUB = ouro_cong 1;;
let OEQ_CONG_MUL = ouro_cong 2;;
let OFOLDO_OEQ = prove (`!p. oeq (ofoldo p) p`,
  MATCH_MP_TAC oexp_INDUCT THEN REWRITE_TAC [ofoldo_def; OEQ_REFL] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC [OEQ_TRANS; OADD_OEQ; OSUB_OEQ; OMUL_OEQ; OEQ_CONG_ADD; OEQ_CONG_SUB; OEQ_CONG_MUL]);;

(* ---------------- refinement is invisible to the real semantics --------- *)
let oeq_preserves = prove
  (`!p q. oeq p q ==> !k i. ofuel q <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb p])) = eval_n k (INL (ost0, oenv i, [oemb q]))`,
  REWRITE_TAC [oeq_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ofuel p <= k` ASSUME_TAC THENL
   [ASM_MESON_TAC [LE_TRANS]; ASM_SIMP_TAC [OEVAL]]);;
let OFOLDO_PRESERVES = prove
  (`!p k i. ofuel p <= k ==>
       eval_n k (INL (ost0, oenv i, [oemb (ofoldo p)])) = eval_n k (INL (ost0, oenv i, [oemb p]))`,
  MESON_TAC [oeq_preserves; OFOLDO_OEQ]);;

(* ---------------- the rewriter on the REAL exp ---------------- *)
let oof_def = new_definition `oof e = @p. oemb p = e`;;
let OOF_OEMB = prove (`!p. oof (oemb p) = p`,
  REWRITE_TAC [oof_def; OEMB_11; SELECT_REFL]);;
let ofold_def = new_definition `ofold e = oemb (ofoldo (oof e))`;;
let ocost_def = new_definition `ocost e = onodes (oof e)`;;
let efuel_def = new_definition `efuel e = ofuel (oof e)`;;

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
  MESON_TAC [OFOLDO_OEQ; oeq_def]);;

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

(* ---------------- the kernel's own verdict on this file ---------------- *)
let ouro_rw_thms =
  [("ofrag_oemb", ofrag_oemb); ("ofold_preserves", ofold_preserves);
   ("ofold_frag", ofold_frag); ("ofold_cost", ofold_cost);
   ("orw_oeq", orw_oeq); ("oeq_preserves", oeq_preserves)];;
(* a sanity instance: the rewriter really rewrites ((3 + 7) + x * 0) - (x * 1) *)
let ouro_rw_example =
  OFOLDO_CONV `ofoldo (OSub (OAdd (OAdd (OLit (&3)) (OLit (&7))) (OMul OX (OLit (&0)))) (OMul OX (OLit (&1))))`;;
let OURO_RW_VERDICT =
  if forall (fun (n, th) -> hyp th = []) ouro_rw_thms &&
     aconv (rand (concl ouro_rw_example)) `OSub (OLit (&10)) OX`
  then "OURO_RW_OK: " ^ string_of_int (length ouro_rw_thms) ^ " rewriter theorems, hypothesis-free"
  else "OURO_RW_FAILED";;
