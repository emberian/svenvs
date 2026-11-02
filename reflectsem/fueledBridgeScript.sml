(* =========================================================================
   reflectsem/fueledBridge — the BRIDGE: every fueled mirror agrees with the
   original CakeML semantics for sufficient fuel.

     |- !x. ?k0. !k. k0 <= k ==> F_n k (INJ_i x) = OUT_i (f_i x)

   These theorems are what make a candle theorem about *_n a theorem about
   the REAL semantics: the candle text of *_n is printed from the defining
   theorems of THESE constants (exportLib, faithful by construction), and
   these bridges pin the constants to the originals.

   Every case closes the same way (fueledBridgeLib): bring the callee / IH
   agreements into the assumptions (agree, ih, ih_pat), then agree_close
   picks the fuel bound above all of them and rewrites both definitions.
   ========================================================================= *)
Theory fueledBridge
Ancestors
  ast namespace semanticPrimitives evaluate fueledSem integer cv_std
Libs
  bossLib BasicProvers fueledBridgeLib intLib cv_transLib

(* ---- helper: a uniform fuel bound across a list (EVERY-style nests) ---- *)
Theorem EVERY_agree_bound[local]:
  ∀l (A:'a -> num -> bool) B.
    (∀x. MEM x l ⇒ ∃k0. ∀k. k0 ≤ k ⇒ (A x k ⇔ B x)) ⇒
    ∃k0. ∀k. k0 ≤ k ⇒ (EVERY (λx. A x k) l ⇔ EVERY B l)
Proof
  Induct
  >- (rw [] \\ qexists_tac ‘0’ \\ rw [])
  \\ rpt strip_tac
  \\ ‘∃k1. ∀k. k1 ≤ k ⇒ (A h k ⇔ B h)’ by (first_assum irule \\ simp [])
  \\ ‘∃k2. ∀k. k2 ≤ k ⇒ (EVERY (λx. A x k) l ⇔ EVERY B l)’
       by (first_x_assum irule \\ rpt strip_tac
           \\ first_assum irule \\ simp [])
  \\ qexists_tac ‘MAX k1 k2’ \\ rw [arithmeticTheory.MAX_LE] \\ gvs []
QED

(* ---- pat_bindings (mutual: pat_bindings / pats_bindings; one output) ----
   strengthened: the bound depends only on the pattern, not already_bound *)
val pb_defs = [fueledSemTheory.pat_bindings_n_def, astTheory.pat_bindings_def];

Theorem pat_bindings_n_agrees:
  (∀p. ∃k0. ∀al k. k0 ≤ k ⇒ pat_bindings_n k (INL (p,al)) = pat_bindings p al) ∧
  (∀ps. ∃k0. ∀al k. k0 ≤ k ⇒ pat_bindings_n k (INR (ps,al)) = pats_bindings ps al)
Proof
  ho_match_mp_tac astTheory.pat_induction \\ rw [] \\ agree_close pb_defs
QED

(* ---- every_exp (single member; recursion nests through EVERY) ---- *)
val ee_defs = [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
               pairTheory.ELIM_UNCURRY];

Theorem every_exp_n_agrees:
  ∀p e. ∃k0. ∀k. k0 ≤ k ⇒ (every_exp_n k p e ⇔ every_exp p e)
Proof
  ho_match_mp_tac astTheory.every_exp_ind \\ rw [] \\ agree_triv ee_defs
  (* list cases: Con/App (bare exps), Handle/Mat (pairs), Letrec (triples) *)
  \\ TRY (‘∃kl. ∀k. kl ≤ k ⇒
            (EVERY (λx. every_exp_n k p x) es ⇔ EVERY (λx. every_exp p x) es)’
            by (ho_match_mp_tac EVERY_agree_bound \\ rw [] \\ metis_tac [])
          \\ agree_close ee_defs \\ NO_TAC)
  \\ TRY (‘∃kl. ∀k. kl ≤ k ⇒
            (EVERY (λx. every_exp_n k p (SND x)) pes ⇔
             EVERY (λx. every_exp p (SND x)) pes)’
            by (ho_match_mp_tac EVERY_agree_bound \\ rw []
                \\ Cases_on ‘x’ \\ fs [] \\ metis_tac [])
          \\ agree_close ee_defs \\ NO_TAC)
  \\ ‘∃kl. ∀k. kl ≤ k ⇒
        (EVERY (λx. every_exp_n k p (SND (SND x))) funs ⇔
         EVERY (λx. every_exp p (SND (SND x))) funs)’
       by (ho_match_mp_tac EVERY_agree_bound \\ rw []
           \\ PairCases_on ‘x’ \\ fs [] \\ metis_tac [])
  \\ agree_close ee_defs
QED

(* ---- one_con_check (non-recursive: ANY positive fuel agrees) ---- *)
Theorem one_con_check_n_agrees_uniform:
  ∀k envc e. 0 < k ⇒ (one_con_check_n k envc e ⇔ one_con_check envc e)
Proof
  Cases \\ rw [] \\ Cases_on ‘e’
  \\ rw [fueledSemTheory.one_con_check_n_def,
         semanticPrimitivesTheory.one_con_check_def]
QED

Theorem one_con_check_n_agrees:
  ∀envc e. ∃k0. ∀k. k0 ≤ k ⇒ (one_con_check_n k envc e ⇔ one_con_check envc e)
Proof
  rw [] \\ qexists_tac ‘SUC 0’ \\ rw [one_con_check_n_agrees_uniform]
QED

(* the fueled nest as it occurs inside eval_n's Dlet/Dletrec clauses *)
Theorem every_exp_one_con_check_n_agrees:
  ∀envc e. ∃k0. ∀k. k0 ≤ k ⇒
    (every_exp_n k (λx. one_con_check_n k envc x) e ⇔
     every_exp (one_con_check envc) e)
Proof
  rw []
  \\ qspecl_then [‘one_con_check envc’,‘e’] strip_assume_tac every_exp_n_agrees
  \\ qexists_tac ‘MAX (SUC 0) k0’ \\ rw [arithmeticTheory.MAX_LE]
  \\ ‘(λx. one_con_check_n k envc x) = one_con_check envc’
       by rw [FUN_EQ_THM, one_con_check_n_agrees_uniform]
  \\ fs []
QED

(* ---- do_eq (mutual: do_eq / do_eq_list; one output type) ---- *)
val deq_defs = [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def];

Theorem do_eq_n_agrees:
  (∀v1 v2. ∃k0. ∀k. k0 ≤ k ⇒ do_eq_n k (INL (v1,v2)) = do_eq v1 v2) ∧
  (∀vs1 vs2. ∃k0. ∀k. k0 ≤ k ⇒ do_eq_n k (INR (vs1,vs2)) = do_eq_list vs1 vs2)
Proof
  ho_match_mp_tac semanticPrimitivesTheory.do_eq_ind \\ rw []
  \\ agree_triv deq_defs
  >~ [‘do_eq (Conv cn1 vs1) (Conv cn2 vs2)’]
  >- (Cases_on ‘cn1 = cn2 ∧ LENGTH vs1 = LENGTH vs2’
      >- (ih_pat ‘_ ⇒ _’ \\ agree_close deq_defs)
      \\ agree_close_cases deq_defs)
  >~ [‘do_eq (Vectorv vs1) (Vectorv vs2)’]
  >- (Cases_on ‘LENGTH vs1 = LENGTH vs2’
      >- (ih_pat ‘_ ⇒ _’ \\ agree_close deq_defs)
      \\ agree_close_cases deq_defs)
  >~ [‘do_eq_list (v1::vs1) (v2::vs2)’]
  \\ Cases_on ‘do_eq v1 v2’ \\ gvs []
  >- (Cases_on ‘b’ \\ gvs [] \\ agree_close deq_defs)
  \\ agree_close deq_defs
QED

(* ---- pmatch (mutual: pmatch / pmatch_list; one output type) ---- *)
val pm_defs = [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def];

Theorem pmatch_n_agrees:
  (∀envC s p v env. ∃k0. ∀k. k0 ≤ k ⇒
     pmatch_n k (INL (envC,s,p,v,env)) = pmatch envC s p v env) ∧
  (∀envC s ps vs env. ∃k0. ∀k. k0 ≤ k ⇒
     pmatch_n k (INR (envC,s,ps,vs,env)) = pmatch_list envC s ps vs env)
Proof
  ho_match_mp_tac semanticPrimitivesTheory.pmatch_ind \\ rw []
  \\ agree_triv pm_defs
  >~ [‘Pcon (SOME n) ps’, ‘Conv (SOME stamp') vs’]
  >- (Cases_on ‘nsLookup envC n’ >- agree_close pm_defs
      \\ PairCases_on ‘x’
      \\ Cases_on ‘same_type x1 stamp' ∧ same_ctor x1 stamp' ∧
                   x0 = LENGTH ps ∧ LENGTH vs = LENGTH ps’
      >- (ih [‘x1’] \\ agree_close_cases pm_defs)
      \\ agree_close_cases pm_defs)
  >~ [‘Pcon NONE ps’]
  >- (Cases_on ‘LENGTH ps = LENGTH vs’
      >- (ih_pat ‘_ ⇒ _’ \\ agree_close pm_defs)
      \\ agree_close pm_defs)
  >~ [‘Pref p’, ‘Loc _ lnum’]
  >- (Cases_on ‘store_lookup lnum s’ >- agree_close pm_defs
      \\ Cases_on ‘x’
      \\ TRY (rename1 ‘store_lookup lnum s = SOME (Refv vv)’
              \\ ih [‘vv’] \\ agree_close pm_defs \\ NO_TAC)
      \\ agree_close pm_defs)
  >~ [‘pmatch_list _ _ (p::ps) (v::vs)’]
  >- (Cases_on ‘pmatch envC s p v env’ \\ gvs [] \\ agree_close pm_defs)
  (* Pas / Ptannot: the IH bound alone *)
  \\ agree_close pm_defs
QED

(* ---- v_to_list / v_to_char_list / vs_to_string (single member) ---- *)
Theorem v_to_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_list_n k v = v_to_list v
Proof
  ho_match_mp_tac semanticPrimitivesTheory.v_to_list_ind \\ rw []
  \\ agree_triv [fueledSemTheory.v_to_list_n_def,
                 semanticPrimitivesTheory.v_to_list_def]
  \\ Cases_on ‘stamp = TypeStamp «::» list_type_num’ \\ gvs []
  >- (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’ \\ fs []
      \\ rw [fueledSemTheory.v_to_list_n_def,
             semanticPrimitivesTheory.v_to_list_def]
      \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
      \\ every_case_tac \\ fs [])
  \\ agree_close [fueledSemTheory.v_to_list_n_def,
                  semanticPrimitivesTheory.v_to_list_def]
QED

Theorem v_to_char_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_char_list_n k v = v_to_char_list v
Proof
  ho_match_mp_tac semanticPrimitivesTheory.v_to_char_list_ind \\ rw []
  \\ agree_triv [fueledSemTheory.v_to_char_list_n_def,
                 semanticPrimitivesTheory.v_to_char_list_def]
  \\ Cases_on ‘stamp = TypeStamp «::» list_type_num’ \\ gvs []
  >- (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’ \\ fs []
      \\ rw [fueledSemTheory.v_to_char_list_n_def,
             semanticPrimitivesTheory.v_to_char_list_def]
      \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
      \\ every_case_tac \\ fs [])
  \\ agree_close [fueledSemTheory.v_to_char_list_n_def,
                  semanticPrimitivesTheory.v_to_char_list_def]
QED

Theorem vs_to_string_n_agrees:
  ∀vs. ∃k0. ∀k. k0 ≤ k ⇒ vs_to_string_n k vs = vs_to_string vs
Proof
  ho_match_mp_tac semanticPrimitivesTheory.vs_to_string_ind \\ rw []
  \\ agree_triv [fueledSemTheory.vs_to_string_n_def,
                 semanticPrimitivesTheory.vs_to_string_def]
  \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’ \\ fs []
  \\ rw [fueledSemTheory.vs_to_string_n_def,
         semanticPrimitivesTheory.vs_to_string_def]
  \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
  \\ every_case_tac \\ fs []
QED

(* ---- concrete_v (mutual: concrete_v / concrete_v_list) ---- *)
Theorem concrete_v_n_agrees:
  (∀v. ∃k0. ∀k. k0 ≤ k ⇒ (concrete_v_n k (INL v) ⇔ concrete_v v)) ∧
  (∀vs. ∃k0. ∀k. k0 ≤ k ⇒ (concrete_v_n k (INR vs) ⇔ concrete_v_list vs))
Proof
  ho_match_mp_tac semanticPrimitivesTheory.concrete_v_ind \\ rw []
  \\ TRY (Cases_on ‘v’) \\ gvs []
  \\ agree_close [fueledSemTheory.concrete_v_n_def,
                  semanticPrimitivesTheory.concrete_v_def]
QED

(* ---- can_pmatch_all (recursive over the pat list; pmatch_n pointwise) ---- *)
val cpa_defs = [fueledSemTheory.can_pmatch_all_n_def,
                semanticPrimitivesTheory.can_pmatch_all_def];

Theorem can_pmatch_all_n_agrees:
  ∀ps envC refs v. ∃k0. ∀k. k0 ≤ k ⇒
    (can_pmatch_all_n k envC refs ps v ⇔ can_pmatch_all envC refs ps v)
Proof
  Induct >- (rw [] \\ agree_close cpa_defs)
  \\ rw []
  \\ first_x_assum (qspecl_then [‘envC’,‘refs’,‘v’] strip_assume_tac)
  \\ agree [‘envC’,‘refs’,‘h’,‘v’,‘[]’] (CONJUNCT1 pmatch_n_agrees)
  \\ agree_close cpa_defs
QED

(* ---- do_test (non-recursive; do_eq_n pointwise in the Equal branch) ---- *)
Theorem do_test_n_agrees:
  ∀tst ty v1 v2. ∃k0. ∀k. k0 ≤ k ⇒
    do_test_n k tst ty v1 v2 = do_test tst ty v1 v2
Proof
  rpt gen_tac \\ agree [‘v1’,‘v2’] (CONJUNCT1 do_eq_n_agrees)
  \\ Cases_on ‘tst’
  \\ agree_close [fueledSemTheory.do_test_n_def,
                  semanticPrimitivesTheory.do_test_def]
QED

(* ---- v_to_word8_list / v_to_word64_list (v_to_list_n pointwise) ---- *)
Theorem v_to_word8_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_word8_list_n k v = v_to_word8_list v
Proof
  gen_tac \\ agree [‘v’] v_to_list_n_agrees
  \\ agree_close [fueledSemTheory.v_to_word8_list_n_def,
                  semanticPrimitivesTheory.v_to_word8_list_def]
QED

Theorem v_to_word64_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_word64_list_n k v = v_to_word64_list v
Proof
  gen_tac \\ agree [‘v’] v_to_list_n_agrees
  \\ agree_close [fueledSemTheory.v_to_word64_list_n_def,
                  semanticPrimitivesTheory.v_to_word64_list_def]
QED

(* ---- compiler_agrees (non-recursive; concrete_v_n / v_to_word*_list_n
        pointwise on the four values it inspects) ---- *)
Theorem compiler_agrees_n_agrees:
  ∀f args r. ∃k0. ∀k. k0 ≤ k ⇒
    (compiler_agrees_n k f args r ⇔ compiler_agrees f args r)
Proof
  rpt gen_tac \\ PairCases_on ‘args’ \\ PairCases_on ‘r’
  \\ agree [‘r0’] (CONJUNCT1 concrete_v_n_agrees)
  \\ agree [‘args2’] (CONJUNCT1 concrete_v_n_agrees)
  \\ agree [‘r1’] v_to_word8_list_n_agrees
  \\ agree [‘r2’] v_to_word64_list_n_agrees
  \\ agree_close_cases [fueledSemTheory.compiler_agrees_n_def,
                        semanticPrimitivesTheory.compiler_agrees_def]
QED

(* ---- do_eval (non-recursive; concrete_v_n and compiler_agrees_n on the
        one row that inspects the argument values; every other row is
        identical on both sides) ---- *)
val deval_defs =
  [fueledSemTheory.do_eval_n_def, semanticPrimitivesTheory.do_eval_def];

Theorem do_eval_n_agrees:
  ∀vs es. ∃k0. ∀k. k0 ≤ k ⇒ do_eval_n k vs es = do_eval vs es
Proof
  rpt gen_tac
  \\ Cases_on ‘∃s env id st_v decs_v st_v2 bs_v ws_v.
                 es = SOME (EvalDecs s) ∧
                 vs = [Env env id; st_v; decs_v; st_v2; bs_v; ws_v]’
  >- (gvs [] \\ Cases_on ‘s.decode_decs decs_v’ >- agree_close deval_defs
      \\ agree [‘decs_v’] (CONJUNCT1 concrete_v_n_agrees)
      \\ agree [‘s.compiler’,‘(id,st_v,x)’,‘(st_v2,bs_v,ws_v)’]
           compiler_agrees_n_agrees
      \\ agree_close deval_defs)
  \\ agree_close_cases deval_defs
QED

(* ---- do_eval_res (non-recursive; do_eval_n pointwise) ---- *)
Theorem do_eval_res_n_agrees:
  ∀vs s. ∃k0. ∀k. k0 ≤ k ⇒ do_eval_res_n k vs s = do_eval_res vs s
Proof
  rpt gen_tac \\ agree [‘vs’,‘s.eval_state’] do_eval_n_agrees
  \\ agree_close [fueledSemTheory.do_eval_res_n_def,
                  evaluateTheory.do_eval_res_def]
QED

(* ---- do_app (non-recursive, huge case tree; callee agreements pointwise
        in exactly six ops: Equality, Test, Implode, Strcat, VfromList,
        ListAppend; every other op's row is identical on both sides) ---- *)
val dapp_defs =
  [fueledSemTheory.do_app_n_def, semanticPrimitivesTheory.do_app_def];
(* split the argument list down to one element / two elements; every other
   shape is a NONE row on both sides *)
val dapp_one =
  Cases_on ‘vs’ \\ agree_triv dapp_defs \\ Cases_on ‘t’ \\ agree_triv dapp_defs
  \\ rename1 ‘[v1]’;
val dapp_two =
  Cases_on ‘vs’ \\ agree_triv dapp_defs \\ Cases_on ‘t’ \\ agree_triv dapp_defs
  \\ Cases_on ‘t'’ \\ agree_triv dapp_defs \\ rename1 ‘[v1; v2]’;

Theorem do_app_n_agrees:
  ∀st ffi op vs. ∃k0. ∀k. k0 ≤ k ⇒
    do_app_n k (st,ffi) op vs = do_app (st,ffi) op vs
Proof
  rpt gen_tac \\ Cases_on ‘op’ \\ agree_triv dapp_defs
  >~ [‘Equality’]
  >- (dapp_two \\ agree [‘v1’,‘v2’] (CONJUNCT1 do_eq_n_agrees)
      \\ agree_close dapp_defs)
  >~ [‘Test tst tty’]
  >- (dapp_two \\ agree [‘tst’,‘tty’,‘v1’,‘v2’] do_test_n_agrees
      \\ agree_close dapp_defs)
  >~ [‘Implode’]
  >- (dapp_one \\ agree [‘v1’] v_to_char_list_n_agrees
      \\ agree_close dapp_defs)
  >~ [‘Strcat’]
  >- (dapp_one \\ agree [‘v1’] v_to_list_n_agrees
      \\ agree [‘THE (v_to_list v1)’] vs_to_string_n_agrees
      \\ agree_close_cases dapp_defs)
  >~ [‘VfromList’]
  >- (dapp_one \\ agree [‘v1’] v_to_list_n_agrees \\ agree_close dapp_defs)
  >~ [‘ListAppend’]
  \\ dapp_two \\ agree [‘v1’] v_to_list_n_agrees \\ agree [‘v2’] v_to_list_n_agrees
  \\ agree_close dapp_defs
QED

(* ---- eval_n: THE KEYSTONE — the fueled mirror of the clocked mutual
        evaluate / evaluate_match / evaluate_decs group agrees with the real
        CakeML semantics for sufficient fuel. One case per evaluate clause
        that is not closed by the recursive bounds alone. ---- *)
val eval_defs = [fueledSemTheory.eval_n_def, evaluateTheory.full_evaluate_def];

Theorem eval_n_agrees:
  (∀(st:'ffi state) env es. ∃k0. ∀k. k0 ≤ k ⇒
     eval_n k (INL (st,env,es)) = INL (evaluate st env es)) ∧
  (∀(st:'ffi state) env v pes errv. ∃k0. ∀k. k0 ≤ k ⇒
     eval_n k (INR (INL (st,env,v,pes,errv))) =
     INR (INL (evaluate_match st env v pes errv))) ∧
  (∀(st:'ffi state) env ds. ∃k0. ∀k. k0 ≤ k ⇒
     eval_n k (INR (INR (st,env,ds))) =
     INR (INR (evaluate_decs st env ds)))
Proof
  ho_match_mp_tac evaluateTheory.full_evaluate_ind \\ rw []
  \\ agree_triv eval_defs
  >~ [‘evaluate st env (e1::e2::es)’]
  >- (Cases_on ‘evaluate st env [e1]’ \\ Cases_on ‘r’
      >- (ih [‘q’,‘a’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Handle e pes]’]
  >- (Cases_on ‘evaluate st env [e]’ \\ Cases_on ‘r’ >- agree_close eval_defs
      \\ Cases_on ‘e'’ \\ TRY (agree_close eval_defs \\ NO_TAC)
      \\ rename1 ‘evaluate st env [e] = (q,Rerr (Rraise vv))’
      \\ agree [‘MAP FST pes’,‘env.c’,‘q.refs’,‘vv’] can_pmatch_all_n_agrees
      \\ Cases_on ‘can_pmatch_all env.c q.refs (MAP FST pes) vv’
      >- (ih [‘q’,‘vv’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Con cn es]’]
  >- (Cases_on ‘do_con_check env.c cn (LENGTH es)’
      >- (ih_pat ‘_ ⇒ _’ \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[App op es]’]
  >- (Cases_on ‘evaluate st env (REVERSE es)’ \\ Cases_on ‘r’
      >- (Cases_on ‘getOpClass op’ \\ fs []
          >- (* EvalOp *)
           (agree [‘REVERSE a’,‘q’] (INST_TYPE [beta |-> “:v”] do_eval_res_n_agrees)
            \\ Cases_on ‘do_eval_res (REVERSE a) q
                           :'ffi state # (v sem_env # dec list, v) result’
            \\ rename1 ‘do_eval_res _ _ = (st1,res)’ \\ Cases_on ‘res’
            >- (rename1 ‘(st1,Rval ed)’ \\ PairCases_on ‘ed’
                \\ Cases_on ‘st1.clock = 0’ >- agree_close eval_defs
                \\ ih [‘st1’,‘ed0’,‘ed1’] \\ agree_close eval_defs)
            \\ agree_close eval_defs)
          >- (* FunApp *)
           (Cases_on ‘do_opapp (REVERSE a)’ >- agree_close eval_defs
            \\ PairCases_on ‘x’
            \\ Cases_on ‘q.clock = 0’ >- agree_close eval_defs
            \\ ih [‘x0’,‘x1’] \\ agree_close eval_defs)
          >- (* Force *)
           (Cases_on ‘dest_thunk (REVERSE a) q.refs’
            \\ TRY (agree_close eval_defs \\ NO_TAC)
            \\ Cases_on ‘t’ >- agree_close eval_defs
            \\ rename1 ‘dest_thunk (REVERSE a) q.refs = IsThunk NotEvaluated vv’
            \\ Cases_on ‘do_opapp [vv; Conv NONE []]’ >- agree_close eval_defs
            \\ PairCases_on ‘x’
            \\ Cases_on ‘q.clock = 0’ >- agree_close eval_defs
            \\ ih [‘vv’,‘x0’,‘x1’] \\ agree_close eval_defs)
          (* Simple *)
          \\ agree [‘q.refs’,‘q.ffi’,‘op’,‘REVERSE a’] do_app_n_agrees
          \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Log lop e1 e2]’]
  >- (Cases_on ‘evaluate st env [e1]’ \\ Cases_on ‘r’
      >- (Cases_on ‘do_log lop (HD a) e2’ >- agree_close eval_defs
          \\ Cases_on ‘x’
          >- (rename1 ‘do_log lop (HD a) e2 = SOME (Exp ee)’
              \\ ih [‘q’,‘a’,‘ee’] \\ agree_close eval_defs)
          \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[If e1 e2 e3]’]
  >- (Cases_on ‘evaluate st env [e1]’ \\ Cases_on ‘r’
      >- (Cases_on ‘do_if (HD a) e2 e3’ >- agree_close eval_defs
          \\ ih [‘q’,‘a’,‘x’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Mat e pes]’]
  >- (Cases_on ‘evaluate st env [e]’ \\ Cases_on ‘r’
      >- (agree [‘MAP FST pes’,‘env.c’,‘q.refs’,‘HD a’] can_pmatch_all_n_agrees
          \\ Cases_on ‘can_pmatch_all env.c q.refs (MAP FST pes) (HD a)’
          >- (ih [‘q’,‘a’] \\ agree_close eval_defs)
          \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Let xo e1 e2]’]
  >- (Cases_on ‘evaluate st env [e1]’ \\ Cases_on ‘r’
      >- (ih [‘q’,‘a’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Letrec funs e]’]
  >- (Cases_on ‘ALL_DISTINCT (MAP (λ(x,y,z). x) funs)’
      >- (ih_pat ‘_ ⇒ _’ \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘evaluate_match st env v ((p,e)::pes) err_v’]
  >- (agree [‘p’] (CONJUNCT1 pat_bindings_n_agrees)
      \\ agree [‘env.c’,‘st.refs’,‘p’,‘v’,‘[]’] (CONJUNCT1 pmatch_n_agrees)
      \\ Cases_on ‘ALL_DISTINCT (pat_bindings p [])’
      >- (Cases_on ‘pmatch env.c st.refs p v []’
          >- (ih_pat ‘_ ∧ _ = No_match ⇒ _’ \\ agree_close eval_defs)
          >- agree_close eval_defs
          \\ rename1 ‘pmatch _ _ _ _ _ = Match bnds’
          \\ ih_pat_at ‘∀env_v'. _ ⇒ _’ [‘bnds’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘evaluate_decs st env (d1::d2::ds)’]
  >- (Cases_on ‘evaluate_decs st env [d1]’ \\ Cases_on ‘r’
      >- (ih [‘q’,‘a’] \\ agree_close eval_defs)
      \\ agree_close eval_defs)
  >~ [‘[Dlet locs p e]’]
  >- (agree [‘p’] (CONJUNCT1 pat_bindings_n_agrees)
      \\ agree [‘env.c’,‘e’] every_exp_one_con_check_n_agrees
      \\ Cases_on ‘ALL_DISTINCT (pat_bindings p []) ∧
                   every_exp (one_con_check env.c) e’
      >- (ih_pat ‘_ ∧ _ ⇒ ∃k0. _’
          \\ Cases_on ‘evaluate st env [e]’ \\ Cases_on ‘r’
          >- (agree [‘env.c’,‘q.refs’,‘p’,‘HD a’,‘[]’]
                (CONJUNCT1 pmatch_n_agrees)
              \\ agree_close eval_defs)
          \\ agree_close eval_defs)
      \\ agree_close_cases eval_defs)
  >~ [‘[Dletrec locs funs]’]
  >- (‘∃kl. ∀k. kl ≤ k ⇒
         (EVERY (λx. every_exp_n k (λzw1. one_con_check_n k env.c zw1)
                       (SND (SND x))) funs ⇔
          EVERY (λx. every_exp (one_con_check env.c) (SND (SND x))) funs)’
        by (ho_match_mp_tac EVERY_agree_bound \\ rw []
            \\ agree [‘env.c’,‘SND (SND x)’] every_exp_one_con_check_n_agrees
            \\ qexists_tac ‘k0’ \\ fs [])
      \\ agree_close (pairTheory.ELIM_UNCURRY :: eval_defs))
  >~ [‘[Dlocal lds ds]’]
  \\ Cases_on ‘evaluate_decs st env lds’ \\ Cases_on ‘r’
  >- (ih [‘q’,‘a’] \\ agree_close eval_defs)
  \\ agree_close eval_defs
QED

(* =========================================================================
   AST SMART-CONSTRUCTOR OPTIMIZATIONS & OUROBOROS `ofold` PASS ON `eval_n`,
   WITH IN-KERNEL `cv_eval` TRANSLATION AND BENCHMARKS.
   ========================================================================= *)

val sem_simps = [
  evaluateTheory.evaluate_def, evaluateTheory.fix_clock_def,
  semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.check_type_def,
  semanticPrimitivesTheory.do_arith_def, semanticPrimitivesTheory.do_test_def,
  semanticPrimitivesTheory.do_eq_def, semanticPrimitivesTheory.lit_same_type_def,
  semanticPrimitivesTheory.do_if_def,
  namespaceTheory.nsOptBind_def,
  semanticPrimitivesTheory.state_component_equality
];

Theorem Boolv_11[local,simp]:
  (Boolv b1 = Boolv b2) ⇔ (b1 = b2)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ EVAL_TAC
QED

Theorem sem_env_with_v_self[local,simp]:
  (env : 'v sem_env) with v := env.v = env
Proof
  rw [semanticPrimitivesTheory.sem_env_component_equality]
QED

Theorem state_with_refs_ffi_self[local,simp]:
  (st : 'ffi state) with <|refs := st.refs; ffi := st.ffi|> = st
Proof
  rw [semanticPrimitivesTheory.state_component_equality]
QED

Definition ast_mk_let_def:
  ast_mk_let xo (e1:ast$exp) (e2:ast$exp) =
    case (xo, e1) of
    | (NONE, Lit l) => e2
    | _ => Let xo e1 e2
End

Theorem ast_mk_let_evaluate:
  ∀(st:'ffi state) env xo e1 e2.
    evaluate st env [ast_mk_let xo e1 e2] = evaluate st env [Let xo e1 e2]
Proof
  rw [ast_mk_let_def]
  \\ every_case_tac \\ fs []
  \\ rw sem_simps
QED

Theorem ast_mk_let_eval_n_agrees:
  ∀(st:'ffi state) env xo e1 e2.
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [ast_mk_let xo e1 e2])) =
      eval_n k (INL (st, env, [Let xo e1 e2]))
Proof
  rpt gen_tac
  \\ qspecl_then [‘st’, ‘env’, ‘[ast_mk_let xo e1 e2]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qspecl_then [‘st’, ‘env’, ‘[Let xo e1 e2]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qexists_tac ‘MAX k0 k0'’
  \\ rw [arithmeticTheory.MAX_LE, ast_mk_let_evaluate]
QED

Definition ast_dest_int_lit_def:
  ast_dest_int_lit (Lit (IntLit i)) = SOME i ∧
  ast_dest_int_lit _ = NONE
End

Theorem ast_dest_int_lit_SOME:
  ∀e i. ast_dest_int_lit e = SOME i ⇔ e = Lit (IntLit i)
Proof
  Cases \\ simp [ast_dest_int_lit_def]
  \\ Cases_on ‘l’ \\ simp [ast_dest_int_lit_def]
QED

Definition ast_mk_app_def:
  ast_mk_app (op:ast$op) (es:ast$exp list) =
    case es of
    | [e1; e2] =>
        (case (ast_dest_int_lit e1, ast_dest_int_lit e2) of
         | (SOME m, SOME n) =>
             if op = Arith Add IntT then Lit (IntLit (m + n))
             else if op = Arith Sub IntT then Lit (IntLit (m - n))
             else if op = Arith Mul IntT then Lit (IntLit (m * n))
             else App op es
         | _ => App op es)
    | _ => App op es
End

Theorem ast_mk_app_evaluate:
  ∀(st:'ffi state) env op es.
    evaluate st env [ast_mk_app op es] = evaluate st env [App op es]
Proof
  rw [ast_mk_app_def]
  \\ every_case_tac \\ fs [ast_dest_int_lit_SOME]
  \\ rw sem_simps
QED

Theorem ast_mk_app_eval_n_agrees:
  ∀(st:'ffi state) env op es.
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [ast_mk_app op es])) =
      eval_n k (INL (st, env, [App op es]))
Proof
  rpt gen_tac
  \\ qspecl_then [‘st’, ‘env’, ‘[ast_mk_app op es]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qspecl_then [‘st’, ‘env’, ‘[App op es]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qexists_tac ‘MAX k0 k0'’
  \\ rw [arithmeticTheory.MAX_LE, ast_mk_app_evaluate]
QED

Definition ast_mk_if_def:
  ast_mk_if (c:ast$exp) (e2:ast$exp) (e3:ast$exp) =
    case c of
    | App (Test Equal IntT) [e1; e1'] =>
        (case (ast_dest_int_lit e1, ast_dest_int_lit e1') of
         | (SOME m, SOME n) => if m = n then e2 else e3
         | _ => If c e2 e3)
    | _ => If c e2 e3
End

Theorem ast_mk_if_evaluate:
  ∀(st:'ffi state) env c e2 e3.
    evaluate st env [ast_mk_if c e2 e3] = evaluate st env [If c e2 e3]
Proof
  rw [ast_mk_if_def]
  \\ every_case_tac \\ fs [ast_dest_int_lit_SOME]
  \\ rw sem_simps
QED

Theorem ast_mk_if_eval_n_agrees:
  ∀(st:'ffi state) env c e2 e3.
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [ast_mk_if c e2 e3])) =
      eval_n k (INL (st, env, [If c e2 e3]))
Proof
  rpt gen_tac
  \\ qspecl_then [‘st’, ‘env’, ‘[ast_mk_if c e2 e3]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qspecl_then [‘st’, ‘env’, ‘[If c e2 e3]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qexists_tac ‘MAX k0 k0'’
  \\ rw [arithmeticTheory.MAX_LE, ast_mk_if_evaluate]
QED

(* ---- Recursive Ouroboros AST fragment (`oexp`) embedded in `ast$exp` ---- *)

Datatype:
  oexp = OVar
       | OLit int
       | OAdd oexp oexp
       | OSub oexp oexp
       | OMul oexp oexp
       | OLetNil int oexp
       | OIfEq int int oexp oexp
End

Definition oemb_def:
  oemb OVar = Var (Short «x») ∧
  oemb (OLit i) = Lit (IntLit i) ∧
  oemb (OAdd p q) = App (Arith Add IntT) [oemb p; oemb q] ∧
  oemb (OSub p q) = App (Arith Sub IntT) [oemb p; oemb q] ∧
  oemb (OMul p q) = App (Arith Mul IntT) [oemb p; oemb q] ∧
  oemb (OLetNil i p) = Let NONE (Lit (IntLit i)) (oemb p) ∧
  oemb (OIfEq m n p q) =
    If (App (Test Equal IntT) [Lit (IntLit m); Lit (IntLit n)])
       (oemb p) (oemb q)
End

Definition oexp_eval_def:
  oexp_eval (x_val:int) OVar = x_val ∧
  oexp_eval x_val (OLit i) = i ∧
  oexp_eval x_val (OAdd p q) = oexp_eval x_val p + oexp_eval x_val q ∧
  oexp_eval x_val (OSub p q) = oexp_eval x_val p - oexp_eval x_val q ∧
  oexp_eval x_val (OMul p q) = oexp_eval x_val p * oexp_eval x_val q ∧
  oexp_eval x_val (OLetNil i p) = oexp_eval x_val p ∧
  oexp_eval x_val (OIfEq m n p q) =
    if m = n then oexp_eval x_val p else oexp_eval x_val q
End

Definition ocost_def:
  ocost OVar = 1n ∧
  ocost (OLit _) = 1n ∧
  ocost (OAdd p q) = 1n + ocost p + ocost q ∧
  ocost (OSub p q) = 1n + ocost p + ocost q ∧
  ocost (OMul p q) = 1n + ocost p + ocost q ∧
  ocost (OLetNil _ p) = 2n + ocost p ∧
  ocost (OIfEq _ _ p q) = 4n + ocost p + ocost q
End

Definition ofuel_def:
  ofuel OVar = 1n ∧
  ofuel (OLit _) = 1n ∧
  ofuel (OAdd p q) = MAX (ofuel p) (ofuel q) + 2n ∧
  ofuel (OSub p q) = MAX (ofuel p) (ofuel q) + 2n ∧
  ofuel (OMul p q) = MAX (ofuel p) (ofuel q) + 2n ∧
  ofuel (OLetNil _ p) = ofuel p + 1n ∧
  ofuel (OIfEq _ _ p q) = MAX (ofuel p) (ofuel q) + 4n
End

Theorem ofuel_pos:
  ∀p. 1n ≤ ofuel p
Proof
  Induct \\ rw [ofuel_def, arithmeticTheory.MAX_DEF]
QED

Theorem oexp_evaluate_correct:
  ∀p (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    evaluate st env [oemb p] = (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  gen_tac \\ rpt gen_tac \\ strip_tac
  \\ Induct_on ‘p’
  \\ rw ([oemb_def, oexp_eval_def] @ sem_simps)
QED

(* Recursive AST-level optimizer composing ast_mk_let, ast_mk_app, ast_mk_if *)
Definition ast_fold_oexp_def:
  ast_fold_oexp OVar = Var (Short «x») ∧
  ast_fold_oexp (OLit i) = Lit (IntLit i) ∧
  ast_fold_oexp (OAdd p q) =
    ast_mk_app (Arith Add IntT) [ast_fold_oexp p; ast_fold_oexp q] ∧
  ast_fold_oexp (OSub p q) =
    ast_mk_app (Arith Sub IntT) [ast_fold_oexp p; ast_fold_oexp q] ∧
  ast_fold_oexp (OMul p q) =
    ast_mk_app (Arith Mul IntT) [ast_fold_oexp p; ast_fold_oexp q] ∧
  ast_fold_oexp (OLetNil i p) =
    ast_mk_let NONE (Lit (IntLit i)) (ast_fold_oexp p) ∧
  ast_fold_oexp (OIfEq m n p q) =
    ast_mk_if (App (Test Equal IntT) [Lit (IntLit m); Lit (IntLit n)])
              (ast_fold_oexp p) (ast_fold_oexp q)
End

Theorem ast_fold_oexp_evaluate:
  ∀p (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    evaluate st env [ast_fold_oexp p] = evaluate st env [oemb p] ∧
    evaluate st env [ast_fold_oexp p] =
      (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  gen_tac \\ rpt gen_tac \\ strip_tac
  \\ drule oexp_evaluate_correct \\ strip_tac
  \\ simp []
  \\ Induct_on ‘p’
  \\ rw [ast_fold_oexp_def, oexp_eval_def,
         ast_mk_app_evaluate, ast_mk_let_evaluate, ast_mk_if_evaluate]
  \\ rw sem_simps
QED

Theorem ast_fold_oexp_eval_n_agrees:
  ∀p (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [ast_fold_oexp p])) =
        eval_n k (INL (st, env, [oemb p])) ∧
      eval_n k (INL (st, env, [ast_fold_oexp p])) =
        INL (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  rpt strip_tac
  \\ drule ast_fold_oexp_evaluate \\ strip_tac
  \\ drule oexp_evaluate_correct \\ strip_tac
  \\ qspecl_then [‘st’, ‘env’, ‘[ast_fold_oexp p]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qspecl_then [‘st’, ‘env’, ‘[oemb p]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qexists_tac ‘MAX k0 k0'’
  \\ rw [arithmeticTheory.MAX_LE]
QED

Definition oadd_smart_def:
  oadd_smart (a:oexp) (b:oexp) =
    case (a, b) of
    | (OLit m, OLit n) => OLit (m + n)
    | (OLit m, _) => if m = 0 then b else OAdd a b
    | (_, OLit n) => if n = 0 then a else OAdd a b
    | _ => OAdd a b
End

Definition osub_smart_def:
  osub_smart (a:oexp) (b:oexp) =
    case (a, b) of
    | (OLit m, OLit n) => OLit (m - n)
    | (_, OLit n) => if n = 0 then a else OSub a b
    | _ => OSub a b
End

Definition omul_smart_def:
  omul_smart (a:oexp) (b:oexp) =
    case (a, b) of
    | (OLit m, OLit n) => OLit (m * n)
    | (OLit m, _) =>
        if m = 0 then OLit 0
        else if m = 1 then b
        else OMul a b
    | (_, OLit n) =>
        if n = 0 then OLit 0
        else if n = 1 then a
        else OMul a b
    | _ => OMul a b
End

Definition ofold_def:
  ofold OVar = OVar ∧
  ofold (OLit i) = OLit i ∧
  ofold (OAdd p q) = oadd_smart (ofold p) (ofold q) ∧
  ofold (OSub p q) = osub_smart (ofold p) (ofold q) ∧
  ofold (OMul p q) = omul_smart (ofold p) (ofold q) ∧
  ofold (OLetNil _ p) = ofold p ∧
  ofold (OIfEq m n p q) = if m = n then ofold p else ofold q
End

Theorem oadd_smart_eval[local]:
  ∀a b x_val. oexp_eval x_val (oadd_smart a b) = oexp_eval x_val a + oexp_eval x_val b
Proof
  rw [oadd_smart_def] \\ every_case_tac \\ fs [oexp_eval_def]
QED

Theorem osub_smart_eval[local]:
  ∀a b x_val. oexp_eval x_val (osub_smart a b) = oexp_eval x_val a - oexp_eval x_val b
Proof
  rw [osub_smart_def] \\ every_case_tac \\ fs [oexp_eval_def]
QED

Theorem omul_smart_eval[local]:
  ∀a b x_val. oexp_eval x_val (omul_smart a b) = oexp_eval x_val a * oexp_eval x_val b
Proof
  rw [omul_smart_def] \\ every_case_tac \\ fs [oexp_eval_def]
QED

Theorem ofold_eval_correct:
  ∀p x_val. oexp_eval x_val (ofold p) = oexp_eval x_val p
Proof
  Induct \\ rw [ofold_def, oexp_eval_def,
                oadd_smart_eval, osub_smart_eval, omul_smart_eval]
QED

Theorem oadd_smart_cost[local]:
  ∀a b. ocost (oadd_smart a b) ≤ 1n + ocost a + ocost b
Proof
  rw [oadd_smart_def] \\ every_case_tac \\ rw [ocost_def]
QED

Theorem osub_smart_cost[local]:
  ∀a b. ocost (osub_smart a b) ≤ 1n + ocost a + ocost b
Proof
  rw [osub_smart_def] \\ every_case_tac \\ rw [ocost_def]
QED

Theorem omul_smart_cost[local]:
  ∀a b. ocost (omul_smart a b) ≤ 1n + ocost a + ocost b
Proof
  rw [omul_smart_def] \\ every_case_tac \\ rw [ocost_def]
QED

Theorem ofold_cost_nonincreasing:
  ∀p. ocost (ofold p) ≤ ocost p
Proof
  Induct \\ rw [ofold_def, ocost_def]
  >- (
    ‘ocost (oadd_smart (ofold p) (ofold p')) ≤ 1 + ocost (ofold p) + ocost (ofold p')’
      by rw [oadd_smart_cost]
    \\ decide_tac
  )
  >- (
    ‘ocost (osub_smart (ofold p) (ofold p')) ≤ 1 + ocost (ofold p) + ocost (ofold p')’
      by rw [osub_smart_cost]
    \\ decide_tac
  )
  >- (
    ‘ocost (omul_smart (ofold p) (ofold p')) ≤ 1 + ocost (ofold p) + ocost (ofold p')’
      by rw [omul_smart_cost]
    \\ decide_tac
  )
QED

Theorem oadd_smart_fuel[local]:
  ∀a b. ofuel (oadd_smart a b) ≤ MAX (ofuel a) (ofuel b) + 2n
Proof
  rw [oadd_smart_def] \\ every_case_tac
  \\ rw [ofuel_def, arithmeticTheory.MAX_DEF]
QED

Theorem osub_smart_fuel[local]:
  ∀a b. ofuel (osub_smart a b) ≤ MAX (ofuel a) (ofuel b) + 2n
Proof
  rw [osub_smart_def] \\ every_case_tac
  \\ rw [ofuel_def, arithmeticTheory.MAX_DEF]
QED

Theorem omul_smart_fuel[local]:
  ∀a b. ofuel (omul_smart a b) ≤ MAX (ofuel a) (ofuel b) + 2n
Proof
  rw [omul_smart_def] \\ every_case_tac
  \\ rw [ofuel_def, arithmeticTheory.MAX_DEF]
QED

Theorem ofold_fuel_nonincreasing:
  ∀p. ofuel (ofold p) ≤ ofuel p
Proof
  Induct \\ rw [ofold_def, ofuel_def]
  >- (
    ‘ofuel (oadd_smart (ofold p) (ofold p')) ≤
       MAX (ofuel (ofold p)) (ofuel (ofold p')) + 2’
      by rw [oadd_smart_fuel]
    \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac
  )
  >- (
    ‘ofuel (osub_smart (ofold p) (ofold p')) ≤
       MAX (ofuel (ofold p)) (ofuel (ofold p')) + 2’
      by rw [osub_smart_fuel]
    \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac
  )
  >- (
    ‘ofuel (omul_smart (ofold p) (ofold p')) ≤
       MAX (ofuel (ofold p)) (ofuel (ofold p')) + 2’
      by rw [omul_smart_fuel]
    \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac
  )
  >- (fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
  >- (fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
QED

Theorem ofold_evaluate_preserves:
  ∀p (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    evaluate st env [oemb (ofold p)] = evaluate st env [oemb p] ∧
    evaluate st env [oemb (ofold p)] =
      (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  rpt strip_tac
  \\ drule oexp_evaluate_correct
  \\ simp [ofold_eval_correct]
QED

Theorem ofold_eval_n_agrees:
  ∀p (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [oemb (ofold p)])) =
        eval_n k (INL (st, env, [oemb p])) ∧
      eval_n k (INL (st, env, [oemb (ofold p)])) =
        INL (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  rpt strip_tac
  \\ drule oexp_evaluate_correct \\ strip_tac
  \\ qspecl_then [‘st’, ‘env’, ‘[oemb (ofold p)]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qspecl_then [‘st’, ‘env’, ‘[oemb p]’]
       strip_assume_tac (CONJUNCT1 eval_n_agrees)
  \\ qexists_tac ‘MAX k0 k0'’
  \\ rw [arithmeticTheory.MAX_LE, ofold_eval_correct]
QED

Theorem eval_n_var_step:
  ∀f (st:'ffi state) env x_val.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ⇒
    eval_n (SUC f) (INL (st, env, [Var (Short «x»)])) =
    INL (st, Rval [Litv (IntLit x_val)])
Proof
  rw [fueledSemTheory.eval_n_def]
QED

Theorem eval_n_lit_step:
  ∀f (st:'ffi state) env i.
    eval_n (SUC f) (INL (st, env, [Lit (IntLit i)])) =
    INL (st, Rval [Litv (IntLit i)])
Proof
  rw [fueledSemTheory.eval_n_def]
QED

Theorem eval_n_pair_step[local]:
  ∀f (st:'ffi state) env a b v1 v2.
    eval_n f (INL (st, env, [a])) = INL (st, Rval [v1]) ∧
    eval_n f (INL (st, env, [b])) = INL (st, Rval [v2]) ⇒
    eval_n (SUC f) (INL (st, env, [a; b])) = INL (st, Rval [v1; v2])
Proof
  rw [Once fueledSemTheory.eval_n_def, evaluateTheory.fix_clock_def]
QED

Theorem do_app_n_arith_step[local]:
  ∀f refs (ffi:'ffi ffi_state) m n.
    do_app_n (SUC f) (refs, ffi) (Arith Add IntT) [Litv (IntLit m); Litv (IntLit n)] =
      SOME ((refs, ffi), Rval (Litv (IntLit (m + n)))) ∧
    do_app_n (SUC f) (refs, ffi) (Arith Sub IntT) [Litv (IntLit m); Litv (IntLit n)] =
      SOME ((refs, ffi), Rval (Litv (IntLit (m - n)))) ∧
    do_app_n (SUC f) (refs, ffi) (Arith Mul IntT) [Litv (IntLit m); Litv (IntLit n)] =
      SOME ((refs, ffi), Rval (Litv (IntLit (m * n))))
Proof
  rw [fueledSemTheory.do_app_n_def, semanticPrimitivesTheory.check_type_def,
      semanticPrimitivesTheory.do_arith_def]
QED

Theorem eval_n_arith_step:
  ∀f (st:'ffi state) env a b m n.
    eval_n f (INL (st, env, [a])) = INL (st, Rval [Litv (IntLit m)]) ∧
    eval_n f (INL (st, env, [b])) = INL (st, Rval [Litv (IntLit n)]) ⇒
    eval_n (SUC (SUC f)) (INL (st, env, [App (Arith Add IntT) [a; b]])) =
      INL (st, Rval [Litv (IntLit (m + n))]) ∧
    eval_n (SUC (SUC f)) (INL (st, env, [App (Arith Sub IntT) [a; b]])) =
      INL (st, Rval [Litv (IntLit (m - n))]) ∧
    eval_n (SUC (SUC f)) (INL (st, env, [App (Arith Mul IntT) [a; b]])) =
      INL (st, Rval [Litv (IntLit (m * n))])
Proof
  rpt strip_tac
  \\ ‘eval_n (SUC f) (INL (st, env, [b; a])) =
        INL (st, Rval [Litv (IntLit n); Litv (IntLit m)])’
       by metis_tac [eval_n_pair_step]
  \\ rw [Once fueledSemTheory.eval_n_def, evaluateTheory.fix_clock_def,
         astTheory.getOpClass_def, do_app_n_arith_step]
QED

Theorem eval_n_let_nil_step:
  ∀f (st:'ffi state) env i a m.
    0 < f ∧
    eval_n f (INL (st, env, [a])) = INL (st, Rval [Litv (IntLit m)]) ⇒
    eval_n (SUC f) (INL (st, env, [Let NONE (Lit (IntLit i)) a])) =
      INL (st, Rval [Litv (IntLit m)])
Proof
  Cases \\ rw []
  \\ rw [Once fueledSemTheory.eval_n_def, eval_n_lit_step,
         evaluateTheory.fix_clock_def, namespaceTheory.nsOptBind_def]
QED

Theorem do_app_n_test_eq_step[local]:
  ∀f refs (ffi:'ffi ffi_state) m n.
    do_app_n (SUC (SUC (SUC f))) (refs, ffi) (Test Equal IntT)
      [Litv (IntLit m); Litv (IntLit n)] =
    SOME ((refs, ffi), Rval (Boolv (m = n)))
Proof
  rw [fueledSemTheory.do_app_n_def, fueledSemTheory.do_test_n_def,
      fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.check_type_def,
      semanticPrimitivesTheory.lit_same_type_def]
QED

Theorem eval_n_test_eq_step[local]:
  ∀f (st:'ffi state) env m n.
    eval_n (SUC (SUC (SUC (SUC f))))
      (INL (st, env, [App (Test Equal IntT) [Lit (IntLit m); Lit (IntLit n)]])) =
    INL (st, Rval [Boolv (m = n)])
Proof
  rpt gen_tac
  \\ ‘eval_n (SUC (SUC (SUC f))) (INL (st, env, [Lit (IntLit n); Lit (IntLit m)])) =
        INL (st, Rval [Litv (IntLit n); Litv (IntLit m)])’
       by simp [eval_n_pair_step, eval_n_lit_step]
  \\ rw [Once fueledSemTheory.eval_n_def, evaluateTheory.fix_clock_def,
         astTheory.getOpClass_def, do_app_n_test_eq_step]
QED

Theorem eval_n_if_eq_step:
  ∀f (st:'ffi state) env m n a b va vb.
    4n ≤ f ∧
    eval_n f (INL (st, env, [a])) = INL (st, Rval [va]) ∧
    eval_n f (INL (st, env, [b])) = INL (st, Rval [vb]) ⇒
    eval_n (SUC f)
      (INL (st, env,
            [If (App (Test Equal IntT) [Lit (IntLit m); Lit (IntLit n)]) a b])) =
    INL (st, Rval [if m = n then va else vb])
Proof
  rpt strip_tac
  \\ ‘∃f0. f = SUC (SUC (SUC (SUC f0)))’
       by (qexists_tac ‘f - 4’ \\ decide_tac)
  \\ gvs []
  \\ rw [Once fueledSemTheory.eval_n_def, eval_n_test_eq_step,
         evaluateTheory.fix_clock_def, semanticPrimitivesTheory.do_if_def]
QED

Theorem oexp_eval_n_fuel_correct:
  ∀p (st:'ffi state) env x_val k.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ∧
    ofuel p ≤ k ⇒
    eval_n k (INL (st, env, [oemb p])) =
      INL (st, Rval [Litv (IntLit (oexp_eval x_val p))])
Proof
  gen_tac \\ ntac 3 gen_tac
  \\ qid_spec_tac ‘p’
  \\ Induct \\ rw [oemb_def, ofuel_def]
  >| [
    ‘∃f. k = SUC f’ by (qexists_tac ‘k - 1’ \\ decide_tac)
    \\ gvs []
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘x_val’] mp_tac eval_n_var_step
    \\ simp [oexp_eval_def],
    ‘∃f. k = SUC f’ by (qexists_tac ‘k - 1’ \\ decide_tac)
    \\ gvs [eval_n_lit_step, oexp_eval_def],
    ‘∃f. k = SUC (SUC f) ∧ ofuel p ≤ f ∧ ofuel p' ≤ f’
      by (qexists_tac ‘k - 2’ \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ gvs [] \\ rpt strip_tac
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘oemb p’, ‘oemb p'’,
                    ‘oexp_eval x_val p’, ‘oexp_eval x_val p'’]
         mp_tac eval_n_arith_step
    \\ impl_tac >| [simp [], strip_tac \\ simp [oexp_eval_def]],
    ‘∃f. k = SUC (SUC f) ∧ ofuel p ≤ f ∧ ofuel p' ≤ f’
      by (qexists_tac ‘k - 2’ \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ gvs [] \\ rpt strip_tac
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘oemb p’, ‘oemb p'’,
                    ‘oexp_eval x_val p’, ‘oexp_eval x_val p'’]
         mp_tac eval_n_arith_step
    \\ impl_tac >| [simp [], strip_tac \\ simp [oexp_eval_def]],
    ‘∃f. k = SUC (SUC f) ∧ ofuel p ≤ f ∧ ofuel p' ≤ f’
      by (qexists_tac ‘k - 2’ \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ gvs [] \\ rpt strip_tac
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘oemb p’, ‘oemb p'’,
                    ‘oexp_eval x_val p’, ‘oexp_eval x_val p'’]
         mp_tac eval_n_arith_step
    \\ impl_tac >| [simp [], strip_tac \\ simp [oexp_eval_def]],
    ‘1n ≤ ofuel p’ by rw [ofuel_pos]
    \\ ‘∃f. k = SUC f ∧ 0 < f ∧ ofuel p ≤ f’
         by (qexists_tac ‘k - 1’ \\ decide_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ gvs [] \\ rpt strip_tac
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘i’, ‘oemb p’, ‘oexp_eval x_val p’]
         mp_tac eval_n_let_nil_step
    \\ impl_tac >| [simp [], strip_tac \\ simp [oexp_eval_def]],
    ‘1n ≤ ofuel p ∧ 1n ≤ ofuel p'’ by rw [ofuel_pos]
    \\ ‘∃f. k = SUC f ∧ 4n ≤ f ∧ ofuel p ≤ f ∧ ofuel p' ≤ f’
         by (qexists_tac ‘k - 1’ \\ fs [arithmeticTheory.MAX_DEF] \\ decide_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ gvs [] \\ rpt strip_tac
    \\ qspecl_then [‘f’, ‘st:'ffi state’, ‘env’, ‘i0’, ‘i’, ‘oemb p’, ‘oemb p'’,
                    ‘Litv (IntLit (oexp_eval x_val p))’,
                    ‘Litv (IntLit (oexp_eval x_val p'))’]
         mp_tac eval_n_if_eq_step
    \\ impl_tac >| [simp [], strip_tac \\ simp [oexp_eval_def] \\ rw []]
  ]
QED

Theorem ofold_eval_n_fuel_preserves:
  ∀p (st:'ffi state) env x_val k.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit x_val)) ∧
    ofuel p ≤ k ⇒
    eval_n k (INL (st, env, [oemb (ofold p)])) =
      eval_n k (INL (st, env, [oemb p])) ∧
    eval_n k (INL (st, env, [oemb (ofold p)])) =
      INL (st, Rval [Litv (IntLit (oexp_eval x_val p))]) ∧
    ofuel (ofold p) ≤ ofuel p
Proof
  rpt strip_tac
  \\ ‘ofuel (ofold p) ≤ ofuel p’ by rw [ofold_fuel_nonincreasing]
  \\ ‘ofuel (ofold p) ≤ k’ by decide_tac
  \\ qspecl_then [‘p’, ‘st:'ffi state’, ‘env’, ‘x_val’, ‘k’]
       mp_tac oexp_eval_n_fuel_correct
  \\ qspecl_then [‘ofold p’, ‘st:'ffi state’, ‘env’, ‘x_val’, ‘k’]
       mp_tac oexp_eval_n_fuel_correct
  \\ simp [ofold_eval_correct]
QED

(* ---- In-kernel `cv_eval` translations and benchmarks ---- *)

val () = cv_auto_trans oemb_def;
val () = cv_auto_trans oexp_eval_def;
val () = cv_auto_trans ocost_def;
val () = cv_auto_trans ofuel_def;
val () = cv_auto_trans oadd_smart_def;
val () = cv_auto_trans osub_smart_def;
val () = cv_auto_trans omul_smart_def;
val () = cv_auto_trans ofold_def;

Definition demo_ouro_exp_def:
  demo_ouro_exp =
    OLetNil 99
      (OIfEq 5 5
        (OSub
          (OAdd (OAdd (OLit 3) (OLit 7))
                (OMul (OAdd OVar (OLit 100)) (OLit 0)))
          (OMul OVar (OLit 1)))
        (OMul OVar (OLit 999)))
End

val () = cv_auto_trans demo_ouro_exp_def;

Theorem ofold_cv_benchmark:
  ofold demo_ouro_exp = OSub (OLit 10) OVar ∧
  ocost demo_ouro_exp = 22 ∧
  ocost (ofold demo_ouro_exp) = 3 ∧
  ofuel demo_ouro_exp = 14 ∧
  ofuel (ofold demo_ouro_exp) = 3 ∧
  oexp_eval 7 demo_ouro_exp = 3 ∧
  oexp_eval 7 (ofold demo_ouro_exp) = 3 ∧
  oemb (ofold demo_ouro_exp) =
    App (Arith Sub IntT) [Lit (IntLit 10); Var (Short «x»)]
Proof
  CONV_TAC cv_eval
QED

Theorem demo_ouro_eval_n_cv_verified:
  ∀(st:'ffi state) env.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit 7)) ⇒
    ∃k0. ∀k. k0 ≤ k ⇒
      eval_n k (INL (st, env, [oemb (ofold demo_ouro_exp)])) =
        eval_n k (INL (st, env, [oemb demo_ouro_exp])) ∧
      eval_n k (INL (st, env, [oemb (ofold demo_ouro_exp)])) =
        INL (st, Rval [Litv (IntLit 3)])
Proof
  rpt strip_tac
  \\ qspecl_then [‘demo_ouro_exp’, ‘st:'ffi state’, ‘env’, ‘7’] mp_tac ofold_eval_n_agrees
  \\ simp [ofold_cv_benchmark]
QED

Theorem demo_ouro_eval_n_fuel_cv_verified:
  ∀(st:'ffi state) env.
    nsLookup env.v (Short «x») = SOME (Litv (IntLit 7)) ⇒
    (∀k. 3n ≤ k ⇒
       eval_n k (INL (st, env, [oemb (ofold demo_ouro_exp)])) =
         INL (st, Rval [Litv (IntLit 3)])) ∧
    (∀k. 14n ≤ k ⇒
       eval_n k (INL (st, env, [oemb (ofold demo_ouro_exp)])) =
         eval_n k (INL (st, env, [oemb demo_ouro_exp])) ∧
       eval_n k (INL (st, env, [oemb (ofold demo_ouro_exp)])) =
         INL (st, Rval [Litv (IntLit 3)]))
Proof
  rpt strip_tac
  \\ qspecl_then [‘ofold demo_ouro_exp’, ‘st:'ffi state’, ‘env’, ‘7’, ‘k’]
       mp_tac oexp_eval_n_fuel_correct
  \\ qspecl_then [‘demo_ouro_exp’, ‘st:'ffi state’, ‘env’, ‘7’, ‘k’]
       mp_tac ofold_eval_n_fuel_preserves
  \\ simp [ofold_cv_benchmark, ofuel_def, oemb_def, oexp_eval_def,
           arithmeticTheory.MAX_DEF]
QED
