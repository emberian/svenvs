(* =========================================================================
   reflectsem/fueledBridge — the BRIDGE: every fueled mirror agrees with the
   original CakeML semantics for sufficient fuel.

     |- !x. ?k0. !k. k0 <= k ==> F_n k (INJ_i x) = OUT_i (f_i x)

   These theorems are what make a candle theorem about *_n a theorem about
   the REAL semantics: the candle text of *_n is printed from the defining
   theorems of THESE constants (exportLib, faithful by construction), and
   these bridges pin the constants to the originals.
   ========================================================================= *)
Theory fueledBridge
Ancestors
  ast namespace semanticPrimitives evaluate fueledSem
Libs
  bossLib BasicProvers

(* ---- helper: a uniform fuel bound across a list (EVERY-style nests) ---- *)
Theorem EVERY_agree_bound[local]:
  ∀l (A:'a -> num -> bool) B.
    (∀x. MEM x l ⇒ ∃k0. ∀k. k0 ≤ k ⇒ (A x k ⇔ B x)) ⇒
    ∃k0. ∀k. k0 ≤ k ⇒ (EVERY (λx. A x k) l ⇔ EVERY B l)
Proof
  Induct
  >- (rw [] \\ qexists_tac ‘0’ \\ rw [])
  \\ rw []
  \\ ‘∃k1. ∀k. k1 ≤ k ⇒ (A h k ⇔ B h)’ by metis_tac []
  \\ ‘∃k2. ∀k. k2 ≤ k ⇒ (EVERY (λx. A x k) l ⇔ EVERY B l)’ by metis_tac []
  \\ qexists_tac ‘MAX k1 k2’ \\ rw [arithmeticTheory.MAX_LE]
  \\ metis_tac []
QED

(* ---- pat_bindings (mutual: pat_bindings / pats_bindings; one output) ----
   strengthened: the bound depends only on the pattern, not already_bound *)
Theorem pat_bindings_n_agrees:
  (∀p. ∃k0. ∀al k. k0 ≤ k ⇒ pat_bindings_n k (INL (p,al)) = pat_bindings p al) ∧
  (∀ps. ∃k0. ∀al k. k0 ≤ k ⇒ pat_bindings_n k (INR (ps,al)) = pats_bindings ps al)
Proof
  ho_match_mp_tac astTheory.pat_induction \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.pat_bindings_n_def, astTheory.pat_bindings_def]
          \\ NO_TAC)
  \\ TRY (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.pat_bindings_n_def, astTheory.pat_bindings_def]
          \\ NO_TAC)
  \\ qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.pat_bindings_n_def, astTheory.pat_bindings_def,
         arithmeticTheory.MAX_LE]
QED

(* ---- every_exp (single member; recursion nests through EVERY) ---- *)
Theorem every_exp_n_agrees:
  ∀p e. ∃k0. ∀k. k0 ≤ k ⇒ (every_exp_n k p e ⇔ every_exp p e)
Proof
  ho_match_mp_tac astTheory.every_exp_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def]
          \\ NO_TAC)
  \\ TRY (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def]
          \\ NO_TAC)
  \\ TRY (qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
                 arithmeticTheory.MAX_LE]
          \\ NO_TAC)
  \\ TRY (qexists_tac ‘SUC (MAX k0 (MAX k0' k0''))’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
                 arithmeticTheory.MAX_LE]
          \\ NO_TAC)
  (* list cases: Con/App (bare exps), Handle/Mat (pairs), Letrec (triples) *)
  \\ TRY (‘∃kl. ∀k. kl ≤ k ⇒
            (EVERY (λx. every_exp_n k p x) es ⇔ EVERY (λx. every_exp p x) es)’
            by (ho_match_mp_tac EVERY_agree_bound \\ rw [] \\ metis_tac [])
          \\ qexists_tac ‘SUC kl’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
                 arithmeticTheory.MAX_LE]
          \\ NO_TAC)
  \\ TRY (‘∃kl. ∀k. kl ≤ k ⇒
            (EVERY (λx. every_exp_n k p (SND x)) pes ⇔
             EVERY (λx. every_exp p (SND x)) pes)’
            by (ho_match_mp_tac EVERY_agree_bound \\ rw []
                \\ Cases_on ‘x’ \\ fs [] \\ metis_tac [])
          \\ qexists_tac ‘SUC (MAX k0 kl)’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
                 arithmeticTheory.MAX_LE, pairTheory.ELIM_UNCURRY]
          \\ NO_TAC)
  \\ ‘∃kl. ∀k. kl ≤ k ⇒
        (EVERY (λx. every_exp_n k p (SND (SND x))) funs ⇔
         EVERY (λx. every_exp p (SND (SND x))) funs)’
       by (ho_match_mp_tac EVERY_agree_bound \\ rw []
           \\ PairCases_on ‘x’ \\ fs [] \\ metis_tac [])
  \\ qexists_tac ‘SUC (MAX k0 kl)’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.every_exp_n_def, astTheory.every_exp_def,
         arithmeticTheory.MAX_LE, pairTheory.ELIM_UNCURRY]
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
Theorem do_eq_n_agrees:
  (∀v1 v2. ∃k0. ∀k. k0 ≤ k ⇒ do_eq_n k (INL (v1,v2)) = do_eq v1 v2) ∧
  (∀vs1 vs2. ∃k0. ∀k. k0 ≤ k ⇒ do_eq_n k (INR (vs1,vs2)) = do_eq_list vs1 vs2)
Proof
  ho_match_mp_tac semanticPrimitivesTheory.do_eq_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def]
          \\ NO_TAC)
  >- (* Conv/Conv *)
   (Cases_on ‘cn1 = cn2 ∧ LENGTH vs1 = LENGTH vs2’
    >- (qpat_x_assum ‘_ ⇒ _’ mp_tac \\ simp [] \\ strip_tac
        \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def])
    \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def]
    \\ every_case_tac \\ gvs [])
  >- (* Vectorv/Vectorv *)
   (Cases_on ‘LENGTH vs1 = LENGTH vs2’
    >- (qpat_x_assum ‘_ ⇒ _’ mp_tac \\ simp [] \\ strip_tac
        \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def])
    \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def]
    \\ every_case_tac \\ gvs [])
  (* cons/cons *)
  \\ Cases_on ‘do_eq v1 v2’ \\ gvs []
  >- (Cases_on ‘b’ \\ gvs []
      >- (qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.do_eq_n_def,
                 semanticPrimitivesTheory.do_eq_def, arithmeticTheory.MAX_LE])
      \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
      \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def])
  \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.do_eq_n_def, semanticPrimitivesTheory.do_eq_def]
QED

(* ---- pmatch (mutual: pmatch / pmatch_list; one output type) ---- *)
Theorem pmatch_n_agrees:
  (∀envC s p v env. ∃k0. ∀k. k0 ≤ k ⇒
     pmatch_n k (INL (envC,s,p,v,env)) = pmatch envC s p v env) ∧
  (∀envC s ps vs env. ∃k0. ∀k. k0 ≤ k ⇒
     pmatch_n k (INR (envC,s,ps,vs,env)) = pmatch_list envC s ps vs env)
Proof
  ho_match_mp_tac semanticPrimitivesTheory.pmatch_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def]
          \\ NO_TAC)
  >- (* Pcon SOME / Conv SOME *)
   (Cases_on ‘nsLookup envC n’
    >- (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.pmatch_n_def,
               semanticPrimitivesTheory.pmatch_def])
    \\ PairCases_on ‘x’
    \\ Cases_on ‘same_type x1 stamp' ∧ same_ctor x1 stamp' ∧
                 x0 = LENGTH ps ∧ LENGTH vs = LENGTH ps’
    >- (first_x_assum (qspec_then ‘x1’ mp_tac) \\ simp [] \\ strip_tac
        \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.pmatch_n_def,
               semanticPrimitivesTheory.pmatch_def]
        \\ every_case_tac \\ gvs [])
    \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def]
    \\ every_case_tac \\ gvs [])
  >- (* Pcon NONE / Conv NONE *)
   (Cases_on ‘LENGTH ps = LENGTH vs’
    >- (qpat_x_assum ‘_ ⇒ _’ mp_tac \\ simp [] \\ strip_tac
        \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.pmatch_n_def,
               semanticPrimitivesTheory.pmatch_def])
    \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def])
  >- (* Pref / Loc *)
   (Cases_on ‘store_lookup lnum s’
    >- (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
        \\ fs [fueledSemTheory.pmatch_n_def,
               semanticPrimitivesTheory.pmatch_def])
    \\ Cases_on ‘x’
    \\ TRY (rename1 ‘store_lookup lnum s = SOME (Refv vv)’
            \\ first_x_assum (qspec_then ‘vv’ mp_tac)
            \\ simp [] \\ strip_tac
            \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
            \\ fs [fueledSemTheory.pmatch_n_def,
                   semanticPrimitivesTheory.pmatch_def] \\ NO_TAC)
    \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def])
  >- (* Pas *)
   (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def])
  >- (* Ptannot *)
   (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
    \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def])
  (* cons/cons *)
  \\ Cases_on ‘pmatch envC s p v env’ \\ gvs []
  >- (qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
      \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def,
             arithmeticTheory.MAX_LE])
  >- (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
      \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def])
  \\ qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.pmatch_n_def, semanticPrimitivesTheory.pmatch_def,
         arithmeticTheory.MAX_LE]
QED

(* ---- v_to_list (single member, the pattern-setter) ---- *)
Theorem v_to_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_list_n k v = v_to_list v
Proof
  ho_match_mp_tac semanticPrimitivesTheory.v_to_list_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.v_to_list_n_def,
                 semanticPrimitivesTheory.v_to_list_def] \\ NO_TAC)
  \\ Cases_on ‘stamp = TypeStamp «::» list_type_num’ \\ gvs []
  >- (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’ \\ fs []
      \\ rw [fueledSemTheory.v_to_list_n_def,
             semanticPrimitivesTheory.v_to_list_def]
      \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
      \\ every_case_tac \\ fs [])
  \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.v_to_list_n_def,
         semanticPrimitivesTheory.v_to_list_def]
QED

(* ---- v_to_char_list ---- *)
Theorem v_to_char_list_n_agrees:
  ∀v. ∃k0. ∀k. k0 ≤ k ⇒ v_to_char_list_n k v = v_to_char_list v
Proof
  ho_match_mp_tac semanticPrimitivesTheory.v_to_char_list_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.v_to_char_list_n_def,
                 semanticPrimitivesTheory.v_to_char_list_def] \\ NO_TAC)
  \\ Cases_on ‘stamp = TypeStamp «::» list_type_num’ \\ gvs []
  >- (qexists_tac ‘SUC k0’ \\ Cases_on ‘k’ \\ fs []
      \\ rw [fueledSemTheory.v_to_char_list_n_def,
             semanticPrimitivesTheory.v_to_char_list_def]
      \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
      \\ every_case_tac \\ fs [])
  \\ qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.v_to_char_list_n_def,
         semanticPrimitivesTheory.v_to_char_list_def]
QED

(* ---- vs_to_string ---- *)
Theorem vs_to_string_n_agrees:
  ∀vs. ∃k0. ∀k. k0 ≤ k ⇒ vs_to_string_n k vs = vs_to_string vs
Proof
  ho_match_mp_tac semanticPrimitivesTheory.vs_to_string_ind \\ rw []
  \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
          \\ fs [fueledSemTheory.vs_to_string_n_def,
                 semanticPrimitivesTheory.vs_to_string_def] \\ NO_TAC)
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
  >- (Cases_on ‘v’ \\ gvs []
      \\ TRY (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
              \\ fs [fueledSemTheory.concrete_v_n_def,
                     semanticPrimitivesTheory.concrete_v_def] \\ NO_TAC)
      \\ qexists_tac ‘SUC k0’ \\ Cases_on ‘k’
      \\ fs [fueledSemTheory.concrete_v_n_def,
             semanticPrimitivesTheory.concrete_v_def])
  >- (qexists_tac ‘SUC 0’ \\ Cases_on ‘k’
      \\ fs [fueledSemTheory.concrete_v_n_def,
             semanticPrimitivesTheory.concrete_v_def])
  \\ qexists_tac ‘SUC (MAX k0 k0')’ \\ Cases_on ‘k’
  \\ fs [fueledSemTheory.concrete_v_n_def,
         semanticPrimitivesTheory.concrete_v_def, arithmeticTheory.MAX_LE]
QED
