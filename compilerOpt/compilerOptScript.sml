(*
  compilerOptScript — a genuinely NEW verified optimization pass for CakeML's
  BVL intermediate language, proven semantics-preserving against the REAL
  `bvlSem$evaluate`, and wired as a CONCRETE proved witness into svenvs's
  self-improvement genealogy.

  THE PASS.  `optimise : bvl$exp -> bvl$exp` recursively eliminates empty
  Let-bindings.  `Let [] e` binds nothing, so evaluating it is the same as
  evaluating `e` in the same environment (the bound-value list is `[]`, which
  prepends nothing to `env`).  The pass rewrites `Let [] e ~> optimise e` and
  otherwise recurses structurally through every constructor of the language.

  WHAT IS PROVED (all against CakeML's actual semantics, zero cheats):

   * `let_nil_correct`  — THE LAW: `evaluate ([Let [] e],env,s) =
       evaluate ([e],env,s)`, directly from the real `evaluate_def`.

   * `optimise_correct` — THE PRIZE, FULL CONGRUENCE:
       `evaluate (MAP optimise xs,env,s) = evaluate (xs,env,s)`,
       proved by induction on the real `evaluate_ind`, handling EVERY
       evaluate equation (cons, Var, If, Let, Raise, Handle, Op, Tick,
       Force, Call) with the genuine fix_clock reasoning.  This is the
       canonical CakeML forward-simulation/preservation proof — not a
       top-only fallback.

   * `optimise_nonincreasing` + `optimise_let_nil_strict` — a node-count cost
     measure, monotone non-increase under the pass, and a strict win on the
     redex: it is a real optimization.

   * GENEALOGY INSTANTIATION.  With
       `ccorrect c <=> !e env s. evaluate ([c e],env,s) = evaluate ([e],env,s)`
     we prove `ccorrect optimise` and then instantiate
     `genealogyTheory.genealogy_sound` to show that an UNBOUNDED forward-
     certified chain of such semantics-preserving BVL passes keeps EVERY
     stage correct.  This upgrades the genealogy's compiler line from CITED
     to a CONCRETE PROVED witness on real CakeML.

  PROVED; no `cheat`/`mk_thm`/`new_axiom`/oracle.
*)

open HolKernel boolLib bossLib BasicProvers;
open preamble arithmeticTheory listTheory cv_transLib cv_stdTheory;
open bvlTheory bvlSemTheory bvlPropsTheory backendPropsTheory;
open certifierTheory genealogyTheory recursiveImprovementTheory;

val _ = new_theory "compilerOpt";
val _ = numLib.prefer_num ();

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "fromAList_def"];

(* ===================================================================== *)
(* (a) THE LAW — against the REAL bvlSem$evaluate.                        *)
(* ===================================================================== *)

(* Evaluating an empty Let is evaluating its body in the same environment.
   evaluate ([Let xs x2],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s1) => evaluate ([x2],vs++env,s1) | res => res
   At xs = [] : evaluate ([],env,s) = (Rval [],s); fix_clock s (Rval [],s)
   simplifies (s.clock = s.clock so MIN is idempotent), and []++env = env. *)
Theorem let_nil_correct:
  !e env s. evaluate ([Let [] e],env,s) = evaluate ([e],env,s)
Proof
  rw[evaluate_def, fix_clock_def]
QED

(* ===================================================================== *)
(* (b) THE PASS — a structural exp -> exp transformation.                 *)
(* ===================================================================== *)

(* `optimise` recurses into every constructor and collapses `Let [] e`.
   Defined mutually with a list companion `optimise_list` (the standard
   CakeML idiom — gives the clean sum-type termination measure), which we
   then prove is literally `MAP optimise`. *)
Definition optimise_def:
  (optimise (Var n) = Var n) /\
  (optimise (If x1 x2 x3) = If (optimise x1) (optimise x2) (optimise x3)) /\
  (optimise (Let xs x2) =
     if xs = [] then optimise x2
     else Let (optimise_list xs) (optimise x2)) /\
  (optimise (Raise x1) = Raise (optimise x1)) /\
  (optimise (Handle x1 x2) = Handle (optimise x1) (optimise x2)) /\
  (optimise (Tick x) = Tick (optimise x)) /\
  (optimise (Call ticks dest xs) = Call ticks dest (optimise_list xs)) /\
  (optimise (Force fl n) = Force fl n) /\
  (optimise (Op op xs) = Op op (optimise_list xs)) /\
  (optimise_list [] = []) /\
  (optimise_list (x::xs) = optimise x :: optimise_list xs)
Termination
  WF_REL_TAC `measure (\x. case x of INL e => exp_size e
                                   | INR es => list_size exp_size es)`
  \\ rw[list_size_def, exp_size_def]
End

(* The list companion is exactly `MAP optimise`. *)
Theorem optimise_list_eq_map:
  !xs. optimise_list xs = MAP optimise xs
Proof
  Induct \\ rw[optimise_def]
QED

(* ===================================================================== *)
(* (c) PASS CORRECTNESS — the full congruence, by recInduct evaluate_ind. *)
(* ===================================================================== *)

Theorem optimise_correct:
  !xs env s. evaluate (MAP optimise xs, env, s) = evaluate (xs, env, s)
Proof
  (* Induction on the REAL evaluate_ind: one case per evaluate equation
     (nil, cons, Var, If, Let, Raise, Handle, Op, Tick, Force, Call).
     `optimise`/`optimise_list` unfold (with optimise_list = MAP optimise),
     the empty-Let case collapses via let_nil_correct (folded into the
     evaluate_def rewrite as the xs=[] branch of evaluate ([Let xs x2],..)),
     and the genuine fix_clock/case reasoning is discharged uniformly. *)
  recInduct evaluate_ind
  \\ rw[optimise_def, optimise_list_eq_map, evaluate_def]
  \\ every_case_tac \\ fs[] \\ rfs[] \\ rw[] \\ fs[]
  \\ fs[let_nil_correct, optimise_def, optimise_list_eq_map, evaluate_def]
QED

(* The single-expression corollary in the form the genealogy wants. *)
Theorem optimise_correct_single:
  !e env s. evaluate ([optimise e],env,s) = evaluate ([e],env,s)
Proof
  rpt gen_tac
  \\ `evaluate (MAP optimise [e],env,s) = evaluate ([e],env,s)`
       by rw[optimise_correct]
  \\ fs[]
QED

(* ===================================================================== *)
(* (d) COST — node count; the pass never increases it, and strictly       *)
(*     decreases it on the empty-Let redex (a real optimization).         *)
(* ===================================================================== *)

Definition cost_def:
  (cost (Var n) = 1n) /\
  (cost (If x1 x2 x3) = 1 + cost x1 + cost x2 + cost x3) /\
  (cost (Let xs x2) = 1 + cost_list xs + cost x2) /\
  (cost (Raise x1) = 1 + cost x1) /\
  (cost (Handle x1 x2) = 1 + cost x1 + cost x2) /\
  (cost (Tick x) = 1 + cost x) /\
  (cost (Call ticks dest xs) = 1 + cost_list xs) /\
  (cost (Force fl n) = 1) /\
  (cost (Op op xs) = 1 + cost_list xs) /\
  (cost_list [] = 0) /\
  (cost_list (x::xs) = cost x + cost_list xs)
Termination
  WF_REL_TAC `measure (\x. case x of INL e => exp_size e
                                   | INR es => list_size exp_size es)`
  \\ rw[list_size_def, exp_size_def]
End

Theorem optimise_nonincreasing:
  (!e. cost (optimise e) <= cost e) /\
  (!es. cost_list (optimise_list es) <= cost_list es)
Proof
  (* Mutual structural induction on the BVL exp datatype (its auto-generated
     induction principle, with one predicate for exps and one for exp lists). *)
  ho_match_mp_tac bvlTheory.exp_induction
  \\ rw[optimise_def, cost_def]
  \\ rw[cost_def] \\ fs[]
QED

(* In the `MAP optimise` form, matching optimise_correct. *)
Theorem optimise_nonincreasing_map:
  (!e. cost (optimise e) <= cost e) /\
  (!es. cost_list (MAP optimise es) <= cost_list es)
Proof
  metis_tac[optimise_nonincreasing, optimise_list_eq_map]
QED

(* Strict improvement on the redex: optimising `Let [] e` is a genuine win. *)
Theorem optimise_let_nil_strict:
  !e. cost (optimise (Let [] e)) < cost (Let [] e)
Proof
  rw[optimise_def, cost_def]
  \\ `cost (optimise e) <= cost e` by rw[optimise_nonincreasing]
  \\ decide_tac
QED

(* ===================================================================== *)
(* (e) GENEALOGY INSTANTIATION — from CITED to a CONCRETE PROVED witness   *)
(*     on real CakeML.                                                     *)
(* ===================================================================== *)

(* A BVL compiler pass is CORRECT iff it preserves bvlSem semantics on every
   expression, in every environment, in every state.

   The bvlSem state `('c,'ffi) state` is polymorphic in its compile-oracle
   and FFI types; a HOL Definition's RHS may not introduce type variables
   absent from the constant's type, so we pin the state to the concrete BVL
   instance `(unit,unit) state` here — a genuine, fully-defined CakeML BVL
   semantics instance.  (The underlying preservation result `optimise_correct`
   is itself fully polymorphic in the state, so it specialises to this and to
   every other instance; see optimise_correct above.) *)
Definition ccorrect_def:
  ccorrect (c:bvl$exp -> bvl$exp) <=>
    !e env (s:(unit,unit) bvlSem$state).
      evaluate ([c e],env,s) = evaluate ([e],env,s)
End

(* `optimise` is such a correct pass — the headline made concrete.  Specialised
   from the fully-polymorphic optimise_correct, so this is no weaker a result. *)
Theorem optimise_is_ccorrect:
  ccorrect optimise
Proof
  rw[ccorrect_def, optimise_correct_single]
QED

(* The identity pass is correct (the genesis/non-strengthening compiler). *)
Theorem id_is_ccorrect:
  ccorrect (\e. e)
Proof
  rw[ccorrect_def]
QED

(* Composition of correct passes is correct: the line is closed under the
   genealogy's forward step for ANY semantics-preserving successor. *)
Theorem ccorrect_compose:
  ccorrect c1 /\ ccorrect c2 ==> ccorrect (c2 o c1)
Proof
  rw[ccorrect_def] \\ fs[]
QED

(* The genealogy vouching relation for the compiler line: a successor pass is
   vouched-for iff IT is itself a semantics-preserving (ccorrect) pass.  Then
   correctness propagates forward unconditionally — this is exactly the shape
   of genealogyTheory.vouch_sound at the BVL-compiler judge type. *)
Definition cvouch_def:
  cvouch (c1:bvl$exp -> bvl$exp) (c2:bvl$exp -> bvl$exp) <=> ccorrect c2
End

Theorem compiler_vouch_sound:
  vouch_sound ccorrect cvouch
Proof
  rw[vouch_sound_def, cvouch_def]
QED

(* THE CONCRETE WITNESS.  Given a CORRECT genesis pass and a forward-certified
   UNBOUNDED succession of BVL passes (each vouched-for, i.e. each itself
   semantics-preserving against the real bvlSem), EVERY pass in the line is
   correct.  Pure genealogy_sound, instantiated at the real BVL compiler.   *)
Theorem compiler_genealogy_keeps_every_stage_correct:
  ccorrect (C 0n) /\ forward_certified cvouch C ==>
  !n. ccorrect (C n)
Proof
  rpt strip_tac
  \\ `vouch_sound ccorrect cvouch` by rw[compiler_vouch_sound]
  \\ metis_tac[genealogy_sound]
QED

(* The concrete genesis: start the line at `optimise` itself.  Anyone can
   instantiate the unbounded chain from this real, proved-correct first pass.*)
Theorem optimise_genesis_chain_correct:
  forward_certified cvouch C /\ (C 0n = optimise) ==>
  !n. ccorrect (C n)
Proof
  rpt strip_tac
  \\ `ccorrect (C 0n)` by rw[optimise_is_ccorrect]
  \\ metis_tac[compiler_genealogy_keeps_every_stage_correct]
QED

(* ===================================================================== *)
(* (e') THE CAPSTONE WIRE-IN — feed this concrete, real-CakeML `ccorrect`  *)
(*      directly into recursiveImprovementTheory's mutual                  *)
(*      verifier+compiler self-improvement theorem.  The recursive         *)
(*      capstone is polymorphic in the compiler-correctness predicate      *)
(*      `ccorrect : 'c -> bool`; here we INSTANTIATE that slot with our    *)
(*      proved-on-real-bvlSem predicate (at compiler type `exp -> exp`).   *)
(*      The upshot: in an unbounded mutual recursion whose every verifier  *)
(*      step certifies a semantics-preserving BVL pass, EVERY stage's      *)
(*      compiler genuinely preserves CakeML's bvlSem$evaluate — no longer  *)
(*      a cited assumption but a discharged property of the real semantics.*)
Theorem recursive_compiler_line_preserves_bvlSem:
  vouch_sound vsound vvouch /\
  (!V c. vsound V /\ vcert_c V c ==> ccorrect c) /\
  vsound (FST (St 0n)) /\ ccorrect (SND (St 0n)) /\
  forward_certified (stage_vouches vvouch vcert_c loader_ok) St ==>
  !n. vsound (FST (St n)) /\
      (!e env (s:(unit,unit) bvlSem$state).
         evaluate ([(SND (St n)) e],env,s) = evaluate ([e],env,s))
Proof
  rpt strip_tac
  \\ `!n. vsound (FST (St n)) /\ ccorrect (SND (St n))`
       by metis_tac[recursive_mutual_self_improvement_is_safe]
  \\ fs[ccorrect_def]
QED

(* And the unconditional optimization regime, made concrete: if the verifier
   only ever certifies semantics-preserving BVL passes and the genesis stage's
   compiler is exactly `optimise`, then every compiler in the unbounded mutual
   recursion preserves the real bvlSem semantics. *)
Theorem recursive_optimise_line_preserves_bvlSem:
  vouch_sound vsound vvouch /\
  (!V c. vsound V /\ vcert_c V c ==> ccorrect c) /\
  vsound (FST (St 0n)) /\ (SND (St 0n) = optimise) /\
  forward_certified (stage_vouches vvouch vcert_c loader_ok) St ==>
  !n. !e env (s:(unit,unit) bvlSem$state).
        evaluate ([(SND (St n)) e],env,s) = evaluate ([e],env,s)
Proof
  rpt strip_tac
  \\ `ccorrect (SND (St 0n))` by metis_tac[optimise_is_ccorrect]
  \\ `!n. vsound (FST (St n)) /\ ccorrect (SND (St n))`
       by metis_tac[recursive_mutual_self_improvement_is_safe]
  \\ fs[ccorrect_def]
QED

(* ===================================================================== *)
(* (f) WHOLE-PROGRAM FFI-TRACE & INSTALL-ORACLE SIMULATION (`Layer B`).   *)
(*     Lifts `optimise` to whole BVL programs (`optimise_prog`), proves   *)
(*     code-table + Install compile-oracle forward simulation             *)
(*     (`evaluate_optimise`), per-Call lifting (`opt_evaluate_Call`), and *)
(*     closes the whole-program observational semantics theorem           *)
(*     `semantics_optimise` / `optimise_prog_semantics`.                  *)
(* ===================================================================== *)

Overload optimise_one = ``compilerOpt$optimise``

Theorem optimise_one_def:
  (optimise_one (Var v) = Var v) /\
  (optimise_one (If x1 x2 x3) =
     If (optimise_one x1) (optimise_one x2) (optimise_one x3)) /\
  (optimise_one (Let xs x2) =
     if xs = [] then optimise_one x2
     else Let (optimise_list xs) (optimise_one x2)) /\
  (optimise_one (Raise x1) = Raise (optimise_one x1)) /\
  (optimise_one (Handle x1 x2) = Handle (optimise_one x1) (optimise_one x2)) /\
  (optimise_one (Op op xs) = Op op (optimise_list xs)) /\
  (optimise_one (Tick x) = Tick (optimise_one x)) /\
  (optimise_one (Force m n) = Force m n) /\
  (optimise_one (Call ticks dest xs) = Call ticks dest (optimise_list xs)) /\
  (optimise_list [] = []) /\
  (optimise_list ((x:bvl$exp)::xs) = optimise_one x :: optimise_list xs)
Proof
  rw[optimise_def]
QED

Definition optimise_sing_def:
  optimise_sing e = optimise_one e
End

Definition optimise_prog_def:
  optimise_prog prog = MAP (\(n,a,e). (n,a,optimise_one e)) prog
End

Theorem optimise_list_eq_MAP:
  !xs. optimise_list xs = MAP optimise_one xs
Proof
  rw[optimise_list_eq_map]
QED

Theorem optimise_list_sing[simp]:
  optimise_list [x] = [optimise_one x]
Proof
  fs[optimise_one_def]
QED

Theorem optimise_one_correct:
  !e env s. evaluate ([optimise_one e],env,s) = evaluate ([e],env,s)
Proof
  rw[optimise_correct_single]
QED

Theorem optimise_sing_correct:
  !e env s. evaluate ([optimise_sing e],env,s) = evaluate ([e],env,s)
Proof
  rw[optimise_sing_def, optimise_one_correct]
QED

Theorem MAP_FST_optimise_prog[simp]:
  MAP FST (optimise_prog prog) = MAP FST prog
Proof
  Induct_on `prog` \\ fs[optimise_prog_def, FORALL_PROD]
QED

Theorem optimise_prog_names:
  MAP FST (optimise_prog prog) = MAP FST prog
Proof
  fs[]
QED

Definition opt_state_rel_def:
  opt_state_rel (s:('c,'ffi) bvlSem$state) (t:('c,'ffi) bvlSem$state) <=>
    t = s with <| code := map (I ## optimise_one) s.code
                ; compile := t.compile
                ; compile_oracle :=
                    (I ## MAP (I ## I ## optimise_one)) o s.compile_oracle |> /\
    s.compile = \cfg prog. t.compile cfg (MAP (I ## I ## optimise_one) prog)
End

val opt_state_rel_alt = opt_state_rel_def;

val opt_state_rel_def = opt_state_rel_def
  |> SIMP_RULE (srw_ss()) [bvlSemTheory.state_component_equality, GSYM CONJ_ASSOC];

Theorem do_app_lemma[local]:
  opt_state_rel s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => do_app op a t1 = Rerr err
    | Rval (v,s2) => ?t2. opt_state_rel s2 t2 /\ do_app op a t1 = Rval (v,t2)
Proof
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [opt_state_rel_def] \\ rveq \\ fs []
    \\ fs [bvlSemTheory.state_component_equality,domain_map]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `s1.compile_oracle 0` \\ fs []
      \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ fs [map_fromAList] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs [] \\ rfs [FORALL_PROD,shift_seq_def])
  \\ strip_tac \\ Cases_on `do_app op a s1` \\ fs []
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [opt_state_rel_alt]
    \\ disch_then (qspecl_then [`map (I ## optimise_one) s1.code`,
        `t1.compile`,`(I ## MAP (I ## I ## optimise_one)) o
          s1.compile_oracle`] mp_tac)
    \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = t1` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [bvlSemTheory.state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [opt_state_rel_alt]
  \\ disch_then (qspecl_then [`map (I ## optimise_one) s1.code`,
      `t1.compile`,`(I ## MAP (I ## I ## optimise_one)) o
        s1.compile_oracle`] mp_tac)
  \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
QED

Theorem find_code_optimise[local]:
  !dest vs code args exp.
    find_code dest vs code = SOME (args,exp) ==>
    find_code dest vs (map (I ## optimise_one) code) =
      SOME (args, optimise_one exp)
Proof
  Cases \\ fs [find_code_def]
  \\ rw [] \\ fs [case_eq_thms,lookup_map] \\ rveq \\ fs []
QED

Theorem evaluate_optimise:
  !es env s1 res t1 s2.
     opt_state_rel s1 t1 /\
     evaluate (es,env,s1) = (res,s2) /\ res <> Rerr (Rabort Rtype_error) ==>
     ?t2. evaluate (optimise_list es,env,t1) = (res,t2) /\ opt_state_rel s2 t2
Proof
  recInduct evaluate_ind \\ rw []
  \\ fs [optimise_one_def,optimise_list_eq_MAP]
  \\ fs [evaluate_def]
  THEN1 (* cons *)
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ rename1 `evaluate ([x],env,s) = (q1,r1)`
    \\ `q1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ gvs [])
    \\ `?u. evaluate ([optimise_one x],env,t1) = (q1,u) /\ opt_state_rel r1 u`
         by (last_x_assum drule \\ disch_then drule \\ rw [] \\ metis_tac [])
    \\ reverse (Cases_on `q1`) \\ gvs []
    \\ Cases_on `evaluate (y::xs,env,r1)` \\ gvs []
    \\ rename1 `evaluate (y::xs,env,r1) = (q2,r2)`
    \\ `q2 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ gvs [])
    \\ `?u2. evaluate (optimise_one y::MAP optimise_one xs,env,u) = (q2,u2) /\
             opt_state_rel r2 u2`
         by (last_x_assum drule \\ disch_then drule \\ rw []
             \\ fs [optimise_list_eq_MAP] \\ metis_tac [])
    \\ qpat_x_assum `evaluate (optimise_one y::_,_,u) = _` (fn th => simp [th])
    \\ Cases_on `q2` \\ gvs [])
  THEN1 (* Var *) (rw [] \\ fs [])
  THEN1 (* If *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Let -- redex (xs = []) and structural *)
   (Cases_on `xs = []` \\ fs [] \\ fs [evaluate_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Raise *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Handle *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Op *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ rveq \\ fs []
    \\ drule do_app_lemma
    \\ disch_then (qspecl_then [`op`,`REVERSE vs`] mp_tac)
    \\ fs [] \\ rw [] \\ fs [])
  THEN1 (* Tick *)
   (`t1.clock = s.clock` by fs [opt_state_rel_def]
    \\ reverse (Cases_on `s.clock = 0`) \\ fs [] \\ rveq \\ fs []
    THEN1
     (`opt_state_rel (dec_clock 1 s) (dec_clock 1 t1)`
        by fs [opt_state_rel_def,dec_clock_def]
      \\ res_tac \\ fs [] \\ res_tac \\ fs []
      \\ rveq \\ fs []
      \\ goal_assum drule \\ fs [])
    \\ qexists_tac `t1` \\ fs [])
  THEN1 (* Force *)
   (gvs [AllCaseEqs(), PULL_EXISTS]
    >- gvs [opt_state_rel_def]
    >- gvs [opt_state_rel_def, find_code_def, AllCaseEqs(), lookup_map]
    \\ rename1 `opt_state_rel s t`
    \\ `opt_state_rel (dec_clock 1 s) (dec_clock 1 t)`
      by gvs [opt_state_rel_def, dec_clock_def]
    \\ gvs [oneline dest_thunk_def, AllCaseEqs(), PULL_EXISTS]
    \\ `FLOOKUP t.refs ptr = SOME (Thunk NotEvaluated v)`
      by gvs [opt_state_rel_def]
    \\ gvs []
    \\ `t.clock <> 0` by gvs [opt_state_rel_def] \\ gvs [PULL_EXISTS]
    \\ `find_code (SOME force_loc) [RefPtr v0 ptr; v] t.code =
           SOME (args, optimise_one exp)`
      by gvs [find_code_def, AllCaseEqs(), opt_state_rel_def, lookup_map]
    \\ gvs []
    \\ first_x_assum drule \\ rw [] \\ gvs []
    \\ goal_assum drule \\ fs [])
  THEN1 (* Call *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
    \\ rename1`find_code _ _ _ = SOME (_,exp)`
    \\ `t2.code = map (I ## optimise_one) s.code /\ t2.clock = s.clock`
          by fs [opt_state_rel_def]
    \\ imp_res_tac find_code_optimise \\ fs []
    THEN1 (* timeout branch *) fs [opt_state_rel_def,dec_clock_def]
    \\ `opt_state_rel (dec_clock (ticks + 1) s) (dec_clock (ticks + 1) t2)`
          by fs [opt_state_rel_def,dec_clock_def]
    \\ first_x_assum drule \\ rw [] \\ gvs []
    \\ goal_assum drule \\ fs [])
QED

Definition optimise_cc_def:
  optimise_cc cc =
     (\cfg prog. cc cfg (MAP (I ## I ## optimise_one) prog))
End

Theorem opt_evaluate_Call:
  evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (optimise_cc cc) k) = (r, s) /\
   r <> Rerr (Rabort Rtype_error) ==>
   ?(s2:('c,'ffi) bvlSem$state).
     evaluate
      ([Call 0 (SOME start) []], [],
        initial_state ffi0 (map (I ## optimise_one) prog)
          ((I ## MAP (I ## I ## optimise_one)) o co)
          cc k) = (r, s2) /\
     s2.ffi = s.ffi /\ s.clock = s2.clock
Proof
  strip_tac \\ fs [optimise_cc_def]
  \\ drule_at (Pat `evaluate _ = _`) evaluate_optimise
  \\ fs [optimise_one_def]
  \\ disch_then (qspec_then
       `initial_state ffi0 (map (I ## optimise_one) prog)
          ((I ## MAP (I ## I ## optimise_one)) o co) cc k` mp_tac)
  \\ impl_tac
  THEN1
   (fs [opt_state_rel_def,initial_state_def,
        bvlSemTheory.state_component_equality,FUN_EQ_THM,FORALL_PROD])
  \\ strip_tac \\ qexists_tac `t2` \\ fs [opt_state_rel_def]
QED

Theorem map_fromAList_optimise:
  map (I ## optimise_one) (fromAList prog) =
  fromAList (MAP (I ## I ## optimise_one) prog)
Proof
  fs [map_fromAList]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem MAP_I_I_optimise_eq_optimise_prog:
  MAP (I ## I ## optimise_one) prog = optimise_prog prog
Proof
  fs [optimise_prog_def] \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem opt_evaluate_Call_no_Fail[local]:
  (!k. FST (evaluate ([Call 0 (SOME start) []], [],
              initial_state ffi0 prog co (optimise_cc cc) k)) <>
       Rerr (Rabort Rtype_error)) ==>
  !k.
    FST (evaluate ([Call 0 (SOME start) []], [],
           initial_state ffi0 (map (I ## optimise_one) prog)
             ((I ## MAP (I ## I ## optimise_one)) o co) cc k)) =
      FST (evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (optimise_cc cc) k)) /\
    (SND (evaluate ([Call 0 (SOME start) []], [],
            initial_state ffi0 (map (I ## optimise_one) prog)
              ((I ## MAP (I ## I ## optimise_one)) o co) cc k))).ffi =
      (SND (evaluate ([Call 0 (SOME start) []], [],
              initial_state ffi0 prog co (optimise_cc cc) k))).ffi
Proof
  strip_tac \\ gen_tac
  \\ first_x_assum (qspec_then `k` mp_tac)
  \\ Cases_on `evaluate ([Call 0 (SOME start) []], [],
                 initial_state ffi0 prog co (optimise_cc cc) k)`
  \\ fs [] \\ strip_tac
  \\ drule_all opt_evaluate_Call
  \\ strip_tac \\ fs []
QED

Theorem semantics_optimise:
  semantics ffi prog co (optimise_cc cc) start <> Fail ==>
  semantics ffi (map (I ## optimise_one) prog)
    ((I ## MAP (I ## I ## optimise_one)) o co) cc start =
  semantics (ffi:'ffi ffi_state) prog co (optimise_cc cc) start
Proof
  simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  \\ drule opt_evaluate_Call_no_Fail
  \\ strip_tac \\ fs []
  \\ `(some res.
        ?k s r outcome.
          evaluate ([Call 0 (SOME start) []],[],
            initial_state ffi (map (I ## optimise_one) prog)
              ((I ## MAP (I ## I ## optimise_one)) o co) cc k) = (r,s) /\
          (case r of
           | Rerr (Rabort Rtimeout_error) => F
           | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
           | _ => outcome = Success) /\
          res = Terminate outcome s.ffi.io_events) =
      (some res.
        ?k s r outcome.
          evaluate ([Call 0 (SOME start) []],[],
            initial_state ffi prog co (optimise_cc cc) k) = (r,s) /\
          (case r of
           | Rerr (Rabort Rtimeout_error) => F
           | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
           | _ => outcome = Success) /\
          res = Terminate outcome s.ffi.io_events)`
    by (AP_TERM_TAC \\ rw [FUN_EQ_THM]
        \\ eq_tac \\ rw []
        \\ first_x_assum (qspec_then `k` mp_tac)
        \\ Cases_on `evaluate ([Call 0 (SOME start) []],[],
                       initial_state ffi prog co (optimise_cc cc) k)`
        \\ Cases_on `evaluate ([Call 0 (SOME start) []],[],
                       initial_state ffi (map (I ## optimise_one) prog)
                         ((I ## MAP (I ## I ## optimise_one)) o co) cc k)`
        \\ fs [] \\ rw [] \\ qexists_tac `k` \\ fs [])
  \\ simp []
QED

Theorem optimise_prog_semantics:
  semantics ffi (fromAList prog) co (optimise_cc cc) start <> Fail ==>
  semantics ffi (fromAList (optimise_prog prog))
    ((I ## MAP (I ## I ## optimise_one)) o co) cc start =
  semantics (ffi:'ffi ffi_state) (fromAList prog) co (optimise_cc cc) start
Proof
  strip_tac
  \\ drule semantics_optimise
  \\ simp [map_fromAList_optimise, MAP_I_I_optimise_eq_optimise_prog]
QED

(* ===================================================================== *)
(* (g) IN-KERNEL VERIFIED COMPUTATION (`cv_compute`) FOR BVL PASS        *)
(*     Translates `optimise`, `cost`, and `optimise_prog` to `:cv` via   *)
(*     `cv_auto_trans` so whole-program BVL optimization and cost        *)
(*     reduction execute inside the HOL4 kernel via `cv_eval`.           *)
(* ===================================================================== *)

val () = cv_auto_trans optimise_def;
val () = cv_auto_trans cost_def;
val () = cv_auto_trans optimise_prog_def;

Definition demo_bvl_prog_def:
  demo_bvl_prog : (num # num # bvl$exp) list =
    [(0, 2, Let [] (If (Let [] (Var 0))
                       (Let [] (Let [] (Var 1)))
                       (Tick (Let [] (Var 0)))));
     (1, 1, Handle (Let [] (Call 0 (SOME 0) [Let [] (Var 0); Let [] (Var 0)]))
                   (Let [] (Var 0)))]
End

val () = cv_auto_trans demo_bvl_prog_def;

Theorem optimise_prog_cv_benchmark:
  optimise_prog demo_bvl_prog =
    [(0, 2, If (Var 0) (Var 1) (Tick (Var 0)));
     (1, 1, Handle (Call 0 (SOME 0) [Var 0; Var 0]) (Var 0))] /\
  cost_list (MAP SND (MAP SND (optimise_prog demo_bvl_prog))) = 10 /\
  cost_list (MAP SND (MAP SND demo_bvl_prog)) = 19
Proof
  CONV_TAC cv_eval
QED

(* ===================================================================== *)
(* (h) CONSTANT FOLDING & DEAD-BRANCH ELIMINATION BVL PASS (`bvl_fold`)  *)
(*     Combines empty-Let elimination with dead-branch elimination on    *)
(*     constant boolean conditions (`Op (BlockOp (Cons (bool_to_tag b)))`) *)
(*     and integer constant folding (`Add`, `Sub`, `Mult`), proven       *)
(*     semantics-preserving against `bvlSem$evaluate` and translated     *)
(*     to `:cv` via `cv_auto_trans`.                                     *)
(* ===================================================================== *)

Definition bvl_mk_if_def:
  bvl_mk_if (c:bvl$exp) (x2:bvl$exp) (x3:bvl$exp) =
    if c = Op (BlockOp (Cons (bool_to_tag T))) [] then x2
    else if c = Op (BlockOp (Cons (bool_to_tag F))) [] then x3
    else If c x2 x3
End

Theorem bvl_mk_if_correct:
  !c x2 x3 env s.
    evaluate ([bvl_mk_if c x2 x3], env, s) = evaluate ([If c x2 x3], env, s)
Proof
  rw [bvl_mk_if_def, evaluate_def, fix_clock_def, Boolv_def,
      backend_commonTheory.bool_to_tag_def]
  \\ fs [Boolv_def, backend_commonTheory.bool_to_tag_def]
QED

Theorem cost_bvl_mk_if:
  !c x2 x3. cost (bvl_mk_if c x2 x3) <= 1 + cost c + cost x2 + cost x3
Proof
  rw [bvl_mk_if_def, cost_def]
QED

Definition bvl_dest_const_def:
  bvl_dest_const (Op (IntOp (Const n)) []) = SOME n /\
  bvl_dest_const _ = NONE
End

Theorem bvl_dest_const_SOME:
  !e n. bvl_dest_const e = SOME n <=> e = Op (IntOp (Const n)) []
Proof
  Cases \\ simp [bvl_dest_const_def]
  \\ Cases_on `o'` \\ simp [bvl_dest_const_def]
  \\ Cases_on `i` \\ Cases_on `l` \\ simp [bvl_dest_const_def]
QED

Definition bvl_mk_op_def:
  bvl_mk_op op (xs:bvl$exp list) =
    case xs of
    | [x1; x2] =>
        (case (bvl_dest_const x1, bvl_dest_const x2) of
         | (SOME n1, SOME n2) =>
             if op = IntOp Add then Op (IntOp (Const (n2 + n1))) []
             else if op = IntOp Sub then Op (IntOp (Const (n2 - n1))) []
             else if op = IntOp Mult then Op (IntOp (Const (n2 * n1))) []
             else Op op xs
         | _ => Op op xs)
    | _ => Op op xs
End

Theorem bvl_mk_op_correct:
  !op xs env s.
    evaluate ([bvl_mk_op op xs], env, s) = evaluate ([Op op xs], env, s)
Proof
  rw [bvl_mk_op_def]
  \\ every_case_tac \\ fs [bvl_dest_const_SOME]
  \\ rw [evaluate_def, fix_clock_def, do_app_def, do_int_app_def]
QED

Theorem cost_bvl_mk_op:
  !op xs. cost (bvl_mk_op op xs) <= 1 + cost_list xs
Proof
  rw [bvl_mk_op_def]
  \\ every_case_tac \\ fs [bvl_dest_const_SOME]
  \\ rw [cost_def]
QED

Definition bvl_fold_def:
  (bvl_fold (Var n) = Var n) /\
  (bvl_fold (If x1 x2 x3) =
     bvl_mk_if (bvl_fold x1) (bvl_fold x2) (bvl_fold x3)) /\
  (bvl_fold (Let xs x2) =
     if xs = [] then bvl_fold x2
     else Let (bvl_fold_list xs) (bvl_fold x2)) /\
  (bvl_fold (Raise x1) = Raise (bvl_fold x1)) /\
  (bvl_fold (Handle x1 x2) = Handle (bvl_fold x1) (bvl_fold x2)) /\
  (bvl_fold (Tick x) = Tick (bvl_fold x)) /\
  (bvl_fold (Call ticks dest xs) = Call ticks dest (bvl_fold_list xs)) /\
  (bvl_fold (Force fl n) = Force fl n) /\
  (bvl_fold (Op op xs) = bvl_mk_op op (bvl_fold_list xs)) /\
  (bvl_fold_list [] = []) /\
  (bvl_fold_list (x::xs) = bvl_fold x :: bvl_fold_list xs)
Termination
  WF_REL_TAC `measure (\x. case x of INL e => exp_size e
                                   | INR es => list_size exp_size es)`
  \\ rw [list_size_def, exp_size_def]
End

Theorem bvl_fold_list_eq_map:
  !xs. bvl_fold_list xs = MAP bvl_fold xs
Proof
  Induct \\ rw [bvl_fold_def]
QED

Theorem bvl_fold_correct:
  !xs env s. evaluate (MAP bvl_fold xs, env, s) = evaluate (xs, env, s)
Proof
  recInduct evaluate_ind
  \\ rw [bvl_fold_def, bvl_fold_list_eq_map, bvl_mk_if_correct,
         bvl_mk_op_correct, evaluate_def]
  \\ every_case_tac \\ fs [] \\ rfs [] \\ rw [] \\ fs []
  \\ fs [let_nil_correct, bvl_fold_def, bvl_fold_list_eq_map,
         bvl_mk_if_correct, bvl_mk_op_correct, evaluate_def]
QED

Theorem bvl_fold_correct_single:
  !e env s. evaluate ([bvl_fold e], env, s) = evaluate ([e], env, s)
Proof
  rpt gen_tac
  \\ `evaluate (MAP bvl_fold [e], env, s) = evaluate ([e], env, s)`
       by rw [bvl_fold_correct]
  \\ fs []
QED

Theorem bvl_fold_is_ccorrect:
  ccorrect bvl_fold
Proof
  rw [ccorrect_def, bvl_fold_correct_single]
QED

Theorem bvl_fold_nonincreasing:
  (!e. cost (bvl_fold e) <= cost e) /\
  (!es. cost_list (bvl_fold_list es) <= cost_list es)
Proof
  ho_match_mp_tac bvlTheory.exp_induction
  \\ rw [bvl_fold_def, cost_def]
  >- (
    `cost (bvl_mk_if (bvl_fold e) (bvl_fold e') (bvl_fold e'')) <=
       1 + cost (bvl_fold e) + cost (bvl_fold e') + cost (bvl_fold e'')`
      by rw [cost_bvl_mk_if]
    \\ decide_tac
  )
  >- (
    `cost (bvl_mk_op o' (bvl_fold_list es)) <=
       1 + cost_list (bvl_fold_list es)`
      by rw [cost_bvl_mk_op]
    \\ decide_tac
  )
QED

Theorem bvl_fold_if_true_strict:
  !x2 x3.
    cost (bvl_fold (If (Op (BlockOp (Cons (bool_to_tag T))) []) x2 x3)) <
    cost (If (Op (BlockOp (Cons (bool_to_tag T))) []) x2 x3)
Proof
  rw [bvl_fold_def, bvl_mk_op_def, bvl_mk_if_def, cost_def]
  \\ `cost (bvl_fold x2) <= cost x2` by rw [bvl_fold_nonincreasing]
  \\ decide_tac
QED

Theorem bvl_fold_add_const_strict:
  !n1 n2.
    cost (bvl_fold (Op (IntOp Add) [Op (IntOp (Const n1)) [];
                                    Op (IntOp (Const n2)) []])) <
    cost (Op (IntOp Add) [Op (IntOp (Const n1)) [];
                          Op (IntOp (Const n2)) []])
Proof
  rw [bvl_fold_def, bvl_mk_op_def, bvl_dest_const_def, cost_def]
QED

Definition bvl_fold_prog_def:
  bvl_fold_prog prog = MAP (\(n,a,e). (n,a,bvl_fold e)) prog
End

Theorem MAP_FST_bvl_fold_prog[simp]:
  MAP FST (bvl_fold_prog prog) = MAP FST prog
Proof
  Induct_on `prog` \\ fs [bvl_fold_prog_def, FORALL_PROD]
QED

Definition bvl_fold_state_rel_def:
  bvl_fold_state_rel (s:('c,'ffi) bvlSem$state) (t:('c,'ffi) bvlSem$state) <=>
    t = s with <| code := map (I ## bvl_fold) s.code
                ; compile := t.compile
                ; compile_oracle :=
                    (I ## MAP (I ## I ## bvl_fold)) o s.compile_oracle |> /\
    s.compile = \cfg prog. t.compile cfg (MAP (I ## I ## bvl_fold) prog)
End

val bvl_fold_state_rel_alt = bvl_fold_state_rel_def;

val bvl_fold_state_rel_def = bvl_fold_state_rel_def
  |> SIMP_RULE (srw_ss()) [bvlSemTheory.state_component_equality, GSYM CONJ_ASSOC];

Theorem do_app_bvl_fold_lemma[local]:
  bvl_fold_state_rel s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => do_app op a t1 = Rerr err
    | Rval (v,s2) => ?t2. bvl_fold_state_rel s2 t2 /\ do_app op a t1 = Rval (v,t2)
Proof
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [bvl_fold_state_rel_def] \\ rveq \\ fs []
    \\ fs [bvlSemTheory.state_component_equality,domain_map]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `s1.compile_oracle 0` \\ fs []
      \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ fs [map_fromAList] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs [] \\ rfs [FORALL_PROD,shift_seq_def])
  \\ strip_tac \\ Cases_on `do_app op a s1` \\ fs []
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [bvl_fold_state_rel_alt]
    \\ disch_then (qspecl_then [`map (I ## bvl_fold) s1.code`,
        `t1.compile`,`(I ## MAP (I ## I ## bvl_fold)) o
          s1.compile_oracle`] mp_tac)
    \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = t1` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [bvlSemTheory.state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [bvl_fold_state_rel_alt]
  \\ disch_then (qspecl_then [`map (I ## bvl_fold) s1.code`,
      `t1.compile`,`(I ## MAP (I ## I ## bvl_fold)) o
        s1.compile_oracle`] mp_tac)
  \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
QED

Theorem find_code_bvl_fold[local]:
  !dest vs code args exp.
    find_code dest vs code = SOME (args,exp) ==>
    find_code dest vs (map (I ## bvl_fold) code) =
      SOME (args, bvl_fold exp)
Proof
  Cases \\ fs [find_code_def]
  \\ rw [] \\ fs [case_eq_thms,lookup_map] \\ rveq \\ fs []
QED

Theorem evaluate_bvl_fold:
  !es env s1 res t1 s2.
     bvl_fold_state_rel s1 t1 /\
     evaluate (es,env,s1) = (res,s2) /\ res <> Rerr (Rabort Rtype_error) ==>
     ?t2. evaluate (bvl_fold_list es,env,t1) = (res,t2) /\ bvl_fold_state_rel s2 t2
Proof
  recInduct evaluate_ind \\ rw []
  \\ fs [bvl_fold_def,bvl_fold_list_eq_map,bvl_mk_if_correct,bvl_mk_op_correct]
  \\ fs [evaluate_def]
  THEN1 (* cons *)
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ rename1 `evaluate ([x],env,s) = (q1,r1)`
    \\ `q1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ gvs [])
    \\ `?u. evaluate ([bvl_fold x],env,t1) = (q1,u) /\ bvl_fold_state_rel r1 u`
         by (last_x_assum drule \\ disch_then drule \\ rw [] \\ metis_tac [])
    \\ reverse (Cases_on `q1`) \\ gvs []
    \\ Cases_on `evaluate (y::xs,env,r1)` \\ gvs []
    \\ rename1 `evaluate (y::xs,env,r1) = (q2,r2)`
    \\ `q2 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ gvs [])
    \\ `?u2. evaluate (bvl_fold y::MAP bvl_fold xs,env,u) = (q2,u2) /\
             bvl_fold_state_rel r2 u2`
         by (last_x_assum drule \\ disch_then drule \\ rw []
             \\ fs [bvl_fold_list_eq_map] \\ metis_tac [])
    \\ qpat_x_assum `evaluate (bvl_fold y::_,_,u) = _` (fn th => simp [th])
    \\ Cases_on `q2` \\ gvs [])
  THEN1 (* Var *) (rw [] \\ fs [])
  THEN1 (* If *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Let *)
   (Cases_on `xs = []` \\ fs [] \\ fs [evaluate_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Raise *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Handle *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [])
  THEN1 (* Op *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ rveq \\ fs []
    \\ drule do_app_bvl_fold_lemma
    \\ disch_then (qspecl_then [`op`,`REVERSE vs`] mp_tac)
    \\ fs [] \\ rw [] \\ fs [])
  THEN1 (* Tick *)
   (`t1.clock = s.clock` by fs [bvl_fold_state_rel_def]
    \\ reverse (Cases_on `s.clock = 0`) \\ fs [] \\ rveq \\ fs []
    THEN1
     (`bvl_fold_state_rel (dec_clock 1 s) (dec_clock 1 t1)`
        by fs [bvl_fold_state_rel_def,dec_clock_def]
      \\ res_tac \\ fs [] \\ res_tac \\ fs []
      \\ rveq \\ fs []
      \\ goal_assum drule \\ fs [])
    \\ qexists_tac `t1` \\ fs [])
  THEN1 (* Force *)
   (gvs [AllCaseEqs(), PULL_EXISTS]
    >- gvs [bvl_fold_state_rel_def]
    >- gvs [bvl_fold_state_rel_def, find_code_def, AllCaseEqs(), lookup_map]
    \\ rename1 `bvl_fold_state_rel s t`
    \\ `bvl_fold_state_rel (dec_clock 1 s) (dec_clock 1 t)`
      by gvs [bvl_fold_state_rel_def, dec_clock_def]
    \\ gvs [oneline dest_thunk_def, AllCaseEqs(), PULL_EXISTS]
    \\ `FLOOKUP t.refs ptr = SOME (Thunk NotEvaluated v)`
      by gvs [bvl_fold_state_rel_def]
    \\ gvs []
    \\ `t.clock <> 0` by gvs [bvl_fold_state_rel_def] \\ gvs [PULL_EXISTS]
    \\ `find_code (SOME force_loc) [RefPtr v0 ptr; v] t.code =
           SOME (args, bvl_fold exp)`
      by gvs [find_code_def, AllCaseEqs(), bvl_fold_state_rel_def, lookup_map]
    \\ gvs []
    \\ first_x_assum drule \\ rw [] \\ gvs []
    \\ goal_assum drule \\ fs [])
  THEN1 (* Call *)
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule \\ rw [] \\ fs [] \\ rveq \\ fs [PULL_EXISTS]
    \\ rename1`find_code _ _ _ = SOME (_,exp)`
    \\ `t2.code = map (I ## bvl_fold) s.code /\ t2.clock = s.clock`
          by fs [bvl_fold_state_rel_def]
    \\ imp_res_tac find_code_bvl_fold \\ fs []
    THEN1 (* timeout branch *) fs [bvl_fold_state_rel_def,dec_clock_def]
    \\ `bvl_fold_state_rel (dec_clock (ticks + 1) s) (dec_clock (ticks + 1) t2)`
          by fs [bvl_fold_state_rel_def,dec_clock_def]
    \\ first_x_assum drule \\ rw [] \\ gvs []
    \\ goal_assum drule \\ fs [])
QED

Definition bvl_fold_cc_def:
  bvl_fold_cc cc =
     (\cfg prog. cc cfg (MAP (I ## I ## bvl_fold) prog))
End

Theorem bvl_fold_evaluate_Call:
  evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (bvl_fold_cc cc) k) = (r, s) /\
   r <> Rerr (Rabort Rtype_error) ==>
   ?(s2:('c,'ffi) bvlSem$state).
     evaluate
      ([Call 0 (SOME start) []], [],
        initial_state ffi0 (map (I ## bvl_fold) prog)
          ((I ## MAP (I ## I ## bvl_fold)) o co)
          cc k) = (r, s2) /\
     s2.ffi = s.ffi /\ s.clock = s2.clock
Proof
  strip_tac \\ fs [bvl_fold_cc_def]
  \\ drule_at (Pat `evaluate _ = _`) evaluate_bvl_fold
  \\ fs [bvl_fold_def]
  \\ disch_then (qspec_then
       `initial_state ffi0 (map (I ## bvl_fold) prog)
          ((I ## MAP (I ## I ## bvl_fold)) o co) cc k` mp_tac)
  \\ impl_tac
  THEN1
   (fs [bvl_fold_state_rel_def,initial_state_def,
        bvlSemTheory.state_component_equality,FUN_EQ_THM,FORALL_PROD])
  \\ strip_tac \\ qexists_tac `t2` \\ fs [bvl_fold_state_rel_def]
QED

Theorem map_fromAList_bvl_fold:
  map (I ## bvl_fold) (fromAList prog) =
  fromAList (MAP (I ## I ## bvl_fold) prog)
Proof
  fs [map_fromAList]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem MAP_I_I_bvl_fold_eq_bvl_fold_prog:
  MAP (I ## I ## bvl_fold) prog = bvl_fold_prog prog
Proof
  fs [bvl_fold_prog_def] \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem bvl_fold_evaluate_Call_no_Fail[local]:
  (!k. FST (evaluate ([Call 0 (SOME start) []], [],
              initial_state ffi0 prog co (bvl_fold_cc cc) k)) <>
       Rerr (Rabort Rtype_error)) ==>
  !k.
    FST (evaluate ([Call 0 (SOME start) []], [],
           initial_state ffi0 (map (I ## bvl_fold) prog)
             ((I ## MAP (I ## I ## bvl_fold)) o co) cc k)) =
      FST (evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (bvl_fold_cc cc) k)) /\
    (SND (evaluate ([Call 0 (SOME start) []], [],
            initial_state ffi0 (map (I ## bvl_fold) prog)
              ((I ## MAP (I ## I ## bvl_fold)) o co) cc k))).ffi =
      (SND (evaluate ([Call 0 (SOME start) []], [],
              initial_state ffi0 prog co (bvl_fold_cc cc) k))).ffi
Proof
  strip_tac \\ gen_tac
  \\ first_x_assum (qspec_then `k` mp_tac)
  \\ Cases_on `evaluate ([Call 0 (SOME start) []], [],
                 initial_state ffi0 prog co (bvl_fold_cc cc) k)`
  \\ fs [] \\ strip_tac
  \\ drule_all bvl_fold_evaluate_Call
  \\ strip_tac \\ fs []
QED

Theorem semantics_bvl_fold:
  semantics ffi prog co (bvl_fold_cc cc) start <> Fail ==>
  semantics ffi (map (I ## bvl_fold) prog)
    ((I ## MAP (I ## I ## bvl_fold)) o co) cc start =
  semantics (ffi:'ffi ffi_state) prog co (bvl_fold_cc cc) start
Proof
  simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  \\ drule bvl_fold_evaluate_Call_no_Fail
  \\ strip_tac \\ fs []
  \\ `(some res.
        ?k s r outcome.
          evaluate ([Call 0 (SOME start) []],[],
            initial_state ffi (map (I ## bvl_fold) prog)
              ((I ## MAP (I ## I ## bvl_fold)) o co) cc k) = (r,s) /\
          (case r of
           | Rerr (Rabort Rtimeout_error) => F
           | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
           | _ => outcome = Success) /\
          res = Terminate outcome s.ffi.io_events) =
      (some res.
        ?k s r outcome.
          evaluate ([Call 0 (SOME start) []],[],
            initial_state ffi prog co (bvl_fold_cc cc) k) = (r,s) /\
          (case r of
           | Rerr (Rabort Rtimeout_error) => F
           | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
           | _ => outcome = Success) /\
          res = Terminate outcome s.ffi.io_events)`
    by (AP_TERM_TAC \\ rw [FUN_EQ_THM]
        \\ eq_tac \\ rw []
        \\ first_x_assum (qspec_then `k` mp_tac)
        \\ Cases_on `evaluate ([Call 0 (SOME start) []],[],
                       initial_state ffi prog co (bvl_fold_cc cc) k)`
        \\ Cases_on `evaluate ([Call 0 (SOME start) []],[],
                       initial_state ffi (map (I ## bvl_fold) prog)
                         ((I ## MAP (I ## I ## bvl_fold)) o co) cc k)`
        \\ fs [] \\ rw [] \\ qexists_tac `k` \\ fs [])
  \\ simp []
QED

Theorem bvl_fold_prog_semantics:
  semantics ffi (fromAList prog) co (bvl_fold_cc cc) start <> Fail ==>
  semantics ffi (fromAList (bvl_fold_prog prog))
    ((I ## MAP (I ## I ## bvl_fold)) o co) cc start =
  semantics (ffi:'ffi ffi_state) (fromAList prog) co (bvl_fold_cc cc) start
Proof
  strip_tac
  \\ drule semantics_bvl_fold
  \\ simp [map_fromAList_bvl_fold, MAP_I_I_bvl_fold_eq_bvl_fold_prog]
QED


(* ===================================================================== *)
(* (i) THEOREM-GATED BVL COMPILER PASS CELL (`compiler_pass_gate`)       *)
(*     Operational pass-upgrade gate over `certifierTheory.cgate`,       *)
(*     with exact necessity iff (`sound_certifier_iff_compiler_pass_gate_safe`) *)
(*     and `cv_eval`-verified multi-pass benchmark.                      *)
(* ===================================================================== *)

Definition compiler_pass_gate_def:
  compiler_pass_gate (cert:bool) (old_pass:bvl$exp -> bvl$exp)
                     (new_pass:bvl$exp -> bvl$exp) =
    cgate cert old_pass new_pass
End

Definition compiler_pass_loop_def:
  compiler_pass_loop (chk:'o -> bool) (init_pass:bvl$exp -> bvl$exp)
                     (offers:('o # (bvl$exp -> bvl$exp)) list) =
    cgate_run chk init_pass offers
End

Theorem compiler_pass_gate_installs:
  cert ==> compiler_pass_gate cert old_pass new_pass = new_pass
Proof
  rw [compiler_pass_gate_def, cgate_installs]
QED

Theorem compiler_pass_gate_rejects:
  ~cert ==> compiler_pass_gate cert old_pass new_pass = old_pass
Proof
  rw [compiler_pass_gate_def, cgate_rejects]
QED

Theorem compiler_pass_gate_preserves_ccorrect:
  sound_certifier chk sem /\ (sem ob ==> ccorrect new_pass) /\
  ccorrect old_pass ==>
  ccorrect (compiler_pass_gate (chk ob) old_pass new_pass)
Proof
  metis_tac [compiler_pass_gate_def, cgate_safe]
QED

Definition bad_bvl_pass_def:
  bad_bvl_pass (e:bvl$exp) = Raise (Op (IntOp (Const 0)) [])
End

Theorem bad_bvl_pass_not_ccorrect:
  ~ccorrect bad_bvl_pass
Proof
  rw [ccorrect_def, bad_bvl_pass_def]
  \\ qexistsl_tac [`Op (IntOp (Const 0)) []`, `[]`, `ARB`]
  \\ rw [evaluate_def, fix_clock_def, do_app_def, do_int_app_def]
QED

Theorem sound_certifier_iff_compiler_pass_gate_safe:
  sound_certifier chk sem <=>
    !ob old_pass new_pass.
      ccorrect old_pass /\ (sem ob ==> ccorrect new_pass) ==>
      ccorrect (compiler_pass_gate (chk ob) old_pass new_pass)
Proof
  eq_tac
  >- metis_tac [compiler_pass_gate_preserves_ccorrect]
  \\ rw [sound_certifier_def] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspecl_then [`ob`, `bvl_fold`, `bad_bvl_pass`] mp_tac)
  \\ simp [bvl_fold_is_ccorrect, bad_bvl_pass_not_ccorrect,
           compiler_pass_gate_def, cgate_def]
QED

Theorem compiler_pass_loop_safe:
  sound_certifier chk sem /\
  EVERY (\(ob,p). sem ob ==> ccorrect p) offers /\
  ccorrect init_pass ==>
  (!n. ccorrect (compiler_pass_loop chk init_pass (TAKE n offers))) /\
  ccorrect (compiler_pass_loop chk init_pass offers)
Proof
  rw [compiler_pass_loop_def]
  \\ metis_tac [cgate_run_safe]
QED

Theorem compiler_pass_loop_safe_iff:
  EVERY (\(ob,p). chk ob ==> ccorrect p) offers <=>
    !init_pass.
      ccorrect init_pass ==>
      !n. ccorrect (compiler_pass_loop chk init_pass (TAKE n offers))
Proof
  qspecl_then [`ccorrect`, `bvl_fold`, `chk`, `offers`] mp_tac cgate_run_safe_iff
  \\ simp [bvl_fold_is_ccorrect, compiler_pass_loop_def]
QED

val () = cv_auto_trans bvl_mk_if_def;
val () = cv_auto_trans bvl_dest_const_def;
val () = cv_auto_trans bvl_mk_op_def;
val () = cv_auto_trans bvl_fold_def;
val () = cv_auto_trans bvl_fold_prog_def;

Definition demo_bvl_fold_prog_def:
  demo_bvl_fold_prog : (num # num # bvl$exp) list =
    [(0, 1,
      Let []
        (If (Let [] (Op (BlockOp (Cons (bool_to_tag T))) []))
            (Let [] (Op (IntOp Add)
                       [Let [] (Op (IntOp (Const 7)) []);
                        Op (IntOp Mult)
                          [Op (IntOp (Const 5)) [];
                           Op (IntOp (Const 7)) []]]))
            (Raise (Var 0))));
     (1, 1,
      If (Op (BlockOp (Cons (bool_to_tag F))) [])
         (Raise (Var 0))
         (Let [] (Op (IntOp Sub)
                    [Op (IntOp (Const 8)) [];
                     Op (IntOp (Const 50)) []])))]
End

val () = cv_auto_trans demo_bvl_fold_prog_def;

Theorem bvl_fold_prog_cv_benchmark:
  bvl_fold_prog demo_bvl_fold_prog =
    [(0, 1, Op (IntOp (Const 42)) []);
     (1, 1, Op (IntOp (Const 42)) [])] /\
  cost_list (MAP SND (MAP SND (bvl_fold_prog demo_bvl_fold_prog))) = 2 /\
  cost_list (MAP SND (MAP SND (optimise_prog demo_bvl_fold_prog))) = 16 /\
  cost_list (MAP SND (MAP SND demo_bvl_fold_prog)) = 21
Proof
  CONV_TAC cv_eval
QED

val _ = export_theory ();
