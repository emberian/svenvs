(* Gate and compose program rewrites at the Pancake compiler boundary.
   Evaluation equality includes errors, timeouts and the complete state. *)
Theory pancakeOptGate
Ancestors
  panSem wordLang certifier pan_to_target
Libs
  preamble

Definition fold_shift_def:
  fold_shift (panLang$Shift sh (panLang$Const w) n) =
    (case word_sh sh w n of NONE => panLang$Shift sh (panLang$Const w) n
                          | SOME v => panLang$Const v) /\
  fold_shift e = e
End

Theorem eval_fold_shift[simp]:
  panSem$eval s (fold_shift e) = panSem$eval s e
Proof
  Cases_on `e` >> simp[fold_shift_def] >>
  rename1 `panLang$Shift sh arg n` >> Cases_on `arg` >>
  simp[fold_shift_def,panSemTheory.eval_def] >> CASE_TAC >> simp[panSemTheory.eval_def]
QED

Definition pancake_opt_def:
  pancake_opt (panLang$Seq p q) = panLang$Seq (pancake_opt p) (pancake_opt q) /\
  pancake_opt (panLang$Dec v sh e p) = panLang$Dec v sh (fold_shift e) (pancake_opt p) /\
  pancake_opt (panLang$Store a e) = panLang$Store (fold_shift a) (fold_shift e) /\
  pancake_opt (panLang$Assign vk v e) = panLang$Assign vk v (fold_shift e) /\
  pancake_opt (panLang$Return e) = panLang$Return (fold_shift e) /\
  pancake_opt p = p
End

Theorem pancake_opt_pass_sound:
  !p s. panSem$evaluate (pancake_opt p,s) = panSem$evaluate (p,s)
Proof
  ho_match_mp_tac pancake_opt_ind >> rw[pancake_opt_def] >>
  once_rewrite_tac[panSemTheory.evaluate_def] >> simp[]
QED

Theorem pancake_opt_changes_code:
  pancake_opt (panLang$Store (panLang$Const 0w) (panLang$Shift Lsl (panLang$Const (3w:word64)) 2)) = panLang$Store (panLang$Const 0w) (panLang$Const 12w)
Proof
  simp[pancake_opt_def,fold_shift_def,word_sh_def] >> EVAL_TAC
QED

Definition pancake_correct_def:
  pancake_correct (ty:'ffi itself) (pass:64 panLang$prog -> 64 panLang$prog) <=>
    !p (s:(64,'ffi) panSem$state). panSem$evaluate (pass p,s) = panSem$evaluate (p,s)
End

Theorem pancake_gate_preserves:
  sound_certifier chk obligation_holds /\ (obligation_holds ob ==> pancake_correct ty candidate) /\
  pancake_correct ty active ==>
  pancake_correct ty (cgate (chk ob) active candidate)
Proof
  metis_tac[cgate_safe]
QED

Theorem pancake_gate_installs_folder:
  cgate T active pancake_opt = pancake_opt /\ pancake_correct ty pancake_opt
Proof
  simp[cgate_def,pancake_correct_def,pancake_opt_pass_sound]
QED

Theorem discard_body_not_correct:
  ~pancake_correct ty (K panLang$Skip)
Proof
  simp[pancake_correct_def] >>
  qexistsl_tac [`panLang$Break`,`ARB`] >> simp[panSemTheory.evaluate_def]
QED

Theorem pancake_gate_safe_iff:
  sound_certifier chk obligation_holds <=>
    !ob active candidate.
      pancake_correct ty active /\ (obligation_holds ob ==> pancake_correct ty candidate) ==>
      pancake_correct ty (cgate (chk ob) active candidate)
Proof
  irule sound_certifier_iff_cgate_safe >>
  metis_tac[pancake_gate_installs_folder,discard_body_not_correct]
QED

(* Feed transformed function bodies to CakeML's real Pancake backend.
   Nonfunction declarations and every other function field are retained. *)
Definition rewrite_decl_def:
  rewrite_decl pass (panLang$Function fi) = panLang$Function (fi with body := pass fi.body) /\
  rewrite_decl pass d = d
End

Definition gated_compile_prog_def:
  gated_compile_prog chk ob pass asm_conf c ds =
    pan_to_target$compile_prog asm_conf c
      (MAP (rewrite_decl (cgate (chk ob) I pass)) ds)
End

Theorem gated_compile_prog_rejected:
  ~chk ob ==>
  gated_compile_prog chk ob pass asm_conf c ds =
    pan_to_target$compile_prog asm_conf c ds
Proof
  rw[gated_compile_prog_def,cgate_def] >>
  AP_TERM_TAC >>
  Induct_on `ds` >> simp[] >> Cases_on `h` >> simp[rewrite_decl_def] >>
  simp[panLangTheory.fun_decl_component_equality,panLangTheory.fun_decl_accfupds]
QED

Theorem gated_compile_prog_installs:
  chk ob ==>
  gated_compile_prog chk ob pancake_opt asm_conf c ds =
    pan_to_target$compile_prog asm_conf c (MAP (rewrite_decl pancake_opt) ds) /\
  (!p s. panSem$evaluate (pancake_opt p,s) = panSem$evaluate (p,s))
Proof
  simp[gated_compile_prog_def,cgate_def,pancake_opt_pass_sound]
QED

(* ------------------------------------------------------------------------
   The composed optimizer.

   An operand of Op, Cmp or Shift and a load address are read only as words,
   so a rewrite there need only agree on word results. Everywhere else a
   rewrite must agree on the exact result: `x ^ 0` fails on a Struct and `x`
   does not, and `And (Load a) 0` fails on an unmapped address and `0` does
   not.
   ------------------------------------------------------------------------ *)

Definition as_word_def:
  as_word (SOME (panSem$Val (panSem$Word w))) = SOME (w:'a word) /\
  as_word (_:'a panSem$v option) = NONE
End

fun word_cases q =
  Cases_on q >> simp[as_word_def] >>
  TRY (rename1 `SOME vv` >> Cases_on `vv` >> simp[as_word_def] >>
       TRY (rename1 `panSem$Val ll` >> Cases_on `ll` >> simp[as_word_def]))

Theorem as_word_OPTION_MAP[local]:
  as_word (OPTION_MAP ValWord z) = z
Proof
  Cases_on `z` >> simp[as_word_def]
QED

Theorem eval_word_forms[local]:
  (panSem$eval s (panLang$Load sh a) =
     OPTION_BIND (as_word (panSem$eval s a))
       (\w. mem_load sh w s.memaddrs s.memory)) /\
  (panSem$eval s (panLang$Load32 a) =
     OPTION_BIND (as_word (panSem$eval s a))
       (\w. OPTION_MAP (\x. ValWord (w2w x))
              (mem_load_32 s.memory s.memaddrs s.be w))) /\
  (panSem$eval s (panLang$LoadByte a) =
     OPTION_BIND (as_word (panSem$eval s a))
       (\w. OPTION_MAP (\x. ValWord (w2w x))
              (mem_load_byte s.memory s.memaddrs s.be w))) /\
  (panSem$eval s (panLang$Shift h a n) =
     OPTION_MAP ValWord
       (OPTION_BIND (as_word (panSem$eval s a)) (\w. word_sh h w n))) /\
  (panSem$eval s (panLang$Cmp c x y) =
     OPTION_BIND (as_word (panSem$eval s x)) (\w1.
       OPTION_BIND (as_word (panSem$eval s y)) (\w2.
         SOME (ValWord (if word_cmp c w1 w2 then 1w else 0w)))))
Proof
  rpt conj_tac >> simp[Once panSemTheory.eval_def]
  >- (word_cases `panSem$eval s a`)
  >- (word_cases `panSem$eval s a` >> TOP_CASE_TAC >> simp[])
  >- (word_cases `panSem$eval s a` >> TOP_CASE_TAC >> simp[])
  >- (word_cases `panSem$eval s a`)
  >> word_cases `panSem$eval s x` >> word_cases `panSem$eval s y`
QED

Theorem opt_words[local]:
  !es. OPT_MMAP (\e. as_word (panSem$eval s e)) es =
       case OPT_MMAP (panSem$eval s) es of
         NONE => NONE
       | SOME ws =>
           if EVERY (\w. case w of ValWord _ => T | _ => F) ws
           then SOME (MAP (\w. case w of ValWord n => n) ws) else NONE
Proof
  Induct >> simp[OPT_MMAP_def] >> rpt strip_tac >>
  word_cases `panSem$eval s h` >>
  Cases_on `OPT_MMAP (panSem$eval s) es` >> simp[] >> rw[]
QED

Theorem eval_Op_word:
  panSem$eval s (panLang$Op b es) =
    OPTION_MAP ValWord
      (OPTION_BIND (OPT_MMAP (\e. as_word (panSem$eval s e)) es) (word_op b))
Proof
  simp[Once panSemTheory.eval_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[opt_words] >>
  Cases_on `OPT_MMAP (panSem$eval s) es` >> simp[] >> rw[]
QED

(* every successful evaluation is a word *)
Definition word_valued_def:
  word_valued (panLang$Const w) = T /\
  word_valued (panLang$Load sh a) = (sh = One) /\
  word_valued (panLang$Load32 a) = T /\
  word_valued (panLang$LoadByte a) = T /\
  word_valued (panLang$Op b es) = T /\
  word_valued (panLang$Panop p es) = T /\
  word_valued (panLang$Cmp c x y) = T /\
  word_valued (panLang$Shift h x n) = T /\
  word_valued panLang$BaseAddr = T /\
  word_valued panLang$TopAddr = T /\
  word_valued panLang$BytesInWord = T /\
  word_valued (_:'a panLang$exp) = F
End

Theorem word_valued_SOME[local]:
  word_valued e /\ panSem$eval s e = SOME v ==> ?w. v = ValWord w
Proof
  Cases_on `e` >> rw[word_valued_def] >>
  gvs[panSemTheory.eval_def, AllCaseEqs(), Once panSemTheory.mem_load_def,
      optionTheory.OPTION_MAP_EQ_SOME] >>
  TRY (rename1 `s.memory aa` >> Cases_on `s.memory aa` >> simp[]) >>
  metis_tac[]
QED

Theorem word_valued_eval:
  word_valued e ==>
  panSem$eval s e = OPTION_MAP ValWord (as_word (panSem$eval s e))
Proof
  strip_tac >> Cases_on `panSem$eval s e` >> simp[as_word_def] >>
  drule_all word_valued_SOME >> rw[] >> simp[as_word_def]
QED

(* evaluates to a word in EVERY state: no variable, no memory, no partial op *)
Definition exp_pure_def:
  exp_pure (panLang$Const w) = T /\
  exp_pure panLang$BaseAddr = T /\
  exp_pure panLang$TopAddr = T /\
  exp_pure panLang$BytesInWord = T /\
  exp_pure (panLang$Op b es) =
    ((b <> asm$Sub \/ LENGTH es = 2) /\ EVERY exp_pure es) /\
  exp_pure (panLang$Cmp c x y) = (exp_pure x /\ exp_pure y) /\
  exp_pure (panLang$Shift h (x:'a panLang$exp) n) =
    (n < dimindex(:'a) /\ exp_pure x) /\
  exp_pure _ = F
Termination
  wf_rel_tac `measure (panLang$exp_size ARB)` >> rpt strip_tac >>
  imp_res_tac panLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >> decide_tac
End

Theorem exp_pure_words[local]:
  !es. (!e. MEM e es ==> ?w. panSem$eval s e = SOME (ValWord w)) ==>
       ?ws. OPT_MMAP (\e. as_word (panSem$eval s e)) es = SOME ws /\
            LENGTH ws = LENGTH es
Proof
  Induct >> simp[OPT_MMAP_def, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  gvs[as_word_def]
QED

Theorem exp_pure_eval:
  !e (s:('a,'ffi) panSem$state). exp_pure e ==> ?w. panSem$eval s e = SOME (ValWord w)
Proof
  recInduct exp_pure_ind >> rw[exp_pure_def] >>
  TRY (simp[panSemTheory.eval_def] >> NO_TAC)
  >~ [`panLang$Cmp`]
  >- (`?w1. panSem$eval s x = SOME (ValWord w1)` by metis_tac[] >>
      `?w2. panSem$eval s y = SOME (ValWord w2)` by metis_tac[] >>
      simp[eval_word_forms, as_word_def])
  >~ [`panLang$Shift`]
  >- (`?w1. panSem$eval s x = SOME (ValWord w1)` by metis_tac[] >>
      `~(n <> 0 /\ n >= dimindex(:'a))` by decide_tac >>
      simp[eval_word_forms, as_word_def, wordLangTheory.word_sh_def] >>
      Cases_on `h` >> simp[])
  >> `?ws. OPT_MMAP (\e. as_word (panSem$eval s e)) es = SOME ws /\
           LENGTH ws = LENGTH es` by
       (irule exp_pure_words >> fs[EVERY_MEM] >> metis_tac[]) >>
  simp[eval_Op_word] >>
  Cases_on `b` >> gvs[wordLangTheory.word_op_def] >>
  Cases_on `ws` >> gvs[] >> Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]
QED

Definition is_unit_op_def:
  is_unit_op asm$Add = T /\
  is_unit_op asm$Or = T /\
  is_unit_op asm$Xor = T /\
  is_unit_op asm$And = F /\
  is_unit_op asm$Sub = F
End

Theorem word_op_unit_fold[local]:
  is_unit_op b ==>
  ?f. (!ws. word_op b ws = SOME (FOLDR f (0w:'a word) ws)) /\
      (!x. f 0w x = x) /\ (!x. f x 0w = x)
Proof
  Cases_on `b` >> simp[is_unit_op_def, wordLangTheory.word_op_def]
  >- (qexists_tac `word_add` >> simp[])
  >- (qexists_tac `word_or` >> simp[])
  >> qexists_tac `word_xor` >> simp[]
QED

Theorem eval_Const[local]:
  panSem$eval s (panLang$Const c) = SOME (ValWord c)
Proof
  simp[panSemTheory.eval_def]
QED

Theorem filter_zero_fold[local]:
  (!x:'a word. f 0w x = x) ==>
  !es. OPTION_MAP (FOLDR f 0w)
         (OPT_MMAP (\e. as_word (panSem$eval s e))
            (FILTER (\e. e <> panLang$Const 0w) es)) =
       OPTION_MAP (FOLDR f 0w)
         (OPT_MMAP (\e. as_word (panSem$eval s e)) es)
Proof
  strip_tac >> Induct >> simp[] >> qx_gen_tac `h` >>
  Cases_on `h = panLang$Const 0w`
  >- (simp[OPT_MMAP_def, eval_Const, as_word_def] >>
      Cases_on `OPT_MMAP (\e. as_word (panSem$eval s e)) es` >> gvs[])
  >> simp[OPT_MMAP_def] >>
  Cases_on `as_word (panSem$eval s h)` >> simp[] >>
  Cases_on `OPT_MMAP (\e. as_word (panSem$eval s e)) es` >>
  Cases_on `OPT_MMAP (\e. as_word (panSem$eval s e))
              (FILTER (\e. e <> panLang$Const 0w) es)` >>
  gvs[]
QED

Theorem eval_Op_filter[local]:
  is_unit_op b ==>
  panSem$eval s (panLang$Op b (FILTER (\e. e <> panLang$Const 0w) es)) =
  panSem$eval s (panLang$Op b es)
Proof
  strip_tac >> drule word_op_unit_fold >> strip_tac >>
  `!z. OPTION_BIND z (word_op b) = OPTION_MAP (FOLDR f 0w) z`
    by (Cases >> simp[]) >>
  simp[eval_Op_word, filter_zero_fold]
QED

Theorem eval_Op_single[local]:
  is_unit_op b ==>
  panSem$eval s (panLang$Op b [x]) =
    OPTION_MAP ValWord (as_word (panSem$eval s x))
Proof
  strip_tac >> drule word_op_unit_fold >> strip_tac >>
  simp[eval_Op_word, OPT_MMAP_def] >>
  Cases_on `as_word (panSem$eval s x)` >> simp[]
QED

Theorem eval_Op_nil[local]:
  is_unit_op b ==> panSem$eval s (panLang$Op b []) = SOME (ValWord 0w)
Proof
  strip_tac >> drule word_op_unit_fold >> strip_tac >>
  simp[eval_Op_word, OPT_MMAP_def]
QED

Theorem pure_and_fold[local]:
  !es. EVERY exp_pure es ==>
       ?ws. OPT_MMAP (\e. as_word (panSem$eval s e)) es = SOME ws /\
            (MEM (panLang$Const 0w) es ==> FOLDR word_and (~0w) ws = 0w)
Proof
  Induct >> simp[OPT_MMAP_def] >> rpt strip_tac >>
  `?c. panSem$eval s h = SOME (ValWord c)` by metis_tac[exp_pure_eval] >>
  gvs[as_word_def] >> rw[] >> gvs[eval_Const]
QED

Theorem eval_and_zero[local]:
  MEM (panLang$Const 0w) es /\ EVERY exp_pure es ==>
  panSem$eval s (panLang$Op asm$And es) = SOME (ValWord 0w)
Proof
  strip_tac >> drule_then (qspec_then `s` strip_assume_tac) pure_and_fold >>
  gvs[eval_Op_word, wordLangTheory.word_op_def]
QED

Definition const_args_def:
  const_args [] = SOME [] /\
  const_args (panLang$Const w :: es) = OPTION_MAP (CONS w) (const_args es) /\
  const_args _ = NONE
End

Theorem const_args_words[local]:
  !es ws. const_args es = SOME ws ==>
          OPT_MMAP (\e. as_word (panSem$eval s e)) es = SOME ws
Proof
  recInduct const_args_ind >> rw[const_args_def, OPT_MMAP_def] >>
  gvs[eval_Const, as_word_def]
QED

Definition same_op_def:
  same_op b (panLang$Op c es) = (b = c) /\
  same_op b _ = F
End

(* The verified parser folds `((a ^ b) ^ c)` into one n-ary Op, so the rules
   work on the operand list. `wpos` records that the parent reads this result
   only as a word. A leading operand with the same operator is left in place:
   the parser would merge it, so that shape has no concrete syntax. *)
Definition alg_nary_def:
  alg_nary wpos b es =
    case const_args es of
      SOME ws =>
        (case word_op b ws of
           SOME r => panLang$Const r
         | NONE => panLang$Op b es)
    | NONE =>
      if is_unit_op b then
        (case FILTER (\e. e <> panLang$Const 0w) es of
           [] => panLang$Const 0w
         | [x] => if wpos \/ word_valued x then x else panLang$Op b es
         | x::y::rest =>
             if same_op b x then panLang$Op b es
             else panLang$Op b (x::y::rest))
      else if b = asm$And /\ MEM (panLang$Const 0w) es /\ EVERY exp_pure es
      then panLang$Const 0w
      else panLang$Op b es
End

Theorem alg_nary_correct:
  as_word (panSem$eval s (alg_nary wpos b es)) =
    as_word (panSem$eval s (panLang$Op b es)) /\
  (~wpos ==>
   panSem$eval s (alg_nary wpos b es) = panSem$eval s (panLang$Op b es))
Proof
  simp[alg_nary_def] >>
  Cases_on `const_args es` >> simp[]
  >- (Cases_on `is_unit_op b` >> simp[]
      >- (`panSem$eval s (panLang$Op b (FILTER (\e. e <> panLang$Const 0w) es)) =
           panSem$eval s (panLang$Op b es)` by simp[eval_Op_filter] >>
          Cases_on `FILTER (\e. e <> panLang$Const 0w) es` >> gvs[]
          >- gvs[eval_Op_nil, eval_Const]
          >> Cases_on `t` >> gvs[]
          >- (qpat_x_assum `_ = panSem$eval s (panLang$Op b es)` (assume_tac o GSYM) >>
              rw[] >> gvs[eval_Op_single, as_word_OPTION_MAP] >>
              metis_tac[word_valued_eval])
          >> rw[])
      >> rw[] >> gvs[eval_and_zero, eval_Const])
  >> imp_res_tac const_args_words >>
  first_x_assum (qspec_then `s` assume_tac) >>
  simp[eval_Op_word] >>
  Cases_on `word_op b x` >> simp[eval_Const, as_word_def, eval_Op_word]
QED

Definition fold_cmp_def:
  fold_cmp c (panLang$Const a) (panLang$Const b) =
    panLang$Const (if word_cmp c a b then 1w else 0w) /\
  fold_cmp c x y = panLang$Cmp c x y
End

Theorem eval_fold_cmp:
  panSem$eval s (fold_cmp c x y) = panSem$eval s (panLang$Cmp c x y)
Proof
  Cases_on `x` >> Cases_on `y` >> simp[fold_cmp_def, panSemTheory.eval_def]
QED

Definition simp_exp_def:
  simp_exp wpos (panLang$Struct es) = panLang$Struct (MAP (simp_exp F) es) /\
  simp_exp wpos (panLang$Field i e) = panLang$Field i (simp_exp F e) /\
  simp_exp wpos (panLang$Load sh a) = panLang$Load sh (simp_exp T a) /\
  simp_exp wpos (panLang$Load32 a) = panLang$Load32 (simp_exp T a) /\
  simp_exp wpos (panLang$LoadByte a) = panLang$LoadByte (simp_exp T a) /\
  simp_exp wpos (panLang$Op b es) = alg_nary wpos b (MAP (simp_exp T) es) /\
  simp_exp wpos (panLang$Panop p es) = panLang$Panop p (MAP (simp_exp F) es) /\
  simp_exp wpos (panLang$Cmp c x y) = fold_cmp c (simp_exp T x) (simp_exp T y) /\
  simp_exp wpos (panLang$Shift h x n) = fold_shift (panLang$Shift h (simp_exp T x) n) /\
  simp_exp wpos e = e
Termination
  wf_rel_tac `measure (\(w,e). panLang$exp_size ARB e)` >> rpt strip_tac >>
  imp_res_tac panLangTheory.MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >> simp[]
End

Theorem OPT_MMAP_eval_MAP[local]:
  !es. (!e. MEM e es ==> panSem$eval s (f e) = panSem$eval s e) ==>
       OPT_MMAP (panSem$eval s) (MAP f es) = OPT_MMAP (panSem$eval s) es
Proof
  Induct >> simp[OPT_MMAP_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem OPT_MMAP_word_MAP[local]:
  !es. (!e. MEM e es ==>
            as_word (panSem$eval s (f e)) = as_word (panSem$eval s e)) ==>
       OPT_MMAP (\e. as_word (panSem$eval s e)) (MAP f es) =
       OPT_MMAP (\e. as_word (panSem$eval s e)) es
Proof
  Induct >> simp[OPT_MMAP_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem eval_simp_exp:
  !wpos e (s:('a,'ffi) panSem$state).
    as_word (panSem$eval s (simp_exp wpos e)) = as_word (panSem$eval s e) /\
    (~wpos ==> panSem$eval s (simp_exp wpos e) = panSem$eval s e)
Proof
  recInduct simp_exp_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY disch_tac >> TRY gen_tac >>
  TRY (simp[simp_exp_def] >> NO_TAC)
  >~ [`panLang$Struct`]
  >- (`panSem$eval s (panLang$Struct (MAP (simp_exp F) es)) =
       panSem$eval s (panLang$Struct es)` by
        (`OPT_MMAP (panSem$eval s) (MAP (simp_exp F) es) =
          OPT_MMAP (panSem$eval s) es` by (irule OPT_MMAP_eval_MAP >> simp[]) >>
         simp[panSemTheory.eval_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
      simp[simp_exp_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])
  >~ [`panLang$Panop`]
  >- (`panSem$eval s (panLang$Panop p (MAP (simp_exp F) es)) =
       panSem$eval s (panLang$Panop p es)` by
        (`OPT_MMAP (panSem$eval s) (MAP (simp_exp F) es) =
          OPT_MMAP (panSem$eval s) es` by (irule OPT_MMAP_eval_MAP >> simp[]) >>
         simp[panSemTheory.eval_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
      simp[simp_exp_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])
  >~ [`panLang$Op`]
  >- (`panSem$eval s (panLang$Op b (MAP (simp_exp T) es)) =
       panSem$eval s (panLang$Op b es)` by
        (simp[eval_Op_word] >>
         `OPT_MMAP (\e. as_word (panSem$eval s e)) (MAP (simp_exp T) es) =
          OPT_MMAP (\e. as_word (panSem$eval s e)) es`
           by (irule OPT_MMAP_word_MAP >> simp[]) >> simp[]) >>
      simp[simp_exp_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      simp[alg_nary_correct])
  >~ [`panLang$Field`]
  >- simp[simp_exp_def, panSemTheory.eval_def]
  >> simp[simp_exp_def, eval_word_forms, eval_fold_shift, eval_fold_cmp]
QED

(* ------------------------------------------------------------------------
   One traversal, three passes. `walk fe r` rewrites each expression with fe
   and then each statement, bottom-up, with r.
   ------------------------------------------------------------------------ *)

Definition walk_def:
  walk fe r panLang$Skip = r panLang$Skip /\
  walk fe r (panLang$Dec v sh e p) = r (panLang$Dec v sh (fe e) (walk fe r p)) /\
  walk fe r (panLang$Assign k v e) = r (panLang$Assign k v (fe e)) /\
  walk fe r (panLang$Store a e) = r (panLang$Store (fe a) (fe e)) /\
  walk fe r (panLang$Store32 a e) = r (panLang$Store32 (fe a) (fe e)) /\
  walk fe r (panLang$StoreByte a e) = r (panLang$StoreByte (fe a) (fe e)) /\
  walk fe r (panLang$Seq p q) = r (panLang$Seq (walk fe r p) (walk fe r q)) /\
  walk fe r (panLang$If c p q) = r (panLang$If (fe c) (walk fe r p) (walk fe r q)) /\
  walk fe r (panLang$While c p) = r (panLang$While (fe c) (walk fe r p)) /\
  walk fe r panLang$Break = r panLang$Break /\
  walk fe r panLang$Continue = r panLang$Continue /\
  walk fe r (panLang$Call NONE f args) = r (panLang$Call NONE f (MAP fe args)) /\
  walk fe r (panLang$Call (SOME (rt,NONE)) f args) =
    r (panLang$Call (SOME (rt,NONE)) f (MAP fe args)) /\
  walk fe r (panLang$Call (SOME (rt,SOME (eid,ev,h))) f args) =
    r (panLang$Call (SOME (rt,SOME (eid,ev,walk fe r h))) f (MAP fe args)) /\
  walk fe r (panLang$DecCall rt sh f args p) =
    r (panLang$DecCall rt sh f (MAP fe args) (walk fe r p)) /\
  walk fe r (panLang$ExtCall f a b c d) =
    r (panLang$ExtCall f (fe a) (fe b) (fe c) (fe d)) /\
  walk fe r (panLang$Raise eid e) = r (panLang$Raise eid (fe e)) /\
  walk fe r (panLang$Return e) = r (panLang$Return (fe e)) /\
  walk fe r (panLang$ShMemLoad op k v a) = r (panLang$ShMemLoad op k v (fe a)) /\
  walk fe r (panLang$ShMemStore op a e) = r (panLang$ShMemStore op (fe a) (fe e)) /\
  walk fe r panLang$Tick = r panLang$Tick /\
  walk fe r (panLang$Annot a b) = r (panLang$Annot a b)
End

(* Every clause of evaluate_def except While, which would unfold forever. *)
val evaluate_no_while =
  LIST_CONJ (List.filter
    (fn th => not (can (find_term (fn t => is_const t andalso
                                           fst (dest_const t) = "While"))
                       (lhs (concl (SPEC_ALL th)))))
    (CONJUNCTS panSemTheory.evaluate_def));

Theorem walk_correct:
  (!(s:('a,'ffi) panSem$state) e. panSem$eval s (fe e) = panSem$eval s e) /\
  (!p (s:('a,'ffi) panSem$state).
     panSem$evaluate (r p, s) = panSem$evaluate (p, s)) ==>
  !p (s:('a,'ffi) panSem$state).
    panSem$evaluate (walk fe r p, s) = panSem$evaluate (p, s)
Proof
  strip_tac >>
  `!(s:('a,'ffi) panSem$state) es.
     OPT_MMAP (panSem$eval s) (MAP fe es) = OPT_MMAP (panSem$eval s) es` by
    (rpt gen_tac >> irule OPT_MMAP_eval_MAP >> simp[]) >>
  recInduct panSemTheory.evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY disch_tac
  >~ [`panLang$While`]
  >- (fs[walk_def] >>
      once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      Cases_on `panSem$eval s e` >> simp[] >>
      rename1 `panSem$eval s e = SOME vv` >> Cases_on `vv` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val ll)` >> Cases_on `ll` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val (panSem$Word w))` >>
      Cases_on `w = 0w` >> simp[] >>
      Cases_on `s.clock = 0` >> gvs[] >>
      Cases_on `panSem$evaluate (c, dec_clock s)` >> gvs[] >>
      rename1 `panSem$evaluate (c, dec_clock s) = (res, s1)` >>
      Cases_on `res` >> gvs[] >>
      rename1 `SOME rr` >> Cases_on `rr` >> gvs[])
  >~ [`panLang$Seq`]
  >- (fs[walk_def] >> once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      Cases_on `panSem$evaluate (c1,s)` >> gvs[] >> rw[])
  >~ [`panLang$If`]
  >- (fs[walk_def] >> once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      Cases_on `panSem$eval s e` >> simp[] >>
      rename1 `panSem$eval s e = SOME vv` >> Cases_on `vv` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val ll)` >> Cases_on `ll` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val (panSem$Word w))` >>
      first_x_assum (qspec_then `w` mp_tac) >> simp[] >>
      Cases_on `w = 0w` >> simp[])
  >~ [`panLang$Dec`]
  >- (fs[walk_def] >> once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      Cases_on `panSem$eval s e` >> gvs[])
  >~ [`panLang$DecCall`]
  >- (fs[walk_def] >> once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      rpt (TOP_CASE_TAC >> gvs[]))
  >~ [`panLang$Call`]
  >- (Cases_on `caltyp` >> TRY (PairCases_on `x`) >> TRY (Cases_on `x1`) >>
      TRY (PairCases_on `x`) >> fs[walk_def] >>
      once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >>
      rpt (TOP_CASE_TAC >> gvs[]))
  >> simp[walk_def, evaluate_no_while]
QED

(* ------------------------------------------------------------------------
   The three passes: algebraic identities, constant-condition branches, and
   Skip removal.
   ------------------------------------------------------------------------ *)

Definition branch_root_def:
  branch_root (panLang$If (panLang$Const w) p q) = (if w <> 0w then p else q) /\
  branch_root p = p
End

Theorem branch_root_correct:
  !p (s:('a,'ffi) panSem$state).
    panSem$evaluate (branch_root p, s) = panSem$evaluate (p, s)
Proof
  recInduct branch_root_ind >> rw[branch_root_def] >>
  simp[Once panSemTheory.evaluate_def, SimpRHS, panSemTheory.eval_def]
QED

Definition seq_root_def:
  seq_root (panLang$Seq p q) =
    (if p = panLang$Skip then q
     else if q = panLang$Skip then p
     else panLang$Seq p q) /\
  seq_root p = p
End

Theorem evaluate_Seq_Skip[local]:
  panSem$evaluate (panLang$Seq panLang$Skip q, s) = panSem$evaluate (q, s) /\
  panSem$evaluate (panLang$Seq p panLang$Skip, s) = panSem$evaluate (p, s)
Proof
  conj_tac >> simp[Once panSemTheory.evaluate_def]
  >- simp[panSemTheory.evaluate_def]
  >> Cases_on `panSem$evaluate (p,s)` >> simp[] >> rw[panSemTheory.evaluate_def]
QED

Theorem seq_root_correct:
  !p (s:('a,'ffi) panSem$state).
    panSem$evaluate (seq_root p, s) = panSem$evaluate (p, s)
Proof
  Cases >> rw[seq_root_def, evaluate_Seq_Skip]
QED

Definition alg_pass_def:
  alg_pass = walk (simp_exp F) I
End

Definition branch_pass_def:
  branch_pass = walk I branch_root
End

Definition seq_pass_def:
  seq_pass = walk I seq_root
End

Theorem alg_pass_correct:
  pancake_correct ty alg_pass
Proof
  simp[pancake_correct_def, alg_pass_def] >>
  irule walk_correct >> simp[eval_simp_exp]
QED

Theorem branch_pass_correct:
  pancake_correct ty branch_pass
Proof
  simp[pancake_correct_def, branch_pass_def] >>
  irule walk_correct >> simp[branch_root_correct]
QED

Theorem seq_pass_correct:
  pancake_correct ty seq_pass
Proof
  simp[pancake_correct_def, seq_pass_def] >>
  irule walk_correct >> simp[seq_root_correct]
QED

Definition run_passes_def:
  run_passes [] p = p /\
  run_passes (f::fs) p = run_passes fs (f p)
End

Theorem run_passes_correct:
  !fs. EVERY (pancake_correct ty) fs ==> pancake_correct ty (run_passes fs)
Proof
  Induct >> fs[run_passes_def, pancake_correct_def]
QED

Definition opt_passes_def:
  opt_passes = [alg_pass; branch_pass; seq_pass]
End

Theorem opt_passes_correct:
  pancake_correct ty (run_passes opt_passes)
Proof
  irule run_passes_correct >>
  simp[opt_passes_def, alg_pass_correct, branch_pass_correct, seq_pass_correct]
QED

Theorem opt_passes_fires:
  run_passes opt_passes
    (panLang$If
       (panLang$Cmp asm$Equal (panLang$Const 1w) (panLang$Const (1w:word64)))
       (panLang$Seq panLang$Skip
          (panLang$Store (panLang$Const 0w)
             (panLang$Op asm$Xor
                [panLang$Const 0w;
                 panLang$Load One
                   (panLang$Op asm$Add
                      [panLang$Var panLang$Local «b»; panLang$Const 0w])])))
       panLang$Tick) =
  panLang$Store (panLang$Const 0w)
    (panLang$Load One (panLang$Var panLang$Local «b»))
Proof
  EVAL_TAC
QED

Theorem opt_passes_keep_unmapped_load:
  run_passes opt_passes
    (panLang$Return
       (panLang$Op asm$And
          [panLang$Load One (panLang$Const 0w); panLang$Const (0w:word64)])) =
  panLang$Return
    (panLang$Op asm$And
       [panLang$Load One (panLang$Const 0w); panLang$Const 0w])
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Any finite list of gate-admitted passes composes, and the result installs
   into CakeML's Pancake compiler with the source semantics unchanged.
   ------------------------------------------------------------------------ *)

Definition pancake_gate_def:
  pancake_gate chk ob (pass:64 panLang$prog -> 64 panLang$prog) active =
    cgate (chk ob) active (pass o active)
End

Definition gated_pipeline_def:
  gated_pipeline chk active [] = active /\
  gated_pipeline chk active ((ob,pass)::rest) =
    gated_pipeline chk (pancake_gate chk ob pass active) rest
End

Theorem pancake_correct_compose:
  pancake_correct ty f /\ pancake_correct ty g ==> pancake_correct ty (f o g)
Proof
  fs[pancake_correct_def]
QED

Theorem pancake_pipeline_sound:
  !offers active.
    sound_certifier chk obligation_holds /\
    (!ob pass. MEM (ob,pass) offers /\ obligation_holds ob ==>
               pancake_correct ty pass) /\
    pancake_correct ty active ==>
    pancake_correct ty (gated_pipeline chk active offers)
Proof
  Induct >- simp[gated_pipeline_def] >>
  qx_gen_tac `st` >> PairCases_on `st` >> rpt gen_tac >> strip_tac >>
  `obligation_holds st0 ==> pancake_correct ty st1` by
    (strip_tac >> first_x_assum irule >> qexists_tac `st0` >> simp[]) >>
  `!ob pass. MEM (ob,pass) offers /\ obligation_holds ob ==>
             pancake_correct ty pass` by metis_tac[MEM] >>
  `pancake_correct ty (pancake_gate chk st0 st1 active)` by
    (simp[pancake_gate_def] >> irule cgate_safe >> simp[] >>
     qexists_tac `obligation_holds` >> simp[] >> strip_tac >>
     irule pancake_correct_compose >> fs[]) >>
  simp[gated_pipeline_def] >>
  first_x_assum (qspec_then `pancake_gate chk st0 st1 active` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem gated_pipeline_all_admitted:
  !offers active.
    EVERY (chk o FST) offers ==>
    gated_pipeline chk active offers = run_passes (MAP SND offers) o active
Proof
  Induct >- simp[gated_pipeline_def, run_passes_def, FUN_EQ_THM] >>
  Cases >> rw[gated_pipeline_def, pancake_gate_def, cgate_def, run_passes_def,
              FUN_EQ_THM]
QED

Theorem gated_pipeline_none_admitted:
  !offers active.
    EVERY (\st. ~chk (FST st)) offers ==>
    gated_pipeline chk active offers = active
Proof
  Induct >- simp[gated_pipeline_def] >>
  Cases >> rw[gated_pipeline_def, pancake_gate_def, cgate_def]
QED

Definition code_rel_def:
  code_rel f (c:mlstring |-> (mlstring # shape) list # 'a panLang$prog) c' <=>
    !n. FLOOKUP c' n = OPTION_MAP (\(ps,b). (ps,f b)) (FLOOKUP c n)
End

Theorem OPT_MMAP_congr[local]:
  !xs. (!x. MEM x xs ==> f x = g x) ==> OPT_MMAP f xs = OPT_MMAP g xs
Proof
  Induct >> simp[OPT_MMAP_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem eval_upd_code[local]:
  !(s:('a,'ffi) panSem$state) e. panSem$eval (s with code := c) e = panSem$eval s e
Proof
  recInduct panSemTheory.eval_ind >> rw[panSemTheory.eval_def] >>
  `OPT_MMAP (\a. panSem$eval (s with code := c) a) es =
   OPT_MMAP (\a. panSem$eval s a) es` by (irule OPT_MMAP_congr >> simp[]) >>
  simp[]
QED

Theorem eval_upd_code_fn[local]:
  panSem$eval ((s:('a,'ffi) panSem$state) with code := c) = panSem$eval s
Proof
  simp[FUN_EQ_THM, eval_upd_code]
QED

Theorem lookup_code_rel[local]:
  code_rel f c c' ==>
  lookup_code c' fname args =
    OPTION_MAP (\(p,l). (f p,l)) (lookup_code c fname args)
Proof
  rw[code_rel_def, panSemTheory.lookup_code_def] >>
  first_x_assum (qspec_then `fname` assume_tac) >>
  Cases_on `FLOOKUP c fname` >> gvs[] >>
  rename1 `SOME xx` >> PairCases_on `xx` >> rw[]
QED

val state_defs = [panSemTheory.empty_locals_def, panSemTheory.dec_clock_def,
                  panSemTheory.set_var_def, panSemTheory.set_global_def,
                  panSemTheory.set_kvar_def, panSemTheory.sh_mem_load_def,
                  panSemTheory.sh_mem_store_def, panSemTheory.lookup_kvar_def,
                  panSemTheory.is_valid_value_def];

Theorem evaluate_code_rel:
  (!p (s:('a,'ffi) panSem$state).
     panSem$evaluate (f p, s) = panSem$evaluate (p, s)) ==>
  !c' p (s:('a,'ffi) panSem$state).
    code_rel f s.code c' ==>
    panSem$evaluate (p, s with code := c') =
      (FST (panSem$evaluate (p, s)),
       SND (panSem$evaluate (p, s)) with code := c') /\
    (SND (panSem$evaluate (p, s))).code = s.code
Proof
  strip_tac >> gen_tac >>
  recInduct panSemTheory.evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt disch_tac
  >~ [`panLang$While`]
  >- (once_rewrite_tac[panSemTheory.evaluate_def] >> simp[eval_upd_code] >>
      Cases_on `panSem$eval s e` >> simp[] >>
      rename1 `panSem$eval s e = SOME vv` >> Cases_on `vv` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val ll)` >> Cases_on `ll` >> simp[] >>
      rename1 `panSem$eval s e = SOME (panSem$Val (panSem$Word w))` >>
      Cases_on `w = 0w` >> simp[] >>
      Cases_on `s.clock = 0` >> simp[panSemTheory.empty_locals_def] >> gvs[] >>
      `panSem$dec_clock (s with code := c') = panSem$dec_clock s with code := c'`
        by simp[panSemTheory.dec_clock_def] >>
      `code_rel f (panSem$dec_clock s).code c'`
        by simp[panSemTheory.dec_clock_def] >>
      gvs[] >>
      Cases_on `panSem$evaluate (c, panSem$dec_clock s)` >> gvs[] >>
      rename1 `panSem$evaluate (c, panSem$dec_clock s) = (res, s1)` >>
      `s1.code = s.code` by gvs[panSemTheory.dec_clock_def] >>
      Cases_on `res` >> gvs[] >>
      rename1 `SOME rr` >> Cases_on `rr` >> gvs[])
  >~ [`panLang$Seq`]
  >- (once_rewrite_tac[panSemTheory.evaluate_def] >> simp[] >> gvs[] >>
      Cases_on `panSem$evaluate (c1,s)` >> gvs[] >> rw[] >> gvs[])
  >~ [`panLang$Dec`]
  >- (once_rewrite_tac[panSemTheory.evaluate_def] >> simp[eval_upd_code] >>
      Cases_on `panSem$eval s e` >> gvs[] >>
      Cases_on `panSem$evaluate (prog, s with locals := s.locals |+ (v,x))` >>
      gvs[])
  >~ [`panLang$DecCall`]
  >- (fs[] >> simp[evaluate_no_while, eval_upd_code_fn, eval_upd_code] >>
      Cases_on `OPT_MMAP (panSem$eval s) argexps` >> simp[] >>
      rename1 `OPT_MMAP (panSem$eval s) argexps = SOME args` >>
      `lookup_code c' fname args =
       OPTION_MAP (\(p,l). (f p,l)) (lookup_code s.code fname args)`
        by metis_tac[lookup_code_rel] >>
      simp[] >>
      Cases_on `lookup_code s.code fname args` >> simp[] >>
      rename1 `lookup_code s.code fname args = SOME pl` >>
      PairCases_on `pl` >> simp[] >>
      Cases_on `s.clock = 0` >> simp[panSemTheory.empty_locals_def] >> gvs[] >>
      `panSem$dec_clock (s with code := c') with locals := pl1 =
       (panSem$dec_clock s with locals := pl1) with code := c'`
        by simp[panSemTheory.dec_clock_def] >>
      `code_rel f (panSem$dec_clock s).code c'`
        by simp[panSemTheory.dec_clock_def] >>
      gvs[] >>
      Cases_on `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1)` >>
      gvs[] >>
      rename1 `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1) =
               (res, st)` >>
      `st.code = s.code` by gvs[panSemTheory.dec_clock_def] >>
      Cases_on `res` >> gvs[] >>
      rename1 `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1) =
               (SOME rr, st)` >>
      Cases_on `rr` >> gvs[panSemTheory.empty_locals_def] >>
      rw[] >> gvs[panSemTheory.set_var_def] >>
      rpt (pairarg_tac >> gvs[]))
  >~ [`panLang$Call`]
  >- (fs[] >> simp[evaluate_no_while, eval_upd_code_fn, eval_upd_code] >>
      Cases_on `OPT_MMAP (panSem$eval s) argexps` >> simp[] >>
      rename1 `OPT_MMAP (panSem$eval s) argexps = SOME args` >>
      `lookup_code c' fname args =
       OPTION_MAP (\(p,l). (f p,l)) (lookup_code s.code fname args)`
        by metis_tac[lookup_code_rel] >>
      simp[] >>
      Cases_on `lookup_code s.code fname args` >> simp[] >>
      rename1 `lookup_code s.code fname args = SOME pl` >>
      PairCases_on `pl` >> simp[] >>
      Cases_on `s.clock = 0` >> simp[panSemTheory.empty_locals_def] >> gvs[] >>
      `panSem$dec_clock (s with code := c') with locals := pl1 =
       (panSem$dec_clock s with locals := pl1) with code := c'`
        by simp[panSemTheory.dec_clock_def] >>
      `code_rel f (panSem$dec_clock s).code c'`
        by simp[panSemTheory.dec_clock_def] >>
      gvs[] >>
      Cases_on `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1)` >>
      gvs[] >>
      rename1 `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1) =
               (res, st)` >>
      `st.code = s.code` by gvs[panSemTheory.dec_clock_def] >>
      Cases_on `res` >> gvs[] >>
      rename1 `panSem$evaluate (pl0, panSem$dec_clock s with locals := pl1) =
               (SOME rr, st)` >>
      Cases_on `rr` >> gvs[panSemTheory.empty_locals_def] >>
      rpt (TOP_CASE_TAC >> gvs[panSemTheory.set_var_def, panSemTheory.set_global_def,
                               panSemTheory.set_kvar_def]))
  >> simp ([evaluate_no_while, eval_upd_code_fn, eval_upd_code] @ state_defs) >>
  rpt (TOP_CASE_TAC >> fs[])
QED

Theorem eval_code_locals[local]:
  panSem$eval ((s:('a,'ffi) panSem$state) with <|locals := L; code := c|>) e =
  panSem$eval (s with locals := L) e
Proof
  `s with <|locals := L; code := c|> = (s with locals := L) with code := c`
    by simp[panSemTheory.state_component_equality] >>
  pop_assum SUBST1_TAC >> simp[eval_upd_code]
QED

Theorem evaluate_decls_rewrite:
  !(s:('a,'ffi) panSem$state) ds c.
    code_rel f s.code c ==>
    case panSem$evaluate_decls s ds of
      NONE => panSem$evaluate_decls (s with code := c) (MAP (rewrite_decl f) ds) = NONE
    | SOME t =>
        ?c'. panSem$evaluate_decls (s with code := c) (MAP (rewrite_decl f) ds) =
               SOME (t with code := c') /\ code_rel f t.code c'
Proof
  recInduct panSemTheory.evaluate_decls_ind >> rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >> simp[panSemTheory.evaluate_decls_def] >>
      qexists_tac `c` >> simp[])
  >- (rpt strip_tac >>
      simp[rewrite_decl_def, panSemTheory.evaluate_decls_def, eval_code_locals] >>
      Cases_on `panSem$eval (s with locals := FEMPTY) e` >> simp[] >>
      rename1 `panSem$eval _ e = SOME res` >>
      Cases_on `sh = shape_of res` >> simp[] >> gvs[] >>
      first_x_assum (qspec_then `c` mp_tac) >> simp[])
  >> rpt strip_tac >>
  simp[rewrite_decl_def, panSemTheory.evaluate_decls_def] >>
  first_x_assum (qspec_then `c |+ (fi.name,(fi.params,f fi.body))` mp_tac) >>
  impl_tac
  >- (gvs[code_rel_def, FLOOKUP_UPDATE] >> rw[]) >>
  simp[]
QED

Theorem pair_eq_fst_snd[local]:
  (x = (r,t)) <=> (r = FST x /\ t = SND x)
Proof
  Cases_on `x` >> simp[] >> metis_tac[]
QED

Theorem semantics_code_rel:
  (!p (s:('a,'ffi) panSem$state).
     panSem$evaluate (f p, s) = panSem$evaluate (p, s)) /\
  code_rel f (s:('a,'ffi) panSem$state).code c ==>
  panSem$semantics (s with code := c) start = panSem$semantics s start
Proof
  strip_tac >>
  drule_then (qspec_then `c` assume_tac) evaluate_code_rel >>
  `!k. panSem$evaluate (panLang$Call NONE start [], (s with code := c) with clock := k) =
       (FST (panSem$evaluate (panLang$Call NONE start [], s with clock := k)),
        SND (panSem$evaluate (panLang$Call NONE start [], s with clock := k))
          with code := c)` by
    (gen_tac >>
     `(s with code := c) with clock := k = (s with clock := k) with code := c`
       by simp[panSemTheory.state_component_equality] >>
     pop_assum SUBST1_TAC >>
     first_x_assum (qspecl_then [`panLang$Call NONE start []`,`s with clock := k`] mp_tac) >>
     simp[]) >>
  simp[panSemTheory.semantics_def, LET_THM, pair_eq_fst_snd]
QED

Theorem semantics_decls_rewrite:
  pancake_correct (ty:'ffi itself) f /\ (s:(64,'ffi) panSem$state).code = FEMPTY ==>
  panSem$semantics_decls s start (MAP (rewrite_decl f) ds) =
  panSem$semantics_decls s start ds
Proof
  strip_tac >>
  `!p (t:(64,'ffi) panSem$state).
     panSem$evaluate (f p, t) = panSem$evaluate (p, t)` by fs[pancake_correct_def] >>
  `code_rel f s.code FEMPTY` by simp[code_rel_def] >>
  drule_then (qspec_then `ds` mp_tac) evaluate_decls_rewrite >>
  `s with code := FEMPTY = s` by simp[panSemTheory.state_component_equality] >>
  simp[panSemTheory.semantics_decls_def] >>
  Cases_on `panSem$evaluate_decls s ds` >> simp[] >> strip_tac >> simp[] >>
  irule semantics_code_rel >> qexists_tac `f` >> simp[]
QED

Definition gated_compile_pipeline_def:
  gated_compile_pipeline chk offers asm_conf c ds =
    pan_to_target$compile_prog asm_conf c
      (MAP (rewrite_decl (gated_pipeline chk I offers)) ds)
End

Theorem gated_compile_pipeline_installs:
  sound_certifier chk obligation_holds /\
  (!ob pass. MEM (ob,pass) offers /\ obligation_holds ob ==>
             pancake_correct (ty:'ffi itself) pass) /\
  (s:(64,'ffi) panSem$state).code = FEMPTY ==>
  gated_compile_pipeline chk offers asm_conf c ds =
    pan_to_target$compile_prog asm_conf c
      (MAP (rewrite_decl (gated_pipeline chk I offers)) ds) /\
  panSem$semantics_decls s start
      (MAP (rewrite_decl (gated_pipeline chk I offers)) ds) =
    panSem$semantics_decls s start ds
Proof
  strip_tac >> simp[gated_compile_pipeline_def] >>
  irule semantics_decls_rewrite >> simp[] >> qexists_tac `ty` >>
  `pancake_correct ty I` by simp[pancake_correct_def] >>
  irule pancake_pipeline_sound >> simp[] >>
  qexists_tac `obligation_holds` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rewrite_decl_I[local]:
  !ds. MAP (rewrite_decl I) ds = ds
Proof
  Induct >> simp[] >> Cases >> simp[rewrite_decl_def] >>
  simp[panLangTheory.fun_decl_component_equality]
QED

Theorem gated_compile_pipeline_rejected:
  EVERY (\st. ~chk (FST st)) offers ==>
  gated_compile_pipeline chk offers asm_conf c ds =
    pan_to_target$compile_prog asm_conf c ds
Proof
  simp[gated_compile_pipeline_def, gated_pipeline_none_admitted, rewrite_decl_I]
QED

Theorem opt_passes_semantics:
  (s:(64,'ffi) panSem$state).code = FEMPTY ==>
  panSem$semantics_decls s start (MAP (rewrite_decl (run_passes opt_passes)) ds) =
  panSem$semantics_decls s start ds
Proof
  strip_tac >> irule semantics_decls_rewrite >> simp[] >>
  qexists_tac `(:'ffi)` >> simp[opt_passes_correct]
QED

(* Install the concrete composition through the original single-pass API. *)
Theorem gated_compile_prog_installs_opt_passes:
  chk ob /\ (s:(64,'ffi) panSem$state).code = FEMPTY ==>
  gated_compile_prog chk ob (run_passes opt_passes) asm_conf c ds =
    pan_to_target$compile_prog asm_conf c
      (MAP (rewrite_decl (run_passes opt_passes)) ds) /\
  panSem$semantics_decls s start (MAP (rewrite_decl (run_passes opt_passes)) ds) =
    panSem$semantics_decls s start ds
Proof
  simp[gated_compile_prog_def, cgate_def, opt_passes_semantics]
QED

(* ------------------------------------------------------------------------
   Programs that differ only in annotations, `Skip` and the grouping of `Seq`.
   CakeML's parser places location annotations and groups sequences its own
   way, so a printed and reparsed program is compared with the printer's
   input under `canon`, which erases exactly those differences.
   ------------------------------------------------------------------------ *)

Definition seq_app_def:
  seq_app (panLang$Seq a b) q = panLang$Seq a (seq_app b q) /\
  seq_app panLang$Skip q = q /\
  seq_app p q = if q = panLang$Skip then p else panLang$Seq p q
End

Theorem evaluate_Seq_assoc[local]:
  panSem$evaluate (panLang$Seq (panLang$Seq a b) c, s) =
  panSem$evaluate (panLang$Seq a (panLang$Seq b c), s)
Proof
  simp[Once panSemTheory.evaluate_def, SimpLHS] >>
  simp[Once panSemTheory.evaluate_def, SimpLHS] >>
  simp[Once panSemTheory.evaluate_def, SimpRHS] >>
  Cases_on `panSem$evaluate (a,s)` >> simp[] >> rw[] >>
  simp[Once panSemTheory.evaluate_def]
QED

Theorem evaluate_seq_app[local]:
  !p q (s:('a,'ffi) panSem$state).
    panSem$evaluate (seq_app p q, s) = panSem$evaluate (panLang$Seq p q, s)
Proof
  recInduct seq_app_ind >> rw[seq_app_def, evaluate_Seq_Skip] >>
  simp[evaluate_Seq_assoc] >>
  simp[Once panSemTheory.evaluate_def] >> simp[Once panSemTheory.evaluate_def, SimpRHS]
QED

Definition canon_root_def:
  canon_root (panLang$Annot a b) = panLang$Skip /\
  canon_root (panLang$Seq p q) = seq_app p q /\
  canon_root p = p
End

Definition canon_def:
  canon = walk I canon_root
End

Theorem canon_correct:
  pancake_correct ty canon
Proof
  simp[pancake_correct_def, canon_def] >> irule walk_correct >> simp[] >>
  Cases >> simp[canon_root_def, evaluate_seq_app] >>
  simp[panSemTheory.evaluate_def]
QED

Theorem canon_erases:
  canon (panLang$Seq (panLang$Seq (panLang$Annot a b) panLang$Tick)
                     (panLang$Seq panLang$Skip (panLang$Return (panLang$Const (0w:word64))))) =
  panLang$Seq panLang$Tick (panLang$Return (panLang$Const 0w))
Proof
  EVAL_TAC
QED

(* The body of the named function in a declaration list. *)
Definition fun_body_def:
  fun_body n [] = panLang$Skip /\
  fun_body n (panLang$Function fi :: ds) =
    (if fi.name = n then fi.body else fun_body n ds) /\
  fun_body n (panLang$Decl sh v e :: ds) = fun_body n ds
End

Theorem fun_body_rewrite_decl[local]:
  f panLang$Skip = panLang$Skip ==>
  !ds. fun_body n (MAP (rewrite_decl f) ds) = f (fun_body n ds)
Proof
  strip_tac >> Induct >> simp[fun_body_def] >>
  Cases >> rw[fun_body_def, rewrite_decl_def]
QED

Theorem canon_opt_Skip[local]:
  canon panLang$Skip = panLang$Skip /\
  run_passes opt_passes panLang$Skip = panLang$Skip
Proof
  EVAL_TAC
QED

(* A declaration list that agrees with the optimizer's output up to `canon`
   has the source's function bodies and the source's program semantics. *)
Theorem canon_agree_evaluate:
  MAP (rewrite_decl canon) ds' =
    MAP (rewrite_decl canon) (MAP (rewrite_decl (run_passes opt_passes)) ds) ==>
  !n (s:(64,'ffi) panSem$state).
    panSem$evaluate (fun_body n ds', s) = panSem$evaluate (fun_body n ds, s)
Proof
  rpt strip_tac >>
  `canon (fun_body n ds') = canon (run_passes opt_passes (fun_body n ds))` by
    (qpat_x_assum `_ = _`
       (mp_tac o AP_TERM ``fun_body n : 64 panLang$decl list -> 64 panLang$prog``) >>
     rewrite_tac[MATCH_MP fun_body_rewrite_decl (CONJUNCT1 canon_opt_Skip),
                 MATCH_MP fun_body_rewrite_decl (CONJUNCT2 canon_opt_Skip)]) >>
  `!p (t:(64,'ffi) panSem$state). panSem$evaluate (canon p, t) = panSem$evaluate (p, t) /\
     panSem$evaluate (run_passes opt_passes p, t) = panSem$evaluate (p, t)` by
    metis_tac[canon_correct, opt_passes_correct, pancake_correct_def] >>
  metis_tac[]
QED

Theorem canon_agree_semantics_decls:
  MAP (rewrite_decl canon) ds' =
    MAP (rewrite_decl canon) (MAP (rewrite_decl (run_passes opt_passes)) ds) ==>
  !(s:(64,'ffi) panSem$state) start.
    s.code = FEMPTY ==>
    panSem$semantics_decls s start ds' = panSem$semantics_decls s start ds
Proof
  rpt strip_tac >>
  `!xs. panSem$semantics_decls s start (MAP (rewrite_decl canon) xs) =
        panSem$semantics_decls s start xs` by
    (gen_tac >> irule semantics_decls_rewrite >> simp[] >>
     qexists_tac `(:'ffi)` >> simp[canon_correct]) >>
  metis_tac[opt_passes_semantics]
QED

(* The rewrite this gate must refuse: dropping a load under `And _ 0`. On an
   unmapped address the source errors and the rewritten program returns 0. *)
Definition unsound_load_drop_def:
  unsound_load_drop (panLang$Return (panLang$Op b [e; z])) =
    (if b = asm$And /\ z = panLang$Const 0w
     then panLang$Return (panLang$Const 0w)
     else panLang$Return (panLang$Op b [e; z])) /\
  unsound_load_drop p = p
End

Theorem unsound_load_drop_not_correct:
  ~pancake_correct (ty:'ffi itself) unsound_load_drop
Proof
  simp[pancake_correct_def] >>
  qexistsl_tac
    [`panLang$Return
        (panLang$Op asm$And
           [panLang$Load One (panLang$Const 0w); panLang$Const 0w])`,
     `(ARB:(64,'ffi) panSem$state) with memaddrs := {}`] >>
  simp[unsound_load_drop_def, panSemTheory.evaluate_def, panSemTheory.eval_def,
       OPT_MMAP_def, Once panSemTheory.mem_load_def, panSemTheory.shape_of_def,
       panLangTheory.size_of_shape_def]
QED

Theorem unsound_load_drop_rejected:
  sound_certifier chk obligation_holds /\
  (obligation_holds ob ==> pancake_correct ty unsound_load_drop) ==>
  ~chk ob /\ pancake_gate chk ob unsound_load_drop active = active
Proof
  rw[sound_certifier_def, pancake_gate_def, cgate_def] >>
  metis_tac[unsound_load_drop_not_correct]
QED
