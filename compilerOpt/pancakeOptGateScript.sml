(* Install a constant-shift folder at the Pancake program boundary.
   An out-of-range shift must retain its dynamic error. *)
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
