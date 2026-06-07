# A — reset-model compiler upgrade (statement + proof)

Builds against a built `backendProof`; specialises `source_eval_to_flat_semantics` at `ev := SOME ci'`. Kept as documentation (not in selfUpgrade's default build) so the dir stays dependency-light. To build: drop into `compiler/backend/proofs/` (or a dir with `backendProof` on INCLUDES) and `Holmake`.

```sml
(*
  Soundness of a COMPILER SELF-UPGRADE at CakeML's eval semantics.

  Deliverable A (RESET model): re-initialising the eval_state to a fresh
  compiler instance ci' keeps eval-correctness sound, as a corollary of the
  parametric backendProof$source_eval_to_flat_semantics.

  Deliverable B (in-place, history-PRESERVING swap): a generalised
  per-generation oracle-wellformedness invariant and the key PRESERVATION
  lemma for an in-place compiler swap that bumps the eval generation.
*)
Theory evalUpgrade
Ancestors
  backendProof source_evalProof semanticPrimitives backend
Libs
  preamble

(* ------------------------------------------------------------------ *)
(* DELIVERABLE A — the RESET upgrade model                            *)
(* ------------------------------------------------------------------ *)

(* Upgrading the running compiler to ci' = re-initialising the eval state
   to mk_init_eval_state ci'.  The store/refs of s are preserved; the
   eval-environment history is reset.  This is exactly add_eval_state for
   ev = SOME ci'. *)
Definition eval_upgrade_def:
  eval_upgrade ci' s = add_eval_state (SOME ci') s
End

Theorem eval_upgrade_thm:
  eval_upgrade ci' s =
    s with eval_state := SOME (mk_init_eval_state ci')
Proof
  rw [eval_upgrade_def, add_eval_state_def]
QED

(* The store and ffi are untouched by the upgrade. *)
Theorem eval_upgrade_ffi:
  (eval_upgrade ci' s).ffi = s.ffi
Proof
  rw [eval_upgrade_def, add_eval_state_ffi]
QED

Theorem eval_upgrade_refs:
  (eval_upgrade ci' s).refs = s.refs
Proof
  rw [eval_upgrade_thm]
QED

(* The headline: a program run from the UPGRADED state is governed by
   eval-correctness AT ci'.  Specialise the parametric eval-correctness
   theorem at ev := SOME ci'.  Upgrading to ANY ci' that is well-formed
   for the target (opt_eval_config_wf) keeps eval sound: the source
   semantics from the upgraded state is reproduced by the compiled flat
   semantics with the cake oracle for ci'. *)
Theorem eval_upgrade_preserves_semantics:
  ~ semantics_prog (eval_upgrade ci' s0) env prog Fail /\
  compile asm_conf (c : config) prog = SOME (b,bm,c') /\
  source_to_flat$compile prim_src_config (source_to_source$compile prog) = (src_c', p') /\
  THE (prim_sem_env (ffi:'ffi ffi_state)) = (s0, env) /\
  opt_eval_config_wf asm_conf c' (SOME ci') /\
  c.source_conf = prim_src_config ==>
  ? syntax_oracle.
  semantics_prog (eval_upgrade ci' s0) env prog (flatSem$semantics
    (mk_flat_install_conf
        (backend_from_flat_tuple_cc asm_conf c)
        (cake_orac asm_conf c' syntax_oracle (SND o config_tuple1) (\ps. ps.flat_prog)))
    s0.ffi p')
Proof
  rw [eval_upgrade_def]
  \\ irule source_eval_to_flat_semantics
  \\ rpt (first_assum (irule_at Any))
  \\ fs []
QED

(* ------------------------------------------------------------------ *)
(* DELIVERABLE B — the in-place, history-PRESERVING swap              *)
(* ------------------------------------------------------------------ *)

(*
  The existing recorded_orac_wf pins ONE compiler across the whole oracle
  history.  We generalise it to a per-GENERATION compiler map.

  An EvalOracle's oracle entry j carries the (env_id, compiler_state, decs)
  recorded for the j-th eval call; entry 0 is special (it carries the
  current write index and the live compiler_state).  recorded_orac_wf asks
  that each recorded call (1..idx) was produced by the SINGLE pinned
  compiler.  recorded_orac_wf_gen instead takes a function

      g2c : num -> compiler_fun

  assigning a compiler to each generation, together with a function

      gen : num -> num

  telling which generation produced oracle entry j, and asks each recorded
  call be wf for ITS generation's compiler.  When g2c is constant and gen
  is arbitrary this collapses to the original notion.
*)
Definition recorded_orac_wf_gen_def:
  recorded_orac_wf_gen (g2c : num -> compiler_fun) (gen : num -> num)
                       (orac : eval_oracle_fun) <=>
  (0 < FST (FST (orac 0)) ==>
    ?r. g2c (gen (FST (FST (orac 0)))) (orac (FST (FST (orac 0)))) = SOME r /\
        FST (SND (orac 0)) = FST r) /\
  (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
    ?r. g2c (gen j) (orac j) = SOME r /\ FST (SND (orac (j + 1))) = FST r)
End

(* Sanity: the generalised notion subsumes the original.  With a constant
   compiler map it is exactly recorded_orac_wf. *)
Theorem recorded_orac_wf_gen_const:
  recorded_orac_wf_gen (K compiler) gen orac =
  recorded_orac_wf compiler orac
Proof
  rw [recorded_orac_wf_gen_def, recorded_orac_wf_def]
QED

(*
  An in-place swap.  We model "bump the eval generation and install ci'
  for the new generation" at the level of the per-generation compiler map:
  generations strictly below the bump point keep their old compiler; the
  new generation (and above) get ci'.

  gen_set_from n newc g2c   is the map that agrees with g2c below n and is
  newc from n upward.
*)
Definition gen_set_from_def:
  gen_set_from n newc g2c = (\k. if k < n then g2c k else newc)
End

Theorem gen_set_from_below:
  k < n ==> gen_set_from n newc g2c k = g2c k
Proof
  rw [gen_set_from_def]
QED

Theorem gen_set_from_above:
  ~(k < n) ==> gen_set_from n newc g2c k = newc
Proof
  rw [gen_set_from_def]
QED

(*
  KEY PRESERVATION LEMMA.

  Suppose the recorded history is wf for the per-generation map g2c, and
  every recorded oracle entry up to the write index belongs to a generation
  strictly below n (i.e. all already-recorded calls predate the swap point
  n).  Then after swapping in newc for generations >= n (gen_set_from n
  newc g2c), the history is STILL wf: every old recorded entry j has
  gen j < n, so gen_set_from n newc g2c (gen j) = g2c (gen j) by
  gen_set_from_below, and its wf obligation is the unchanged old one.

  This is the heart of the in-place swap: installing a new compiler for a
  fresh generation does not disturb the wellformedness of any previously
  recorded eval call, because those calls are pinned to their own (earlier,
  untouched) generation's compiler.
*)
Theorem swap_preserves_recorded_orac_wf_gen:
  recorded_orac_wf_gen g2c gen orac /\
  (!j. j <= FST (FST (orac 0)) ==> gen j < n) ==>
  recorded_orac_wf_gen (gen_set_from n newc g2c) gen orac
Proof
  rw [recorded_orac_wf_gen_def]
  >- (
    (* entry 0 obligation: idx = FST (FST (orac 0)) is recorded, gen idx < n *)
    first_x_assum (qspec_then `FST (FST (orac 0))` mp_tac)
    \\ rw []
    \\ simp [gen_set_from_below]
  )
  >- (
    (* entry j obligation for 0 < j < idx: gen j < n *)
    last_x_assum (qspec_then `j` mp_tac)
    \\ rw []
    \\ `gen j < n` by (first_x_assum irule \\ simp [])
    \\ simp [gen_set_from_below]
  )
QED

(*
  A corollary phrased as the swap step itself.  Before the swap the live
  generation count is some n (all recorded calls live in generations < n);
  the swap installs newc at generation n via gen_set_from (n+1) ... -- i.e.
  it leaves generations 0..n untouched (those keep g2c) and uses newc only
  from generation n+1 onward when the *next* generation is bumped.  Either
  framing (>= n or > n) is covered: as long as no already-recorded entry's
  generation reaches the swap point, wf is preserved.
*)
Theorem swap_preserves_recorded_orac_wf_gen_strict:
  recorded_orac_wf_gen g2c gen orac /\
  (!j. j <= FST (FST (orac 0)) ==> gen j <= n) ==>
  recorded_orac_wf_gen (gen_set_from (SUC n) newc g2c) gen orac
Proof
  strip_tac
  \\ irule swap_preserves_recorded_orac_wf_gen
  \\ simp []
  \\ rw []
  \\ `gen j <= n` by (first_x_assum irule \\ simp [])
  \\ simp []
QED

(*
  And the new generation IS wf for the new compiler.  After the swap, if a
  future eval call is recorded into a generation >= n with newc, its wf
  obligation is discharged by newc (gen_set_from n newc g2c (gen j) = newc
  for gen j >= n).  We state the local fact that the map yields newc on the
  new generations, which is what threads newc's correctness (proven
  elsewhere for ci') into the future entries' obligations.
*)
Theorem new_generation_uses_newc:
  n <= gen j ==>
  gen_set_from n newc g2c (gen j) = newc
Proof
  rw [gen_set_from_above]
QED

End
```
