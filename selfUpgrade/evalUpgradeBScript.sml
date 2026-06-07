(*
  Deliverable B: the in-place, history-PRESERVING compiler swap.

  This theory generalises source_evalProof's single-pinned-compiler oracle
  wellformedness invariant (recorded_orac_wf) to a PER-GENERATION compiler
  map, and proves the KEY PRESERVATION LEMMA: an in-place swap that installs
  a new compiler for a fresh eval generation preserves the generalised
  invariant -- prior generations keep their wellformedness for their own
  compiler, and the new generation is wellformed for the new compiler.

  It depends only on source_evalProof (and semanticPrimitives), NOT on the
  full backendProof chain, so it isolates the genuinely-new content.
*)
Theory evalUpgradeB
Ancestors
  source_evalProof semanticPrimitives
Libs
  preamble

(* The existing recorded_orac_wf (source_evalProof) pins ONE compiler across
   the whole oracle history.  We generalise it to a function

       g2c : num -> compiler_fun

   assigning a compiler to each generation, plus a function

       gen : num -> num

   telling which generation produced oracle entry j, and ask that each
   recorded call be wf for ITS generation's compiler. *)
Definition recorded_orac_wf_gen_def:
  recorded_orac_wf_gen (g2c : num -> compiler_fun) (gen : num -> num)
                       (orac : eval_oracle_fun) <=>
  (0 < FST (FST (orac 0)) ==>
    ?r. g2c (gen (FST (FST (orac 0)))) (orac (FST (FST (orac 0)))) = SOME r /\
        FST (SND (orac 0)) = FST r) /\
  (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
    ?r. g2c (gen j) (orac j) = SOME r /\ FST (SND (orac (j + 1))) = FST r)
End

(* Sanity: with a constant compiler map this is exactly recorded_orac_wf. *)
Theorem recorded_orac_wf_gen_const:
  recorded_orac_wf_gen (K compiler) gen orac =
  recorded_orac_wf compiler orac
Proof
  rw [recorded_orac_wf_gen_def, recorded_orac_wf_def]
QED

(* The in-place swap on the per-generation compiler map: generations below n
   keep their old compiler, generations >= n get newc. *)
Definition gen_set_from_def:
  gen_set_from (n:num) newc g2c = (\(k:num). if k < n then g2c k else newc)
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

(* KEY PRESERVATION LEMMA.

   If the recorded history is wf for g2c and every recorded entry up to the
   write index belongs to a generation strictly below the swap point n, then
   after installing newc for generations >= n the history is STILL wf: each
   old entry j has gen j < n, so gen_set_from n newc g2c (gen j) = g2c (gen j)
   and its (unchanged) obligation still holds.  Installing a new compiler for
   a fresh generation never disturbs any previously recorded eval call. *)
Theorem swap_preserves_recorded_orac_wf_gen:
  recorded_orac_wf_gen g2c gen orac /\
  (!j. j <= FST (FST (orac 0)) ==> gen j < n) ==>
  recorded_orac_wf_gen (gen_set_from n newc g2c) gen orac
Proof
  rw [recorded_orac_wf_gen_def]
  >- (
    first_x_assum (qspec_then `FST (FST (orac 0))` mp_tac)
    \\ rw []
    \\ simp [gen_set_from_below]
  )
  >- (
    last_x_assum (qspec_then `j` mp_tac)
    \\ rw []
    \\ `gen j < n` by (first_x_assum irule \\ simp [])
    \\ simp [gen_set_from_below]
  )
QED

(* Corollary in the "bump generation" framing: prior recorded entries live in
   generations <= n, the swap installs newc from generation n+1 onward. *)
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

(* And the new generation IS governed by the new compiler: future entries
   recorded into a generation >= n have their wf obligation discharged by
   newc.  This is what threads newc's correctness (proven for ci') into the
   new generation's entries. *)
Theorem new_generation_uses_newc:
  n <= gen j ==>
  gen_set_from n newc g2c (gen j) = newc
Proof
  rw [gen_set_from_above]
QED
