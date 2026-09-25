(* =========================================================================
   reflectsem/fueledBridgeLib.sml — tactics for the fueled-mirror bridge.

   Every bridge goal has the shape

     ∃k0. ∀xs k. k0 ≤ k ⇒ F_n k (INJ x) = OUT (f x)

   and is closed the same way: pick a fuel bound above every callee/IH
   bound already in the assumptions (each of the form ∀ys k. b ≤ k ⇒ ...),
   take one more step of fuel, case the fuel, and rewrite both defining
   theorems — the callee agreements fire as conditional rewrites.
   ========================================================================= *)
structure fueledBridgeLib = struct

open HolKernel boolLib bossLib BasicProvers;

val MAX_tm = prim_mk_const {Thy = "arithmetic", Name = "MAX"};

(* the bound b of an assumption  ∀ys k. b ≤ k ⇒ P  (b a variable) *)
fun bound_of_hyp h =
  let
    val (vs, body) = strip_forall h
    val (ant, _) = dest_imp body
    val (b, k) = numSyntax.dest_leq ant
  in
    if is_var b andalso List.exists (aconv k) vs
       andalso not (List.exists (fn v => free_in v b) vs)
    then SOME b else NONE
  end
  handle HOL_ERR _ => NONE;

(* close: witness SUC (MAX of every assumption bound), case the fuel, put
   each bound's k_i ≤ fuel into the assumptions, and rewrite with the
   defining theorems (both sides) *)
fun agree_close defs : tactic =
  W (fn (asl, _) =>
    let
      val bs = Lib.op_mk_set aconv (List.mapPartial bound_of_hyp asl)
      val m = case bs of
                [] => numSyntax.zero_tm
              | _ => List.foldr (fn (b, acc) => list_mk_comb (MAX_tm, [b, acc]))
                                (List.last bs) (List.take (bs, length bs - 1))
    in
      exists_tac (numSyntax.mk_suc m) \\ rpt gen_tac
      \\ W (fn (_, g) =>
            let val (k0k, _) = dest_imp g
                val (_, k) = numSyntax.dest_leq k0k
            in Cases_on [ANTIQUOTE k] end)
      \\ TRY (simp [] \\ NO_TAC)              (* fuel 0: below the bound *)
      \\ disch_then (strip_assume_tac o
                      SIMP_RULE arith_ss [arithmeticTheory.MAX_LE])
      \\ fs defs
    end);

(* close, then finish residual case splits the rewriting leaves behind *)
fun agree_close_cases defs = agree_close defs \\ every_case_tac \\ gvs [];

(* close the goal now or leave it untouched *)
fun agree_triv defs = TRY (agree_close defs \\ NO_TAC);

(* bring in a callee agreement at the given arguments *)
fun agree qs th = qspecl_then qs strip_assume_tac th;

(* instantiate the most recent matching IH, discharge its side conditions
   from the assumptions, and keep its bound *)
fun ih qs = first_x_assum (qspecl_then qs mp_tac) \\ simp [] \\ strip_tac;
fun ih_pat pat = qpat_x_assum pat mp_tac \\ simp [] \\ strip_tac;
fun ih_pat_at pat qs =
  qpat_x_assum pat (qspecl_then qs mp_tac) \\ simp [] \\ strip_tac;

end
