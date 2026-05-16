(*
  A concrete instance of the abstract envelope: a pole-balancing cart.

  We use an integer model so every obligation is closed by linear integer
  arithmetic (no real analysis, no cheats) and the system is *executable*
  with EVAL — you can literally run the pole cart inside the logic.

  State  : the pole's angular offset from upright (an int; 0 = balanced).
  Action : a motor command (an int; the envelope restricts it to -1/0/+1).

  Dynamics (discrete, per tick):
    - gravity makes the pole fall *away* from upright by one unit in the
      direction it already leans  (cp_drift);
    - the motor applies twice the authority of gravity, so a correct push
      can always make progress.

      cp_step a u  =  a + cp_drift a - 2*u

  This is the classic double-bang pole model, quantised. Cart position is a
  documented future upgrade axis (see cartpoleUpgradesScript / DESIGN.md).
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory;

val _ = new_theory "cartpole";

(* Gravity: the pole drifts outward by one unit in its lean direction. *)
Definition cp_drift_def:
  cp_drift (a:int) = if 0 < a then 1 else if a < 0 then -1 else 0
End

(* One tick of the (controlled) dynamics. Control authority = 2 > 1 = drift. *)
Definition cp_step_def:
  cp_step (a:int) (u:int) = a + cp_drift a - 2 * u
End

(* Safety: the pole stays within +/- 3 of upright. *)
Definition cp_safe_def:
  cp_safe (a:int) ⇔ -3 ≤ a ∧ a ≤ 3
End

(* The cart starts perfectly balanced. *)
Definition cp_init_def:
  cp_init (a:int) ⇔ (a = 0)
End

(* gravity is bounded by one unit either way. *)
Theorem cp_drift_bound:
  -1 ≤ cp_drift a ∧ cp_drift a ≤ 1
Proof
  rw[cp_drift_def] >> intLib.ARITH_TAC
QED

val _ = export_theory ();
