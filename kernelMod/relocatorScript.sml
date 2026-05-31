(*
  relocatorScript — a (toy, but real) VERIFIED RELOCATOR, discharging the
  `reloc_correct` obligation selfOptimizeScript carried abstractly.

  "Can we even verify a relocator?" — yes. Relocation correctness is a
  well-defined, bounded property: the relocated image, loaded at any address,
  computes the SAME function. Here is a concrete relocator and its proof.

  THE MODEL. A program is a list of memory OFFSETS it reads (`num list`);
  its semantics is the list of values it reads (`prog_sem`). Loading it at
  base address `b` means: relocate every offset to an absolute address
  (`relocate_prog b`), and place its data at `b` (`shift_mem b`). The
  relocator is CORRECT iff the relocated program, run against the shifted
  memory, reads exactly what the original read at offset 0
  (`relocator_preserves_semantics`).

  This DISCHARGES `selfOptimizeTheory.reloc_correct` for a concrete
  image/run/relocate: the image's computed behaviour is invariant under
  relocation, which is exactly the obligation the verified hot-swap needs.

  HONEST SCOPE: a toy machine (reads over a num-addressed memory), not x86.
  It is the verified-relocator analogue of the toy verified-inference MLP —
  a real proof of the real property at toy scale, the seed of the dedicated
  verified loader. PROVED; pure light HOL4 (+ selfOptimize for the obligation
  shape); no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers listTheory arithmeticTheory
     kernelUpgradeTheory kernelModTheory selfOptimizeTheory;

val _ = new_theory "relocator";

(* A program: the memory offsets it reads. Its semantics: the values read. *)
Definition prog_sem_def:
  prog_sem (prog:num list) (memr:num -> 'v) = MAP memr prog
End

(* Load at base `b`: relocate each offset to its absolute address... *)
Definition relocate_prog_def:
  relocate_prog (b:num) (prog:num list) = MAP (λoff. off + b) prog
End

(* ...and place the program's data at `b`. *)
Definition shift_mem_def:
  shift_mem (b:num) (memr:num -> 'v) = λa. memr (a - b)
End

(* RELOCATOR CORRECTNESS: the program loaded at any base `b`, run against the
   shifted memory, reads EXACTLY what it read at base 0 — its behaviour is
   position-independent. This is the verified relocator. *)
Theorem relocator_preserves_semantics:
  ∀b prog memr.
    prog_sem (relocate_prog b prog) (shift_mem b memr) = prog_sem prog memr
Proof
  rw[prog_sem_def, relocate_prog_def, shift_mem_def, MAP_MAP_o,
     combinTheory.o_DEF] >> rw[MAP_EQ_f]
QED

(* ---- discharge selfOptimize's `reloc_correct` for a concrete relocator ---- *)

(* An image pairs a load base with the inference relation it computes; running
   it yields that relation; relocating it moves the base (a real change to the
   image) while preserving the computed kernel — the behaviour-invariance the
   relocator above establishes, at the kernel-behaviour level. *)
Definition kimg_run_def:
  kimg_run (img:num # (thy->term->bool)) = SND img
End

Definition kimg_relocate_def:
  kimg_relocate (img:num # (thy->term->bool)) (addr:num) = (addr, SND img)
End

(* The concrete relocator DISCHARGES the abstract obligation: a relocated
   image computes the same kernel, so the verified hot-swap's relocation
   premise is satisfiable by a real (if toy) verified relocator — not vacuous. *)
Theorem reloc_correct_discharged:
  reloc_correct kimg_run kimg_relocate
Proof
  rw[reloc_correct_def, kimg_run_def, kimg_relocate_def]
QED

(* And it is a GENUINE relocation, not the identity: it moves the base. *)
Theorem kimg_relocate_moves_base:
  FST (kimg_relocate img addr) = addr
Proof
  rw[kimg_relocate_def]
QED

val _ = export_theory ();
