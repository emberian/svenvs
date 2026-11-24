(* What the Obend kernel theories share: CakeML's verified parser at 64 bits,
   a machine state whose memory is a word list from address 256, and the
   part of a run that the native drivers also print. *)
Theory pancakeKernel
Ancestors
  panPtreeConversion panSem pancakeOptGate sptree
Libs
  preamble

Definition parse_kernel_def:
  parse_kernel src =
    case parse_topdecs_to_ast src of
      INL (ds:64 panLang$decl list) => SOME ds
    | INR _ => NONE
End

(* A finite map keeps memory small under EVAL across thousands of stores.
   An absent address is never in a kernel state's `memaddrs`. *)
Definition kernel_memory_def:
  kernel_memory t (a:word64) =
    case sptree$lookup (w2n a) t of NONE => Word (0w:word64) | SOME v => v
End

Theorem kernel_memory_update[compute]:
  (a =+ v) (kernel_memory t) = kernel_memory (insert (w2n a) v t)
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, kernel_memory_def,
     sptreeTheory.lookup_insert] >> Cases_on `x = a` >> simp[]
QED

Definition kernel_image_def:
  kernel_image a [] = LN /\
  kernel_image a ((w:word64) :: ws) = insert a (Word w) (kernel_image (a + 8) ws)
End

(* Every word argument is a local, `ws` is the whole of memory from 256, and
   all other fields of `s` are arbitrary. *)
Definition kernel_state_def:
  kernel_state (s:(64,'ffi) panSem$state) args clock (ws:word64 list) =
    s with <| locals := FEMPTY |++ MAP (λ(v,w:word64). (v, ValWord w)) args;
              globals := FEMPTY; clock := clock; be := F;
              memaddrs := {a | 256 <= w2n a /\ w2n a < 256 + 8 * LENGTH ws /\
                               w2n a MOD 8 = 0};
              memory := kernel_memory (kernel_image 256 ws) |>
End

(* The result and the first n words of memory. *)
Definition kernel_obs_def:
  kernel_obs n (r, s:(64,'ffi) panSem$state) =
    (r, GENLIST (λi. case s.memory (n2w (256 + 8 * i)) of
                       Word w => w
                     | _ => 0w) n)
End
