(* Run the proved optimizer on CakeML's own parse of each emitted kernel.

   For each NAME in $PANCAKE_KERNEL_NAMES this reads $PANCAKE_KERNELS/NAME.pnk,
   parses it with the verified parser, applies `run_passes opt_passes`, and
   writes the result to $PANCAKE_KERNELS/opt/NAME.pnk for the native run.

   The printer sits outside the proofs, so two checks bind it to them:
   it must reproduce the original source byte for byte from the parsed AST, and
   the verified parser must read its output back as the optimized AST (up to
   location annotations and the grouping of Seq). *)
Theory pancakeKernelOpt
Ancestors
  panPtreeConversion panSem pancakeOptGate sptree
Libs
  preamble

Definition kernel_body_def:
  kernel_body src =
    case parse_topdecs_to_ast src of
      INL [panLang$Function f] => SOME (f.body:64 panLang$prog)
    | _ => NONE
End

(* Memory is `ws` from address 256, one word per 8 bytes. *)
Definition kernel_state_def:
  kernel_state locals (ws:word64 list) =
    (ARB:(64,unit) panSem$state) with
      <| locals := locals; globals := FEMPTY; clock := 0; be := F;
         memaddrs := {a | 256 <= w2n a /\ w2n a < 256 + 8 * LENGTH ws /\
                          w2n a MOD 8 = 0};
         memory := (λa. Word (EL ((w2n a - 256) DIV 8) ws)) |>
End

Definition kernel_obs_def:
  kernel_obs n (r, s:(64,unit) panSem$state) =
    (r, GENLIST (λi. case s.memory (n2w (256 + 8*i)) of Word w => w) n)
End

(* Use a finite map for the thousands of writes in the cSHAKE permutation.
   This EVAL rule implements ordinary functional update on the same memory. *)
Definition kernel_memory_def:
  kernel_memory t (a:word64) = case sptree$lookup (w2n a) t of NONE => Word (0w:word64) | SOME v => v
End

Theorem kernel_memory_update[local,compute]:
  (a =+ v) (kernel_memory t) = kernel_memory (insert (w2n a) v t)
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, kernel_memory_def,
     sptreeTheory.lookup_insert] >> Cases_on `x = a` >> simp[]
QED

(* SP 800-185 sample 3. The 25-lane state begins at 256, two frame
   blocks at 456, six slice descriptor words at 728, followed by the
   little-endian bytes of "Email Signature" and the message 00 01 02 03. *)
Definition cshake_sample_state_def:
  cshake_sample_state =
    (ARB:(64,unit) panSem$state) with
      <| locals := FEMPTY |+ («base», ValWord 256w) |+ («frame», ValWord 456w)
                          |+ («slices», ValWord 728w);
         globals := FEMPTY; clock := 512; be := F;
         memaddrs := {a | 256 <= w2n a /\ w2n a < 800 /\ w2n a MOD 8 = 0};
         memory := kernel_memory (fromAList
           [(744,Word 776w); (752,Word 15w); (760,Word 792w); (768,Word 4w);
            (776,Word 0x6953206C69616D45w); (784,Word 0x65727574616E67w);
            (792,Word 0x03020100w)]) |>
End

val dir = valOf (OS.Process.getEnv "PANCAKE_KERNELS")
val names =
  String.tokens Char.isSpace
    (Option.getOpt (OS.Process.getEnv "PANCAKE_KERNEL_NAMES",
                    "beltLatch keccakF1600 cshake256"))
val outdir = OS.Path.concat (dir, "opt")
val _ = OS.FileSys.mkDir outdir handle OS.SysErr _ => ()

fun slurp p =
  let val f = TextIO.openIn p val s = TextIO.inputAll f
  in TextIO.closeIn f; s end
fun spit p s =
  let val f = TextIO.openOut p in TextIO.output (f, s); TextIO.closeOut f end
fun value t = rhs (concl (EVAL t))
fun since t0 =
  Real.fmt (StringCvt.FIX (SOME 1)) (Time.toReal (Time.- (Time.now (), t0)))
fun say s = (print (s ^ "\n"); TextIO.flushOut TextIO.stdOut)

fun ctor t = if is_const t then #Name (dest_thy_const t) else ""
fun is_panlang t = is_const t andalso #Thy (dest_thy_const t) = "panLang"

(* AST nodes, not counting location annotations or the Seq that carries them *)
val prog_ty = ``:64 panLang$prog``
val seq_tm = ``panLang$Seq : 64 panLang$prog -> 64 panLang$prog -> 64 panLang$prog``
val skip_tm = ``panLang$Skip : 64 panLang$prog``

fun flatten t acc =
  case strip_comb t of
    (h, [a, b]) => if is_panlang h andalso ctor h = "Seq"
                   then flatten a (flatten b acc) else norm_stmt t :: acc
  | _ => norm_stmt t :: acc
and norm_stmt t =
  let val (h, args) = strip_comb t
  in if is_panlang h andalso type_of t = prog_ty
     then list_mk_comb (h, map (fn a => if type_of a = prog_ty then norm a else a) args)
     else t
  end
and norm t =
  let val parts = List.filter (fn x => ctor (fst (strip_comb x)) <> "Annot")
                              (flatten t [])
  in case parts of
       [] => skip_tm
     | _ => let val r = List.rev parts
            in List.foldl (fn (x, acc) => list_mk_comb (seq_tm, [x, acc]))
                          (hd r) (tl r) end
  end

fun nodes t =
  let val n = ref 0
      fun go t =
        if is_comb t then (go (rator t); go (rand t))
        else if is_panlang t andalso Char.isUpper (String.sub (ctor t, 0)) andalso
                not (mem (ctor t) ["Annot","One","Comb","Local","Global"])
        then n := !n + 1 else ()
  in go t; !n end

(* The emitter's concrete syntax. Anything it cannot print stops the run. *)
fun bad what t = raise Fail ("cannot print " ^ what ^ ": " ^ term_to_string t)
fun word_text w = Arbnum.toString (numSyntax.dest_numeral (rand w))
fun name_text t = stringSyntax.fromHOLstring (rand t)

fun exp_text e emit =
  let val (h, args) = strip_comb e
      fun bin x op_s y =
        (emit "("; exp_text x emit; emit (" " ^ op_s ^ " "); exp_text y emit; emit ")")
  in case (ctor h, args) of
       ("Const", [w]) => emit (word_text w)
     | ("Var", [k, v]) =>
         if ctor k = "Local" then emit (name_text v) else bad "global" e
     | ("Load", [sh, a]) =>
         if ctor sh = "One"
         then (emit "(lds 1 "; exp_text a emit; emit ")") else bad "load shape" e
     | ("LoadByte", [a]) => (emit "(ld8 "; exp_text a emit; emit ")")
     | ("Struct", [l]) =>
         let val (xs, _) = listSyntax.dest_list l
             fun go [] = ()
               | go [x] = exp_text x emit
               | go (x::r) = (exp_text x emit; emit ", "; go r)
         in emit "< "; go xs; emit " >" end
     | ("Op", [b, l]) =>
         (* The parser appends each right operand of a left-nested chain to
            one Op, so a list prints as ((x op y) op z). Sub does not merge. *)
         let val sym = case ctor b of
                 "Add" => "+" | "Sub" => "-" | "And" => "&"
               | "Or" => "|" | "Xor" => "^" | _ => bad "op" e
             val merges = ctor b <> "Sub"
         in case fst (listSyntax.dest_list l) of
              x :: y :: rest =>
                (if not merges andalso not (null rest) then bad "Sub arity" e
                 else if merges andalso ctor (fst (strip_comb x)) = "Op" andalso
                         ctor (hd (snd (strip_comb x))) = ctor b
                 then bad "leading operand with the same operator" e else ();
                 List.app (fn _ => emit "(") (y :: rest);
                 exp_text x emit;
                 List.app (fn z => (emit (" " ^ sym ^ " "); exp_text z emit; emit ")"))
                          (y :: rest))
            | _ => bad "operator arity" e
         end
     | ("Cmp", [c, x, y]) =>
         bin x (case ctor c of "Equal" => "==" | "NotEqual" => "!=" | "Lower" => "<+"
                             | "NotLower" => ">=+" | "Less" => "<" | "NotLess" => ">="
                             | _ => bad "comparison" e) y
     | ("Shift", [s, x, n]) =>
         (emit "("; exp_text x emit;
          emit (" " ^ (case ctor s of "Lsl" => "<<" | "Lsr" => ">>>" | "Asr" => ">>"
                                    | "Ror" => "#>>" | _ => bad "shift" e) ^ " ");
          emit (Arbnum.toString (numSyntax.dest_numeral n)); emit ")")
     | _ => bad "expression" e
  end

fun stmt_text p emit =
  let val (h, args) = strip_comb p
      (* removing Skip can leave a block with only annotations *)
      fun body q =
        let val acc = ref []
            val _ = stmt_text q (fn x => acc := x :: !acc)
        in if null (!acc) then emit "skip;\n" else List.app emit (List.rev (!acc)) end
      fun block q = (emit "{\n"; body q; emit "}")
  in case (ctor h, args) of
       ("Annot", _) => ()
     | ("Skip", []) => emit "skip;\n"
     | ("Seq", [a, b]) => (stmt_text a emit; stmt_text b emit)
     | ("Dec", [v, sh, e, q]) =>
         if ctor sh <> "One" then bad "declaration shape" p else
         (emit "{\nvar 1 "; emit (name_text v); emit " = "; exp_text e emit;
          emit ";\n"; body q; emit "};\n")
     | ("Assign", [k, v, e]) =>
         if ctor k <> "Local" then bad "global assignment" p else
         (emit (name_text v); emit " = "; exp_text e emit; emit ";\n")
     | ("Store", [a, e]) =>
         (emit "st "; exp_text a emit; emit ", "; exp_text e emit; emit ";\n")
     | ("StoreByte", [a, e]) =>
         (emit "st8 "; exp_text a emit; emit ", "; exp_text e emit; emit ";\n")
     | ("If", [c, a, b]) =>
         (emit "if "; exp_text c emit; emit " "; block a; emit " else ";
          block b; emit "\n")
     | ("While", [c, a]) =>
         (emit "while "; exp_text c emit; emit " "; block a; emit "\n")
     | ("Return", [e]) => (emit "return "; exp_text e emit; emit ";\n")
     | _ => bad "statement" p
  end

fun body_text body =
  let val acc = ref [] in
    stmt_text body (fn s => acc := s :: !acc);
    String.concat (List.rev (!acc))
  end

(* the source is `<header>{\n<body>}\n` *)
fun split_source src =
  let val marker = ") {\n"
      fun find i = if String.substring (src, i, size marker) = marker then i
                   else find (i + 1)
      val i = find 0 + size marker
  in if String.isSuffix "}\n" src
     then (String.substring (src, 0, i),
           String.substring (src, i, size src - i - 2))
     else raise Fail "source does not end in a closing brace"
  end

fun parse_body name src =
  let val b = value “kernel_body ^(stringSyntax.fromMLstring src)”
  in if optionSyntax.is_some b then optionSyntax.dest_some b
     else raise Fail (name ^ ": the verified parser rejected the source")
  end

(* Evaluate a kernel in the logic. Stores change only memory, so the memory is
   normalized to a word list between them to keep the terms small. *)
fun top_steps t =
  case strip_comb t of
    (h, [a, b]) => if ctor h = "Seq" then a :: top_steps b else [t]
  | _ => [t]

fun run_steps n locals [] _ = raise Fail "the program ran past its last statement"
  | run_steps n locals (p::ps) ws =
      let val res = value “kernel_obs ^(numSyntax.term_of_int n)
                             (panSem$evaluate (^p, kernel_state ^locals ^ws))”
          val (r, out) = pairSyntax.dest_pair res
      in if not (optionSyntax.is_none r) then (r, out)
         else if ctor (fst (strip_comb p)) = "Store" then run_steps n locals ps out
         else raise Fail "a statement other than a store fell through"
      end

fun word_terms ns =
  listSyntax.mk_list (map (fn x => wordsSyntax.mk_wordi (x, 64)) ns, ``:word64``)
fun csv_words l =
  String.concatWith "," (map word_text (fst (listSyntax.dest_list l)))
fun csv_nums ns = String.concatWith "," (map Arbnum.toString ns)

val keccak_cases =
  let val high = Arbnum.fromString "9223372036854775808"
      fun pad tail = List.tabulate (25, fn i =>
        if i = 0 then Arbnum.fromInt tail
        else if i = 16 then high else Arbnum.zero)
  in [("zero", List.tabulate (25, fn _ => Arbnum.zero)),
      ("empty", pad 6), ("abc", pad 0x06636261)] end

val belt_cases =
  let val g = [11,12,13,14] and d = [21,22,23,24]
      and p = [31,32,33,34] and x = [41,42,43,44]
      val st = [1] @ g @ [100] @ d @ p
      val rq = g @ [100,101] @ d @ x @ p @ [1]
      fun set l i v = List.take (l,i) @ [v] @ List.drop (l,i+1)
      val cases = [("accept",st,rq), ("uninitialized",set st 0 2,rq),
                   ("genesis",st,set rq 0 99), ("stale",st,set rq 4 99),
                   ("nonincreasing",st,set rq 5 100), ("fork",st,set rq 6 99),
                   ("drift",st,set rq 14 99), ("noack",st,set rq 18 0)]
  in map (fn (id,a,b) => (id, map Arbnum.fromInt (a @ b))) cases end

val keccak_locals =
  ``(FEMPTY |+ («base», ValWord 256w)) : mlstring |-> 64 panSem$v``
val belt_locals =
  ``(FEMPTY |+ («current», ValWord 256w) |+ («candidate», ValWord 368w))
    : mlstring |-> 64 panSem$v``

(* Each vector must give the same result, memory and status before and after
   optimization. The rows go to the native run for a third comparison. *)
fun cshake_sample body opt =
  let fun observe p = value “kernel_obs 68 (panSem$evaluate (^p, cshake_sample_state))”
      val before_opt = observe body
      val after_opt = observe opt
      val (r, memory) = pairSyntax.dest_pair before_opt
      val _ = if aconv before_opt after_opt andalso
                 aconv r “SOME (panSem$Return (ValWord (0w:word64)))” then ()
              else raise Fail "cshake256: sample 3 status or memory differs"
      val digest = List.take (fst (listSyntax.dest_list memory), 4)
  in String.concatWith "\t" ["cshake256", "sample3", "0,1,2,3", "0",
                             String.concatWith "," (map word_text digest)] end

fun eval_rows name body opt =
  let
    val setup = case name of
        "keccakF1600" => SOME (keccak_cases, keccak_locals, 25)
      | "beltLatch" => SOME (belt_cases, belt_locals, 33)
      | _ => NONE
    val orig_steps = top_steps (norm body) and opt_steps = top_steps (norm opt)
    fun row (id, input) =
      let val (cases_locals, n) =
            case setup of SOME (_, l, n) => (l, n) | NONE => raise Fail "no setup"
          val ws = word_terms input
          val t0 = Time.now ()
          val (r0, m0) = run_steps n cases_locals orig_steps ws
          val (r1, m1) = run_steps n cases_locals opt_steps ws
          val _ = if aconv r0 r1 andalso aconv m0 m1 then ()
                  else raise Fail (name ^ " " ^ id ^ ": EVAL differs after optimization")
          val status = word_text (rand (rand (rand (optionSyntax.dest_some r0))))
      in say (name ^ " " ^ id ^ ": EVAL agrees before and after (" ^ since t0 ^ "s)");
         String.concatWith "\t" [name, id, csv_nums input, status, csv_words m0]
      end
  in case setup of
       SOME (cases, _, _) => map row cases
     | NONE => if name = "cshake256" then [cshake_sample body opt]
               else raise Fail ("no EVAL vectors for " ^ name)
  end

fun run_kernel name =
  let
    val t0 = Time.now ()
    val src = slurp (OS.Path.concat (dir, name ^ ".pnk"))
    val (header, source_body) = split_source src
    val body = parse_body name src
    val _ = say (name ^ ": parsed " ^ Int.toString (size src) ^ " bytes in " ^ since t0 ^ "s")
    val _ = if body_text body = source_body then ()
            else raise Fail (name ^ ": printer does not reproduce the source")
    val t1 = Time.now ()
    val opt = value “run_passes opt_passes ^body”
    val _ = say (name ^ ": optimized in " ^ since t1 ^ "s")
    val opt_src = header ^ body_text opt ^ "}\n"
    val _ = spit (OS.Path.concat (outdir, name ^ ".pnk")) opt_src
    val t2 = Time.now ()
    val reparsed = parse_body name opt_src
    val _ = if aconv (norm reparsed) (norm opt) then ()
            else raise Fail (name ^ ": printed program does not parse to the optimized AST")
    val _ = say (name ^ ": printed program reparsed to the optimized AST in " ^ since t2 ^ "s")
    val n0 = nodes (norm body) and n1 = nodes (norm opt)
    val row = String.concatWith "\t"
      [name, Int.toString n0, Int.toString n1,
       Int.toString (size src), Int.toString (size opt_src)]
  in
    say (name ^ ": nodes " ^ Int.toString n0 ^ " -> " ^ Int.toString n1 ^
         ", source bytes " ^ Int.toString (size src) ^ " -> " ^ Int.toString (size opt_src));
    (row, eval_rows name body opt)
  end

val results = map run_kernel names
val _ = spit (OS.Path.concat (outdir, "stats.tsv"))
             (String.concatWith "\n" (map fst results) ^ "\n")
val _ = spit (OS.Path.concat (outdir, "eval.tsv"))
             (String.concat (map (fn r => r ^ "\n") (List.concat (map snd results))))
