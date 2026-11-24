(* Bring one of Obend's emitted Pancake kernels into the current theory.

   `ingest NAME` reads $PANCAKE_KERNELS/NAME.pnk, parses it with CakeML's
   verified parser in the logic, applies `run_passes opt_passes`, and prints
   the result to $PANCAKE_KERNELS/opt/NAME.pnk for the native build. The
   printer sits outside the proofs, so two checks bind it to them: it must
   reproduce the original source byte for byte from the parsed AST, and the
   verified parser must read its output back to declarations that agree with
   the optimizer's under `canon`. The theory then holds

     NAME_parse      parse_kernel NAME_source = SOME NAME_decls
     NAME_opt_parse  parse_kernel NAME_opt_source = SOME NAME_opt_decls
     NAME_canon      the two lists agree up to annotations and grouping
     NAME_evaluate   every function of the printed program evaluates as the
                     original one does, from every state
     NAME_semantics  the printed program's semantics_decls is the original's

   where NAME_source and NAME_opt_source are the two files' contents. *)
structure pancakeKernelLib =
struct

open HolKernel Parse boolLib bossLib
open pancakeKernelTheory pancakeOptGateTheory

val ERR = mk_HOL_ERR "pancakeKernelLib"

fun kernel_dir () =
  case OS.Process.getEnv "PANCAKE_KERNELS" of
    SOME d => d
  | NONE => raise ERR "kernel_dir" "PANCAKE_KERNELS is not set"

fun out_dir () =
  let val d = OS.Path.concat (kernel_dir (), "opt")
  in (OS.FileSys.mkDir d handle OS.SysErr _ => ()); d end

fun slurp p =
  let val f = TextIO.openIn p val s = TextIO.inputAll f
  in TextIO.closeIn f; s end
fun spit p s =
  let val f = TextIO.openOut p in TextIO.output (f, s); TextIO.closeOut f end
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
fun bad what t = raise ERR "print" ("cannot print " ^ what ^ ": " ^ term_to_string t)
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

fun decl_fields d =
  case strip_comb d of
    (h, [fi]) => if ctor h = "Function" then snd (TypeBase.dest_record fi)
                 else bad "declaration" d
  | _ => bad "declaration" d

(* `export fun name(1 a, 1 b) {` with the default return shape, then the body *)
fun decl_text d =
  let val fs = decl_fields d
      fun field f = Lib.assoc f fs
      fun param p =
        let val (v, sh) = pairSyntax.dest_pair p
        in if ctor sh = "One" then "1 " ^ name_text v else bad "parameter shape" p end
      val _ = if field "inline" ~~ F andalso ctor (field "return") = "One" then ()
              else bad "function attributes" d
  in (if field "export" ~~ T then "export " else "") ^ "fun " ^
     name_text (field "name") ^ "(" ^
     String.concatWith ", " (map param (fst (listSyntax.dest_list (field "params")))) ^
     ") {\n" ^ body_text (field "body") ^ "}\n"
  end

fun decls_list ds = fst (listSyntax.dest_list ds)
fun program_text ds = String.concatWith "\n" (map decl_text (decls_list ds))
fun fun_names ds = map (fn d => name_text (Lib.assoc "name" (decl_fields d))) (decls_list ds)
fun decls_nodes ds =
  List.foldl (fn (d, n) => n + nodes (norm (Lib.assoc "body" (decl_fields d)))) 0
             (decls_list ds)

fun define name tm =
  new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))

val parse_kernel_tm = ``parse_kernel``

(* `parse_kernel c = SOME ds` for the constant c of src_def *)
fun parse_source what src_def =
  let val th = EVAL (mk_comb (parse_kernel_tm, rhs (concl src_def)))
      val r = rhs (concl th)
  in if optionSyntax.is_some r
     then (optionSyntax.dest_some r, TRANS (AP_TERM parse_kernel_tm src_def) th)
     else raise ERR "ingest" (what ^ ": the verified parser rejected the source")
  end

(* rewrite the literal argument of `SOME` to the constant it defines *)
fun some_const decls_def =
  CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (SYM decls_def))))

fun ingest name =
  let
    val t0 = Time.now ()
    val src = slurp (OS.Path.concat (kernel_dir (), name ^ ".pnk"))
    val src_def = define (name ^ "_source") (stringSyntax.fromMLstring src)
    val (ds, parse_th) = parse_source name src_def
    val decls_def = define (name ^ "_decls") ds
    val _ = save_thm (name ^ "_parse", some_const decls_def parse_th)
    val _ = say (name ^ ": parsed " ^ Int.toString (size src) ^ " bytes into " ^
                 String.concatWith ", " (fun_names ds) ^ " in " ^ since t0 ^ "s")
    val _ = if program_text ds = src then ()
            else raise ERR "ingest" (name ^ ": the printer does not reproduce the source")
    val t1 = Time.now ()
    val opt_tm = ``MAP (rewrite_decl (run_passes opt_passes)) :
                   64 panLang$decl list -> 64 panLang$decl list``
    val opt_th = EVAL (mk_comb (opt_tm, ds))
    val opt_ds = rhs (concl opt_th)
    val opt_th = CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (SYM decls_def)))) opt_th
    val _ = say (name ^ ": optimized in " ^ since t1 ^ "s")
    val opt_src = program_text opt_ds
    val _ = spit (OS.Path.concat (out_dir (), name ^ ".pnk")) opt_src
    val t2 = Time.now ()
    val opt_src_def = define (name ^ "_opt_source") (stringSyntax.fromMLstring opt_src)
    val (ds', reparse_th) = parse_source (name ^ " (optimized)") opt_src_def
    val opt_decls_def = define (name ^ "_opt_decls") ds'
    val _ = save_thm (name ^ "_opt_parse", some_const opt_decls_def reparse_th)
    val _ = say (name ^ ": reparsed the printed program in " ^ since t2 ^ "s")
    (* MAP canon NAME_opt_decls = MAP canon (MAP opt NAME_decls) *)
    val canon_tm = ``MAP (rewrite_decl canon) :
                     64 panLang$decl list -> 64 panLang$decl list``
    val c1 = CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (SYM opt_decls_def))))
                       (EVAL (mk_comb (canon_tm, ds')))
    val c2 = EVAL (mk_comb (canon_tm, opt_ds))
    val _ = if aconv (rhs (concl c1)) (rhs (concl c2)) then ()
            else raise ERR "ingest" (name ^ ": the printed program does not reparse to the optimized one")
    val canon_th = save_thm (name ^ "_canon",
                     TRANS c1 (SYM (TRANS (AP_TERM canon_tm opt_th) c2)))
    val _ = save_thm (name ^ "_evaluate", MATCH_MP canon_agree_evaluate canon_th)
    val _ = save_thm (name ^ "_semantics", MATCH_MP canon_agree_semantics_decls canon_th)
    val n0 = decls_nodes ds and n1 = decls_nodes opt_ds
  in
    spit (OS.Path.concat (out_dir (), name ^ ".stats"))
         (String.concatWith "\t" [name, Int.toString n0, Int.toString n1,
                                  Int.toString (size src), Int.toString (size opt_src)] ^ "\n");
    say (name ^ ": nodes " ^ Int.toString n0 ^ " -> " ^ Int.toString n1 ^
         ", source bytes " ^ Int.toString (size src) ^ " -> " ^ Int.toString (size opt_src) ^
         ", " ^ since t0 ^ "s in all")
  end

end
