(* Check the saved proof objects and bind the native harness's inputs to them,
   including when Holmake reuses an existing theory. Run with hol run. *)
load "pancakeKernelOptTheory";
load "pancakeKernelLib";

open pancakeKernelLib;

fun check_theory thy =
  let
    val entries = DB.thms thy
    fun check (name, th) =
      if null (Thm.hyp th) andalso Tag.isDisk (Thm.tag th) then ()
      else raise Fail (thy ^ "." ^ name ^ ": open hypotheses or unexpected proof tag")
  in
    if null entries orelse not (null (DB.axioms thy)) then
      raise Fail (thy ^ ": missing theory or declared axiom")
    else List.app check entries;
    say (thy ^ ": " ^ Int.toString (length entries) ^ " closed bindings, DISK_THM only")
  end;

fun kernel_theory name =
  "obend" ^ String.str (Char.toUpper (String.sub (name, 0))) ^ String.extract (name, 1, NONE);

fun check_sources name =
  let
    val thy = kernel_theory name
    fun definition suffix = rhs (concl (DB.fetch thy (name ^ suffix)))
    fun check (suffix, dir) =
      let val file = OS.Path.concat (dir, name ^ ".pnk")
          val bytes = slurp file
      in if bytes = stringSyntax.fromHOLstring (definition suffix) then size bytes
         else raise Fail (file ^ ": differs from " ^ thy ^ "." ^ name ^ suffix) end
    val original = check ("_source_def", kernel_dir ())
    val optimized = check ("_opt_source_def", out_dir ())
    val counts = [decls_nodes (definition "_decls_def"), decls_nodes (definition "_opt_decls_def"),
                  original, optimized]
    val stats = String.concatWith "\t" (name :: map Int.toString counts) ^ "\n"
  in
    check_theory thy;
    if stats = slurp (OS.Path.concat (out_dir (), name ^ ".stats")) then ()
    else raise Fail (name ^ ": measurements differ from the parsed files")
  end;

val _ = List.app check_theory ["pancakeOptGate", "pancakeKernel", "pancakeKernelOpt"];
val _ = List.app check_sources ["keccakF1600", "cshake256", "beltLatch", "macaroonVerify", "kmac256"];

(* Reconstruct the two observations claimed by each row. The clock occurs
   only in the proof, so match it as a variable shared by both observations. *)
fun fields ch s = String.fields (fn c => c = ch) s;
fun word s = wordsSyntax.mk_wordi (Arbnum.fromString s, 64);
fun mlstr s = mk_comb (rator ``«x»``, stringSyntax.fromMLstring s);
fun words s = listSyntax.mk_list (map word (fields #"," s), ``:word64``);
fun argument s =
  case fields #"=" s of
    [name, value] => pairSyntax.mk_pair (mlstr name, word value)
  | _ => raise Fail ("invalid argument " ^ s);

fun check_row line =
  case fields #"\t" line of
    [kernel, id, func, args, image, status, output] =>
    let
      val name = kernel ^ "_" ^ id
      val (s, body) = boolSyntax.dest_forall (concl (DB.fetch "pancakeKernelOpt" name))
      val args = listSyntax.mk_list (map argument (fields #"," args), ``:mlstring # word64``)
      val clock = mk_var ("clock", numSyntax.num)
      val state = list_mk_icomb (``kernel_state``, [s, args, clock, words image])
      val out = words output
      val count = numSyntax.term_of_int (length (fields #"," output))
      val ret = word status
      fun observation suffix =
        let val decls = prim_mk_const {Thy = kernel_theory kernel, Name = kernel ^ suffix}
            val f = list_mk_icomb (``fun_body``, [mlstr func, decls])
        in ``kernel_obs ^count (panSem$evaluate (^f, ^state)) =
             (SOME (panSem$Return (ValWord ^ret)), ^out)`` end
      val pattern = mk_conj (observation "_decls", observation "_opt_decls")
      val (sub, _) = match_term pattern body
        handle HOL_ERR _ => raise Fail (name ^ ": row disagrees with its theorem")
      val c = subst sub clock
    in
      if numSyntax.is_numeral c andalso aconv (subst [clock |-> c] pattern) body then ()
      else raise Fail (name ^ ": row disagrees with its theorem")
    end
  | _ => raise Fail "invalid EVAL row";

val rows = String.tokens (fn c => c = #"\n") (slurp (OS.Path.concat (out_dir (), "eval.tsv")));
val _ = List.app check_row rows;
val _ = say (Int.toString (length rows) ^ " native vector rows agree with their saved theorems");
