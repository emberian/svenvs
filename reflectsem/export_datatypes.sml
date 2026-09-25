(* =========================================================================
   reflectsem/export_datatypes.sml — emit candle define_type script for the
   FULL datatype cone of CakeML's evaluate (45 datatypes incl. ast$exp,
   semanticPrimitives$v, sem_env, state, eval_state, ffi, ...), plus their
   case constants and record accessors/fupds, all printed FROM the HOL4
   defining theorems.

   Run on a host with the built CakeML semantics, in $CAKEMLDIR/semantics
   so .holpath resolves (CAKEMLDIR and SVENVS_ROOT default to ~/dev/CakeML
   and ~/dev/svenvs):
     cd $CAKEMLDIR/semantics && \
       $HOLDIR/bin/hol < $SVENVS_ROOT/reflectsem/export_datatypes.sml
   Output: $REFLECTSEM_OUT_DIR/reflectsem_datatypes.ml, default directory
   ${TMPDIR:-/tmp}/svenvs-$USER (the path written is printed; submit it via
   place-submit.sh)
   ========================================================================= *)

val () = print "=== export_datatypes: loading ===\n";

(* output directory: $REFLECTSEM_OUT_DIR, default ${TMPDIR:-/tmp}/svenvs-$USER *)
val out_dir =
  case OS.Process.getEnv "REFLECTSEM_OUT_DIR" of
    SOME d => d
  | NONE =>
      let val tmp = case OS.Process.getEnv "TMPDIR" of
                      SOME t => t | NONE => "/tmp"
          val user = case OS.Process.getEnv "USER" of
                       SOME u => u | NONE => "unknown"
      in OS.Path.concat (tmp, "svenvs-" ^ user) end;
val () =
  if OS.FileSys.access (out_dir, []) then ()
  else OS.FileSys.mkDir out_dir;
val out_path = OS.Path.concat (out_dir, "reflectsem_datatypes.ml");
val cakemldir =
  case OS.Process.getEnv "CAKEMLDIR" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/CakeML");
val () = loadPath :=
  map (fn d => OS.Path.concat (cakemldir, d))
      ["semantics", "semantics/ffi", "misc", "basis/pure"] @ !loadPath;
val () = load "evaluateTheory";

val svenvs =
  case OS.Process.getEnv "SVENVS_ROOT" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/svenvs");
val () = use (OS.Path.concat (svenvs, "reflectsem/exportLib.sml"));

open HolKernel boolLib;

(* monomorphize namespace/id name parameters at mlstring (their only
   instances in the evaluate cone; probed: 3-tyvar nested recursion is
   unsupported in this HOL Light). Keyed by canonical tyvar name. *)
local
  val mlstring_ty = mk_thy_type {Thy="mlstring", Tyop="mlstring", Args=[]}
  fun spec_for ty keepers =
    let val {Args,...} = dest_thy_type ty
    in map (fn a => if Lib.mem (dest_vartype a) keepers then NONE
                    else SOME mlstring_ty) Args
    end
  val ns_ty = let val SOME tyi = TypeBase.read {Thy="namespace",Tyop="namespace"}
              in TypeBasePure.ty_of tyi end
  val id_ty = let val SOME tyi = TypeBase.read {Thy="namespace",Tyop="id"}
              in TypeBasePure.ty_of tyi end
in
val () = exportLib.mono_tab :=
  [(("namespace","namespace"), spec_for ns_ty ["'v"]),
   (("namespace","id"),        spec_for id_ty [])]
end;

(* ---------------- the type walk (cone of evaluate) ---------------- *)

val builtin_ty_names =
  ["fun","bool","num","int","list","option","prod","sum","one","char",
   "itself","string"];
val opaque_ty_thys = ["words","fcp","binary_ieee","machine_ieee","fpSem","real",
                      "realax","integer_word"];

structure SS = Redblackset;
fun spcmp ((a,b),(c,d)) =
  case String.compare (a,c) of EQUAL => String.compare (b,d) | x => x;
val seen_ty = ref (SS.empty spcmp);
val ty_order = ref ([] : hol_type list);

fun visit_type ty =
  if is_vartype ty then ()
  else let
    val {Tyop,Thy,Args} = dest_thy_type ty
    val k = (Thy,Tyop)
    val _ = List.app visit_type Args
  in
    if SS.member (!seen_ty, k) then ()
    else if Lib.mem Tyop builtin_ty_names then seen_ty := SS.add (!seen_ty, k)
    else if Lib.mem Thy opaque_ty_thys then seen_ty := SS.add (!seen_ty, k)
    else
      (seen_ty := SS.add (!seen_ty, k);
       case TypeBase.fetch ty of
         SOME _ =>
           let
             (* canonical instance: the type as its own TypeBase canonical *)
             val cons = TypeBase.constructors_of ty handle HOL_ERR _ => []
             val _ = List.app
                       (fn c => List.app visit_type (fst (strip_fun (type_of c))))
                       cons
           in ty_order := ty :: !ty_order end
       | NONE => print ("WARN no TypeBase for " ^ Thy ^ "$" ^ Tyop ^ "\n"))
  end;

(* seed: walk every type in the full evaluate defining theorem + do_app etc. *)
fun visit_all_types_in th =
  List.app (fn t => visit_type (type_of t))
    (find_terms (fn t => is_const t orelse is_var t) (concl th));

local
  fun fetch thy nm = SOME (DB.fetch thy nm) handle HOL_ERR _ => NONE
in
val seeds = List.mapPartial (fn (t,n) => fetch t n)
  [("evaluate","full_evaluate_def"),
   ("semanticPrimitives","do_app_def"),
   ("semanticPrimitives","do_eval_def"),
   ("semanticPrimitives","pmatch_def"),
   ("semanticPrimitives","do_eq_def"),
   ("semanticPrimitives","build_tdefs_def"),
   ("semanticPrimitives","declare_env_def"),
   ("semanticPrimitives","compiler_agrees_def"),
   ("ffi","call_FFI_def"),
   ("ast","getOpClass_def"),
   ("ast","pat_bindings_def"),
   (* the function cone reaches mlstring comparisons (ordering) *)
   ("mlstring","compare_def")]
end;
val () = List.app visit_all_types_in seeds;

(* the canonical instance for printing: use TypeBase's own canonical type so
   constructor argument types come out in terms of the type's parameters *)
fun canonical ty =
  case TypeBase.fetch ty of
    SOME tyi => TypeBasePure.ty_of tyi
  | NONE => ty;

val dts = List.rev (!ty_order);
val () = print ("datatypes to export: " ^ Int.toString (length dts) ^ "\n");

(* ---------------- emit ---------------- *)

val out = TextIO.openOut out_path;
fun emit s = TextIO.output (out, s ^ "\n");

val () = emit "(* GENERATED by svenvs reflectsem/export_datatypes.sml — the full";
val () = emit "   datatype cone of CakeML's evaluate, printed from the HOL4";
val () = emit "   defining theorems. Do not edit by hand. *)";
val () = emit "";
val () = emit "(* opaque leaf types: meaning pinned by the HOL4 bridge *)";
val () = emit "new_type (\"w8\", 0);;";
val () = emit "new_type (\"w64\", 0);;";
val () = emit "new_constant (\"cml_CHR\", `:num -> char`);;";
val () = emit "new_constant (\"cml_ORD\", `:char -> num`);;";
val () = emit "new_constant (\"cml_char_lt\", `:char -> char -> bool`);;";
val () = emit "";

val dt_names = ref ([] : string list);
val dt_thms = ref ([] : string list);
fun try_emit_dt ty =
  let
    val cty = canonical ty
    val {Tyop,Thy,...} = dest_thy_type cty
    val spec = exportLib.dt_spec cty
    val () = emit ("(* " ^ Thy ^ "$" ^ Tyop ^ " *)")
    val () = emit ("let " ^ exportLib.rename Tyop ^ "_DT = define_type \""
                   ^ spec ^ "\";;")
    (* case constant: instantiate the recursion theorem define_type just
       returned (new_recursive_definition, direct); the generic `define`
       re-derives admissibility and took ~1 hour on op's 50 clauses in
       the verified kernel. `define` stays as a logged fallback. *)
    val () =
      (let val cls = exportLib.case_def_clauses cty
           val nm = exportLib.rename Tyop
       in emit (exportLib.pcase_define nm cls)
       end handle HOL_ERR _ => emit ("(* no case_def for " ^ Tyop ^ " *)"))
    (* record accessors/fupds (named, for rewrite lists) *)
    val () = dt_names := exportLib.rename Tyop :: !dt_names
    val () = dt_thms := (exportLib.rename Tyop ^ "_CASE_def") :: !dt_thms
    val ctr = ref 0
    val () = exportLib.annotate_vars := true
    val () =
      List.app (fn cls =>
          (emit (exportLib.pdefine_named
                   (exportLib.rename Tyop ^ "_rec" ^ Int.toString (!ctr)
                    ^ "_def") cls);
           dt_thms := (exportLib.rename Tyop ^ "_rec" ^ Int.toString (!ctr)
                       ^ "_def") :: !dt_thms;
           ctr := !ctr + 1)
          handle HOL_ERR _ => emit ("(* skipped a record def for " ^ Tyop ^ " *)"))
        (exportLib.record_defs cty)
    val () = exportLib.annotate_vars := false
  in emit "" end
  handle e =>
    (exportLib.annotate_vars := false;
    emit ("(* FAILED to export " ^ exportLib.pty (canonical ty) ^ " : "
          ^ General.exnMessage e ^ " *)\n"));

val () = List.app try_emit_dt dts;
(* the datatypes' names (for distinctness/injectivity) and their case /
   record theorems, as lists the gate scripts use *)
val () = emit ("let reflectsem_dt_names = [" ^ String.concatWith "; "
                 (map (fn n => "\"" ^ n ^ "\"") (List.rev (!dt_names))) ^ "];;");
val () = emit ("let reflectsem_dt_thms = [" ^ String.concatWith "; "
                 (List.rev (!dt_thms)) ^ "];;");
val () = emit "let REFLECTSEM_DATATYPES_END = 1;;";
val () = TextIO.closeOut out;
val () = print ("wrote " ^ out_path ^ "\n");

(* manifest of exported datatypes (Thy$Tyop per line): export_functions.sml
   checks every type its printed definitions mention against it *)
val manifest_path = OS.Path.concat (out_dir, "reflectsem_datatypes.manifest");
val () =
  let val m = TextIO.openOut manifest_path
  in List.app (fn ty => let val {Thy,Tyop,...} = dest_thy_type ty
                        in TextIO.output (m, Thy ^ "$" ^ Tyop ^ "\n") end) dts;
     TextIO.closeOut m
  end;
val () = print ("wrote " ^ manifest_path ^ "\n");
val dt_fail = ref 0;
val () = List.app
  (fn (t,n) => (print ("EXPORT_FAIL unmapped builtin constant: " ^ t ^ "$" ^ n ^ "\n");
                dt_fail := !dt_fail + 1))
  (!exportLib.unmapped_seen);
val () =
  let val ins = TextIO.openIn out_path
      fun loop () = case TextIO.inputLine ins of
                      NONE => ()
                    | SOME l => ((if String.isSubstring "FAILED" l orelse
                                     String.isSubstring "skipped a record" l
                                  then (print ("EXPORT_FAIL " ^ l); dt_fail := !dt_fail + 1)
                                  else ()); loop ())
  in loop (); TextIO.closeIn ins end;
val () =
  if !dt_fail = 0
  then print ("EXPORT_DATATYPES_OK " ^ Int.toString (length dts) ^ "\n")
  else (print "EXPORT_DATATYPES_FAILED\n"; OS.Process.exit OS.Process.failure);
