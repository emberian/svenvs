(* =========================================================================
   reflectsem/cone_walker.sml — compute the EXPORT CONE of CakeML's evaluate.

   Walks the defining theorems transitively from evaluate$full_evaluate_def,
   classifying every constant and type encountered:
     BUILTIN  — maps to a HOL Light/candle primitive (bool, =, COND, num, ...)
     OPAQUE   — word/float leaf ops: become new_constants in candle, meaning
                pinned by the HOL4 bridge
     DATATYPE — needs a candle define_type (+ case const, accessors)
     FUN      — needs a candle define (flagged recursive / mutual group)

   Output is a topologically-ordered export plan, printed to stdout.
   Run:  $HOL -I $CAKEMLDIR/semantics -I $CAKEMLDIR/semantics/ffi \
              -I $CAKEMLDIR/misc -I $CAKEMLDIR/basis/pure < cone_walker.sml
   ========================================================================= *)

val () = print "=== cone walker: loading evaluateTheory ===\n";
val cakemldir =
  case OS.Process.getEnv "CAKEMLDIR" of
    SOME d => d
  | NONE => OS.Path.concat (valOf (OS.Process.getEnv "HOME"), "dev/CakeML");
val () = loadPath :=
  map (fn d => OS.Path.concat (cakemldir, d))
      ["semantics", "semantics/ffi", "misc", "basis/pure"] @ !loadPath;
val () = load "evaluateTheory";
open HolKernel boolLib;

(* ---------------- classification tables ---------------- *)

(* theories whose constants we treat as candle builtins (same constant exists
   in HOL Light with the same characterization, or is logical structure) *)
val builtin_const : (string * string) list = [
  ("min","="), ("min","==>"), ("min","@"),
  ("bool","T"), ("bool","F"), ("bool","/\\"), ("bool","\\/"), ("bool","~"),
  ("bool","!"), ("bool","?"), ("bool","?!"), ("bool","COND"), ("bool","LET"),
  ("bool","ARB"), ("bool","IN"), ("bool","UNCURRY"),
  ("pair",","), ("pair","FST"), ("pair","SND"), ("pair","UNCURRY"),
  ("pair","CURRY"), ("pair","pair_CASE"),
  ("num","0"), ("num","SUC"),
  ("arithmetic","NUMERAL"), ("arithmetic","BIT1"), ("arithmetic","BIT2"),
  ("arithmetic","ZERO"), ("arithmetic","+"), ("arithmetic","-"),
  ("arithmetic","*"), ("arithmetic","<"), ("arithmetic","<="),
  ("arithmetic",">"), ("arithmetic",">="), ("arithmetic","DIV"),
  ("arithmetic","MOD"), ("arithmetic","EXP"), ("arithmetic","MIN"),
  ("arithmetic","MAX")
];

(* theories whose constants become OPAQUE candle constants *)
val opaque_thys = ["words","fcp","binary_ieee","machine_ieee","fp64","real",
                   "realax","transc","intreal"];

(* types treated as builtin in candle (HOL Light core or opaque-as-type) *)
val builtin_tys = ["fun","bool","num","int","list","option","prod","sum",
                   "one","unit","char","string","itself"];
val opaque_tys = ["cart","bit0","bit1","i8","i64","real"];  (* word8/word64 via cart *)

fun ckey c = let val {Name,Thy,...} = dest_thy_const c in (Thy,Name) end;
fun ckey_str (thy,nm) = thy ^ "$" ^ nm;

(* ---------------- defining-theorem lookup ---------------- *)
fun try_fetch thy nm = SOME (DB.fetch thy nm) handle HOL_ERR _ => NONE;

fun defthm (thy,name) =
  case (thy,name) of
    ("evaluate","evaluate")       => try_fetch "evaluate" "full_evaluate_def"
  | ("evaluate","evaluate_match") => try_fetch "evaluate" "full_evaluate_def"
  | ("evaluate","evaluate_decs")  => try_fetch "evaluate" "full_evaluate_def"
  | _ =>
    (case try_fetch thy (name ^ "_def") of SOME th => SOME th | NONE =>
     case try_fetch thy (name ^ "_DEF") of SOME th => SOME th | NONE =>
     case try_fetch thy (name ^ "_thm") of SOME th => SOME th | NONE =>
     try_fetch thy name);

(* lhs head constants of a (possibly mutual, conjunctive) defining theorem *)
fun lhs_heads th =
  let
    val cs = strip_conj (concl th)
    fun head c =
      let val (l,_) = dest_eq (snd (strip_forall c))
      in SOME (ckey (fst (strip_comb l))) end
      handle HOL_ERR _ =>
        (* boolean-valued defs may use <=> at top *)
        (let val (l,_) = dest_eq (snd (strip_forall c))
         in SOME (ckey (fst (strip_comb l))) end handle HOL_ERR _ => NONE)
  in List.mapPartial head cs end;

(* ---------------- the walk ---------------- *)
structure SS = Redblackset;
fun spcmp ((a,b),(c,d)) =
  case String.compare (a,c) of EQUAL => String.compare (b,d) | x => x;

val seen_c   = ref (SS.empty spcmp);   (* visited constants *)
val seen_ty  = ref (SS.empty spcmp);   (* visited tyops *)
val fun_order = ref ([] : ((string*string) list * thm * bool) list;);
val ty_order  = ref ([] : (string*string) list);
val opaques   = ref (SS.empty spcmp);
val missing   = ref (SS.empty spcmp);

fun mem_c k = SS.member (!seen_c, k);
fun add_c k = seen_c := SS.add (!seen_c, k);
fun mem_ty k = SS.member (!seen_ty, k);
fun add_ty k = seen_ty := SS.add (!seen_ty, k);

(* all tyops in a type *)
fun tyops_of ty acc =
  if is_vartype ty then acc
  else let val {Tyop,Thy,Args} = dest_thy_type ty
       in List.foldl (fn (a,acc) => tyops_of a acc) ((Thy,Tyop)::acc) Args end;

(* datatype-derived constants of a tyinfo: constructors, case, accessors,
   updates — these need no separate function export *)
fun tyinfo_consts tyi =
  let
    val cons = TypeBase.constructors_of (TypeBasePure.ty_of tyi)
               handle HOL_ERR _ => []
    val cse  = [TypeBasePure.case_const_of tyi] handle HOL_ERR _ => []
    val accs = map (fn (_,t) => t) [] (* accessors via fields below *)
    val flds = TypeBasePure.fields_of tyi
    val acc_cs = List.mapPartial
                   (fn (nm,_) => NONE) flds (* accessor consts resolved later *)
  in map ckey (cons @ cse) end;

val dt_derived = ref (SS.empty spcmp);

fun visit_type ty =
  if is_vartype ty then ()
  else let
    val {Tyop,Thy,Args} = dest_thy_type ty
    val k = (Thy,Tyop)
    val _ = List.app visit_type Args
  in
    if mem_ty k then ()
    else if Lib.mem Tyop builtin_tys then add_ty k
    else if Lib.mem Tyop opaque_tys orelse Lib.mem Thy opaque_thys then
      (add_ty k; opaques := SS.add (!opaques, ("type:" ^ Thy, Tyop)))
    else
      (add_ty k;
       (case TypeBase.fetch ty of
          SOME tyi =>
            let
              val cons = TypeBase.constructors_of ty handle HOL_ERR _ => []
              val cse  = ([TypeBasePure.case_const_of tyi] handle HOL_ERR _ => [])
              (* record accessors/updates *)
              val accs = TypeBase.accessors_of ty handle HOL_ERR _ => []
              val upds = TypeBase.updates_of ty handle HOL_ERR _ => []
              val derived = map ckey (cons @ cse)
                            @ map (ckey o lhs o concl o SPEC_ALL) accs
                            @ map (ckey o lhs o concl o SPEC_ALL) upds
                handle HOL_ERR _ => map ckey (cons @ cse)
              val _ = List.app (fn k => dt_derived := SS.add (!dt_derived,k))
                               derived
              (* constructor argument types pull more types in *)
              val _ = List.app
                        (fn c => List.app visit_type
                                   (fst (strip_fun (type_of c)))) cons
            in ty_order := k :: !ty_order end
        | NONE => missing := SS.add (!missing, ("TYPE?" ^ Thy, Tyop))))
  end
and lhs t = fst (strip_comb (fst (dest_eq (snd (strip_forall t)))));

fun visit_const c =
  let val k as (thy,nm) = ckey c in
    if mem_c k then () else
    if Lib.mem k builtin_const then add_c k else
    (add_c k;
     visit_type (type_of c);
     if SS.member (!dt_derived, k) then () else
     if Lib.mem thy opaque_thys then opaques := SS.add (!opaques, k) else
     case defthm k of
       NONE => missing := SS.add (!missing, k)
     | SOME th =>
       let
         val heads = lhs_heads th
         val _ = List.app (fn h => add_c h) heads
         val body = concl th
         val rhs_consts =
           List.filter (fn t => is_const t) (find_terms is_const body)
         val recursive =
           List.exists (fn t => Lib.mem (ckey t) heads)
             (List.concat (map (fn cj =>
                let val (_,r) = dest_eq (snd (strip_forall cj))
                in find_terms is_const r end handle HOL_ERR _ => [])
                (strip_conj body)))
         (* visit types of everything in the body *)
         val _ = List.app (fn t => visit_type (type_of t))
                          (find_terms (fn t => is_const t orelse is_var t) body)
         (* recurse into rhs constants *)
         val _ = List.app visit_const rhs_consts
       in
         fun_order := (heads, th, recursive) :: !fun_order
       end)
  end;

(* ---------------- seed ---------------- *)
val seed = prim_mk_const {Thy="evaluate", Name="evaluate"};
val () = visit_const seed;

(* ---------------- report ---------------- *)
fun pr s = print (s ^ "\n");
val () = pr "\n=== EXPORT CONE: datatypes (definition order) ===";
val () = List.app (fn (thy,nm) => pr ("  DATATYPE " ^ thy ^ "$" ^ nm))
                  (List.rev (!ty_order));
val () = pr "\n=== EXPORT CONE: functions (definition order) ===";
val () = List.app
  (fn (heads,_,recursive) =>
     pr ("  FUN " ^ String.concatWith " + " (map ckey_str heads)
         ^ (if recursive then "   [RECURSIVE]" else "")))
  (List.rev (!fun_order));
val () = pr "\n=== OPAQUE leaves (new_constant + bridge) ===";
val () = SS.app (fn (thy,nm) => pr ("  OPAQUE " ^ thy ^ "$" ^ nm)) (!opaques);
val () = pr "\n=== MISSING defining theorems (need manual handling) ===";
val () = SS.app (fn (thy,nm) => pr ("  MISSING " ^ thy ^ "$" ^ nm)) (!missing);
val () = pr "\n=== cone walker done ===";
