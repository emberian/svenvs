(* =========================================================================
   reflectsem/fueledGenLib.sml — generate FUELED MIRRORS of recursive
   functions whose recursion HOL Light's define cannot handle directly
   (nested recursion over v/exp/pat through lists, and the clocked mutual
   evaluate group).

   For a group [f1,...,fm] with stored (pattern-compiled, non-overlapping)
   clausal definitions, produce a single dispatcher

     F_n : num -> in1+...+inm -> out   (out = sum if outputs differ)

     F_n 0 x = ARB
     F_n (SUC k) (INJ_i (tuple args_i)) = rhs_i [ f_j es |->
            (\xs. PROJ_j (F_n k (INJ_j (tuple xs)))) es , beta-reduced ]

   primitive recursion on the fuel — definable by HOL Light's define no
   matter how the original recursed. For m = 1 with identical in/out, no
   sums are introduced and the original argument structure is kept.

   The HOL4 Define of these clauses is the artifact of record: the candle
   text is PRINTED from its defining theorem (exportLib), and the HOL4
   bridge lemmas (∃k0. ∀k ≥ k0. F_n k (INJ_i x) = INJ'_i (f_i x)) pin the
   fueled mirror to the original semantics.
   ========================================================================= *)

structure fueledGenLib = struct

open HolKernel boolLib bossLib pairSyntax sumSyntax numSyntax;

(* ---------- sum-encoding helpers ---------- *)

(* right-nested sum of types; injection/projection builders *)
fun mk_sumty [t] = t
  | mk_sumty (t :: ts) = mk_sum (t, mk_sumty ts)
  | mk_sumty [] = raise Fail "mk_sumty: empty";

(* inject a term of type (el i tys) into mk_sumty tys *)
fun mk_inj tys i tm =
  case tys of
    [_] => tm
  | t :: ts =>
      if i = 0 then mk_inl (tm, mk_sumty ts)
      else mk_inr (mk_inj ts (i-1) tm, t)
  | [] => raise Fail "mk_inj";

(* project from a term of type mk_sumty tys back to el i tys *)
fun mk_proj tys i tm =
  case tys of
    [_] => tm
  | t :: ts =>
      if i = 0 then mk_outl tm
      else mk_proj ts (i-1) (mk_outr tm)
  | [] => raise Fail "mk_proj";

(* ---------- group analysis ---------- *)

(* clauses of a stored def: [(member-const, lhs-args, rhs)] *)
fun dest_clauses def_th =
  map (fn cj =>
        let val (l,r) = dest_eq (snd (strip_forall cj))
            val (f,args) = strip_comb l
        in (f, args, r) end)
      (strip_conj (concl def_th));

(* group signature: distinct member constants in clause order *)
fun members clauses =
  List.foldl (fn ((f,_,_), acc) =>
      if List.exists (fn g => same_const f g) acc then acc else acc @ [f])
    [] clauses;

(* ---------- the generator ---------- *)

(* environment of ALREADY-fueled constants: maps an original constant to a
   builder that, given the fuel term, yields its replacement lambda
   (\xs. PROJ (G_n fuel (INJ (tuple xs)))). Callers of fueled functions
   must thread fuel through ("fuel infection"). *)
type fuel_env = (term * (term -> term)) list;

(* TYPE-INSTANTIATING fuel substitution. The entries' constants carry the
   types of their stored defining theorems (e.g. do_eval_res : α state ...),
   but a use site may be a proper instance ('ffi state ...). Term.subst
   matches redexes up to aconv only, so each occurrence gets its own redex:
   the template is instantiated with the type match from the stored
   constant to that occurrence. *)
fun inst_sigma (templates : (term * term) list) r =
  List.concat (map (fn (c, tmpl) =>
      let
        val occs = Lib.op_mk_set aconv
                     (find_terms (fn t => is_const t andalso same_const t c) r)
      in
        map (fn occ =>
               occ |-> Term.inst (Type.match_type (type_of c) (type_of occ))
                                 tmpl)
            occs
      end) templates);

fun env_templates (env : fuel_env) k = map (fn (c, mk) => (c, mk k)) env;

(* build the env entries for a group just defined: Fn_const the dispatcher *)
fun group_env_entries Fn_const mems arities in_tys out_tys one_out simple :
    fuel_env =
  List.tabulate (length mems, fn j =>
    let
      val f = List.nth (mems, j)
      val n = List.nth (arities, j)
      val (doms,_) = strip_fun (type_of f)
      fun mk k =
        let
          val xs = List.tabulate (n, fn i =>
                     mk_var ("zw" ^ Int.toString i, List.nth (doms, i)))
          val body =
            if simple
            then list_mk_comb (Fn_const, k :: xs)
            else (if one_out then (fn t => t) else mk_proj out_tys j)
                   (list_mk_comb
                      (Fn_const, [k, mk_inj in_tys j (list_mk_pair xs)]))
        in list_mk_abs (xs, body) end
    in (f, mk) end);

(* mk_fueled name ext def_th
   returns (defining_clauses_term, wrapper_specs, in_tys, out_tys, one_out) *)
fun mk_fueled fueled_name (ext : fuel_env) def_th =
  let
    val clauses = dest_clauses def_th
    val mems = members clauses
    val m = length mems
    (* per-member arity: from the first clause of that member *)
    fun arity_of f =
      case List.find (fn (g,_,_) => same_const f g) clauses of
        SOME (_,args,_) => length args
      | NONE => raise Fail "arity_of"
    val arities = map arity_of mems
    (* in/out types per member *)
    fun in_ty_of (f, n) =
      let val (doms,_) = strip_fun (type_of f)
      in list_mk_prod (List.take (doms, n)) end
    fun out_ty_of (f, n) =
      let val (doms,rng) = strip_fun (type_of f)
      in List.foldr (op -->) rng (List.drop (doms, n)) end
    val in_tys = ListPair.map in_ty_of (mems, arities)
    val out_tys = ListPair.map out_ty_of (mems, arities)
    val out_distinct =
      Lib.op_mk_set (fn a => fn b => Type.compare (a,b) = EQUAL) out_tys
    val one_out = length out_distinct = 1
    val out_sumty = if one_out then hd out_tys else mk_sumty out_tys
    (* out injection index: position of member's out type in out_tys-sum *)
    fun out_inj i tm = if one_out then tm else mk_inj out_tys i tm
    fun out_proj i tm = if one_out then tm else mk_proj out_tys i tm
    val in_sumty = mk_sumty in_tys
    val simple = (m = 1)  (* keep curried args, no sums *)
    val Fn_ty =
      if simple
      then num --> (List.foldr op--> (hd out_tys)
                      (fst (strip_fun (type_of (hd mems)))
                       |> (fn ds => List.take (ds, hd arities))))
      else num --> in_sumty --> out_sumty
    val Fn = mk_var (fueled_name, Fn_ty)
    val k = mk_var ("fuel", num)
    (* the replacement lambda for member j at fuel k *)
    fun repl j =
      let
        val f = List.nth (mems, j)
        val n = List.nth (arities, j)
        val (doms,_) = strip_fun (type_of f)
        val xs = List.tabulate (n, fn i =>
                   mk_var ("zz" ^ Int.toString i, List.nth (doms, i)))
        val body =
          if simple
          then list_mk_comb (Fn, k :: xs)
          else out_proj j (list_mk_comb
                 (Fn, [k, mk_inj in_tys j (list_mk_pair xs)]))
      in list_mk_abs (xs, body) end
    val templates = List.tabulate (m, fn j => (List.nth (mems, j), repl j))
                    @ env_templates ext k
    fun fuel_rhs r =
      let val r' = Term.subst (inst_sigma templates r) r
      in rhs (concl (QCONV (TOP_DEPTH_CONV BETA_CONV) r')) end
    (* SUC-clauses *)
    val suck = mk_suc k
    fun mk_clause (f, args, r) =
      let
        val j = case List.tabulate (m, fn i => i)
                       |> List.find (fn i => same_const (List.nth (mems,i)) f)
                of SOME j => j | NONE => raise Fail "mk_clause"
        val lhs' =
          if simple then list_mk_comb (Fn, suck :: args)
          else list_mk_comb (Fn, [suck, mk_inj in_tys j (list_mk_pair args)])
        val rhs' = out_inj j (fuel_rhs r)
      in mk_eq (lhs', rhs') end
    (* base clause *)
    val xin = mk_var ("xin", if simple then hd in_tys else in_sumty)
    val base =
      if simple then
        let val (doms,_) = strip_fun (type_of (hd mems))
            val xs = List.tabulate (hd arities, fn i =>
                       mk_var ("xx" ^ Int.toString i, List.nth (doms, i)))
        in mk_eq (list_mk_comb (Fn, zero_tm :: xs), mk_arb (hd out_tys)) end
      else
        mk_eq (list_mk_comb (Fn, [zero_tm, xin]), mk_arb out_sumty)
    val all = list_mk_conj (base :: map mk_clause clauses)
    val wrappers = List.tabulate (m, fn j =>
        (List.nth (mems, j), List.nth (arities, j), j))
  in
    (all, wrappers, in_tys, out_tys, one_out)
  end;

(* define a fueled group in the current theory; returns the defining theorem
   plus the fuel_env entries for downstream (infected) groups *)
fun define_fueled fueled_name (ext : fuel_env) def_th =
  let
    val (tm, wrappers, in_tys, out_tys, one_out) =
      mk_fueled fueled_name ext def_th
    val def = TotalDefn.Define [ANTIQUOTE tm]
    (* dispatcher constant now exists *)
    val Fn_const =
      tm |> strip_conj |> hd |> strip_forall |> snd |> dest_eq |> fst
         |> strip_comb |> fst
         |> (fn v => let val (nm,ty) = dest_var v
                     in prim_mk_const {Thy = current_theory (), Name = nm}
                        handle HOL_ERR _ => mk_const (nm, ty)
                     end)
    val clauses = dest_clauses def_th
    val mems = members clauses
    fun arity_of f =
      case List.find (fn (g,_,_) => same_const f g) clauses of
        SOME (_,args,_) => length args
      | NONE => raise Fail "arity_of"
    val arities = map arity_of mems
    val simple = length mems = 1
    val new_env =
      group_env_entries Fn_const mems arities in_tys out_tys one_out simple
  in (def, new_env) end;

(* ---------- post-generation check ---------- *)

(* every ORIGINAL member constant of any fueled group that still occurs on a
   right-hand side of any generated fueled definition: each one is a missed
   fuel infection (or an ordering error in the group sequence).
   groups: (fueled def name, original defining theorem, fueled def) *)
fun leftover_originals (groups : (string * thm * thm) list) =
  let
    val origs = List.concat (map (fn (_,d,_) => members (dest_clauses d)) groups)
    (* a clause stored as `P xs` or `~P xs` has rhs T/F: nothing to scan *)
    fun rhss th =
      List.mapPartial (fn cj => let val c = snd (strip_forall cj)
                                in if is_eq c then SOME (rhs c) else NONE end)
        (strip_conj (concl th))
  in
    List.concat (map (fn (nm,_,fd) =>
        map (fn c => (nm, c))
          (Lib.op_mk_set aconv
             (List.concat (map (find_terms (fn t => is_const t andalso
                                  List.exists (same_const t) origs))
                               (rhss fd)))))
      groups)
  end;

(* the same through the DIRECT (unfueled) functions the mirrors call: a
   direct function whose definition, transitively, calls an original is
   itself a missed fuel infection (its exported text would reference a
   constant that only exists as a mirror). Only constants of theories
   descending from ast can mention the semantics' originals.
   Returns (direct constant, original it reaches). *)
fun defthm_of c =
  let
    val {Thy, Name, ...} = dest_thy_const c
    fun try nm = SOME (DB.fetch Thy nm) handle HOL_ERR _ => NONE
  in
    case try (Name ^ "_def") of SOME th => SOME th | NONE =>
    case try (Name ^ "_DEF") of SOME th => SOME th | NONE => try Name
  end;

fun infected_direct (groups : (string * thm * thm) list) =
  let
    val origs = List.concat (map (fn (_,d,_) => members (dest_clauses d)) groups)
    fun is_orig t = List.exists (same_const t) origs
    val fueled_thy = current_theory ()
    fun candidate t =
      is_const t andalso not (is_orig t) andalso
      let val thy = #Thy (dest_thy_const t)
      in thy <> fueled_thy andalso thy <> "fueledSem" andalso
         (thy = "ast" orelse Lib.mem "ast" (Theory.ancestry thy))
      end handle HOL_ERR _ => false
    fun consts_of th = find_terms is_const (concl th)
    val seen = ref ([] : term list)
    val bad = ref ([] : (term * term) list)
    fun visit c =
      if List.exists (same_const c) (!seen) then ()
      else
        (seen := c :: !seen;
         case defthm_of c of
           NONE => ()
         | SOME th =>
             let val cs = consts_of th
             in List.app (fn o' => bad := (c, o') :: !bad)
                  (Lib.op_mk_set same_const (List.filter is_orig cs));
                List.app visit (List.filter candidate cs)
             end)
  in
    List.app (fn (_,_,fd) => List.app visit (List.filter candidate (consts_of fd)))
      groups;
    List.rev (!bad)
  end;

fun report_leftovers groups =
  let
    val bad = leftover_originals groups
    val () = List.app (fn (nm, c) =>
        print ("LEFTOVER original in " ^ nm ^ ": " ^ term_to_string c ^
               " : " ^ type_to_string (type_of c) ^ "\n")) bad
    val bad' = infected_direct groups
    val () = List.app (fn (d, c) =>
        print ("LEFTOVER original via direct function " ^ term_to_string d ^
               ": " ^ term_to_string c ^ "\n")) bad'
    val () = print ("fueled groups checked: " ^ Int.toString (length groups) ^
                    ", leftover original constants: " ^
                    Int.toString (length bad + length bad') ^ "\n")
  in map #2 bad @ map #2 bad' end;

end
