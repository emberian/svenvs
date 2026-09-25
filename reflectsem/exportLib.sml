(* =========================================================================
   reflectsem/exportLib.sml — print HOL4 types/terms/definitions as
   HOL Light (Candle) concrete syntax.

   The output is GENERATED FROM the HOL4 defining theorems (TypeBase +
   DB.fetch), never hand-invented: faithfulness of the printed text to the
   HOL4 originals is by construction of this printer; the semantic bridge
   (fueled eval_n vs real evaluate, opaque-leaf isomorphisms) is proved
   separately in HOL4 (reflectsem/...Script.sml).

   Conventions:
     - terms print fully parenthesized, first-order (no match sugar; case
       constants become exported <ty>_CASE functions, one define each);
     - HOL4 records print as single-constructor datatypes + accessor and
       fupd functions (their HOL4 defining theorems printed as defines);
     - word8/word64/fp64/char-leaf ops become opaque new_constants, meaning
       pinned by the HOL4-side bridge;
     - builtins map per the table below (HOL4 const -> HOL Light name).
   ========================================================================= *)

structure exportLib = struct

open HolKernel boolLib;

(* ---------------- naming ---------------- *)

(* HOL Light names that must not be shadowed; rename with cml_ prefix *)
val reserved = ["T","F","I","o","K","S","W","C","ALL","EX","MEM","APPEND",
                "LENGTH","MAP","REVERSE","EL","HD","TL","NULL","FILTER",
                "ITLIST","ZIP","REPLICATE","LAST","BUTLAST","NIL","CONS",
                "SUC","PRE","DIV","MOD","EXP","MAX","MIN","FST","SND",
                "CURRY","UNCURRY","COND","LET","GABS","GEQ","ASSOC",
                "CHR","ORD","ASCII","int","real","list","option","num",
                "bool","char","sum","prod","one","Some","None","SOME","NONE",
                "INL","INR","Eval"];

fun rename n =
  let
    (* record constants come as recordtype.<ty>.seldef.<field>[_fupd] *)
    val toks = String.tokens (fn c => c = #".") n
    val toks = List.filter (fn t => t <> "recordtype" andalso t <> "seldef") toks
    val n = String.concatWith "_" toks
  in
    if Lib.mem n reserved then "cml_" ^ n
    else String.translate (fn #"'" => "_" | c => str c) n
  end;

(* ----- type-variable handling -----
   HOL Light's define_type needs the type parameters in a canonical order;
   we force it: inside a datatype spec (dtspec_mode), tyvars print as
   placeholder tokens; dt_spec then assigns A,B,C... by first occurrence in
   the printed spec and records, per type operator, the permutation from
   HOL4's canonical argument order to that occurrence order, which reference
   sites use to reorder instantiating arguments. *)
val dtspec_mode = ref false;

(* (thy,tyop) -> positions: HOL-Light param i = HOL4 canonical arg (perm i) *)
val tyvar_tab = ref ([] : ((string * string) * int list) list);
fun perm_of k = Option.map snd (List.find (fn (k',_) => k' = k) (!tyvar_tab));
fun set_perm k p = tyvar_tab := (k,p) :: !tyvar_tab;

(* the type(s) currently being defined: print bare *)
val self_tys = ref ([] : (string * string) list);

(* ----- monomorphization -----
   HOL Light's define_type cannot handle >2-tyvar nested recursion (probed:
   NS3_FAIL); types used in the cone at fixed name parameters are exported
   monomorphized at those parameters. (thy,tyop) -> per-canonical-arg:
   SOME ty = fixed at ty, NONE = kept as a parameter. The HOL4 bridge
   records the instantiation. *)
val mono_tab = ref ([] : ((string * string) * hol_type option list) list);
fun mono_of k = Option.map snd (List.find (fn (k',_) => k' = k) (!mono_tab));

(* type variables 'a 'b ... -> A B ... (or placeholder token in dtspec) *)
fun pvarty ty =
  let val n = dest_vartype ty
      val core = String.translate (fn #"'" => "" | c => str c) n
  in
    if !dtspec_mode then "TYV" ^ core ^ "Z"
    else String.map Char.toUpper core
  end;

(* ---------------- classification ---------------- *)

val opaque_tyops : (string * string * string) list =  (* (thy,tyop) -> candle name *)
  [];  (* filled by callers via opaque_ty_name *)

fun is_word8  ty = (dest_thy_type ty; ty = ``:word8``)  handle HOL_ERR _ => false;
fun is_word64 ty = (ty = ``:word64``) handle HOL_ERR _ => false;

(* builtin type printers *)
fun pty ty =
  if is_vartype ty then pvarty ty
  else if is_word8 ty then "w8"
  else if is_word64 ty then "w64"
  else let val {Tyop,Thy,Args} = dest_thy_type ty in
    case (Thy,Tyop) of
      ("min","bool") => "bool"
    | ("min","fun")  => "(" ^ pty (hd Args) ^ "->" ^ pty (hd (tl Args)) ^ ")"
    | ("num","num")  => "num"
    | ("integer","int") => "int"
    | ("list","list") => "((" ^ pty (hd Args) ^ ")list)"
    | ("option","option") => "((" ^ pty (hd Args) ^ ")option)"
    | ("pair","prod") => "(" ^ pty (hd Args) ^ "#" ^ pty (hd (tl Args)) ^ ")"
    | ("sum","sum") => "((" ^ pty (hd Args) ^ "," ^ pty (hd (tl Args)) ^ ")sum)"
    | ("one","one") => "(1)"      (* HOL Light unit type *)
    | ("string","char") => "char"
    | ("ternaryComparisons","ordering") => "ordering"
    | _ =>
      (* exported datatype: (A,B)name or (A)name or name; self-references in
         a datatype spec print bare; argument order per recorded permutation *)
      let
        val nm = rename Tyop
        (* monomorphized types: check fixed args, keep only parametric ones *)
        val Args =
          case mono_of (Thy,Tyop) of
            NONE => Args
          | SOME spec =>
            List.mapPartial (fn x => x)
              (ListPair.map
                 (fn (a, NONE) => SOME a
                   | (a, SOME fixed) =>
                     if a = fixed orelse is_vartype a then NONE
                     else raise Fail
                       ("monomorphized " ^ Thy ^ "$" ^ Tyop ^
                        " used at a non-fixed instance: " ^
                        Hol_pp.type_to_string a))
                 (Args, spec))
      in
        if !dtspec_mode andalso Lib.mem (Thy,Tyop) (!self_tys) then nm
        else case Args of
          [] => nm
        | _  =>
          let val args =
                case perm_of (Thy,Tyop) of
                  SOME p => map (fn i => List.nth (Args, i)) p
                | NONE => Args
          in "((" ^ String.concatWith "," (map pty args) ^ ")" ^ nm ^ ")" end
      end
  end;

(* ---------------- builtin constant table ---------------- *)
(* (thy,name) -> SOME (candle syntax, is_infix) *)
fun builtin (thy,name) =
  case (thy,name) of
    ("min","=") => SOME ("=", true)
  | ("bool","T") => SOME ("T", false)
  | ("bool","F") => SOME ("F", false)
  | ("bool","/\\") => SOME ("/\\", true)
  | ("bool","\\/") => SOME ("\\/", true)
  | ("min","==>") => SOME ("==>", true)
  | ("bool","~") => SOME ("~", false)
  | ("bool","!") => SOME ("!", false)   (* binder: handled in ptm *)
  | ("bool","?") => SOME ("?", false)
  | ("bool","COND") => SOME ("COND", false) (* handled in ptm *)
  | ("bool","LET") => SOME ("LET", false)   (* handled in ptm *)
  | ("bool","ARB") => SOME ("(@arb. T)", false)
  | ("bool","literal_case") => SOME ("cml_literal_case", false)
  | ("num","num_CASE") => SOME ("cml_num_CASE", false)
  | ("prim_rec","num_CASE") => SOME ("cml_num_CASE", false)
  | ("arithmetic","num_CASE") => SOME ("cml_num_CASE", false)
  | ("arithmetic","PRE") => SOME ("PRE", false)
  | ("arithmetic","FUNPOW") => SOME ("cml_FUNPOW", false)
  | ("arithmetic","ODD") => SOME ("ODD", false)
  | ("arithmetic","EVEN") => SOME ("EVEN", false)
  | ("pair",",") => SOME (",", true)
  | ("pair","FST") => SOME ("FST", false)
  | ("pair","SND") => SOME ("SND", false)
  | ("pair","UNCURRY") => SOME ("UNCURRY", false) (* handled: GABS *)
  | ("arithmetic","+") => SOME ("+", true)
  | ("arithmetic","-") => SOME ("-", true)
  | ("arithmetic","*") => SOME ("*", true)
  | ("arithmetic","<") => SOME ("<", true)
  | ("arithmetic","<=") => SOME ("<=", true)
  | ("arithmetic",">") => SOME (">", true)
  | ("arithmetic",">=") => SOME (">=", true)
  | ("arithmetic","DIV") => SOME ("DIV", true)
  | ("arithmetic","MOD") => SOME ("MOD", true)
  | ("arithmetic","EXP") => SOME ("EXP", true)
  | ("arithmetic","MIN") => SOME ("MIN", false)
  | ("arithmetic","MAX") => SOME ("MAX", false)
  | ("num","SUC") => SOME ("SUC", false)
  | ("prim_rec","<") => SOME ("<", true)
  (* integers: HOL Light calc_int names *)
  (* integers: HOL Light's int constants by NAME, prefix: the overloaded
     symbols (+, <, &, abs, ...) are resolved by type inference, which
     guessed real for lambda-bound operands and mistyped whole defines *)
  | ("integer","int_add") => SOME ("int_add", false)
  | ("integer","int_sub") => SOME ("int_sub", false)
  | ("integer","int_mul") => SOME ("int_mul", false)
  | ("integer","int_lt") => SOME ("int_lt", false)
  | ("integer","int_le") => SOME ("int_le", false)
  | ("integer","int_gt") => SOME ("int_gt", false)
  | ("integer","int_ge") => SOME ("int_ge", false)
  | ("integer","int_neg") => SOME ("int_neg", false)
  | ("integer","int_of_num") => SOME ("int_of_num", false)
  | ("integer","ABS") => SOME ("int_abs", false)
  | ("integer","int_ABS") => SOME ("int_abs", false)
  (* lists: HOL Light core *)
  | ("list","NIL") => SOME ("[]", false)
  | ("list","CONS") => SOME ("CONS", false)
  | ("list","APPEND") => SOME ("APPEND", false)
  | ("list","LENGTH") => SOME ("LENGTH", false)
  | ("list","MAP") => SOME ("MAP", false)
  | ("list","REVERSE") => SOME ("REVERSE", false)
  | ("list","HD") => SOME ("HD", false)
  | ("list","TL") => SOME ("TL", false)
  | ("list","NULL") => SOME ("NULL", false)
  | ("list","EL") => SOME ("cml_EL", false)        (* arg order differs! exported *)
  | ("list","EVERY") => SOME ("ALL", false)
  | ("list","EXISTS") => SOME ("EX", false)
  | ("list","MEM") => SOME ("MEM", false)          (* via set? HOL Light MEM : a->list->bool *)
  | ("list","ZIP") => SOME ("cml_ZIP", false)      (* HOL4 ZIP takes a pair; exported *)
  | ("list","FLAT") => SOME ("cml_FLAT", false)
  | ("list","FOLDR") => SOME ("cml_FOLDR", false)
  | ("list","TAKE") => SOME ("cml_TAKE", false)
  | ("list","DROP") => SOME ("cml_DROP", false)
  | ("list","LUPDATE") => SOME ("cml_LUPDATE", false)
  | ("list","oEL") => SOME ("cml_oEL", false)
  | ("list","ALL_DISTINCT") => SOME ("cml_ALL_DISTINCT", false)
  | ("rich_list","REPLICATE") => SOME ("REPLICATE", false)
  | ("alist","ALOOKUP") => SOME ("cml_ALOOKUP", false)
  (* options / sums *)
  | ("option","SOME") => SOME ("SOME", false)
  | ("option","NONE") => SOME ("NONE", false)
  | ("option","option_CASE") => SOME ("option_CASE", false) (* exported *)
  | ("sum","INL") => SOME ("INL", false)
  | ("sum","INR") => SOME ("INR", false)
  | ("sum","sum_CASE") => SOME ("sum_CASE", false)          (* exported *)
  | ("sum","OUTL") => SOME ("OUTL", false)
  | ("sum","OUTR") => SOME ("OUTR", false)
  | ("one","one") => SOME ("one", false)
  | ("combin","o") => SOME ("o", true)
  | ("combin","K") => SOME ("cml_K", false)
  | ("combin","I") => SOME ("I", false)
  | ("combin","S") => SOME ("cml_S", false)
  | ("combin","C") => SOME ("cml_C", false)
  | ("combin","W") => SOME ("cml_W", false)
  | ("string","CHR") => SOME ("cml_CHR", false)   (* opaque/bridged *)
  | ("string","ORD") => SOME ("cml_ORD", false)
  | ("string","char_lt") => SOME ("cml_char_lt", false)
  | ("pair","pair_CASE") => SOME ("pair_CASE", false)  (* handled in ptm *)
  | ("pair","CURRY") => SOME ("CURRY", false)
  | ("list","list_CASE") => SOME ("list_CASE", false)      (* exported *)
  (* sets: HOL4's MEM is `x IN set l` *)
  | ("bool","IN") => SOME ("IN", true)
  | ("list","LIST_TO_SET") => SOME ("set_of_list", false)
  (* integer ops whose HOL Light namesakes differ (HOL Light int_div is
     Euclidean, int_mod is a congruence): exported from HOL4's theorems *)
  | ("integer","Num") => SOME ("cml_Num", false)
  | ("integer","int_div") => SOME ("cml_int_div", false)
  | ("integer","int_mod") => SOME ("cml_int_mod", false)
  | _ => NONE;

(* theories whose constants must reach candle through the builtin table
   (or as opaques): a constant of one of these that falls through to its
   bare name would be a free variable in candle, so the printer records it
   and the drivers fail loudly *)
val builtin_thys =
  ["min","bool","pair","num","prim_rec","arithmetic","list","rich_list",
   "alist","option","sum","one","combin","string","integer","pred_set",
   "while","numeral","marker"];
val unmapped_seen = ref ([] : (string * string) list);
(* every cml_* name the printer emitted for a builtin: each must be defined
   by the driver's scaffolding/prelude, checked at the end of the export *)
val cml_used = ref ([] : string list);
fun note_cml s =
  if String.isPrefix "cml_" s andalso not (Lib.mem s (!cml_used))
  then cml_used := s :: !cml_used else ();

(* guarded defining equations (!x. c ==> l = r, e.g. integer int_div)
   become total ones l = if c then r else ARB: the value outside c is
   unconstrained in HOL4 too, and callers in the cone guard c *)
fun total_clause cj =
  let val b = snd (strip_forall cj)
  in if is_imp_only b then
       let val (c, eq) = dest_imp b
           val (l, r) = dest_eq eq
       in mk_eq (l, mk_cond (c, r, mk_arb (type_of r))) end
     else b
  end;

(* opaque constants: word/float leaves -> new_constant names. Polymorphic
   word ops are split per width (w8/w64) by their instance type; every
   opaque instance encountered is collected so the driver can emit its
   new_constant declaration in the prelude. *)
val opaque_seen = ref ([] : (string * string) list);  (* (name, pty type) *)

fun width_suffix ty =
  let
    val w8 = ``:word8`` and w64 = ``:word64``
    fun occurs t =
      Lib.can (find_term (fn _ => false)) t  (* placeholder, not used *)
    fun has goal ty =
      if Type.compare (ty, goal) = EQUAL then true
      else case Lib.total dest_thy_type ty of
             SOME {Args,...} => List.exists (has goal) Args
           | NONE => false
  in
    (if has w8 ty then "8" else "") ^ (if has w64 ty then "64" else "")
  end;

fun opaque_const_at (thy,name) ty =
  if Lib.mem thy ["words","fcp","binary_ieee","machine_ieee","fpSem",
                  "integer_word"]
  then
    let val nm = "cml_" ^ name ^
                 (if Lib.mem thy ["words","integer_word"] then width_suffix ty
                  else "")
    in SOME nm end
  else NONE;

(* ---------------- numerals / literals ---------------- *)

fun is_numeral tm = Literal.is_numeral tm;
fun numeral_str tm = Arbnum.toString (Literal.relaxed_dest_numeral tm);
fun is_strlit tm = Literal.is_string_lit tm handle HOL_ERR _ => false;
fun is_charlit tm = Literal.is_char_lit tm handle HOL_ERR _ => false;

fun escape_string s =
  String.translate
    (fn #"\\" => "\\\\" | #"\"" => "\\\"" | #"\n" => "\\n" | c => str c) s;

(* ---------------- the term printer ---------------- *)

val avoid_dollar = String.translate (fn #"$" => "_" | c => str c);

(* when set, variables print with their type: used for record accessor /
   fupd defines, whose HOL Light inference would otherwise generalise
   `f : A -> B` and make the fupd type-changing *)
val annotate_vars = ref false;

fun var_str v =
  let val (n,ty) = dest_var v
      val s = rename (avoid_dollar n)
  in if !annotate_vars then "(" ^ s ^ ":" ^ pty ty ^ ")" else s end;

fun ptm tm =
  if is_numeral tm then numeral_str tm
  else if is_strlit tm then "\"" ^ escape_string (Literal.relaxed_dest_string_lit tm) ^ "\""
  else if is_charlit tm then
    "(cml_CHR " ^ Int.toString (Char.ord (Literal.dest_char_lit tm)) ^ ")"
  else if is_var tm then var_str tm
  else if is_const tm then pconst tm
  else if is_cond tm then
    let val (g,t,e) = dest_cond tm in
      "(if " ^ ptm g ^ " then " ^ ptm t ^ " else " ^ ptm e ^ ")"
    end
  else if is_forall tm then pbinder "!" (dest_forall tm)
  else if is_exists tm then pbinder "?" (dest_exists tm)
  else if is_select tm then pbinder "@" (dest_select tm)
  else if is_conj tm then pbin "/\\" (dest_conj tm)
  else if is_disj tm then pbin "\\/" (dest_disj tm)
  else if is_imp_only tm then pbin "==>" (dest_imp tm)
  else if is_neg tm then "(~(" ^ ptm (dest_neg tm) ^ "))"
  else if is_eq tm then pbin "=" (dest_eq tm)
  else if is_let tm then plet tm
  else if pairSyntax.is_pair tm then
    let val (a,b) = pairSyntax.dest_pair tm
    in "(" ^ ptm a ^ "," ^ ptm b ^ ")" end
  else if is_abs tm then
    let val (v,b) = dest_abs tm in "(\\" ^ var_str v ^ ". " ^ ptm b ^ ")" end
  else if pairSyntax.is_pabs tm then
    let val (p,b) = pairSyntax.dest_pabs tm
    in "(\\" ^ ppat p ^ ". " ^ ptm b ^ ")" end
  else (* application *)
    let val (f,xs) = strip_comb tm in papp f xs end

and ppat p =                          (* pair pattern in a GABS *)
  if is_var p then var_str p
  else let val (a,b) = pairSyntax.dest_pair p
       in "(" ^ ppat a ^ "," ^ ppat b ^ ")" end

and pbinder q (v,b) = "(" ^ q ^ var_str v ^ ". " ^ ptm b ^ ")"
and pbin opr (a,b) = "(" ^ ptm a ^ " " ^ opr ^ " " ^ ptm b ^ ")"
and plet tm =
  let val (binds, body) = pairSyntax.strip_anylet tm
      fun pb (v,e) = ppat v ^ " = " ^ ptm e
  in "(let " ^ String.concatWith " and "
        (map pb (List.concat binds)) ^ " in " ^ ptm body ^ ")"
  end

and pconst c =
  let val k as (thy,name) = let val {Thy,Name,...} = dest_thy_const c in (Thy,Name) end
  in if k = ("bool","ARB") then
       (* typed: an untyped ARB leaves its type variables free (e.g. the
          ARB base of a record literal under a type-changing fupd), which
          new_specification rejects *)
       "(@arb:" ^ pty (type_of c) ^ ". T)"
     else case builtin k of
       SOME (s, true) => "(" ^ s ^ ")"     (* infix used curried: parenthesize *)
     | SOME (s, false) => (note_cml s; s)
     | NONE =>
       (case opaque_const_at k (type_of c) of
          SOME s =>
            (if List.exists (fn (s',_) => s' = s) (!opaque_seen) then ()
             else opaque_seen := (s, pty (type_of c)) :: !opaque_seen;
             s)
        | NONE =>
            (if Lib.mem thy builtin_thys andalso
                not (Lib.mem k (!unmapped_seen))
             then unmapped_seen := k :: !unmapped_seen else ();
             rename name))
  end

and papp f xs =
  (* infix builtins applied to exactly 2 args print infix *)
  let
    val infix_s =
      if is_const f then
        (case builtin (let val {Thy,Name,...} = dest_thy_const f in (Thy,Name) end) of
           SOME (s, true) => SOME s | _ => NONE)
      else NONE
    val num_ty = mk_thy_type {Thy="num", Tyop="num", Args=[]}
    fun operand a =
      if Lib.mem (valOf infix_s) ["+","-","*","<","<=",">",">=","DIV","MOD","EXP"]
         andalso Type.compare (type_of a, num_ty) = EQUAL
      then "(" ^ ptm a ^ ":num)" else ptm a
  in
    case (infix_s, xs) of
      (SOME s, [a,b]) =>
        if s = "," then "(" ^ ptm a ^ "," ^ ptm b ^ ")"
        else "(" ^ operand a ^ " " ^ s ^ " " ^ ptm b ^ ")"
    | _ =>
      "(" ^ String.concatWith " " (ptm f :: map ptm xs) ^ ")"
  end;

(* ---------------- datatype export ---------------- *)

(* find all "TYV<name>Z" tokens in order of first occurrence *)
fun scan_tokens s =
  let
    val n = String.size s
    fun upto i j = String.substring (s, i, j - i)
    fun loop i acc =
      if i >= n then List.rev acc
      else if i + 3 <= n andalso upto i (i+3) = "TYV" then
        let fun fin j = if j < n andalso String.sub (s,j) <> #"Z" then fin (j+1)
                        else j
            val j = fin (i+3)
            val tok = upto i (j+1)
        in loop (j+1) (if Lib.mem tok acc then acc else tok :: acc) end
      else loop (i+1) acc
  in loop 0 [] end;

fun replace_all (old, new) s =
  let
    val n = String.size s val m = String.size old
    fun loop i acc =
      if i + m > n then acc ^ String.extract (s, i, NONE)
      else if String.substring (s, i, m) = old then loop (i+m) (acc ^ new)
      else loop (i+1) (acc ^ str (String.sub (s, i)))
  in loop 0 "" end;

fun letter i = str (Char.chr (Char.ord #"A" + i));

(* one datatype: returns the HOL Light define_type spec string, assigning
   tyvars A,B,C... by first occurrence and recording the reference
   permutation for this type operator *)
fun dt_spec ty =
  let
    val {Tyop,Thy,Args} = dest_thy_type ty
    (* instantiate fixed (monomorphized) parameters in constructor types *)
    val (Args, fix_subst) =
      case mono_of (Thy,Tyop) of
        NONE => (Args, [])
      | SOME spec =>
        (List.mapPartial (fn x => x)
           (ListPair.map (fn (a, NONE) => SOME a | (_, SOME _) => NONE)
                         (Args, spec)),
         List.mapPartial (fn x => x)
           (ListPair.map (fn (a, SOME fixed) => SOME (a |-> fixed)
                           | (_, NONE) => NONE)
                         (Args, spec)))
    val cons = map (Term.inst fix_subst) (TypeBase.constructors_of ty)
    val () = self_tys := [(Thy,Tyop)]
    val () = dtspec_mode := true
    fun con_spec c =
      let val (argtys,_) = strip_fun (type_of c)
          val {Name,...} = dest_thy_const c
      in String.concatWith " " (rename Name :: map pty argtys) end
    val body = String.concatWith " | " (map con_spec cons)
                 handle e => (dtspec_mode := false; raise e)
    val () = dtspec_mode := false
    (* assign letters by first occurrence; record the permutation *)
    val toks = scan_tokens body
    val canon_toks = map (fn a => "TYV" ^ String.translate
                            (fn #"'" => "" | c => str c) (dest_vartype a) ^ "Z")
                         Args
    (* HOL Light param position i <- canonical index of toks[i] *)
    fun idx_of t =
      let fun go _ [] = raise Fail ("tyvar token not canonical: " ^ t)
            | go i (x::xs) = if x = t then i else go (i+1) xs
      in go 0 canon_toks end
    val positions = map idx_of toks
    val () = if length toks = length Args then set_perm (Thy,Tyop) positions
             else if null Args then ()
             else raise Fail ("phantom type parameter in " ^ Thy ^ "$" ^ Tyop)
    val body = #2 (List.foldl (fn (t,(i,s)) =>
                     (i+1, replace_all (t, letter i) s)) (0, body) toks)
  in
    rename Tyop ^ " = " ^ body
  end;

(* case constant define: from TypeBase case_def *)
fun case_def_clauses ty =
  let val cd = TypeBase.case_def_of ty
  in map (fn cj => snd (strip_forall cj)) (strip_conj (concl cd)) end;

(* accessors and fupds for records *)
fun record_defs ty =
  let
    val accs = TypeBase.accessors_of ty handle HOL_ERR _ => []
    val upds = TypeBase.updates_of ty handle HOL_ERR _ => []
    fun clauses th = map (fn cj => snd (strip_forall cj)) (strip_conj (concl th))
  in
    map clauses accs @ map clauses upds
  end;

(* HOL Light typechecks a quotation with ONE type per variable NAME; clause
   pattern variables (a, a0, ...) recur across clauses at different types.
   Freshen: a free var keeps its name only if it occurs in EVERY clause at
   the same type; otherwise it gets a per-clause suffix. *)
fun freshen_clauses clauses =
  let
    val fvss = map free_vars clauses
    fun in_all (v:term) =
      List.all (fn fvs => List.exists (fn u => Term.term_eq u v) fvs) fvss
    fun fresh1 (i, cl) =
      let
        val sub =
          List.mapPartial
            (fn v => if in_all v then NONE
                     else let val (n,ty) = dest_var v
                          in SOME (v |-> mk_var (n ^ "_" ^ Int.toString i, ty))
                          end)
            (free_vars cl)
      in Term.subst sub cl end
  in
    case clauses of
      [_] => clauses                       (* single clause: nothing to do *)
    | _ => map fresh1 (Lib.enumerate 0 clauses)
  end;

(* print one define from equation clauses *)
fun pdefine clauses =
  "let _ = define `" ^
  String.concatWith " /\\\n   " (map ptm (freshen_clauses clauses)) ^ "`;;";

(* a datatype's case constant, from the recursion theorem <nm>_DT returned
   by define_type; falls back (loudly) to the generic define *)
fun pcase_define nm clauses =
  let val body = String.concatWith " /\\\n   " (map ptm (freshen_clauses clauses))
  in "let " ^ nm ^ "_CASE_def =\n  try new_recursive_definition (snd " ^ nm ^
     "_DT) `" ^ body ^ "`\n  with Failure _ -> (warn true \"RS_CASE_FALLBACK " ^
     nm ^ "\"; define `" ^ body ^ "`);;"
  end;

(* OCaml binds a capitalised identifier as a CONSTRUCTOR pattern
   (`let Boolv_def = ...` is "Undefined constructor"): ML names of
   theorems must start lower-case *)
fun ml_name n =
  if n <> "" andalso Char.isUpper (String.sub (n, 0)) then "rs_" ^ n else n;

(* a define with a name binding (for eyeballing) *)
fun pdefine_named name clauses =
  "let " ^ ml_name name ^ " = define `" ^
  String.concatWith " /\\\n   " (map ptm (freshen_clauses clauses)) ^ "`;;";

(* ---------------- smart definitions ----------------
   HOL Light's generic `define` re-derives pattern disjointness and
   termination inside the verified kernel: on a 9-clause nested-pattern
   function it ground for >15 min, and it cannot prove termination of
   recursion that passes through case-combinator lambdas (nsLookup,
   maybe_all_list). So multi-clause definitions go through two cheap,
   conservative steps instead:
     1. the constant is introduced by a CASE-TREE: HOL4's own pattern
        compiler (TypeBase.mk_pattern_fn) turns the clauses' non-recursion
        arguments into nested case constants; recursive functions are
        introduced by new_recursive_definition on the recursion theorem of
        their structural argument (primitive recursion, no termination
        proof), non-recursive ones by a single-clause define;
     2. the ORIGINAL clauses (printed, as always, from the HOL4 defining
        theorem) are then PROVED in the candle kernel from that definition
        by rewriting with the case constants' definitions.
   The theorem bound to <name> is the clause theorem of step 2, so what
   callers rewrite with is exactly the HOL4 text, kernel-checked. *)

fun clause_parts cl =
  let val (l, r) = dest_eq cl
      val (f, args) = strip_comb l
  in (f, args, r) end;

fun is_ctor_pat t =
  let val (h, _) = strip_comb t
  in is_const h andalso
     (Lib.mem (#Name (dest_thy_const h)) ["0","NIL","CONS","SUC"] orelse
      (TypeBase.is_constructor h handle HOL_ERR _ => false))
  end handle HOL_ERR _ => false;

(* full applications of f in r (as many args as the clauses' lhs has) *)
fun calls_of f r = find_terms (fn t => is_const t andalso same_const t f) r;
fun full_calls f arity r =
  find_terms (fn t => let val (h, a) = strip_comb t
                      in is_const h andalso same_const h f andalso
                         length a = arity end) r;
(* every occurrence of the constant f in r is the head of a full call *)
fun only_full_calls f arity r =
  length (find_terms (fn t => is_const t andalso same_const t f) r) =
  length (full_calls f arity r);

(* a recursive call's full argument list (calls may be partially applied
   under a combinator; those have too few args and are rejected) *)
fun call_args arity t =
  let val (_, a) = strip_comb t in if length a = arity then SOME a else NONE end;

(* lift a top-level case on a whole-argument variable into clauses *)
fun lift_clause cl =
  let val (f, args, r) = clause_parts cl
  in
    (let val (_, scrut, rows) = TypeBase.dest_case r
     in if is_var scrut andalso List.exists (fn a => term_eq a scrut) args
        then List.concat (map (fn (pat, rhs) =>
               lift_clause (mk_eq (list_mk_comb (f, map (fn a =>
                   if term_eq a scrut then pat else a) args),
                 Term.subst [scrut |-> pat] rhs))) rows)
        else [cl]
     end handle HOL_ERR _ => [cl])
  end;

(* the structural position: every clause has a one-level constructor
   pattern there, and every recursive call passes, there, a variable bound
   by that clause's pattern at that position *)
fun pr_position clauses =
  let
    val parts = map clause_parts clauses
    val (f, args0, _) = hd parts
    val n = length args0
    fun ok i =
      List.all (fn (_, args, r) =>
        let val p = List.nth (args, i)
            val (_, cargs) = strip_comb p
        in is_ctor_pat p andalso List.all is_var cargs andalso
           only_full_calls f n r andalso
           List.all (fn c =>
             case call_args n c of
               NONE => false
             | SOME a => let val x = List.nth (a, i)
                         in is_var x andalso List.exists (fn v => term_eq v x) cargs end)
             (full_calls f n r)
        end) parts
    fun find i = if i >= n then NONE else if ok i then SOME i else find (i+1)
  in find 0 end;

fun recursion_thm_of ty =
  let val {Thy, Tyop, ...} = dest_thy_type ty
  in case (Thy, Tyop) of
       ("num","num") => "num_RECURSION"
     | ("list","list") => "list_RECURSION"
     | ("option","option") => "option_RECURSION"
     | ("sum","sum") => "sum_RECURSION"
     | _ => "(snd " ^ rename Tyop ^ "_DT)"
  end;

(* candle ML name of the defining theorem of a case constant *)
fun case_def_ml c =
  let val {Thy, Name, ...} = dest_thy_const c
  in case (Thy, Name) of
       ("arithmetic","num_CASE") => SOME "cml_num_CASE_def"
     | ("prim_rec","num_CASE") => SOME "cml_num_CASE_def"
     | ("num","num_CASE") => SOME "cml_num_CASE_def"
     | ("bool","literal_case") => SOME "cml_literal_case_def"
     | _ => if String.isSuffix "_CASE" Name
            then SOME (ml_name (rename Name ^ "_def")) else NONE
  end handle HOL_ERR _ => NONE;

fun fresh_args avoid tys =
  let fun go _ [] _ = []
        | go i (ty :: rest) av =
            let val v = variant av (mk_var ("xa" ^ Int.toString i, ty))
            in v :: go (i+1) rest (v :: av) end
  in go 0 tys avoid end;

(* case tree for rows (argument-pattern lists) over the variables xs *)
fun case_tree xs rows =
  case rows of
    [(ps, r)] =>
      if List.all is_var ps andalso
         length (Lib.mk_set (map (fst o dest_var) ps)) = length ps
      then Term.subst (ListPair.map (fn (p, x) => p |-> x) (ps, xs)) r
      else case_tree' xs rows
  | _ => case_tree' xs rows
and case_tree' xs rows =
  let val tup = pairSyntax.list_mk_pair
      val fnt = TypeBase.mk_pattern_fn (map (fn (ps, r) => (tup ps, r)) rows)
  in Term.beta_conv (mk_comb (fnt, tup xs))
     handle HOL_ERR _ => mk_comb (fnt, tup xs)
  end;

(* the rewrite list that reduces a case tree: every case constant in it *)
fun case_defs_in tms =
  Lib.mk_set (List.mapPartial case_def_ml
    (List.concat (map (find_terms (fn t => is_const t andalso
                                    Lib.can case_def_ml t andalso
                                    isSome (case_def_ml t))) tms)));

val smart_log = ref ([] : (string * string) list);   (* (name, route) *)

(* ML names of clause theorems that are safe as rewrite rules: excluded
   are recursive functions with an all-variable clause (rewriting with
   them never stops, e.g. compare_aux) *)
val rewrite_safe = ref ([] : string list);
fun note_rewrite recursive clauses nm =
  if recursive andalso
     List.exists (fn cl => List.all is_var (#2 (clause_parts cl))) clauses
  then () else rewrite_safe := nm :: !rewrite_safe;

fun pdefine_smart name clauses0 =
  let
    val mlnm = ml_name name
    val (f, args0, _) = clause_parts (hd clauses0)
    val n = length args0
    val recursive = List.exists (fn cl => not (null (calls_of f (#3 (clause_parts cl))))) clauses0
    val all_var_single =
      (case clauses0 of [cl] => List.all is_var (#2 (clause_parts cl)) | _ => false)
    val lifted = recursive andalso not (isSome (pr_position clauses0))
    val clauses = if lifted then List.concat (map lift_clause clauses0)
                  else clauses0
    val avoid = List.concat (map free_vars clauses)
    val xs = fresh_args avoid (map type_of args0)
    (* the clause theorem proved: HOL4's clauses; for a lifted recursive
       function, the per-constructor clauses HOL4's dest_case gives *)
    val orig_text = String.concatWith " /\\\n   " (map ptm (freshen_clauses clauses))
    val () = note_rewrite recursive clauses mlnm
    fun proof_of deftext cases =
      "let " ^ mlnm ^ " = prove (`" ^ orig_text ^ "`,\n  REWRITE_TAC ["
      ^ String.concatWith "; " ((mlnm ^ "_tree") ::
          ["FST", "SND", "NOT_SUC", "PRE"] @ cases) ^ "]);;"
  in
    if all_var_single andalso not recursive then
      (smart_log := (name, "define") :: !smart_log; pdefine_named name clauses0)
    else if not recursive then
      if length clauses0 = 1 then
        (smart_log := (name, "define") :: !smart_log; pdefine_named name clauses0)
      else
        let val rows = map (fn cl => let val (_, a, r) = clause_parts cl in (a, r) end) clauses0
            val tree = case_tree xs rows
            val tl = mk_eq (list_mk_comb (f, xs), tree)
            val cases = case_defs_in [tree]
        in smart_log := (name, "case-tree") :: !smart_log;
           "let " ^ mlnm ^ "_tree = define `" ^ ptm tl ^ "`;;\n" ^
           proof_of () cases
        end
    else
      case pr_position clauses of
        NONE => (smart_log := (name, "define (recursive, no structural arg)") :: !smart_log;
                 pdefine_named name clauses0)
      | SOME i =>
        let
          val parts = map clause_parts clauses
          (* group by constructor at i, first-appearance order *)
          fun ctor_of (_, a, _) = fst (strip_comb (List.nth (a, i)))
          val ctors = List.foldl (fn (p, acc) =>
                        if List.exists (fn c => same_const c (ctor_of p)) acc
                        then acc else acc @ [ctor_of p]) [] parts
          val others = List.filter (fn j => j <> i) (List.tabulate (n, fn j => j))
          val oxs = map (fn j => List.nth (xs, j)) others
          fun group c =
            let
              val ps = List.filter (fn p => same_const (ctor_of p) c) parts
              val (_, a1, _) = hd ps
              val canon = snd (strip_comb (List.nth (a1, i)))
              fun norm (_, a, r) =
                let val cargs = snd (strip_comb (List.nth (a, i)))
                    val sub = ListPair.map (fn (v, w) => v |-> w) (cargs, canon)
                in (map (fn j => Term.subst sub (List.nth (a, j))) others,
                    Term.subst sub r)
                end
              val rows = map norm ps
              val tree = if null others then #2 (hd rows) else case_tree oxs rows
              val largs = List.tabulate (n, fn j =>
                            if j = i then List.nth (a1, i) else List.nth (xs, j))
            in (mk_eq (list_mk_comb (f, largs), tree), tree) end
          val eqs = map group ctors
          val cases = case_defs_in (map #2 eqs)
          val rth = recursion_thm_of (type_of (List.nth (args0, i)))
        in
          smart_log := (name, "primitive recursion on arg " ^ Int.toString i ^
                                (if lifted then " (case-lifted)" else "")) :: !smart_log;
          "let " ^ mlnm ^ "_tree = new_recursive_definition " ^ rth ^ " `" ^
          String.concatWith " /\\\n   " (map (ptm o #1) eqs) ^ "`;;\n" ^
          proof_of () cases
        end
  end;

end
