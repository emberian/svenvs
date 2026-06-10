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
  | ("integer","int_add") => SOME ("+", true)
  | ("integer","int_sub") => SOME ("-", true)
  | ("integer","int_mul") => SOME ("*", true)
  | ("integer","int_lt") => SOME ("<", true)
  | ("integer","int_le") => SOME ("<=", true)
  | ("integer","int_gt") => SOME (">", true)
  | ("integer","int_ge") => SOME (">=", true)
  | ("integer","int_neg") => SOME ("--", false)
  | ("integer","int_of_num") => SOME ("&", false)
  | ("integer","ABS") => SOME ("abs", false)
  | ("integer","int_ABS") => SOME ("abs", false)
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
  | _ => NONE;

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

fun var_str v =
  let val (n,_) = dest_var v
  in rename (avoid_dollar n) end;

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
  in case builtin k of
       SOME (s, true) => "(" ^ s ^ ")"     (* infix used curried: parenthesize *)
     | SOME (s, false) => s
     | NONE =>
       (case opaque_const_at k (type_of c) of
          SOME s =>
            (if List.exists (fn (s',_) => s' = s) (!opaque_seen) then ()
             else opaque_seen := (s, pty (type_of c)) :: !opaque_seen;
             s)
        | NONE => rename name)
  end

and papp f xs =
  (* infix builtins applied to exactly 2 args print infix *)
  let
    val infix_s =
      if is_const f then
        (case builtin (let val {Thy,Name,...} = dest_thy_const f in (Thy,Name) end) of
           SOME (s, true) => SOME s | _ => NONE)
      else NONE
  in
    case (infix_s, xs) of
      (SOME s, [a,b]) =>
        if s = "," then "(" ^ ptm a ^ "," ^ ptm b ^ ")"
        else "(" ^ ptm a ^ " " ^ s ^ " " ^ ptm b ^ ")"
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

(* a define with a name binding (for eyeballing) *)
fun pdefine_named name clauses =
  "let " ^ name ^ " = define `" ^
  String.concatWith " /\\\n   " (map ptm (freshen_clauses clauses)) ^ "`;;";

end
