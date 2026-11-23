(* Run on fresh fixtures written by the Obend test executable. *)
Theory pancakeDifferential
Ancestors
  panPtreeConversion panSem
Libs
  preamble

Definition fixture_state_def:
  fixture_state (ws:word64 list) clk count =
    (ARB:(64,unit) panSem$state) with
      <| locals := FEMPTY |+ («base»,ValWord 256w);
         globals := FEMPTY; clock := clk; be := F;
         memaddrs := {a | 256 <= w2n a /\ w2n a < 256 + 8 * count /\ w2n a MOD 8 = 0};
         memory := (λa. Word (EL ((w2n a - 256) DIV 8) ws)) |>
End

Definition observation_def:
  observation (r,s:(64,unit) panSem$state) =
    (r,s.clock,GENLIST (λi. (case s.memory (n2w (256 + 8*i)) of Word w => w)) 25)
End

Definition parsed_body_def:
  parsed_body src =
    case parse_topdecs_to_ast src of
      INL [Function f] => SOME (f.body:64 panLang$prog)
    | _ => NONE
End

val dir = valOf (OS.Process.getEnv "PANCAKE_CORPUS")
fun file name =
  let val f = TextIO.openIn (OS.Path.concat (dir,name))
      val contents = TextIO.inputAll f
  in TextIO.closeIn f; contents end
fun lines name = String.tokens (fn c => c = #"\n") (file name)
fun term s = Parse.Term [QUOTE s]
fun num s = numSyntax.mk_numeral (Arbnum.fromString s)
fun words s = term ("[" ^ String.concatWith ";" (map (fn x => x ^ "w")
                      (String.fields (fn c => c = #",") s)) ^ "]:word64 list")
fun value t = rhs (concl (EVAL t))
fun check tag actual expected =
  if aconv actual expected then ()
  else raise Fail (tag ^ " differs: " ^ term_to_string actual)

(* The Obend pin calls the anonymous tuple constructor RStruct. The svenvs
   pin calls it Struct. Both are the word-layout constructor used by Store. *)
val tuple = (prim_mk_const {Thy="panLang",Name="RStruct"}
             handle HOL_ERR _ => prim_mk_const {Thy="panLang",Name="Struct"})
val _ = overload_on ("SpineTuple",tuple)
val steps = map (fn line => term ("(" ^ line ^ "):64 panLang$prog"))
                (lines "keccakF1600.hol")
val _ = if length steps = 73 then () else raise Fail "expected 72 stores and a return"

(* Normalize the 25 observed memory words between stores. Stores preserve
   the parameter and clock. This bounds the size of HOL function-update terms. *)
fun runKeccak ws clk count =
  let fun run [p] input =
            value “observation (evaluate (^p,fixture_state ^input ^clk ^count))”
        | run (p::ps) input =
            let val (head,_) = strip_comb p
                val _ = check "stage constructor" head “panLang$Store:64 panLang$exp -> 64 panLang$exp -> 64 panLang$prog”
                val res = value “observation (evaluate (^p,fixture_state ^input ^clk ^count))”
                val (r,rest) = pairSyntax.dest_pair res
                val (clock,output) = pairSyntax.dest_pair rest
                val _ = if optionSyntax.is_none r andalso aconv clock clk then ()
                        else raise Fail "stage failed or consumed clock"
            in run ps output end
        | run [] _ = raise Fail "missing return"
  in run steps ws end

fun runCase row =
  case String.fields (fn c => c = #"\t") row of
    [id,name,k,n,input,ret,k',output] =>
    let val ws = words input and clk = num k and count = num n
        val result = case ret of
          "timeout" => “SOME panSem$TimeOut : 64 panSem$result option”
        | "error" => “SOME panSem$Error : 64 panSem$result option”
        | w => term ("SOME (panSem$Return (ValWord (" ^ w ^ "w:word64)))")
        val actual =
          if name = "keccakF1600" then runKeccak ws clk count
          else let val src = stringSyntax.fromMLstring (file (name ^ ".pnk"))
                   val p = optionSyntax.dest_some (value “parsed_body ^src”)
               in value “observation (evaluate (^p,fixture_state ^ws ^clk ^count))” end
        val expected = pairSyntax.mk_pair(result,pairSyntax.mk_pair(num k',words output))
        val _ = check id actual expected
    in print (id ^ ": HOL4 return, clock and 25 lanes agree\n"); id end
  | _ => raise Fail "invalid corpus row"

val ids = map runCase (lines "cases.tsv")
val _ = if ids = ["zero","empty","abc","loop","timeout","unmapped","badshift"]
        then () else raise Fail "incomplete corpus"
