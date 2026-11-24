(* HOL4 runs Obend's five Pancake kernels on concrete inputs under CakeML's
   semantics, before and after the proved optimizer.

   Each kernel's own theory (obend<Kernel>Theory, built by pancakeKernelLib)
   holds the verified parser's reading of the emitted source and of the
   printed optimizer output, and proves that every function of the printed
   program evaluates as the original does. Each vector here is EVAL on the
   original body; the optimized conjunct follows from that theorem.

   The rows written to $PANCAKE_KERNELS/opt/eval.tsv go to the native run,
   which compares both compiled binaries with them. *)
Theory pancakeKernelOpt
Ancestors
  obendBeltLatch obendKeccakF1600 obendCshake256 obendMacaroonVerify obendKmac256
Libs
  pancakeKernelLib

(* ------------------------------------------------------------------------
   Locals under EVAL. panSem extends `locals` with |+ on every assignment
   and restores it with \\ after every Dec. On a finite-map term those
   layers pile up, so each lookup walks every earlier update and a loop's
   cost grows with its iteration count. `kernel_locals` keeps one entry per
   variable; these rules are its whole interface to EVAL, and the state is
   rewritten to it before each evaluation.
   ------------------------------------------------------------------------ *)

Definition kernel_locals_def[nocompute]:
  kernel_locals (l:(mlstring # 64 panSem$v) list) = alist_to_fmap l
End

Theorem kernel_locals_FLOOKUP[compute]:
  FLOOKUP (kernel_locals l) k = ALOOKUP l k
Proof
  simp[kernel_locals_def, alistTheory.ALOOKUP_EQ_FLOOKUP]
QED

Theorem kernel_locals_FUPDATE[compute]:
  kernel_locals l |+ (k, v) = kernel_locals ((k, v) :: FILTER (λ(k',v'). k' <> k) l)
Proof
  simp[kernel_locals_def, finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE,
       alistTheory.ALOOKUP_EQ_FLOOKUP, alistTheory.ALOOKUP_FILTER] >> rw[]
QED

Theorem kernel_locals_DOMSUB[compute]:
  kernel_locals l \\ k = kernel_locals (FILTER (λ(k',v'). k' <> k) l)
Proof
  simp[kernel_locals_def, finite_mapTheory.fmap_eq_flookup, finite_mapTheory.DOMSUB_FLOOKUP_THM,
       alistTheory.ALOOKUP_EQ_FLOOKUP, alistTheory.ALOOKUP_FILTER] >> rw[]
QED

Theorem kernel_state_locals:
  kernel_state (s:(64,'ffi) panSem$state) args c ws =
    s with <| locals := kernel_locals (REVERSE (MAP (λ(v,w:word64). (v, ValWord w)) args));
              globals := FEMPTY; clock := c; be := F;
              memaddrs := {a | 256 <= w2n a /\ w2n a < 256 + 8 * LENGTH ws /\
                               w2n a MOD 8 = 0};
              memory := kernel_memory (kernel_image 256 ws) |>
Proof
  simp[pancakeKernelTheory.kernel_state_def, kernel_locals_def,
       alistTheory.FUPDATE_LIST_EQ_APPEND_REVERSE]
QED

(* ------------------------------------------------------------------------
   Evaluation vectors. `run_vector` proves, for every state s,

     kernel_obs n (evaluate (fun_body F K_decls, kernel_state s args c ws)) = r /\
     kernel_obs n (evaluate (fun_body F K_opt_decls, kernel_state s args c ws)) = r

   The first conjunct is EVAL on the parsed body. The second is the first
   rewritten with K_evaluate, so the printed program that CakeML compiles is
   covered by proof rather than by a second evaluation.
   ------------------------------------------------------------------------ *)

type kernel_vector = {kernel : string, func : string, id : string,
               args : (string * Arbnum.num) list, clock : int,
               image : Arbnum.num list, obs : int}

fun theory_of kernel =
  "obend" ^ String.str (Char.toUpper (String.sub (kernel, 0))) ^
  String.extract (kernel, 1, NONE)

val s_var = mk_var ("s", ``:(64,'ffi) panSem$state``)
fun word64 n = wordsSyntax.mk_wordi (n, 64)
val strlit_tm = rator ``«x»``
fun mlstr v = mk_comb (strlit_tm, stringSyntax.fromMLstring v)
fun words_tm ns = listSyntax.mk_list (map word64 ns, ``:word64``)
fun args_tm args =
  listSyntax.mk_list (map (fn (v, n) => pairSyntax.mk_pair (mlstr v, word64 n)) args,
                      ``:mlstring # word64``)
fun num_of w = numSyntax.dest_numeral (rand w)
fun csv ns = String.concatWith "," (map Arbnum.toString ns)

fun vector_state ({args, clock, image, ...} : kernel_vector) =
  list_mk_icomb (``kernel_state``,
                 [s_var, args_tm args, numSyntax.term_of_int clock, words_tm image])

fun vector_obs (v : kernel_vector) decls =
  list_mk_icomb (``kernel_obs``,
    [numSyntax.term_of_int (#obs v),
     mk_icomb (``panSem$evaluate``,
               pairSyntax.mk_pair (list_mk_icomb (``fun_body``, [mlstr (#func v), decls]),
                                   vector_state v))])

(* the theorem, the returned word, and the observed memory words *)
fun run_vector (v : kernel_vector) =
  let
    val thy = theory_of (#kernel v)
    val decls = prim_mk_const {Thy = thy, Name = #kernel v ^ "_decls"}
    val opt_decls = prim_mk_const {Thy = thy, Name = #kernel v ^ "_opt_decls"}
    val label = #kernel v ^ " " ^ #id v
    val t0 = Time.now ()
    val body_th =
      (RAND_CONV (REWR_CONV (DB.fetch thy (#kernel v ^ "_decls_def"))) THENC EVAL)
        (list_mk_icomb (``fun_body``, [mlstr (#func v), decls]))
    val th = (RAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV body_th) THENC
                                    RAND_CONV (REWR_CONV kernel_state_locals))) THENC EVAL)
               (vector_obs v decls)
    val (r, out) = pairSyntax.dest_pair (rhs (concl th))
    val status =
      if null (free_vars r) andalso null (free_vars out) andalso optionSyntax.is_some r
      then num_of (rand (rand (rand (optionSyntax.dest_some r))))
      else raise ERR "run_vector" (label ^ " did not return a word: " ^ term_to_string r)
    val _ = if aconv r ``SOME (panSem$Return (ValWord ^(word64 status)))`` then ()
            else raise ERR "run_vector" (label ^ " did not return normally: " ^ term_to_string r)
    val opt_th = RAND_CONV (REWR_CONV (DB.fetch thy (#kernel v ^ "_evaluate")))
                           (vector_obs v opt_decls)
    val vth = save_thm (#kernel v ^ "_" ^ #id v, GEN s_var (CONJ th (TRANS opt_th th)))
  in
    say (label ^ ": returns " ^ Arbnum.toString status ^ " (" ^ since t0 ^ "s)");
    (vth, status, map num_of (fst (listSyntax.dest_list out)))
  end

(* One row per vector for the native comparison: the inputs as they sit in
   memory, the returned word and the observed words. *)
fun vector_row (v : kernel_vector) status out =
  String.concatWith "\t"
    [#kernel v, #id v, #func v,
     String.concatWith "," (map (fn (a, n) => a ^ "=" ^ Arbnum.toString n) (#args v)),
     csv (#image v), Arbnum.toString status, csv out]

(* ------------------------------------------------------------------------
   Keccak-f[1600] and the SP 800-185 encodings in SML. They only build
   inputs and expected answers; every claim below is an EVAL theorem.
   ------------------------------------------------------------------------ *)

val round_constants : Word64.word list =
  [0wx1, 0wx8082, 0wx800000000000808A, 0wx8000000080008000, 0wx808B, 0wx80000001,
   0wx8000000080008081, 0wx8000000000008009, 0wx8A, 0wx88, 0wx80008009, 0wx8000000A,
   0wx8000808B, 0wx800000000000008B, 0wx8000000000008089, 0wx8000000000008003,
   0wx8000000000008002, 0wx8000000000000080, 0wx800A, 0wx800000008000000A,
   0wx8000000080008081, 0wx8000000000008080, 0wx80000001, 0wx8000000080008008]
(* rotation of lane x + 5y *)
val rotations = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

fun rotl (v, 0) = v
  | rotl (v, n) = Word64.orb (Word64.<< (v, Word.fromInt n), Word64.>> (v, Word.fromInt (64 - n)))

fun keccak_round (rc, lanes) =
  let
    val a = Vector.fromList lanes
    fun at i = Vector.sub (a, i)
    val c = Vector.tabulate (5, fn x =>
              List.foldl Word64.xorb 0w0 (List.tabulate (5, fn y => at (x + 5 * y))))
    fun col x = Vector.sub (c, x mod 5)
    val t = Vector.tabulate (25, fn i =>
              Word64.xorb (at i, Word64.xorb (col (i + 4), rotl (col (i + 1), 1))))
    val b = Array.array (25, 0w0 : Word64.word)
    val _ = List.app (fn i =>
              let val x = i mod 5 and y = i div 5
              in Array.update (b, y + 5 * ((2 * x + 3 * y) mod 5),
                               rotl (Vector.sub (t, i), List.nth (rotations, i))) end)
              (List.tabulate (25, fn i => i))
    fun bb i = Array.sub (b, i)
    val chi = List.tabulate (25, fn i =>
                let val r = 5 * (i div 5)
                in Word64.xorb (bb i, Word64.andb (Word64.notb (bb (r + (i + 1) mod 5)),
                                                   bb (r + (i + 2) mod 5))) end)
  in Word64.xorb (hd chi, rc) :: tl chi end

fun keccak_f lanes = List.foldl keccak_round lanes round_constants

val rate = 136
fun zeros n = List.tabulate (n, fn _ => 0)
fun le_word bs = List.foldr (fn (b, w) => Word64.orb (Word64.<< (w, 0w8), Word64.fromInt b)) 0w0 bs
fun le_words [] = []
  | le_words bs = le_word (List.take (bs, 8)) :: le_words (List.drop (bs, 8))
fun word_bytes w = List.tabulate (8, fn i =>
                     Word64.toInt (Word64.andb (Word64.>> (w, Word.fromInt (8 * i)), 0wxFF)))

fun absorb (lanes, []) = lanes
  | absorb (lanes, bs) =
      let val block = le_words (List.take (bs, rate))
          val mixed = ListPair.map Word64.xorb (lanes, block @ List.tabulate (8, fn _ => 0w0))
      in absorb (keccak_f mixed, List.drop (bs, rate)) end

fun pad (bs, suffix) =
  let val n = rate - length bs mod rate
      val tail = List.tabulate (n, fn i =>
                   (if i = 0 then suffix else 0) + (if i = n - 1 then 128 else 0))
  in bs @ tail end

fun left_encode n =
  let fun digits 0 acc = acc | digits k acc = digits (k div 256) (k mod 256 :: acc)
      val ds = case digits n [] of [] => [0] | l => l
  in length ds :: ds end
fun right_encode n = let val l = left_encode n in tl l @ [hd l] end
fun encode_string s = left_encode (8 * length s) @ s
fun bytepad x =
  let val z = left_encode rate @ x in z @ zeros ((rate - length z mod rate) mod rate) end

val zero_lanes = List.tabulate (25, fn _ => 0w0 : Word64.word)
fun cshake_midstate (name, custom) =
  absorb (zero_lanes, bytepad (encode_string name @ encode_string custom))
fun kmac_midstate (key, custom) =
  absorb (cshake_midstate (map Char.ord (explode "KMAC"), custom), bytepad (encode_string key))
fun resume_lanes (lanes, msg, trailer) =
  absorb (lanes, pad (msg @ (if trailer then right_encode 256 else []), 4))

fun num w = Arbnum.fromString (LargeInt.toString (Word64.toLargeInt w))
fun nums ws = map num ws
fun ascii s = map Char.ord (explode s)
fun span n = List.tabulate (n, fn i => i mod 256)
fun hex_bytes s =
  List.tabulate (size s div 2, fn i =>
    valOf (StringCvt.scanString (Int.scan StringCvt.HEX) (String.substring (s, 2 * i, 2))))

(* ------------------------------------------------------------------------
   Memory images. Regions are laid out from address 256 in order; byte
   strings are packed little-endian and padded to whole words.
   ------------------------------------------------------------------------ *)

fun byte_region bs = nums (le_words (bs @ zeros ((8 - length bs mod 8) mod 8)))
fun layout regions =
  let fun go _ [] = ([], [])
        | go a (ws :: rest) =
            let val (addrs, image) = go (a + 8 * length ws) rest
            in (a :: addrs, ws @ image) end
  in go 256 regions end
fun n i = Arbnum.fromInt i

(* The SysV slice table: pointer and length of each byte string. *)
fun sponge_vector {kernel, func, id, state, strings, frame, extra} =
  let
    val placeholder = List.tabulate (6, fn _ => Arbnum.zero)
    val regions = [state, placeholder] @ map byte_region strings @
                  [List.tabulate ((frame + 7) div 8, fn _ => Arbnum.zero)]
    val (addrs, _) = layout regions
    val ptrs = List.take (List.drop (addrs, 2), length strings)
    val table = List.concat (ListPair.map (fn (p, s) => [n p, n (length s)]) (ptrs, strings))
    val table = table @ List.tabulate (6 - length table, fn _ => Arbnum.zero)
    val (_, image) = layout ([state, table] @ tl (tl regions))
  in
    {kernel = kernel, func = func, id = id, clock = 4096, obs = 25, image = image,
     args = [("base", n 256), ("frame", n (List.last addrs)), ("slices", n (hd (tl addrs)))]
            @ extra} : kernel_vector
  end

(* ------------------------------------------------------------------------
   The vectors.
   ------------------------------------------------------------------------ *)

val keccak_vectors =
  let fun padded tail =
        List.tabulate (25, fn i => if i = 0 then tail
                                   else if i = 16 then Arbnum.fromString "9223372036854775808"
                                   else Arbnum.zero)
      fun keccak id image = {kernel = "keccakF1600", func = "keccakF1600", id = id,
                             args = [("base", n 256)], clock = 0, image = image, obs = 25}
  in [keccak "zero" (List.tabulate (25, fn _ => Arbnum.zero)),
      keccak "empty" (padded (n 6)), keccak "abc" (padded (n 0x06636261))] end

val belt_vectors =
  let val g = [11,12,13,14] and d = [21,22,23,24]
      and p = [31,32,33,34] and x = [41,42,43,44]
      val st = [1] @ g @ [100] @ d @ p
      val rq = g @ [100,101] @ d @ x @ p @ [1]
      fun set l i v = List.take (l,i) @ [v] @ List.drop (l,i+1)
      fun belt (id, a, b) =
        {kernel = "beltLatch", func = "stepBeltLatch", id = id,
         args = [("current", n 256), ("candidate", n 368)], clock = 0,
         image = map n (a @ b), obs = 33}
  in map belt [("accept",st,rq), ("uninitialized",set st 0 2,rq),
               ("genesis",st,set rq 0 99), ("stale",st,set rq 4 99),
               ("nonincreasing",st,set rq 5 100), ("fork",st,set rq 6 99),
               ("drift",st,set rq 14 99), ("noack",st,set rq 18 0)] end

(* Obend's macaroon fixtures: tokens at 256, the workspace at 640. A tag
   link is the first four lanes of cSHAKE256 under the macaroon domain. *)
val macaroon_prefix =
  cshake_midstate ([], ascii "OBEND.PANCAKE.MACAROON/v1")
fun mac (key, msg) =
  let val block = key @ msg @ [0w4, 0w0, 0w0, 0w0, 0w0, 0w0, 0w0, 0w0,
                               0wx8000000000000000] @ List.tabulate (8, fn _ => 0w0)
  in List.take (keccak_f (ListPair.map Word64.xorb (macaroon_prefix, block)), 4) end
val root_key : Word64.word list =
  [0wx0123456789abcdef, 0wxfedcba9876543210, 0wx0f1e2d3c4b5a6978, 0wx8796a5b4c3d2e1f0]
val nonce : Word64.word list = [0w1, 0w2, 0w3, 0wxdeadbeefcafebabe]
val request : Word64.word list = [0w6, 0w42, 0w500, 0w1000]
val c1 : Word64.word list = [0w15, 0w42, 0w1000, 0w900]
val c2 : Word64.word list = [0w6, 0w42, 0w500, 0w1000]
val admitting : Word64.word list list =
  [c1, c2, [0wxffffffffffffffff, 0w42, 0wxffffffffffffffff, 0w0], [0w7, 0w42, 0w700, 0w10],
   [0w14, 0w42, 0w600, 0w999], [0wxff, 0w42, 0w501, 0w1000],
   [0w6, 0w42, 0wx8000000000000000, 0w1], [0w14, 0w42, 0wx7fffffffffffffff, 0w1000]]
val scratch = List.tabulate (25, fn i =>
                Word64.* (0wx9e3779b97f4a7c15, Word64.fromInt (i + 1)))

fun macaroon id count caveats tamper =
  let val tag = List.foldl (fn (m, k) => mac (k, m)) root_key (nonce :: caveats)
      val token = root_key @ nonce @ List.concat caveats @ tamper tag @ request
      val token = token @ List.tabulate (48 - length token, fn _ => 0wx5a5a5a5a5a5a5a5a)
  in {kernel = "macaroonVerify", func = "macaroonVerify", id = id,
      args = [("token", n 256), ("count", num count), ("state", n 640)], clock = 64,
      image = nums (token @ scratch), obs = 73} : kernel_vector end

fun flip_bit k tag =
  List.tabulate (4, fn i => if i = k div 64
                            then Word64.xorb (List.nth (tag, i), Word64.<< (0w1, Word.fromInt (k mod 64)))
                            else List.nth (tag, i))

val macaroon_vectors =
  [(macaroon "accept_none" 0w0 [] I, 0),
   (macaroon "accept_two" 0w2 [c1, c2] I, 0),
   (macaroon "forged" 0w0 [] (flip_bit 255), 2),
   (macaroon "too_early" 0w1 [[0w15, 0w42, 0w1000, 0w1001]] I, 6),
   (macaroon "overspend" 0w1 [[0w15, 0w42, 0w499, 0w0]] I, 5),
   (macaroon "malformed" 0w9 admitting I, 1)]

(* KMAC256 with L = 256 from SP 800-185 sample 4's key, customization and
   message, NIST ACVP-Server KMAC-256-1.0 tgId 4 tcId 307, and the two
   midstate resumes from the sample-4 prefix. *)
val kmac_key = List.tabulate (32, fn i => 0x40 + i)
val tagged = ascii "My Tagged Application"
val acvp = map hex_bytes [
  (* key, 512 bytes *)
   "e22e3b592d75705e115eb59d10db6876aebd4cdb419e1a7f0faf2532df869cf5ae808a80b63c3ddd" ^
   "f929ba14dc6b9b56509bdf7f50e98f6caff2966b536988cb739208ab31b8118e3c9dc4d10bc971a5" ^
   "1b789c67510f87b62cbc39c8ca7a7abefac6de4e10b6cfec02318fd7a0bb29e8ba60e6cd28839151" ^
   "e0196101a514bfcc74658d35b22c050146c4ebe36167d08ebededc8947ef2487fb907b16b716b0ee" ^
   "15f03f704ae7c797ea2dbd4c0b8de25b2f19175602d4bdb4d6d71c79c3ef2f0410f67044c3ffa7d5" ^
   "34de5e04a4fa5f170a3f06e61ac1e486350370f1bdfb75483162466aa5ec9a36003218e65af2b847" ^
   "c8d97539386066576015305e36a8084cc5b9f65c4127f17f783f478119459c6662a699c5483a0228" ^
   "be8792966c137547b3312cf7581aed629fbd743b8825dff3ac9d72abf0bb7ef1b04e762f8a903dec" ^
   "7ad0a6f9384803d4528a81c62bb37635b71d27a900ef185a2a643f5bee3fec2084a0eeff5b9610d4" ^
   "46729b0816a955f0aa656e77b1c28c69d0028f491c4947ed92976f81a3219b2694d86b8d59e85cba" ^
   "ad5ca4352d7fb8f4219221f7bca5adb100f4f17263034d4f9b9cf669b6aefbf1f94ceec9fb47e183" ^
   "0ad385f17037c28b42223c55da55079b26a07d0f03c3c8a783912e7f30efd43d49cbc86a9f73ef19" ^
   "abfa2c7f557f8227cb1fb9cf842b4fd33e24645f506d856fa192d45c7dd2bae0",
  (* customization *)
   "5176f563574225a94aba54dbf29f32bcec43b582b0c280753e40106faf18408d80901ee81bfa5d5b" ^
   "eb",
  (* message *)
   "311dbb59e25a3b0f"]
val acvp_tag = "b557ec7607c18d826f7e08cb61065d6149abf54d6fb8160a736823fc0b905451"
val small = span 4

fun kmac_oneshot id (key, custom, msg) =
  sponge_vector {kernel = "kmac256", func = "kmac256", id = id, state = map n (zeros 25),
                 strings = [key, custom, msg],
                 frame = 440 + length key + length custom + length msg, extra = []}
fun kmac_resume id (lanes, msg, trailer) =
  sponge_vector {kernel = "kmac256", func = "kmacResume", id = id, state = nums lanes,
                 strings = [[], [], msg], frame = 294 + length msg,
                 extra = [("trailer", n (if trailer then 1 else 0))]}
val cshake_kmac =
  sponge_vector {kernel = "cshake256", func = "cshake256", id = "kmac",
                 state = map n (zeros 25), strings = [ascii "KMAC", tagged, small],
                 frame = 294 + 4 + length tagged + length small, extra = []}
val cshake_sample3 =
  sponge_vector {kernel = "cshake256", func = "cshake256", id = "sample3",
                 state = map n (zeros 25), strings = [[], ascii "Email Signature", small],
                 frame = 294 + 15 + 4, extra = []}

val sponge_vectors =
  [(cshake_sample3, nums (resume_lanes (cshake_midstate ([], ascii "Email Signature"), small, false))),
   (cshake_kmac, nums (resume_lanes (cshake_midstate (ascii "KMAC", tagged), small, false))),
   (kmac_oneshot "acvp" (List.nth (acvp, 0), List.nth (acvp, 1), List.nth (acvp, 2)),
    nums (resume_lanes (kmac_midstate (List.nth (acvp, 0), List.nth (acvp, 1)), List.nth (acvp, 2), true))),
   (kmac_oneshot "tagged" (kmac_key, tagged, small),
    nums (resume_lanes (kmac_midstate (kmac_key, tagged), small, true))),
   (kmac_resume "resume" (kmac_midstate (kmac_key, tagged), small, true),
    nums (resume_lanes (kmac_midstate (kmac_key, tagged), small, true))),
   (kmac_resume "cshake_resume" (cshake_midstate (ascii "KMAC", tagged), small, false),
    nums (resume_lanes (cshake_midstate (ascii "KMAC", tagged), small, false)))]

(* The ACVP answer pins the SML reference to NIST. *)
val _ =
  let val lanes = resume_lanes (kmac_midstate (List.nth (acvp, 0), List.nth (acvp, 1)),
                                List.nth (acvp, 2), true)
      val hex = String.concat (map (fn b => StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX b))
                                   (List.concat (map word_bytes (List.take (lanes, 4)))))
  in if String.map Char.toLower hex = acvp_tag then ()
     else raise Fail ("the SML reference gives " ^ hex ^ " for ACVP tcId 307") end

(* ------------------------------------------------------------------------
   Run them. A vector whose answer differs from the expectation stops the
   build; the rows go to the native comparison.
   ------------------------------------------------------------------------ *)

fun expect_status (v : kernel_vector) code (th, status, out) =
  if status = Arbnum.fromInt code then (v, th, status, out)
  else raise Fail (#kernel v ^ " " ^ #id v ^ ": returned " ^ Arbnum.toString status ^
                   ", expected " ^ Int.toString code)

fun expect_lanes (v : kernel_vector) lanes (th, status, out) =
  if status = Arbnum.zero andalso out = lanes then (v, th, status, out)
  else raise Fail (#kernel v ^ " " ^ #id v ^ ": lanes differ from SP 800-185")

fun expect_words (v : kernel_vector) code words (th, status, out) =
  if status = Arbnum.fromInt code andalso out = words then (v, th, status, out)
  else raise Fail (#kernel v ^ " " ^ #id v ^ ": returned " ^ Arbnum.toString status ^
                   " with other memory, expected " ^ Int.toString code)

fun keccak_expected (v : kernel_vector) =
  nums (keccak_f (map (fn x => Word64.fromLargeInt (valOf (LargeInt.fromString
                                 (Arbnum.toString x)))) (#image v)))

val results =
  map (fn v => expect_words v 0 (keccak_expected v) (run_vector v)) keccak_vectors @
  ListPair.map (fn (v, code) => expect_status v code (run_vector v))
               (belt_vectors, [0, 1, 1, 2, 3, 4, 5, 6]) @
  map (fn (v, code) =>
         let val token = List.take (#image v, 48)
             val workspace = if code = 1 then List.drop (#image v, 48)
                             else List.tabulate (25, fn _ => Arbnum.zero)
         in expect_words v code (token @ workspace) (run_vector v) end)
      macaroon_vectors @
  map (fn (v, lanes) => expect_lanes v lanes (run_vector v)) sponge_vectors

fun result id =
  case List.find (fn (v : kernel_vector, _, _, _) => #kernel v ^ "_" ^ #id v = id) results of
    SOME (_, th, _, _) => th
  | NONE => raise Fail ("no vector " ^ id)

(* Both sides return 0 with the same 25 lanes, for the parsed and for the
   printed program. *)
fun parity name (a, b) =
  let val ta = SPEC s_var (result a) and tb = SPEC s_var (result b)
      fun side f = TRANS (f ta) (SYM (f tb))
  in save_thm (name, GEN s_var (CONJ (side CONJUNCT1) (side CONJUNCT2))) end

val kmac256_resume_parity = parity "kmac256_resume_parity" ("kmac256_resume", "kmac256_tagged")
val kmac256_cshake_resume_parity =
  parity "kmac256_cshake_resume_parity" ("kmac256_cshake_resume", "cshake256_kmac")

val _ = spit (OS.Path.concat (out_dir (), "eval.tsv"))
             (String.concat (map (fn (v, _, status, out) => vector_row v status out ^ "\n") results))
