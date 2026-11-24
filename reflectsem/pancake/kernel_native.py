"""Compile each kernel before and after the HOL4 optimizer and compare the binaries.

usage: kernel_native.py KERNEL_DIR

KERNEL_DIR holds NAME.pnk and Obend's C driver for each kernel, and opt/ with
the optimized sources, the node counts (NAME.stats) and the HOL4 evaluation
rows (eval.tsv). Every vector must produce identical bytes from both builds,
and those bytes must match an independent model: hashlib, the SP 800-185
reference below (checked against NIST's published answers first), or the
belt-latch or macaroon specification. Each HOL4 vector must also give its
EVAL result natively.
"""
import hashlib
import os
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
CAKE = os.environ.get("CAKE", "cake")
CC = os.environ.get("CC", "cc")
WORD = (1 << 64) - 1
KERNELS = ["keccakF1600", "beltLatch", "cshake256", "macaroonVerify", "kmac256"]


def words(*values):
    return struct.pack(f"<{len(values)}Q", *values)


def build(source, driver, stem):
    asm = stem.with_suffix(".S")
    with asm.open("wb") as out:
        subprocess.run([CAKE, "--pancake", "--main_return=true"],
                       input=source.read_bytes(), stdout=out, check=True)
    subprocess.run([CC, "-c", str(asm), "-o", str(stem.with_suffix(".o"))], check=True)
    binary = stem.with_suffix(".bin")
    subprocess.run([CC, "-O2", "-static", "-Wl,-z,noexecstack", str(driver), str(asm),
                    "-o", str(binary)], check=True)
    return binary


def code_stats(obj):
    """Machine instructions and bytes in the object's code."""
    text = subprocess.check_output(["objdump", "-d", "--no-show-raw-insn", str(obj)],
                                   text=True)
    insns = sum(1 for line in text.splitlines() if re.match(r"^\s*[0-9a-f]+:\s+\S", line))
    sections = subprocess.check_output(["size", "-A", str(obj)], text=True)
    text_size = next(int(row.split()[1]) for row in sections.splitlines()
                     if row.split()[:1] == [".text"])
    return insns, text_size


def run(binary, *args, stdin=None):
    """Exit status and standard output."""
    done = subprocess.run([binary, *args], input=stdin, stdout=subprocess.PIPE)
    return done.returncode, done.stdout


def both(old, new, *args, stdin=None):
    """The output both builds agree on, or an error."""
    a = run(old, *args, stdin=stdin)
    if a != run(new, *args, stdin=stdin):
        raise ValueError("native outputs differ")
    return a


# ---------------------------------------------------------------------------
# FIPS 202 Keccak-f[1600] and SP 800-185, written from the standards.

ROUND_CONSTANTS = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
# rotation of lane x + 5y
ROTATIONS = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
             41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
RATE = 136
ZERO = [0] * 25


def rotl(v, n):
    return ((v << n) | (v >> (64 - n))) & WORD if n else v


def keccak_f(lanes):
    a = list(lanes)
    for rc in ROUND_CONSTANTS:
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        a = [a[i] ^ c[(i + 4) % 5] ^ rotl(c[(i + 1) % 5], 1) for i in range(25)]
        b = [0] * 25
        for i in range(25):
            x, y = i % 5, i // 5
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(a[i], ROTATIONS[i])
        a = [b[i] ^ (~b[5 * (i // 5) + (i + 1) % 5] & b[5 * (i // 5) + (i + 2) % 5])
             for i in range(25)]
        a[0] ^= rc
    return a


def absorb(lanes, data):
    for k in range(0, len(data), RATE):
        block = struct.unpack("<17Q", data[k:k + RATE])
        lanes = keccak_f([lane ^ block[i] if i < 17 else lane for i, lane in enumerate(lanes)])
    return lanes


def pad(data, suffix):
    tail = bytearray(RATE - len(data) % RATE)
    tail[0] = suffix
    tail[-1] |= 0x80
    return data + bytes(tail)


def squeeze(lanes, n):
    out = b""
    while len(out) < n:
        if out:
            lanes = keccak_f(lanes)
        out += struct.pack("<17Q", *lanes[:17])
    return out[:n]


def left_encode(x):
    n = max(1, (x.bit_length() + 7) // 8)
    return bytes([n]) + x.to_bytes(n, "big")


def right_encode(x):
    n = max(1, (x.bit_length() + 7) // 8)
    return x.to_bytes(n, "big") + bytes([n])


def encode_string(s):
    return left_encode(8 * len(s)) + s


def bytepad(x):
    z = left_encode(RATE) + x
    return z + bytes(-len(z) % RATE)


def cshake_midstate(name, custom):
    return absorb(ZERO, bytepad(encode_string(name) + encode_string(custom)))


def kmac_midstate(key, custom):
    return absorb(cshake_midstate(b"KMAC", custom), bytepad(encode_string(key)))


def resume(lanes, message, trailer):
    """The 25 lanes kmacResume leaves after absorbing message and its trailer."""
    return absorb(lanes, pad(message + (right_encode(256) if trailer else b""), 0x04))


def cshake256(name, custom, message):
    if not name and not custom:
        return absorb(ZERO, pad(message, 0x1F))
    return resume(cshake_midstate(name, custom), message, False)


def kmac256(key, custom, message):
    return resume(kmac_midstate(key, custom), message, True)


def digest(lanes):
    return words(*lanes[:4])


def span(n):
    return bytes(i & 255 for i in range(n))


TAGGED = b"My Tagged Application"
KMAC_KEY = bytes(range(0x40, 0x60))
# SP 800-185 KMAC256 sample 4 uses a four-byte message and L = 512.
SAMPLE4 = ("20c570c31346f703c9ac36c61c03cb64c3970d0cfc787e9b79599d273a68d2f7"
           "f69d4cc3de9d104a351689f27cf6f5951f0103f33f4f24871024d9c27773a8dd")
# NIST ACVP-Server KMAC-256-1.0 internalProjection.json, tgId 4, tcId 307 (L = 256).
ACVP_TAG = "b557ec7607c18d826f7e08cb61065d6149abf54d6fb8160a736823fc0b905451"


def check_reference():
    for n in (0, 3, 135, 136, 137, 300):
        m = span(n)
        if digest(cshake256(b"", b"", m)) != hashlib.shake_256(m).digest(32) or \
           squeeze(absorb(ZERO, pad(m, 0x06)), 32) != hashlib.sha3_256(m).digest():
            raise ValueError("the Keccak reference differs from hashlib")
    email = b"Email Signature"
    for n, expected in ((4, "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1"),
                        (200, "07dc27b11e51fbac75bc7b3c1d983e8b4b85fb1defaf218912ac864302730917")):
        if digest(cshake256(b"", email, span(n))).hex() != expected:
            raise ValueError("the cSHAKE256 reference differs from SP 800-185")
    tail = span(4) + right_encode(512)
    if squeeze(absorb(kmac_midstate(KMAC_KEY, TAGGED), pad(tail, 0x04)), 64).hex() != SAMPLE4:
        raise ValueError("the KMAC256 reference differs from SP 800-185 sample 4")


# ---------------------------------------------------------------------------
# keccakF1600, beltLatch and cshake256

def keccak_vectors():
    def padded(tail):
        lanes = [0] * 25
        lanes[0] = tail
        lanes[16] = 1 << 63
        return lanes

    rng = random.Random(0x4b656363)
    named = {"zero": [0] * 25, "empty": padded(6), "abc": padded(0x06636261)}
    for i in range(61):
        named[f"random{i}"] = [rng.getrandbits(64) for _ in range(25)]
    return named


def run_keccak(old, new, scratch):
    for name, lanes in keccak_vectors().items():
        rc, out = both(old, new, stdin=words(*lanes))
        if rc or out != words(0, *keccak_f(lanes)):
            raise ValueError(f"keccakF1600 {name}: differs from Keccak-f[1600]")
        if name in ("empty", "abc") and \
           out[8:40] != hashlib.sha3_256(b"" if name == "empty" else b"abc").digest():
            raise ValueError(f"keccakF1600 {name}: SHA3-256 digest differs")
    return len(keccak_vectors())


def belt_vectors():
    rng = random.Random(0x62656c74)
    cases = []
    for _ in range(40):
        genesis = [rng.getrandbits(64) for _ in range(4)]
        digest_ = [rng.getrandbits(64) for _ in range(4)]
        policy = [rng.getrandbits(64) for _ in range(4)]
        epoch = rng.getrandbits(63)
        state = [1, *genesis, epoch, *digest_, *policy]
        next_digest = [rng.getrandbits(64) for _ in range(4)]
        request = [*genesis, epoch, epoch + 1, *digest_, *next_digest, *policy, 1]
        cases.append((state, request))
        for i in range(14):
            bad = list(state)
            bad[i] = (bad[i] ^ (1 << rng.randrange(64))) & WORD
            cases.append((bad, request))
        for i in range(19):
            bad = list(request)
            bad[i] = (bad[i] ^ (1 << rng.randrange(64))) & WORD
            cases.append((state, bad))
        stale = list(request)
        stale[5] = epoch
        cases.append((state, stale))
    return cases


def belt_expected(state, request):
    """Obend's stepBeltLatch verdict and caller-owned buffers, in ABI order."""
    if state[0] != 1 or state[1:5] != request[:4]:
        code = 1
    elif state[5] != request[4]:
        code = 2
    elif state[5] >= request[5]:
        code = 3
    elif state[6:10] != request[6:10]:
        code = 4
    elif state[10:14] != request[14:18]:
        code = 5
    elif request[18] != 1:
        code = 6
    else:
        code = 0
        state = [*state[:5], request[5], *request[10:14], *state[10:]]
    return words(code, *state, *request)


def run_belt(old, new, scratch):
    record = scratch / "belt.record"
    seen = set()
    cases = belt_vectors()
    for state, request in cases:
        record.write_bytes(words(*state, *request))
        rc, out = both(old, new, record)
        if rc or out != belt_expected(state, request):
            raise ValueError("beltLatch: native verdict or buffers differ from stepBeltLatch")
        seen.add(struct.unpack("<Q", out[:8])[0])
    if seen != set(range(7)):
        raise ValueError(f"beltLatch: vectors reached only statuses {sorted(seen)}")
    return len(cases)


def write_files(scratch, **contents):
    paths = []
    for name, data in contents.items():
        path = scratch / name
        path.write_bytes(data)
        paths.append(path)
    return paths


def run_cshake(old, new, scratch):
    email = b"Email Signature"
    domains = [(b"", b""), (b"", email), (b"KMAC", b""), (span(32), span(130)),
               (span(128), b""), (b"", span(129))]
    sizes = [0, 1, 3, 4, 135, 136, 137, 200, 271, 272, 273, 409]
    count = 0
    for name, custom in domains:
        for n in sizes:
            message = b"abc" if n == 3 else span(n)
            paths = write_files(scratch, name=name, custom=custom, message=message)
            rc, out = both(old, new, *paths)
            if rc or out != digest(cshake256(name, custom, message)):
                raise ValueError(f"cshake256 |N|={len(name)} |S|={len(custom)} |X|={n}: "
                                 "differs from SP 800-185")
            count += 1
    return count


# ---------------------------------------------------------------------------
# macaroonVerify, after Obend's tests/metasystem/PancakeMacaroonVerifierTest.lean

DOMAIN = b"OBEND.PANCAKE.MACAROON/v1"
ACCEPTED, MALFORMED, FORGED, OP_DENIED, WRONG_SEAT, OVER_SPEND, TOO_EARLY = range(7)
TOKEN_WORDS = 48
SCRATCH = [(0x9e3779b97f4a7c15 * (i + 1)) & WORD for i in range(25)]


def mac(key, msg):
    """One link: cSHAKE256 under the domain of the key words then the message words."""
    return list(cshake256(b"", DOMAIN, words(*key, *msg))[:4])


def tag(root, nonce, caveats):
    t = mac(root, nonce)
    for c in caveats:
        t = mac(t, c)
    return t


def verdict(c, request):
    op, seat, spend, epoch = request
    if c[0] & op != op:
        return OP_DENIED
    if c[1] != seat:
        return WRONG_SEAT
    if spend > c[2]:
        return OVER_SPEND
    if c[3] > epoch:
        return TOO_EARLY
    return ACCEPTED


def verify(root, nonce, caveats, claimed, request, count):
    """Obend's verifyMacaroon, for a token whose caveat count is `count`."""
    if count > 8:
        return MALFORMED
    if tag(root, nonce, caveats) != claimed:
        return FORGED
    for c in caveats:
        if verdict(c, request) != ACCEPTED:
            return verdict(c, request)
    return ACCEPTED


ROOT = [0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x8796a5b4c3d2e1f0]
NONCE = [1, 2, 3, 0xdeadbeefcafebabe]
REQUEST = [0b0110, 42, 500, 1000]
C1 = [0b1111, 42, 1000, 900]
C2 = [0b0110, 42, 500, 1000]
ADMITTING = [C1, C2, [WORD, 42, WORD, 0], [0b0111, 42, 700, 10], [0b1110, 42, 600, 999],
             [0xff, 42, 501, 1000], [0b0110, 42, 1 << 63, 1], [0b1110, 42, (1 << 63) - 1, 1000]]


def mint(caveats, root=ROOT, nonce=NONCE):
    return {"root": root, "nonce": nonce, "caveats": [list(c) for c in caveats],
            "claimed": tag(root, nonce, caveats)}


def changed(token, **fields):
    return {**token, **fields}


def flip_claimed(token, limb):
    d = list(token["claimed"])
    d[limb] ^= [1, 0x100, 1 << 63, 0x10000][limb]
    return changed(token, claimed=d)


def attenuate(token, caveat):
    return changed(token, caveats=token["caveats"] + [caveat],
                   claimed=mac(token["claimed"], caveat))


def macaroon_vectors():
    two = mint([C1, C2])
    refusing = lambda c: mint([c])
    v = [("no caveats", mint([]), REQUEST, None),
         ("one caveat", mint([C1]), REQUEST, None),
         ("spend and epoch on their bounds", mint([C2]), REQUEST, None),
         ("three caveats", mint(ADMITTING[:3]), REQUEST, None),
         ("eight caveats", mint(ADMITTING), REQUEST, None),
         ("nine caveats", mint(ADMITTING), REQUEST, 9),
         ("count 2^64-1", mint(ADMITTING), REQUEST, WORD),
         ("flipped bit in a caveat mask",
          changed(two, caveats=[[C1[0] ^ 1, *C1[1:]], C2]), REQUEST, None),
         ("flipped top byte of the last epoch floor",
          changed(two, caveats=[C1, [*C2[:3], C2[3] ^ 0xff00000000000000]]), REQUEST, None),
         ("flipped nonce", changed(two, nonce=[*NONCE[:3], NONCE[3] ^ 1]), REQUEST, None),
         ("other root key", changed(two, root=[0, *ROOT[1:]]), REQUEST, None),
         *[(f"claimed limb {i}", flip_claimed(two, i), REQUEST, None) for i in range(4)],
         ("last caveat removed", changed(two, caveats=[C1]), REQUEST, None),
         ("operation outside the mask", refusing([0b0100, 42, 1000, 0]), REQUEST, None),
         ("other seat", refusing([0b1111, 41, 1000, 0]), REQUEST, None),
         ("spend one over", refusing([0b1111, 42, 499, 0]), REQUEST, None),
         ("epoch one under", refusing([0b1111, 42, 1000, 1001]), REQUEST, None),
         ("first refusal decides", mint([[0b1111, 41, 1000, 0], [0, 42, 0, 9999]]), REQUEST, None),
         ("later caveat refuses", mint([C1, [0b1111, 42, 100, 0]]), REQUEST, None),
         ("forgery outranks refusal", flip_claimed(refusing([0b1111, 41, 1000, 0]), 3),
          REQUEST, None),
         ("unsigned spend", refusing([0b1111, 42, 1, 0]), [*REQUEST[:2], 1 << 63, REQUEST[3]], None),
         ("unsigned epoch", refusing([0b1111, 42, 1000, 1 << 63]), [*REQUEST[:3], 1], None),
         ("attenuated by the holder", attenuate(mint([C1]), C2), REQUEST, None),
         ("attenuation narrows", attenuate(mint([C1]), [0b1111, 42, 100, 0]), REQUEST, None)]
    # Every bit of the claimed tag, on the two-caveat token.
    for bit in range(256):
        d = list(two["claimed"])
        d[bit // 64] ^= 1 << (bit % 64)
        v.append((f"claimed bit {bit}", changed(two, claimed=d), REQUEST, None))
    # Random tokens of every length that admit a random request, and the same
    # tokens with one random bit of an authenticated word flipped.
    rng = random.Random(0x6d616361)
    for n in range(9):
        for k in range(4):
            request = [rng.getrandbits(64) for _ in range(4)]
            caveats = [[request[0] | rng.getrandbits(64), request[1],
                        rng.randrange(request[2], 1 << 64), rng.randrange(0, request[3] + 1)]
                       for _ in range(n)]
            token = mint(caveats, [rng.getrandbits(64) for _ in range(4)],
                         [rng.getrandbits(64) for _ in range(4)])
            v.append((f"random {n} caveats #{k}", token, request, None))
            flat = token["root"] + token["nonce"] + sum(token["caveats"], []) + token["claimed"]
            i = rng.randrange(len(flat))
            flat[i] ^= 1 << rng.randrange(64)
            tampered = {"root": flat[0:4], "nonce": flat[4:8],
                        "caveats": [flat[8 + 4 * j:12 + 4 * j] for j in range(n)],
                        "claimed": flat[8 + 4 * n:12 + 4 * n]}
            v.append((f"random {n} caveats #{k}, word {i} flipped", tampered, request, None))
    return v


def token_image(token, request):
    ws = token["root"] + token["nonce"] + sum(token["caveats"], []) + token["claimed"] + request
    return ws + [0x5a5a5a5a5a5a5a5a] * (TOKEN_WORDS - len(ws))


def macaroon_expected(token, request, count):
    status = verify(token["root"], token["nonce"], token["caveats"], token["claimed"],
                    request, count)
    workspace = SCRATCH if count > 8 else [0] * 25
    return words(status, *token_image(token, request), *workspace)


def run_macaroon(old, new, scratch):
    record = scratch / "macaroon.record"
    seen = set()
    vectors = macaroon_vectors()
    for name, token, request, count in vectors:
        count = len(token["caveats"]) if count is None else count
        record.write_bytes(words(count, *SCRATCH, *token_image(token, request)))
        rc, out = both(old, new, record)
        if rc or out != macaroon_expected(token, request, count):
            raise ValueError(f"macaroonVerify {name}: differs from the specification")
        seen.add(out[0])
    if seen != set(range(7)):
        raise ValueError(f"macaroonVerify: vectors reached only statuses {sorted(seen)}")
    return len(vectors)


# ---------------------------------------------------------------------------
# kmac256: kmac256 one-shot, and kmacResume with the KMAC and cSHAKE trailers,
# on Obend's grid from tests/metasystem/PancakeKmac256Test.lean.

def kmac_vectors():
    customs = [b"", b"OBEND.KMAC/v1", span(140)]
    grid = [(span(k), s, b"abc" if n == 3 else span(n))
            for k in (0, 32, 128, 136, 200) for s in customs
            for n in (0, 3, 133, 134, 136, 409)]
    return grid + [(KMAC_KEY, TAGGED, span(4)),
                   (KMAC_KEY, b"DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1", b"abc"),
                   (span(32), b"", span(132)), (span(32), b"", span(135))]


def run_kmac(old, new, scratch):
    count = 0
    for key, custom, message in kmac_vectors():
        label = f"|K|={len(key)} |S|={len(custom)} |X|={len(message)}"
        paths = write_files(scratch, key=key, custom=custom, message=message)
        expected = digest(kmac256(key, custom, message))
        if both(old, new, *paths) != (0, expected):
            raise ValueError(f"kmac256 {label}: one-shot differs from SP 800-185")
        for trailer, lanes, answer in (
                ("1", kmac_midstate(key, custom), expected),
                ("0", cshake_midstate(b"KMAC", custom), digest(cshake256(b"KMAC", custom, message)))):
            state = write_files(scratch, state=words(*lanes))[0]
            if both(old, new, "--resume", state, trailer, paths[2]) != (0, answer):
                raise ValueError(f"kmac256 {label}: resume with trailer {trailer} differs")
        count += 3
    return count


# ---------------------------------------------------------------------------
# The HOL4 evaluation rows

EVAL_CASES = {
    "keccakF1600": {"zero", "empty", "abc"},
    "beltLatch": {"accept", "uninitialized", "genesis", "stale", "nonincreasing",
                  "fork", "drift", "noack"},
    "cshake256": {"sample3", "kmac"},
    "macaroonVerify": {"accept_none", "accept_two", "forged", "too_early", "overspend",
                       "malformed"},
    "kmac256": {"acvp", "tagged", "resume", "cshake_resume"},
}


def eval_rows(root):
    rows = {}
    for line in (root / "opt" / "eval.tsv").read_text().splitlines():
        kernel, case, func, args, image, status, out = line.split("\t")
        if (kernel, case) in rows:
            raise ValueError(f"duplicate EVAL vector {kernel} {case}")
        rows[kernel, case] = {
            "func": func,
            "args": {k: int(v) for k, v in (a.split("=") for a in args.split(","))},
            "image": [int(x) for x in image.split(",")],
            "status": int(status), "out": [int(x) for x in out.split(",")]}
    return rows


def slices(row):
    """The three byte strings named by the slice table in a sponge vector's memory."""
    memory = words(*row["image"])
    table = (row["args"]["slices"] - 256) // 8
    pairs = row["image"][table:table + 6]
    return [memory[p - 256:p - 256 + n] for p, n in zip(pairs[0::2], pairs[1::2])]


def check_eval(rows, name, binaries, scratch):
    """HOL4 EVAL, the original binary and the optimized binary agree."""
    cases = {case: row for (kernel, case), row in rows.items() if kernel == name}
    if set(cases) != EVAL_CASES[name]:
        raise ValueError(f"{name}: EVAL vectors {sorted(cases)}, expected {sorted(EVAL_CASES[name])}")
    for case, row in cases.items():
        image, status, out = row["image"], row["status"], row["out"]
        stdin, args = None, []
        if name == "keccakF1600":
            if status or out != keccak_f(image[:25]):
                raise ValueError(f"keccakF1600 {case}: EVAL differs from Keccak-f[1600]")
            stdin, expected = words(*image), (0, words(status, *out))
        elif name == "beltLatch":
            args, expected = write_files(scratch, record=words(*image)), (0, words(status, *out))
        elif name == "macaroonVerify":
            record = words(row["args"]["count"], *image[48:73], *image[:48])
            args, expected = write_files(scratch, record=record), (0, words(status, *out))
        elif row["func"] == "kmacResume":
            message = slices(row)[2]
            state = write_files(scratch, state=words(*image[:25]))[0]
            args = ["--resume", state, str(row["args"]["trailer"]), *write_files(scratch, message=message)]
            lanes = resume(image[:25], message, row["args"]["trailer"])
            expected = (0, digest(out))
        else:
            first, custom, message = slices(row)
            args = write_files(scratch, first=first, custom=custom, message=message)
            lanes = kmac256(first, custom, message) if name == "kmac256" \
                else cshake256(first, custom, message)
            expected = (0, digest(out))
        if name in ("cshake256", "kmac256") and (status or out != lanes):
            raise ValueError(f"{name} {case}: EVAL differs from SP 800-185")
        for binary in binaries:
            if run(binary, *args, stdin=stdin) != expected:
                raise ValueError(f"{name} {case}: native output differs from HOL4 EVAL")
    return cases


def check_anchors(rows):
    """Published answers, and the two midstate resumes against their one-shots."""
    out = lambda kernel, case: rows[kernel, case]["out"]
    anchors = [("cshake256", "sample3", "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1"),
               ("kmac256", "acvp", ACVP_TAG),
               # PyCryptodome, as recorded in Obend's test
               ("kmac256", "tagged", "f2d95c33c9a201eb10c524b9084b4bacae0092f869122df7d7870b92c842e05b")]
    for kernel, case, answer in anchors:
        if digest(out(kernel, case)).hex() != answer:
            raise ValueError(f"{kernel} {case}: EVAL digest differs from the published answer")
    if out("kmac256", "resume") != out("kmac256", "tagged") or \
       out("kmac256", "cshake_resume") != out("cshake256", "kmac"):
        raise ValueError("a resumed EVAL differs from its one-shot")


def main(root):
    check_reference()
    drivers = {"keccakF1600": HERE / "keccak_driver.c",
               "beltLatch": root / "beltLatch.c",
               "cshake256": root / "cshake256.c",
               "macaroonVerify": root / "macaroonVerify.c",
               "kmac256": root / "kmac256.c"}
    runners = {"keccakF1600": run_keccak, "beltLatch": run_belt, "cshake256": run_cshake,
               "macaroonVerify": run_macaroon, "kmac256": run_kmac}
    selected = os.environ.get("PANCAKE_KERNEL_NAMES", " ".join(KERNELS)).split()
    if not selected or not set(selected) <= set(KERNELS):
        raise ValueError(f"select kernels from {KERNELS}")
    rows = eval_rows(root)
    check_anchors(rows)
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        for name in selected:
            _, n0, n1, b0, b1 = (root / "opt" / f"{name}.stats").read_text().split()
            if int(n1) >= int(n0):
                raise ValueError(f"{name}: no AST node reduction")
            old = build(root / f"{name}.pnk", drivers[name], scratch / f"{name}_old")
            new = build(root / "opt" / f"{name}.pnk", drivers[name], scratch / f"{name}_new")
            count = runners[name](old, new, scratch)
            agreed = check_eval(rows, name, (old, new), scratch)
            i0, t0 = code_stats(old.with_suffix(".o"))
            i1, t1 = code_stats(new.with_suffix(".o"))
            same = old.with_suffix(".S").read_bytes() == new.with_suffix(".S").read_bytes()
            print(f"{name}: {count} vectors byte-identical, {len(agreed)} also equal to HOL4 EVAL; "
                  f"AST nodes {n0} -> {n1}, source bytes {b0} -> {b1}, "
                  f"instructions {i0} -> {i1}, .text bytes {t0} -> {t1}, "
                  f"assembly {'byte-identical' if same else 'differs'}")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
