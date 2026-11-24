"""Compile each kernel before and after the HOL4 optimizer and compare the binaries.

usage: kernel_native.py KERNEL_DIR

KERNEL_DIR holds NAME.pnk, opt/NAME.pnk, beltLatch.c and cshake256.c. Every
vector must produce identical bytes from both builds. Known-answer vectors are
also checked against hashlib or the published cSHAKE samples.
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
    text = subprocess.run(["objdump", "-d", str(obj)], stdout=subprocess.PIPE,
                          check=True, text=True).stdout
    insns = sum(1 for line in text.splitlines()
                if re.match(r"^\s+[0-9a-f]+:\t[0-9a-f]{2} ", line) and
                len(line.split("\t")) >= 3)
    sections = subprocess.check_output(["size", "-A", str(obj)], text=True)
    text_size = next(int(row.split()[1]) for row in sections.splitlines()
                     if row.split()[:1] == [".text"])
    return insns, text_size


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


def run_keccak(old, new):
    for name, lanes in keccak_vectors().items():
        data = words(*lanes)
        a = subprocess.run([old], input=data, stdout=subprocess.PIPE, check=True).stdout
        b = subprocess.run([new], input=data, stdout=subprocess.PIPE, check=True).stdout
        if a != b or len(a) != 208 or a[:8] != words(0):
            raise ValueError(f"keccakF1600 {name}: native outputs differ")
        if name in ("empty", "abc"):
            message = b"" if name == "empty" else b"abc"
            if a[8:40] != hashlib.sha3_256(message).digest():
                raise ValueError(f"keccakF1600 {name}: SHA3-256 digest differs")
    return len(keccak_vectors())


def belt_vectors():
    rng = random.Random(0x62656c74)
    cases = []
    for _ in range(40):
        genesis = [rng.getrandbits(64) for _ in range(4)]
        digest = [rng.getrandbits(64) for _ in range(4)]
        policy = [rng.getrandbits(64) for _ in range(4)]
        epoch = rng.getrandbits(63)
        state = [1, *genesis, epoch, *digest, *policy]
        next_digest = [rng.getrandbits(64) for _ in range(4)]
        request = [*genesis, epoch, epoch + 1, *digest, *next_digest, *policy, 1]
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


def run_belt(old, new, scratch):
    record = scratch / "belt.record"
    seen = set()
    cases = belt_vectors()
    for state, request in cases:
        record.write_bytes(words(*state, *request))
        a = subprocess.run([old, record], stdout=subprocess.PIPE, check=True).stdout
        b = subprocess.run([new, record], stdout=subprocess.PIPE, check=True).stdout
        if a != b or len(a) != 272:
            raise ValueError("beltLatch: native outputs differ")
        seen.add(struct.unpack("<Q", a[:8])[0])
    if seen != set(range(7)):
        raise ValueError(f"beltLatch: vectors reached only statuses {sorted(seen)}")
    return len(cases)


def run_cshake(old, new, scratch):
    span = lambda n: bytes(i & 255 for i in range(n))
    email = b"Email Signature"
    domains = [(b"", b""), (b"", email), (b"KMAC", b""), (span(32), span(130)),
               (span(128), b""), (b"", span(129))]
    sizes = [0, 1, 3, 4, 135, 136, 137, 200, 271, 272, 273, 409]
    paths = [scratch / "name", scratch / "custom", scratch / "message"]
    count = 0
    for name, custom in domains:
        for n in sizes:
            message = b"abc" if n == 3 else span(n)
            for path, data in zip(paths, (name, custom, message)):
                path.write_bytes(data)
            a = subprocess.run([old, *paths], stdout=subprocess.PIPE, check=True).stdout
            b = subprocess.run([new, *paths], stdout=subprocess.PIPE, check=True).stdout
            if a != b or len(a) != 32:
                raise ValueError(f"cshake256 |N|={len(name)} |S|={len(custom)} |X|={n}: outputs differ")
            if not name and not custom and a != hashlib.shake_256(message).digest(32):
                raise ValueError(f"cshake256 |X|={n}: differs from SHAKE256")
            count += 1
    # NIST SP 800-185 cSHAKE256 samples 3 and 4, first 256 bits.
    samples = [(span(4), "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1"),
               (span(200), "07dc27b11e51fbac75bc7b3c1d983e8b4b85fb1defaf218912ac864302730917")]
    for message, expected in samples:
        for path, data in zip(paths, (b"", email, message)):
            path.write_bytes(data)
        for binary in (old, new):
            out = subprocess.run([binary, *paths], stdout=subprocess.PIPE, check=True).stdout
            if out.hex() != expected:
                raise ValueError("cshake256: NIST sample differs")
    return count


def check_eval(root, name, binaries, scratch):
    """HOL4 EVAL, the original binary and the optimized binary agree."""
    expected_cases = {
        "keccakF1600": {"zero", "empty", "abc"},
        "beltLatch": {"accept", "uninitialized", "genesis", "stale", "nonincreasing",
                      "fork", "drift", "noack"},
        "cshake256": {"sample3"},
    }[name]
    seen = set()
    for line in (root / "opt" / "eval.tsv").read_text().splitlines():
        kernel, case, before, status, after = line.split("\t")
        if kernel != name:
            continue
        if case in seen or case not in expected_cases:
            raise ValueError(f"{name}: unexpected or duplicate EVAL vector {case}")
        seen.add(case)
        inputs = list(map(int, before.split(",")))
        outputs = list(map(int, after.split(",")))
        expected = words(int(status), *outputs)
        stdin, args = None, []
        if name == "keccakF1600":
            stdin = words(*inputs)
        elif name == "beltLatch":
            record = scratch / "eval.record"
            record.write_bytes(words(*inputs))
            args = [record]
        else:
            # The Obend driver exits nonzero if the Pancake return status is
            # nonzero and writes the first 32 bytes of the state on success.
            if int(status) != 0 or len(outputs) != 4 or inputs != [0, 1, 2, 3]:
                raise ValueError("cshake256: invalid EVAL result for SP 800-185 sample 3")
            args = [scratch / key for key in ("name", "custom", "message")]
            for path, content in zip(args, (b"", b"Email Signature", bytes(inputs))):
                path.write_bytes(content)
            expected = words(*outputs)
        for binary in binaries:
            if subprocess.check_output([binary, *args], input=stdin) != expected:
                raise ValueError(f"{name} {case}: native output differs from HOL4 EVAL")
    if seen != expected_cases:
        raise ValueError(f"{name}: missing EVAL vectors {sorted(expected_cases - seen)}")
    return len(seen)


def main(root):
    drivers = {"keccakF1600": HERE / "keccak_driver.c",
               "beltLatch": root / "beltLatch.c",
               "cshake256": root / "cshake256.c"}
    selected = os.environ.get("PANCAKE_KERNEL_NAMES", " ".join(drivers)).split()
    if not selected:
        raise ValueError("select at least one kernel")
    nodes = {row[0]: (int(row[1]), int(row[2])) for row in
             (line.split("\t") for line in (root / "opt" / "stats.tsv").read_text().splitlines())}
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        for name in selected:
            if nodes[name][1] >= nodes[name][0]:
                raise ValueError(f"{name}: no AST node reduction")
            driver = drivers[name]
            old = build(root / f"{name}.pnk", driver, scratch / f"{name}_old")
            new = build(root / "opt" / f"{name}.pnk", driver, scratch / f"{name}_new")
            if name == "keccakF1600":
                count = run_keccak(old, new)
            elif name == "beltLatch":
                count = run_belt(old, new, scratch)
            else:
                count = run_cshake(old, new, scratch)
            agreed = check_eval(root, name, (old, new), scratch)
            i0, b0 = code_stats(old.with_suffix(".o"))
            i1, b1 = code_stats(new.with_suffix(".o"))
            same = old.with_suffix(".S").read_bytes() == new.with_suffix(".S").read_bytes()
            print(f"{name}: {count} vectors byte-identical, {agreed} also equal to HOL4 EVAL; "
                  f"AST nodes {nodes[name][0]} -> {nodes[name][1]}, "
                  f"instructions {i0} -> {i1}, .text bytes {b0} -> {b1}, "
                  f"assembly {'byte-identical' if same else 'differs'}")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
