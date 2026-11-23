"""Compile the emitted Pancake file, then compare native output with PanSem."""
import csv
import hashlib
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile


def word_bytes(field):
    return struct.pack("<25Q", *(int(w) for w in field.split(",")))


def main(corpus, basis):
    source = (corpus / "keccakF1600.pnk").read_bytes()
    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        with (tmp / "kernel.S").open("wb") as asm:
            subprocess.run([os.environ.get("CAKE", "cake"), "--pancake"],
                           input=source + b"""
fun main() {
  var p = @base;
  @input(p, 0, p, 200);
  var 1 result = keccakF1600(p);
  st (p + 200), result;
  @output(p + 200, 8, p, 200);
  return result;
}
""", stdout=asm, check=True)
        binary = tmp / "kernel"
        subprocess.run([os.environ.get("CC", "cc"), "-O2", str(tmp / "kernel.S"),
                        str(basis), str(Path(__file__).with_name("buffer_ffi.c")),
                        "-lm", "-o", str(binary)], check=True)
        cases = set()
        for name, fn, _, _, before, ret, _, after in csv.reader(
                (corpus / "cases.tsv").read_text().splitlines(), delimiter="\t"):
            if fn != "keccakF1600":
                continue
            actual = subprocess.run([binary], input=word_bytes(before),
                                    stdout=subprocess.PIPE, check=True).stdout
            if ret != "0" or actual != word_bytes(after):
                raise ValueError(f"{name}: native return or 200-byte state differs")
            if name in ("abc", "empty"):
                msg = b"abc" if name == "abc" else b""
                if actual[:32] != hashlib.sha3_256(msg).digest():
                    raise ValueError(f"{name}: SHA3-256 digest differs")
            cases.add(name)
            print(f"{name}: all 25 native lanes agree")
        if cases != {"zero", "empty", "abc"}:
            raise ValueError("missing Keccak test cases")


if __name__ == "__main__":
    main(*(Path(arg) for arg in sys.argv[1:]))
