#!/usr/bin/env python3
"""Check (or show) that the definition `PartitionArrow` in Challenge.lean is a verbatim copy of
the one in Erdos1219/Defs.lean.  Usage: sync_challenge.py --check"""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
def block(path):
    txt = (root / path).read_text(encoding="utf-8")
    m = re.search(r"^def PartitionArrow .*?(?=^\n(?:end|theorem|/--|--)|\Z)", txt, re.S | re.M)
    if not m:
        sys.exit(f"{path}: PartitionArrow not found")
    return m.group(0).rstrip() + "\n"
a, b = block("Erdos1219/Defs.lean"), block("Challenge.lean")
if a != b:
    print("Challenge.lean PartitionArrow differs from Erdos1219/Defs.lean:\n--- Defs\n" + a + "--- Challenge\n" + b)
    sys.exit(1)
print("Challenge.lean: PartitionArrow in sync with Erdos1219/Defs.lean")
