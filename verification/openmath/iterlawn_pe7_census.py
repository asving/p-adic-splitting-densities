#!/usr/bin/env python3
"""ITERLAWN-PE7 independent machine-census re-run.

Own reimplementation from the r6 bracket's stated pattern list (8 widened
patterns, case-insensitive) over the pinned 0672082 text. Compares raw hit
count, distinct-line count, per-pattern counts, and the line->disposition
map against PE6 Appendix A.
"""
import re
import sys
from collections import Counter

PATH = sys.argv[1] if len(sys.argv) > 1 else "/tmp/pe7/pinned_0672082.md"

# The 8 patterns exactly as stated in PE6 section 3 / the r6 bracket.
PATTERNS = [
    ("only", re.compile(r"\bonly\b", re.IGNORECASE)),
    ("alone", re.compile(r"\balone\b", re.IGNORECASE)),
    ("not_affected", re.compile(r"not\s+affected", re.IGNORECASE)),
    ("self_contained", re.compile(r"self-contained", re.IGNORECASE)),
    ("free", re.compile(r"free", re.IGNORECASE)),          # substring
    ("independen", re.compile(r"independen", re.IGNORECASE)),  # substring
    ("consum", re.compile(r"consum", re.IGNORECASE)),       # substring
    ("never", re.compile(r"\bnever\b", re.IGNORECASE)),
]

lines = open(PATH, encoding="utf-8").read().split("\n")
# file ends with trailing newline -> last split element empty; keep 1-index map
per_pattern = Counter()
hit_lines = {}  # lineno -> list of pattern names (one entry per raw hit)
total = 0
for i, line in enumerate(lines, start=1):
    for name, rx in PATTERNS:
        n = len(rx.findall(line))
        if n:
            per_pattern[name] += n
            total += n
            hit_lines.setdefault(i, []).extend([name] * n)

print(f"TOTAL RAW HITS: {total}")
print(f"DISTINCT LINES: {len(hit_lines)}")
print("PER-PATTERN:", dict(sorted(per_pattern.items(), key=lambda kv: -kv[1])))

# ---- PE6 Appendix A map, transcribed verbatim ----
def rng(a, b):
    return list(range(a, b + 1))

APPENDIX_A = {
    "R1": [139], "R2": [69, 308, 313, 316], "R3": [54, 58, 59, 64],
    "R4": [248], "R5": [219, 944, 947, 954], "R6": [274], "R7": [345],
    "R8": [420], "R9": [244, 422, 444, 445, 1198, 1358], "R10": [458],
    "R11": [518, 520, 529, 531],
    "R12": [567, 569, 572, 573, 575, 581, 583, 586],
    "R14": [607, 608, 616], "R15": [710, 711], "R16": [774, 775],
    "R17": [952], "R19": [1200],
    "R20": [1212, 1216, 1218, 1223, 1226, 1229, 1230, 1234, 1235, 1237, 1240, 1247],
    "R21": [162, 328, 1265, 1266, 1267, 1271, 1272, 1274, 1276],
    "R22": [305, 405, 415, 1006, 1353, 1355, 1365, 1373, 1375],
    "R23": [208],
    "F1": [50, 319, 789, 1207, 1327], "F2": [865, 891], "F3": [623],
    "F4": [73], "F5": [26], "F6": [1160, 1176, 1193],
    "F7": [1287, 1288, 1337],
    "A": [1102, 1103, 1104] + rng(1113, 1124) + rng(1126, 1129) + rng(1131, 1134) + [1144, 1391],
    "B": [29, 99, 528, 1170, 1171, 1188],
    "C": [36, 49, 389, 396, 466, 643, 693, 705, 884, 963, 1057, 1067, 803, 1069,
          1302, 1329, 1399, 1401],
    "D": [266, 267, 715, 736, 737, 932],
}

mapped_lines = set()
for cls, ls in APPENDIX_A.items():
    mapped_lines.update(ls)

my_lines = set(hit_lines)
print(f"\nAPPENDIX-A MAPPED LINES: {len(mapped_lines)}")

only_mine = sorted(my_lines - mapped_lines)
only_a = sorted(mapped_lines - my_lines)
print(f"LINES I HIT BUT APPENDIX A LACKS: {only_mine}")
for ln in only_mine:
    print(f"   L{ln} [{','.join(hit_lines[ln])}]: {lines[ln-1].strip()[:110]}")
print(f"LINES APPENDIX A MAPS BUT I DON'T HIT: {only_a}")
for ln in only_a:
    print(f"   L{ln}: {lines[ln-1].strip()[:110]}")

# Hits-per-class recomputed from MY hit counts on Appendix A's line sets
print("\nHITS PER APPENDIX-A CLASS (my raw hit counts on its line lists):")
grand = 0
groups = {"R-rows": [k for k in APPENDIX_A if k.startswith("R")],
          "F-families": [k for k in APPENDIX_A if k.startswith("F")],
          "A": ["A"], "B": ["B"], "C": ["C"], "D": ["D"]}
for gname, keys in groups.items():
    n = sum(len(hit_lines.get(ln, [])) for k in keys for ln in APPENDIX_A[k])
    grand += n
    print(f"  {gname}: {n}")
print(f"  SUM: {grand}")

# PE6 claims rows 13 and 18 are pattern-free; their sites per Appendix B:
# row 13 site L632, row 18 site L1033-34.
for ln in (632, 1033, 1034):
    print(f"ROW-13/18 SITE L{ln} hits: {hit_lines.get(ln, 'NONE')}")

# expected values
EXP = {"total": 194, "lines": 147,
       "per": {"consum": 84, "only": 51, "never": 18, "alone": 15,
               "self_contained": 9, "independen": 8, "free": 6, "not_affected": 3}}
ok = (total == EXP["total"] and len(hit_lines) == EXP["lines"]
      and all(per_pattern[k] == v for k, v in EXP["per"].items())
      and not only_mine and not only_a)
print(f"\nMATCH VS PE6: {'EXACT' if ok else 'DIVERGENCE'}")
sys.exit(0 if ok else 1)
