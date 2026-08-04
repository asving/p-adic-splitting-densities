#!/usr/bin/env python3
"""RMENGINE claims-table MACHINE CENSUS — the tag grammar (r3; the ITERLAWN
machine-census pattern, made syntactic).

The recurring charter defect (PC-G3 -> PC2-g2/PE2-1 -> PC3-g2: three rounds of
hand censuses, each finding new absentees) is structural: "in-scope dependency
claim" is fuzzy, so no fuzzy matcher or hand pass can CLOSE the charter. This
script closes it syntactically:

  GRAMMAR (in the note body, outside excluded surfaces):
    - every occurrence of a charter keyword (only / never / nothing / -free /
      self-contained / automatic) must lie on a physical line that carries
      either an explicit row tag  ⟦C<nn>⟧  (this claim is covered by table row
      C<nn>) or the non-claim marker  ⟦nc⟧  (this keyword occurrence asserts no
      dependency/scope fact about this note's proof chain — rhetoric, arithmetic
      narration, or an upstream note's own claim). One tag covers ALL keyword
      hits on its line.
    - every ⟦C<nn>⟧ must reference an existing row of the S8 claims table.
    - every table row must be referenced by at least one body tag OR carry the
      row-note "(table-only: <reason>)" in its site column (for rows whose grep
      key lives in an excluded surface, e.g. repair-record claims).

  EXCLUDED SURFACES (no tags required): the S8 tables themselves, the head
  repair brackets, the tail repair records, the S11 residual list, and the
  ledger-quote blocks — these record or aggregate claims; they are not body
  claims. Verbatim ⟦...⟧-free quotes of round reports are also excluded by the
  bracket-context rule below.

  VERIFIER AFFORDANCE: any ⟦nc⟧ can be challenged INDIVIDUALLY (is this really
  a non-claim?) — a focused, local judgment replacing the unclosable global
  census. The tag placement is part of the note's audited text.

Output: per-class counts, then every violation (untagged keyword line, dangling
tag, unreferenced row). Exit 0 iff zero violations. Run from anywhere.
"""
import re, sys, pathlib

NOTE = pathlib.Path(__file__).resolve().parents[2] / "lean/notes/openmath/RMENGINE_2026-08-08.md"
KEY_RE = re.compile(r"(?i)\b(only|never|nothing|self-contained|automatic(?:ally)?)\b|(?<=\w)-free\b")
TAG_RE = re.compile(r"⟦(C\d+|nc)⟧")
LEX_SKIP = re.compile(r"(?i)\bif and only if\b|\bonly if\b|\bnot only\b")

text = NOTE.read_text(encoding="utf-8")
lines = text.split("\n")

# --- excluded surfaces ---
zones = []
def find(pred):
    return [i for i, l in enumerate(lines) if pred(l)]
s8 = find(lambda l: l.startswith("## S8"))
s9 = find(lambda l: l.startswith("## S9"))
if s8 and s9:
    zones.append((s8[0], s9[0]))
s11 = find(lambda l: l.startswith("## S11"))
if s11:
    zones.append((s11[0], len(lines)))
for i, l in enumerate(lines):
    if l.startswith("**[REPAIR ROUND"):
        j = i
        while j < len(lines) and not lines[j].rstrip().endswith("]**"):
            j += 1
        zones.append((i, j + 1))
    if l.startswith("**REPAIR RECORD"):
        j = i + 1
        while j < len(lines) and not lines[j].startswith(("## ", "— GENERIC")):
            j += 1
        zones.append((i, j))

def excluded(i):
    return any(a <= i < b for a, b in zones)

# --- table rows ---
rows = set()
if s8 and s9:
    for l in lines[s8[0]:s9[0]]:
        m = re.match(r"\|\s*(C\d+)\s*\|", l.strip())
        if m:
            rows.add(m.group(1))
table_only = set()
if s8 and s9:
    for l in lines[s8[0]:s9[0]]:
        m = re.match(r"\|\s*(C\d+)\s*\|", l.strip())
        if m and "(table-only:" in l:
            table_only.add(m.group(1))

# --- census ---
viol_untagged, viol_dangling, used_tags = [], [], set()
n_kw_lines = n_nc = n_ctag = 0
for i, l in enumerate(lines):
    if excluded(i):
        continue
    tags = TAG_RE.findall(l)
    for t in tags:
        if t != "nc":
            used_tags.add(t)
            if t not in rows:
                viol_dangling.append((i + 1, t))
    stripped = LEX_SKIP.sub("", l)
    if KEY_RE.search(stripped):
        n_kw_lines += 1
        if not tags:
            viol_untagged.append((i + 1, re.sub(r"\s+", " ", l).strip()[:110]))
        elif "nc" in tags:
            n_nc += 1
        else:
            n_ctag += 1

viol_unref = sorted(r for r in rows if r not in used_tags and r not in table_only)

print(f"MACHINE CENSUS (tag grammar): {n_kw_lines} keyword lines in body "
      f"({n_ctag} row-tagged, {n_nc} nc-tagged); {len(rows)} table rows "
      f"({len(table_only)} table-only); excluded zones: {len(zones)}")
ok = True
if viol_untagged:
    ok = False
    print(f"\nUNTAGGED keyword lines ({len(viol_untagged)}):")
    for ln, ctx in viol_untagged:
        print(f"  line {ln}: {ctx}")
if viol_dangling:
    ok = False
    print(f"\nDANGLING tags ({len(viol_dangling)}): " + ", ".join(f"line {ln}:{t}" for ln, t in viol_dangling))
if viol_unref:
    ok = False
    print(f"\nUNREFERENCED rows ({len(viol_unref)}): " + ", ".join(viol_unref))
print("\nCENSUS " + ("CLOSED — zero violations." if ok else "OPEN — violations above."))
sys.exit(0 if ok else 1)
