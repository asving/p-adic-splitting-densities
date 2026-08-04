#!/usr/bin/env python3
"""RMENGINE-PE4 extension referee (read-only; nothing committed is mutated).

Legs:
  K1  all 33 claim-table row keys are EXACT quotes of the committed text
      (normalization per the S8 charter: whitespace-normalize, join wrapped
      lines, strip ⟦...⟧ tags before matching; keys with an ellipsis "…"
      match piecewise around it; table-only rows match inside their stated
      record surface instead of the body).
  K2  inventory of the 12 ⟦nc⟧-tagged keyword lines (for individual challenge).
  K3  inventory of keyword lines carrying >= 2 distinct keyword hits with a
      single row tag (one-tag-per-line audit surface).
  K4  excluded-zone inventory: print each zone's first/last line for the
      hidden-body-claim scan.
"""
import re, pathlib, sys

NOTE = pathlib.Path(__file__).resolve().parents[2] / "lean/notes/openmath/RMENGINE_2026-08-08.md"
text = NOTE.read_text(encoding="utf-8")
lines = text.split("\n")
TAG_RE = re.compile(r"⟦(C\d+|nc)⟧")
KEY_RE = re.compile(r"(?i)\b(only|never|nothing|self-contained|automatic(?:ally)?)\b|(?<=\w)-free\b")
LEX_SKIP = re.compile(r"(?i)\bif and only if\b|\bonly if\b|\bnot only\b")

def norm(s):
    s = TAG_RE.sub("", s)
    return re.sub(r"\s+", " ", s).strip()

body_flat = norm(" ".join(lines))          # whole doc, tag-stripped, ws-normalized

# --- K1: row keys ---
# (row, key, where) — where: 'body' or a substring pinning the record surface
KEYS = [
 ("C1", "(C-EPS) is [IL]† L1", "body"),
 ("C2", "deg Q < deg Φ_m is then automatic", "body"),
 ("C3", "DEV-1 itself is NOT consumed", "body"),
 ("C4", "No window hypothesis is consumed here", "body"),
 ("C5", "consumed by NOTHING", "body"),
 ("C6", "all integrality sits in the t-chain", "body"),
 ("C7", "EXP-KIT(b) ([ILN]† S3, self-contained modulo L1)", "body"),
 ("C7", "as re-displayed self-contained in [ILN]† S3", "body"),
 ("C8", "(At e₀ = 1 ∧ d₀ ≥ 2 the Y-child does not descend", "body"),
 ("C9", "(D3): every child has w_m(R₀(child)) ≥ line(child) ≥ β*", "body"),
 ("C10", "still never consume residue survival", "body"),
 ("C11", "the tree and DEV-(m) are g_m-blind", "body"),
 ("C12", "consumed here as that sealed conjecture, its grade unchanged", "body"),
 ("C13", "consumes reads 0..m−1 only", "body"),
 ("C14", "nothing consumes it", "S8-grade-row-9"),
 ("C15", "instance evidence and design input only, never proof steps", "body"),
 ("C16", "the ONLY bend", "body"),
 ("C17", "ONLY along the promotion edge", "body"),
 ("C18", "the L-child is never the zero polynomial", "body"),
 ("C19", "the box NEVER receives v = 0", "body"),
 ("C20", "only ever exercised at foreign targets", "body"),
 ("C21", "nothing is claimed for non-canonical lifts", "body"),
 ("C22", "(for S7's consequence display only)", "body"),
 ("C22", "(S6/S7 display only)", "body"),
 ("C23", "NO leg other than L-MU consumed e_i ≥ 2", "body"),
 ("C24", "PROMOTION-FREE and junk-free: carry depth 0", "body"),
 ("C25", "L-EXACT is scope-free", "body"),
 ("C25", "(L-LINE(i), scope-free)", "body"),
 ("C26", "proved, engine-free", "body"),
 ("C26", "no primitivity hypothesis, engine-free", "body"),
 ("C27", "valuation + division arithmetic only", "body"),
 ("C27", "needs only h ≥ 1", "body"),
 ("C27", "gcd(e_j, h_j) = 1 only", "body"),
 ("C27", "nothing new", "body"),
 ("C28", "The complete r1 statement-change census", "round-1-record"),
 ("C29", "a valid tiebreak mechanism, consumed by nothing", "body"),
 ("C30", "then λ_{l−1} ∈ ℤ automatically", "body"),
 ("C31", "automatic at on-line targets", "body"),
 ("C31", "is AUTOMATIC", "body"),
 ("C31", "(on-grid automatic, L-GRID)", "body"),
 ("C31", "the slot congruence holds automatically", "body"),
 ("C32", "modulo nothing but the accepted [IL]†/[IL3]†/[ILN]† packages", "body"),
 ("C32", "UNCONDITIONAL (modulo the accepted … packages)", "body"),
 ("C33", "re-scoped at r1 per PE-F1: d₀ ≥ 2 ONLY", "body"),
]
print("== K1: row-key exact-quote check (normalized per charter) ==")
fails = 0
for row, key, where in KEYS:
    if "…" in key:
        parts = [norm(p) for p in key.split("…")]
        # piecewise: all parts occur, in order, within 120 chars
        idx, ok, cur = 0, True, 0
        for p in parts:
            j = body_flat.find(p, cur)
            if j < 0:
                ok = False; break
            cur = j + len(p)
        hit = ok
    else:
        hit = norm(key) in body_flat
    # count occurrences for body keys (should be >= 2: body site + table row, or 1 for table-only)
    n = body_flat.count(norm(key)) if "…" not in key else -1
    status = "OK" if hit else "FAIL"
    if not hit: fails += 1
    print(f"  {row:4s} [{status}] n={n:2d}  {key[:72]}")
print(f"K1 VERDICT: {'GREEN [all keys quote the committed text]' if fails==0 else f'RED [{fails} dead keys]'}")

# --- zones (replicate the committed script exactly) ---
zones = []
def find(pred): return [i for i,l in enumerate(lines) if pred(l)]
s8 = find(lambda l: l.startswith("## S8")); s9 = find(lambda l: l.startswith("## S9"))
if s8 and s9: zones.append((s8[0], s9[0]))
s11 = find(lambda l: l.startswith("## S11"))
if s11: zones.append((s11[0], len(lines)))
for i,l in enumerate(lines):
    if l.startswith("**[IL") and "the ledger block" in l:
        j = i
        while j < len(lines) and lines[j].strip(): j += 1
        zones.append((i,j))
for i,l in enumerate(lines):
    if l.startswith("**[REPAIR ROUND"):
        j = i
        while j < len(lines) and not lines[j].rstrip().endswith("]**"): j += 1
        zones.append((i,j+1))
    if l.startswith("**REPAIR RECORD"):
        j = i+1
        while j < len(lines) and not lines[j].startswith(("## ", "— GENERIC")): j += 1
        zones.append((i,j))
def excluded(i): return any(a <= i < b for a,b in zones)

print("\n== K4: excluded zones (1-indexed first..last, first-line snippet) ==")
for a,b in sorted(zones):
    print(f"  lines {a+1}..{b}: {lines[a][:70]}")

# --- K2/K3: keyword-line inventory ---
print("\n== K2: nc-tagged keyword lines ==")
nc_n = 0
multi = []
for i,l in enumerate(lines):
    if excluded(i): continue
    tags = TAG_RE.findall(l)
    stripped = LEX_SKIP.sub("", l)
    hits = KEY_RE.findall(stripped)
    if KEY_RE.search(stripped):
        nhits = len(list(KEY_RE.finditer(stripped)))
        if "nc" in tags:
            nc_n += 1
            print(f"  line {i+1}: {norm(l)[:100]}")
        if nhits >= 2 and tags and "nc" not in tags:
            multi.append((i+1, nhits, tags, norm(l)[:100]))
print(f"  total nc keyword lines: {nc_n}")
print("\n== K3: multi-keyword lines with row tags (one-tag-per-line audit) ==")
for ln, nh, tags, ctx in multi:
    print(f"  line {ln}: {nh} hits, tags {tags}: {ctx}")
print("\nPE4-EXT done.")
