# GRTJB-PE3 — hostile verification pass on the post-r2 J-B tree-junction note (FIRST ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD**, i.e. the
r0 note (composed 5a72b62, sealed 7f6759d, verdict f5578d0) **plus repair round
r1** (`4c97649` + `46f9452`) **plus repair round r2** (`67bf0c4` = walker2 sealed
unrun, `888e293` = artifacts + the note's r2 block).
**Scripts re-run (all four):** `verification/openmath/grt_jb_checks.py` (sealed) ·
`grt_jb_r1_levelcensus.py` · `grt_jb_printwalk.py` · `grt_jb_printwalk2.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-05 (wallclock). Prior passes **JB-PE1** (85a8dc9, 1C+9G) and
**JB-PE2** (`GRTJB_passPE2_report.md`, 0C+7G) read in full, and both repair
diffs read, before this pass formed any judgment. This is the THIRD hostile
reader; it deliberately attacks the sites the first two only spot-checked
(§2–§4 body mathematics, the fences as a system, the r2 instrument's code).

---

## §0. VERDICT

**0 CRITICAL, 8 JUSTIFICATION GAPS.**

    GRTJB-PE3 FINDINGS: 0 critical, 8 gaps / VERDICT: NOT CLEAN
    acceptance counter stays 0/2 (a pass with findings is not a clean pass)

(Findings are numbered F-1, F-1B, F-2 … F-7 and are listed in severity order;
F-1B is a same-class sibling of F-1, given a non-sequential label so that no
other finding number moves.)

All seven PE2 gaps were applied, and applied correctly, except that **r2's own
repairs reproduced G2-1's disease twice more**: the retracted-but-carried u ≥ 0
proviso does not reach §7.2's JB-VTX row nor §7.3's polygon half (F-1), and the
NEW qcap fence r2's re-grep put on JB-TREE(iii)/(iv) does not reach the grade cap
or JB-BOX-2 — while r2 explicitly declares both of those surfaces "already
consistent" (F-1B). So the answer to "are the eight re-fenced grade surfaces now
mutually consistent?" is **no, at four sites, in two independent fences**.

The other new findings are concentrated where nobody has dug: the
**machine-evidence audit of §2/§3** (F-2, F-3 — one advertised second engine is
provably unable to fire, one advertised tie count exceeds the code by exactly
the tie that has no leg at all), the **level bookkeeping of the single r2
perimeter** (F-4 — the three layers of JB-DEV(iii) sit on J-A hypotheses stated
at DIFFERENT levels, and the fence is written once), and three smaller
quantifier/record defects (F-5, F-6, F-7).

Everything else I attacked SURVIVED, including the parts PE1/PE2 only sampled:

* **JB-VTX(a) re-derived in full from the print source** — including the second
  half `e_q·u_i + h_q·i = v_{q+2}(A_i Φ_q^i)`, which I checked against
  `propertiesv` item 3 in `docs/references/HigherNewton.tex` under the §1 index
  dictionary. It is right, and the index shift is right (§2.1).
* **JB-VTX(b)(c) and JB-AFF** re-derived; the realized-side-goes-horizontal and
  slope-translation arithmetic is exact (§2.1).
* **The JB-ID identity's proof is correct** and the runner's `jb_id` print leg is
  genuinely print-side (unlike `jb_dev`'s — F-2) (§2.3).
* **The (VAL)/(GRID)/(RES) transcriptions are faithful to J-A**, verbatim-checked
  against `GRTJA_PROOF_2026-08-08.md` §3.1/§3.3/§3.4 (§2.2).
* **G2-6's perimeter choice is SOURCE-CORRECT.** J-A's own §1 defines the
  shared-key perimeter at level m as "Φ_q = φ_{q+1} for all q ≤ m−1" — the
  *strictly below* reading — so r2 picked the reading the source uses, and the
  runner's `qcap = min(n, shared_upto+1)` is exactly the top level admitted by
  it. r0/r1's "for all j ≤ q" was the mis-transcription. This is a clean fix
  (§3.1).
* **G2-4's sharpened refutation is CONFIRMED FROM THE COMMITTED ROSTER** — T3D
  and T3E share `reads[0] = (2,1,2)` and `psi[0] = [1,1,1]` literally, hence the
  same `A_1 = 2` and the same `ord(z_1) = 3`, and they still split (§4).
* **walker2's gate, certificates and reconciliation are correctly implemented**
  and its disclosed limitation is honoured everywhere in the note (§5).
* **Every figure in the note reproduces**: 66 = 56+2+8, 21 = 13+8, 458 = 362+96,
  45+27+12 = 84, 8 byteeq-false rows = 4 base (12 walks) + 4 chamber (8 walks),
  79/125 tree walks, PW-ID 38 (§1, §6).
* **All four scripts exit 0 and reproduce bit-identically** (§1).

The seven gaps, most-severe first, are stated in §7.

---

## §1. MACHINE LEG (mandatory — all FOUR runners RUN, exit 0)

Run from `verification/openmath/`, `python3`, no arguments, nothing edited.

| runner | md5 at HEAD | exit | reproduction |
|---|---|---|---|
| `grt_jb_checks.py` (sealed) | `55f4911eaddd8524fd91368b30ed71bd` **intact** | **0** | 18/18 families GREEN, 6,700 samples, 0 violations, elapsed 0.7 s; every per-family count and every census identical to the note's §7.1 |
| `grt_jb_r1_levelcensus.py` | `2bcb44fdbf839d367f0e11033a5d3fd7` | **0** | output identical to committed `_output.txt`, line for line |
| `grt_jb_printwalk.py` | `f53e23e8d1c79f084a1e34eee857e37c` **intact** | **0** | 5/5 families GREEN, 458 total samples, coverage 84 / 12 / 72 — identical to committed `_output.txt` |
| `grt_jb_printwalk2.py` | `6c6318f7fc6570a2d454389b38441329` **intact** | **0** | 3/3 families GREEN, 45 / 27 / 28 on their predictions, 0 violations — identical to committed `_output.txt` |

**Sealed-runner figures vs §7.1 (all match):** EXT-GATE 1 · JB-DEV 893 ·
JB-KEYEQ 25 · JB-SHEAR 893 · JB-VTX 893 · JB-ID 34 · JB-TREE 79 · JB-LINE 194 ·
JB-EPS 955 · JB-CM 28 · JB-CREAD 79 · JB-QO 5 · JB-D0 4 · TW-JB 2,480 · teeth
3/3/3/3 all caught. Censuses **scored 104 | boundary 21 | v = 0: 0 | R = 0: 0 |
off-perimeter tree rows 0**.

**Level census vs §7.4(A) (all match):** m = 1 scored 45 / boundary 0 · m = 2
scored 8 / boundary 10 (T3A 3, T3B 3, T3C 1, T3D 3) · m = 3 scored 3 /
boundary 3 (I4B) · reasons R EVAL-FALSE 10, f EVAL-FALSE 3, scope-outs 0 ·
cross-check 13 + 8 = 21.

**walker2 mini-seal: HOLDS.** `67bf0c4` adds `grt_jb_printwalk2.py` only (no
`_output.txt`, no `_results.json`); `888e293` adds those two artifacts plus the
note's r2 block; the script's md5 is identical at both commits and at HEAD. The
r1 walker and the sealed runner are byte-untouched by r2, as the note claims.

**Byte census (JB-KEYEQ) spot-check against §7.1's examples:** `I4A {1:T,2:T,3:T}`,
`I4B {1:T,2:T,3:T}` (byte-equal through the census top ✓), `T3A/T3C/T3D/T3E`
all `{1:T,2:F}` (diverge at q = 2 ✓), `I4C {1:T,2:F,3:F}` (q = 2, 3 ✓). The
three `{}` rows are the T.n = 0 QO shapes, as G-3 says.

---

## §2. THE BODY MATHEMATICS (charge 1 — the part PE1/PE2 only spot-checked)

### 2.1 JB-VTX(a)–(d) and JB-AFF, re-derived

**(a) first half — CORRECT.** With §1's `u_i := v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})`
and `H(f) := {(i, e_q·w_q(A_i) + i·γ_{q+1})}`:

    Σ_q(i, u_i) = (i, e_q·v_{q+1}(A_i) + i·[e_q·v_{q+1}(φ_{q+1}) + h_q])
                = (i, e_q·w_q(A_i)   + i·γ_{q+1})

using `v_{q+1} = w_q` on `A_i` (JA-VAL) and on the key (`v_{q+1}(φ_{q+1}) = w_qΦ_q`
at the representative pin) plus `γ_{q+1} = e_q w_qΦ_q + h_q`. Exact.

**(a) second half — CORRECT, and the index shift is right.** The note asserts
`e_q·u_i + h_q·i = v_{q+2}(A_i·Φ_q^i)` "(propertiesv item 3 at a single digit)".
The print (`docs/references/HigherNewton.tex`, Prop `propertiesv` item 3) reads

    v_r(P) = min_i {v_r(a_i φ_{r-1}^i)}
           = e_{r-1} · min_i {v_{r-1}(a_i) + i(v_{r-1}(φ_{r-1}) + |λ_{r-1}|)}

At `r = q+2` this is `e_{q+1}^cls` and `|λ_{q+1}^cls| = h_{q+1}^cls/e_{q+1}^cls`;
under §1's dictionary (GMN level i = harness read i−1) those are the harness
`e_q, h_q`, so term-by-term

    v_{q+2}(a_i φ_{q+1}^i) = e_q·[v_{q+1}(a_i) + i·v_{q+1}(φ_{q+1})] + h_q·i
                           = e_q·u_i + h_q·i .

The "at a single digit" gloss is doing real work and is legitimate: applied to
`P = a_i φ^i` alone the development is that one term (deg a_i < deg φ), so the
`min` is that term. **No defect.**

**JB-AFF — CORRECT** (two lines, and both relations quoted are the defining ones
for lower hulls; `a > 0` is used exactly where needed).

**(b) — CORRECT** given (a) + JB-AFF; the runner keys it as
`vH == [(x, e*y + h*x) for (x,y) in vU]` on fresh hulls, which is the statement.

**(c) — CORRECT** on slope and abscissa run: `(e_q u₁ + h_q i₁ − e_q u₀ − h_q i₀)
/(i₁−i₀) = e_q σ + h_q`, and `σ = −h_q/e_q ↦ 0`. The lattice-data sentence
("degree d = (abscissa run)/e is the same integer in both frames") is trivially
true as an arithmetic statement (the run is preserved and `e` is print-side);
its substantive parenthetical "(the print's d(S) = the harness grid count)" is
clear only on the REALIZED side, where the lowest-terms denominator is `e_q`. I
record this as loose wording, not a finding: `hull_sides` keys the slope/length
law, which is what (c) claims in its first sentence.

**(d) — three of the four ties are real; the fourth is F-3.** See §2.4.

### 2.2 The (VAL)/(GRID)/(RES) layers — transcription check against J-A

| layer | note's text | J-A source | verdict |
|---|---|---|---|
| (VAL) | `w_q(A_i) = v_{q+1}(A_i)` | §3.1 THEOREM JA-VAL "for every m ≥ 0 and every nonzero A: w_m(A) = v_{m+1}(A)", grade "PROVED (attempt grade), unconditional on the shared-key perimeter" | **faithful**; and it is machine-keyed digit-by-digit (`jb_dev`'s `G.vgen(q+1,A) != T.wlev(q,A)`) |
| (GRID) | "the on-line attained abscissas lie on the print's T-side grid s + j·e_q, and the plain carry = the side-lattice crossing indicator" | §3.3 JA-GRID (b) "the print's slot grid s + je and slot values V_j equal the harness digit grid and digit weights at every junction slot" + (c) the carry clause | **faithful compression**; and the note's fence is CORRECT in riding (a)'s `[JA-r1]` proviso, since (b) is stated "consequently" from (a). (c) rides nothing, and the note says so at two places. |
| (RES) | "at read level m := q+1 ≥ 2 … c_i = z_{m−1}^{−i·A_{m−1}}·C_i … unconditional at m = 2, per-digit proviso at m ≥ 3" | §3.4 THEOREM JA-RES "Level m ≥ 2, shared keys below m. IF (VD-(m−1)) holds at every on-line digit a_i … THEN for every attained abscissa i: c_i = z_{m−1}^{−i·A_{m−1}}·C_i … the law is UNCONDITIONAL at m = 2" | **faithful in content**; the note drops "for every attained abscissa i" (harmless) — but its LEVEL bookkeeping is F-4 |

The r1/F1 fence separating JA-RES (per-slot, unconditional at m = 2) from the
evaluated dictionary (VD-2) is correct and is stated at every one of the 22
sites PE2 enumerated; I re-grepped `VD-`/`JA-RES`/`JA-VDIND`/`uncond` and found
no regression and no new site.

### 2.3 The JB-ID identity's proof — CORRECT

`(ID-(i+1))` rearranges to `Φ_{i+1} = Φ_i^{P_i} + Σ_{k<g_i} C_k^{(i)} Φ_i^{e_i k}`.
For this to BE the `Φ_i`-adic development one needs exactly two facts, and the
note names both: (α) `deg C_k^{(i)} < deg Φ_i` ("the C_k are reduced, REALIZE
R1"), (β) the abscissas `e_i·k` (k < g_i) are distinct and all `< P_i`. Given
`P_i = e_i g_i` (β) is immediate, and uniqueness of the `Φ_i`-adic development
finishes. The runner's `jb_id` keys exactly this (the identity, then
`fresh_dev(Φ_{i+1}, Φ_i)` digit-by-digit against the expected list), and its
print leg is genuinely print-side (`fresh_dev(G.phi[r], G.phi[r-1])`, grid
support + shear-constancy) — unlike `jb_dev`'s print leg (F-2).

One residue: **`P_i` is used undefined in this note** (F-7).

### 2.4 What `jb_shear_vtx` actually checks vs what §3/§7.1 advertise

`jb_shear_vtx` (grt_jb_checks.py L258–296) contains, after the pointwise shear
check, exactly **three** tie assertions:

    if minH != T.wlev(q + 1, f):                 viol   # (d) minH = w_{q+1}(f)
    if q <= L:
        if minU != G.vgen(q + 1, f):             viol   # (d) minU = v_{q+1}(f)
        if q + 1 <= G.RANK and minH != G.vgen(q + 2, f): viol   # (d) = v_{q+2}(f)

and then (b) the vertex bijection and (c) the per-side slope/length law. Clause
(e) (the window clause) has **no leg in this family at all** — correctly, since
it is a W2-C1a consumption, and the note does not claim one for it. The
"four min/read ties" claim is F-3.

---

## §3. THE r2 FENCES AS A SYSTEM (charge 2)

### 3.1 G2-6's perimeter, checked against the SOURCE (not just internally)

PE2's G2-6 found §1's definition (`j ≤ q`) contradicting the r1 citations
(`j < q`). r2 split them and pointed every citation at the *strictly below*
reading. **This is the source-correct choice**, which PE2 could not confirm
because it did not open J-A. `GRTJA_PROOF_2026-08-08.md` L69–70:

> **Shared-key perimeter at level m**: Φ_q^har = φ_{q+1}^cls byte-for-byte for
> all **q ≤ m−1** (all operators at level m consume only keys that deep).

So J-A's perimeter at level m is `j ≤ m−1`, i.e. strictly below m. At `m = q`
that is `j < q` — r2's SHARED-KEY PERIMETER, verbatim. And
`qcap = min(n, shared_upto+1) = L+1` is precisely the largest level q whose
`j < q` condition is met (`j ≤ L` ✓), with `q = L+2` failing. **The runner's
quantifier and J-A's definition coincide exactly.** No widening; G2-6 is clean.

### 3.2 The eight r2/r1 grade-surface sites, cross-checked pairwise

| site | qcap perimeter carried? | u ≥ 0 proviso carried? |
|---|---|---|
| Grade cap (L21–31) | YES, (VAL)/(GRID)/(RES) at q ≤ qcap | YES |
| §2 ∎ grade line (L516–521) | YES, (i)/(ii)/(iv) free, (iii) at q ≤ qcap | YES |
| §3 theorem head (L539–547) | YES, 0 ≤ q ≤ qcap | n/a (theorem head) |
| §3 ∎ grade line (L608–620) | YES | YES (for clause (d)) |
| §4 ∎ grade line (L692–700) | YES, (iii)/(iv) at m ≤ qcap; (i)/(ii) free | n/a (no JA-GRID) |
| §5 ∎ grade line (L834–841) | not stated — see §3.4 | n/a |
| §7.2 JB-DEV row | YES | YES |
| §7.2 JB-VTX row | YES | **NO — F-1** |
| §7.2 JB-TREE row | YES | n/a |
| §7.2 JB-CREAD row | (VD-m) fence only | n/a |
| §7.3 W-3 bullet | YES | **only for JB-DEV(iii); NOT for JB-VTX(d) — F-1** |
| §7.3 W-5 bullet | YES ((VD-m) ∩ {v≠0}) | n/a |
| JB-BOX-2 | JB-DEV/JB-VTX yes; **JB-TREE(iii)/(iv) missing — F-1B** | YES, and it NAMES JB-VTX(d) |
| Grade cap, JB-TREE sentence (L38–41) | **NO — F-1B** | n/a |
| S-status / counter | 0/2 consistent at all six sites | — |

So neither column closes. The **proviso** column fails at §7.2's JB-VTX row and
§7.3's polygon half (F-1); the **qcap** column fails at the grade cap's JB-TREE
sentence and at JB-BOX-2's own qcap sentence (F-1B). Everything else in the qcap
column is right, and the three hits r2's re-grep found on its own (§3 grade line,
§4 grade line, §7.2 JB-TREE row) are real and correctly applied.

### 3.3 The JB-CREAD conditionality graph, built from scratch

Real dependencies of `ρ_m(R) = c_m·ρ_m(f)`, traced through the proof line by
line, and whether the note states them:

| # | dependency | where it enters the five-line chain | stated? |
|---|---|---|---|
| 1 | (VD-m) at f | line 1 `ρ_m(f) = ε_m(λ)·v` | YES (hypothesis, fully fenced) |
| 2 | (VD-m) at R | line 1 of the display | YES |
| 3 | v ≠ 0 | to get `R_{m,λ+γ}(R) ≠ 0` | YES (stratum, displayed) |
| 4 | [RMG] (C-READ) | display line 2 | YES |
| 5 | [RMG] (C-W_R) (the ≥ half) | pinning `w_m(R) = λ+γ_{m+1}` | YES |
| 6 | [RMG] L-CELL(ii) = (B-READ) + L-CELL(i) | the ≤ half | YES (r1/G-7 resolved it; verbatim-correct) |
| 7 | LEMMA JB-EPS at (V,V′) = (λ, γ_{m+1}) | display line 4→5 | YES — but the instance is outside the lemma's stated quantifier: **F-5** |
| 8 | `τ_m = ε_m(γ_{m+1})^{−1}c_m`, `c_m = ψ_{m,0}` | display line 3 | YES ([ILN]† WELL-DEF + REALIZE R3) |
| 9 | `τ_m` a unit ← `ψ_j(0) ≠ 0` | before the display | YES (r1 hygiene) |
| 10 | `R ≠ 0` (so `s_m^ini(R)`, `ρ_m(R)` are defined) | implicit in `ρ_m(R)` | **derived, not assumed** — `R_{m,λ+γ}(R) ≠ 0` forces it. Sound; no gap. |
| 11 | `γ_{m+1} ≥ 0` in the level-m weight lattice | JB-EPS's quantifier | **NOT stated: F-5** |
| 12 | the ε′ of JB-EPS = the ε′ of (C-READ) | the cancellation | YES, and **verbatim-correct**: [RMG] S0.2's box says `ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋` with `s_m` the eq-(12-int) split = the note's `s_m^wt`; the runner computes `ep = (s_geo(lam,e,h) + s_geo(gam1,e,h))//e`. Identical integer. |
| 13 | [RMG]'s own scope (T-scope(m), g_m = 1) | via "(RM-m) box … ACCEPTED on its scope" | YES, by the "on its scope" clause + JB-BOX-4 |

Stated dependencies that are NOT real: none found. The `[RMG]` (C-W_Q) clause
is listed in §4(iv) but is not used in §5, and §5 does not claim it.

### 3.4 One perimeter the note does not state for §5 — checked and CLEARED

`run_tower_families` cuts the reduction levels at `qcap_of(T,G)` before
`jb_tree`/`jb_cread` (`if m > qcap_of(T, G): COUNTS['JB-TREE-OFFPERIM'] += 1;
continue`), while §5's grade line names only the (VD-m) perimeter ∩ {v ≠ 0}. I
checked whether this is a hidden fence: it is not. §5's print-side content
enters ONLY through the (VD-m) hypothesis, so the theorem is a legitimate
conditional at any level; and the note discloses the cut's effect exactly
("off-perimeter tree rows: 0" in §7.1, and the §3 grade line's "the
off-perimeter counter is 0 on the roster, so nothing was silently scored
outside the fence"). **No finding.**

---

## §4. G2-4's SHARPENED REFUTATION — CONFIRMED FROM THE COMMITTED ROSTER

The note's strongest new claim in r2 is that T3D and T3E "share the level-0 read
(e₀, h₀, g₀) = (2, 1, 2) and the same ψ₀ (⇒ the same A_1 and the same z₁ of
order 3 in F₄), and they still split". Read off `GWP.TOWERS` (raw spec) and
`ITL.build_tower`:

    T3D  Fpt p=2  reads = [(2,1,2), (2,1,1), (2,1,1)]   psi = [[1,1,1], …]
    T3E  Zp  p=2  reads = [(2,1,2), (1,1,1), (2,3,1)]   psi = [[1,1,1], …]

so `reads[0]` and `psi[0]` are **literally identical byte-lists**, and (built):

    tower  d0  e        h        g        psi0        gam1  l0  A_1  ord(z1)  A_1 mod ord
    T3A    2   [2,2,2]  [1,1,1]  [1,1,1]  [(0,1),(1,0)]  1    1    1    3        1
    T3B    1   [3,2,2]  [1,1,1]  [1,1,1]  [(1,),(1,)]    1    1    1    2        1
    T3C    1   [2,3,2]  [1,2,1]  [1,1,1]  [(1,),(1,)]    1    1    1    2        1
    T3D    1   [2,2,2]  [1,1,1]  [2,1,1]  [(1,),(1,),(1,)] 1  1    2    3        2
    T3E    1   [2,1,2]  [1,1,3]  [2,1,1]  [(1,),(1,),(1,)] 1  1    2    3        2
    T3F    1   [1,3,2]  [2,1,1]  [2,1,1]  [(1,),(0,),(1,)] 2  0    0    4        0

T3D and T3E: same `A_1 = 2`, same `ord(z₁) = 3` (i.e. `K₁ = F₄`), same nonzero
`A_1 mod ord(z₁) = 2` — and T3D is BOUNDARY at m = 2 while T3E scores 6/6. So
the failing set is **not** a function of `(A_1, ord z₁)`, exactly as the note
says. T3F is the unique `e₀ = 1` row and the unique `A_1 = 0` row, so the
surviving implication (`e₀ = 1 ⇒ A_1 = 0 ⇒ (VD-2)`) is consistent and the
"necessary, not sufficient" wording is right. Every entry of the note's §7.1
r2 table (`e`, `h`, `g`, `d₀`, ring, p, verdict, and T3C's "1 row, 2 scored")
matches. **G2-4 is fully discharged; no finding.**

---

## §5. walker2 (`grt_jb_printwalk2.py`) — CODE AUDIT (charge 3)

**Gate — CORRECTLY IMPLEMENTED as `chain_eq ∧ ¬chat_eq`.** L124–141:

    if not chain_eq:  row['noclaim'] += 1 ; COUNTS['PW2-NOCLAIM'] += 1 ; continue
    if chat_eq:       note('PW2-DEGEN') ; …certify… ; continue
    note('PW2-XFRAME')      # ⇒ reached iff chain_eq and not chat_eq

**Non-degeneracy certificate — YES, PER SAMPLE.** Inside the `for f in fpool`
loop, before the walk: `if fCh == fC: viol('PW2-XFRAME', …, 'non-degeneracy
certificate FAILS …')`. This is the right object: `chain_eq` already forces
`div_har == key`, so the ONLY thing that can differ between leg A's and leg B's
argument tuples is the dividend, and `fCh ≠ fC` is exactly that. (It is not
vacuous a priori: `O` is `Z/p^N`-like, so `f·(Ĉ^cls − Ĉ^har) = 0` with `f ≠ 0`
is conceivable.) 45/45 certificates passed.

**Degeneracy certificate — correct and complete.** The DEGEN branch checks
`fCh == fC` and `div_har == key`, i.e. byte-identity of the whole leg-B argument
tuple, and does NOT re-run the comparison. 27/27.

**Reconciliation arithmetic — CORRECT.** `reconcile()` compares per-row
`chain_eq`, `chat_eq`, `walks`, and `a['xframe_rows'] == b['degen'] + b['xframe']`,
plus the walk totals. Recounted by me from the two committed JSONs:

    r1 leg-A walks                                  84
    chain_eq ∧ chat_eq   (9 rows × 3)  degenerate   27
    chain_eq ∧ ¬chat_eq (15 rows × 3)  cross-frame  45
    ¬chain_eq            (4 rows × 3)  no-claim     12
    45 + 27 + 12 = 84 ✓ ; 45 + 27 = 72 = r1's advertised PW-XFRAME ✓
    rows 15 + 9 + 4 = 28 ✓

and the 9 degenerate rows are element-for-element the list the note prints at
L1240–1242. **Also correct:** `all_ok = not VIOL` (ANY violation in ANY family
turns the verdict RED and the exit code 1), and the inherited-violation sweep
over `PW.VIOL` at the end.

**Disclosed limitation — honoured everywhere.** I grepped every mention of the
r2 instrument. The front matter calls it "the GATE REPAIR"; the r2 block says
"Its own disclosed limitation: it imports the frozen r1 walker's machinery on
purpose (gate repair, not decorrelation)"; §7.4(C) says "this is a GATE REPAIR,
not a decorrelated second instrument" and "**What it does not buy:** no new
decorrelation (same machinery, by design)". **Nothing in the note claims
decorrelation for leg (C).** One over-tight phrase is F-6.

**One structural observation, recorded but NOT scored.** Because `chain_eq`
forces `div_har == key` byte-for-byte, on every leg-B row (r1 or r2) the
"harness-key division" is a division by a polynomial byte-identical to the print
key. So no walk in EITHER instrument compares the print-keyed tree against a
division by a genuinely different key — and none can, since where the keys
differ the two divisions are different objects (which is exactly why the note
says "leg B not claimable" on the 12 chain-divergent walks). The note discloses
the divisor byte-equality explicitly in the G2-2 mechanism paragraph, so the
reader is given the fact; the cross-frame content is the multiplicand, and the
note says that too ("the harness multiplicand Ĉ_m^har is a genuinely different
polynomial"). Not a finding.

---

## §6. FIGURE DECOMPOSITIONS (charge 6) — ALL EXACT

Recounted by me from the committed JSONs, not from the note:

| note figure | my recount | verdict |
|---|---|---|
| "non-chamber 66 = 16-tower roster 56 + QO leg 2 + d₀ leg 8" | `cread` block: roster-16 scored **56**, QO **2**, d₀ **8**, chamber **38**; total 104 | **EXACT** |
| "boundary 21 = roster 13 + chamber 8" | roster-16 **13**, QO 0, d₀ 0, chamber **8** | **EXACT** |
| "79 walks (125 with chambers)" | `tree` block walks: non-chamber **79**, all **125** | **EXACT** |
| "458 = 362 LAW samples + 96 coverage-counter increments" | PW-ID 38 + PW-WALK 84 + PW-REASM 84 + PW-DIV 84 + PW-XFRAME 72 = **362**; `PW-UNEQUAL-WALKS` 12 + `PW-CHAIN-DIVERGENT` 12 + `PW-XFRAME-AGREE` 72 = **96** | **EXACT** |
| "PW-ID 38" | Σ over the 28 walker rows of m (20×1 + 6×2 + 2×3) = **38** | **EXACT** |
| G2-3's "EIGHT byteeq: false rows … four base (3 walks each = 12) AND four chamber (2 walks each = 8)" | base: T3A m2, T3C m2, T3D m2, T3E m2 (3 each = 12); chamber: T3A/tw, T3C/tw, T3D/tw, T3E/tw at m = 2 (2 each = 8) | **EXACT** |
| "10 of the 13 roster boundary rows at m = 2" | level census re-run: 0/10/3 | **EXACT** |

---

## §7. FINDINGS

### F-1 — JUSTIFICATION GAP (grade surface; G2-1's disease reproduced by G2-5's own repair). The retracted-but-carried u ≥ 0 proviso is NOT carried at §7.2's JB-VTX row nor at §7.3's polygon half, although JB-BOX-2 names JB-VTX(d) as a consumer

JB-BOX-2, as rewritten in r2, says (L901–903):

> STATUS: CARRIED, DISCHARGE OWED. **Every statement consuming §2(iii)(GRID) —
> JB-DEV(iii)'s (GRID) layer and, through it, the grid/abscissa content of
> JB-VTX(d) — is conditional on this proviso in addition to its other fences.**

and the §3 grade line was correspondingly re-fenced (re-grep hit 6):

> **[r2, G2-1 re-grep — one fence this line was missing: clause (d)'s
> read-grid/attained-abscissa content consumes JA-GRID, so it also rides
> JA-GRID(a)'s UNDISCHARGED `[JA-r1]` u ≥ 0 proviso (r2, G2-5; carried in
> JB-BOX-2).**

But the two surfaces a downstream unit actually reads still omit it. §7.2's
JB-VTX row (L1067) reads, in full:

> | JB-VTX | window/development polygon = Σ_q(N_{q+1}(f)) vertex-for-vertex;
> slope/length translation; **min/read ties**; window clause | PROVED (attempt
> grade), at the W2-C1 representative ~~(no perimeter)~~ **[r2, G2-1 — AND ONLY
> ON THE SHARED-KEY PERIMETER 0 ≤ q ≤ qcap … the (d) print-side min ties are
> machine-restricted further to q ≤ shared_upto. Clause (e) is at
> f = Φ_{q+1}^har (r1, G-4), not at the theorem's quantified f]** |

— the r2 bracket touches clause (d) explicitly ("the (d) print-side min ties")
and still says nothing about the proviso. And §7.3's W-3 bullet (L1088–1089):

> The (GRID) layer inside JB-DEV(iii) rides JA-GRID(a)'s undischarged u ≥ 0
> proviso (r2, G2-5), and JB-VTX(e) is at f = Φ_{q+1}^har only (r1, G-4).

W-3 is defined two lines above as "both halves of the identity (expansion +
polygon…)"; the proviso is attached to the expansion half only, so a consumer
reading §7.3 alone takes the polygon half's read-data content as proviso-free —
which JB-BOX-2 says it is not.

This is exactly the defect PE2 raised as G2-1 ("the grade surface downstream
units read is the one PE1's G-9 named"), one round later and for the r2 fence
instead of the r1 fence — and it survived r2's *own* mandated re-grep, which
the note advertises as "**RE-GREP RESULT: 8 grade-surface hits inconsistent with
the r1/r2 body fences, all 8 fixed**". Classification: gap, not critical — the
body fences are right and JB-BOX-2 is right, so the conditionality is on record;
what is wrong is the two surfaces that exist in order to be read alone.

### F-1B — JUSTIFICATION GAP (grade surface, and a false consistency declaration). The qcap fence r2's re-grep NEWLY put on JB-TREE(iii)/(iv) does not reach the grade cap or JB-BOX-2 — the two surfaces r2 declares "already consistent"

Re-grep hit 7 added a fence that did not exist before r2 (§4 ∎ grade line,
L692–700):

> **[r2, G2-1 re-grep — a fence r1 carried into §2/§3 and left out of this grade
> line, although this section consumes the same input: clauses (iii) and (iv) use
> JA-VAL …, which J-A grades "PROVED unconditionally ON THE SHARED-KEY
> PERIMETER" — so (iii)/(iv) are asserted at levels m ≤ qcap = min(n,
> shared_upto+1) (§1) … Clauses (i)/(ii) are perimeter-free**

and hit 8 carried it to §7.2's JB-TREE row. It was carried to **neither** of the
two surfaces that summarise the whole note. The grade cap — the paragraph headed
"**Grade cap (read first)**", which does carry the qcap fence for JB-DEV's three
layers and for JB-VTX — says of JB-TREE only (L38–41):

> JB-TREE (§4) is PROVED at attempt grade on [RMG]'s own scope (T-scope(m)
> termination fence, g_m = 1 rows for the Ĉ_m instance), consuming [RMG] as
> ACCEPTED and LED-Λ at ATTEMPT grade (its λ_E face is cited as the polygon
> bookkeeping — the grade rides).

and JB-BOX-2's own perimeter sentence (L911–914) enumerates the fenced
statements and omits JB-TREE:

> **[r1, G-9]** The (VAL)/(GRID)/(RES) layers **and all of JB-VTX** are
> quantified on the SHARED-KEY perimeter q ≤ qcap … — restated at §2(iii) and at
> the JB-VTX theorem.

The honesty defect is the accompanying declaration. The r2 block states
(L238–241):

> and all three corrections MOVE IN THE DIRECTION OF MORE CONDITIONALITY (no
> statement is widened anywhere in r2). **The grade cap, the §5 grade line and
> JB-BOX-2 were already consistent and are untouched except for the G2-5
> proviso.**

The grade cap and JB-BOX-2 were consistent *before* hit 7, precisely because
nothing yet said JB-TREE(iii)/(iv) needed the perimeter. Hit 7 created the
inconsistency in the same round, and this sentence asserts its absence. So r2's
re-grep is not complete on its own terms: the sweep found three new hits and
introduced a fourth and fifth. Classification: gap, not critical — the fence is
on record at §4 and §7.2, and the direction is toward more conditionality, so no
statement is unsound; what is wrong is that the two summary surfaces still grade
JB-TREE with no perimeter and the note certifies that they need none.

### F-2 — JUSTIFICATION GAP (machine evidence; PE1's G-1 disease at a site r1 did not correct). JB-DEV's advertised "both engines" print-side leg is a re-execution of ONE pure function on byte-equal arguments, and is moreover unreachable in the failure path

§2's machine bracket (L521–525) and §7.1's JB-DEV row (L966) read:

> [Machine: JB-DEV — the development recomputed by this runner's OWN schoolbook
> division (fresh leg, decorrelated from the shared PolyO.dev used by both
> engines) and **compared against both engines' digit lists at every shared
> level**; …]

> | JB-DEV | **fresh schoolbook dev == both engines** + digit weight ties | 893 | GREEN |

The code (`grt_jb_checks.py` L218–233) is:

    dvF = [tuple(a) for a in fresh_dev(T.R, f, key)]
    dvI = [tuple(a) for a in T.P.dev(f, key)]
    if dvF != dvI:
        viol(fam, tag, 'fresh dev != engine dev at q=%d' % q); continue
    if q >= 1 and tuple(G.phi[q + 1]) == key:
        dvG = [tuple(a) for a in G.P.dev(f, G.phi[q + 1])]
        if dvF != dvG:
            viol(fam, tag, 'fresh dev != print dev at q=%d' % q)

Two facts make the "print engine" leg empty:

1. **`G.P` and `T.P` are the same computation.** `iterlawn_pe_reimpl.PolyO`
   carries exactly one attribute — `def __init__(self, R): self.R = R` — and
   `grt_weld_probe.gmn_from_tower(T)` builds `GmnLeg(T.R, …)`, whose
   `__init__` does `self.P = ITL.PolyO(R)` with **the same ring object `T.R`**.
   So `G.P.dev` and `T.P.dev` are the identical method on instances that differ
   in nothing. The guard requires `G.phi[q+1] == key`, so the arguments are
   byte-equal too: `dvG` is bit-for-bit `dvI`, always.
2. **It is guarded behind the very comparison that would have to fail first.**
   The `continue` on `dvF != dvI` means the print leg is only reached when
   `dvF == dvI`; combined with (1), `dvF == dvG` is then forced. The violation
   `'fresh dev != print dev'` is **unreachable**.

Mechanically confirmed (read-only probe, T3B):

    vars(G.P) = {'R': <iterlawn_pe_reimpl.Zp object at 0x7fe89ca23fd0>}
    vars(T.P) = {'R': <iterlawn_pe_reimpl.Zp object at 0x7fe89ca23fd0>}
    G.P.dev.__func__ is T.P.dev.__func__  ->  True
    print-dev leg fired on 38 (q, f) pairs; identical to the harness dev on 38/38

This is precisely what PE1's G-1 charged against `jb_tree`'s print-key leg ("one
`fresh_divmod` re-executed on equal tuples … it cannot fail unless the first
does"), and r1 corrected the JB-TREE wording at three sites while leaving the
same claim standing at JB-DEV. The note's own parenthetical "the shared PolyO
.dev used by both engines" concedes the sharing, which makes the surviving
phrase "compared against **both engines'** digit lists" and "== **both
engines**" the defect: there is one engine comparison, not two, and the second
is not even a consistency re-check (`jb_tree`'s at least runs on a separately
constructed key list; this one is dead code for violation purposes). The real
JB-DEV evidence — `fresh_dev` vs `PolyO.dev`, plus the (VAL) digit-weight tie
`G.vgen(q+1,A) == T.wlev(q,A)`, which IS a genuine two-engine comparison — is
untouched and is what the family actually establishes.

### F-3 — JUSTIFICATION GAP (machine-claim inflation, landing on the one conditional clause). §3 and §7.1 claim JB-SHEAR keys "all four" of clause (d)'s min/read ties; the code has three, and the missing fourth is exactly the (GRID)-derived content that rides the undischarged proviso

§3's machine bracket (L620–625) and §7.1's JB-SHEAR row (L968):

> JB-SHEAR — pointwise shear + **all four min/read ties**, with v_{q+1}(f)
> computed BOTH as min u_i and by the vgen recursion …

> | JB-SHEAR | pointwise shear + **the four min/read ties** (Lemma shape 1
> through a second development) | 893 | GREEN |

Clause (d) states four ties: (d1) `min U(f) = v_{q+1}(f)`; (d2)
`min H(f) = w_{q+1}(f)`; (d3) `= v_{q+2}(f)`; (d4) "the attained abscissas on
the realized side are the read grid `s(λ) + j·e_q`, and the level-(q+1) read is
assembled exactly from the on-line digits at those slots (S0.2 consumed;
JA-GRID)". `jb_shear_vtx` contains **three** tie assertions (quoted in §2.4
above), covering (d1)/(d2)/(d3). **(d4) has no machine leg anywhere in the
battery** — `jb_dev` checks only the (VAL) weight tie, `jb_line` checks
`line == wlev == vgen` on reduced cells, `jb_cread` evaluates (VD-m), and
`jb_eps` keys JA-GRID's **carry** clause (c) (`s_geo(V)+s_geo(V′)−s_geo(V+V′) =
e·ε′`), which is the *other* half of the (GRID) layer. None of these is the
attained-abscissa/read-grid statement, and (c) is precisely the half the note
correctly says carries no proviso.

The sharpness is the coincidence: (d4) is the clause r2 has just declared
conditional on JA-GRID(a)'s **undischarged** u ≥ 0 proviso (§3 grade line,
re-grep hit 6). So the single sub-clause with an open inherited hypothesis is
also the single sub-clause with zero machine evidence, and both surfaces that
mention machine coverage say "all four". Compare the treatment PE1's G-3 got
(three vacuous JB-KEYEQ rows named as "VACUOUS, not confirmations"); the same
disclosure is owed here and is absent.

### F-4 — JUSTIFICATION GAP (quantifier / level bookkeeping in the r2 fence itself). §2(iii) fences (VAL), (GRID) and (RES) with ONE perimeter, but their J-A sources are stated at DIFFERENT levels; instantiating J-A's own level-indexed definition for (RES) gives the BYTE-EQUAL CHAIN THROUGH q, the condition r2 just separated off

§2(iii) (L421–430):

> This clause is asserted ONLY on the SHARED-KEY PERIMETER of §1: levels q with
> Φ_j^har = φ_{j+1}^cls byte-for-byte **for all j < q**, i.e. q ≤ qcap :=
> min(n, shared_upto + 1) … For the common digit list (A_i): (VAL) … (GRID) …
> (RES) at read level m := q+1 ≥ 2 …

J-A's perimeter is **level-indexed** (`GRTJA_PROOF` L69–70): "Shared-key
perimeter at level m: Φ_q = φ_{q+1} byte-for-byte for all q ≤ m−1 (all
operators at level m consume only keys that deep)". Instantiate it at each
layer's own level:

* (VAL) is JA-VAL **at level q** (`w_q(A_i) = v_{q+1}(A_i)`) ⟹ needs
  `Φ_j = φ_{j+1}` for `j ≤ q−1`, i.e. `j < q`. **Matches the note's fence.**
* (RES) is JA-RES **at level m = q+1** (the note says so, and JA-RES develops
  its argument by `Φ_{m−1} = Φ_q`) ⟹ needs `Φ_j = φ_{j+1}` for `j ≤ m−1 = q`,
  i.e. **through j = q** — which is r2's own second name, the BYTE-EQUAL CHAIN
  THROUGH q, reserved in §1 for JB-DEV(ii)'s byte clause.

At the top level `q = qcap = shared_upto + 1` the two conditions differ exactly
(that is the whole content of G2-6), and there `Φ_q = φ_{q+1}^cls` **fails by
definition of `shared_upto`**. So the (RES) layer is asserted at one level per
tower beyond the hypothesis of the theorem it cites, unless the representative
pin `φ_{q+1} := Φ_q^har` is taken to discharge J-A's `j = q` requirement — a
reading the note nowhere states and which, if adopted, would also weaken what
(VAL)'s fence is doing. §1's r2 block asserts the opposite:

> **Every r1/r2 restatement (§2(iii), the JB-VTX theorem and grade line,
> JB-BOX-2, §7.2, §7.3) now cites the SHARED-KEY PERIMETER in this second
> sense, `j < q`, 0 ≤ q ≤ qcap, and no statement cites §1 for the through-q
> condition except JB-DEV(ii)'s byte clause, which means the first.**

No machine leg can catch this: the runner checks (VAL) over `range(0, qcap+1)`
and checks the (RES) layer **nowhere**. Classification: gap, not critical —
nothing inside §3–§5 consumes (RES) (JB-VTX consumes JA-VAL and JA-GRID; §4
consumes JA-VAL; §5 consumes (VD-m) as a hypothesis), so the logical chain of
the note is unaffected; what is over-supplied is JB-DEV(iii)'s (RES) layer as
handed to a downstream unit through §7.3's W-3 bullet.

### F-5 — JUSTIFICATION GAP (the applied instance is outside the lemma's stated quantifier). LEMMA JB-EPS is quantified over the level-m WEIGHT LATTICE; THEOREM JB-CREAD applies it at V′ = γ_{m+1}, whose lattice membership is never established — the [RMG] clause that would give it is dropped from §5's "verbatim" box

LEMMA JB-EPS (L752–755):

> For every m ≥ 1 and V, V′ ≥ 0 **in the level-m weight lattice**, with
> t_m(β) = (ℓ_{m−1}β − s_m^wt(β))/e_{m−1} … and ε′ := ⌊(s_m^wt(V) +
> s_m^wt(V′))/e_{m−1}⌋ …

THEOREM JB-CREAD's display applies it at `(V, V′) = (λ, γ_{m+1})`:

>            = [ε_m(λ+γ_{m+1}) ε_m(λ)^{−1} ε_m(γ_{m+1})^{−1}] · z_m^{ε′} · c_m · ε_m(λ)·v
>            = z_m^{−ε′} · z_m^{ε′} · c_m · ρ_m(f)            [JB-EPS]

`λ = w_m(f)` is a level-m weight by construction. `γ_{m+1}` is introduced in §1
as a *defined integer* (`γ_{m+1} := e_m w_mΦ_m + h_m` in the shared read data),
and nothing in the note says it lies in the level-m weight lattice. The fact
that would supply it is `w_m(Ĉ_m) = γ_{m+1}` — which is in [RMG]'s box
("Ĉ_m the canonical correction digit of WELL-DEF-(n)(ii) (deg < deg Φ_m,
**w_m = γ_{m+1}**, R_{m,γ_{m+1}}(Ĉ_m) = τ_m …)") and is **dropped** from §5's
own recital, which the note labels "the (RM-m) box verbatim":

> Setting: the (RM-m) box **verbatim** ([RMG] S0.2, ACCEPTED on its scope):
> level m, g_m = 1, Ĉ_m the canonical correction digit
> (R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m), f ≠ 0 with
> deg f < deg Φ_m …

(the same recital also drops `deg Ĉ_m < deg Φ_m`, which is one of the three
hypotheses [RMG]'s L-CANON needs to make "the canonical division" canonical).
The lemma is in fact TRUE for all `V, V′ ∈ ℤ_{≥0}` — its own proof uses only
`s^wt(β) ≡ ℓ_{m−1}β (mod e_{m−1})` and JA-GRID(c), and the runner's `jb_eps`
leg quantifies over `Vs = range(0, min(3*e*h + 5, 25))`, i.e. plain integers,
**not** lattice elements — so the substance is unharmed and the repair is one
word. But as literally written the citation is unlicensed, and the machine
bracket "[Machine: JB-EPS, integers + field elements, every roster level]" is
evidence for a statement the lemma does not make.

### F-6 — JUSTIFICATION GAP (two record/wording defects in the r2 text, each small, both in load-bearing sentences)

**(a) "equivalently" conflates J-A's SUFFICIENT print bound with u ≥ 0, at two
of the three sites that define the open obligation.** JB-BOX-2 (L904–905):

> A real discharge must derive u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0,
> **equivalently** V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) in J-A's own form, for EVERY V
> in the quantified window …

and §2(iii) (L291–292): "derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}), **equivalently**
V ≥ s_m^wt(V)·h_{m−1}". J-A presents the print bound as sufficient, not
equivalent ("the proviso holds at every consumption site **by** the print's own
hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})"), and `u ≥ 0 ⟺ V ≥ s·h` is the
genuine equivalence. The note gets this right at exactly one of the three sites
— §2(iii) L489–490, "derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) (**or directly**
V ≥ s_m^wt(V)·h_{m−1}, which is what u ≥ 0 says)" — so the three r2 statements
of the same obligation are mutually inconsistent, and two of them overstate what
a discharge must prove.

**(b) §7.4(C)'s "machine-established rather than argued" overstates by one
step.** The line reads: "the vacuity of the other 27 is **machine-established
rather than argued**". What `PW2-DEGEN` establishes mechanically is byte-identity
of the argument tuple (`fCh == fC`, `div_har == key`). The step from byte-identity
to vacuity is the purity of `pwalk`/`my_divmod`, which is argued (the r2 block
argues it: "both are pure deterministic functions of those arguments") and not
machine-checked. Small, but it is the sentence that states what leg (C) buys.

### F-7 — JUSTIFICATION GAP (undefined symbol, PE1/G-7 genre, unfixed). `P_i` is used undefined in §4 and in §7.4, and it is load-bearing for JB-TREE(ii)'s digit-list claim

§4(ii) (L650–654):

> The identity (ID-(i+1)): Φ_i^{**P_i**} = Φ_{i+1} − Σ_{k<g_i} C_k^{(i)}·Φ_i^{e_ik}
> IS the statement that the φ_{i+1}-adic development of the KEY φ_{i+2} = Φ_{i+1}
> has digit list {C_k^{(i)} at abscissa e_i·k (k < g_i), 1 at abscissa **P_i**}

and §7.4's PW-ID / PW-WALK rows use `P_i` and `P_l` ("digit 1 at abscissa P_i",
"every R-leaf reduced (j_l ≤ P_l − 1)"). `P_i` appears nowhere else in the note
and is never defined; it is `e_i·g_i`, defined in [RMG] S0.1 as an abbreviation
explicitly scoped **"local to this note"** ("P_l := e_lg_l (the level-(l+1)
period)"), and J-B's header consumption list cites [RMG] S0.2/S2.1/S2.2/S3.2/S4
but **not** S0.1. The value matters: the proof of (ii) needs `e_i·k < P_i` for
all `k < g_i`, which is exactly `P_i = e_i g_i`. r1's G-7 fixed three such
symbols (`m_{q+1}^GMN`, `(B-READ)`, `s_m(·)`) at first use; this is the fourth,
in the same genre, in a clause whose proof depends on the definition.

---

## §8. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **The four PE1 re-derivations still stand in the post-r2 text**, and I redid
  the two hardest independently: JB-EPS's integer telescope (only ℤ-linearity of
  `ℓ_{m−1}·(·)` + JA-GRID(c), whose own two-line proof I re-derived: three
  `s`-values in `[0,e)` congruent mod `e`) and the ε-cancellation, whose `ε′` I
  matched **verbatim** against [RMG] S0.2's box (`ε′ := ⌊(s_m(λ) +
  s_m(γ_{m+1}))/e_{m−1}⌋`) and against the runner's `ep = (s_geo(lam,e,h) +
  s_geo(gam1,e,h))//e`.
* **No §2–§5 identity moved in r2.** `git diff 46f9452 888e293 --
  lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` has **48 deleted lines and
  every one of them is a fence, grade, box, record or verdict line** (I read all
  48): not one displayed equation of JB-DEV, JB-AFF, JB-VTX, JB-TREE, JB-EPS or
  JB-CREAD is touched, and every deletion is a strike-and-replace with the r0/r1
  text retained struck. The note's claim "No §2–§5 identity moves in this round
  either" is accurate. (The same holds for r1, as PE2 found.)
* **JB-VTX(e)'s r1/G-4 subject correction is right** and is consistently applied
  at three sites (§3(e), the §3 proof line, §7.2's JB-VTX row).
* **JB-CREAD's degenerate branch is honest as a scope statement** (v = 0 not
  claimed, read-at-target only), and `R ≠ 0` is *derived* rather than assumed
  (§3.3 row 10). I note that the branch is machine-**unexercised** (v = 0
  census 0, R = 0 census 0), so §5's "(checking ρ_m(f) = 0 on them, which does
  hold)" is true on zero rows; §7.1 discloses both zeros in the same paragraph,
  so I record this as disclosed-vacuity rather than a finding.
* **G2-2's disclosure is exemplary and mechanically correct** — the 27/45 split,
  the 9 rows, the gate mechanism (`chain_eq` forcing the divisor), and the
  "dropped where it should have negated" post-mortem all check against the code
  and the JSON.
* **G2-3's restatement is exact** (8 byteeq-false rows, 4+4, 12+8 walks) and the
  "STILL PRINT-UNCHECKED" enumeration is complete.
* **G2-7's decompositions are exact** (§6) and are now used consistently.
* **The (B-READ) step is sound under either reading** of L-CELL(ii)'s
  hypothesis direction (as PE2 also found), so the `w_m(R) ≤ λ + γ_{m+1}` half
  does not turn on resolving it.
* **The seal record is accurate at HEAD**: sealed runner md5 unchanged across
  seal → verdict → r1 → r2 → HEAD; the G-8 erratum's two halves both check; both
  r1 instruments byte-untouched by r2; walker2's own two-commit mini-seal holds.
* **Acceptance-counter honesty**: "attempt grade, acceptance counter 0/2, TWO
  hostile passes RUN and TWO repair rounds applied … A repair round is NOT a
  pass" is consistent at the S-status line, the r1 block's tail, the r2 block's
  tail, JB-BOX-6, §7.3's CONSUMES line and the sign-off. The r1 block's
  now-superseded "next acceptance attempt" sentence is struck in place and
  re-pointed at JB-PE3. No gate claim, no gr/carrier claim, no density claim.
* **`I4C` as the scope fence from both sides** and the walker's `print_elig`
  agreeing with `elig_ms` (off-perimeter counter 0) — reconfirmed.
* **`JB-TREE-OFFPERIM` = 0**, so the runner's `m > qcap` cut removed nothing on
  this roster (§3.4).

---

## §9. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **F-1** — one clause each into §7.2's JB-VTX row and §7.3's W-3 bullet:
   JB-VTX(d)'s grid/abscissa content rides JA-GRID(a)'s undischarged u ≥ 0
   proviso (JB-BOX-2 already says it).
1b. **F-1B** — carry hit 7's fence into the grade cap's JB-TREE sentence and into
   JB-BOX-2's perimeter enumeration ("… and JB-TREE(iii)/(iv) at m ≤ qcap"), and
   correct the r2 block's "The grade cap … and JB-BOX-2 were already consistent"
   to record that hit 7 made them inconsistent. Given that this is the third and
   fourth recurrence of the same body-vs-surface divergence in one arc, the
   durable fix is a rule (**every fence added to any body grade line is added in
   the same edit to the corresponding grade-cap sentence, §7.2 row and §7.3
   bullet, and to JB-BOX-2's enumeration**) rather than a fifth sweep.
2. **F-2** — restate JB-DEV's machine bracket and §7.1 row to what the code
   establishes: `fresh_dev` vs `PolyO.dev` (one genuine second implementation)
   plus the (VAL) digit-weight tie `vgen(q+1) == wlev(q)` (the genuine
   cross-engine content); and say that the `G.P.dev` leg is the same
   `PolyO.dev` on byte-equal arguments behind a guard that already forced
   agreement — i.e. carries no information — or drop it.
3. **F-3** — "three of clause (d)'s four ties", and name (d4) (attained
   abscissas = read grid, read assembled from on-line digits) as machine-unkeyed,
   noting that it is also the sub-clause carrying the open u ≥ 0 proviso.
4. **F-4** — either fence (RES) separately on the BYTE-EQUAL CHAIN THROUGH q
   (J-A's perimeter at level m = q+1), or state and justify that the
   representative pin `φ_{q+1} := Φ_q^har` discharges J-A's `j = q` requirement
   for JA-RES; and correct §1's "no statement cites §1 for the through-q
   condition except JB-DEV(ii)'s byte clause".
5. **F-5** — widen JB-EPS's quantifier to `V, V′ ∈ ℤ_{≥0}` (its proof and its
   machine leg already establish that), or restore [RMG]'s `w_m(Ĉ_m) = γ_{m+1}`
   to §5's box recital and cite it at the JB-EPS step; and stop calling the
   abbreviated recital "verbatim" (it also drops `deg Ĉ_m < deg Φ_m`).
6. **F-6** — make the three statements of the u ≥ 0 obligation agree ("or
   directly", not "equivalently"); and soften §7.4(C) to "the byte-identity of
   the argument tuple is machine-certified; the vacuity follows from purity".
7. **F-7** — define `P_i := e_i·g_i` at first use in §4 (or add [RMG] S0.1 to
   the header consumption list).

---

## §10. Divergences from PE1 and PE2 (both read before this pass, judged independently)

* **PE1's F1 stays CURED** (I re-grepped all 22 sites; no regression, no new
  site) and **PE2's G2-4 is discharged with a stronger witness than PE2 had** —
  PE2 argued from `(e₀, g₀)`; the roster in fact gives T3D/T3E the same `ψ₀`,
  the same `A_1 = 2` and the same `ord(z₁) = 3` (§4). r2 states the stronger
  form and it is exactly right.
* **PE2's G2-6 is not merely fixed but fixed the SOURCE-CORRECT way** — a check
  PE2 did not run (it never opened J-A's §1). §3.1.
* **PE2's G2-1 recurs twice, as F-1 and F-1B** — once for the proviso (missing at
  §7.2's JB-VTX row and §7.3's polygon half) and once for the perimeter fence r2
  itself introduced (missing at the grade cap and at JB-BOX-2, both of which r2
  declares "already consistent"). Both survived r2's own mandated re-grep. This
  is the disease's third and fourth appearance in this note's arc
  (PE1/G-9 → PE2/G2-1 → PE3/F-1 + F-1B); a repair should adopt a mechanical rule
  rather than run a fifth sweep (§9 item 1b).
* **The re-grep's own accounting is worth auditing next round.** r2 claims "8
  grade-surface hits inconsistent with the r1/r2 body fences, all 8 fixed"; the
  eight it lists are real and are fixed, but the sweep did not close the surface
  set (F-1, F-1B), so the "all 8" is a count of hits found, not of surfaces made
  consistent — a distinction the note's wording does not make.
* **PE1's G-1 recurs as F-2**, at a second site r1 never audited. PE1 found the
  disease at `jb_tree`; PE2 found it at the r1 walker's leg B; it is also at
  `jb_dev`, and there it is not merely uninformative but unreachable.
* **New in this pass** (neither PE1 nor PE2 raised them): F-2, F-3, F-4, F-5,
  F-6, F-7, and F-1's specific two surfaces.
* **PE2's "small=True changes pool CONTENT" note** is correctly recorded in r2's
  "findings NOT requiring an edit" list; I confirm the counts the note quotes
  are unaffected.

---

## §11. Pass hygiene

Nothing was edited. The sealed runner, both r1 instruments, walker2, all
committed artifacts and the note are byte-untouched; the four re-runs regenerate
`grt_jb_checks_results.json`, `grt_jb_printwalk_results.json` and
`grt_jb_printwalk2_results.json` with **zero diff** (`git diff verification/` is
empty after the pass). Only `verification/openmath/__pycache__` was written by
the interpreter, and my own probes were written to `/tmp`. `git add` was scoped
to this report file alone; the GRTJC PE1 verifier's in-flight
`GRTJC_passPE1_report.md` was never read, touched or staged.

No leg is NOT-RUN. (The Bash tool was intermittently refused on the
model-availability path during this pass; every leg was retried and completed,
and all four scripts ran to exit 0.)

— GRTJB-PE3, Fable, fresh context, 2026-08-05. This pass returns findings, so it
is **not** a clean pass: the acceptance counter for the note remains **0/2**, and
the first acceptance attempt has not landed.
