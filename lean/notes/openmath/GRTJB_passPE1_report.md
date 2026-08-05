# GRTJB-PE1 — hostile verification pass on the J-B tree-junction note

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` (J-B COMPOSER; the
tree-junction composition of the GRT weld: JB-DEV / JB-AFF / JB-VTX / JB-TREE /
JB-EPS / JB-CREAD + six honest boxes).
**Runner:** `verification/openmath/grt_jb_checks.py` (sealed at 7f6759d).
**Commits confirmed from `git log`:** 17adb80 (skeleton) · 5a72b62 (note composed) ·
7f6759d (SEAL commit 1: runner, 990 lines added) · f5578d0 (VERDICT commit 2: §7
records appended).
**Verifier:** Fable, fresh context, read-only. Fixes NOTHING. Genre: quote-and-classify
(CRITICAL ERROR = breaks the logical chain; JUSTIFICATION GAP = assume and continue).
Pass date 2026-08-05 (wallclock). This is the SECOND attempt at PE1 — the first died
in an API outage (partial archived at `GRTJB_passPE1_PARTIAL_outage_2026-08-05.md`);
this pass formed its judgment independently and cross-checks the partial only in §5.

---

## §0. VERDICT

**1 CRITICAL, 9 JUSTIFICATION GAPS.**

    GRTJB-PE1 FINDINGS: 1 critical, 9 gaps / VERDICT: NOT CLEAN

**F1 (CRITICAL, grade-surface):** the note claims (VD-m) is "unconditional for
m ≤ 2" at four sites, conflating J-A's PER-SLOT law JA-RES (which IS
unconditional at m = 2) with the EVALUATED dictionary (VD-2) (which J-A
supplies only through JA-VDIND's character-collapse hypothesis). **The note's
own sealed runner refutes it: 10 of its 13 roster boundary rows are
machine-evaluated FALSE instances of (VD-2)** on T3A/T3B/T3C/T3D — and §7.1
attributes that census to "exactly the JA-BOX-2/(VD-m)-proviso geography",
which is the m ≥ 3 box. THEOREM JB-CREAD itself survives (it is
hypothesis-guarded and its algebra is correct); what fails is the advertised
perimeter, i.e. exactly what downstream units consume. After correction
JB-CREAD has no unconditional stratum above m = 1.

Gaps, most-severe first: **G-1** the tree's "harness AND print keys" is one
division computed twice · **G-2** "22 samples across 7 towers" → 14 towers ·
**G-3** "q = 1 byte-equal on all 25 rows" → 22 rows, 3 vacuous · **G-4**
JB-VTX(e)'s subject is Φ_{q+1}^har, not the theorem's f (false as literally
read) · **G-5** JA-GRID(a)'s u ≥ 0 proviso is carried by no box · **G-6**
JB-KEYEQ cannot reproduce the probe's F1 pattern "row-for-row" (it walks 12 of
30 F1 junctions; the 16 top junctions carry 12 of the 18 REDs) · **G-7** three
undefined/overloaded symbols ((B-READ), m_{q+1}^GMN, s_m(·)) · **G-8** two
attribution/record slips ("GD-2's T-F check"; the seal commit message) ·
**G-9** JB-VTX/JB-DEV(iii) quantify over 0 ≤ q ≤ n while their proofs need
shared keys below q.

The four load-bearing derivations I was charged to attack all SURVIVE re-derivation:

* **LEMMA JB-EPS (the ε-carry collapse) is CORRECT**, line by line, and its two
  ingredients check out against their sources: the integer telescope needs only
  linearity of ℓ_{m−1}·(·) plus J-A's JA-GRID(c) carry clause (graded there PROVED,
  unconditional), and the field form needs ε_m = z_m^{−t_m}, which is JA-EPS's
  displayed content AND is what the committed engine computes (verified against
  `iterlawn_pe_reimpl.eps`, see §2.2).
* **THEOREM JB-CREAD's algebra is CORRECT**: every one of the five displayed lines
  is a legitimate substitution, and the ε′ in the cancelling pair is literally the
  same integer as [RMG] (C-READ)'s ε′ (verbatim source check, §2.3).
* **The JB-VTX shear is DERIVED, not asserted** (§2.4), including the slope law,
  the realized-side-goes-horizontal clause and the principal-part correspondence.
* **The machine leg reproduces BIT-IDENTICALLY** (§1): exit 0, 18/18 families
  GREEN, 6,700 samples, 0 violations, censuses 104/21/0/0/0 — the re-run JSON
  differs from the committed artifact in ONE byte-level field (`elapsed_s`
  0.7 → 0.8), i.e. the sealed numbers are real.

The findings are machine-claim inflation and record/notation defects, not
mathematics. They are listed most-severe-first in §3.

---

## §1. MACHINE LEG (mandatory; RUN)

Command (from `verification/openmath/`, python3, no arguments — the note's own
runner, unedited):

    python3 grt_jb_checks.py      →  EXIT 0

Re-run summary vs the note's §7.1 quoted figures:

| quantity | note §7.1 | re-run | match |
|---|---|---|---|
| families GREEN | 18/18 | 18/18 | YES |
| total violations | 0 | 0 | YES |
| total samples | 6,700 | 6,700 | YES |
| JB-DEV / JB-SHEAR / JB-VTX | 893 / 893 / 893 | 893 / 893 / 893 | YES |
| JB-KEYEQ | 25 | 25 | YES |
| JB-ID / JB-LINE | 34 / 194 | 34 / 194 | YES |
| JB-TREE | 79 | 79 | YES |
| JB-EPS / JB-CM / JB-CREAD | 955 / 28 / 79 | 955 / 28 / 79 | YES |
| JB-QO / JB-D0 | 5 / 4 | 5 / 4 | YES |
| TW-JB | 2,480 | 2,480 | YES |
| teeth MJB-DEV/VTX/TREE/CREAD | 3/3/3/3 caught | 3/3/3/3, 0 viol | YES |
| censuses scored / boundary / v=0 / R=0 / off-perimeter | 104 / 21 / 0 / 0 / 0 | 104 / 21 / 0 / 0 / 0 | YES |
| elapsed | 0.7 s | 0.8 s | timing only |

`git diff` of the runner-written `grt_jb_checks_results.json` after the re-run:
ONE changed line, `"elapsed_s": 0.7` → `"elapsed_s": 0.8`. Everything else —
every family count, every violation list, every per-tower census, the byte
census — is byte-identical to the committed artifact (whose md5 is
0dc4b015ac520d2bb05094329d7754ba). I restored the committed JSON afterwards
(`git checkout --`, md5 re-verified), so this pass leaves the repo unchanged
except for this report; the note and the runner were never edited.

The tee'd `grt_jb_checks_output.txt` in the tree also matches the re-run
line-for-line (modulo the same elapsed timings).

### 1.1 Two-commit seal — VERIFIED

* `7f6759d` ("GRTJB SEAL (commit 1 of 2)") PRECEDES `f5578d0`
  ("GRTJB VERDICT (commit 2 of 2)") in `git log`. ✓
* Runner md5 at seal = at verdict = at HEAD:
  `55f4911eaddd8524fd91368b30ed71bd`. The runner was NOT touched between the
  seal and the verdict. ✓
* `git diff 7f6759d f5578d0 -- <the note>` touches ONLY §7.1: the
  `[VERDICT APPENDED AT COMMIT 2]` placeholder + the sealed-prediction list is
  replaced by the results table and the census paragraph. **No §1–§6 law
  statement, box, or grade moved between seal and verdict** — the substantive
  seal property. ✓
* The seal commit's stat shows the runner only (990 insertions); the note itself
  was committed one commit earlier at 5a72b62 with the predictions written in
  prose ("Sealed predictions (commit 1): EXT-GATE 0 · JB-DEV 0 · …"), so the
  predictions were on record before the battery. ✓ (Minor record wording issue:
  the seal commit message says "note + runner sealed" while that commit contains
  only the runner — see finding G-8.)

### 1.2 Derived §7.1 figures recomputed from the committed JSON

Every derived census figure in §7.1 was recomputed by summing the per-row
`cread` block of `grt_jb_checks_results.json` (25 non-chamber rows + 16 `/tw`
chamber rows):

| §7.1 claim | recomputed | verdict |
|---|---|---|
| "scored 104 (66 roster + 38 chamber)" | non-chamber 66, chamber 38, total 104 | **EXACT** |
| "boundary 21" | non-chamber 13 + chamber 8 = 21 | **EXACT** |
| boundary "ALL on … T3A, T3B, T3C, T3D, I4B and their transported chambers" | boundary-positive rows = T3A 3, T3B 3, T3C 1, T3D 3, I4B 3, T3A/tw 2, T3B/tw 2, T3D/tw 2, I4B/tw 2 — a subset of the claimed set | **TRUE** |
| "v = 0 stratum: 0 occurrences; R = 0: 0; off-perimeter tree rows: 0" | 0 / 0 / 0 | **EXACT** |
| "79 walks (125 with chambers)" | trees: non-chamber 79, chamber 46, total 125 | **EXACT** |
| "22 scored samples with z_m^{ε′} ≠ 1" | teeth: non-chamber 15 + chamber 7 = 22 | **EXACT** |
| "…across 7 towers" | teeth-positive rows = 21 (14 base + 7 chamber); distinct TOWERS = 14 (T2A, T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F, I4B, JD3A, JD3C, JD5A) | **FALSE — finding G-2** |
| "(28 eligible (T, m) rows)" for JB-CM | 28 non-chamber jb_cm calls | **EXACT** |
| "q = 1 byte-equal on all 25 rows" (JB-KEYEQ) | 22 of the 25 rows carry a q = 1 entry, all `true`; 3 rows (QO:x3-3/Q3, QO:x4+2x2+2/Q2, QO:x4-2/Q2) have an EMPTY census — T.n = 0, no junction walked, TH-BASE not exercised | **OVERSTATED — finding G-3** |

Eight of the ten derived figures reproduce exactly; one is a coverage
overstatement; one ("across 7 towers") is wrong.

### 1.3 EXTRA MACHINE LEG (this pass's own, decorrelating instrument)

The note's boundary census (21 rows) is disclosed as a count with a tower list
but WITHOUT the level m at which each boundary row sits, and without saying
whether "boundary" means "(VD-m) evaluated FALSE" or "the print-side evaluator
asserted out". Both matter for the note's grade claims, so I re-ran
`grt_jb_checks`'s own `vd_eval` / `elig_ms` / `chat_of` / `fresh_divmod` on the
16-tower roster from a separate script (`/tmp/jbpe1_probe.py`, read-only,
imports the sealed runner; the runner is untouched) and split the boundary
rows by (level, reason):

    BOUNDARY  m=2  R: (VD-m) EVALUATED FALSE          7
    BOUNDARY  m=2  f: (VD-m) EVALUATED FALSE          3
    BOUNDARY  m=3  R: (VD-m) EVALUATED FALSE          3
    SCORED    m=1  law ok                            45
    SCORED    m=2  law ok                             8
    SCORED    m=3  law ok                             3

Per tower: **T3A m=2 (2×R, 1×f), T3B m=2 (3×R), T3C m=2 (1×f), T3D m=2
(2×R, 1×f), I4B m=3 (3×R)**. Not one boundary row is an evaluator scope-out:
every one is a genuine machine-evaluated FALSE of (VD-m), and **10 of the 13
roster boundary rows sit at m = 2** — inside the stratum the note calls
unconditional. This is finding **F1** (§3).

The four towers carrying the m = 2 failures are exactly the ones with a
visible level-1 character: T3A (e = 2,2,2 / h = 1,1,1 / d₀ = 2), T3B
(e = 3,2,2), T3C (e = 2,3,2 / h = 1,2,1), T3D (F₂[[t]], e = 2,2,2, g₀ = 2);
the two T3 rows that score 6/6 are T3E (e₁ = 1, flat middle) and T3F
(e₀ = 1) — i.e. precisely where A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses,
which is J-A's own JA-VDIND boundary. So the failure pattern is not noise: it
is the mechanism J-A displays and J-B's grade line contradicts.

---

## §2. The four charged re-derivations

### 2.1 JB-TREE's "harness AND print keys" — ONE reading, printed twice (charge item 1)

The note's §4 machine bracket claims three distinct tree checks, the second being

> "(2) the canonical division by the harness key AND by the print-side key
> where byte-equal"

and §7.1's table row drops the fence entirely: "fresh tree walk == canonical
division, harness AND print keys". The runner (`jb_tree`, lines 476–503):

    byteeq = (tuple(G.phi[m + 1]) == Phim)
    ...
    Qf, Rf = fresh_divmod(T.R, fC, Phim)
    if R0 != Rf or Qp != Qf: viol(... 'tree != canonical division (harness key)')
    if byteeq:
        Qg, Rg = fresh_divmod(T.R, fC, tuple(G.phi[m + 1]))
        if R0 != Rg or Qp != Qg: viol(... 'tree != print-key division')

The print-key leg fires ONLY under `byteeq`, i.e. only when
`tuple(G.phi[m+1]) == Phim` as Python tuples. `fresh_divmod` is a pure function
of `(R, fC, key)`; called twice on equal arguments it returns the identical
pair. So the second test is not an independent check of anything — it is the
first test re-executed on the same inputs, and it CANNOT fail unless the first
does. Off the byte-equal set (where the print key genuinely differs — 18 of
the probe's 30 F1 junctions) the tree-vs-print-key correspondence is not
machine-checked at all.

The mathematics is untouched: THEOREM JB-TREE is stated at the representative
φ_{m+1} := Φ_m^har, so a print-key division statement at a DIFFERENT key is
not claimed (and JB-DEV(iv) fences it explicitly). The defect is purely one of
machine-evidence advertising: two key families are reported where one
computation ran. Finding **G-1**.

For contrast, the runner's genuinely decorrelated legs in the same section are
real: `fresh_divmod`/`fresh_dev` are the runner's own schoolbook division (not
`PolyO.dev`), `lnorm_split` re-derives L-NORM with an in-code exactness
assertion, the E1-priority walk is re-implemented from the [RMG] text, and the
signed reassembly f·Ĉ_m = R₀ + Q·Φ_m is checked before the divmod comparison.
JB-TREE(i)'s substance is machine-supported; only its second key family is
empty.

### 2.2 LEMMA JB-EPS, line by line — CORRECT (charge item 2)

Statement checked as displayed (note §5): with t_m(β) := (ℓ_{m−1}β −
s_m(β))/e_{m−1} and ε′ := ⌊(s_m(V) + s_m(V′))/e_{m−1}⌋,

    t_m(V + V′) − t_m(V) − t_m(V′) = ε′,
    ε_m(V+V′)·ε_m(V)^{−1}·ε_m(V′)^{−1} = z_m^{−ε′}.

Line 1 (the telescope). Numerator of the left side =
[ℓ(V+V′) − s(V+V′)] − [ℓV − s(V)] − [ℓV′ − s(V′)]. The ℓ-terms cancel
identically because ℓ_{m−1}·(·) is ℤ-linear — this is the only property of ℓ
used, and it is available (ℓ is an integer). Remainder =
s(V) + s(V′) − s(V+V′). ✓ as the note displays it.

Line 2 (the carry clause). The note asserts s(V) + s(V′) − s(V+V′) = e_{m−1}ε′
"by the carry clause (JA-GRID(c) = (C-EPS))". J-A §3.3(c) verbatim: "for
V, V′ ≥ 0, s(V) + s(V′) − s(V + V′) = e·δ, δ ∈ {0, 1}, δ = 1 ⟺
s(V) + s(V′) ≥ e", proof "s(V+V′) ≡ ℓ(V+V′) ≡ s(V) + s(V′) (mod e) and all
three lie in [0, e)", graded there **PROVED, unconditional**. Since all three
s-values lie in [0, e), δ = ⌊(s(V)+s(V′))/e⌋ = ε′ identically. ✓ The
citation is exact and the cited clause is the unconditional one (J-A's (a) has
a u ≥ 0 proviso; (c) has none — the note cites (c) only). Division by e_{m−1}
is legitimate: t_m(β) ∈ ℤ because s(β) = ℓβ mod e.

Line 3 (the field form). The note says "the field form is JA-EPS (ε = z^{−t})".
J-A §3.2's proof line: "the ε-exponent ℓ′s − ℓu′ = −t_m(β)", so
ε_m(β) = z_m^{−t_m(β)}. Substituting into line 1 gives z_m^{−ε′}. ✓
INDEPENDENT CHECK against the committed engine: `iterlawn_pe_reimpl.eps`
computes `expo = lp[m−1]*s − l[m−1]*u` with `(s, u) = eq12(β, e, h)`; with
u = (β − sh)/e and ℓ′ = (1 − ℓh)/e one gets ℓβ − s = e(ℓu − ℓ′s), i.e.
t_m(β) = −expo, so the engine's ε is exactly z_m^{−t_m}. The note's
convention and the engine agree — there is no sign slip.

Also verified: the runner's `s_geo(V, e, h)` (smallest x ∈ [0,e) with
(V − xh) ≡ 0 mod e) equals `eq12`'s s = (ℓV) mod e, so JB-EPS's integer leg
is checked with a genuinely ℓ-free geometric implementation, and the runner
re-derives the carry clause itself (`if s1 + s2 - s3 != e*ep`) instead of
assuming it. Both halves (955 samples) green.

**Verdict: JB-EPS is PROVED as displayed, unconditional as claimed.** Its only
non-elementary input is JA-GRID(c), itself unconditional and re-derived by the
runner; grading JB-EPS "PROVED, unconditional" is honest.

### 2.3 THEOREM JB-CREAD's algebra — CORRECT under its hypotheses (charge item 2 cont.)

Chain re-derived left to right, with each step's warrant:

| step | note's line | warrant | ✓ |
|---|---|---|---|
| 1 | ρ_m(R) = ε_m(λ+γ_{m+1})·R_{m,λ+γ_{m+1}}(R) | (VD-m) at R **plus** w_m(R) = λ+γ_{m+1} | ✓ |
| 2 | = ε_m(λ+γ)·z_m^{ε′}·v·τ_m | [RMG] (C-READ) verbatim | ✓ |
| 3 | = ε_m(λ+γ)·z_m^{ε′}·v·ε_m(γ)^{−1}·c_m | (RM-m) box's τ_m = ε_m(γ_{m+1})^{−1}c_m | ✓ |
| 4 | = [ε(λ+γ)ε(λ)^{−1}ε(γ)^{−1}]·z^{ε′}·c_m·ε(λ)v | regrouping in the field K_m (commutative; ε's are units) | ✓ |
| 5 | = z^{−ε′}·z^{ε′}·c_m·ρ_m(f) | JB-EPS at (V, V′) = (λ, γ_{m+1}) + (VD-m) at f | ✓ |
| 6 | = c_m·ρ_m(f) | — | ✓ |

The ε′ MATCH is the step a hostile reader must not take on trust, so I pulled
[RMG] S0.2's box verbatim (`RMENGINE_2026-08-08.md` lines 317–318):

>   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m,
>   ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋  [the level-m EPS-carry].

That is literally JB-EPS's ε′ at (V, V′) = (λ, γ_{m+1}) — same floor, same
divisor, same two arguments. **The cancellation is real, not a coincidence of
notation.** The runner independently recomputes `ep = (s_geo(lam,e,h) +
s_geo(gam1,e,h))//e` from fresh integers.

The w_m(R) pin (step 1's second input) is also derived, not assumed:
R_{m,λ+γ}(R) = z^{ε′}vτ_m ≠ 0 forces some cell of R on-line on-grid at
λ+γ_{m+1}, hence w_m(R) ≤ λ+γ_{m+1}; with (C-W_R)'s "w_m(R) ≥ λ + γ_{m+1}"
(box verbatim, line 315) this is equality. ✓ The nonvanishing needs v ≠ 0
(hypothesis) and τ_m ≠ 0; the note asserts "τ_m is a unit" without a citation,
but it is forced by the consumed class pin (J-A §1: "ψ_j monic irreducible,
ψ_j(0) ≠ 0"), since c_m = ψ_{m,0} and ε_m(γ)^{−1} is a unit — so this is a
missing one-word citation, not a gap. (The engine enforces it: `SpecTower`
rejects ψ candidates with `Kj.is_zero(trial[0])`.)

Two further checks on §5's setting:
* c_m = ψ_{m,0} = −z_{m+1}: with g_m = 1, WELL-DEF's lift gives
  Ĉ_m = C_0^{(m)} = realize_m(ε_m(γ_{m+1})^{−1}ψ_{m,0}, γ_{m+1}), so REALIZE R3
  gives R_{m,γ_{m+1}}(Ĉ_m) = ε_m(γ_{m+1})^{−1}ψ_{m,0}; comparing with the box's
  τ_m = ε_m(γ_{m+1})^{−1}c_m gives c_m = ψ_{m,0}, and ψ_m(y) = y + ψ_{m,0}
  with ψ_m(z_{m+1}) = 0 gives ψ_{m,0} = −z_{m+1}. ✓ (Machine JB-CM, 28 rows.
  Note this leg is a self-consistency check of the harness construction, not an
  independent confirmation — the note does not claim otherwise.)
* the v = 0 branch: correctly displayed as read-at-target only, with the
  reason given (R's own weight may sit strictly above λ+γ_{m+1}); the runner
  censuses it (0 occurrences on this roster, honestly reported as 0).

**Verdict: the theorem as stated — under (VD-m) at f and at R, and v ≠ 0 — is
PROVED, and the ε-carry collapse is exactly right.** What is NOT right is the
advertised size of the perimeter (F1).

### 2.4 The JB-VTX shear — DERIVED, not asserted (charge item 3)

(a) is a two-line computation, displayed in full and independently correct:
u_i = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1}) gives
e_q u_i + h_q i = e_q v_{q+1}(A_i) + i(e_q v_{q+1}(φ_{q+1}) + h_q), and the two
substitutions are named (JA-VAL for v_{q+1} = w_q; JA-PIN clause 7 for
γ_{q+1} = e_q w_qΦ_q + h_q). ✓ Nothing is asserted.

(c) the slope law "print slope σ over [i₀,i₁] ↦ sheared slope e_qσ + h_q over
the same [i₀,i₁]" follows from Σ_q's own formula in one line:
((e u₁ + h i₁) − (e u₀ + h i₀))/(i₁ − i₀) = e·σ + h. ✓ DERIVED. Its three
corollaries also check: the realized side σ = −h_q/e_q ↦ e_q(−h_q/e_q) + h_q =
0 ✓; principal part σ < 0 ↦ sheared slope < h_q since e_q > 0 ✓; abscissa runs
preserved because Σ_q is abscissa-preserving, so d = run/e is the same integer
in both frames ✓ (trivially true, and stated as such).

(b) is JB-AFF applied to Σ_q. LEMMA JB-AFF's own proof is correct: a > 0 gives
au + bi + c < au′ + bi + c ⟺ u < u′ at equal i, and hulls/faces/vertices are
defined by exactly that relation plus abscissa order. ✓ (The lemma is stated
for general (a, b, c) with a > 0 and applied at (e_q, h_q, 0).)

(d)'s four ties are the print's Lemma `shape` item 1 plus the weight recursion
one level up; the runner checks all four, and computes v_{q+1}(f) BOTH as
min u_i and through the vgen recursion — two developments, one value, so
`shape` item 1 is machine-keyed rather than only cited. ✓

The 41,720 / 7,472 figures in §1 check out against their source
(`O1thr_phaseB_verifybrief_rev3.md` §9 T-F: 41,720 site-instances, 0 violations
of WGEO/(M6c); 7,472 violations of the unsheared reading) and against the
blueprint's own two citations of them. The attribution "GD-2's T-F machine
check" is loose — T-F is the O1thr rev-3 runner, cited by GD-2/GD-3 — but the
numbers are not stale. Minor: finding **G-6**.

One real display defect in §3: clause (e) — see finding **G-4** (its subject is
Φ_{q+1}^har, not the theorem's quantified f, under which reading it would be
false).

### 2.5 The six-box fence inventory vs what the proofs actually consume (charge item 4)

Consumption sites walked one by one against §6:

| consumed conditionality | site in §2–§5 | covered by |
|---|---|---|
| [RMG] ACCEPTED + T-scope(m) + g_m = 1 + W-WIN unused | §4 setting, §4 grade | JB-BOX-4 ✓ |
| LED-Λ at ATTEMPT grade (λ_E face) | §4(iii) | JB-BOX-4 ✓ (+ the runner re-derives the quanta) |
| W-2 clause 1 (admissibility) / W2-C1a | §2(i), §3 preamble, §3(e) | JB-BOX-2 (via "W-2's (C-coll)/recursion split") — partially; the clause-1 perimeter itself is named inline in §2(i)/§3 ✓ |
| W-2 clause 2 byte law + (C-coll) | §2(ii) | JB-BOX-2 ✓ |
| W-2 clause 3 chamber | §4 setting, TW-JB | JB-BOX-2/§4 ✓ |
| W2-OPEN-1 | consumed nowhere — VERIFIED: W-2 §5.3 is the transported value/cocycle battery, and no §2–§5 statement touches K5/K6/K7/K12 | JB-BOX-2's "consumed NOWHERE" ✓ TRUE |
| J-A JA-BOX-1 (slot-independent c refuted) | §2(iii)(RES) inline | inline ✓ |
| J-A JA-BOX-2 ((VD-m) proviso) | §5 | JB-BOX-2 — but MIS-SCOPED to m ≥ 3, see F1 ✗ |
| J-A JA-BOX-3 (unpinned ℓ) | §2(iv), §6 | JB-BOX-2 ✓ |
| J-A JA-BOX-4 (equal characteristic, no PARI) | F_p[[t]] rows | JB-BOX-5 ✓ |
| J-A JA-BOX-5 (realized principal reads only) | §3(c) inline ("consumes only the principal sides") | inline ✓ |
| JA-GRID(a)'s u ≥ 0 proviso ([JA-r1] repair, NOT a JA box) | §2(iii)(GRID) | NOT covered — finding **G-5** |
| the v ≠ 0 stratum | §5 theorem + §6 | JB-BOX-2 ✓ |
| gr/carrier and density fences | §5 remark, §7.3 | JB-BOX-6 ✓ |
| cross-representative fence | §2(iv) | JB-BOX-3 ✓ |

So the inventory is thorough — two holes: the (VD-m) proviso is scoped to
m ≥ 3 when the machine shows it biting at m = 2 (F1, the critical one), and
one inherited J-A proviso that is not one of J-A's boxes rides in uncarried
(G-5).

---

## §3. FINDINGS

### F1 — CRITICAL. "(VD-m) unconditional at m ≤ 2" is FALSE, and the note's own sealed runner refutes it at 10 in-roster instances

**Offending passages (four sites, verbatim).**

§5, inside the theorem statement (lines 330–332):

> **THEOREM JB-CREAD.** Suppose (VD-m) (J-A §3.4's evaluated dictionary)
> holds at f and at R — **unconditional for m ≤ 2 (VD-1 = W2-L3; m = 2 by
> JA-RES)**, per-digit proviso / (R-coll) at m ≥ 3 (JA-BOX-2) —

Grade cap (lines 21–22):

> JB-CREAD (§5) is PROVED on the (VD-m) perimeter (**unconditional
> at m ≤ 2**; per-digit proviso / (R-coll) at m ≥ 3)

§7.2 claims table (line 481):

> | JB-CREAD | (C-READ) transport: ρ_m(R) = c_m·ρ_m(f), carry-free in print
> coordinates | PROVED on the (VD-m) perimeter ∩ {v ≠ 0} (**uncond. m ≤ 2**) |

JB-BOX-2 (lines 402–405):

> Every print-residual statement rides J-A's boxes verbatim: the
> (VD-m)/per-digit proviso **at m ≥ 3** (JA-BOX-2 — (R-coll) sufficient,
> converse unsealed)

**Why it is false.** (VD-m) and JA-RES are DIFFERENT statements. J-A §3.4:
JA-RES is the PER-SLOT law "c_i = z_{m−1}^{−i·A_{m−1}}·C_i", and J-A's
"**the law is UNCONDITIONAL at m = 2**" is about that per-slot law (its
proviso at m = 2 is (VD-1) = W2-L3). The EVALUATED dictionary (VD-m) —
"z_m^{τ_m(A)}·R_m(A)(z_m) = ε_m(β)·R_m v(A)" — is obtained from the per-slot
law only through COROLLARY JA-VDIND, which J-A states with an explicit extra
hypothesis:

> **COROLLARY JA-VDIND …** Under the per-slot law, (VD-m) holds for A IF the
> slot character is trivial ABSOLUTELY on A's attained abscissas:
> z_{m−1}^{i·A_{m−1}} = 1 for every attained i (sufficient: A_{m−1} = 0, i.e.
> e_{m−2} = 1; or ord(z_{m−1}) | A_{m−1} and the abscissa condition; NOT
> sufficient: single-slot support alone …). Conversely, when the absolute
> character is nontrivial on the attained set, the two sides of (VD-m) differ
> by z_{m−1}^{−s₀A}·(the ϑ-twisted packed sum vs the packed sum), which is
> generically nonzero

At m = 2 that condition is z_1^{i·A_1} = 1 on the attained abscissas, with
A_1 = ℓ₀g₀γ₁ — nontrivial precisely on the towers with e₀ ≥ 2 and a
nontrivial z₁. J-A never claims (VD-2) unconditional; J-B's parenthetical
"m = 2 by JA-RES" is the exact conflation JA-VDIND warns against.

**Machine counter-instances (the note's OWN runner, its OWN `vd_eval`).**
`vd_eval` is a faithful evaluator of (VD-m) (β = wlev, v = read, s₀ = the
print's initial attained abscissa, τ = (s₀ − ℓβ)/e, ρ = z^τ·R^cls(z),
holds ⟺ ρ = ε(β)·v). Splitting the 13 roster boundary rows by level and
reason (§1.3):

    T3A  m=2   (VD-2) EVALUATED FALSE at R (2 rows), at f (1 row)
    T3B  m=2   (VD-2) EVALUATED FALSE at R (3 rows)
    T3C  m=2   (VD-2) EVALUATED FALSE at f (1 row)
    T3D  m=2   (VD-2) EVALUATED FALSE at R (2 rows), at f (1 row)
    I4B  m=3   (VD-3) EVALUATED FALSE at R (3 rows)      ← the only JA-BOX-2 rows

Ten of thirteen are at **m = 2**, none is an evaluator scope-out, and the four
carrying towers are exactly the e₀ ≥ 2 character-visible ones (T3A e = 2,2,2;
T3B e = 3,2,2; T3C e = 2,3,2; T3D e = 2,2,2 over F₂[[t]]), while the two
level-flat T3 rows (T3E e₁ = 1, T3F e₀ = 1) score 6/6. The pattern IS
JA-VDIND's boundary.

**Consequential mis-attribution in the verdict text** (§7.1, lines 457–461):

> JB-CREAD **scored 104 (66 roster + 38 chamber), 0 violations; boundary 21 —
> ALL on the character-visible/interior-twist towers T3A, T3B, T3C, T3D,
> I4B and their transported chambers**, exactly the JA-BOX-2/(VD-m)-proviso
> geography

The tower list and the counts are right (§1.2), but the geography is NOT
JA-BOX-2's: JA-BOX-2 is the m ≥ 3 box, and 10 of the 13 roster boundary rows
(plus, by the same towers, the 8 chamber ones) sit at m = 2. The census the
note discloses is in fact the evidence against its own "uncond. m ≤ 2" line —
it was read as confirming the m ≥ 3 box instead.

**Scope of the damage (why CRITICAL and not a gap).** THEOREM JB-CREAD itself
survives untouched: it is hypothesis-guarded ("Suppose (VD-m) … holds at f and
at R"), its algebra is correct (§2.3), and on the 56 rows where the hypothesis
was machine-verified the law held with 0 violations. What is false is the
note's statement of WHERE the hypothesis is free — and that statement sits on
the note's grade surface (grade cap + claims table + box), which is exactly
what downstream units (the W-5 row; the J-C germ; the weld ledger) consume.
After the correction, JB-CREAD has **no unconditional stratum above m = 1**:
the honest perimeter is (VD-1) = W2-L3 at m = 1, and the JA-VDIND collapse
condition / (R-coll) at every m ≥ 2. A repair is a one-line rescope in four
places plus one sentence in §7.1; nothing in §2–§4 is affected, and the
(C-READ) transport itself is not in doubt.

### G-1 — JUSTIFICATION GAP. The tree's "harness AND print keys" is one division computed twice

§4 machine bracket: "(2) the canonical division by the harness key **AND by
the print-side key where byte-equal**"; §7.1 table row (fence dropped):
"fresh tree walk == canonical division, **harness AND print keys**". Under
`byteeq` the two `fresh_divmod` calls receive equal tuples, so the second
comparison is the first re-run — it cannot fail independently, and off the
byte-equal set (18 of the probe's 30 F1 junctions) no print-key tree check
runs at all. Evidence advertised as two key families is one. (Details §2.1.
The mathematics is fenced correctly by JB-DEV(iv)/JB-BOX-3; only the machine
claim is inflated.)

### G-2 — JUSTIFICATION GAP (record). "across 7 towers" is wrong: the 22 teeth samples span 14 towers

§7.1: "MJB-CREAD teeth material: **22 scored samples with z_m^{ε′} ≠ 1 across
7 towers** — the spurious-carry reading fails on every one". Recomputed from
the committed JSON: 22 is exact (15 base + 7 chamber), but the teeth-positive
rows are 21 (14 base rows + 7 chamber rows), spanning **14 distinct towers**
(T2A, T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F, I4B, JD3A, JD3C, JD5A).
"7" is the number of teeth-positive CHAMBER rows — and coincidentally the
size of the runner docstring's smoke-probe designation list ("MJB-CREAD
visible on T2A/T2D/T2G/T3A/T3D/T3E/I4B", which is exactly the 7 chamber rows).
This looks like a smoke-era figure carried into the full-run verdict. The
claim's substance (the ε-carry collapse is machine-load-bearing) is
unaffected and understated, not overstated.

### G-3 — JUSTIFICATION GAP (completeness over an enumeration). "q = 1 byte-equal on all 25 rows" is vacuous on 3 of the 25

§7.1 table: "JB-KEYEQ | byte census + TH-BASE (**q = 1 byte-equal on all 25
rows**) | 25". The committed byte census shows three rows with an EMPTY
census — `"QO:x3-3/Q3": {}`, `"QO:x4+2x2+2/Q2": {}`, `"QO:x4-2/Q2": {}` —
because those extracted towers have T.n = 0, so `for q in range(1, T.n + 1)`
walks nothing and the runner's TH-BASE guard (`if T.n >= 1 and not
cen.get(1, True)`) is not exercised. TH-BASE is confirmed on 22 rows, not 25.

### G-4 — JUSTIFICATION GAP (display). JB-VTX(e)'s subject is not the theorem's quantified f

THEOREM JB-VTX is quantified "f ∈ O[x] nonzero"; clause (e) then reads:

> **(e) [window clause].** Restricted to the junction window i ≤ e_q·g_q
> (the lift comparison window), one-sidedness holds in both frames
> simultaneously (Σ_q preserves sides): this is W2-C1a's polygon leg —
> v-correct, one-sided, support {0, e_q g_q} ∪ attained grid slots — i.e.
> the "window polygon" of the blueprint IS N_{q+1}(Φ_{q+1}^har) restricted
> to its single side, vertex-for-vertex under Σ_q.

Read with the theorem's f as subject, the first half is FALSE (a general f's
polygon restricted to i ≤ e_q g_q is not one-sided). The second half reveals
the intended subject, Φ_{q+1}^har, for which the clause is exactly W2-C1a
(quoted correctly, index shift included) plus JB-AFF. The clause needs
"applied at f = Φ_{q+1}^har" in its first sentence. No machine family covers
(e), so nothing else flags it.

### G-5 — JUSTIFICATION GAP (fence inventory). JA-GRID(a)'s u ≥ 0 proviso rides in uncarried

§2(iii) consumes the grid layer as

>     (GRID) the on-line attained abscissas lie on the print's T-side grid
>            s + j·e_q, and the plain carry = the side-lattice crossing
>            indicator                                  [JA-GRID/W2-L0, consumed]

J-A's JA-GRID(a) carries an explicit [JA-r1] repair proviso — "u := (V − s·h)/e
≥ 0 … (the bare V ∈ ℤ_{≥0} quantifier was **false** at small V)" — which is an
inline repair, not one of JA-BOX-1..5. JB-BOX-2's blanket ("rides J-A's boxes
verbatim") therefore does not carry it, and §2(iii) does not restate it. J-A
argues the proviso holds at every consumption site by the print's own
hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}); J-B should either restate that
argument at its own site or name the proviso in JB-BOX-2. (JB-EPS is NOT
affected: it cites JA-GRID(c) only, which has no proviso — §2.2.)

### G-6 — JUSTIFICATION GAP (coverage). JB-KEYEQ cannot "reproduce the probe's F1 pattern row-for-row": it walks 12 of the 30 F1 junctions

§7.1: "Byte census (JB-KEYEQ) **reproduces the probe's F1 pattern
row-for-row** (e.g. I4A/I4B byte-equal through the top; T3A/T3C/T3D/T3E
diverge at q = 2; I4C at q = 2, 3 …)". The probe's F1 family is `r ≥ 3`
(`fam = 'F0' if r == 2 else 'F1'`) and walks r = 2..NR+1, i.e. it INCLUDES the
top junction r = n+2; `jb_keyeq` walks q = 1..T.n, i.e. r = 2..n+1, so it
never walks a top junction. Junctions both instruments see: 12 (T3× r=3 ×6,
I4× r=3,4 ×6) — and on those 12 the agreement is exact, 6 GREEN / 6 RED,
including every example the note lists. But **16 roster F1 junctions (all the
top junctions), carrying 12 of the probe's 18 REDs, are outside JB-KEYEQ's
range**, so "row-for-row" reproduction of the F1 pattern is a coverage
over-claim; and the phrase sits beside "q = 1 byte-equal on all 25 rows",
which is the F0 family. (§2(ii)'s quoted "12 GREEN / 18 RED of 30 walked
junctions" is itself EXACT against the committed probe output — `obs 18 (30)`
— so that citation is clean.)

### G-7 — JUSTIFICATION GAP (notation). Three symbols used before/without definition

* `(B-READ)` at the load-bearing step of the JB-CREAD proof — "so some cell
  of R sits on-line on-grid at λ + γ_{m+1} **(B-READ)**, forcing
  w_m(R) ≤ λ + γ_{m+1}" — is never defined in the note. It is [RMG] Lemma
  L-CELL(ii) (whose PARENT, "L-CELL", is in the header consumption list), and
  the step is legitimate (L-CELL(i)'s w_m = min line + (ii)), but the tag is
  unresolvable from this note alone.
* `m_{q+1}^GMN` in JB-DEV(i) ("Φ_q^har is monic of degree m_{q+1}^GMN") — the
  print's key degree, defined neither here nor in J-A §1, which the note
  imports verbatim as its dictionary.
* `s_m(·)` carries TWO meanings the note uses within one section: the eq-(12)
  weight abscissa (JB-EPS's `s_m(V)`, V a weight) and the initial attained
  abscissa of a POLYNOMIAL (§5's τ_m(A) = (s_m(A) − ℓ_{m−1}w_m(A))/e_{m−1},
  as in (VD-m)). They differ by ν·e_{m−1} in general (J-A's own s₀ = s(β) +
  ν·e_{m−1}). No step of the proof is broken — JB-EPS is applied only at
  weight arguments — but the overload is undeclared and neither meaning is
  defined in-note.

### G-8 — JUSTIFICATION GAP (attribution/record hygiene), two minor items

* §1: "**GD-2's** T-F machine check (41,720 instances) … 7,472 violations of
  the unsheared identification". The figures are right and not stale (source:
  `O1thr_phaseB_verifybrief_rev3.md` §9 T-F — 41,720 site-instances, 0
  violations of WGEO/(M6c); 7,472 violations of the unsheared reading; the
  blueprint quotes both). T-F is the O1thr rev-3 runner, cited BY GD-2/GD-3,
  so "GD-2's T-F machine check" mis-locates the instrument.
* The seal commit 7f6759d's message says "**note + runner** sealed with
  preregistered predictions", but that commit contains only
  `grt_jb_checks.py` (990 insertions); the note was committed one commit
  earlier (5a72b62), with the predictions in prose. The seal property that
  matters — predictions on record before the battery, runner byte-frozen from
  seal to verdict, no §1–§6 movement between them — HOLDS (§1.1); only the
  message is imprecise.

### G-9 — JUSTIFICATION GAP (quantifier/perimeter). JB-VTX and JB-DEV(iii) quantify over 0 ≤ q ≤ n but their proofs need shared keys below q

JB-VTX's header is "Level q with read (e_q, h_q) defined (0 ≤ q ≤ n)" and its
grade line reads "unconditional GIVEN the representative legitimacy (W-2
clause 1's perimeter and conditionality ride; on byte-equal chains no W-2 input
is needed beyond TH-BASE)". But clause (a) consumes JA-VAL — for the digits AND
for the key (v_{q+1}(φ_{q+1}) = w_qΦ_q) — and J-A grades JA-VAL "PROVED
unconditionally **on the shared-key perimeter**". Off that perimeter the print
frame U(f) is computed with print keys that differ from Φ_0..Φ_{q−1}, so (a)
is not merely unproved but false. The runner honors the narrower perimeter
exactly (`qcap_of(T,G) = min(T.n, shared_upto(T,G) + 1)` — "keys shared
strictly below q" — plus the extra `q <= L` guard on the (d) ties), i.e. the
machine evidence quantifies the narrower statement, and §1 does display the
shared-key perimeter under a heading that says "fixed once", which partially
carries the fence. Still: the theorem-level display and the grade line name
only W-2 clause 1, and a reader taking JB-VTX at its stated quantifier gets a
false clause (a). Same mechanism in JB-DEV(iii)(VAL).

---

## §4. Checked and CLEAN (so the coverage of this pass is auditable)

* **JB-AFF**: two-line proof correct as written; a > 0 is used exactly where
  needed; applied at (a,b,c) = (e_q,h_q,0). The runner's `lower_hull` builds
  strict-vertex lower hulls (pops non-strict turns), so "vertices to vertices"
  is tested in the right category.
* **JB-DEV(i)/(ii)**: the "same division" argument is uniqueness of
  division-with-remainder by a monic polynomial — correct, and the runner's
  fresh schoolbook `fresh_dev` (never `PolyO.dev`) is compared to BOTH engines'
  digit lists at every shared level (893 samples). §2(ii)'s quoted probe figure
  "12 GREEN / 18 RED of 30 walked junctions" is EXACT against the committed
  `grt_weld_probe_output.txt` (`F1 … obs 18 (30)`).
* **JB-DEV(iv)** cross-key fence: the cited representative-dependence
  v_{r+1}(φ − φ′) = e_r·v_r(φ) is the standard MacLane fact and is used only to
  DENY a byte identity — the fence is drawn the right way round, and JB-BOX-3
  repeats it.
* **JB-TREE(ii)**: the (ID-(i+1)) digit-list argument is correct (each
  C_k^{(i)}Φ_i^{e_ik} has degree < deg Φ_{i+1}, C_k reduced by REALIZE R1, so
  uniqueness of division reads the digits off), and the runner checks the
  identity in O[x] plus the key's own development digit-by-digit (34 samples).
  The note's display of (ID-(i+1)) drops [RMG]'s ψ_{i,k} ≠ 0 qualifier on the
  sum; harmless, since C_k^{(i)} = 0 exactly there (and the runner skips those k
  explicitly).
* **JB-TREE(iii) quanta vs LED-Λ**: the note's four bullets (promotion
  +q_{i+1} > 0, correction-main v_{m+1}-flat, junk ≥ E_m (π) / ≥ Γ₀ (Y), exits
  pay w_mΦ_m) match LED-Λ's S1 λ_E row verbatim (`LEDGERLAMBDA_2026-08-08.md`
  line 192) with q_l := h_l·∏_{l<t<m}e_t (line 74). I re-derived the promotion
  quantum from the Γ-definitions independently: Γ_{i+1} − P_iΓ_i =
  h_{i+1}∏_{i+1<t<m}e_t, which is exactly the runner's `qq[i+1]`, and the exit
  edge gives −P_{m−1}Γ_{m−1} = −e_{m−1}g_{m−1}γ_m = −w_mΦ_m. ✓ (Observation,
  not a finding: for P- and E-edges this check is an identity in tower data —
  b is unchanged — so JB-LINE's real arithmetic content is the junk-floor rows
  and the leaf tie line = wlev = vgen; the note does not claim more.)
* **JB-BOX-1 (the blueprint correction)**: the blueprint quote is VERBATIM
  (`GRT_WELD_BLUEPRINT_2026-08-08.md` lines 173–175: "multiplying a read digit
  by the canonical correction digit shifts the CLASSIFIER's residual read by
  τ_m with the level-m EPS-carry z_m^{ε′}"), and the correction is right in
  both directions: the print-frame factor is ε_m(γ_{m+1})τ_m = c_m (carry-free)
  and the harness-frame factor is z_m^{ε′}τ_m ([RMG] (C-READ)); the frames
  differ by ε(λ+γ)ε(λ)^{−1} = ε(γ)z^{−ε′}, which is JB-EPS. The
  frame-conflation diagnosis is fair to the blueprint text.
* **W2-OPEN-1 "consumed NOWHERE"**: TRUE. W-2 §5.3's open lemma is the
  transported K5/K6/K7/K12 value battery; no §2–§5 statement touches it. (Worth
  recording the other direction: W-2 §5.3 says the distance to proving
  W2-OPEN-1 "is the W-2 → W-5 seam (the correction-tree junction J-B)" — so J-B
  is the unit expected to eventually supply it, and §7.3's "NOT supplied: …
  W2-OPEN-1" is the honest line.)
* **v = 0 branch**: the displayed reason (R's own weight may exceed
  λ+γ_{m+1} with a nonzero own-side print residual) is correct, and the census
  (0 occurrences) is honestly reported as 0 rather than as a verification.
* **τ_m ≠ 0 / c_m ≠ 0**: forced by the class pin ψ_j(0) ≠ 0 (J-A §1, JA-PIN
  clause 5 with the print's ψ ≠ y at tex 829/882/1149) and enforced in the
  engine's ψ search; also machine-pinned by JB-CM (28/28).
* **I4C as the scope fence in action**: `elig_ms(I4C) = []` (no level with
  g_m = 1 ∧ T-scope), so its tree/cread rows are absent — exactly as §7.1
  states, and the runner's off-perimeter counter is 0, so nothing was silently
  dropped elsewhere.
* **TW-JB**: chambers re-run every family (2,480 samples) with violations
  attributed to TW-JB; transport failure would be a violation, so 0 means all
  16 transports built. Note the runner re-runs chambers on ALL 16 towers
  regardless of ledger triviality (`# trivial ledgers still re-run`), which is
  stronger than the note's "on every tower with a nontrivial W-2 transport
  ledger" — the claim is understated, not overstated.
* **Citation naming**: every external result named with a source — GMN print
  anchors carry tex line numbers (N_r(f) ~1370–1376, N_r^− 1377, Lemma `shape`
  ~1395–1414, Def `t(i)` 1431, `rescoeff` 1447, `defresidual` 1497,
  `propertiesv` item 3 at 1028), consumed notes named with their grades, and
  the print is consumed only through the sealed `GmnLeg` transcription (no new
  transcription in-unit — confirmed: the runner imports `grt_weld_probe`).
  `propertiesv` item 3 is the right anchor for the single-monomial identity
  e_q u_i + h_q i = v_{q+2}(A_iΦ_q^i) (which I re-derived from the
  single-digit/single-monomial developments).
* **Grade-cap honesty elsewhere**: "attempt grade (acceptance counter 0/2; no
  gate fires)" is consistent throughout; §7.3's NOT-supplied list is accurate;
  no accepted text is touched; no gr/carrier or density claim appears (the §5
  remark is explicitly read-values-only with BLOCKED-ON-CARRIER-TIE restated).

---

## §5. Divergences from the archived outage partial

Read only AFTER forming the above. `GRTJB_passPE1_PARTIAL_outage_2026-08-05.md`
carries a machine leg + analysis and NO verdict (its §E is "(filled at end)");
its §C header nevertheless states "**Verdict: 0 CRITICAL ERRORS / 5 findings**".

**Convergent (independent arrival, same substance):**
* partial Finding 1 = my **G-2** ("across 7 towers"). Same diagnosis, same
  smoke-list explanation. Bookkeeping differs in words only: the partial says
  "14 distinct rows, not 7" and then enumerates 11 towers + 3 JD rows; I count
  14 distinct towers / 21 teeth-positive JSON rows.
* partial Finding 2 (+ its §D1) = my **G-1** (print-key division is the same
  computation). Its §D1 adds a useful point I confirm: `gmn_from_tower` grows
  the print key chain through the fresh `_thm_phir`/`construct` recursion, so
  byte-equality is itself a genuine machine fact — the empty part is only the
  second division.
* partial Finding 5 = my **G-3** ("all 25 rows"; same three QO rows).
* partial Finding 3 ≈ my **G-9** (JB-VTX's shared-key perimeter not restated at
  theorem level).

**Divergent:**
1. **THE CRITICAL ONE. The partial CLEARED what I find critical.** Its "Checks
   that PASSED" list contains: "**Boundary geography** — the 21 boundary rows
   sit exclusively on T3A/T3B/T3C/T3D/I4B + their chambers (JSON); all five
   diverge at q = 2 in the byte census (= character-visible per the W-2 byte
   law), with T3B/I4B the W-2 collapse-boundary pair — **the claim as worded
   checks**." It verified WHICH TOWERS the boundary rows sit on but never the
   LEVEL m, and so accepted "boundary … exactly the JA-BOX-2/(VD-m)-proviso
   geography" together with "uncond. m ≤ 2". Splitting the same JSON rows by
   level (§1.3) shows 10 of 13 at m = 2 — inside the claimed-unconditional
   stratum. This is F1, and it is the one finding of this pass that changes the
   note's grade surface.
2. The partial also lists "**JB-CREAD derivation** — every line verified" and
   under it "R ≠ 0 on the scored stratum is forced by the nonzero read" and the
   τ_m-unit chain — I agree with all of that (§2.3); the perimeter claim, not
   the derivation, is what fails.
3. **partial Finding 4 — I do NOT raise it.** It faults JB-BOX-2 for omitting
   W-2 clause 1's admissibility perimeter. But JB-BOX-2's own first sentence
   scopes it ("Every PRINT-RESIDUAL statement rides J-A's boxes verbatim"), and
   clause 1's perimeter is displayed in the grade cap ("its representative
   clause on W-2 clause 1's perimeter") and restated at every consuming site
   (§2(i), §3 preamble, §4 setting). I judge that fence correctly drawn; my
   fence-inventory finding is the JA-GRID(a) proviso instead (G-5), which the
   partial did not raise.
4. **partial G-6-analogue MISSING / cleared.** The partial states the JB byte
   census "matches the probe's byte_equal pattern **row-for-row, 0 mismatches**
   (checked programmatically across all 44 tower junctions)". The two
   instruments walk different junction sets: `jb_keyeq` covers q = 1..T.n
   (print r = 2..n+1) and NEVER a top junction, while the probe's F1 family is
   r ≥ 3 including the top; they share 12 junctions (agreement exact there),
   and the 16 roster top junctions — carrying 12 of the probe's 18 F1 REDs —
   are outside JB-KEYEQ's range. I raise that as G-6; the "44 tower junctions"
   figure does not correspond to either instrument's count (probe: 21 F0 + 30
   F1 = 51; jb_keyeq: 34 entries over 25 rows).
5. **Machine-artifact identity claim — half-confirmed.** The partial reports the
   regenerated JSON "**md5-identical** to the committed sealed artifact
   (0dc4b015ac520d2bb05094329d7754ba)". The quoted md5 IS the committed
   artifact's (verified: `md5sum` after `git checkout` = 0dc4b015…), so the
   partial's run did reproduce it byte-for-byte. But the property is
   timing-dependent, not a property of the artifact: the JSON stores
   `elapsed_s`, and my re-run wrote 0.8 where the seal has 0.7, so my
   regeneration is identical in every count, census and violation entry and
   differs in that one field. Future passes should quote "identical except
   `elapsed_s`" rather than an md5.
6. Internal slip in the partial (noted only because it is archived): its §D3
   says "see Finding 4" where it means Finding 3.

**Nothing in the partial is treated as authoritative here**; every figure in
§1 and §3 of this report was recomputed in this pass.

---

## §6. What a repair would have to do (for the composer, not this verifier)

Not this pass's job to fix, but the F1 repair surface is small and worth
recording so the next round is not re-litigated:

1. Rescope four sites from "unconditional at m ≤ 2" to "unconditional at
   m = 1 ((VD-1) = W2-L3); at every m ≥ 2 conditional on JA-VDIND's absolute
   character-triviality (⊇ (R-coll) at m ≥ 3)": §5's theorem parenthetical,
   the grade cap, §7.2's JB-CREAD row, JB-BOX-2's "at m ≥ 3".
2. Re-word §7.1's census sentence: the boundary is the JA-VDIND collapse
   boundary, m = 2 for 10 of the 13 roster rows and m = 3 for I4B's 3 —
   the disclosure is already there, only the attribution is wrong.
3. Optional but cheap, and it would have caught F1 mechanically: have the
   runner record the level m on every boundary row (it currently aggregates
   per-tower only), so the census cannot be read as an m ≥ 3 phenomenon.
4. G-1: state the tree's second key leg as what it is — "and, where the print
   key is byte-equal, the same division by the print key's bytes (a
   consistency re-check, not an independent reading)".
5. G-2/G-3/G-6: three figure corrections (14 towers not 7; 22 of 25 rows;
   "row-for-row on the 12 junctions both instruments walk").
6. G-4/G-5/G-7/G-9: one clause subject, one proviso named in JB-BOX-2, three
   notation definitions, one theorem-level perimeter restated.
