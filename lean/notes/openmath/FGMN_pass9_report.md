# FGMN pass 9 — hostile verification WITH full execution leg (Fable, fresh context)

**Target:** `lean/notes/openmath/FGMN_REDERIVATION_2026-08-08.md` (REVISION 7) +
`verification/openmath/fgmn_rederivation_check.py` / outputs + the pinned
`docs/references/` sources.  No prior `FGMN_pass*_report.md` was read.  Charge:
mandatory execution leg (both sha256 pins; battery re-run + byte-level compare;
**verifier-owned execution of the REVISION-7 OPERATIONAL closure** over
`lean/LeanUrat/` reconciled against the note's perimeter), then the standing
perimeter (double-scaling diagnosis vs the pinned extraction; row-A; branch+meter;
rescopes; three-token diff; JuncForge/D0/S8 honesty).  Quote-and-classify; nothing
fixed.

## 0. Mandatory execution leg — results

* **Both sha256 pins VERIFIED byte-identical**: PDF
  `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35`, layout
  extraction `8d30f15e6d37a52be20634545c95f32e372a233166c5dab8d995c3d5f76e848b`
  (`sha256sum`, this session).
* **Battery re-executed**: `python3 verification/openmath/fgmn_rederivation_check.py`
  → exit 0, ALL GREEN, TOTAL checks 1093 (= R0 28 + R1 336 + R2 336 + R3 1 +
  R4 336 + R5 56); console **byte-identical** to `fgmn_rederivation_rerun_r1.txt`
  (including timings) and `fgmn_rederivation_results.json` regenerated
  **byte-identical** (working tree clean after the run).  Meters identical:
  misread-ε {A:24,B:48,C:24,K:28,L:24,M:48,N:48}; R2 support {2:264,3:68,5:4}
  (sums 336; minimum 2 — consistent with R2 obs 0 under the repaired branch).
* **REVISION-7 closure executed verifier-side** (own implementation:
  identifier-boundary matching per rule (a); declaration-kind spans with
  namespace-qualified names per (b); recursive ring expansion with the two
  declared prefix-patterns per (c); fixpoint over seed ∪ ring from round 1 per
  (d)).  Findings 1–3 below are its output.
* Environment note (not a finding): the agent-harness `grep` here is ugrep 7.5.0,
  which returns **0** for the pinned pattern on the multibyte term `σ.w`; system
  GNU grep 3.7 computes it correctly.  All greps below used `/usr/bin/grep` or
  Python `re`.

## 1. FINDINGS (quote-and-classify)

### Finding 1 — CRITICAL. The REVISION-7 closure rule is not implementer-independent: its two faithful readings differ by 26×, and the live reading saturates to ~97% of the tree.

Quote (REVISION 7, item 1): "(b) … a hit inside a declaration's source span joins
BY the declaration's fully-qualified name; (c) ring entries ARE recursively
expanded (same rule) … (d) the fixpoint is over the union (seed ∪ ring) from
round 1. **Two faithful implementers now compute the same set.**"

Executed both faithful readings of the expansion step ("for every identifier t in
the set, `grep -rn '<t>'`", REVISION 6, retained by REVISION 7):

* **Fully-qualified-name reading** (grep the string the declaration "joins BY"):
  full FQNs occur **zero** times in source — measured `LeanUrat.MovesJ.SideReads`
  0, `LeanUrat.HC1.Tower.side` 0, `LeanUrat.Scaffold.DictIII.SideClauseR1` 0
  (files open namespaces; even partial `MovesJ.SideReads` (6 hits) does not
  contain the FQN string) — so **no rule-(b) name ever expands**: the fixpoint is
  the round-1 set (**466 declarations** under my span parser) plus
  prefix-pattern-matched identifier chains.  The recursion REVISION 6 called
  load-bearing is dead text under this reading.
* **Base-name reading** (grep the last name component — the only reading that
  makes the recursion live): the fixpoint **saturates at 12,199 declarations
  across 1,171 of 1,203 `.lean` files (~97% of the tree; 11,714 identifiers;
  fixpoint at round 6; rounds add +448, +6,375, +4,512, +362, +6, +0
  identifiers)**.  The saturation is rule-licensed, verified by hand at each
  link: the ring term `σ.w` hits the **docstring** of `def side`
  (`HC1/DefsCar.lean:86–88`, FQN `LeanUrat.HC1.Tower.side`) — rule (a) counts
  docstrings as references — so the identifier `side` joins at round 1; `side`
  then matches English prose tree-wide, and by round 2 single-token names join
  (`of` — e.g. `LeanUrat.MovesT.of` at `MovesT/D2_eligGate.lean:183`,
  `LeanUrat.OM.ProductTheorem.of` at `OM/ProductTheorem.lean:1998` — plus `is`,
  `at`, `as`, `s`, `D`, `O`), whose expansions close over the corpus at round 3.

Failure: 466 vs 12,199 declarations from the same pinned text — the sentence
"Two faithful implementers now compute the same set" is **refuted by execution**,
and the pass-8-gap-1 fix did not achieve its stated property.  Under the only
non-vacuous reading the "application perimeter" is the whole tree, so §S3
obligation (b) ("a grep census of `SideReads` consumers … with per-consumer
disposition") is not dischargeable and the perimeter no longer scopes the re-key
at all.  What is needed is a tiebreak (which string is grepped for a joined
declaration) plus a stop on prose/short-identifier joins (e.g. exclude [doc]
hits from *membership*, or a whitelist of expansion-eligible names) — left to
the prover; nothing fixed here.

### Finding 2 — GAP. Ring term `lastRead_of_readsOf` matches nothing under the pinned matcher (dead entry; evidence the (a)+(c) semantics were never executed against the pinned ring).

Quote (REVISION 7 (a)): matching is by
`(^|[^A-Za-z0-9_'])<t>($|[^A-Za-z0-9_'!?])`; quote (REVISION 6, term set): "…
{`SideReads`, `SideClause`, `sideReads_`, `σ.w`, `readCeil`, `read_locality`,
`lastRead_of_readsOf`} …"; quote (REVISION 7 (c)): "the two prefix entries
(`SideClause`, `sideReads_`) are declared PREFIX-PATTERNS".

Measured: `lastRead_of_readsOf` has **0** boundary matches in the tree — all 4
occurrences (`Scaffold/DictIII/Window.lean:506/:565/:1034`,
`Scaffold/DictIII/CU1.lean:1351`) are the extension `lastRead_of_readsOf_snoc`,
whose following `_` is excluded by the after-boundary class, and the term is not
one of the two declared prefix-patterns.  The pass-6 site that motivated the
entry (`lastRead_of_readsOf_snoc`, Window.lean:506) joins the closure anyway via
the `SideReads`/`ReadsOf` hits inside its span, so no perimeter site is lost —
but the pinned ring as written carries an inert entry, which an executed dry-run
of the pinned rule would have caught.

### Finding 3 — GAP. The round-2 evidence list is off by one under the note's own matcher: 14 files, not 15 (`U27_gateInert` qualifies only via a substring artifact).

Quote (REVISION 6, item 2): "15 `.lean` files reference the four intermediaries
yet never mention `SideReads` directly — HK52_stretchGate, U19_runCoherent,
U1_negWitness, U23_runRealizable, U25_polTotal, **U27_gateInert**, UE_vtxUpper,
MovesT/Defs, MovesT/G1_toyGate, DictIII/CU1, DictIII/Hyps, H1/RCWitness,
H1/RunBinding, H6/EngineConform, H6/RowsK4."

Measured with the REVISION-7 boundary regex: exactly **14** files reference ≥1 of
{`ReadsOf`, `junc_bundle`, `GlueRun`, `DIterJunctionSupplier`} without mentioning
`SideReads` — the list above minus `U27_gateInert`, no extras.
`HC2/U27_gateInert.lean`'s sole intermediary occurrence is the **substring**
`ReadsOf` inside `import LeanUrat.HC2.U31_gateReadsOf` (line 42), which the
pinned identifier-boundary rule excludes (preceded by `e`); it has no other hit
for any of the four.  The file still belongs to the *recursive* perimeter (it
consumes U31 declarations that reference `SideReads`), so the load-bearing point
— the recursion is needed — survives, strengthened; but the displayed evidence
count is a plain-substring artifact that the note's own pinned matcher rejects.
Secondary (same display): under REVISION 7 (d) the four intermediaries are ring
entries expanded **from round 1**, so those files join at round 1 and the
"round-2 evidence" framing is stale relative to the current rule.

## 2. Standing perimeter — all re-verified, no new findings

* **Round-1 census reconciled exactly**: `grep -rn 'SideReads' lean/LeanUrat/` =
  260 lines; 246 in `.lean` across 36 files; 14 in the two `MANIFEST.json`; all
  11 displayed top-file counts exact (V9_K1nonrec 27 … DictIII/Window 9).
* **Named sites at their recorded lines**: `def SideReads` HC2/Defs.lean:280,
  σ.w tokens at :285/:287/:292 (exactly THREE — the REVISION-2 supersession of
  "four" verified), clause-(ii) residual leg already at `ν.σ.wPrev` (:295);
  `SideClauseR1` Locality.lean:272 / `sideReads_r1` :280 / `SideClauseR2` :735
  (σ.w :738) / `sideReads_r2` :744; `lastRead_of_readsOf_snoc` Window.lean:506
  (binds `SideReads` by name); `DIterJunctionSupplier` GlueRun.lean:875 with the
  verbatim antecedent `σ₁.Φ.natDegree < n`.  The full REVISION-4 list
  reconciled line-by-line: dagger rows Locality.lean
  :322/:381/:398/:658/:794/:828/:847/:1327 (all `ν.gam < e·σ.w(B−B′)+j·h`
  shapes) and Window.lean :177/:258/:260/:266/:544 (hwS binder)/:554/:557
  (endpoint functionals).
* **§S1 vs the pinned extraction — every display re-read, exact**: operators at
  the parent valuation (l.869–871 `Ni := Nµi−1,φi`); cloud ordinates µ(aₛφˢ)
  (l.383–385); Qₛ at µᵢ₋₁ (l.936–938); eq (13) two-case window law
  (l.941–943); eq (12) (l.881); Lemma 2.3 proof line (l.415); Def 3.16 with
  ǫᵢ₋₁(αⱼ)·R_{i−1,αⱼ}(aₛⱼ)(zᵢ₋₁) (l.916–923); Cor 4.4(2) verbatim
  (l.1086–1087); Def 3.18 + j₀ = ⌊s(g)/eᵢ⌋ (l.994–1000); eq (14) (l.1004);
  Lemma 4.1 anchor monomials (l.1017–1019); **Thm 4.2 l.1029 verbatim**
  (`Hµ(g) = ϕr(α)Rr,α(g)(yr) = ϕr(g)Rr(g)(yr)`); Cor 5.6(2) (l.1263–1265).
  Trivial cite wobble only: §S1(B)'s "(l.923, l.934)" for sⱼ/αⱼ — the formulas
  sit at l.921/l.932–934, inside the cited Def-3.16 range; immaterial.
* **§S7 PIN-GEN-i column arithmetic recomputed to the codepoint**: line 911's ′
  at codepoint column 52; line 912's two ℓ's at columns 51 and 59; column 52 of
  l.912 is the `i` of the FIRST ℓᵢ — the mode-C reading ǫᵢ(α) =
  zᵢ^{ℓ′ᵢs(α)−ℓᵢu(α)} exactly as claimed.  Genericity ranges verified: 0≤i<r
  (l.910), 0≤i≤r (l.916), 1≤i≤r (l.994–995); ǫ₀≡1 convention (l.914–915).
  TR3-S3's owed pin matches the §S7 discharge scope (TR3S3 note re-read).
* **§S1 translation + §S2 diagnosis re-derived**: e(µᵢ)µᵢ(Bⱼφʲ) =
  eᵢ·[e(µᵢ₋₁)µᵢ₋₁(Bⱼ)] + j·e(µᵢ)(wᵢ+λᵢ) = ν.e·σ.wPrev(Bⱼ) + j·ν.h (uses
  e(µᵢ) = eᵢ·e(µᵢ₋₁)) — exact.  Row-A by hand: fA − Φ1A² = 24, B₀=24, B₂=1;
  w1(24)=3; corrected {2·3+0, 2·0+2·3} = {6,6} = gam 6; compiled {12,6}; the
  parity collision (σ.w(24)=ν.h=3 odd vs graded 2·wPrev=6 even) as displayed.
  `RegradeOf.w_coeff` exists (MovesC/Defs.lean:651); `U31.bStage` literally sets
  `w := bw, wPrev := bw` (U31_gateReadsOf.lean:635–636).
* **Three-token diff**: the §S3 OLD clause-(i) block is verbatim-unique
  tree-wide (1 hit, HC2/Defs.lean); the clause-(ii) functional fragment appears
  exactly twice tree-wide (Defs.lean + the SideClauseR2 mirror :738 — already on
  the REVISION-4 perimeter record; unique within Defs.lean, diff appliable).
* **Branch + meter**: `check_compiled_unsat` implements the REVISION-1 semantics
  exactly (violation iff ≤1 distinct compiled value at supported slots; empty =
  vacuously solvable; any singleton counts); the sealed derivation re-done:
  at a supported slot the compiled value is e·gam − j·h·(e−1), pairwise distinct
  over supported slots for e≥2, h>0 — matches the measured support meter
  minimum 2.  §S8's render vs the raw record: per-slot [12,6] vs raw sorted
  [6,12] with the REV3/REV4 disclosures in place; raw file re-verified as the
  byte-identical record.
* **Rescopes accurate to code**: R1 checks (i-a)/(i-b)/(ii-support+equality)/
  (iii-window-length) only — no σ.R instantiation anywhere (the Lean-side
  corrected-bundle construction stays owed, §S9); R4 is a differential falsifier
  consuming certified Tower state (T.w1/T.res_digit/T.K1/T.z1, keys, chain
  parameters), independent only in recursion/exponent code — §S7's rescoped
  wording matches.  Misread meter discriminates on every row (24–48/row).
* **JuncForge/D0/S8 honesty**: `juncforge_no_e2_junction` (JuncForge.lean:276)
  binds `SideReads` by name and concludes ν.e = 1 — the REVISION-2
  application-mode account (in-place edit would re-key what it asserts;
  recommended mode = new `SideReads'`) is correct; `juncforge_clauseIII_derivable`
  (:578) and `juncforge_D0_instanceFalse` (:686) exist; `gate_glue_conditional`
  GlueRun.lean:1161; eq (14) confirms the D0 degeneracy in the source; R5 GREEN.
  No `.lean` file touched by any FGMN commit (303b11e, 236d85c, fa2180e/861811c/
  3b0ccd8 note-and-artifact only); `juncforge_stage1.py` last modified at
  53f5d03, before the FGMN unit — "imported, not edited" holds.
* Charter/riders located: JUNCFORGE_S2 §R3 (l.223); SYNTHESIS_PASS7 §F1 queue #2
  with the four riders.
* F2c status: this pass executed verifier-side (pins, battery byte-compare,
  verifier-owned closure implementation).  The from-note **reimplementation of
  the §S8 battery** was NOT performed here and remains the acceptance
  obligation exactly as §S9 states.

## 3. Verdict

The mathematical perimeter — diagnosis, row-A, branch+meter, rescopes,
three-token diff, PIN-GEN-i, JuncForge/D0/S8 honesty — survived a full
independent execution leg again, with the pins and battery byte-identical.  The
findings all sit in the REVISION-6/7 closure-rule layer: the operationalization
claim is refuted by execution (Finding 1, critical), and two of its displayed
evidence items fail under its own pinned matcher (Findings 2–3, gaps).
Acceptance counter resets/does not advance.

FGMN-P9 FINDINGS: 1 critical, 2 gaps
VERDICT: CRITICAL
