# UNIT CCA — VERDICT: THE m = 4 REMAINDER CARRIER PARTITIONED AND COUNTED, `ConeRemainderLaw 4 σ` CLOSED AT EVERY ODD-RAMIFICATION TYPE, THE X-STRIP FRONTIER DISSOLVED AT m = 4, THE CENSUS FRONT RE-BASED TO e ≥ 5 + FIVE EVEN-RAM TYPES (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG31.lean` (931 lines, ZERO sorries, zero
warnings; 14 AxCheck footer lines — Lean core `{propext, Classical.choice, Quot.sound}`
on §1 (the carrier identity and both box counts), and Lean core PLUS EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42)
on §§2–6 and the §3b demo; the C.33 (r = 1) cites do NOT occur — no ChapC import; no
landed file touched except the sanctioned one-line aggregator import in
`Uniformity/ChapI.lean`; IFCG29 untouched; no git ops).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG31.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG31` green (8939 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green, PLUS a 720-sample decorrelated GP/PARI
battery (below) — ALL PASS.

## ★★★ THE HEADLINE — the `e = 4` member closed at every odd-ramification type

    theorem coneRemainderLaw_four_mixed   : ConeRemainderLaw 4 ⟨{(1,1),(3,1)}⟩
    theorem coneRemainderLaw_four_of_odd  : (∀ p ∈ σ.data, ¬ 2 ∣ p.1) → ConeRemainderLaw 4 σ
    theorem decidedSliceAt_all_of_remainder5_even4_bridge :        -- ★★★ the front re-based
      (∀ e ≥ 5, (smaller value laws) → ∀ σ deg-e Witnessed, ConeRemainderLaw e σ) →
      (∀ σ deg-4 Witnessed with an even-e member, ConeRemainderLaw 4 σ) →
      (∀ δ e ≥ 2, UnramifiedBlockBridge δ e) → ∀ n, DecidedSliceAt n

The mass-4 remainder value at the mixed type is the constant
`(q−1)/q⁶ + (q−1)/q⁹ = (q−1)(q³+1)/q⁹` — exact at EVERY finite level
(`coneRemainderCount_four_mixed`: `(q−1)q^(4K−6) + (q−1)q^(4K−9)`, `K = M+4`), uniform in
`q`, every complete DVR, every uniformizer.  Every OTHER type all of whose ramification
indices are odd has remainder count IDENTICALLY ZERO (`coneRemainderCount_four_ne_of_odd`
— degree-free statement).  At degree 4 the odd-ramification types are exactly
`{(1,1),(3,1)}` and the FIVE unramified types (`{(1,1)⁴}`, `{(1,1),(1,1),(1,2)}`,
`{(1,2),(1,2)}`, `{(1,1),(1,3)}`, `{(1,4)}`) — so **6 of the 11 degree-4 types are
CLOSED**, and the census's `e = 4` obligation is reduced to exactly the five
even-ramification types: `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`, `{(2,1),(2,1)}`,
`{(2,2)}`, `{(4,1)}`.

## ★★ THE PARTITION (charge item 1) — the m = 4 instrument

    theorem remainder_carrier_four :  (stratum ∩ shallow) \ pureFaceSet
      = (box31a ∪ box31b) ∪ forcedBox          -- Lean-core set identity

with `box31a = {v₀ ≥ 2, v₁ = 1, v₂ ≥ 1, v₃ ≥ 1}`, `box31b = {v₀ ≥ 3, v₁ = 2, v₂ ≥ 2, v₃ ≥ 1}`,
`forcedBox = {v₁ ≥ 2} ∩ ({v₀ = 2} ∪ {v₀ ≥ 3, v₂ = 1})` (all inside the stratum; pure faces
at m = 4 are `h ∈ {1, 3}`).  Counts: `card_box31a = (q−1)q^(4K−6)`,
`card_box31b = (q−1)q^(4K−9)` — CN4's monomial genre, every level.

**The decided sector needs ONE mechanism, not a pigeonhole** (`decidedAt_quartic_31`,
`t := v₁ ∈ {1,2}` parametrizes both boxes): the class polygon has the two-point side
`[1, 4]` of slope `t/3` (support `4t` attained exactly at `{1, 4}`), CRL's Hensel heart
splits every lift into a `(t,3)`-pure cubic block — irreducible `(3,1)` by the unit-width
decision since `3 ∣ deg ≤ 4` pins degree 3 — times a monic linear `(1,1)`.

## ★★ THE X-STRIP FINDING (charge item 2c) — the named frontier DISSOLVED at m = 4

CRL/WFR's fence named "the class-level X-strip" as THE missing mechanism for
invisible-corner cells.  **At m = 4 the law needs no X-strip at all**: the deciding side
`[1, 4]` never touches abscissa 0, so `decidedAt_quartic_31` is uniform over the
invisible corner (`v₀ = K`, `a₀ = 0` included — the `f(0) = 0` lifts ride CRL §2's
built-in X-strip induction inside the heart); and the forced sector's faces (`[0,4]` at
`v₀ = 2` exact — always visible; `[2,4]` at `v₂ = 1` — corner-free) never gate on the
corner either.  Record correction for the successor: the X-strip is NOT census-blocking
at m = 4; it can only re-enter inside the even-ram sector's own deeper discharge.

## ★ THE FORCING (the exclusion engine) and the sector-(b) demo

`forces_even_ram_of_forced`: every `forcedBox` class carries a visible class NP face of
slope `1/2`, so `fracFaceForcesRam_of_stratum` (CRL §3) puts a factor with
`2 ∣ ramIndexOf` in EVERY lift; `not_decidedAt_of_forced_of_odd` turns this into the
zero counts.  §3b lands the forced sector's first decided leaf
(`decidedAt_forced_split`): an `E1` class (`v₀ = 2`, `v₁ ≥ 2`) whose slope-`1/2` class
residual splits into coprime monic linears is DECIDED `{(2,1),(2,1)}` — XHS's
`wideFace_refinement_of_stratum` consumed verbatim, both blocks decided by IFCG26 §4,
the cofactor `R` forced to `1` by degrees.  This is exactly the leaf shape the even-ram
successor consumes.

## THE DECORRELATED BATTERY (`runs/wave-c/cca_battery.py`, GP/PARI 2.17.4)

720 samples over ℤ_p, p ∈ {2,3,5} (random digits, vanishing coefficients, huge/invisible
corners included), factored by `factorpadic` + `idealprimedec` (the calibrated oracle's
logic): **T1/T2 (480): every box31a/b lift has type {(1,1),(3,1)} — PASS.  T3 (240):
every forcedBox lift has an even-e factor — PASS**, and the observed genre table is
EXACTLY the predicted surviving five: `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`,
`{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}` — with `(4,1)` occurring ONLY at p = 2 (the wild
double-root recursion), confirming the parity structure below.

## THE EXACT SURVIVING OPEN SET (charge item 3 — the fence)

After this unit `DecidedSliceAt n` for all `n` rests on precisely (via the new bridge):

1. **`ConeRemainderLaw 4 σ` at the five even-ramification types.**  Their carrier is
   `forcedBox`; its hull genres and mechanisms, computed here (prose-level analysis,
   verified by the battery, NOT yet Lean):
   (a) *slope-1/2 wide faces* (`E1`; also `v₀ odd ≥ 5` integer-slope width-2 faces in
   `E2`): residual quadratics.  SPLIT residuals → §3b's leaf (DECIDED, landed);
   IRREDUCIBLE residuals → `{(2,2)}`-type leaves = **B.63's `order1Type` territory**
   (the perimeter supply at residual degree 2); DOUBLE-ROOT residuals → the RECURSION
   (a `(1,2)`-pure quartic block = the smaller-scale census; exists only where the
   char/parity allows — `Y² + d₀` is a square iff char 2, `d₂ ≠ 0` kills it in char 2).
   The depth-0 split/inert counts are PARITY-STRUCTURED (e.g. inert residual pairs:
   `(q−1)²/2` odd q vs `q(q−1)/2` even q) — the uniform-in-q law for each σ genuinely
   needs the double-root recursion to resum; no depth-0 count closes it.
   (b) *`v₂ = 1` mixed systems* (`E2` with `v₁ ∈ {2, ...}`): WFR's pigeonhole decides the
   all-two-point genres (e.g. `{v₀ even, v₁ > (v₀+1)/2}` → `{(2,1),(2,1)}`); the
   invisible-corner sub-cells of `E2` are genuinely UNDECIDED at finite level (lift NP
   genre varies with `v(a₀)` parity) — they contribute 0 per level and their decided
   deep refinements are recursion territory.
2. **`ConeRemainderLaw e σ` at `e ≥ 5`** — untouched, with the same engine bank; note
   the m = 4 pattern (single `[1, m]`-side decisions + one forced sector) suggests the
   odd-ram closure generalizes, but the genre combinatorics grows.
3. **`UnramifiedBlockBridge δ e`** — CN5's family, another unit's, unchanged.

Conjecture recorded for the successor (NOT proved): at every `m`, every shallow stratum
class polygon has a fractional face (all-integer hulls force `vᵢ ≥ m−i` = deep), so the
all-unramified types' zero law should close at EVERY `e` by the §3-style forcing —
the missing lemma is the wide-face generalization of WFR's `staircase_not_shallow` plus
a visibility argument for the chosen face.

## File map (`leanfinal/Uniformity/ChapI/IFCG31.lean`, 931 lines)

§0 `mixedType4`, `typeOf_eq_of_split_three_one` (private) · §1 `box31a/b`,
`mem_box31a/b_iff`, `forcedBox`, ★ `remainder_carrier_four`, `card_box31a/b` ·
§2 ★★ `decidedAt_quartic_31` · §3 `stratum_of_forced`, ★ `forces_even_ram_of_forced`,
`not_decidedAt_of_forced_of_odd` · §3b `ramPairType`, ★ `decidedAt_forced_split` ·
§4 ★★ `coneRemainderCount_four_mixed`, `coneRemainderCount_four_ne_of_odd` ·
§5 ★★★ `coneRemainderLaw_four_mixed`, ★★★ `coneRemainderLaw_four_of_odd`,
★★ `coneRemainderLaw_four_of_evenRam`, `zeroConeClause_four_of_odd` ·
§6 ★★★ `decidedSliceAt_all_of_remainder5_even4_bridge` · AxCheck footer (14 lines).
Imports beyond IFCG26: `ChapI.IFCG30` (the §3b refinement).  Aggregator: one import
line in `Uniformity/ChapI.lean`.  Battery: `runs/wave-c/cca_battery.py`.

## Repair log (3 error rounds, all mechanical; every theorem landed as designed)

1. Law arithmetic: `field_simp` renormalized the ℕ exponent to `4*(M+4) − 6 + 6 − 6`
   (CRL repair #4 re-hit, new spelling) — closed with the omega-backed exponent `show`
   rewrite; note the leftover pattern is the PRE-normalized `w + 6 − 6` form, not CRL's
   `6 + (…) − 6`.
2. §3b: `rw [hgdeg, hGdeg]` left `2 * 1 = 2` unclosed under the instantiated `ℓ` — use
   `omega` on the two degree equations instead.
3. §3b: dot-notation `hRm.natDegree_eq_zero…` failed (the destructured `Monic` hypothesis
   surfaces unfolded as `leadingCoeff = 1`) — call
   `Polynomial.Monic.natDegree_eq_zero hRm` explicitly; the mathlib name at the pin is
   `Monic.natDegree_eq_zero` (no `_iff_eq_one` variant).

Traps AVOIDED by design (CN2/CN4/CRL/WFR/XHS logs consulted): all `fin_cases` goals
closed by defeq `exact` against literal-Fin facts extracted first (never omega on
mk-atoms); heights re-typed via `have hi' : … := hi` before omega; `faceH` membership by
`simp only [Finset.mem_filter]`, never `decide` on the Classical filter; `NPAttains`
second components closed by `rw` + `ring` (symbolic `t`); `forcedBox` spelled without a
`∀` so the carrier omega stays linear.
