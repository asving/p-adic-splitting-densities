# UNIT UZL — VERDICT: THE UNRAMIFIED ZERO-LAW CLOSED AT EVERY MASS — `ConeRemainderLaw m σ` (value 0) FOR EVERY m AND EVERY UNRAMIFIED σ, THE CENSUS FRONT RE-BASED TO RAMIFIED TYPES ONLY AT e ≥ 5 (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG33.lean` (358 lines, ZERO sorries, zero
warnings; 8 AxCheck footer lines — Lean core `{propext, Classical.choice, Quot.sound}`
on §1 (the wide-face lemma), and Lean core PLUS EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) on §§2–5; the C.33 cites do
NOT occur; no landed file touched except the sanctioned one-line aggregator import in
`Uniformity/ChapI.lean`; IFCG32 untouched; no git ops).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG33.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG33` green (8940 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE HEADLINE — CCA's recorded conjecture, PROVED (uniform in q, m, σ)

    theorem coneRemainderLaw_unramified (m : ℕ) {σ}
        (hunr : ∀ p ∈ σ.data, p.1 = 1) : ConeRemainderLaw m σ
    theorem zeroConeClause_unramified {m} (hm : 0 < m) {σ}
        (hunr : ∀ p ∈ σ.data, p.1 = 1) : ZeroConeClause m σ
    theorem decidedSliceAt_all_of_ram5_even4_bridge :          -- ★★★ the front re-based
      (∀ e ≥ 5, (smaller value laws) → ∀ σ deg-e Witnessed,
          (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ) →
      (∀ σ deg-4 Witnessed with an even-e member, ConeRemainderLaw 4 σ) →
      (∀ δ e ≥ 2, UnramifiedBlockBridge δ e) → ∀ n, DecidedSliceAt n

The unramified remainder count is IDENTICALLY ZERO at every finite level
(`coneRemainderCount_unramified : coneRemainderCount O m σ M = 0`), every mass, every
complete DVR, every uniformizer — so every `ConeRemainderLaw m σ` at unramified σ closes
AT ONCE, with value 0.  Combined with IFCG31, the census's remainder obligation is now:
at `e = 4` the FIVE even-ramification types; at `e ≥ 5` ONLY the genuinely RAMIFIED
types (`∃ p ∈ σ.data, p.1 ≠ 1`).

## ★★ THE MECHANISM (sharper than the conjectured route — no staircase induction)

CCA conjectured the closure via a wide-face generalization of WFR's
`staircase_not_shallow` (all-integer hulls force the deep box) plus a separate
visibility argument.  The landed proof needs NEITHER: §1's
`exists_visible_fracFace_of_shallow` (Lean-core) constructs the LAST HULL EDGE directly —

  take `j < m` minimizing `v_j/(m−j)` (the slope of the segment from `(j, v_j)` to the
  monic point `(m, 0)`); the support functional `Φ(i) = e'·v_i + h·i` at the lowest-terms
  slope `h/e' = v_j/(m−j)` has minimum `h·m`, attained at BOTH `j` and `m` — a
  `ClassNPFace c h e'`.  Shallowness (`∃ i₀, v_{i₀} < m−i₀`) forces the min slope `< 1`,
  i.e. `1 ≤ h < e'` — the face is FRACTIONAL (`e' ≥ 2`).  And slope `< 1` makes
  visibility AUTOMATIC: support `= h·m ≤ (e'−1)·m < e'·m ≤ e'·K` — the invisible corner
  (`v₀ = K`) needs no case split, because the deciding face never rides the ceiling.

Then CRL's `fracFaceForcesRam_of_stratum` (IFCG26 §3, already uniform in `m`) puts a
monic irreducible factor with `e' ∣ ramIndexOf` in EVERY lift (`forces_ram_of_shallow`),
and `e' ≥ 2 ∤ 1` kills every unramified decision (`not_decidedAt_unramified_of_shallow`).
NOTE the proof is STRONGER than the carrier needs: no unramified type is decided
ANYWHERE on stratum ∩ shallow — the pure faces need not even be subtracted.

## ★ THE ODD-e EXTENSION — the honest refutation + the generalizable half

The charge's conditional ("extend to all-odd-e σ if the m=4 mechanism generalizes"):
**it does NOT generalize as a zero law** — in-repo witness: IFCG31's
`coneRemainderCount_four_mixed` is `(q−1)q^(4K−6) + (q−1)q^(4K−9) ≠ 0` at the ALL-ODD
type `{(1,1),(3,1)}`.  The m=4 all-odd closure was VALUE-law-dependent (it needed the
decided sector's exact count via the `[1,4]`-side Hensel decision); at general mass the
decided odd-ram sector IS the remaining census.  The generalizable odd-half is landed
as the exclusion tool the even-ram successor consumes:

    theorem not_decidedAt_of_evenFace_of_odd :  -- IFCG31 §3's shape at EVERY mass
      2 ≤ e' → 2 ∣ e' → Coprime h e' → stratum → ClassNPFace c h e' →
      NPVisibleAt c h e' → (∀ p ∈ σ.data, ¬ 2 ∣ p.1) → ¬ DecidedAt O m σ K c

## THE EXACT SURVIVING OPEN SET (charge item 3 — the fence after this unit)

`DecidedSliceAt n` for all `n` now rests on precisely (via the new bridge):

1. **`ConeRemainderLaw e σ` at `e ≥ 5` for σ with SOME ramified part**
   (`∃ p ∈ σ.data, p.1 ≠ 1`) — this includes the odd-ram value-law types (the
   `{(1,1),(3,1)}`-analogues) and the even-ram types; the unramified members are GONE
   at every mass.  (The charge's guess "even-ram only at every mass" would additionally
   need the all-odd VALUE laws at each `e` — mass-specific decided-sector counts, i.e.
   the census recursion itself; not uniform content.)
2. **`ConeRemainderLaw 4 σ` at the five even-ramification types**
   `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`, `{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}` —
   unchanged from CCA (its §3b split leaf + the B.63/recursion genres).
3. **`UnramifiedBlockBridge δ e`** — CN5's family, another unit's, unchanged.

## File map (`leanfinal/Uniformity/ChapI/IFCG33.lean`, 358 lines)

§1 ★★ `exists_visible_fracFace_of_shallow` (Lean-core) · §2 ★ `forces_ram_of_shallow`,
★ `not_decidedAt_unramified_of_shallow`, `not_decidedAt_of_evenFace_of_odd` ·
§3 `coneRemainderCount_unramified` · §4 ★★★ `coneRemainderLaw_unramified`,
★★ `zeroConeClause_unramified` · §5 ★★★ `decidedSliceAt_all_of_ram5_even4_bridge` ·
AxCheck footer (8 lines).  Imports: IFCG26 + IFCG31.  Aggregator: one import line in
`Uniformity/ChapI.lean` (after IFCG31; IFCG32's slot left to its unit).

## Repair log (1 error round + 1 deprecation, both mechanical)

1. `div_le_div_iff` does not exist at the pin — the mathlib name is `div_le_div_iff₀`
   (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1430`); one-token fix.
2. `push_neg` is deprecated at the pin (warns, suggests `push Not`) — replaced by a
   direct `by_contra` witness assembly; zero-warning landing.

Traps AVOIDED by design (CCA/WFR logs consulted): all products kept out of `omega`
(explicit `calc` chains with `Nat.lt_of_mul_lt_mul_left` / `Nat.le_of_mul_le_mul_left`
and gcd-multiplied equalities `g·h = v_j`, `g·e' = m−j`); the argmin taken in ℚ via
`Finset.exists_min_image` then cross-multiplied into ℕ ONCE (`div_le_div_iff₀` +
`exact_mod_cast`); coprimality via `Nat.gcd_mul_left` cancellation (no
`coprime_div_gcd_div_gcd` div-juggling); `npHeight` reads via `npHeight_coe` +
`simpa` at `⟨i, hlt⟩`; set-membership negations by `rintro` under `iff_false`
(IFCG31's pattern), never `not_and` reshaping.
