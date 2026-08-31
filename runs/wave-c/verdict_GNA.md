# UNIT GNA — VERDICT: **LANDED, SORRY-FREE** (2026-08-31)

**Charge:** the general-`n` diagonal assembly — (i) the `n`-ary stratum convolution over
DGT's binary step, (ii) the factorization-type grouping with necklace-count fibers,
(iii) the exact general census + the depth-density `ZcURLim` at EVERY `(n₁, n₂)` —
**VCL's axis 1 closes entirely.**
**File:** `leanfinal/Uniformity/ChapI/IFCG70.lean` (1069 lines; registered in
`Uniformity/ChapI.lean` after IFCG69).
**Verification:** `lake env lean Uniformity/ChapI/IFCG70.lean` exit 0, zero
errors/warnings; `lake build Uniformity.ChapI.IFCG70` green (8971 jobs); grep sorry = 0;
**all 9 AxCheck footer rows PURE Lean core `[propext, Classical.choice, Quot.sound]`** —
no sorryAx, no B.42/C.33/AX_cellRecursion.

## What is now proved (all uniform in `q`, `n`, `v`, and the window; no division in ℕ-land)

1. **§0 `primoPoly` + `primo_cast`** — the `ℚ[X]` mirror of IFCG65's `primo` recursion
   (same well-founded recursion, `X^a − X^{a−δ}` monomial differences):
   `primo q δ e v = (primoPoly δ e v).eval q` for every `q ≥ 1`.  The primary census
   values are polynomials in `q`, at every `(δ, e, v)`.
2. **§1 ★ THE `n`-ARY FOLD** `card_stratumDepthSet_prod`: for any finite family of
   pairwise-coprime monic residual factors of positive degree with per-factor normalized
   laws `V i`, the stratified census at the product residual is
   `coeff_v` of the `PowerSeries ℕ` PRODUCT `∏ mk (V i)` — one `Finset` induction over
   DGT's binary `card_stratumDepthSet_mul`, carrying the exact multiplied normalization
   `q^{v+Σdᵢ} ↔ q^{(Σdᵢ)(2N−1)}`.  The convolution's commutativity/associativity are the
   ring axioms of `PowerSeries ℕ` — no bespoke convolution algebra.
3. **§2 the per-shape general value** `card_stratumDepthSet_eq_patRate`: every monic
   degree-`n` residual `g` = product of its primary parts `p^{count p}` (pairwise coprime
   via `Irreducible.coprime_iff_not_dvd` + monic-associated-equal); the fold +
   `card_stratumDepthSet_pow` give
   `#strat(n,N,v,g)·q^{v+n} = coeff_v (patRate q (patternOf g))·q^{n(2N−1)}`, with
   `patRate q λ := (λ.map ((δ,e) ↦ mk (primo q δ e ·))).prod`.
4. **§3 ★ THE FIBER-COUNT POLYNOMIAL** `exists_fiberPoly`: `#{monic deg-n g : patternOf
   g = λ, avoiding A}` depends on the finite field only through `q` and the per-degree
   avoidance profile — a `ℚ[X]` value, by multiset induction on `λ` through IFCG17's
   landed double count `sum_sigma_fiber_eq` (at `F ≡ 1`) + IFCG19's
   `necklacePoly_eval_card`.  The necklace-multinomial bookkeeping falls out of the
   recursion `(count+1)·#fiber(λ) = (I_δ(q) − a_δ)·#fiber(λ∖(δ,e), profile+1_δ)` — no
   explicit multinomials anywhere.  (Weight bookkeeping: fibers off `Σδe = n` are empty.)
5. **§4 ★★ THE GENERAL DIAGONAL CENSUS** `card_redDepthPairSet_general`:
   `#redDepthPairSet(n,N,v)·q^{v+n} = zed(K,n,v)·q^{n(2N−1)}` for `v < N`, where
   `zed K n v := Σ_{g ∈ monicFinset K n} coeff_v (patRate q (patternOf g))` — IFCG63's
   shape partition reindexed along `monicPoly` (field-usable coefficient-vector bridge
   restated privately; IFCG17's is DVR-scoped).  Exact at every level.
6. **§5 the polynomiality**: `Zpoly n v := Σ_{λ ∈ patternUniverse n} fiberPoly λ n ·
   patNum λ v` with `zed_cast : zed K n v = (Zpoly n v).eval (#K)` — the type grouping
   over the fixed finite `patternUniverse n` (sub-multisets of `n • ([1..n]×[1..n])`),
   fibers by §3, per-pattern convolution cast by §0 through two `PowerSeries.map` ring
   homs (`ℕ-cast` and `evalRingHom q`).
7. **§6 ★★★ `zcURLim_redDiag (n v : ℕ)`** — the reduced diagonal density `ZcURLim` at
   EVERY `n` (witness `(Zpoly n v, X^{v+2n})`; the `1 ≤ n` hypothesis turned out
   unnecessary and was dropped — statement strengthened, never weakened); then
   **`zcURLim_depthDensity (h1 : 0 < n₁) (h2 : 0 < n₂) (v)`** through IFCG61's transport
   + swap — **the depth-density `ZcURLim` at ALL `(n₁, n₂ ≥ 1)`, unconditional**.
   Lean-internal cross-check: the `(2,2)` instance IS NA22's
   `zcURLim_depthDensity_two_two` statement verbatim (compiled `example`).
8. **§7 ★ the regression** `two_mul_zed_two : 2·zed(K,2,v) = duo(#K, v)` — the general
   patternOf-grouped assembly collapses exactly to NA22's independently-derived duo law
   (genre patterns `{(2,1)}`, `{(1,2)}`, `{(1,1),(1,1)}` computed; NA22's public
   trichotomy + doubled counts fired; the two private partition lemmas of IFCG68
   re-derived locally since private).  NA22's five battery-verified IGV `Z₂` rows are
   inherited verbatim.

## Honest remainders / notes

- `n₁, n₂ ≥ 1` in the final theorem: the `n = 0` box is degenerate and outside VCL's
  axis (the transport itself requires `0 < min`); the reduced diagonal `ZcURLim` is
  proved for `n = 0` too.
- `Zpoly n v` is not computed in closed form (IGV's `Z_m(t)` is the predicted closed
  form); no closed form is needed for the `ZcURLim`, and `fiberPoly` is choice-defined,
  so an `n = 3` NUMERIC spot value is not `#eval`-able — the `n = 2` collapse (§7) is
  the pipeline regression instead, and it is exact over every finite field, not spot
  values.  A future display unit can derive closed `Zpoly` rows from `exists_fiberPoly`'s
  recursion if wanted.
- The fiber-polynomial layer is stated at `K : Type` (universe pinned — `choose` needs a
  closed existential); the census carrier `ResidueField O` lives there since `ZcURLim`
  quantifies `O : Type`.  `zed`/census/regression remain universe-polymorphic.
- Aggregator: `import Uniformity.ChapI.IFCG70` added after IFCG69 (IFCG69 itself
  untouched, per charge).

## Notes for the record (what made it land fast)

- **PowerSeries-as-convolution**: making the `n`-ary convolution literally
  `Multiset.prod` in `PowerSeries ℕ` (and `PowerSeries (Polynomial ℚ)` for the mirror)
  eliminated every commutativity/associativity obligation; the truncation-window subtlety
  (laws valid only for `v < N`) is absorbed by ONE Finset induction that carries the
  normalization, instead of an agreement-below-N calculus.
- **The ∃-form fiber polynomial with the bounds hypothesis INSIDE the conclusion** keeps
  `Exists.choose` total, so `Zpoly` is a plain `Finset.sum` of chosen polynomials.
- 9/9 majors landed within ~3 repair rounds each (most first-attempt); the only genuine
  traps: this pin's hypothesis-free `Finset.card_sdiff` (inter form), `rcases`-`rfl`
  eating the `n` binder, and `rw [Finset.sum_mul]` needing `conv_rhs`.
