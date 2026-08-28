# VERDICT — UNIT A0G4: nodes A0G-RS and A0G-FP (2026-08-28)

**HEADLINE: BOTH NODES LANDED, sorry-free, Lean-core.** `leanfinal/Uniformity/ChapI/IFCG3.lean`
(510 lines, NEW) proves the generic `X = πY` rescale loop with a fully characteristic-free
bijection (A0G-RS) and the generic scalar fixed-point solver with an equality strengthening
and an explicit uniqueness lemma (A0G-FP). Verified: `lake env lean Uniformity/ChapI/IFCG3.lean`
— zero errors, zero `sorry`. The AxCheck footer prints, for all 20 declarations,

```
axioms: [propext, Classical.choice, Quot.sound]   -- Lean core only
```

No landed file touched; every landed name (`IFCG1.shiftVecN`/`MBoxN`/`mtruncN`/`mkBoxN` +
cardinalities, `TypeOfInvariance.typeOf_scaleRoots`, `Induction.resSect`, `IFC7.resOut`,
`Hensel.sub_mem_coeffIdeal_maximalIdeal_iff`, `GenuineDensity.decidedSeq_tendsto`) is consumed
as-is.

## Node A0G-RS — the generic rescale loop

* `scaleVecN π f := fun i => π^(m−i) · f i` and `loopVecN π d` (extracting a box
  `d : IFCG1.MBoxN O m M` through a canonical lift) — `monicPoly (scaleVecN π f) =
  (monicPoly f).scaleRoots π` (`monicPoly_scaleVecN_eq_scaleRoots`), so the diagonal
  `typeOf`-preservation (`typeOf_scaleVecN`) is a one-line consequence of the LANDED
  `typeOf_scaleRoots`.
* `loopMapN γ π d := shiftVecN (loopVecN π d) (resSect O γ)` — recentre at a lift of the
  residue centre, then rescale.
* **THE GENERIC LOOP BIJECTION** (`loopMapN_inj`): injective jointly in `γ` AND `d`, at every
  `m ≥ 1`, over every complete DVR with finite residue field, in **every residue
  characteristic** — no wild-prime exclusion. The γ-recovery step is NOT binomial-coefficient
  inversion (which fails whenever `p ∣ m`, e.g. `C(m,1) = m ≡ 0`): it is a single
  characteristic-free polynomial evaluation, `addC_pow_injective`, proved by evaluating
  `(X+Cγ)^m = (X+Cγ')^m` at `X = −γ` to get `(γ'−γ)^m = 0`, hence `γ = γ'` in any field (any
  domain kills `x^m = 0 ⟹ x = 0` regardless of characteristic). The residue-field reduction
  identity feeding this (`map_residue_monicPoly_loopMapN : (monicPoly (loopMapN γ π d)).map
  (residue O) = (X+Cγ)^m`) goes through the general congruence lemma
  `map_residue_monicPoly_congr`, built on `Hensel.sub_mem_coeffIdeal_maximalIdeal_iff`
  (`leanfinal/Uniformity/HenselFactorization.lean`, an existing general-local-ring utility —
  no new cite).
* `decidedAt_of_loopVecN` / `decidedAt_of_loopMapN`: the loop transports `DecidedAt` from
  level `M` to level `M+m`, so the mechanism is genuinely tied to the campaign's
  decided-density semantics, not just an abstract bijection.
* **The two weight formulas** (A0 plan §3.2): `kappaLoop m = m(m−1)/2` and
  `bigTLoop m = m(m+1)/2`, with `bigTLoop_eq_kappaLoop_add : T_m = κ_m + m` and
  `kappaLoop_add_bigTLoop : κ_m + T_m = m²` (both by Gauss-sum identities, no `Nat`-division
  case bashing). `card_MBoxN_kappaLoop` / `card_preimage_mtruncN_kappaLoop` are direct
  renamings of the just-landed `IFCG1.card_MBoxN` / `card_preimage_mtruncN_eq` — the
  "coefficient loss" is *exactly* IFCG1's excess exponent, not a new computation.
  `loopVecN_weight` is the NEW cardinality identity (subtraction-free form of "the full-box
  loop weight is `q^(1−T_m)`"):
  ```
  #(range of the scale-loop mod π^(M+m)) · q^(T_m) = q^(m(M+m))
  ```
  proved from `loopVecN_inj` (`Nat.card_range_of_injective`) plus `IFCG1.card_MBoxN`.
* **Gate — machine numeral pins**: `kappaLoop_two : κ_2 = 1`, `kappaLoop_three : κ_3 = 3`,
  `kappaLoop_four : κ_4 = 6` (all `by decide`).
* **Gate — the IFC7 recovery**: `bigTLoop_three_recovery : (1:ℤ) − T_3 = −5`, i.e. `T_3 = 6`
  reproduces exactly `IFC7.density_ge_of_step`'s hard-coded `q⁻⁵` as the `m = 3` instance of
  the general `q^(1−T_m)` weight.

## Node A0G-FP — the generic scalar fixed-point solver

* `fixedPoint_unique {y b D D'} (hy : y ≠ 1) : D = b+y·D → D' = b+y·D' → D = D'` — the pure
  algebra behind "the affine recurrence has a unique fixed point," stated and proved as its
  own theorem (not just inlined into the density argument).
* `decidedDensity_ge_of_step` — generalizes `IFC7.density_ge_of_step` from the hard-coded
  shift `3` / exponent `5` to an arbitrary shift `s` and exponent `d > 0`, at an arbitrary
  degree `n` (already generic in the landed `GenuineDensity.decidedSeq_tendsto`): given
  `bs → b` and `∀M, bs M + q⁻ᵃ·decidedSeq n σ M ≤ decidedSeq n σ (M+s)`, concludes
  `b·qᵃ/(qᵃ−1) ≤ decidedDensity O n σ`.
* `decidedDensity_eq_of_step_eq` — **the equality strengthening** ("direct equality at the
  decided-density limit"): same hypotheses but with the step as an EXACT equality, concludes
  `decidedDensity O n σ = b·qᵃ/(qᵃ−1)` on the nose (via `tendsto_nhds_unique`, since both
  sides of the recurrence tend to the same limit along the same filter).
* **Gate — no `DrainageAt`**: neither theorem, nor any lemma in this file, mentions
  `DrainageAt`/`genuineDensity_eq_of_drainage`; everything stays on `decidedDensity`/
  `decidedSeq` directly, per the row's mandate.
* **Gate — denominator positivity from `q ≥ 2`**: `qᵃ − 1 > 0` is derived solely from
  `two_le_residueCard` (`q ≥ 2`) and `d > 0` (via `one_lt_pow₀`), exactly as in IFC7's model
  proof — no drainage, no separate density axiom.

## What this does NOT claim

Neither node asserts a real recurrence for any actual `FactorizationType` — that needs the
still-open genre classification (A0G-GC/RW), explicitly out of scope for A0G-RS/A0G-FP. The
solvers here take the step hypothesis as a HYPOTHESIS (exactly mirroring IFC7's
`density_ge_of_step`, which does the same); the loop bijection is a mechanism lemma, not a
disjointness-with-other-strata theorem (that belongs to A0G-GC2/CH). Both are honestly scoped
to what the blueprint rows ask for.

## Build

```
cd leanfinal && lake env lean Uniformity/ChapI/IFCG3.lean
```
Zero errors. `#print axioms` for all 20 declarations: `[propext, Classical.choice, Quot.sound]`.
