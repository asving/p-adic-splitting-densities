# UNIFORMITY_WIRING_BLUEPRINT — re-basing the across-primes uniformity capstone on the Montes counting model

**Date:** 2026-06-30. **Status:** READ-ONLY design (no `.lean` edited, no `lake` run).
**Scope of files read:** `LeanUrat/Goal.lean` (`goal_theorem`, `goal_theorem_montes`,
`countingDensity_eq_sum_coeff` consumer), `LeanUrat/Interface.lean` (`DensityFoundation`,
`OMBridge`, `clusterVolume_rational`, `tame_functionalEquation`, `IsPalindromic`),
`LeanUrat/OM/RealInstance.lean` (`montes_unconditional`, `realM`/`realD`/`realF`, `realP`,
`decode`), `LeanUrat/Decomposition.lean` (`coeff`, `coeff_isRational`,
`countingDensity_isRational`, `countingDensity_eq_sum_coeff`, `wiring_assessment`),
`LeanUrat/L6M4.lean` (`density_rational`, `sum_clusterVol_rational`), `LeanUrat/L7.lean`
(`tame_to_all_primes`, `isPalindromic_of_agree`, `ratfunc_agree_of_infinite`),
`LeanUrat/CountingModel.lean` (`countingDensity`, `density_isLimit`), plus notes
`MONTES_DISCHARGE_STATUS.md`, `GOAL_ONLY_MONTES.md`, `BLUEPRINT_clusterVolume.md`,
`HUMAN_PROOF.md`, and the two graph files `viz/{montes,uniformity}_established.json`.

---

## 0. TL;DR (the bridge in one paragraph)

The wiring is **already substantially built into the codebase**: `Goal.goal_theorem_montes`
is the de-axiomatized sibling of `Goal.goal_theorem`. It produces the *same* uniform-rational +
palindromic conclusion — `∃ num den, den ≠ 0 ∧ (∀ q' > 1, den(q') ≠ 0 ∧ ⟨density family⟩ = num(q')/den(q')) ∧ IsPalindromic num den` —
but its rationality flows through `MontesData.countingDensity_isRational` (Lean-core + the
`MontesData` hypothesis bundle ONLY: NO `clusterMeasure`, `AX_cellRecursion`, `omCells`,
`descend_size_lt`), instead of through `L6M4.density_rational → clusterVolume_rational →
PadicMeasure`. Its footprint is `[propext, Classical.choice, Quot.sound, tame_functionalEquation]`,
exactly the OLD footprint **minus the four measure axioms**. The Montes capstone
`montes_unconditional` fires `goal_theorem_montes` non-vacuously (`realF.density := g_σ`, so the
`hbridge` is `rfl`). **So the de-axiomatization is real and machine-verified.** The single genuine
residual is that the Montes value-identification is pinned to the prototype prime `q = realP = 2`
(the unramified-core residue cardinality), so the *number* `countingDensity` is tied to `num/den`
only at `q = 2`; the **uniform-rational `∀ q'` clause and the palindromy are already fully general
across all prime powers** (that is the across-primes content, and it is NOT pinned). The hardest
honest step is therefore the **measure-wall identification** `hbridge` — that an abstract
`DensityFoundation`'s density equals the count-native OM tree-sum at every residue cardinality —
which is the un-constructed `p`-adic Haar foundation absent from mathlib v4.31.0.

**Verdict (anticipating §8):** wiring is a **clean footprint de-axiomatization** of the
*rationality + palindromy structure* (the four measure axioms genuinely drop), but it does **not**
make the all-primes statement about the paper's real `ρ` unconditional — the same measure wall
(now named `hbridge` / the `q=realP` value pin) remains, just relocated and surfaced honestly as a
hypothesis rather than buried in `clusterMeasure`/`AX_cellRecursion`.

---

## 1. The two capstones, side by side

### 1a. EARLIER uniformity capstone (`LeanUrat/Goal.lean:85`)

```lean
theorem goal_theorem
    (F : DensityFoundation) (B : OMBridge F) (n : ℕ) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧
        F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      IsPalindromic num den
```
- **Rationality half:** `L6M4.density_rational F B n σ hσ`, which uses
  `DensityFoundation.decomposition` (the L1/cluster-tree structural sum
  `density = ∑_T m_T(q)·clusterVolume T q`) and `Interface.clusterVolume_rational F B` (per-SHAPE
  volume rational, now a THEOREM that transports `PadicMeasure.clusterMeasure_isRational_of_AX`
  along the OM bridge `B`).
- **Palindromy half:** `tame_functionalEquation` + `L7.tame_to_all_primes` (ℚ(t) identity theorem
  over the infinite tame-prime set) + `L7.isPalindromic_of_agree`.
- **Footprint** (verified, `GOAL_ONLY_MONTES.md`, `uniformity_established.json`):
  `{propext, Classical.choice, Quot.sound, tame_functionalEquation, AX_cellRecursion,
  clusterMeasure, descend_size_lt, omCells}`.
- **Honest scope:** `∀ F` over an INHABITED (`Witness.DensityFoundation_nonempty`) but
  not-identified-with-real-`ρ` foundation; the `p`-adic Haar identification is the un-crossed
  measure wall.

### 1b. NEW Montes-route GOAL theorem (`LeanUrat/Goal.lean:149`)

```lean
theorem goal_theorem_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesAxiom.MontesData q n M)
    (σ : FactorizationType) (F : DensityFoundation) (hσ : σ.degree = n)
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q') :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ D.shapesOf σ, D.coeff T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      IsPalindromic num den
```
- **Rationality half:** `D.countingDensity_isRational σ` (Decomposition.lean:185) —
  `IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q')`, derived through the GENERIC engine
  `OMInduction.clusterVol_isRational` over `ClusterShape` with count-native
  `cells`/`treeSize`/`countCellCoeff`/`countPivot`. **No measure layer.**
- **Value tie:** `D.countingDensity_eq_sum_coeff σ` (Decomposition.lean:104): the genuine decided
  limit `M.countingDensity σ` equals `∑_T D.coeff T q` at THIS model's `q` (limit-uniqueness, NOT a
  tautology, `hbridge`-FREE).
- **Palindromy half:** SAME L7 machinery; `hbridge` carries `tame_functionalEquation`'s palindromy
  onto the count-native `num/den` (the `hF` step inside `goal_theorem_montes`).
- **Footprint** (verified, `GOAL_ONLY_MONTES.md`):
  `{propext, Classical.choice, Quot.sound, tame_functionalEquation}` — Lean core + the cited tame
  input only; `M`/`D`/`F`/`hbridge` are HYPOTHESES, not axioms.

### 1c. Montes capstone (`LeanUrat/OM/RealInstance.lean:836`)

```lean
theorem montes_unconditional (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ (realD n σ hσ (real_h_node n)).shapesOf σ,
            (realD n σ hσ (real_h_node n)).coeff T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (1 < realP → (realM n σ hσ (real_h_node n)).countingDensity σ
          = num.eval (realP : ℚ) / den.eval (realP : ℚ)) ∧
      IsPalindromic num den :=
  Goal.goal_theorem_montes (realM n σ hσ (real_h_node n))
    (realD n σ hσ (real_h_node n)) σ
    (realF n σ hσ (real_h_node n)) hσ (fun _ _ => rfl)   -- hbridge by rfl
```
- Fires `goal_theorem_montes` at the REAL `(realM, realD, realF)` with `q := realP := 2`.
- Non-vacuous: `realClassify := B.classify realP n`, `shapeMenu n` proven non-empty
  (`shapeMenu_nonempty`), `realF.density := g_σ` so `hbridge` is `fun _ _ => rfl`.
- `h_node` is now the THEOREM `real_h_node` (MERGE round); the other capstone hypotheses are
  discharged by the named GMN/Hensel cites `decidedDensity_mono_realP`, `discZeroValTail_density`,
  `selfLoop_childFiber_corrected`, `boxVolumeScale_collapse`.
- **Footprint (per `MONTES_DISCHARGE_STATUS.md` 2026-06-30 build):** `[propext, Classical.choice,
  Quot.sound, tame_functionalEquation]` (the named CITE axioms `decidedDensity_mono_realP`,
  `discZeroValTail_density`, `selfLoop_childFiber_corrected`, `boxVolumeScale_collapse` and the
  `h_node` cites enter once `real_h_node` is the theorem-route; the authoritative `#print axioms`
  reported the clean four-symbol footprint). **No `sorryAx`.**

---

## 2. The EXACT bridge: which Montes statement supplies what `goal_theorem` consumes

`goal_theorem`'s rationality is `L6M4.density_rational`, which requires for `F`, `B`, `n`, `σ`:

```lean
∃ num den, den ≠ 0 ∧ ∀ q, 1 < q → den.eval q ≠ 0 ∧ F.density n σ q = num.eval q / den.eval q   -- (R)
```

The Montes side supplies precisely this shape, but for the COUNT-NATIVE density family
`g_σ := fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q'`:

```lean
-- Decomposition.lean:185
theorem MontesData.countingDensity_isRational (σ) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q')
-- unfolds (IsRationalFn, RatFn.lean) to:
--   ∃ num den, den ≠ 0 ∧ ∀ q', 1 < q' → den.eval q' ≠ 0 ∧ g_σ q' = num.eval q' / den.eval q'  -- (R-Montes)
```

**The bridge lemma that converts (R-Montes) into (R) is the function equality**

```lean
hbridge : ∀ q' : ℕ, 1 < q' → F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q'
```

i.e. `F.density n σ = g_σ` on prime powers. Given `hbridge`, the substitution `(R-Montes) → (R)` is
one `rw [hbridge q' hq']` (this is exactly the `hF` block inside `goal_theorem_montes`,
Goal.lean:182-186). The palindromy half is UNCHANGED — both capstones run the identical
`L7.tame_to_all_primes`/`isPalindromic_of_agree` on the same `num/den` against the tame
representative.

So **`MontesData.countingDensity_isRational` is the statement that supplies `goal_theorem`'s
density-rationality**, and **`hbridge` is the single bridge connecting it to `F.density`**. The
decomposition tie `MontesData.countingDensity_eq_sum_coeff` additionally connects the genuine decided
limit `M.countingDensity σ` to that rational function's value at `q`.

### 2a. Mapping the interface fields to Montes objects (the `Decomposition.wiring_assessment` ledger)

| `goal_theorem` consumes (interface) | Montes object that discharges it | mechanism |
|---|---|---|
| `F.density n σ q` (the per-type density) | `g_σ(q) = ∑_T D.coeff T q` | `hbridge` (function equality) |
| `DensityFoundation.decomposition` (`density = ∑_T m_T·clusterVolume`) | `countingDensity_eq_sum_coeff` (`countingDensity = ∑_T coeff`), with `m_T ≡ 1`, `clusterVolume T := coeff T` | DERIVED (limit-uniqueness theorem) |
| `Interface.clusterVolume_rational` (per-shape `C_T` rational, via `clusterMeasure`/`AX_cellRecursion`) | `coeff_isRational` (per-shape `D.coeff = D.C` rational, via the GENERIC `OMInduction.clusterVol_isRational` over `ClusterShape`) | REPLACED — count-native, NO measure layer |
| `L6M4.density_rational` (finite-sum closure) | `countingDensity_isRational` (`RatFn.isRationalFn_listSum`) | REPLACED |
| `tame_functionalEquation` (H-tame palindromy) | SAME (`tame_functionalEquation`) | UNCHANGED (kept; not Montes) |
| `L7.tame_to_all_primes` + `isPalindromic_of_agree` | SAME | UNCHANGED |

In `realF` the interface fields are instantiated count-natively (RealInstance.lean:709-726):
`density := g_σ`, `clusterVolume T := realD.coeff T`, `shapes := realD.shapesOf`,
`multiplicity := 1`, `decomposition := by simp` (`g_σ` IS the sum, so the decomposition is a
beta-reduction), `density_nonneg := clusterCount_nonneg`. The `OMBridge B` is NOT supplied (it is
dropped — that is the whole point: `realF` carries NO `clusterMeasure`).

---

## 3. Can `goal_theorem` be re-based on `goal_theorem_montes`?

**Yes, at the level of producing the identical conclusion — but the right move is NOT to literally
edit `goal_theorem`'s body.** Three options, in increasing scope:

### Option A (DONE, the existing state): keep both theorems, route the capstone through Montes
This is what the codebase already does. `goal_theorem` (measure route) is kept as the historical
derivation; `goal_theorem_montes` is the only-Montes sibling; `montes_unconditional` fires the
latter. The across-primes uniformity *result the project wants* is now reachable with the thin
footprint via `goal_theorem_montes`. **No further wiring is required for the footprint claim.**

### Option B (clean de-axiomatization of the OLD signature): re-prove `goal_theorem` from `goal_theorem_montes`
Produce a new bridge lemma that yields `goal_theorem`'s EXACT conclusion (with the `F.density`
clause) from the Montes side, given a coupled `(M, D)` and `hbridge`. Proposed signature:

```lean
-- proposed: LeanUrat/Goal.lean (new), or a wiring module
theorem goal_theorem_via_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesAxiom.MontesData q n M)
    (F : DensityFoundation) (σ : FactorizationType) (hσ : σ.degree = n)
    (hbridge : ∀ q' : ℕ, 1 < q' → F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q') :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        F.density n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧   -- ← OLD goal_theorem's F.density clause
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hgrat, _hval, hpalin⟩ := goal_theorem_montes M D σ F hσ hbridge
  refine ⟨num, den, hden, fun q' hq' => ?_, hpalin⟩
  obtain ⟨hdenq', hgeq⟩ := hgrat q' hq'
  exact ⟨hdenq', by rw [hbridge q' hq', hgeq]⟩   -- F.density = g_σ = num/den
```
- This has the EXACT shape of `goal_theorem`'s conclusion (the three-conjunct
  `den≠0 ∧ ∀q'>1(…) ∧ IsPalindromic`), but takes `(M, D, hbridge)` in place of `(B : OMBridge F)`.
- Footprint: `{propext, Classical.choice, Quot.sound, tame_functionalEquation}` — the four measure
  axioms are GONE.
- It is essentially `goal_theorem_montes` with the value-clause dropped and the rationality clause
  rewritten through `hbridge`. **Grade [NOW]** — it is a 5-line proof from the existing
  `goal_theorem_montes`.

`goal_theorem`'s old signature `(F)(B : OMBridge F)` CANNOT be kept verbatim while dropping the
measure axioms, because `OMBridge F` and `clusterVolume_rational F B` are exactly what drag
`clusterMeasure`/`AX_cellRecursion` in. The re-based theorem must swap `(B : OMBridge F)` for the
`(M, D, hbridge)` triple. So "re-base `goal_theorem` on `goal_theorem_montes`" = "introduce
`goal_theorem_via_montes` with the swapped antecedent; deprecate the `OMBridge` route."

### Option C (full unconditional all-primes `ρ`): construct the coupled real witness with all-q value
Requires the un-constructed `p`-adic Haar foundation (the genuine measure wall). **Out of reach in
mathlib v4.31.0.** See §6.

---

## 4. What genuinely DIFFERS: the prototype-`q` vs all-`q` question

This is the crux of the honest assessment. Decompose the conclusion into its three clauses:

1. **Uniform-rational `∀ q'` clause:**
   `∀ q' > 1, den(q') ≠ 0 ∧ g_σ(q') = num(q')/den(q')`.
   This is about the COEFFICIENT FUNCTION `g_σ : ℕ → ℚ` as a function of a FREE variable `q'`. It is
   proved by `countingDensity_isRational`, which is FULLY GENERAL (the engine
   `OMInduction.clusterVol_isRational` and `RatFn` closure say nothing about a particular prime). It
   ranges over **every prime power `q' > 1`, wild included.** **This IS the across-primes uniformity
   content, and it is NOT pinned to `realP`.** The wild-prime mechanism is genuinely live: the BB3
   residual count `countCellCoeff` carries `(q'^δ)^{dS-1}` (a non-constant monomial in `q'`), so
   `num` genuinely `q'`-varies (cf. `residualCountFn_isRational`, the `X^{δ(d-1)}` numerator).

2. **Value clause:** `1 < q → M.countingDensity σ = num(q)/den(q)`.
   In `montes_unconditional` this is `q := realP = 2`, so it reads
   `1 < 2 → realM.countingDensity σ = num(2)/den(2)`. This is the ONLY place the prototype prime
   enters. It ties the single GENUINE decided-limit number `realM.countingDensity σ` (at the
   unramified-core residue cardinality `q = p^{f_K}`, instantiated to `2`) to the value of the
   already-all-`q` rational function at `q = 2`.

3. **Palindromy:** `IsPalindromic num den` — the functional equation `R(1/t) = R(t)` of the SAME
   `num/den`. Proved via L7 over the infinite tame-prime set. **Fully general** (it is a property of
   the rational function, not of a prime).

**So the "prototype `q = realP = 2`" pin is confined to clause (2).** Clauses (1) and (3) — the
uniform-rational-across-all-primes structure and the palindromic functional equation — are exactly
the across-primes uniformity result the project wants, and they are **not** restricted to `q = 2`.

### 4a. Why the pin exists (and why it is a re-parametrization, not a weakening)
Per `HYPS2_BLUEPRINT.md`/`MONTES_DISCHARGE_STATUS.md`: the box `monicBox(realP, N, n)` is built at the
fixed prime `realP = 2`, but the stratum count is normalized by `q^{nN}`. Two of the discharged
hypotheses are FALSE at free `q > 2` with a `realP=2` box:
- `decided_mono` (cylinder monotonicity): bulk ratio `(2/q)^n < 1` ⇒ eventually decreasing for
  `q > 2`; TRUE only when box prime = normalization prime, i.e. `q = realP`.
- `h_env` (disc-tail decay): the same matched-prime requirement.

These gate only the value clause (2) (they are about `M.countingDensity`, the decided LIMIT at this
model's `q`). They do NOT touch the rational function `g_σ` (clause 1) or its palindromy (clause 3).
The genuine intended instance is the unramified core `q = p^{f_K} = realP`, so pinning `q := realP`
is the correct re-parametrization for the SINGLE-NUMBER value tie, not a restriction of the uniform
statement. **The free-`q` value tie (Montes density at q'≠ box-prime) is genuinely not available
from this single fixed-box model; it would need a per-prime family of boxes — see §6.**

### 4b. How the cross-prime / `q`-uniformity assembles (the answer to "how does q=2 connect to all-primes")
It does NOT need to "connect": the all-primes uniform-rationality is proved *directly* as clause (1),
independently of any single prime, by the count-native engine. The role of `q = realP` is only to
exhibit ONE genuine density value sitting on the curve `num/den`. The cross-prime interpolation that
the EARLIER proof needed (tame primes → wild primes via the ℚ(t) identity theorem) is STILL the
mechanism that delivers palindromy (clause 3): `tame_functionalEquation` gives a palindromic tame
representative `tnum/tden` agreeing with `num/den` at the infinitely many tame primes `p > n`;
`L7.tame_to_all_primes` forces `num·tden = tnum·den` in ℚ(t); `L7.isPalindromic_of_agree` transfers
palindromy to `num/den`, hence to ALL primes including wild. **The tame functional equation is shared
verbatim between the two routes** — it is the same `Interface.tame_functionalEquation` axiom and the
same L7 lemmas. So the wild-prime interpolation is unchanged by the rewire.

---

## 5. The combined footprint after wiring

Re-basing the across-primes uniformity capstone on the Montes route (Option A as-built, or Option B
`goal_theorem_via_montes`) yields:

```
{ propext, Classical.choice, Quot.sound, tame_functionalEquation }
```
plus, IF the capstone is the concrete `montes_unconditional` (which discharges its own hypotheses via
named cites), the additional named CITE axioms that enter through `real_h_node` and the value-clause
discharge:
```
{ decidedDensity_mono_realP, discZeroValTail_density,        -- value-clause cites (GMN §4/§5 + Hensel)
  selfLoop_childFiber_corrected, boxVolumeScale_collapse }   -- h_node (box-additive limit) cites (GMN §3 + A3)
```

**Dropped relative to the OLD `goal_theorem` footprint:**
```
{ AX_cellRecursion, clusterMeasure, descend_size_lt, omCells }   -- the entire measure layer
```

**Net:** the abstract-`goal_theorem_montes` footprint is the cleanest:
`{propext, Classical.choice, Quot.sound, tame_functionalEquation}` — Lean core + one cited tame
literature axiom. The four measure axioms are genuinely gone (verified by per-theorem `#print axioms`
in `GOAL_ONLY_MONTES.md`; the diff against `goal_theorem` is exactly those four). The remaining
non-core axioms are all named literature CITEs (GMN / Hensel / paper §5), none is `sorryAx`, none is
a conclusion-axiom.

---

## 6. The honest residual (the genuine gap that remains)

The wiring de-axiomatizes the *footprint* but does NOT make the all-primes statement about the
paper's real `ρ` unconditional. The residual is the **measure-wall identification**, in two
equivalent guises:

1. **`hbridge` (abstract sibling).** `goal_theorem_montes` takes
   `hbridge : ∀ q' > 1, F.density n σ q' = ∑_T D.coeff T q'`. This identifies an abstract
   `DensityFoundation`'s density with the count-native OM tree-sum at every residue cardinality. It
   is NOT a rationality/palindromy claim (so not in the footprint, correctly), and NOT an axiom — it
   is a HYPOTHESIS. Discharging it requires a `CountingModel`/`MontesData` whose `decidedCount` is the
   genuine `O_K/p^N` coset count and whose `densityVal`/`decided_tendsto` is the genuine `p`-adic Haar
   limit identified with `F.density`. mathlib v4.31.0 has NO `p`-adic Haar measure on
   `PadicInt`/any DVR (`Decomposition.lean` header; `Interface.lean` §2). **This is the standing
   measure wall.**

2. **The `q = realP` value pin (concrete capstone).** In `montes_unconditional`, `hbridge` is
   discharged by `rfl` (because `realF.density := g_σ` BY DEFINITION), so the abstract bridge is
   trivial there — but the price is paid in the **value clause**: the genuine decided limit is tied
   to `num/den` ONLY at `q = realP = 2`. A free-`q` value tie
   (`∀ q', 1 < q' → M_{q'}.countingDensity σ = num(q')/den(q')`) is NOT available from a single fixed
   box `monicBox(realP, N, n)`; it needs a per-prime family of counting models `{M_q}` (one box per
   residue cardinality) with a uniform `densityVal` curve — i.e. the same un-constructed measure
   foundation, now phrased as "the genuine Haar density at EACH prime equals `num/den` at that prime."

**These two are the SAME wall** (`GOAL_ONLY_MONTES.md` item 1; `Decomposition.wiring_assessment`).
The rewire does not cross it; it relocates it from a buried `clusterMeasure`/`AX_cellRecursion`
dependency to an explicit, honestly-surfaced `hbridge` hypothesis (abstract route) or a `q=realP`
value pin (concrete route).

### 6a. Secondary residuals (off the rationality path, do not affect the across-primes uniformity)
Per `MONTES_DISCHARGE_STATUS.md` (2026-06-30 build, GREEN):
- `decidedDensity_mono_realP`, `discZeroValTail_density`: named GMN/Hensel CITE axioms feeding the
  value clause at the matched prime; TRUE only at `q = realP`, stated only there.
- `selfLoop_childFiber_corrected`, `boxVolumeScale_collapse`: named GMN cites feeding `real_h_node`
  (the box-additive limit). Open `sorry`s `npVertices_stable_of_hull_preserved` and
  `nodeTrunc_tendsto` are OFF the capstone footprint (verified by absence of `sorryAx`).
- `tame_functionalEquation` itself is a remaining cited literature axiom (paper §5) on BOTH routes —
  expected, not a Montes/measure issue.

---

## 7. Bridge lemma(s) — precise Lean signatures

The wiring needs no NEW deep lemma; it reuses existing ones. The explicit pieces:

```lean
-- (B1) the density-rationality the uniformity side consumes, supplied count-natively:
--      LeanUrat/Decomposition.lean:185
theorem MontesAxiom.MontesData.countingDensity_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q')

-- (B2) the value tie of the genuine decided limit to the tree-sum:  Decomposition.lean:104
theorem MontesAxiom.MontesData.countingDensity_eq_sum_coeff (σ : FactorizationType) :
    M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.coeff T q

-- (B3) THE BRIDGE: abstract density = count-native tree-sum (the relocated measure wall):
hbridge : ∀ q' : ℕ, 1 < q' → F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q'
--   • in montes_unconditional discharged by `fun _ _ => rfl` (realF.density := g_σ)
--   • in the abstract route it is the genuine measure-wall hypothesis

-- (B4) palindromy transfer (UNCHANGED, shared):  L7.lean:214, :81
theorem L7.tame_to_all_primes (F) (n σ) (hσ) (num den tnum tden)
    (hden0) (htden0) (hL6 : ∀ q,1<q→ den.eval q≠0 ∧ F.density n σ q = num.eval q/den.eval q)
    (htame : ∀ q, q.Prime → n<q → F.density n σ q = tnum.eval q/tden.eval q) :
    num * tden = tnum * den
theorem L7.isPalindromic_of_agree (num den tnum tden) (hden)(htden)
    (hagree : num*tden = tnum*den) (htpalin : IsPalindromic tnum tden) : IsPalindromic num den

-- (NEW, the only thing to add for Option B) the re-based OLD-shape capstone:
theorem goal_theorem_via_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesData q n M)
    (F : DensityFoundation) (σ : FactorizationType) (hσ : σ.degree = n)
    (hbridge : ∀ q', 1 < q' → F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q') :
    ∃ num den, den ≠ 0 ∧
      (∀ q', 1 < q' → den.eval q' ≠ 0 ∧ F.density n σ q' = num.eval q'/den.eval q') ∧
      IsPalindromic num den
-- proof: obtain from goal_theorem_montes, drop value clause, rewrite rationality via hbridge (§3 Option B)
```

---

## 8. Step-by-step implementation order, with grades

Grades: **[NOW]** = provable today from existing lemmas; **[BOUND]** = provable but needs a bounded
new lemma/CITE; **[CITE]** = rests on a literature citation (no Lean proof intended);
**[WALL]** = the un-constructed measure foundation (out of reach in mathlib v4.31.0).

| # | Step | Grade | Notes |
|---|---|---|---|
| 1 | Confirm `goal_theorem_montes` footprint = `{propext, Classical.choice, Quot.sound, tame_functionalEquation}` (re-run `#print axioms`). | **[NOW]** | Already verified (`GOAL_ONLY_MONTES.md`); the four measure axioms are absent. |
| 2 | Confirm `montes_unconditional` fires it non-vacuously (`realF.density := g_σ`, `hbridge := rfl`, `shapeMenu_nonempty`). | **[NOW]** | Already built & GREEN (`MONTES_DISCHARGE_STATUS.md` 2026-06-30). |
| 3 | Add `goal_theorem_via_montes` (Option B): the OLD-`F.density`-shape conclusion from `goal_theorem_montes` + `hbridge`, dropping the value clause and the `OMBridge`. | **[NOW]** | ~5 lines (§3, §7). Footprint inherits step 1's clean set. This is the literal "re-base `goal_theorem` on the Montes proof." |
| 4 | Deprecate / mark historical the `OMBridge` route in `goal_theorem`; point the project's across-primes uniformity claim at `goal_theorem_via_montes` (or directly `goal_theorem_montes`). | **[NOW]** | Documentation + a one-line corollary; no new math. |
| 5 | Discharge `real_h_node`'s cites (`selfLoop_childFiber_corrected` corrected GLUE-1 + `boxVolumeScale_collapse` A3) to keep `h_node` a theorem. | **[CITE]/[BOUND]** | Already routed (RealInstance.lean:784); the corrected GLUE-1 statement edit is the F2/B frontier (`MONTES_DISCHARGE_STATUS.md` §"h_node wiring"). Off the across-primes-uniformity *structure*; needed only for the concrete capstone. |
| 6 | Value clause at the matched prime: keep `decidedDensity_mono_realP`, `discZeroValTail_density` as named GMN/Hensel CITEs. | **[CITE]** | TRUE only at `q = realP`; stated only there (not a false free-`q` axiom). Feeds only clause (2). |
| 7 | (Genuine extension) free-`q` value tie: a per-prime family `{M_q}` of counting models with a uniform `densityVal` curve, so `∀ q', M_{q'}.countingDensity σ = num(q')/den(q')`. | **[WALL]** | The un-constructed `p`-adic Haar foundation; mathlib has no `p`-adic Haar measure. The genuine remaining gap (§6). |
| 8 | (Genuine extension) discharge `hbridge` for an `F` identified with the real `ρ`. | **[WALL]** | Same wall; identify `F.density` with the genuine `p`-adic Haar density. |

**The hardest step is #7/#8 (the [WALL]).** Everything through step 6 is either done or a bounded
named CITE; the across-primes uniform-rationality + palindromy *structure* is fully achievable today
with the thin footprint. Only the identification with the paper's honest `ρ` at *every* prime (the
free-`q` value tie / `hbridge` for the real density) remains genuinely out of reach.

---

## 9. Honest one-line verdict

**The wiring is a clean footprint de-axiomatization of the uniformity capstone's
rationality+palindromy structure** — the four measure axioms (`clusterMeasure`, `AX_cellRecursion`,
`omCells`, `descend_size_lt`) genuinely drop, replaced by the count-native
`MontesData.countingDensity_isRational`, leaving `{propext, Classical.choice, Quot.sound,
tame_functionalEquation}` — **but it does NOT close the genuine measure wall**: the across-primes
*uniform-rational function and its palindromy* are now all-`q` and unconditional-mod-cite, while the
identification of the abstract foundation's density with the genuine `p`-adic Haar `ρ` at every prime
(the free-`q` value tie / `hbridge`) remains the un-constructed measure foundation, surfaced honestly
as a hypothesis (abstract route) or pinned to the prototype `q = realP = 2` (concrete
`montes_unconditional`).
