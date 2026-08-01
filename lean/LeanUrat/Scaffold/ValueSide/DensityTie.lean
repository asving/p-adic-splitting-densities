/-
BP_IV §1.6 — Step 18b, density = series (the squeeze) + the movement
capstone (`DensityTie.lean`).
Units in this file: SKEL (module skeleton), D1 (`dmass_eq_sliceSum`, cast of
the PROVED corpus `TreeSeam.finiteness_stack`), D0a (`dmass_monotone`,
`dmass` monotone in N from `canonical_stable` + T0), D0 (`cylDensity`,
BP_IV §1.6 verbatim), D2 (`sum_cylDensity_eq_one`, the squeeze — BP_IV §1.6
verbatim; the corpus box partition `boxN` (U1) + D0a monotone convergence +
the `henv` binder).  Later waves add
D3 (`cylDensity_eq_seriesSum`), D5 (`renewal_unique_of_margin`), and D4
(`valueSide_massTie`, the movement CAPSTONE).
Import graph (BP_IV §1.0/§4): this module imports the completed
`SeriesTie.lean`; `SeriesTie.lean` never imports this module.  D0a's T0
dependency (`card_boxProj_fiber`) arrives via `Transfer.lean`, a leaf module
over the corpus `MovesU/Defs.lean`; no file in the §4 chain imports
`DensityTie.lean`, so the §1.0 acyclicity is preserved.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.SeriesTie
import LeanUrat.Scaffold.ValueSide.Transfer
import LeanUrat.MovesU.U1_boxN

/-!
# Density = series + the value-side capstone [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.6, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.6 (statement layer) and §0
  (module map row `DensityTie.lean` | step 18b | "squeeze +
  `valueSide_massTie`").
* Math source of record: the D-11 second tranche (MASS-ID M2, monic scope),
  per BP_IV §0 step-18b row.
* Imports: `Mathlib` + `LeanUrat.Scaffold.ValueSide.SeriesTie` (the §1.0
  acyclicity edge: DensityTie imports SeriesTie, never conversely;
  `BridgeKernels`/`DefsLedger` corpus vocabulary arrives transitively).
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU ENNReal Filter Topology Filter

/-- D1 (slice identity — REUSE, not re-proof; BP_IV §1.6): dmass σ N = slice
    sum, i.e. the corpus `TreeSeam.finiteness_stack`
    (`MovesU/DefsLedger.lean:249`, PROVED) recast over ℝ — divide the ℝ≥0∞
    partition identity decided_σ(N) = p^{nN} · Σ_{thr(T) ≤ N} μ(fiber T) by
    p^{nN} and take `toReal`. -/
theorem dmass_eq_sliceSum {n p : ℕ} [NeZero p] {X : ClassifierSpec n p}
    {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (σ : SplittingType n) (N : ℕ) :
    X.dmass σ N = (∑ T ∈ F.thrSlice σ N, F.mass σ T).toReal := by
  have h := seam.finiteness_stack σ N
  have hp0 : ((p : ℝ≥0∞)) ^ (n * N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hpt : ((p : ℝ≥0∞)) ^ (n * N) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hS : ∑ T ∈ F.thrSlice σ N, F.mass σ T
      = (X.decided σ N : ℝ≥0∞) / (p : ℝ≥0∞) ^ (n * N) := by
    rw [ENNReal.eq_div_iff hp0 hpt]
    exact h.symm
  rw [ClassifierSpec.dmass, hS, ENNReal.toReal_div]
  simp [ENNReal.toReal_pow]

/-!
**PROVENANCE (unit D0a; BP_IV §1.6 D0 docstring + §2 D-table row D0a).**
The blueprint displays no code-block signature for D0a; its statement layer is
the D0 docstring ("Monotonicity of `dmass` in N is D0a (from
`canonical_stable`, same counting as T1)") + the §2 D-table row
("`dmass` monotone in N | same counting as T1 on decided classes | dep T0").
Statement below transcribes that specification in the §1.1 T1 signature
pattern (`ClassifierSpec.env_antitone`): `Monotone (X.dmass σ)`.
Mechanism: every level-N decided-σ class lifts to exactly p^{n(N'−N)}
level-N' classes (T0 `card_boxProj_fiber`, fiberwise over the decided set),
all of which are decided σ by `canonical_stable`; divide the resulting count
inequality by the level-N' normalizer p^{nN'}.
-/

/-- D0a (`dmass` monotone in N; BP_IV §1.6 D0 docstring + §2 D-table): from
    `canonical_stable`, the same counting as T1 on decided classes — the
    level-N decided-σ set lifts fiberwise (T0) into the level-N' decided-σ
    set, so d_σ(N) = decided_σ(N)/p^{nN} is monotone. -/
theorem ClassifierSpec.dmass_monotone {n p : ℕ} [Fact p.Prime]
    (X : ClassifierSpec n p) (σ : SplittingType n) :
    Monotone (X.dmass σ) := by
  intro N N' h
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  haveI : NeZero (p ^ N') := ⟨pow_ne_zero N' hp.ne_zero⟩
  -- counting core: each level-N decided-σ class lifts to exactly p^{n(N'−N)}
  -- level-N' classes (T0), all decided σ by `canonical_stable`
  have hcount : X.decided σ N * p ^ (n * (N' - N)) ≤ X.decided σ N' := by
    haveI : Fintype {f : Box p n N // X.canonical N f = some σ} := Fintype.ofFinite _
    set φ : {g : Box p n N' // X.canonical N (boxProj p n h g) = some σ} →
        {f : Box p n N // X.canonical N f = some σ} :=
      fun g => ⟨boxProj p n h g.1, g.2⟩ with hφ
    have hcardS : Nat.card
        {g : Box p n N' // X.canonical N (boxProj p n h g) = some σ}
        = X.decided σ N * p ^ (n * (N' - N)) := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma]
      have hfib : ∀ y : {f : Box p n N // X.canonical N f = some σ},
          Nat.card {x // φ x = y} = p ^ (n * (N' - N)) := by
        intro y
        have e : {x // φ x = y} ≃ {g : Box p n N' // boxProj p n h g = y.1} :=
          { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
            invFun := fun g => ⟨⟨g.1, by rw [g.2]; exact y.2⟩, Subtype.ext g.2⟩
            left_inv := fun x => rfl
            right_inv := fun g => rfl }
        rw [Nat.card_congr e, card_boxProj_fiber h]
      simp only [hfib]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ClassifierSpec.decided, Nat.card_eq_fintype_card]
    have hinj : Nat.card
        {g : Box p n N' // X.canonical N (boxProj p n h g) = some σ}
        ≤ X.decided σ N' :=
      Nat.card_le_card_of_injective
        (fun g => (⟨g.1, X.canonical_stable h g.1 σ g.2⟩ :
          {g : Box p n N' // X.canonical N' g = some σ}))
        (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
    rw [← hcardS]
    exact hinj
  -- divide the counting inequality by the level-N' normalizer p^{nN'}
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpowN : (0 : ℝ) < (p : ℝ) ^ (n * N) := pow_pos hp0 _
  have hpowN' : (0 : ℝ) < (p : ℝ) ^ (n * N') := pow_pos hp0 _
  have hc : (X.decided σ N : ℝ) * (p : ℝ) ^ (n * (N' - N))
      ≤ (X.decided σ N' : ℝ) := by
    exact_mod_cast hcount
  have hsplit : (p : ℝ) ^ (n * N')
      = (p : ℝ) ^ (n * N) * (p : ℝ) ^ (n * (N' - N)) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' h]
  unfold ClassifierSpec.dmass
  rw [div_le_div_iff₀ hpowN hpowN', hsplit]
  calc (X.decided σ N : ℝ) * ((p : ℝ) ^ (n * N) * (p : ℝ) ^ (n * (N' - N)))
      = ((X.decided σ N : ℝ) * (p : ℝ) ^ (n * (N' - N))) * (p : ℝ) ^ (n * N) := by
        ring
    _ ≤ (X.decided σ N' : ℝ) * (p : ℝ) ^ (n * N) :=
        mul_le_mul_of_nonneg_right hc hpowN.le

/-- D0: the (lower) cylinder density of type σ — the scaffold's α(n, τ; p),
    counting form: the monotone limit of decided-σ mass.  Monotonicity of
    `dmass` in N is D0a (from `canonical_stable`, same counting as T1). -/
noncomputable def cylDensity {n p : ℕ} [Fact p.Prime] (X : ClassifierSpec n p)
    (σ : SplittingType n) : ℝ := ⨆ N, X.dmass σ N

/-!
**PROVENANCE (unit D3; BP_IV §1.6 code block + §2 D-table row D3).**
Statement transcribed VERBATIM from §1.6.  Proof per the D3 row sketch
"D1 + imported S0 + toReal cast under `hfin`": D3a is the imported S0
(`seriesSum_eq_iSup_slice`, SeriesTie.lean — M04 Thm 1's ⨆-characterization
over `mem_slice_iff`); D3b is the cast chain — `hfin` bounds every slice sum
away from ⊤ (each is ≤ the ⨆ by S0), so `ENNReal.toReal_iSup` commutes the
cast with the ⨆, and D1 (`dmass_eq_sliceSum`) rewrites termwise.  The `henv`
binder is the §1.6 displayed hypothesis set; this (S2)-free half of D-11 M2
closes from D1 + S0 + `hfin` alone (the lower/⨆ form needs no envelope),
`henv` being consumed by the D2/D4 legs.
-/

/-- D3 (density IS the series, D-11 M2's (S2)-free half): cylDensity =
    (seriesSum's ℝ-value) — from D1 + M04 Theorem 1's ⨆-characterization of
    seriesSum + henv.  D3a: seriesSum σ = ⨆ N (slice sum) (M04 Thm 1, an
    interface lemma over `mem_slice_iff`); D3b: the cast chain. -/
-- `henv` is the §1.6 verbatim binder (statement fence); this (S2)-free leg
-- does not consume it, so the unused-variable lint is silenced for this
-- declaration only.
set_option linter.unusedVariables false in
theorem cylDensity_eq_seriesSum {n p : ℕ} [Fact p.Prime] [NeZero p]
    {X : ClassifierSpec n p} {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (henv : Tendsto X.env atTop (nhds 0)) (σ : SplittingType n)
    (hfin : F.seriesSum σ ≠ ⊤) :
    cylDensity X σ = (F.seriesSum σ).toReal := by
  -- D3b setup: every slice sum is ≤ the seriesSum (S0), hence ≠ ⊤ under hfin
  have hslice : ∀ N, (∑ T ∈ F.thrSlice σ N, F.mass σ T) ≠ ⊤ := by
    intro N
    refine ne_top_of_le_ne_top hfin ?_
    rw [seriesSum_eq_iSup_slice]
    exact le_iSup (fun N => ∑ T ∈ F.thrSlice σ N, F.mass σ T) N
  -- D3a: seriesSum σ = ⨆ N (slice sum)  [imported S0]
  rw [cylDensity, seriesSum_eq_iSup_slice,
    -- D3b: the cast chain — toReal commutes with the ⨆ of finite terms
    ENNReal.toReal_iSup hslice]
  -- termwise: D1 (slice identity)
  exact iSup_congr fun N => dmass_eq_sliceSum seam σ N

end LeanUrat.Scaffold
