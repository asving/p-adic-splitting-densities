/-
BP_IV §1.6 — Step 18b, density = series (the squeeze) + the movement
capstone (`DensityTie.lean`).
Units in this file: SKEL (module skeleton), D1 (`dmass_eq_sliceSum`, cast of
the PROVED corpus `TreeSeam.finiteness_stack`), D0a (`dmass_monotone`,
`dmass` monotone in N from `canonical_stable` + T0), D0 (`cylDensity`,
BP_IV §1.6 verbatim), D2 (`sum_cylDensity_eq_one`, the squeeze — BP_IV §1.6
verbatim; the corpus box partition `boxN` (U1) + D0a monotone convergence +
the `henv` binder), D3 (`cylDensity_eq_seriesSum`), and
D5 (`renewal_unique_of_margin`).

D4 (`valueSide_massTie`, THE MOVEMENT CAPSTONE) LANDED at REVISION 3
(mop-up adjudication) at the S5b-adjudicated binder list + `henv`: the five
undeclared row types enter as opaque predicate parameters resp. the landed
`CensusValueRows`, and the O11-K2 pricing content enters as the named
`SolvePricing` row (owner: `SeriesTie.lean` unit S5b — see its adjudication
record and BP_IV REVISION 3; the original obstruction record is kept verbatim
in the D4 section below).  Proof: pointwise rewrite by D3 and S5b, with the
`toReal` passage lawful by the pricing row's `sol_nonneg` (O-12 positivity
shape).  D2 is not used (BP_IV §2 D-table, REV-2 finding 22).
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

open LeanUrat.MovesU ENNReal Filter Topology

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
**PROVENANCE (unit D2; BP_IV §1.6 code block + §2 D-table row D2).**
Statement transcribed VERBATIM from §1.6 (the trailing `Fintype` comment line
of the blueprint block is met by the corpus instance
`instSplittingTypeFintype`, unit U0b — imported via `MovesU.U1_boxN`).
Proof per the D2 row sketch, generalizing the proved n = 2 pattern
`decided6_lower/upper` (`OM/SeriesAssembly.lean`): the corpus box partition
`boxN` (U1, PROVED: Σ_σ decided_σ(N) + undec(N) = p^{nN}) divided by the
level-N normalizer gives Σ_σ dmass σ N = 1 − env N with defect env N — the
§1.6 docstring's env-defect display; each `dmass σ` is monotone (D0a) and
bounded by 1, so `tendsto_atTop_ciSup` makes every `cylDensity` a true limit;
the finite Σ_σ of limits then meets the `henv`-squeezed limit 1 and
`tendsto_nhds_unique` closes.
-/

/-- D2 (the squeeze): Σ_σ dmass σ N = 1 − env-defect N with defect ≤ env N;
    with `env → 0` (Step 13's delivery) every cylDensity exists as a true limit
    and Σ_σ cylDensity = 1.  (Generalizes the proved n = 2 pattern
    `decided6_lower/upper` in `OM/SeriesAssembly.lean`.) -/
theorem sum_cylDensity_eq_one {n p : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} (henv : Tendsto X.env atTop (nhds 0)) :
    ∑ σ : SplittingType n, cylDensity X σ = 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- the real box partition (boxN/p^{nN}): Σ_σ dmass σ N + env N = 1
  have hpart : ∀ N, (∑ σ : SplittingType n, X.dmass σ N) + X.env N = 1 := by
    intro N
    have hP : (0 : ℝ) < (p : ℝ) ^ (n * N) := pow_pos hp0 _
    have hcast : (∑ σ : SplittingType n, (X.decided σ N : ℝ)) + (X.undec N : ℝ)
        = (p : ℝ) ^ (n * N) := by exact_mod_cast boxN X N
    unfold ClassifierSpec.dmass ClassifierSpec.env
    rw [← Finset.sum_div, ← add_div, hcast, div_self hP.ne']
  have hnn : ∀ (σ : SplittingType n) (N : ℕ), 0 ≤ X.dmass σ N := fun σ N =>
    div_nonneg (Nat.cast_nonneg _) (pow_pos hp0 _).le
  have henv_nn : ∀ N, 0 ≤ X.env N := fun N =>
    div_nonneg (Nat.cast_nonneg _) (pow_pos hp0 _).le
  -- each dmass σ N ≤ 1 (its Σ_σ' companion terms and env N are ≥ 0)
  have hle1 : ∀ (σ : SplittingType n) (N : ℕ), X.dmass σ N ≤ 1 := by
    intro σ N
    calc X.dmass σ N
        ≤ ∑ σ' : SplittingType n, X.dmass σ' N :=
          Finset.single_le_sum (fun σ' _ => hnn σ' N) (Finset.mem_univ σ)
      _ ≤ (∑ σ' : SplittingType n, X.dmass σ' N) + X.env N :=
          le_add_of_nonneg_right (henv_nn N)
      _ = 1 := hpart N
  -- monotone convergence (D0a + the bound): dmass σ → cylDensity X σ
  have hlim : ∀ σ : SplittingType n,
      Tendsto (X.dmass σ) atTop (nhds (cylDensity X σ)) := by
    intro σ
    have hb : BddAbove (Set.range (X.dmass σ)) := by
      refine ⟨1, ?_⟩
      rintro x ⟨N, rfl⟩
      exact hle1 σ N
    exact tendsto_atTop_ciSup (ClassifierSpec.dmass_monotone X σ) hb
  -- the finite sum of the limits …
  have hsum : Tendsto (fun N => ∑ σ : SplittingType n, X.dmass σ N) atTop
      (nhds (∑ σ : SplittingType n, cylDensity X σ)) :=
    tendsto_finsetSum _ fun σ _ => hlim σ
  -- … equals the henv-squeezed limit of 1 − env N
  have hone : Tendsto (fun N => ∑ σ : SplittingType n, X.dmass σ N) atTop
      (nhds 1) := by
    have heq : (fun N => ∑ σ : SplittingType n, X.dmass σ N)
        = fun N => 1 - X.env N := by
      funext N
      linarith [hpart N]
    rw [heq]
    simpa using henv.const_sub 1
  exact tendsto_nhds_unique hsum hone

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

-- `henv` is the §1.6 verbatim binder (statement fence); this (S2)-free leg
-- does not consume it, so the unused-variable lint is silenced for this
-- declaration only.
set_option linter.unusedVariables false in
/-- D3 (density IS the series, D-11 M2's (S2)-free half): cylDensity =
    (seriesSum's ℝ-value) — from D1 + M04 Theorem 1's ⨆-characterization of
    seriesSum + henv.  D3a: seriesSum σ = ⨆ N (slice sum) (M04 Thm 1, an
    interface lemma over `mem_slice_iff`); D3b: the cast chain. -/
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

/-!
**PROVENANCE (unit D5; BP_IV §1.6 code block + §2 D-table row D5).**
Statement transcribed VERBATIM from §1.6.  Proof per the D5 row sketch
"least solution + any solution differ by a fixed point of A; margin kills
it": the difference d = x − y of any two renewal solutions is a fixed point
of A (the b's cancel); at an argmax coordinate i₀ of |d| the row-sum margin
gives |d i₀| ≤ ρ·|d i₀| with ρ < 1, forcing |d i₀| = 0 and hence d = 0.
(S1b leastness + S4a finiteness locate the value; uniqueness itself closes
from the margin alone.)
-/

/-- D5 (the (r1) uniqueness pivot): under the margin, the renewal solution is
    UNIQUE (not merely least) — S1b's leastness + S4a's finiteness. -/
theorem renewal_unique_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (b x y : Fin m → ℝ)
    (hmargin : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ i, ∑ j, |A i j| ≤ ρ)
    (hx : x = b + A.mulVec x) (hy : y = b + A.mulVec y) :
    x = y := by
  obtain ⟨ρ, hρ0, hρ1, hrow⟩ := hmargin
  -- the difference of two solutions is a fixed point of A (the b's cancel)
  have hfix : ∀ i, x i - y i = ∑ j, A i j * (x j - y j) := by
    intro i
    have hx' := congrFun hx i
    have hy' := congrFun hy i
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct] at hx' hy'
    rw [hx', hy']
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  -- the margin kills the fixed point, coordinatewise
  suffices hz : ∀ i, x i - y i = 0 by
    funext i
    have := hz i
    linarith
  intro i
  have : Nonempty (Fin m) := ⟨i⟩
  -- argmax coordinate of |x − y|
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun k => |x k - y k|
  -- contraction at the argmax: |d i₀| ≤ ρ · |d i₀|
  have hbound : |x i₀ - y i₀| ≤ ρ * |x i₀ - y i₀| :=
    calc |x i₀ - y i₀| = |∑ j, A i₀ j * (x j - y j)| := by rw [hfix i₀]
      _ ≤ ∑ j, |A i₀ j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i₀ j| * |x j - y j| := by simp only [abs_mul]
      _ ≤ ∑ j, |A i₀ j| * |x i₀ - y i₀| :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hi₀ j) (abs_nonneg _)
      _ = (∑ j, |A i₀ j|) * |x i₀ - y i₀| := by rw [Finset.sum_mul]
      _ ≤ ρ * |x i₀ - y i₀| :=
          mul_le_mul_of_nonneg_right (hrow i₀) (abs_nonneg _)
  -- ρ < 1 forces the max to vanish
  have hmax0 : |x i₀ - y i₀| ≤ 0 := by nlinarith [abs_nonneg (x i₀ - y i₀)]
  have hi : |x i - y i| = 0 :=
    le_antisymm (le_trans (hi₀ i) hmax0) (abs_nonneg _)
  exact abs_eq_zero.mp hi

/-!
## Unit D4 — `valueSide_massTie` (LANDED at REVISION 3, mop-up adjudication)

**REVISION-3 disposition:** the obstruction record below (kept verbatim — the
type-level half of the D4 warrant) was adjudicated EXACTLY as at S5b
(`SeriesTie.lean`, whose section carries the full two-part warrant incl. the
under-constraint shape): the five undeclared row types enter as opaque
predicate parameters resp. the landed `CensusValueRows` of `Census.lean`, and
the O11-K2 pricing content enters as the ONE named row
`K2 : SolvePricing C K1`.  D4's binder list = S5b's + `henv` (BP_IV §2
D-table: "pointwise rewrite by D3 and S5; D2 is not used"); the `toReal`
passage from S5b's `ofReal` conclusion is lawful by the pricing row's
`sol_nonneg` (the O-12 positivity shape priced by `cycS_eval_pos` at
q₀ = p ≥ 2).  The BP_VI spine must consume THIS binder list verbatim
(§5 statement fence, re-pointed by BP_IV REVISION 3).

**The original BLOCKED(D4) record (2026-08-01, superseded):**
The verbatim statement cannot elaborate: its binder list applies FIVE row
types with no declaration anywhere in the corpus (probe run 2026-08-01, from
`import … DensityTie + … Hyps`, `open LeanUrat.MovesU
LeanUrat.Scaffold.ValueSide`, oleans freshly rebuilt so that the just-landed
S2b `TreeRecursion` resolves — it does):

* `hGRB : GRBRow CD`, `hFresh : FreshRow CD` — the landed BP_III owner rows
  (`Scaffold/DictIII/Hyps.lean`) are named `GRB`/`FRESH` and are indexed
  `(p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]`, not
  `CensusData`-indexed; per the §5 seam ("BP_IV defines no aliases") no
  prover-side alias/bridge may be declared.
* `hcen : CensusValueRows CD` — no owner module anywhere; the §3
  corpus-reuse map keys it to the SlotsG15 `SiteData` carriers as an
  E-phase instruction to the S5 prover, not yet executed.
* `hR14 : R1R4Row n p X` — owner BP_V (`Scaffold/RowStatements.lean`,
  `RootRows.R14`): module absent (unit-H4 ledger, `ValueSide/Hyps.lean`).
* `K4 : TerminalSeamRows n p X F` — owner BP_III (CU-2t,
  `DictIII/CU2t.lean`): module absent (same ledger).

Each of the five fails with
`error: Function expected at GRBRow|FreshRow|CensusValueRows|R1R4Row|`
`TerminalSeamRows, but this term has type ?m.N … The identifier … is
unknown`.  Every OTHER binder (incl. `TreeRecursion X F A b`, `RegP RD`,
`RegPin C RD`, `PackCorrespondence n C P R`, `ADMFull CD`,
`K3DeltaRow p RD RealizedPool DeltaStablePos`) and the conclusion
`∀ σ, cylDensity X σ = C.chain.Rval (vmap C.T σ) (p : ℚ)` elaborate cleanly.
-/

-- The honest-conditionality row binders are deliberately unused in the Lean
-- assembly (see the S5b note in `SeriesTie.lean`); lint silenced for D4
-- only, the D3 precedent above.
set_option linter.unusedVariables false in
open ValueSide in
/-- D4 (THE MOVEMENT CAPSTONE — α = R_τ at the full displayed hypothesis
    set; BP_IV §1.6 at the REVISION-3 adjudicated scope, = S5b's binder list
    + `henv`): the cylinder-limit density of every type σ equals the chain's
    measured value R_τ(σ) at q₀ = p.  Proof: pointwise rewrite by D3
    (`cylDensity_eq_seriesSum`) and S5b (`seriesTie_of_kernels`); D2 is not
    used. -/
theorem valueSide_massTie {n p m : ℕ} [Fact p.Prime] [NeZero p]
    {C : UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {CD : CensusData} {RD : RegData p} {P : AssembledPack n}
    {R : PackReference n C P}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    {GRBRow FreshRow : CensusData → Prop}
    {SW : StratumR CD} {SJ : JunctionStratum CD}
    {R1R4Row : ClassifierSpec n p → Prop}
    {TerminalSeamRows : FiberSeries n p X → Prop}
    {RealizedPool DeltaStablePos : ℕ → Prop}
    (seam : TreeSeam n p X F)
    (K1 : TreeRecursion X F A b)
    (hreg : RegP RD) (hpin : RegPin C RD)
    (K2 : SolvePricing C K1)
    (hpack : PackCorrespondence n C P R)
    (hGRB : GRBRow CD) (hFresh : FreshRow CD) (hadm : ADMFull CD)
    (hcen : CensusValueRows CD GRBRow FreshRow SW SJ)
    (hR14 : R1R4Row X)
    (hK3δ : K3DeltaRow p RD RealizedPool DeltaStablePos)
    (K4 : TerminalSeamRows F)
    (henv : Tendsto X.env atTop (nhds 0)) :
    ∀ σ : SplittingType n,
      cylDensity X σ = C.chain.Rval (vmap C.T σ) (p : ℚ) := by
  intro σ
  have hp : p.Prime := Fact.out
  -- S5b: the series tie
  have htie : F.seriesSum σ
      = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ)) :=
    seriesTie_of_kernels seam K1 hreg hpin K2 hpack hGRB hFresh hadm hcen
      hR14 hK3δ K4 σ
  -- the pricing row's nonnegativity read at the measured value
  have hnn : 0 ≤ C.chain.Rval (vmap C.T σ) (p : ℚ) := by
    rw [← evalℝ_eq_Rval_of_solvePin hpin hreg hp K2.solve_pin σ,
      ← K2.sol_reads σ]
    exact K2.sol_nonneg σ
  have hfin : F.seriesSum σ ≠ ⊤ := by
    rw [htie]; exact ENNReal.ofReal_ne_top
  -- D3 + S5b + the lawful toReal passage
  rw [cylDensity_eq_seriesSum seam henv σ hfin, htie,
    ENNReal.toReal_ofReal hnn]

end LeanUrat.Scaffold
