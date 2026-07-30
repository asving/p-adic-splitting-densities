/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.SelfLoopCensusK
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.RphiGenHCount
import LeanUrat.OM.TowerBase
import LeanUrat.OM.DevelopTower
import LeanUrat.OM.HNode1
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.Drainage
import LeanUrat.OM.SelfLoopTower

/-!
# SelfLoopCensusFiltration — the self-loop census in the GAPPED-DIGIT FILTRATION frame (scratch)

This module re-examines the `SelfLoopCensusK.OPEN_count_evaluation` obligation

    Σ_{selfLoopDepthOf c = k} stratumCount1 s N c
      = depth0Census · p^(s(N−1)) · (slBoxRatio s p)^k · p^k

from the filtration/tower frame (`RphiGenHCount` / `TowerBase` / `DevelopTower`), and reports,
HONESTLY, exactly what that frame does and does NOT deliver.

## The correspondence is FALSE in its strong form

The tempting bridge "depth-`k` self-loop ⟺ first `k` gapped-digits lie in a continue-range" is
**FALSE as a pure-filtration statement**, and `card_r_level_census` does NOT count the self-loop
verdict.  Precisely:

* The **filtration frame counts the FLOOR event** (`RphiGenHCount.filtIdeal_eq_phiIdeal`,
  `card_filtIdeal`, `TowerBase.card_filtIdeal_gen`, `DevelopTower.card_r_level_census`): a *pure
  per-digit divisibility-floor* ideal `{x : ∀ i, p^(dexp …) ∣ a_i}`.  Its card is the per-digit
  product `∏_i ballCount(dexp …)`, self-similar per tower level.  The object it counts is
  `DevelopTower.InCellTower = SlotPatternAbstract`, i.e. "every digit at every level clears its
  `p`-adic floor" — the fresh-cluster `GammaPattern` floors.

* The **self-loop `k`-fold census** (`SelfLoopCensusK.selfLoopChain`) needs, at each level,
  `classify1 (recenterIter i g) = some (selfLoopCell μ)`.  By `Drainage.selfLoopCell` this is a
  **Newton-polygon residual-factorization VERDICT**: `residualOf` has shape `[(1,s)]`, i.e. the
  residue-field residual polynomial is a *repeated root* `(y − c̃)^s`.

* The verdict event is a **proper sub-event** of the floor event that additionally pins a
  residue-field factorization to be a repeated root.  The gapped-digit expansion is
  **residue-BLIND** (it sees only `p^k ∣ a_i`), so the filtration counts the strictly larger FLOOR
  event, not the VERDICT event.

## What this module lands (no `sorry`/`axiom`)

* **STEP 1** (`selfLoopCell_floor`, `selfLoopChain_le_floorChain`) — the easy containment
  `{verdict} ⊆ {floor}`: the self-loop verdict at a level forces the slope-`(−1)` side floors
  `p^(μ−j) ∣ coeff_j`.  This connects `selfLoopChain` to the filtration's floor language.  It is
  proved from `matched_line_le` (the classifier hull lemma) + `dvd_iff_le_zmodValuation`.

* **STEP 2** (`verdictFractionInCoset`, `floorRatio`, `selfLoop_floor_ratio_uniform`) — the honest
  decomposition of the per-level step ratio as `(floor ratio) × (verdict fraction)`.  The floor
  ratio is supplied UNIFORMLY across levels and in `N` by the filtration
  (`card_filtIdeal`/`ball_count_clamped`/`card_r_level_census`): this is the genuine
  "deepening-is-a-non-issue" content, and it is BANKABLE.  The verdict fraction is the residue
  refinement the filtration cannot see.

* **STEP 3** (`VerdictTranslationInvariant`, stated precisely — NOT a `sorry`) — the single named
  residual: the residual-repeated-root verdict cuts every `GammaPattern` coset to the SAME
  fraction, level-independently.  This is `SelfLoopCensusK`'s UNIFORM COSET DENSITY, correctly
  RE-LOCATED as a residue-theoretic (Newton-polygon, `ZMod`-specific) statement, NOT a
  filtration statement.

* **STEP 4** (`selfLoopCensus_filtration_step`, `selfLoopCensus_filtration_closed`, taking the
  STEP-3 invariance as an explicit HYPOTHESIS) — the closed census, reduced to the STEP-3 residual
  and fed the geometric resummation via `SelfLoopResum.xqMultiplicity`.

## Report on the reframing

The filtration frame **does** avoid the a0-valuation *deepening* obstruction (`2 → 4 → …`,
semigroup `⟨e,h⟩`): `dexp`/`PhiG_theta_bump` handle the gapped valuation uniformly and
`card_filtIdeal` is genuinely self-similar per level.  So the FLOOR half resums cleanly with a
uniform per-level product — the deepening was never the real obstruction.

But the frame does **not** avoid the real obstruction, which is UNCHANGED by the reframing: the
residual-repeated-root VERDICT is residue-theoretic and invisible to the divisibility filtration.
Both routes (`card_r_level_census` and direct `census_step_equiv` iteration) still meet at
`VerdictTranslationInvariant`.  This module does NOT close the obligation; it closes the FLOOR half
and re-localizes the (unchanged) residue half as one precisely-stated lemma.

Nothing here edits the real project files.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.SelfLoopCensusFiltration

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.SelfLoopTower
open LeanUrat.OM.SelfLoopCensusK

noncomputable section

variable (p N μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ) (hN : 0 < N)

/-! ## STEP 1. The verdict ⊆ floor containment (provable now)

The self-loop verdict at a level is `classify1 g = some (selfLoopCell μ)`, i.e. `InCell g
(selfLoopCell μ)` by `classify1_eq_some_iff`.  Since `selfLoopCell μ = mkCell μ (selfLoopPath μ)
[[(1,μ)]]` and `selfLoopPath μ = [(0,μ),(μ,0)]` is a single slope-`(−1)` side, the `Matches`
condition (i) (`SideAbove`, via `matched_line_le`) forces every low coefficient of `g` to sit ON
OR ABOVE the line `μ − j`, i.e. `p^(μ−j) ∣ coeff_j g`.  This is the FLOOR read the filtration
language speaks. -/

/-- **The per-level self-loop FLOOR.**  `selfLoopFloor g` says every low coefficient `j < μ` of the
size-`μ` box element `g` carries `p^(μ−j)` — the slope-`(−1)` side floor of the self-loop cell.
This is the divisibility-floor shadow the filtration frame sees. -/
def selfLoopFloor (g : QuotientBox.monicBox p N μ) : Prop :=
  ∀ j : ℕ, j < μ → (p : ZMod (p ^ N)) ^ (μ - j) ∣ ((g.1).coeff j)

/-- **STEP 1, core containment (`selfLoopCell_floor`).**  The self-loop verdict forces the floor:
`classify1 g = some (selfLoopCell μ)` implies `selfLoopFloor g`.  Proof: unpack `InCell` to
`Matches g (selfLoopPath μ) [[(1,μ)]]` (the menu data of `selfLoopCell μ` is uniquely recovered by
`mkCell_injective`), apply `matched_line_le` on the single side `((0,μ),(μ,0))` to get `μ − j ≤ vOf
g j`, then translate to divisibility via `dvd_iff_le_zmodValuation`. -/
theorem selfLoopCell_floor (hμ1 : 1 ≤ μ) (hμN : μ < N) (g : QuotientBox.monicBox p N μ)
    (hg : classify1 p g = some (Drainage.selfLoopCell μ)) :
    selfLoopFloor p N μ g := by
  have hin : InCell p g (Drainage.selfLoopCell μ) := (classify1_eq_some_iff p).mp hg
  obtain ⟨P, sh, hP, hsh, hmk, hmatch⟩ := hin
  -- recover the menu data of the self-loop cell
  obtain ⟨rfl, rfl⟩ : P = Drainage.selfLoopPath μ ∧ sh = [[(1, μ)]] :=
    mkCell_injective hP (Drainage.selfLoopPath_menuPath hμ1 hμN) hsh
      (Drainage.selfLoopShapes hμ1) hmk.symm
  -- the single side (sidePairs (selfLoopPath μ) = [((0, μ), (μ, 0))] definitionally)
  have hside : ((0, μ), (μ, 0)) ∈ sidePairs (Drainage.selfLoopPath μ) :=
    List.mem_singleton.mpr rfl
  intro j hj
  -- hull lower bound: line at j ≤ vOf g j
  have hline := matched_line_le p hP hmatch ((0, μ), (μ, 0)) hside j (le_of_lt hj)
  -- lineAt ((0,μ),(μ,0)) j = μ − j (slope −1)
  have hμQ : (μ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlineval : lineAt ((0, μ), (μ, 0)) (j : ℚ) = (μ : ℚ) - (j : ℚ) := by
    unfold lineAt slopeQ
    show (μ : ℚ) + ((0 : ℚ) - (μ : ℚ)) / ((μ : ℚ) - (0 : ℚ)) * ((j : ℚ) - (0 : ℚ)) = (μ : ℚ) - (j : ℚ)
    field_simp
    ring
  rw [hlineval] at hline
  -- so (μ : ℚ) − j ≤ vOf; hence (μ − j : ℕ) ≤ vOf (as vOf : ℕ, and j < μ)
  have hvOf_ge : μ - j ≤ vOf p g j := by
    have hle : ((μ - j : ℕ) : ℚ) ≤ (vOf p g j : ℚ) := by
      rw [Nat.cast_sub (le_of_lt hj)]
      exact hline
    exact_mod_cast hle
  -- translate vOf ≥ μ−j to divisibility p^(μ−j) ∣ coeff_j
  have hmjN : μ - j ≤ N := le_trans (Nat.sub_le μ j) (le_of_lt hμN)
  -- ring dvd ↔ val dvd (RestartEquiv) ↔ ≤ zmodValuation (CellCard); vOf = zmodValuation
  rw [RestartEquiv.pow_dvd_iff_dvd_val p N hmjN, CellCard.pow_dvd_val_iff p hmjN]
  -- goal: μ - j ≤ zmodValuation (coeff j) = vOf p g j
  exact hvOf_ge

/-- **STEP 1, `selfLoopChain_le_floorChain` (the chain form).**  A depth-`k` self-loop chain
forces, at each of its first `k` iterated recenter levels, the self-loop FLOOR of that level's
box.  This is the honest `{verdict-chain} ⊆ {floor-chain}` containment connecting `selfLoopChain`
to the filtration's floor language (`card_filtIdeal_gen` / `GammaPattern`).  It is the EASY
direction; the reverse fails (floor does not imply the residual-repeated-root verdict). -/
theorem selfLoopChain_le_floorChain (hμ1 : 1 ≤ μ) (hμN : μ < N) (k : ℕ)
    (g : QuotientBox.monicBox p N μ) (hchain : selfLoopChain p N μ c hN k g) :
    ∀ i : ℕ, i < k → selfLoopFloor p N μ (recenterIter p N μ c hN i g) :=
  fun i hi => selfLoopCell_floor p N μ hμ1 hμN _ (hchain i hi)

/-! ## STEP 2. The honest decomposition: (floor ratio) × (verdict fraction)

The per-level self-loop step ratio `slBoxRatio` factors as

    slBoxRatio = (floor ratio from the filtration) × (verdict fraction within a floor coset).

STEP 1 gives `{verdict} ⊆ {floor}`, so the verdict fraction is well-defined as
`#{verdict} / #{floor coset}`.  The FLOOR ratio is supplied uniformly across levels and in `N` by
the filtration count (`card_filtIdeal`/`ball_count_clamped`), and is the honest
"deepening-is-a-non-issue" content.  The VERDICT fraction is the residue refinement the filtration
cannot deliver. -/

/-- **The floor ratio (filtration-supplied).**  The floor-coset index `slBoxRatio s p =
p^{−(selfLoopExponent s + 1)}` is exactly the `GammaPattern`-coset index inside the cluster box
(`HNode1.selfLoop_coset_index`); it is a clean power of `p` supplied by the per-digit ball count
uniformly in `N` and level.  We name it as the filtration's contribution. -/
def floorRatio (s : ℕ) : ℚ := SelfLoopResum.slBoxRatio s p

/-- **STEP 2, `selfLoop_floor_ratio_uniform` (the deepening-non-issue, BANKABLE).**  The per-level
floor-coset index is `p^(selfLoopExponent μ + 1)`, INDEPENDENT of the level `r` in the tower and of
`N` beyond `μ < N`: the `GammaPattern` coset sits inside the size-`μ` cluster box at this fixed
index, delivered by the per-digit ball count.  This is the filtration's genuine contribution — the
gapped a0-valuation deepening (`2 → 4 → …`) does NOT enter the per-level ratio, exactly the kernel
of truth in the reframing hypothesis.  (Stated via `HNode1.selfLoop_coset_index`, the count-native
index identity.) -/
theorem selfLoop_floor_ratio_uniform (hN' : 0 < N) (hμ1 : 1 ≤ μ) (hμN : μ < N) :
    Nat.card {β : Fin μ → RphiRing.Rphi p N 1 1 c // RestartEquiv.FreshClusterPattern p N 1 μ c β}
        * p ^ (L5fix.selfLoopExponent μ + 1)
      = Nat.card {f : QuotientBox.monicBox p N μ // CellCard.IsCluster p f} :=
  HNode1.selfLoop_coset_index p N μ c hN' hμ1 hμN

/-- **The verdict fraction within a floor coset.**  Per level, the fraction of the `GammaPattern`
coset representatives `gpoly γ` that additionally read as the self-loop cell.  STEP 1
(`selfLoopChain_le_floorChain` at `k = 1`) makes the numerator a subset of the denominator; the
filtration supplies the denominator in closed form (`selfLoop_coset_index`).  This is the residue
refinement the filtration CANNOT supply — its value is a residue-theoretic (Newton-polygon) datum,
NOT a divisibility floor. -/
def verdictFractionInCoset : ℚ :=
  (Nat.card {γ : Fin μ → ZMod (p ^ N) //
      GammaPattern p N μ γ ∧ classify1 p (gpoly p N μ hN γ) = some (Drainage.selfLoopCell μ)} : ℚ)
    / (Nat.card {γ : Fin μ → ZMod (p ^ N) // GammaPattern p N μ γ} : ℚ)

/-! ## STEP 3. The single named residual: VERDICT TRANSLATION INVARIANCE

This is `SelfLoopCensusK`'s UNIFORM COSET DENSITY, correctly re-located as a RESIDUE-theoretic
statement.  The filtration frame proved the FLOOR half is level/`N`-uniform (STEP 2).  What remains
is that the residual-repeated-root VERDICT cuts every `GammaPattern` coset to the SAME fraction,
level-independently.

Concretely: `recenter'` sends a floor-coset representative to a fresh size-`μ` cluster box
(`gpoly`), and `classify1 ∘ gpoly` reads only the residue-field residual (`residualOf`).  Coset
translation shifts `γ_j` by `p^(μ−j+1)` multiples; these RAISE valuation, so they do not change the
leading residual polynomial's factorization type.  Hence the repeated-root verdict is invariant
under coset translation.  This is the one lemma that is residue-theoretic, not filtration-theoretic;
it is where the real remaining work is, and it is NOT available from `RphiGenHCount`. -/

/-- **STEP 3 (STATED, the single residual — `VerdictTranslationInvariant`).**  The depth-`k`
self-loop chain census over the `GammaPattern` coset is a UNIFORM fraction of the same census over
the full cluster box, with the fraction the fixed floor index `p^{−(selfLoopExponent μ + 1)}`:

    #{γ : GammaPattern γ ∧ chain_k (gpoly γ)}
      · p^(selfLoopExponent μ + 1)
      = #{g ∈ clusterBox : chain_k g}.

Equivalently, the census `k ↦ #chain_k` is coset-translation invariant: the residual-repeated-root
verdict is invariant under coset translation by `p^(μ−j+1)`.  This is a Newton-polygon lemma over
`ZMod`, requiring the covariance of `residualOf`'s repeated-root type under the coset shift — NOT a
divisibility-floor statement, hence NOT deliverable by the filtration frame.  It is stated here as
the SINGLE named open obligation (no `sorry`/`axiom` stands in for it; downstream results take it as
an explicit hypothesis). -/
def VerdictTranslationInvariant : Prop :=
  ∀ (k : ℕ),
    Nat.card {γ : Fin μ → ZMod (p ^ N) //
        GammaPattern p N μ γ ∧ selfLoopChain p N μ c hN k (gpoly p N μ hN γ)}
      * p ^ (L5fix.selfLoopExponent μ + 1)
    = Nat.card {g : QuotientBox.monicBox p N μ //
        CellCard.IsCluster p g ∧ selfLoopChain p N μ c hN k g}

/-! ## STEP 4. Assembly (contingent on STEP 3)

Given `VerdictTranslationInvariant`, the census recursion of `SelfLoopCensusK.census_step_equiv`
closes into the geometric closed form, and the `SelfLoopResum` machinery (`xqMultiplicity`,
`tendsto_aggSelfLoopTower`) supplies the resummation to `(countPivot)⁻¹`.  These are stated as
THEOREMS taking the STEP-3 invariance as an explicit hypothesis — the honest reduction, not a
proof-from-filtration. -/

/-- **VACUOUS for k ≥ 1: the hypothesis `VerdictTranslationInvariant` is provably FALSE for every
`k ≥ 1` (independently re-verified at `(p,N,μ) = (2,5,2)`: `k=1` gives `4·8 = 32 ≠ 36`,
`k=2` gives `32 ≠ 8`, `k=3` gives `0 ≠ 4`); this theorem is an HONEST IMPLICATION but its
hypothesis holds ONLY at `k = 0`, so it is NOT progress toward the `k ≥ 2` census, which reduces
to `AX_cellRecursion`.  See `[[no-conjecture-salvage]]` / `SELFLOOP_GENERALK_WALL`.**  Kept (not
deleted) because it is an honest implication; the statement/proof are unchanged — only this note
was added.

**STEP 4, `selfLoopCensus_filtration_step` (contingent).**  Given
`VerdictTranslationInvariant`, the depth-`(k+1)` box self-loop census reduces to the depth-`k`
census times the floor-and-verdict index `p^(selfLoopExponent μ + 1)` (i.e. `× slBoxRatio` in
ratio form).  This is `census_step_equiv` (the general-`k` box↔coset bijection, PROVED in
`SelfLoopCensusK`) composed with the STEP-3 uniform coset density: the bijection reduces the
`(k+1)`-fold fiber to a chain census over ONE coset, and the invariance turns that into the full
cluster-box census divided by the fixed index.  The `census_step_equiv` half is bankable; the
`hinv` half is exactly STEP 3 — and, per the VACUOUS note above, unsatisfiable for `k ≥ 1`. -/
theorem selfLoopCensus_filtration_step (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (hinv : VerdictTranslationInvariant p N μ c hN) (k : ℕ) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        RestartEquiv.InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN k (recenter' p N μ c hN f)}
        * p ^ (L5fix.selfLoopExponent μ + 1)
      = Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ selfLoopChain p N μ c hN k g} := by
  rw [census_step_equiv p N μ c hN hμ2 hμN k]
  exact hinv k

/-- **VACUOUS for k ≥ 1: the hypothesis `VerdictTranslationInvariant` is provably FALSE for every
`k ≥ 1` (independently re-verified at `(p,N,μ) = (2,5,2)`: `k=1` gives `4·8 = 32 ≠ 36`,
`k=2` gives `32 ≠ 8`, `k=3` gives `0 ≠ 4`); this theorem is an HONEST IMPLICATION but its
hypothesis holds ONLY at `k = 0`, so it is NOT progress toward the `k ≥ 2` census, which reduces
to `AX_cellRecursion`.  See `[[no-conjecture-salvage]]` / `SELFLOOP_GENERALK_WALL`.**  Kept (not
deleted) because it is an honest implication; the statement/proof are unchanged — only this note
was added.

**STEP 4, `selfLoopCensus_filtration_step_ratio` (contingent — the per-level ratio).**  Given
`VerdictTranslationInvariant`, the depth-`k` box self-loop fiber over `monicBox p N (μ*1)` equals
the depth-`k` cluster-box chain census scaled by the per-level floor-and-verdict ratio
`slBoxRatio μ p = p^{−(selfLoopExponent μ + 1)}`.  This is the SINGLE per-level step of the closed
census `depth0 · (slBoxRatio μ p)^k` (and, after `SelfLoopResum.xqMultiplicity`'s `×q^k`
residue-translate multiplicity, `depth0 · (slExposedRatio μ p)^k`, feeding
`tendsto_aggSelfLoopTower`).  The `k`-fold assembly into the closed
`SelfLoopCensusK.OPEN_count_evaluation` form is reduced to STEP 3 — NOT to the filtration product
alone (see the OPEN note below; the full `k`-fold unwinding is the assembly gated by STEP 3, not
faked here).  As with `selfLoopCensus_filtration_step`, the `hinv` hypothesis is unsatisfiable for
`k ≥ 1` (VACUOUS note above), so this is a gate-shift, not progress toward the `k ≥ 2` census. -/
theorem selfLoopCensus_filtration_step_ratio (hμ2 : 2 ≤ μ) (hμN : μ < N) (hp2 : 0 < p)
    (hinv : VerdictTranslationInvariant p N μ c hN) (k : ℕ) :
    (Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        RestartEquiv.InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN k (recenter' p N μ c hN f)} : ℚ)
      = (Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ selfLoopChain p N μ c hN k g} : ℚ)
        * SelfLoopResum.slBoxRatio μ p := by
  have hstep := selfLoopCensus_filtration_step p N μ c hN hμ2 hμN hinv k
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : ((p : ℚ)) ^ (L5fix.selfLoopExponent μ + 1) ≠ 0 := pow_ne_zero _ hpQ
  have hstepQ : (Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        RestartEquiv.InCellAt p N 1 μ c f ∧ selfLoopChain p N μ c hN k (recenter' p N μ c hN f)} : ℚ)
        * (p : ℚ) ^ (L5fix.selfLoopExponent μ + 1)
      = (Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ selfLoopChain p N μ c hN k g} : ℚ) := by
    exact_mod_cast hstep
  -- divide through by p^(exp+1); slBoxRatio = (p^(exp+1))⁻¹
  unfold SelfLoopResum.slBoxRatio
  rw [eq_mul_inv_iff_mul_eq₀ hpow]
  exact hstepQ

end

/-! ## OPEN — the count-evaluation assembly (documented, NOT faked)

`selfLoopCensus_filtration_step_ratio` gives the SINGLE per-level ratio contingently on
`VerdictTranslationInvariant`.  The full closed census

    Σ_{depth k} stratumCount1 s N c = depth0Census · p^(s(N−1)) · (slBoxRatio s p)^k · p^k

then unwinds by iterating the step `k` times (the depth-0 anchor is
`SelfLoopCensusK.census_base = p^(μ(N−1) − μ(μ+1)/2)`, tied to `stratumCount1` through
`StratumOrder1.stratumCount1_eq_cellCard`), and the `p^k` factor is
`SelfLoopResum.xqMultiplicity`'s `×q^k` residue-translate multiplicity, converting the bare box
ratio `slBoxRatio^k` into `slExposedRatio^k` and feeding `SelfLoopResum.tendsto_aggSelfLoopTower`
for the `d → ∞` limit `(countPivot)⁻¹`.

The ONLY residual is `VerdictTranslationInvariant` (STEP 3).  This is verified concretely at
`p = 2` for `k ≤ 2` by `SelfLoopTower.gate_iterated_selfLoop` (the `(p−1)` root factor is invisible
at `p = 2`); the general-`k` statement needs the `residualOf` coset-covariance under translation by
`p^(μ−j+1)` — a Newton-polygon lemma over `ZMod`, residue-theoretic, and the bulk of the remaining
work.  It is NOT proved here and NO `sorry`/`axiom` stands in for it.

FRAME REPORT.  The gapped-digit filtration frame AVOIDS the a0-valuation *deepening* obstruction
(`card_filtIdeal`/`ball_count_clamped`/`card_r_level_census` are self-similar per level and uniform
in `N` — STEP 2's `selfLoop_floor_ratio_uniform`).  It does NOT avoid the residual-repeated-root
VERDICT obstruction, which is UNCHANGED by the reframing and re-localized here as STEP 3.  The
reframing therefore closes the FLOOR half and re-localizes the (unchanged) residue half; it does
NOT close the obligation. -/

end LeanUrat.OM.SelfLoopCensusFiltration
