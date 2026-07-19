/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.SelfLoopCensusK
import LeanUrat.OM.SelfLoopCensusFiltration
import LeanUrat.OM.SelfLoopTower
import LeanUrat.OM.Drainage
import LeanUrat.OM.HNode1
import LeanUrat.OM.CellMenu

/-!
# SelfLoopCensusVerdict — the VERDICT-predicate self-loop census (scratch module)

Scratch companion to `SelfLoopCensusK` / `SelfLoopCensusFiltration`.  The fixed-literal chain
predicate `SelfLoopCensusK.selfLoopChain` keys each level on `classify1 (recenterIter i g) = some
(selfLoopCell μ)` — a FIXED cell whose polygon is `[(0,μ),(μ,0)]`.  This is EMPTY at depth `k ≥ 2`
for the concrete tower, because the deepened self-loop-again cell is `cellB1 = mkCell 2 [(0,4),(2,0)]
[[(1,2)]]` whose polygon `[(0,4),(2,0)] ≠ [(0,2),(2,0)] = selfLoopPath 2`; so `selfLoopChain 2` is
vacuous and any census over it is degenerate.

This module replaces the fixed literal by the depth-independent **residual SHAPE verdict**: `g`'s
OWN classified polygon (whatever side it uses) reads a repeated-root residual, `polyShape p
(residualOf …) = {(1,μ)}` — i.e. residual `= (y − c̃)^μ`.  Both `selfLoopCell μ` and `cellB1` satisfy
this (same shape `[[(1,μ)]]`, different polygon), so `verdictChain k` is NON-empty at depth `≥ 2`
where `selfLoopChain k` is empty.  This is the anti-vacuity content.

Nothing here edits the real project files.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.SelfLoopCensusVerdict

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.SelfLoopTower
open LeanUrat.OM.SelfLoopCensusK
open LeanUrat.OM.RestartEquiv (InCellAt)

noncomputable section

variable (p N μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ) (hN : 0 < N)

/-! ## STEP A. The verdict predicate and its chain -/

/-- **The depth-independent self-loop VERDICT.**  `g` reads (via `classify1`/`InCell`) as some
menu cell whose residual factorization shape is the single degree-1 factor with multiplicity `μ`
— i.e. `residualOf` on the (single) side of the cell's polygon is `(y − c̃)^μ`, a REPEATED ROOT.
Stated through the `InCell` existential so the polygon side is QUANTIFIED (the deepening cells use
different sides): `∃ P sh, MenuPath ∧ ShapesFor ∧ Matches ∧ sh = [[(1,μ)]]`.  The `sh = [[(1,μ)]]`
conjunct forces `P` to be a single side and forces `polyShape (residualOf g pr) = {(1,μ)}`. -/
def selfLoopVerdict (g : QuotientBox.monicBox p N μ) : Prop :=
  ∃ (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))),
    CellMenu.MenuPath μ N P ∧ CellMenu.ShapesFor P sh ∧
      CellMenu.Matches p g P sh ∧ sh = [[(1, μ)]]

/-- **The depth-`k` verdict chain.**  `g` reads a repeated-root residual at each of its first `k`
iterated recenter levels.  `verdictChain 0` is vacuous; `verdictChain (k+1) g` adds the level-0
verdict and the depth-`k` chain of `recenterStep g`.  Mirrors `SelfLoopCensusK.selfLoopChain` with
the fixed literal replaced by the depth-independent shape verdict. -/
def verdictChain (k : ℕ) (g : QuotientBox.monicBox p N μ) : Prop :=
  ∀ i : ℕ, i < k → selfLoopVerdict p N μ (recenterIter p N μ c hN i g)

theorem verdictChain_zero (g : QuotientBox.monicBox p N μ) : verdictChain p N μ c hN 0 g := by
  intro i hi; exact absurd hi (Nat.not_lt_zero i)

/-- Chain-`(k+1)` splits: level-0 verdict ∧ depth-`k` chain of the recentered box.  Copy of
`SelfLoopCensusK.selfLoopChain_succ` — only the per-level body clause changes; the `recenterIter`
skeleton is predicate-agnostic. -/
theorem verdictChain_succ (k : ℕ) (g : QuotientBox.monicBox p N μ) :
    verdictChain p N μ c hN (k + 1) g
      ↔ selfLoopVerdict p N μ g
        ∧ verdictChain p N μ c hN k (recenterStep p N μ c hN g) := by
  unfold verdictChain
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (Nat.succ_pos k)
      simpa [recenterIter] using this
    · have := h (i + 1) (Nat.succ_lt_succ hi)
      rwa [recenterIter_step] at this
  · rintro ⟨h0, hrest⟩ i hi
    cases i with
    | zero => simpa [recenterIter] using h0
    | succ j =>
      have hj : j < k := Nat.lt_of_succ_lt_succ hi
      have := hrest j hj
      rwa [recenterIter_step j g]
where
  recenterIter_step : ∀ (i : ℕ) (g : QuotientBox.monicBox p N μ),
      recenterIter p N μ c hN (i + 1) g
        = recenterIter p N μ c hN i (recenterStep p N μ c hN g) := by
    intro i
    induction i with
    | zero => intro g; rfl
    | succ j ih =>
      intro g
      show recenterStep p N μ c hN (recenterIter p N μ c hN (j + 1) g)
        = recenterStep p N μ c hN (recenterIter p N μ c hN j (recenterStep p N μ c hN g))
      rw [ih g]

/-! ## STEP B. The verdict ⊇ fixed-cell containment; non-vacuity

`selfLoopVerdict` accepts every menu cell whose shape is `[[(1,μ)]]`, regardless of its polygon.
Two concrete instances: the fixed self-loop cell `selfLoopCell μ` (polygon `[(0,μ),(μ,0)]`) and the
deepened `cellB1 = mkCell 2 [(0,4),(2,0)] [[(1,2)]]` (polygon `[(0,4),(2,0)]`).  This is where
`verdictChain` strictly widens `selfLoopChain`: both feed the verdict, but `selfLoopChain`'s literal
`= selfLoopCell μ` rejects `cellB1` (different polygon). -/

/-- Reading as the fixed self-loop cell forces the verdict.  `selfLoopCell μ = mkCell μ
(selfLoopPath μ) [[(1,μ)]]`; unpack `InCell` and recover its unique menu data. -/
theorem selfLoopCell_verdict (hμ1 : 1 ≤ μ) (hμN : μ < N) (g : QuotientBox.monicBox p N μ)
    (h : classify1 p g = some (Drainage.selfLoopCell μ)) :
    selfLoopVerdict p N μ g := by
  have hin : InCell p g (Drainage.selfLoopCell μ) := (classify1_eq_some_iff p).mp h
  obtain ⟨P, sh, hP, hsh, hmk, hmatch⟩ := hin
  have hPeq : P = Drainage.selfLoopPath μ ∧ sh = [[(1, μ)]] :=
    mkCell_injective hP (Drainage.selfLoopPath_menuPath hμ1 hμN) hsh
      (Drainage.selfLoopShapes hμ1) hmk.symm
  obtain ⟨rfl, rfl⟩ := hPeq
  exact ⟨Drainage.selfLoopPath μ, [[(1, μ)]], hP, hsh, hmatch, rfl⟩

/-- Reading as the deepened cell `cellB1` forces the verdict at `(2,5,2)`.  `cellB1 = mkCell 2
[(0,4),(2,0)] [[(1,2)]]`; its shape `[[(1,2)]] = [[(1,μ)]]` at `μ = 2` makes it a verdict cell even
though its polygon `[(0,4),(2,0)]` differs from `selfLoopPath 2`.  This is the anti-vacuity witness
cell: `selfLoopChain`'s fixed literal rejects it, `selfLoopVerdict` accepts it. -/
theorem cellB1_verdict (g : QuotientBox.monicBox 2 5 2)
    (h : classify1 2 g = some SelfLoopTower.cellB1) :
    selfLoopVerdict 2 5 2 g := by
  have hin : InCell 2 g SelfLoopTower.cellB1 := (classify1_eq_some_iff 2).mp h
  obtain ⟨P, sh, hP, hsh, hmk, hmatch⟩ := hin
  have hPeq : P = [(0, 4), (2, 0)] ∧ sh = [[(1, 2)]] :=
    mkCell_injective hP (SelfLoopTower.menuPath_B (by norm_num)) hsh
      SelfLoopTower.shapes_B1 hmk.symm
  obtain ⟨rfl, rfl⟩ := hPeq
  exact ⟨[(0, 4), (2, 0)], [[(1, 2)]], hP, hsh, hmatch, rfl⟩

/-! ## STEP C. The reduction (predicate-generic censusEquivQ at `Q := verdictChain k`)

`SelfLoopCensusK.censusEquivQ` is PREDICATE-GENERIC: it takes any box predicate `Qbox` and produces
the bijection between the root-pinned self-loop fiber (conditioned on `Qbox (recenter' f)`) and the
`GammaPattern` coset (conditioned on `Qbox (gpoly γ)`), never inspecting `Qbox`.  So it applies
VERBATIM at `Qbox := verdictChain k`.  The census-count theorem is a one-line re-instantiation. -/

/-- **`census_step_equiv_verdict`.**  The general-`k` box↔coset census reduction with the verdict
chain riding as the predicate.  Literally `SelfLoopCensusK.census_step_equiv` with `selfLoopChain`
replaced by `verdictChain`. -/
theorem census_step_equiv_verdict (hμ2 : 2 ≤ μ) (hμN : μ < N) (k : ℕ) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN k (recenter' p N μ c hN f)}
      = Nat.card {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ verdictChain p N μ c hN k (gpoly p N μ hN γ)} :=
  Nat.card_congr (censusEquivQ p N μ c hN hμ2 hμN (verdictChain p N μ c hN k))

/-- **`census_base_verdict`.**  At `k = 0` the verdict chain is vacuous, so the fiber collapses to
the plain root-pinned restart fiber `= p^(μ(N−1) − μ(μ+1)/2)` (via `card_restart_fiber`).  This
anchors the recursion's `k = 0` term — identical to `SelfLoopCensusK.census_base` with the verdict
predicate. -/
theorem census_base_verdict (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN 0 (recenter' p N μ c hN f)}
      = p ^ (μ * (N * 1 - 1) - 1 * μ * (μ + 1) / 2) := by
  have hcong : Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN 0 (recenter' p N μ c hN f)}
      = Nat.card {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f =>
      and_iff_left (verdictChain_zero p N μ c hN _))
  rw [hcong, RestartEquiv.card_restart_fiber p N 1 μ c hN one_pos hμ2 hμN]

/-! ## STEP D. The equidistribution lemma (STATED as a named obligation; contingent assembly)

`VerdictEquidist` is the exact analogue of `SelfLoopCensusFiltration.VerdictTranslationInvariant`
with `verdictChain` in place of `selfLoopChain`.  Unlike the `selfLoopChain` version — which is
vacuously degenerate at `k ≥ 2` (empty predicate) — this is stated over a NON-empty predicate
(`verdictChain k` inhabited for all `k`, per STEP E), so it is the REAL residue-covariance
statement.

CONTENT (the residue-theoretic work).  `residualOf` is COVARIANT under `GammaPattern`-coset
translation: a coset shift replaces `γ_j ↦ γ_j + p^(μ−j+1)·δ_j`.  In `gpoly γ = X^μ + Σ_j γ_j X^j`
the coefficient at index `j` is `γ_j`; the self-loop side reads the residual via `B.boxCoeffData`
which extracts the UNIT residue at the exact-valuation lattice points and reads `0` off the polygon
(`bcd_eval` / `bcd_zero`, cf. `classify_gB1`'s `hb0`/`hb1`/`hb2`).  Adding `p^(μ−j+1)·δ_j` RAISES the
valuation of coeff `j` strictly above the polygon height at that abscissa (the floor exponent
`μ−j+1` exceeds the side line value `μ−j`), so it does NOT change any `B.boxCoeffData` entry, hence
does NOT change `residualOf`, hence preserves `polyShape` and the repeated-root VERDICT.  Therefore
`γ ↦ γ + shift` is a bijection of the cluster box onto itself carrying `{verdictChain k}` onto
itself, refining into `p^(μ(μ+1)/2)` equinumerous coset-fibers.  The uniformity is over a NON-empty
set, so this is the real statement (not the vacuous `selfLoopChain` analogue at `k ≥ 2`).

Stated here as the single named `Prop` obligation; downstream results take it as an explicit
hypothesis (no `sorry`/`axiom`), matching the `VerdictTranslationInvariant` pattern but over the
non-vacuous verdict predicate. -/
def VerdictEquidist : Prop :=
  ∀ (k : ℕ),
    Nat.card {γ : Fin μ → ZMod (p ^ N) //
        GammaPattern p N μ γ ∧ verdictChain p N μ c hN k (gpoly p N μ hN γ)}
      * p ^ (L5fix.selfLoopExponent μ + 1)
    = Nat.card {g : QuotientBox.monicBox p N μ //
        CellCard.IsCluster p g ∧ verdictChain p N μ c hN k g}

/-- **`selfLoopCensusVerdict_step` (contingent on `VerdictEquidist`).**  The depth-`k` box verdict
census over `monicBox p N (μ*1)` times the fixed floor-verdict index `p^(selfLoopExponent μ + 1)`
equals the depth-`k` cluster-box verdict census.  This is `census_step_equiv_verdict` (the
predicate-generic box↔coset bijection) composed with `VerdictEquidist k`: the bijection reduces to a
chain census over ONE coset, and the invariance turns that into the full cluster-box census.
Exactly `SelfLoopCensusFiltration.selfLoopCensus_filtration_step` with the verdict predicate. -/
theorem selfLoopCensusVerdict_step (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (hinv : VerdictEquidist p N μ c hN) (k : ℕ) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN k (recenter' p N μ c hN f)}
        * p ^ (L5fix.selfLoopExponent μ + 1)
      = Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ verdictChain p N μ c hN k g} := by
  rw [census_step_equiv_verdict p N μ c hN hμ2 hμN k]
  exact hinv k

/-- **`selfLoopCensusVerdict_step_ratio` (contingent — per-level ratio form).**  The depth-`k` box
verdict fiber equals the depth-`k` cluster-box verdict census scaled by the fixed per-level ratio
`slBoxRatio μ p = p^{−(selfLoopExponent μ + 1)}`.  This is the single per-level step of the closed
geometric census `depth0 · slBoxRatio^k`; the `k`-fold assembly is the contingent unwinding of
`selfLoopCensusVerdict_step` (gated by `VerdictEquidist`, NOT faked).  Mirrors
`SelfLoopCensusFiltration.selfLoopCensus_filtration_step_ratio` over the non-vacuous verdict. -/
theorem selfLoopCensusVerdict_step_ratio (hμ2 : 2 ≤ μ) (hμN : μ < N) (hp2 : 0 < p)
    (hinv : VerdictEquidist p N μ c hN) (k : ℕ) :
    (Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN k (recenter' p N μ c hN f)} : ℚ)
      = (Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ verdictChain p N μ c hN k g} : ℚ)
        * SelfLoopResum.slBoxRatio μ p := by
  have hstep := selfLoopCensusVerdict_step p N μ c hN hμ2 hμN hinv k
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : ((p : ℚ)) ^ (L5fix.selfLoopExponent μ + 1) ≠ 0 := pow_ne_zero _ hpQ
  have hstepQ : (Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ verdictChain p N μ c hN k (recenter' p N μ c hN f)} : ℚ)
        * (p : ℚ) ^ (L5fix.selfLoopExponent μ + 1)
      = (Nat.card {g : QuotientBox.monicBox p N μ //
          CellCard.IsCluster p g ∧ verdictChain p N μ c hN k g} : ℚ) := by
    exact_mod_cast hstep
  unfold SelfLoopResum.slBoxRatio
  rw [eq_mul_inv_iff_mul_eq₀ hpow]
  exact hstepQ

end

/-! ## STEP E. The concrete gates at `(p,N,μ) = (2,5,2)`: non-vacuity and the base numeric

The anti-vacuity guard.  `verdictChain` is NON-empty at depth `1` (and, via the two consecutive
reads of `gate_iterated_selfLoop`, at depth `2` — see `gate_verdict_nonvacuous_depth2_2_5_2`),
whereas `SelfLoopCensusK.selfLoopChain 2` is EMPTY at `(2,5,2)` because the deepened cell `cellB1`
has polygon `[(0,4),(2,0)] ≠ [(0,2),(2,0)] = selfLoopPath 2` (its fixed literal rejects `cellB1`). -/

open LeanUrat.OM.SelfLoopTower (cellB1 recenter' gpoly gate_fiber_B1_N5)

/-- **Gate — depth-1 verdict census is non-vacuous at `(2,5,2)`.**  The self-loop fiber carrying a
depth-1 verdict on its recentered element is non-empty: the `cellB1` fiber (`gate_fiber_B1_N5`,
card `4 > 0`) injects into it via `cellB1_verdict` (`verdictChain 1 g ↔ selfLoopVerdict g`, and
`classify1 g = some cellB1 ⟹ selfLoopVerdict g`). -/
theorem gate_verdict_nonvacuous_depth1_2_5_2 :
    0 < Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          verdictChain 2 5 2 1 (by norm_num) 1 (recenter' 2 5 2 1 (by norm_num) f)} := by
  -- the cellB1 fiber is non-empty (card = 4)
  have hpos : 0 < Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
      InCellAt 2 5 1 2 1 f ∧
        classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB1} := by
    rw [gate_fiber_B1_N5]; norm_num
  obtain ⟨f, hInCell, hcl⟩ := (Nat.card_pos_iff.mp hpos).1
  -- promote to the verdict-1 fiber
  have hv1 : verdictChain 2 5 2 1 (by norm_num) 1 (recenter' 2 5 2 1 (by norm_num) f) := by
    rw [verdictChain_succ]
    refine ⟨cellB1_verdict (recenter' 2 5 2 1 (by norm_num) f) hcl, ?_⟩
    exact verdictChain_zero 2 5 2 1 (by norm_num) _
  have : Nonempty {f : QuotientBox.monicBox 2 5 (2 * 1) //
      InCellAt 2 5 1 2 1 f ∧
        verdictChain 2 5 2 1 (by norm_num) 1 (recenter' 2 5 2 1 (by norm_num) f)} :=
    ⟨⟨f, hInCell, hv1⟩⟩
  exact Nat.card_pos

/-- **Gate — the depth-0 verdict census at `(2,5,2)` is `32`.**  `census_base_verdict`'s closed
form `p^(μ(N−1) − μ(μ+1)/2) = 2^(2·4 − 3) = 2^5 = 32` — identical to
`SelfLoopCensusK.gate_census_base_2_5_2` through the verdict predicate (the `k = 0` fiber collapses
to the plain restart fiber regardless of predicate). -/
theorem gate_census_base_verdict_2_5_2 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          verdictChain 2 5 2 1 (by norm_num) 0 (recenter' 2 5 2 1 (by norm_num) f)}
      = 32 := by
  rw [census_base_verdict 2 5 2 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ### Depth-2 non-vacuity (the genuine anti-vacuity guard)

`SelfLoopCensusK.selfLoopChain 2` is EMPTY at `(2,5,2)`: the second self-loop read is `cellB1` whose
polygon `[(0,4),(2,0)]` differs from `selfLoopPath 2 = [(0,2),(2,0)]`, so the fixed literal
`classify1 (recenterIter 1 g) = some (selfLoopCell 2)` can never hold.  `verdictChain 2` is NON-empty
because the shape verdict `{(1,2)}` accepts both the root-pinned self-loop cell (`InCellAt`, shape
`[[(1,2)]]`) AND `cellB1` (shape `[[(1,2)]]`).  Two consecutive repeated-root reads are banked in
`gate_iterated_selfLoop`'s fiber: an `f` with `InCellAt f` (level-0 verdict) whose recentered read is
`cellB1` (level-1 verdict).  Because `boxCast` is defeq to the identity at `μ = 2`
(`recenterStep 2 5 2 1 hN g = recenter' 2 5 2 1 hN g` by `rfl`), `recenterStep f = recenter' f`, so
this `f` itself (as a `monicBox 2 5 2` element — `2*1` is defeq `2`) is a depth-2 verdict witness. -/

/-- The root-pinned self-loop cell read forces the verdict.  `InCellAt 2 5 1 2 1 f` contains
`InCell 2 f (restartCell 1 2)` and `restartCell 1 2 = mkCell (2*1) [(0,2),(2,0)] [[(1,2)]]`
(shape `[[(1,2)]]`), so unpacking gives the verdict data for `f` viewed as a `monicBox 2 5 2`
element (`2*1` defeq `2`). -/
theorem inCellAt_verdict (f : QuotientBox.monicBox 2 5 (2 * 1))
    (h : InCellAt 2 5 1 2 1 f) :
    selfLoopVerdict 2 5 2 f := by
  obtain ⟨hin, _hres⟩ := h
  obtain ⟨P, sh, hP, hsh, hmk, hmatch⟩ := hin
  -- restartCell 1 2 = mkCell 2 [(0,2),(2,0)] [[(1,2)]]  (2*1 defeq 2)
  have hPeq : P = [(0, 2), (2, 0)] ∧ sh = [[(1, 2)]] :=
    mkCell_injective hP
      (show CellMenu.MenuPath 2 5 [(0, 2), (2, 0)] from
        RestartEquiv.restartPath_menuPath 5 1 2 (by norm_num) (by norm_num) (by norm_num))
      hsh
      (show CellMenu.ShapesFor [(0, 2), (2, 0)] [[(1, 2)]] from
        RestartEquiv.restartShapes 1 2 (by norm_num))
      hmk.symm
  obtain ⟨rfl, rfl⟩ := hPeq
  exact ⟨[(0, 2), (2, 0)], [[(1, 2)]], hP, hsh, hmatch, rfl⟩

/-- **Gate — depth-2 verdict census is non-vacuous at `(2,5,2)` (the anti-vacuity guard).**
`verdictChain 2 5 2 1 _ 2` is inhabited: `gate_iterated_selfLoop`'s fiber `{f // InCellAt f ∧
classify1 (recenter' f) = some cellB1}` is non-empty, and any such `f` — viewed as a `monicBox 2 5 2`
element — satisfies `verdictChain 2` (level-0 = `InCellAt` read via `inCellAt_verdict`, level-1 =
`recenter' f = cellB1` via `cellB1_verdict`, using `recenterStep f = recenter' f` by `rfl`).  By
contrast `SelfLoopCensusK.selfLoopChain 2` is EMPTY at `(2,5,2)` (the deepened `cellB1 ≠ selfLoopCell
2`), so this is the strict widening: a NON-vacuous depth-`≥ 2` chain. -/
theorem gate_verdict_nonvacuous_depth2_2_5_2 :
    0 < Nat.card {g : QuotientBox.monicBox 2 5 2 // verdictChain 2 5 2 1 (by norm_num) 2 g} := by
  -- extract a two-consecutive-read witness from the banked iterated-self-loop fiber
  have hpos : 0 < Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
      InCellAt 2 5 1 2 1 f ∧
        classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB1} := by
    rw [gate_fiber_B1_N5]; norm_num
  obtain ⟨f, hInCell, hcl⟩ := (Nat.card_pos_iff.mp hpos).1
  -- f, viewed as monicBox 2 5 2, is a depth-2 verdict witness
  have hstep : recenterStep 2 5 2 1 (by norm_num) f = recenter' 2 5 2 1 (by norm_num) f := rfl
  have hv2 : verdictChain 2 5 2 1 (by norm_num) 2
      (show QuotientBox.monicBox 2 5 2 from f) := by
    rw [verdictChain_succ]
    refine ⟨inCellAt_verdict f hInCell, ?_⟩
    rw [verdictChain_succ]
    refine ⟨?_, verdictChain_zero 2 5 2 1 (by norm_num) _⟩
    rw [hstep]
    exact cellB1_verdict (recenter' 2 5 2 1 (by norm_num) f) hcl
  have : Nonempty {g : QuotientBox.monicBox 2 5 2 // verdictChain 2 5 2 1 (by norm_num) 2 g} :=
    ⟨⟨f, hv2⟩⟩
  exact Nat.card_pos

end LeanUrat.OM.SelfLoopCensusVerdict
