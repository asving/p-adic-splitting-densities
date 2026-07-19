/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0
import LeanUrat.OM.CellPartition
import LeanUrat.OM.Termination
import LeanUrat.OM.RealInstance

/-!
# Order0Capstone — the CONDITIONAL Phase-A capstone `montes_order0` (`notes/VACUITY_SIGMA_BLUEPRINT.md` §2.7 items 4–5)

**The statement.** For each degree-`n` unramified factorization type `σ` (pattern λ ⊢ n), the
ORDER-0 GENERIC-STRATUM density — the level-`N` normalized count of monic degree-`n` cosets whose
genuine OM classifier lands in the pattern-λ leaf menu (the FLAT-FACE, UNIT-CONSTANT-COEFFICIENT
substratum) — is a UNIFORM RATIONAL FUNCTION of `q` (one `num/den` at every `q > 1`), and the REAL
counts at the matched prime `realP` converge to that rational function's value at `realP`.

⚠ **AUDIT SCOPE CORRECTION (SIGMA-1, 2026-07-02 adversarial audit).** The certified substratum is
STRICTLY SMALLER than the order-0-decidable separable stratum: separable reductions with residue
root `0` (lifts of `X·g`, `g(0) ≠ 0`) are order-0-decidable in GMN terms but lie OUTSIDE every
`sepShape` fiber (the flat width-`n` face forces a unit `a₀`). The per-λ certified count is the
PUNCTURED `m̃_λ` (`avail₁ = q − 1`), not the unconditioned `m_λ` (`M₁(q) = q`); the excluded
unramified mass is `(m_λ − m̃_λ)·q^{−n}`, nonzero iff λ has a part of size 1. Concretely at
`realP = 2`, `n = 2`, the SPLIT fiber is genuinely EMPTY (`ff(q−1,2) = 0` at `q = 2`: any two
distinct monic linears over `F₂` include `X`) — certified density `0`, while the full
order-0-decided split density is `1/4`. This is CORRECT behavior, not a bug — do NOT "fix" the
empty fiber; recovering the excluded mass needs the multi-side menu (Phase-A′ extension or
Phase B).

**Honest scope.**
* The menu `sepShapesOf n σ` is the σ-keyed set of order-0 separable leaf shapes: DIRECT
  `ClusterShape` literals indexed by `Nat.Partition n` — tree `[(0, n, n)]`, payload one childless
  cell per part with `δ = 1` and the shared flat face. NO polynomial witnesses are required
  (`treeSize ≤ n` is read off the root slot).
* The per-shape coefficient is the CORRECTED `Order0.rootCount` (engine-reconciled §2.6; equals
  `m_λ(q)·q^{−n}`-shaped choice-count × volume on these shapes — numeric gate PASSED).
* `h_node0` — the per-menu-shape limit `stratumCount T N / realP^{nN} → rootCount T realP` — is an
  explicit HYPOTHESIS. Its Phase-A discharge route (level-1 decidedness of separable-reduction
  cosets + the constant `realP^n`-fold fiber growth, `CountingModel.cylinder_count_stable`) is the
  truth-restoration work item; it is NOT faked here. The FACE-EQUALITY GATE (the classifier's
  emitted generic-stratum shape literally equals `sepShape n λ`) is part of that discharge.
* NO palindromy clause: the separable-stratum MONIC density is genuinely non-palindromic (the
  functional equation belongs to the full projective density — Phase B).
* σ with no unramified pattern (ramified types) get the EMPTY menu: the theorem is then the honest
  triviality "the zero function is rational and the counts converge to 0" — order-0 cannot decide
  ramified types (they live in the undecided pool until Phase B).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.Order0

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom RatFn Polynomial Filter Topology
open LeanUrat.OM

/-! ## The flat order-0 face and the separable leaf menu -/

/-- The generic order-0 side: the flat segment `(0,0)–(n,0)` (the lower Newton polygon of a monic
degree-`n` polynomial with unit constant coefficient). -/
def flatSide (n : ℕ) : NewtonPolygon.Side := ⟨0, n, 0, 0⟩

/-- The generic order-0 lattice face: `toSideFace` of the flat side. -/
noncomputable def flatFace (n : ℕ) : L4.LatticePolygon := M7.toSideFace (flatSide n)

/-- **The order-0 separable leaf shape of pattern `λ ⊢ n`** — a DIRECT `ClusterShape` literal:
tree `[(0, n, n)]` (order 0, cluster size `n`, residual degree `n`) and payload one CHILDLESS cell
per part (ascending part order, matching the classifier's degree-sorted emission), each with
`δ = 1` and the shared flat face. -/
noncomputable def sepShape (n : ℕ) (lam : Nat.Partition n) : ClusterShape :=
  ⟨[(0, n, n)],
   (lam.parts.sort (· ≤ ·)).map (fun d => ⟨d, 1, flatFace n, []⟩)⟩

/-- The unramified factorization type of a partition: `(e, f) = (1, d)` per part. -/
def unramType (n : ℕ) (lam : Nat.Partition n) : FactorizationType :=
  ⟨lam.parts.map (fun d => (1, d))⟩

/-- **The σ-keyed order-0 separable menu**: the shapes of the partitions whose unramified type is
`σ` (a singleton for genuinely unramified degree-`n` σ; EMPTY for ramified σ — order-0 honesty). -/
noncomputable def sepShapesOf (n : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun lam => σ = unramType n lam)).image (sepShape n)

/-! ## The menu shapes are childless, and their reader is faithful -/

/-- The guarded faithful reader on a menu shape returns exactly the payload erasure: one childless
`CountCell` per part. (The descent filter keeps every cell — all children lists are empty.) -/
theorem cellsOfShapeWF_sepShape (n : ℕ) (lam : Nat.Partition n) :
    M7.cellsOfShapeWF (sepShape n lam)
      = (lam.parts.sort (· ≤ ·)).map (fun d => ⟨d, 1, flatFace n, []⟩) := by
  have h : ∀ c ∈ M7.cellsOfShape (sepShape n lam), ∀ ch ∈ c.children,
      M5.nodeSizeOf ch < M5.nodeSizeOf (sepShape n lam) := by
    intro c hc ch hch
    -- every payload cell of `sepShape` has `children = []`
    simp only [M7.cellsOfShape, sepShape, List.map_map, List.mem_map] at hc
    obtain ⟨d, _, rfl⟩ := hc
    simp at hch
  rw [M7.cellsOfShapeWF_eq_of_descend _ h]
  simp only [M7.cellsOfShape, sepShape, List.map_map]
  rfl

/-- Every cell of a menu shape is childless (the `hleaf` input to
`rootCount_isRational_of_leaf`). -/
theorem sepShape_leaf (n : ℕ) (lam : Nat.Partition n) :
    ∀ c ∈ M7.cellsOfShapeWF (sepShape n lam), c.children = [] := by
  intro c hc
  rw [cellsOfShapeWF_sepShape] at hc
  rw [List.mem_map] at hc
  obtain ⟨d, _, rfl⟩ := hc
  rfl

/-! ## Rationality closure over the finite menu -/

/-- Finite `Finset`-indexed sums of uniform rational functions are uniform rational functions. -/
theorem isRationalFn_finsetSum {α : Type*} (s : Finset α) (f : α → ℕ → ℚ)
    (h : ∀ a ∈ s, IsRationalFn (f a)) :
    IsRationalFn (fun q => ∑ a ∈ s, f a q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRationalFn_const 0
  | insert a s ha ih =>
      have hfa : IsRationalFn (f a) := h a (Finset.mem_insert_self a s)
      have hs : IsRationalFn (fun q => ∑ b ∈ s, f b q) :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have := isRationalFn_add hfa hs
      simpa [Finset.sum_insert ha] using this

/-! ## The Phase-A capstone -/

/-- **`montes_order0` (Phase A, `notes/VACUITY_SIGMA_BLUEPRINT.md` §2.7 item 5).** For a degree-`n`
type `σ`, the order-0 separable-stratum density function
`g_σ : q' ↦ ∑_{T ∈ sepShapesOf n σ} rootCount T q'`
(the CORRECTED, engine-reconciled per-shape coefficients — `m_λ(q')·q'^{−B}` choice-count × volume
on this childless menu) is a UNIFORM RATIONAL FUNCTION of `q'` (one `num/den`, denominator
nonvanishing at every `q' > 1`), and — GIVEN the per-shape counting limit `h_node0` (the honest
Phase-A hypothesis; its discharge is the level-1 stability work item) — the REAL normalized counts
of the σ-menu strata at the matched prime `realP` converge to `num(realP)/den(realP)`.

NO palindromy clause (the monic separable stratum is genuinely non-palindromic; the functional
equation lives with the full projective density, Phase B). For ramified σ the menu is empty and the
statement is the honest triviality about the zero function. -/
theorem montes_order0 (n : ℕ) (σ : FactorizationType)
    (h_node0 : ∀ T ∈ sepShapesOf n σ,
      Filter.Tendsto
        (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP))) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf n σ,
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) := by
  classical
  -- (1) each menu shape is childless, so its corrected coefficient is rational:
  have hrat : ∀ T ∈ sepShapesOf n σ,
      IsRationalFn (fun q' =>
        rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q') := by
    intro T hT
    rw [sepShapesOf, Finset.mem_image] at hT
    obtain ⟨lam, _, rfl⟩ := hT
    exact rootCount_isRational_of_leaf _ _ _ _ (sepShape_leaf n lam)
  -- (2) the finite menu sum is rational:
  obtain ⟨num, den, hden, hall⟩ :=
    isRationalFn_finsetSum (sepShapesOf n σ)
      (fun T q' => rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q') hrat
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) the value tie at `realP`: sum of the per-shape limits (h_node0) = the rational value.
  have hq : 1 < M9.realP := by unfold M9.realP; norm_num
  have hsum : Filter.Tendsto
      (fun N => ∑ T ∈ sepShapesOf n σ,
        M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (∑ T ∈ sepShapesOf n σ,
        rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP)) :=
    tendsto_finsetSum (sepShapesOf n σ) (fun T hT => h_node0 T hT)
  have hpush : (fun N => (∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
        / (M9.realP : ℚ) ^ (n * N))
      = fun N => ∑ T ∈ sepShapesOf n σ,
          M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N) := by
    funext N
    rw [Finset.sum_div]
  rw [hpush]
  have hval := (hall M9.realP hq).2
  rw [← hval]
  exact hsum

end LeanUrat.OM.Order0
