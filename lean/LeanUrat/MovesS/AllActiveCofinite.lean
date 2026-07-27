/-
Unit U-22b `allActive_cofinite` (medium) — PER-CELL keyed (R45); split (R48).
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are
roots of some not-identically-zero cell-size polynomial)".  Route IN SCOPE
(Fable#7-GAP-2): the exceptional pools are roots of the finitely many PER-CELL
polynomials `cellP ≠ 0` (root-set finiteness over the finitely many (e, τ, c);
act_iff per cell); infinitude = `M.pools_infinite` minus the finite root union.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem allActive_cofinite {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) :
    {q₀ ∈ M.Pools | q₀ ∉ allActivePools M}.Finite ∧ (allActivePools M).Infinite := by
  classical
  -- Part 1: the exceptional pools sit inside the finite root-union of the per-cell
  -- polynomials, hence are finite.
  have hfin : {q₀ ∈ M.Pools | q₀ ∉ allActivePools M}.Finite := by
    apply Set.Finite.subset
      ((Finset.Icc 1 n).biUnion (fun e =>
        Finset.univ.biUnion (fun τ : T.State e =>
          Finset.univ.biUnion (fun c : M.Cell e τ =>
            (RB.cellP e τ c).roots.toFinset)))).finite_toSet
    intro q₀ hq
    obtain ⟨hpool, hnot⟩ := hq
    -- q₀ ∈ Pools but not all-active: extract a failing (e, τ).
    simp only [allActivePools, Set.mem_setOf_eq] at hnot
    push_neg at hnot
    obtain ⟨e, he, τ, hτ⟩ := hnot hpool
    -- act_iff turns inactivity into a vanishing cell polynomial (a root).
    rw [RB.act_iff q₀ hpool e he τ] at hτ
    push_neg at hτ
    obtain ⟨c, hc⟩ := hτ
    -- membership in the finite root-union
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨e, he, τ, c, RB.cellP_nonzero e he τ c, hc⟩
  refine ⟨hfin, ?_⟩
  -- Part 2: all-active pools = Pools minus a finite set, so infinite.
  have hsub : M.Pools \ {q₀ ∈ M.Pools | q₀ ∉ allActivePools M} ⊆ allActivePools M := by
    intro q₀ hq
    obtain ⟨hpool, hnotE⟩ := hq
    by_contra hcon
    exact hnotE ⟨hpool, hcon⟩
  exact (M.pools_infinite.sdiff hfin).mono hsub

end LeanUrat.MovesS
