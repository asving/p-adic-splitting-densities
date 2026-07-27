/-
Unit `n2_shapefam` (easy; S5 construction batch) — ShapeFam (the n = 2 root
shapes, δOf ≡ 1); consumedDeltas = {1} at this instance (no split outcomes).
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/-- THE n = 2 root shape: one leg at block e = 2 (state τ★), base-change factor
δ = 1 (CONVENTION DELTA-ABS). -/
noncomputable def n2RootShape : Shape n2T where
  k := 1
  eOf := fun _ => 2
  eIcc := fun _ => by decide
  τOf := fun _ => n2τ
  δOf := fun _ => 1
  σ0 := 0

noncomputable def n2F : ShapeFam n2T := ⟨{n2RootShape}⟩

theorem n2_shapefam :
    (∀ Ŝ ∈ n2F.Sh, ∀ i, Ŝ.δOf i = 1) ∧
    n2F.Sh.Nonempty ∧
    consumedDeltas n2T n2F = {1} := by
  refine ⟨?_, ?_, ?_⟩
  · -- every leg's δ is 1 (the single shape's δOf is the constant 1)
    intro Ŝ hŜ i
    simp only [n2F, Finset.mem_singleton] at hŜ
    subst hŜ
    rfl
  · -- the family is nonempty
    simp only [n2F]
    exact Finset.singleton_nonempty _
  · -- consumedDeltas = {1}: no split outcomes, and the one leg has δ = 1
    -- Step A: no roster outcome (at any block e ∈ {1,2}) routes to `.split`.
    have hno_split : ∀ e ∈ Finset.Icc 1 2, ∀ (τ : n2T.State e) (o : n2T.Out e τ),
        routeOf (n2T.odata e τ o) ≠ Route.split := by
      obtain ⟨hK, hSpl, hIn, _, _, _, _, hexh, _, hst2, _, hb1⟩ := n2_shape
      intro e he
      rw [Finset.mem_Icc] at he
      obtain ⟨he1, he2⟩ := he
      interval_cases e
      · intro τ o
        rw [(hb1 τ o).1]; decide
      · intro τ o
        have hτ := hst2 τ
        subst hτ
        rcases hexh o with rfl | rfl | rfl
        · rw [hK]; decide
        · rw [hSpl]; decide
        · rw [hIn]; decide
    -- Step B: deltaFactors n2T n2F = {1}.
    have hD : deltaFactors n2T n2F = {1} := by
      ext x
      unfold deltaFactors
      rw [Finset.mem_union]
      constructor
      · rintro (h | h)
        · -- the split-leg part is empty
          exfalso
          rw [Finset.mem_biUnion] at h
          obtain ⟨e, he, h⟩ := h
          rw [Finset.mem_biUnion] at h
          obtain ⟨τ, _, h⟩ := h
          rw [Finset.mem_biUnion] at h
          obtain ⟨o, _, h⟩ := h
          rw [if_neg (hno_split e he τ o)] at h
          exact Finset.notMem_empty x h
        · -- the shape-leg part: every element is δOf i = 1
          rw [Finset.mem_biUnion] at h
          obtain ⟨Ŝ, hŜ, h⟩ := h
          rw [Finset.mem_image] at h
          obtain ⟨i, _, hi⟩ := h
          simp only [n2F, Finset.mem_singleton] at hŜ
          subst hŜ
          rw [Finset.mem_singleton, ← hi]
          rfl
      · intro h
        rw [Finset.mem_singleton] at h
        subst h
        right
        rw [Finset.mem_biUnion]
        refine ⟨n2RootShape, ?_, ?_⟩
        · simp only [n2F, Finset.mem_singleton]
        · rw [Finset.mem_image]
          exact ⟨(0 : Fin 1), Finset.mem_univ _, rfl⟩
    -- Step C: {1} is a fixed point of the closure step, so the iterate is {1}.
    unfold consumedDeltas
    exact Function.iterate_fixed
      (by simp only [hD, Finset.image₂_singleton, mul_one, Finset.union_self]) 2

end LeanUrat.MovesS
