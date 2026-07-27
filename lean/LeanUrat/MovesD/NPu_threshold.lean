/-
Unit NPu.threshold  (MovesD campaign, E-phase)  [REV 6, Codex#4 f.4]
moves_ref: L12: "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if
Pref(P̂) = ∅ … N(P̂) is finite" — NP is the DEFINED formula (§3.3; the max collapses by
shape-constancy; the empty convention falls out of the sup). `hstab` is DERIVED, not
assumed (the rev-5 field deleted).  [REV 7: NP_stab is stated on the INHABITED branch
(NP = NPband); the empty branch never consumes stability.]
deps: Defs, L9s.
sketch: NP_stab — every band coordinate has level ≤ NP − 1 (the filter's sup), so the
level-range extension beyond NP adds nothing; combine with L9s at Nshape via
NP_le_Nshape.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.L9s_Astable

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- 1 ≤ N(P̂) (both branches of the piecewise NP). -/
theorem NP_pos : 1 ≤ P.NP pol := by
  unfold Shape.NP
  split
  · rw [ShapePrefix.NPband]; omega
  · omega

/-- N(P̂) ≤ Nshape(P̂) (sup < Nshape; 1 ≤ Nshape). -/
theorem NP_le_Nshape : P.NP pol ≤ (P : ShapePrefix).Nshape := by
  have hNs : 0 < (P : ShapePrefix).Nshape := by rw [ShapePrefix.Nshape]; omega
  unfold Shape.NP
  split
  · rw [ShapePrefix.NPband, Nat.add_comm 1, Nat.add_one_le_iff, Finset.sup_lt_iff hNs]
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hc
    exact hc.1.1
  · omega

/-- A-stability from NP on (INHABITED branch — NP = NPband). -/
theorem NP_stab [Nonempty (PrefIdx n pol P)] :
    ∀ N : ℕ, P.NP pol ≤ N → (P : ShapePrefix).A n N = (P : ShapePrefix).A' n := by
  classical
  intro N hN
  have hne : Nonempty (PrefIdx n pol P) := inferInstance
  have hNPeq : P.NP pol = (P : ShapePrefix).NPband n := by
    unfold Shape.NP; rw [if_pos hne]
  rw [hNPeq] at hN
  rcases Nat.lt_or_ge N (P : ShapePrefix).Nshape with hcase | hcase
  · unfold ShapePrefix.A' ShapePrefix.A
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.mem_range] at hr
    congr 1
    apply Finset.ext
    intro c
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hband⟩
      exact ⟨⟨lt_of_lt_of_le h1 hcase.le, h2⟩, hband⟩
    · rintro ⟨⟨h1, h2⟩, hband⟩
      refine ⟨⟨?_, h2⟩, hband⟩
      have hmem : c ∈ (Finset.range (P : ShapePrefix).Nshape ×ˢ Finset.range n).filter
          (fun c => ∃ r < (P : ShapePrefix).reads.length, (P : ShapePrefix).bandS n r c) := by
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨h1, h2⟩, ⟨r, hr, hband⟩⟩
      have hlt : c.1 < (P : ShapePrefix).NPband n := by
        rw [ShapePrefix.NPband]
        have hle : c.1 ≤ _ := Finset.le_sup (f := fun c => c.1) hmem
        omega
      exact lt_of_lt_of_le hlt hN
  · exact A_stable hcase

end LeanUrat.MovesD
