/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G19
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G30a — `depthSet_odd_eq_empty`, the ODD strata above the window vanish

**Chapter G, MICRO-NODE G.30a** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT 2026-08-15
§A-7 — the dependency-gap cure for G.31). *Above the level-`N` window there is no class of
exact ODD depth*: `depthSet π N (2j+1) = ∅` whenever `N ≤ 2j+1`.

This is the missing supplier of G.31: its statement sums the ram-decided classes over
`j ∈ Finset.range N`, an index set that overshoots the genuine odd strata `2j+1 < N`, so the
⊇ inclusion needs the overshoot `N ≤ 2j+1 ≤ 2N−1` to contribute nothing.

**PROOF.** A class of depth `≥ 2j+1` at level `N ≤ 2j+1` can be pushed one step deeper *inside
its own class*: for a lift `a` with `Tang π a (2j+1) γ`, kill the value at the centre by
`b := ![a 0 − qval a γ, a 1]` (G.33's move). Then `qval b γ = 0`, so `b` has depth `≥ 2j+2` at
`γ`, and `b` is still a lift of the same class because `a 0 − b 0 = qval a γ` is divisible by
`π ^ (2j+1)` hence by `π ^ N`. The derivative side costs nothing **because the depth is odd**:
`Tang` asks for `π ^ ⌈t/2⌉ ∣ qder`, and `⌈(2j+1)/2⌉ = j+1 = ⌈(2j+2)/2⌉`, so the requirement at
depth `2j+2` is the one already in hand.

**⚠ THE EVEN ANALOGUE IS FALSE — see AMENDMENT §A-7.** `depthSet π N t = ∅ for t ≥ N` (the
shape the wave-3 fleet booked as its obstruction) does NOT hold at even `t` in residue
characteristic 2: over `O = ℤ₂`, `π = 2`, `N = 2`, the class of `![0, 2]` lies in
`depthSet 2 2 2`. There the derivative requirement genuinely increases (`⌈2k/2⌉ = k`,
`⌈(2k+1)/2⌉ = k+1`) and the residual quadratic `z² + b₁z + b₀` cannot be given a double root
while `b₁ mod π` is pinned by the class. The odd statement below is exactly the true part, and
exactly the part G.31's odd-indexed union consumes.

DEPENDS: G.19 · landed `Uniformity.Density.proj_eq_iff_dvd` (`DensityAPI.lean:124`),
`Uniformity.Density.qval`, `Uniformity.Density.qder`, `Uniformity.Density.Tang`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **Odd strata above the window are empty.** At level `N`, no class has exact depth `2j+1`
once `N ≤ 2j+1`: the value at the centre can be killed without leaving the class, which pushes
the depth to `2j+2` at no cost on the derivative side (`⌈(2j+1)/2⌉ = ⌈(2j+2)/2⌉`). The even
analogue is FALSE in residue characteristic 2 (module docstring). -/
theorem depthSet_odd_eq_empty (hπ : Irreducible π) {N j : ℕ} (hN : N ≤ 2 * j + 1) :
    depthSet π N (2 * j + 1) = (∅ : Set (Coeff O 2 N)) := by
  refine Set.eq_empty_iff_forall_notMem.2 fun c hc => ?_
  obtain ⟨a, ha, γ, hTang⟩ := hc.1
  refine hc.2 ⟨![a 0 - qval a γ, a 1], ?_, γ, ?_, ?_⟩
  · rw [← ha, proj_eq_iff_dvd hπ]
    intro i
    fin_cases i <;> simp [dvd_trans (pow_dvd_pow π hN) hTang.1]
  · have hz : qval ![a 0 - qval a γ, a 1] γ = 0 := by
      simp only [qval, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
    rw [hz]
    exact dvd_zero _
  · have hq : qder ![a 0 - qval a γ, a 1] γ = qder a γ := by
      simp only [qder, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hq, show (2 * j + 1 + 1 + 1) / 2 = (2 * j + 1 + 1) / 2 by omega]
    exact hTang.2

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.depthSet_odd_eq_empty

end AxCheck
