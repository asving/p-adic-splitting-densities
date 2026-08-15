/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G19
import Uniformity.ChapG.G25
import Uniformity.ChapG.G26
import Uniformity.ChapG.G27
import Uniformity.ChapG.G28

/-!
# Uniformity.ChapG.G30 — `depth_type`, the stratum-to-type map

**Chapter G, NODE G.30** (`blueprint/CHAP-G_base_cases_menus.md` §5). *The stratum-to-type map.*
For `t < N`: if `t = 2j+1` is odd, every class of `depthSet π N t` is `ramType`-decided; if
`t = 2k` is even, every class of `depthSet π N t` is `inertType`-decided or `splitType`-decided,
according to the dichotomy of G.26.

**⚠ BOUNDARY NOTE WITHDRAWN 2026-08-15 (blueprint AMENDMENT §A-2).** The blueprint's original
`⚠ BOUNDARY CONDITION, DECLARED` block worried that the even branch's separable case needed
`2k+2 ≤ N` (one more than the odd branch), losing the top even stratum `t = N−1`. That worry is
resolved upstream at G.28, whose landed signature already carries the weaker `hN : 2*k+1 ≤ N` —
exactly `t < N` for `t = 2k` — so this node's even branch needs no extra hypothesis and no
stratum is lost.

DEPENDS: G.19, G.25, G.26, G.27, G.28 · landed `decidedSet_disjoint` (`GenuineDensity.lean:92`),
`inertType_ne_ramType`, `splitType_ne_inertType`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem depth_type (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {N t : ℕ} (ht : t < N) {c : Coeff O 2 N} (hc : c ∈ depthSet π N t) :
    (∃ j, t = 2 * j + 1 ∧ DecidedAt O 2 ramType N c)
      ∨ (∃ k, t = 2 * k ∧ (DecidedAt O 2 inertType N c ∨ DecidedAt O 2 splitType N c)) := by
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨j, hj⟩
  · -- `t` even, `t = k + k`
    right
    refine ⟨k, by omega, ?_⟩
    obtain ⟨a, ha, γ, hTang⟩ := hc.1
    have hTang' : Tang π a (2 * k) γ := by rwa [show 2 * k = t by omega]
    have hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ' := by
      rintro ⟨γ', hγ'⟩
      refine hc.2 ⟨a, ha, γ', ?_⟩
      rwa [show t + 1 = 2 * k + 1 by omega]
    have hderdvd : π ^ k ∣ qder a γ := by
      have h := hTang'.2
      rwa [show (2 * k + 1) / 2 = k by omega] at h
    obtain ⟨b₀, hb₀⟩ := hTang'.1
    obtain ⟨b₁, hb₁⟩ := hderdvd
    rcases depth_even_dichotomy hπ (N := N) hTang' hmax hb₀ hb₁ with hani | ⟨z, hz, hs⟩
    · left
      have hd := decidedAt_inert_of_ani hπ (N := N) (by omega) hb₀ hb₁ hani
      rwa [ha] at hd
    · right
      have hd := decidedAt_split_of_sep hπ (N := N) (by omega) hb₀ hb₁ hz hs
      rwa [ha] at hd
  · -- `t` odd, `t = 2 * j + 1`
    left
    refine ⟨j, hj, ?_⟩
    have hc' : c ∈ depthSet π N (2 * j + 1) := by rwa [← hj]
    exact decidedAt_ram_of_depth_odd hπ hc' (by omega)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.depth_type

end AxCheck
