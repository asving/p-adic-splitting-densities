/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G38

/-!
# Uniformity.ChapG.G39 — `SepPair`, `two_mul_card_sepPair`

**Chapter G, NODE G.39** (`blueprint/CHAP-G_base_cases_menus.md` §7). Over a finite field, the
pairs whose quadratic has **two distinct roots** number `q(q−1)/2` — the same count as the
anisotropic ones. Subtraction-free: `2·#{p | SepPair p} + q = q·q`.

DEPENDS: G.38 · landed `rootPairMap`, `rootPairMap_injective`, `exists_rootPairMap_iff`,
mathlib `Sym2.natCard`, `Sym2.IsDiag`.

**⚠ ARITHMETIC CROSS-CHECK, verified at AMENDMENT §A-3.** This chapter's strata are indexed by
**all** pairs `(b₀, b₁) ∈ F_q²` (the depth filtration does not normalise `b₀` away), so the split
row here is `q(q−1)/2`, not W-11's `(q−1)(q−2)/2` (which counts only `b₀ ≠ 0`). Both tables are
correct about their own object; see the blueprint's node entry and AMENDMENT §A-3 for the full
reconciliation. Do not "correct" this count to W-11's.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- `p = (b₀, b₁)` is a *separable-split* pair: `X² − b₁X + b₀` has two distinct roots. -/
def SepPair {K : Type*} [Field K] (p : K × K) : Prop :=
  ∃ y z : K, y ≠ z ∧ p = (y * z, y + z)

private theorem sepPair_rootPairMap_of_not_isDiag {K : Type*} [Field K] (s : Sym2 K)
    (hs : ¬ s.IsDiag) : SepPair (rootPairMap K s) := by
  revert hs
  induction s using Sym2.ind with
  | _ y z =>
    intro hs
    rw [rootPairMap_mk]
    rw [Sym2.mk_isDiag_iff] at hs
    exact ⟨y, z, hs, rfl⟩

theorem two_mul_card_sepPair (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // SepPair p} + Nat.card K = Nat.card K * Nat.card K := by
  classical
  have hbij : Function.Bijective
      (fun s : {s : Sym2 K // ¬ s.IsDiag} =>
        (⟨rootPairMap K s.1, sepPair_rootPairMap_of_not_isDiag s.1 s.2⟩ :
          {p : K × K // SepPair p})) := by
    constructor
    · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
      exact Subtype.ext (rootPairMap_injective (congrArg Subtype.val h))
    · rintro ⟨p, y, z, hyz, rfl⟩
      exact ⟨⟨s(y, z), by rw [Sym2.mk_isDiag_iff]; exact hyz⟩, Subtype.ext (rootPairMap_mk y z)⟩
  have hcard1 : Nat.card {s : Sym2 K // ¬ s.IsDiag} = Nat.card {p : K × K // SepPair p} :=
    Nat.card_eq_of_bijective _ hbij
  have hcard2 : Nat.card {s : Sym2 K // s.IsDiag} + Nat.card {s : Sym2 K // ¬ s.IsDiag}
      = Nat.card (Sym2 K) := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl Sym2.IsDiag)]
  have hdiag : Nat.card {s : Sym2 K // s.IsDiag} = Nat.card K := Sym2.natCard_subtype_diag K
  have hy : Nat.card (Sym2 K) = (Nat.card K + 1).choose 2 := Sym2.natCard K
  have h2 := two_mul_choose_two (Nat.card K)
  nlinarith [hcard1, hcard2, hdiag, hy, h2]

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.two_mul_card_sepPair

end AxCheck
