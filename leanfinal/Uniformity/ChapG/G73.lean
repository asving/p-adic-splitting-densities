/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G73 — `species3`, the W12-S3.2 species

**Chapter G, NODE G.73** (`blueprint/CHAP-G_base_cases_menus.md` §10). *The W12-S3.2 species.*
The level-`N` cubic classes with `a₀ ≡ a₁ ≡ 0 (mod π^N)` and `a₂` free — `q^N` classes.

DEPENDS: landed `Uniformity.Density.Coeff`, `Uniformity.Density.card_res`.

⚠ COORDINATE NOTE (blueprint, carried forward verbatim). The corpus counts `q` centres ×
`q^(N−1)` recentred states; this node counts one centre (`γ = 0`) with `a₂` free over the
*whole* of `Res O N`. Both give `q^N` — the translation bijection (`EFF.HEX3.02`) is exactly the
identification of the two pictures, and the Lean node takes the simpler one. This is a real
(harmless) divergence from the source's bookkeeping and a cross-read item.

**PROOF.** the map `c ↦ c 2` is a bijection `species3 N ≃ Res O N` (inverse `x ↦ ![0, 0, x]`);
`card_res`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The `q^N`-element species of `EFF.HEX3.07` / LEMMA W12-S3.2: separation data hidden, `b₂`
free and visible. -/
def species3 (N : ℕ) : Set (Coeff O 3 N) := {c | c 0 = 0 ∧ c 1 = 0}

/-- The `c ↦ c 2` bijection witnessing `species3 N ≃ Res O N`; a private helper (not part of the
node's SIGNATURE) discharging `card_species3`. -/
private def species3Equiv (N : ℕ) : species3 (O := O) N ≃ Res O N where
  toFun c := c.1 2
  invFun x := ⟨![0, 0, x], by simp [species3]⟩
  left_inv := by
    rintro ⟨c, hc0, hc1⟩
    ext i
    fin_cases i <;> simp [hc0, hc1]
  right_inv := by intro x; simp

theorem card_species3 (N : ℕ) : Nat.card (species3 (O := O) N) = residueCard O ^ N := by
  rw [Nat.card_congr (species3Equiv (O := O) N), card_res]

section AxCheck
#print axioms Uniformity.Density.Menu.card_species3
end AxCheck

end Uniformity.Density.Menu
