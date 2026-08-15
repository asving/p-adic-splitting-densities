/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.AnisotropicForms

/-!
# Uniformity.ChapG.G38 — `two_mul_card_aniForm`

**Chapter G, NODE G.38** (`blueprint/CHAP-G_base_cases_menus.md` §7). Over a finite field, the
anisotropic pairs number `q(q−1)/2`, stated subtraction-free:
`2·#{p | AniForm p} + q = q·q`.

DEPENDS: landed `Uniformity.Density.AniForm`, `Uniformity.Density.rootPairMap`,
`Uniformity.Density.rootPairMap_injective`, `Uniformity.Density.exists_rootPairMap_iff`,
`Uniformity.Density.two_mul_choose_two` (`AnisotropicForms.lean:55–124`), mathlib
`Sym2.natCard`.

**PROOF.** `rootPairMap` corestricts to a bijection `Sym2 K ≃ {p // ¬ AniForm p}` (injective
everywhere, and its range is exactly the non-anisotropic pairs by `exists_rootPairMap_iff`), so
`Nat.card {p // ¬ AniForm p} = Nat.card (Sym2 K) = (q+1).choose 2`; the two subtypes `AniForm`/
`¬ AniForm` are complementary in `K × K` (`Equiv.sumCompl`), giving
`Nat.card {AniForm} + Nat.card {¬AniForm} = q * q`; combine with `two_mul_choose_two`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

theorem two_mul_card_aniForm (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // AniForm p} + Nat.card K = Nat.card K * Nat.card K := by
  classical
  have hmapsto : ∀ z : Sym2 K, ¬ AniForm (rootPairMap K z) := fun z =>
    (exists_rootPairMap_iff (rootPairMap K z)).1 ⟨z, rfl⟩
  have hbij : Function.Bijective
      (fun z : Sym2 K => (⟨rootPairMap K z, hmapsto z⟩ : {p : K × K // ¬ AniForm p})) := by
    constructor
    · intro z w h
      exact rootPairMap_injective (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨z, hz⟩ := (exists_rootPairMap_iff p).2 hp
      exact ⟨z, Subtype.ext hz⟩
  have hcard1 : Nat.card (Sym2 K) = Nat.card {p : K × K // ¬ AniForm p} :=
    Nat.card_eq_of_bijective _ hbij
  have hy : Nat.card {p : K × K // ¬ AniForm p} = (Nat.card K + 1).choose 2 := by
    rw [← hcard1, Sym2.natCard]
  have hcard2 : Nat.card {p : K × K // AniForm p} + Nat.card {p : K × K // ¬ AniForm p}
      = Nat.card K * Nat.card K := by
    rw [← Nat.card_prod, ← Nat.card_sum, Nat.card_congr (Equiv.sumCompl AniForm)]
  have h2 := two_mul_choose_two (Nat.card K)
  nlinarith [hcard2, hy, h2]

section AxCheck
#print axioms Uniformity.Density.Menu.two_mul_card_aniForm
end AxCheck

end Uniformity.Density.Menu
