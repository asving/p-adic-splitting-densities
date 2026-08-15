/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G10 — `tang_shift`, centre-shift stability of tangency depth

**Chapter G, NODE G.10** (`blueprint/CHAP-G_base_cases_menus.md` §4). *Centre-shift stability.*
If `γ` has depth `≥ t` for `a` and `π^⌈t/2⌉ ∣ (γ' − γ)`, then `γ'` has depth `≥ t` for `a`.
(`⌈t/2⌉` is `(t+1)/2` in `ℕ`-division.)

DEPENDS: landed `Uniformity.Density.Tang`, `Uniformity.Density.qval_shift`
(`Drainage.lean:214`), `Uniformity.Density.qder_shift` (`Drainage.lean:218`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem tang_shift {a : Fin 2 → O} {t : ℕ} {γ γ' : O} (h : Tang π a t γ)
    (hδ : π ^ ((t + 1) / 2) ∣ (γ' - γ)) : Tang π a t γ' := by
  obtain ⟨hv, hd⟩ := h
  set m := (t + 1) / 2 with hm
  set s := γ' - γ with hs
  have hγ' : γ' = γ + s := by rw [hs]; ring
  have hle : t ≤ m + m := by omega
  have hpow : π ^ (m + m) = π ^ m * π ^ m := pow_add π m m
  have hss : s ^ 2 = s * s := by ring
  refine ⟨?_, ?_⟩
  · rw [hγ', qval_shift, hss]
    have e2 : π ^ (m + m) ∣ qder a γ * s := by rw [hpow]; exact mul_dvd_mul hd hδ
    have e3 : π ^ (m + m) ∣ s * s := by rw [hpow]; exact mul_dvd_mul hδ hδ
    exact dvd_add (dvd_add hv (dvd_trans (pow_dvd_pow π hle) e2))
      (dvd_trans (pow_dvd_pow π hle) e3)
  · rw [hγ', qder_shift]
    exact dvd_add hd (hδ.mul_left 2)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.tang_shift

end AxCheck
