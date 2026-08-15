/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H51 — class separation mod `e₁`

**Chapter H, NODE H.51** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer).
Source: `EFF.GENHN.27` (`LEMMA GENHN-2`): *"the minimum's residue class mod `e₁` is `i·h mod e₁`
(distinct for distinct `i` mod `e₁` since `gcd(h, e₁) = 1`)"*.

If `h` and `e` are coprime then multiplication by `h` is injective on residues mod `e`; in
particular `i ↦ i * h % e` separates the classes `i < e`, and (being an injective self-map of the
finite set `Finset.range e`) it is a bijection of `range e` onto itself.

DEPENDS: none beyond mathlib (`Nat.ModEq.cancel_right_of_coprime`,
`Set.Finite.injOn_iff_bijOn_of_mapsTo`).

**PROOF.** `class_sep`: `hmod` *is* `i * h ≡ i' * h [MOD e]`; cancel the coprime factor `h` to get
`i ≡ i' [MOD e]`, then `Nat.mod_eq_of_lt` on both sides. `class_sep_bij`: the map sends
`range e` into `range e` (`Nat.mod_lt`, after dispatching `e = 0` where `range 0 = ∅`), it is
injective there by `class_sep`, and an injective self-map of a finite set is bijective.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- **H.51 (a) — class separation mod `e`.** If `h` is coprime to `e`, then the residues
`i * h % e` for `i < e` are pairwise distinct. -/
theorem class_sep {h e : ℕ} (hcop : Nat.Coprime h e) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmod : i * h % e = i' * h % e) : i = i' := by
  have hgcd : Nat.gcd e h = 1 := hcop.symm
  have hcancel : i ≡ i' [MOD e] := Nat.ModEq.cancel_right_of_coprime hgcd hmod
  have : i % e = i' % e := hcancel
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at this

/-- **H.51 (b) — the class map is a bijection of `range e` onto itself.** -/
theorem class_sep_bij {h e : ℕ} (hcop : Nat.Coprime h e) :
    Set.BijOn (fun i => i * h % e) (Finset.range e) (Finset.range e) := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp
  · have hmaps : Set.MapsTo (fun i => i * h % e) (Finset.range e) (Finset.range e) := by
      intro i _
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.mod_lt _ he
    have hinj : Set.InjOn (fun i => i * h % e) (Finset.range e) := by
      intro i hi i' hi' hmod
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      exact class_sep hcop hi hi' hmod
    exact ((Finset.range e : Finset ℕ).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj

section AxCheck
#print axioms Uniformity.Density.Induction.class_sep
#print axioms Uniformity.Density.Induction.class_sep_bij
end AxCheck

end Uniformity.Density.Induction
