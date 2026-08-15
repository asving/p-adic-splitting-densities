/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G14 — the valuation strata of `Res O N` and their exact sizes

**Chapter G, NODE G.14** (`blueprint/CHAP-G_base_cases_menus.md` §4). The two valuation strata
of `Res O N` and their exact sizes, stated without `ℕ`-subtraction and without division (the
level is written `k + r`, so the answers are `q^r` and `q^(r+1) − q^r` in additive form):
`#{x : Res O (k+r) | π^k ∣ x} = q^r`, and
`#{x : Res O (k+r+1) | v(x) = k exactly} + q^r = q^(r+1)`.

DEPENDS: landed `Uniformity.Density.resFactor`, `resFactor_surjective`, `card_res`
(`LocalData.lean:215,221,228`), `card_preimage_of_surjective` (`LocalData.lean:192`),
`mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean:635`).

⚠ RE-DERIVATION TARGET, with its statement discipline: `leancheck/UniformityCheck/Counting.lean`
lands `dvdSet`, `exactSet`, `card_dvdSet` and `card_exactSet_add` in exactly these shapes; the
additive/index-shifted phrasing is deliberate (holds verbatim in residue characteristic 2 and 3,
no side conditions). Chapter G adopts that discipline for every count node.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- The classes of valuation `≥ k`. -/
def dvdSet (π : O) (k N : ℕ) : Set (Res O N) :=
  {x | ∃ y : O, Ideal.Quotient.mk _ (π ^ k * y) = x}

/-- The classes of valuation exactly `k`. -/
def exactSet (π : O) (k N : ℕ) : Set (Res O N) := dvdSet π k N \ dvdSet π (k + 1) N

theorem card_dvdSet (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (dvdSet π k (k + r)) = residueCard O ^ r := by
  have hle : k ≤ k + r := Nat.le_add_right k r
  set f := (resFactor (O := O) hle).toAddMonoidHom with hf
  have hsurj : Function.Surjective f := resFactor_surjective hle
  have hset : dvdSet π k (k + r) = f ⁻¹' {0} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change resFactor (O := O) hle (Ideal.Quotient.mk _ (π ^ k * y)) = 0
      rw [resFactor_mk, Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_dvd hπ]
      exact ⟨y, rfl⟩
    · intro hx0
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ (k + r)) x
      have hx0' : resFactor (O := O) hle (Ideal.Quotient.mk _ z) = 0 := hx0
      rw [resFactor_mk, Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_dvd hπ] at hx0'
      obtain ⟨y, hy⟩ := hx0'
      exact ⟨y, by rw [hy]⟩
  have h1 : Nat.card (f ⁻¹' ({0} : Set (Res O k)))
      = Nat.card f.ker * Nat.card ({0} : Set (Res O k)) :=
    card_preimage_of_surjective f hsurj {0}
  have h2 : Nat.card (f ⁻¹' (Set.univ : Set (Res O k)))
      = Nat.card f.ker * Nat.card (Set.univ : Set (Res O k)) :=
    card_preimage_of_surjective f hsurj Set.univ
  have hcard0 : Nat.card ({0} : Set (Res O k)) = 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_singleton]
  have hu1 : Nat.card (Set.univ : Set (Res O (k + r))) = residueCard O ^ (k + r) := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, card_res]
  have hu2 : Nat.card (Set.univ : Set (Res O k)) = residueCard O ^ k := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, card_res]
  rw [Set.preimage_univ, hu1, hu2] at h2
  rw [hcard0, mul_one] at h1
  rw [hset, h1]
  have hpow : residueCard O ^ (k + r) = residueCard O ^ k * residueCard O ^ r := pow_add _ k r
  rw [hpow, mul_comm (Nat.card f.ker)] at h2
  have hpos : 0 < residueCard O ^ k := pow_pos (residueCard_pos O) k
  exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm

theorem card_exactSet_add (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (exactSet π k (k + r + 1)) + residueCard O ^ r = residueCard O ^ (r + 1) := by
  have hsub : dvdSet π (k + 1) (k + r + 1) ⊆ dvdSet π k (k + r + 1) := by
    rintro x ⟨y, rfl⟩
    exact ⟨π * y, by congr 1; ring⟩
  have hkey := Set.ncard_sdiff_add_ncard_of_subset hsub
  rw [← Nat.card_coe_set_eq (dvdSet π k (k + r + 1) \ dvdSet π (k + 1) (k + r + 1)),
    ← Nat.card_coe_set_eq (dvdSet π (k + 1) (k + r + 1)),
    ← Nat.card_coe_set_eq (dvdSet π k (k + r + 1))] at hkey
  have e1 : Nat.card (dvdSet π k (k + r + 1)) = residueCard O ^ (r + 1) := by
    have := card_dvdSet (O := O) (π := π) hπ (k := k) (r := r + 1)
    rwa [show k + (r + 1) = k + r + 1 by ring] at this
  have e2 : Nat.card (dvdSet π (k + 1) (k + r + 1)) = residueCard O ^ r := by
    have := card_dvdSet (O := O) (π := π) hπ (k := k + 1) (r := r)
    rwa [show k + 1 + r = k + r + 1 by ring] at this
  rw [e1, e2] at hkey
  rw [← hkey]
  rfl

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_dvdSet
#print axioms Uniformity.Density.Menu.card_exactSet_add

end AxCheck
