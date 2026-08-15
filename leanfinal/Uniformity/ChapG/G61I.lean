/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G14
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G61I — the `n = 3` census infrastructure

**Chapter G, NODE G.61.0** (`blueprint/CHAP-G_base_cases_menus.md` §9), the *workhorse* half of
the SPLIT-MANDATED node G.61: the plumbing that all five cubic lower bounds
(`G61a`–`G61e`) share, landed first so that each sub-node carries only its own family.

Three groups:

* **`decidedDensity_ge_of_inj`** — an INJECTION of a finite type into the `σ`-decided level-`N`
  classes is a density lower bound `#A / q ^ (n·N) ≤ decidedDensity O n σ`. Only an injection is
  needed, never an exact count, which is what makes the family bounds cheap. (Routed through the
  landed CN-09 `decidedDensity_ge_of_subset` on `Set.range f`.)
* **the level-1 residue reader** — `res1Equiv : Res O 1 ≃+* ResidueField O` and its section
  `liftRes1`, which turns a residue-field coefficient vector into a level-1 class, plus
  `residue_comp_of_proj_liftRes1`: every lift of `liftRes1 v` reduces to `v`. This is the bridge
  that lets the residue-field censuses of G.60 count level-1 classes.
* **the level-2 strata** — `unitSet π N := (dvdSet π 1 N)ᶜ` and the three level-2 cardinalities
  `#(dvdSet π 1 2) = q`, `#(exactSet π 1 2) + 1 = q`, `#(unitSet π 2) + q = q²`, together with the
  two directions of "a level-`N` class lies in `dvdSet π k N` iff `π ^ k` divides any lift"
  (`dvd_of_mem_dvdSet` / `mem_dvdSet_of_dvd`). These are what the two ramified families read.

Also two one-line residue bridges (`sub_mem_of_residue_eq`, `isUnit_sub_of_residue_ne`) shared by
the level-1 sub-nodes.

DEPENDS: G.14 (`dvdSet`, `exactSet`, `card_dvdSet`, `card_exactSet_add`) · landed
`decidedDensity_ge_of_subset` (CN-09, `DensityAPI.lean:160`), `card_res`, `instFiniteRes`,
`residueCard` (`LocalData.lean`), `mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean:635`).

PROOF sketch. `decidedDensity_ge_of_inj`: `Set.range f ⊆ decidedSet` by construction, and
`Nat.card (Set.range f) = Nat.card A` by `Equiv.ofInjective`; feed CN-09. `res1Equiv` is
`Ideal.quotEquivOfEq (pow_one 𝔪)`. `card_dvdSet_two` / `card_exactSet_two` are the G.14 counts at
`(k, r) = (1, 1)` and `(1, 0)`; `card_unitSet_two` splits `Res O 2` along `Equiv.sumCompl`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`
(`res1Equiv`, `liftRes1`, `liftRes1_injective`, `resVec_of_proj`, `sub_mem_of_residue_eq`,
`isUnit_sub_of_residue_ne`) and `leancheck/UniformityCheck/N3Density.lean`
(`decidedDensity_ge_of_inj`, `unitSet`, `card_dvdSet_two`, `card_exactSet_two`,
`card_unitSet_two`, `dvd_of_mem_dvdSet`) land the same content in the sibling project. Re-derived
here against `leanfinal`'s own API per the repo's non-import policy (`leancheck` imports
`leanfinal`, never the reverse).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. The workhorse: an injection is a lower bound -/

section Workhorse

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.61.0, the workhorse.** Only an injection is needed, never an exact count. -/
theorem decidedDensity_ge_of_inj [IsAdicComplete (maximalIdeal O) O]
    {n N : ℕ} {σ : FactorizationType} {A : Type*} [Finite A]
    (f : A → Coeff O n N) (hinj : Function.Injective f)
    (hf : ∀ x, DecidedAt O n σ N (f x)) :
    (Nat.card A : ℝ) / (residueCard O : ℝ) ^ (n * N) ≤ decidedDensity O n σ := by
  have hsub : Set.range f ⊆ decidedSet O n σ N := by
    rintro c ⟨x, rfl⟩
    exact hf x
  have hcard : Nat.card (Set.range f) = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective f hinj)).symm
  have h := decidedDensity_ge_of_subset (O := O) (n := n) (N := N) (σ := σ) hsub
  rwa [hcard] at h

end Workhorse

/-! ## 2. Two residue bridges -/

section Bridges

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Equal residues means the difference is in `𝔪`. -/
theorem sub_mem_of_residue_eq {x y : O} (h : residue O x = residue O y) :
    x - y ∈ maximalIdeal O := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]

/-- Distinct residues means the difference is a unit. -/
theorem isUnit_sub_of_residue_ne {x y : O} (h : residue O x ≠ residue O y) : IsUnit (x - y) := by
  refine notMem_maximalIdeal.1 (fun hmem => h ?_)
  have hz := (IsLocalRing.residue_eq_zero_iff (x - y)).2 hmem
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end Bridges

namespace Menu

/-! ## 3. Level 1 is the residue field -/

section Level1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The level-1 residue reader: `Res O 1` is the residue field. -/
noncomputable def res1Equiv (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] : Res O 1 ≃+* IsLocalRing.ResidueField O :=
  Ideal.quotEquivOfEq (pow_one (maximalIdeal O))

theorem res1Equiv_mk (x : O) :
    res1Equiv O (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ 1) x) = IsLocalRing.residue O x :=
  Ideal.quotEquivOfEq_mk _ x

/-- The level-1 class with prescribed residue coefficient vector. -/
noncomputable def liftRes1 (v : Fin 3 → IsLocalRing.ResidueField O) : Coeff O 3 1 :=
  fun i => (res1Equiv O).symm (v i)

theorem liftRes1_injective : Function.Injective (liftRes1 (O := O)) := fun _ _ h =>
  funext fun i => (res1Equiv O).symm.injective (congrFun h i)

/-- The reduction vector of any lift of `liftRes1 v` is `v` itself. -/
theorem residue_comp_of_proj_liftRes1 {v : Fin 3 → IsLocalRing.ResidueField O} {b : Fin 3 → O}
    (hb : proj O 3 1 b = liftRes1 v) : (fun i => IsLocalRing.residue O (b i)) = v := by
  funext i
  have hi : (Ideal.Quotient.mk _ (b i) : Res O 1) = (res1Equiv O).symm (v i) := congrFun hb i
  have h := congrArg (res1Equiv O) hi
  rw [res1Equiv_mk, RingEquiv.apply_symm_apply] at h
  exact h

end Level1

/-! ## 4. The level-2 strata -/

section Level2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- The units of the level-`N` truncation: the complement of `dvdSet π 1 N`. -/
def unitSet (π : O) (N : ℕ) : Set (Res O N) := (dvdSet π 1 N)ᶜ

theorem card_dvdSet_two (hπ : Irreducible π) : Nat.card (dvdSet π 1 2) = residueCard O := by
  have h := card_dvdSet (π := π) hπ (k := 1) (r := 1)
  simpa using h

theorem card_exactSet_two (hπ : Irreducible π) :
    Nat.card (exactSet π 1 2) + 1 = residueCard O := by
  have h := card_exactSet_add (π := π) hπ (k := 1) (r := 0)
  simpa using h

theorem card_unitSet_two (hπ : Irreducible π) :
    Nat.card (unitSet π 2) + residueCard O = residueCard O ^ 2 := by
  classical
  have hsplit : Nat.card (dvdSet π 1 2) + Nat.card (unitSet π 2) = Nat.card (Res O 2) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : Res O 2 => x ∈ dvdSet π 1 2))
  rw [card_res] at hsplit
  rw [card_dvdSet_two hπ] at hsplit
  omega

/-- Reading a level-`N` stratum membership upstairs. -/
theorem dvd_of_mem_dvdSet (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) {a : O}
    (h : (Ideal.Quotient.mk _ a : Res O N) ∈ dvdSet π k N) : π ^ k ∣ a := by
  obtain ⟨y, hy⟩ := h
  rw [Ideal.Quotient.eq] at hy
  have h1 : (π : O) ^ N ∣ π ^ k * y - a := (mem_maximalIdeal_pow_iff_dvd hπ N _).1 hy
  have h2 : (π : O) ^ k ∣ π ^ k * y - a := dvd_trans (pow_dvd_pow π hk) h1
  have h3 : (π : O) ^ k ∣ π ^ k * y := Dvd.intro y rfl
  have h4 : (π : O) ^ k ∣ π ^ k * y - (π ^ k * y - a) := dvd_sub h3 h2
  simpa using h4

/-- The converse direction: a divisible lift lands in the stratum (no level constraint). -/
theorem mem_dvdSet_of_dvd {k N : ℕ} {a : O} (h : π ^ k ∣ a) :
    (Ideal.Quotient.mk _ a : Res O N) ∈ dvdSet π k N := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, by rw [hy]⟩

end Level2

end Menu

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.decidedDensity_ge_of_inj
#print axioms Uniformity.Density.sub_mem_of_residue_eq
#print axioms Uniformity.Density.isUnit_sub_of_residue_ne
#print axioms Uniformity.Density.Menu.res1Equiv
#print axioms Uniformity.Density.Menu.res1Equiv_mk
#print axioms Uniformity.Density.Menu.liftRes1
#print axioms Uniformity.Density.Menu.liftRes1_injective
#print axioms Uniformity.Density.Menu.residue_comp_of_proj_liftRes1
#print axioms Uniformity.Density.Menu.unitSet
#print axioms Uniformity.Density.Menu.card_dvdSet_two
#print axioms Uniformity.Density.Menu.card_exactSet_two
#print axioms Uniformity.Density.Menu.card_unitSet_two
#print axioms Uniformity.Density.Menu.dvd_of_mem_dvdSet
#print axioms Uniformity.Density.Menu.mem_dvdSet_of_dvd

end AxCheck
