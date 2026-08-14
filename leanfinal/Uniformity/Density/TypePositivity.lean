/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.TypePositivity — every `(e, f)` pair of a type is positive

**CN-04** of `spec/CERTAIN_NODES_2026-08-14.md`.

`typeOf f` is the multiset of `(e, f)` pairs of the monic irreducible factors of a monic `f`
(`Density/TypeOf.lean`). This file records the two elementary constraints its members satisfy:

* `efPair_pos_of_mem` (**the contract**) — `0 < e` and `0 < f` for every member pair;
* `efPair_mul_le_natDegree` (helper) — `e * f ≤ deg f`, free from the landed `typeOf_degree`.

Together with `typeOf_degree` (`∑ eᵢ fᵢ = deg f`) these turn "degree `n`" into a *finite*
constraint on a `FactorizationType`: without positivity, degree-`n` types would include junk
like `⟨{(1,1),(1,1),(0,7)}⟩` and no enumeration would be possible. This is what CN-22
(`exists_coveringMenu`) consumes.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

section Positivity

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The monic irreducible factors of a monic polynomial have positive degree. (The argument is
the one inlined in the proof of `typeOf_degree`; it is named here because both lemmas of this
file need it.) -/
theorem natDegree_pos_of_mem_monicFactors {f : Polynomial O} (hf : f.Monic)
    {g : Polynomial O} (hg : g ∈ monicFactors f) : 0 < g.natDegree := by
  obtain ⟨hgm, hgi⟩ := (monicFactors_spec hf).1 g hg
  rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
  · exact absurd ((Polynomial.Monic.natDegree_eq_zero hgm).1 h0 ▸ isUnit_one) hgi.not_isUnit
  · exact h0

/-- **CN-04 — every `(e, f)` pair occurring in a splitting type is positive.**

A member of `(typeOf f).data` is `efPair g` for a monic *irreducible* factor `g` of `f`. Such a
`g` has positive degree, so `normValues g` is nonempty and its gcd `inertiaDegOf g` is positive;
and `ramIndexOf g = deg g / inertiaDegOf g` is positive because `inertiaDegOf g ∣ deg g` and
`deg g > 0`. -/
theorem efPair_pos_of_mem {f : Polynomial O} (hf : f.Monic) {p : ℕ × ℕ}
    (hp : p ∈ (typeOf f).data) : 0 < p.1 ∧ 0 < p.2 := by
  rw [typeOf_data, Multiset.mem_map] at hp
  obtain ⟨g, hg, rfl⟩ := hp
  have hgm : g.Monic := ((monicFactors_spec hf).1 g hg).1
  have hpos : 0 < g.natDegree := natDegree_pos_of_mem_monicFactors hf hg
  have hfpos : 0 < inertiaDegOf g := inertiaDegOf_pos (normValues_nonempty hgm hpos)
  refine ⟨?_, hfpos⟩
  show 0 < ramIndexOf g
  exact Nat.div_pos (Nat.le_of_dvd hpos (inertiaDegOf_dvd_natDegree hgm hpos)) hfpos

/-- **Helper (CN-04's companion): `e * f ≤ deg f` for every member pair.** Each `eᵢ fᵢ` is one
summand of `∑ eᵢ fᵢ = (typeOf f).degree = deg f` (`typeOf_degree`), and all summands are
natural numbers. -/
theorem efPair_mul_le_natDegree {f : Polynomial O} (hf : f.Monic) {p : ℕ × ℕ}
    (hp : p ∈ (typeOf f).data) : p.1 * p.2 ≤ f.natDegree := by
  have hmem : p.1 * p.2 ∈ (typeOf f).data.map (fun q : ℕ × ℕ => q.1 * q.2) :=
    Multiset.mem_map_of_mem _ hp
  have hle : p.1 * p.2 ≤ ((typeOf f).data.map (fun q : ℕ × ℕ => q.1 * q.2)).sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  rwa [← FactorizationType.degree, typeOf_degree hf] at hle

end Positivity

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.efPair_pos_of_mem
#print axioms Uniformity.Density.efPair_mul_le_natDegree

end AxCheck

end Uniformity.Density
