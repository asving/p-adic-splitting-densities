/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H105
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapH.H124 — H.124a: `FullClusterRateBound` and the one-factor base

**Chapter H, NODE H.124** [def+theorem] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §4's terminal display
`inductionStep`, *"T-1's honest conditional Lean form — the reduction, never the theorem"*;
sources `EFF.GENIND.13` (`P(k)`), `EFF.GENIND.54` (Step 1), `EFF.GENIND.57` (the `(A2)`
assembly)).  **PART a of the mandated three-way split** (`H124` / `H124b` / `H124c`):

* the **def half** `FullClusterRateBound` — the carried, never-claimed full-cluster hypothesis;
* the **stratum label** `stratumPoly`, which turns H.100's strata into the fibres of a function
  (this is what makes the §17.3 assembly a `Finset` fibre sum rather than a `Set` induction);
* the **one-factor base** of the blueprint's Step 3: a stratum over an IRREDUCIBLE residue
  polynomial is DECIDED outright, so its undecided count is `0`; at degree `1` that empties the
  whole undecided set.

## ⚠ WHAT THIS NODE IS NOT (the H.98 fence, restated)

`FullClusterRateBound` is a HYPOTHESIS, not a theorem.  Nothing in this file, or in `H124b` /
`H124c`, claims `THEOREM GENIND.B`: the full-cluster rate is carried as an explicit argument of
`inductionPackage_of_clusterRates` (H.124c) and is discharged only on the `m ≤ 3, d = 1` layer
that H.106–H.123 supply — beyond that it is gated by `HYP.36` / `HYP.81` / `HYP.82` (`d = 1`,
`m ≥ 4`) and by `B-BOX-1` (`d ≥ 2`).  These are the section's recorded CONDITIONALITY EDGES
`BP.H.124 → HYP.36 / HYP.81 / HYP.82`.

## The one-factor base, in words

A level-`N` class `c` in the stratum of `g` has *every* monic degree-`n` lift reducing to `g`
(that is H.100's definition).  If `g` is irreducible, CN-21
(`typeOf_inert_of_irreducible_map`) reads the type of every such lift off the residue
factorization: a single unramified factor, `⟨{(1, n)}⟩`.  Since this holds for EVERY lift, `c` is
`⟨{(1, n)}⟩`-DECIDED, hence not undecided.  At `n = 1` every monic residue polynomial has degree
`1` and is therefore irreducible, so `undecidedSet O 1 N = ∅` — the base case the H.124c peel
needs at the left end (`ih` starts at `k = 2`, and a coprime split of a degree-`n` residue
polynomial can perfectly well produce a degree-`1` factor).

## TEETH

Battery `P2(iii)` (per-stratum aggregation against independent child tables, bridge-b certified)
and `P2(vii)` (both-characteristics census equality) — GC-8 disposition **Lean theorem** at
H.124c, where the aggregation is performed; this part carries the two ingredients it consumes.
The one-factor base additionally re-reads `P2(i)`'s `m = 1` cells, whose undecided column is
identically `0`.

DEPENDS: H.100 (`levelZeroStratum`, `mem_levelZeroStratum_iff`, `proj_surjective'`) · H.105 (the
import chain: H.101–H.104) · landed `typeOf_inert_of_irreducible_map` (CN-21), `undecidedSet`,
`undecidedCount`, `undecidedSeq`, `monicPoly`, `exists_monicPoly_eq` (CN-01).

## Status

Sorry-free, axiom-free (Lean core only); footprints printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. The def half — the carried full-cluster hypothesis -/

/-- **H.124 (def half).** The full-cluster rate hypothesis at degree `n`: constants `(K, B, c)`
chosen ONCE (outside `∀ O`), bounding the SEMANTIC per-stratum undecided count of every
full-cluster stratum (`m ≥ 2`, `m·d = n`, centre an irreducible monic `p` of degree `d`) relative
to the stratum total, at every window `M ≥ 1`. -/
def FullClusterRateBound (n : ℕ) (K : ℝ) (B c : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ (p : Polynomial (IsLocalRing.ResidueField O)) (m d : ℕ), 2 ≤ m → m * d = n →
      p.Monic → Irreducible p → p.natDegree = d →
      ∀ M, 1 ≤ M →
        (Nat.card ((undecidedSet O n M ∩ Induction.levelZeroStratum O n M (p ^ m) :
            Set (Coeff O n M))) : ℝ)
          ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹
            * (Nat.card (Induction.levelZeroStratum O n M (p ^ m)) : ℝ)

namespace Induction

/-! ## 2. The stratum label — H.100's strata as the fibres of a function -/

/-- **The stratum label.** The residue polynomial of a level-`N` class, read off one (chosen)
monic lift.  At `1 ≤ N` the reading is class-determined (H.100), so `stratumPoly` is the label
whose fibres are exactly the level-0 strata. -/
noncomputable def stratumPoly (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n N : ℕ) (c : Coeff O n N) : Polynomial (ResidueField O) :=
  (monicPoly (Classical.choose (proj_surjective' O n N c))).map (residue O)

/-- A class in the stratum of `g` is labelled by `g` — no hypothesis on `N` needed: membership
in `levelZeroStratum` is the ∀-lift clause, and `stratumPoly` reads one particular lift. -/
theorem stratumPoly_eq_of_mem {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} {g : Polynomial (ResidueField O)} {c : Coeff O n N}
    (hc : c ∈ levelZeroStratum O n N g) : stratumPoly O n N c = g :=
  hc _ (Classical.choose_spec (proj_surjective' O n N c))

/-- Every class lies in the stratum of its own label (this is where `1 ≤ N` is spent). -/
theorem mem_levelZeroStratum_stratumPoly {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} (hN : 1 ≤ N) (c : Coeff O n N) :
    c ∈ levelZeroStratum O n N (stratumPoly O n N c) :=
  (mem_levelZeroStratum_iff hN _ c).2
    ⟨Classical.choose (proj_surjective' O n N c),
      Classical.choose_spec (proj_surjective' O n N c), rfl⟩

/-- **The fibre reading.** At `1 ≤ N` the stratum of `g` IS the `g`-fibre of the label. -/
theorem mem_levelZeroStratum_iff_stratumPoly {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} (hN : 1 ≤ N) (g : Polynomial (ResidueField O))
    (c : Coeff O n N) : c ∈ levelZeroStratum O n N g ↔ stratumPoly O n N c = g := by
  refine ⟨stratumPoly_eq_of_mem, fun h => ?_⟩
  rw [← h]
  exact mem_levelZeroStratum_stratumPoly hN c

/-- The label is monic. -/
theorem stratumPoly_monic {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (c : Coeff O n N) : (stratumPoly O n N c).Monic :=
  (monicPoly_monic _).map _

/-- The label has the ambient degree. -/
theorem stratumPoly_natDegree {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (c : Coeff O n N) : (stratumPoly O n N c).natDegree = n := by
  rw [stratumPoly, (monicPoly_monic _).natDegree_map, monicPoly_natDegree]

/-- **The label is onto the monic degree-`n` polynomials.** Every monic residue polynomial of
degree `n` labels some class: lift its coefficients through the (surjective) residue map. -/
theorem exists_stratumPoly_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (hN : 1 ≤ N) {g : Polynomial (ResidueField O)} (hg : g.Monic)
    (hd : g.natDegree = n) : ∃ c : Coeff O n N, stratumPoly O n N c = g := by
  obtain ⟨b, hb⟩ := exists_monicPoly_eq hg hd
  choose a ha using fun i : Fin n => IsLocalRing.residue_surjective (R := O) (b i)
  refine ⟨proj O n N a, stratumPoly_eq_of_mem ((mem_levelZeroStratum_iff hN _ _).2 ⟨a, rfl, ?_⟩)⟩
  rw [map_monicPoly]
  simp only [ha]
  exact hb

/-! ## 3. The one-factor base — an irreducible stratum is decided -/

/-- **The one-factor base (`m = 1`), class form.** Over an IRREDUCIBLE residue polynomial every
class of the stratum is `⟨{(1, n)}⟩`-DECIDED: CN-21 reads the inert type off *every* monic lift,
and the ∀-lift clause of `levelZeroStratum` supplies the hypothesis at every lift at once. -/
theorem decidedAt_of_mem_levelZeroStratum_irreducible {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {n N : ℕ} (hn : 0 < n) {g : Polynomial (ResidueField O)} (hg : Irreducible g)
    {c : Coeff O n N} (hc : c ∈ levelZeroStratum O n N g) :
    DecidedAt O n ⟨{(1, n)}⟩ N c := by
  intro a ha
  have hmap : (monicPoly a).map (residue O) = g := hc a ha
  have hdeg : 0 < (monicPoly a).natDegree := by rw [monicPoly_natDegree]; exact hn
  have := typeOf_inert_of_irreducible_map (monicPoly_monic a) hdeg (by rw [hmap]; exact hg)
  rw [this, monicPoly_natDegree]

/-- The one-factor base, undecided form: the undecided part of an irreducible stratum is empty. -/
theorem undecided_inter_levelZeroStratum_irreducible {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {n N : ℕ} (hn : 0 < n) {g : Polynomial (ResidueField O)} (hg : Irreducible g) :
    (undecidedSet O n N ∩ levelZeroStratum O n N g : Set (Coeff O n N)) = ∅ := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hcU hcS
  exact hcU _ (decidedAt_of_mem_levelZeroStratum_irreducible hn hg hcS)

/-! ## 4. Degree one — the left end of the peel -/

/-- At degree `1` every stratum label is a monic polynomial of degree `1`, hence irreducible. -/
theorem irreducible_stratumPoly_one {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {N : ℕ} (c : Coeff O 1 N) :
    Irreducible (stratumPoly O 1 N c) := by
  refine irreducible_of_degree_eq_one ?_
  have hne : stratumPoly O 1 N c ≠ 0 := (stratumPoly_monic c).ne_zero
  exact (degree_eq_iff_natDegree_eq hne).2 (stratumPoly_natDegree c)

/-- **Degree one is fully decided.** Every level-`N` class of degree `1` is decided, so the
degree-`1` undecided set is empty. -/
theorem undecidedSet_one_eq_empty {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {N : ℕ} (hN : 1 ≤ N) : undecidedSet O 1 N = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  have hmem := mem_levelZeroStratum_stratumPoly hN c
  have hempty := undecided_inter_levelZeroStratum_irreducible (O := O) (N := N) Nat.one_pos
    (irreducible_stratumPoly_one c)
  exact absurd (show c ∈ (∅ : Set (Coeff O 1 N)) from hempty ▸ ⟨hc, hmem⟩) (by simp)

/-- The degree-`1` undecided census is `0`. -/
theorem undecidedCount_one_eq_zero {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {N : ℕ} (hN : 1 ≤ N) : undecidedCount O 1 N = 0 := by
  rw [undecidedCount, undecidedSet_one_eq_empty hN]
  simp

/-- The degree-`1` undecided proportion is `0` — the peel's left-end base case. -/
theorem undecidedSeq_one_eq_zero {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {N : ℕ} (hN : 1 ≤ N) : undecidedSeq O 1 N = 0 := by
  rw [undecidedSeq, undecidedCount_one_eq_zero hN]
  simp

end Induction

end Uniformity.Density

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.FullClusterRateBound
#print axioms Uniformity.Density.Induction.stratumPoly
#print axioms Uniformity.Density.Induction.mem_levelZeroStratum_iff_stratumPoly
#print axioms Uniformity.Density.Induction.exists_stratumPoly_eq
#print axioms Uniformity.Density.Induction.decidedAt_of_mem_levelZeroStratum_irreducible
#print axioms Uniformity.Density.Induction.undecided_inter_levelZeroStratum_irreducible
#print axioms Uniformity.Density.Induction.undecidedSet_one_eq_empty
#print axioms Uniformity.Density.Induction.undecidedCount_one_eq_zero
#print axioms Uniformity.Density.Induction.undecidedSeq_one_eq_zero

end AxCheck
