/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H100 — `levelZeroStratum`, the level-0 stratum

**Chapter H, NODE H.100** (`blueprint/CHAP-H_general_induction.md` §17.1, the dated extension of
2026-08-16, unit T-1 / provenance OM-2). The first node of **N-1, the level-0 class transport**.

For a monic residue polynomial `g` over `ResidueField O`, `levelZeroStratum O n N g` is the set of
level-`N` coefficient classes **all** of whose monic lifts reduce to `g` (the ∀-lift form — the
conservative reading, chosen so that membership is a property of the CLASS and not of a chosen
lift). The lemma half says the caution is free at `1 ≤ N`: two lifts of one class differ
coefficientwise by elements of `𝔪 ^ N ⊆ 𝔪`, so the reduction is class-determined and the ∀-lift
and ∃-lift readings agree:

* `mem_levelZeroStratum_iff : 1 ≤ N → (c ∈ levelZeroStratum O n N g ↔ ∃ a, proj O n N a = c ∧
  (monicPoly a).map (residue O) = g)`.

DEPENDS: landed `Uniformity.Density.Coeff`, `proj`, `monicPoly`, `residue`
(`Density/LocalData.lean`). No chapter-H node.

**ENVIRONMENT — ENV-H17** (blueprint §17.0): the standard telescope with **every binder written
INLINE** (the B.42 completeness-binder rule; §17 declares no section variables at all), and
minimally bound per node: **no `Finite (ResidueField O)`, no `IsAdicComplete`** here. Counting and
Hensel enter at H.102/H.105, not at the stratum object.

## Two auxiliaries, both declared rather than smuggled

1. `proj_surjective'` — the landed `Uniformity.Density.proj_surjective` carries
   `[Finite (ResidueField O)]` (a section variable of `Density/LocalData.lean`'s `section Box`,
   auto-included). ENV-H17 forbids that instance at this node, and the proof never needed it:
   `Ideal.Quotient.mk_surjective` is unconditional. `proj_surjective'` is that statement verbatim
   with the spurious instance dropped; its proof is the landed one, three lines.
2. `map_monicPoly` — `(monicPoly a).map φ = monicPoly (φ ∘ a)`, the coefficientwise
   `Polynomial.map` display of `monicPoly`. **Non-blueprint auxiliary**, declared public here
   because H.101 needs the same fact over `Res O N`; it generalizes (dropping both `IsDomain`
   hypotheses, which nothing in the proof uses) the two private copies already in the corpus,
   `g61b_map_monicPoly` (`ChapG/G61b.lean:66`) and `g61c_map_monicPoly` (`ChapG/G61c.lean:55`),
   whose proof is reused verbatim.

SOURCE: OM-2 §4 sketch N1.1 + §3.1 N-1a's stratum object; `EFF.GENIND.54` (the level-0
configuration decomposition: the degree-`n` problem is the disjoint union over level-0
configurations of products of cluster systems and simple branches).

**TEETH** (`verification/openmath/OM2_genindb_battery.py`, RESULTS run 2026-08-16, 612/612):
`P2 total classes` (`total == q ^ (n * N)`) and `P2(i,ii) stratum counts` (per residue
configuration, `cnt == ∏ q ^ (deg p̄ · mlt · (N − 1))`), exhaustive over 12 cells × 2 rings. GC-8
disposition — **Lean theorems** for the structural half (the two `example`s of §3 below: the
strata are pairwise disjoint, and at `1 ≤ N` they cover the box, i.e. they PARTITION `Coeff O n N`,
which is what makes `total` the sum of the stratum counts); **executable regression retained** for
the counting half (the per-stratum value `q ^ (n (N − 1))` is H.102's corollary, not this node's),
with the battery's twelve cell predictions reproduced as kernel `#guard`s in §4.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`). The B.42
axiom does not enter §17 before H.123.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The two auxiliaries -/

/-- **The `Finite`-free surjectivity of `proj`.** Statement of the landed
`Uniformity.Density.proj_surjective` with its auto-included `[Finite (ResidueField O)]` dropped —
ENV-H17 declares no `Finite`, and `Ideal.Quotient.mk_surjective` needs none. -/
theorem proj_surjective' (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n N : ℕ) : Function.Surjective (proj O n N) := by
  intro c
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (c i)
  exact ⟨a, funext ha⟩

/-- **`monicPoly` is a `Polynomial.map`-stable display.** Non-blueprint auxiliary (see the module
docstring): the corpus's `g61b_map_monicPoly`/`g61c_map_monicPoly` with both `IsDomain`
hypotheses dropped, so that it also applies over the truncation ring `Res O N` (H.101). -/
theorem map_monicPoly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (a : Fin n → R) : (monicPoly a).map φ = monicPoly (fun i => φ (a i)) := by
  simp only [monicPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

/-! ## 2. The node -/

/-- **H.100 (def half). The level-0 stratum.** The level-`N` classes ALL of whose monic lifts
reduce to the monic residue polynomial `g` (∀-lift form; the ∃-lift transport is the lemma
half). -/
def levelZeroStratum (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n N : ℕ) (g : Polynomial (ResidueField O)) : Set (Coeff O n N) :=
  {c | ∀ a : Fin n → O, proj O n N a = c → (monicPoly a).map (residue O) = g}

/-- The class-determinacy behind the lemma half: at `1 ≤ N`, two lifts of one level-`N` class have
the same residues, because they differ by elements of `𝔪 ^ N ⊆ 𝔪`. -/
theorem residue_eq_of_proj_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (hN : 1 ≤ N) {a b : Fin n → O} (h : proj O n N a = proj O n N b) (i : Fin n) :
    residue O (a i) = residue O (b i) := by
  have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a i)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (b i) := congrFun h i
  have h2 : a i - b i ∈ (maximalIdeal O) ^ N := Ideal.Quotient.eq.1 h1
  have h3 : a i - b i ∈ maximalIdeal O := Ideal.pow_le_self (by omega) h2
  exact Ideal.Quotient.eq.2 h3

/-- **H.100 (lemma half).** At `1 ≤ N` the reduction is class-determined, so the ∀-lift and
∃-lift readings of the stratum agree. -/
theorem mem_levelZeroStratum_iff {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} (hN : 1 ≤ N)
    (g : Polynomial (ResidueField O)) (c : Coeff O n N) :
    c ∈ levelZeroStratum O n N g ↔
      ∃ a : Fin n → O, proj O n N a = c ∧ (monicPoly a).map (residue O) = g := by
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective' O n N c
    exact ⟨a, ha, hc a ha⟩
  · rintro ⟨a, ha, hg⟩ b hb
    have h : proj O n N b = proj O n N a := by rw [hb, ha]
    have hcoef : ∀ i : Fin n, residue O (b i) = residue O (a i) :=
      residue_eq_of_proj_eq hN h
    calc (monicPoly b).map (residue O)
        = monicPoly (fun i => residue O (b i)) := map_monicPoly _ b
      _ = monicPoly (fun i => residue O (a i)) := by simp only [hcoef]
      _ = (monicPoly a).map (residue O) := (map_monicPoly _ a).symm
      _ = g := hg

end Uniformity.Density.Induction

/-! ## 3. TEETH, Lean half — the strata PARTITION the coefficient box

Battery `P2 total classes` asserts `total == q ^ (n * N)` after summing the per-configuration
stratum counts; the summation is legitimate exactly because the strata are pairwise disjoint and
cover the box. Both halves are cheap here, and neither is a new API surface, so both are recorded
as `example`s. (The per-stratum VALUE `q ^ (n (N − 1))` is H.102's count corollary — not claimed
at this node.) -/

section Teeth

open Uniformity.Density Uniformity.Density.Induction IsLocalRing Polynomial

/-- TEETH (a) — pairwise disjointness, unconditional in `N`: a class determines its stratum. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n N : ℕ}
    {g g' : Polynomial (ResidueField O)} {c : Coeff O n N}
    (h : c ∈ levelZeroStratum O n N g) (h' : c ∈ levelZeroStratum O n N g') : g = g' := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  exact (h a ha).symm.trans (h' a ha)

/-- TEETH (b) — covering, at `1 ≤ N`: every class lies in a (then unique, by (a)) stratum. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n N : ℕ}
    (hN : 1 ≤ N) (c : Coeff O n N) :
    ∃ g : Polynomial (ResidueField O), c ∈ levelZeroStratum O n N g := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  exact ⟨(monicPoly a).map (residue O), (mem_levelZeroStratum_iff hN _ c).2 ⟨a, ha, rfl⟩⟩

end Teeth

/-! ## 4. TEETH, numeric half — the battery's twelve cells

`OM2_genindb_battery.py` PART 2 runs the plan `[(n,q,Ns)] = [(2,2,[1,2,3]), (2,3,[1,2,3]),
(3,2,[2,3]), (3,3,[2]), (4,2,[2,3]), (4,3,[2])]` — 12 cells, each over both rings (`Zq`, `Fqt`) —
and checks `P2 total classes` (`total == q ^ (n * N)`) together with `P2(i,ii) stratum counts`
(`cnt == ∏ q ^ (deg p̄ · mlt · (N − 1))`, whose exponents sum to `n · (N − 1)` because
`∑ deg p̄ · mlt = n`). The two predictions are consistent iff the `q ^ n` monic residue
polynomials of degree `n` carry `q ^ (n (N − 1))` classes apiece; that arithmetic identity is what
the kernel checks below, cell by cell. It is a consistency check on the battery's predictions, NOT
a re-execution of its exhaustive enumeration (which stays the executable regression, GC-8). -/

section NumericGate

/-- `q ^ n` strata × `q ^ (n (N − 1))` classes each `= q ^ (n N)`, at each battery cell. -/
private def cellCensus (q n N : ℕ) : Prop := q ^ n * q ^ (n * (N - 1)) = q ^ (n * N)

instance (q n N : ℕ) : Decidable (cellCensus q n N) := by
  unfold cellCensus; infer_instance

-- n = 2, q = 2, N ∈ {1, 2, 3}
#guard cellCensus 2 2 1
#guard cellCensus 2 2 2
#guard cellCensus 2 2 3
-- n = 2, q = 3, N ∈ {1, 2, 3}
#guard cellCensus 3 2 1
#guard cellCensus 3 2 2
#guard cellCensus 3 2 3
-- n = 3, q = 2, N ∈ {2, 3}
#guard cellCensus 2 3 2
#guard cellCensus 2 3 3
-- n = 3, q = 3, N = 2
#guard cellCensus 3 3 2
-- n = 4, q = 2, N ∈ {2, 3}
#guard cellCensus 2 4 2
#guard cellCensus 2 4 3
-- n = 4, q = 3, N = 2
#guard cellCensus 3 4 2

end NumericGate

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.levelZeroStratum
#print axioms Uniformity.Density.Induction.mem_levelZeroStratum_iff
#print axioms Uniformity.Density.Induction.residue_eq_of_proj_eq
#print axioms Uniformity.Density.Induction.proj_surjective'
#print axioms Uniformity.Density.Induction.map_monicPoly

end AxCheck
