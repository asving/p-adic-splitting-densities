/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B66
import Uniformity.ChapB.B74
import Uniformity.ChapB.B77b

/-!
# Uniformity.ChapB.B66c — `order1Type` is a function of the level-`N` window class

**BOOKED HELPER, B.66-adjacent** (blueprint `CHAP-B_leaf_layer.md` amendment **A-F.12**, node
B.79 PROOF step 5 / §12 rule 2's supplier block). This file holds ONE declaration,
`order1Type_congr`: B.66's order-1 datum `order1Type π φ g` depends on a `Visible`-at-`N`
polynomial `g` only through its level-`N` congruence class.

`order1Type` (B.66, `B66.lean:108`) is the `Multiset.bind` of the pair
`(slope denominator, φ.natDegree * ψ.natDegree)` over B.66a's two canonical index finsets
(`slopeFinset`, `resFactorFinset`). The claim proved here is that **both index finsets are
literally equal** at `g` and at any monic `g'` of the same degree with `π ^ N ∣ (g - g').coeff i`
for every `i` — not merely in bijection — so the bound multisets agree term by term.

## Why this file exists (and why it is NOT B.79b)

B.79 half (b) (`typeOf_congr_of_certificate`) is the level-`N` block certificate; this is its one
non-mechanical leg, and it is the leg with no `hperim` in it. The wave-16 B.79b unit proved the
node's then-frozen signature unprovable — its perimeter hypothesis `hperim` was quantified over
the divisors of the representative `g` (`gS ∣ g`) while the proof applies B.79 half (a) to the
lift `g'`, whose divisor lattice the signature did not relate to `g`'s; B.73–B.77 transport
`suppVal`, `sideSet`, `sideMin`/`sideMax`/`sideDeg`, `IsPure`, `resPoly`, `Visible` and
`NeedsDescent`, and none of them mentions `∣`, `monicFactors` or `inertiaDegOf`. Amendment
**A-F.12** (2026-08-16) re-signed B.79b's `hperim` at `g'` (and B.80/B.81/B.82's at the window
class) and banked this leg here, where it belongs: it is a statement about `order1Type` alone.

**This file is not a node file and it does not contain `typeOf_congr_of_certificate`.** The
B.79b unit that lands that node consumes `order1Type_congr` by name (§0.2's private-copy ban).

## The three legs of the proof

1. **`slopeFinset` agrees.** B.77a's `sideSet_congr` makes the defining condition of B.66a's
   `mem_slopeFinset` literally the same at `g` and at `g'` (the two degree pins come from `hres`
   through landed `Uniformity.Hensel.natDegree_eq_of_map_eq`, and `hdeg` carries the second).
2. **`resFactorFinset` agrees at every slope.** B.66a's `mem_resFactorFinset` reads "monic
   irreducible dividing the residual polynomial at the `sideMin` pin". The pinned abscissa agrees
   (`sideSet_congr` plus proof-irrelevance of `Finset.min'`), the pinned **height** agrees (B.76(i)
   `npHgt_min_congr` together with the window guard, which puts both heights strictly below `N`),
   and then B.77b's `resPoly_congr` makes the residual polynomials themselves equal.
3. **The `Multiset.bind` is congruent term by term** (`Multiset.bind_congr`).

**The window guard is consumed by name, not re-derived** — B.74's `H₀_lt_of_visible`
(`B74.lean:349`), whose conclusion `H₀ < N` at the `sideMin` pin is exactly `resPoly_congr`'s
`hH₀`. That is amendment A-F.11 (VI)'s action item as executed: the item names the inner
`suppVal_lt_of_vis`, but `H₀_lt_of_visible` is the finished guard, so consuming it also spares
this file the HE-T-CAP chain. One visibility hypothesis at abscissa `0` guards the whole side
family — the content the `HE-T-CAP` tooth (`EFF.HE3.54`) tests.

DEPENDS: B.66 (`order1Type`, `order1Type_data`) · B.66a (`mem_slopeFinset`,
`mem_resFactorFinset`, `mem_slopeFinset_imp`) · B.74 (`H₀_lt_of_visible`) · B.76(i)
(`npHgt_min_congr`), B.76(iv) (`visible_congr`) · B.77a (`sideSet_congr`) · B.77b
(`resPoly_congr`) · B.39b (`sideSet_nonempty_gen`) · landed
`Uniformity.Hensel.natDegree_eq_of_map_eq`, `Uniformity.FactorizationType.ext` · mathlib
`Multiset.bind_congr`, `min_choice`.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound`** — and, unlike the retired
`B79bTransport.lean` that first banked this proof, the B.42 literature cite is not even on the
import path (this file does not import B.63/B.42).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
/-- **B.79 half (b), the transport leg** (booked as a B.66-adjacent helper at A-F.12). B.66's
order-1 datum is a function of the level-`N` congruence class of a `Visible`-at-`N` polynomial:
both canonical index finsets are literally equal at `g` and at `g'`, so the data are. -/
theorem order1Type_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ}
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    {N : ℕ} (hvis : Visible π φ g N)
    {g' : Polynomial O} (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hgg' : ∀ i, π ^ N ∣ (g - g').coeff i) :
    order1Type π φ g' = order1Type π φ g := by
  classical
  have hdegμ : g.natDegree = μ * φ.natDegree := by
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq hg hres, Polynomial.natDegree_pow,
      hφ.monic.natDegree_map]
  have hdegμ' : g'.natDegree = μ * φ.natDegree := by rw [hdeg]; exact hdegμ
  have hvis' : Visible π φ g' N := (visible_congr hπ hφ.monic hφ.pos hgg').1 hvis
  have hgg'' : ∀ i, π ^ N ∣ (g' - g).coeff i := by
    intro i
    have hi := hgg' i
    rw [Polynomial.coeff_sub] at hi ⊢
    exact (dvd_sub_comm).1 hi
  have hsideSet : ∀ u ℓ : ℕ, sideSet φ g' u ℓ = sideSet φ g u ℓ :=
    sideSet_congr hπ hφ.monic hφ.pos hgg' hdeg hvis
  -- ## 1. the slope index agrees
  have hslope : slopeFinset π φ g' = slopeFinset π φ g := by
    ext p
    rw [mem_slopeFinset hφ hg' hdegμ', mem_slopeFinset hφ hg hdegμ, hsideSet]
  -- ## 2. the residual index agrees at every slope
  have hresF : ∀ p ∈ slopeFinset π φ g,
      resFactorFinset π φ g' p = resFactorFinset π φ g p := by
    intro p hp
    obtain ⟨hℓ, hcop, -⟩ := mem_slopeFinset_imp hp
    have hne : (sideSet φ g p.1 p.2).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hne' : (sideSet φ g' p.1 p.2).Nonempty := by rw [hsideSet]; exact hne
    have hmin : sideMin φ g' p.1 p.2 hne' = sideMin φ g p.1 p.2 hne := by
      simp only [sideMin]; congr 1; exact hsideSet p.1 p.2
    -- the pinned heights agree: both sit strictly inside the window, where B.76(i) is exact
    have hpin : ∀ H₀ : ℕ, npHgt φ g (sideMin φ g p.1 p.2 hne) = (H₀ : ℕ∞) →
        npHgt φ g' (sideMin φ g' p.1 p.2 hne') = (H₀ : ℕ∞) := by
      intro H₀ hH₀
      have hlt : (H₀ : ℕ∞) < (N : ℕ∞) := by
        exact_mod_cast H₀_lt_of_visible hπ hvis hℓ hne hH₀
      have hmc := npHgt_min_congr hπ hφ.monic hφ.pos hgg' (sideMin φ g p.1 p.2 hne)
      rw [hH₀, min_eq_left hlt.le] at hmc
      rw [hmin]
      rcases min_choice (npHgt φ g' (sideMin φ g p.1 p.2 hne)) (N : ℕ∞) with hc | hc
      · rw [hc] at hmc; exact hmc.symm
      · rw [hc] at hmc; exact absurd hmc (ne_of_lt hlt)
    have hpin' : ∀ H₀ : ℕ, npHgt φ g' (sideMin φ g' p.1 p.2 hne') = (H₀ : ℕ∞) →
        npHgt φ g (sideMin φ g p.1 p.2 hne) = (H₀ : ℕ∞) := by
      intro H₀ hH₀
      have hlt : (H₀ : ℕ∞) < (N : ℕ∞) := by
        exact_mod_cast H₀_lt_of_visible hπ hvis' hℓ hne' hH₀
      have hmc := npHgt_min_congr hπ hφ.monic hφ.pos hgg'' (sideMin φ g' p.1 p.2 hne')
      rw [hH₀, min_eq_left hlt.le] at hmc
      rw [← hmin]
      rcases min_choice (npHgt φ g (sideMin φ g' p.1 p.2 hne')) (N : ℕ∞) with hc | hc
      · rw [hc] at hmc; exact hmc.symm
      · rw [hc] at hmc; exact absurd hmc (ne_of_lt hlt)
    ext ψ
    rw [mem_resFactorFinset hπ hφ hg' hdegμ' hℓ hcop, mem_resFactorFinset hπ hφ hg hdegμ hℓ hcop]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · intro hd _ H₀ hH₀
      have hrp := resPoly_congr hπ hφ.monic hφ.pos hgg' hdeg hvis hne (H₀ := H₀)
        (H₀_lt_of_visible hπ hvis hℓ hne hH₀)
      have hdd := hd hne' H₀ (hpin H₀ hH₀)
      rw [hrp] at hdd
      exact hdd
    · intro hd _ H₀ hH₀
      have hrp := resPoly_congr hπ hφ.monic hφ.pos hgg'' hdeg.symm hvis' hne' (H₀ := H₀)
        (H₀_lt_of_visible hπ hvis' hℓ hne' hH₀)
      have hdd := hd hne H₀ (hpin' H₀ hH₀)
      rw [hrp] at hdd
      exact hdd
  -- ## 3. the `Multiset.bind` is congruent term by term
  refine FactorizationType.ext ?_
  rw [order1Type_data, order1Type_data, hslope]
  exact Multiset.bind_congr fun p hp => by rw [hresF p hp]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.order1Type_congr
end AxCheck
