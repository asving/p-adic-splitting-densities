/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B46
import Uniformity.ChapB.B63a
import Uniformity.ChapB.B78
import Uniformity.ChapB.B79b
import Uniformity.Density.DensityAPI
import Uniformity.MultiHensel

/-!
# Uniformity.ChapB.B80 — the full level-`N` decidedness certificate

**Chapter B, NODE B.80** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C. One signed
declaration.

*The statement.* Over the complete bundle, let `a : Fin n → O` with `0 < n` and write
`f := monicPoly a`. Given order-0 data — order-1 keys `φ i` (`i ∈ s`) with pairwise distinct
reductions, exponents `e i ≥ 1` — together with a peel of the representative (monic `g i` with
`f = ∏_{i ∈ s} g i` and `(g i)‾ = (φ‾ i) ^ (e i)`), and, **per block**, R8-1's two clauses plus
the perimeter (`Visible π (φ i) (g i) N`, `¬ NeedsDescent π (φ i) (g i)`, `hperim i`):

```
DecidedAt O n ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ N (proj O n N a)
```

— every member of the level-`N` class of `a` has the type read off the representative's blocks.

## `hperim` is the window-class closure — the A-F.12 re-sign, and why

This node fires B.79(b) per block at the **lift's peel** `g' i`, which step 3 manufactures by
Hensel and no signature can name. B.79(b)'s own `hperim` was re-signed at A-F.12 to sit at the
lift (`gS ∣ g'`), so what this node must hand it is the perimeter of the divisors of `g' i` — a
polynomial that exists only inside the proof. The clause is therefore closed over the level-`N`
window class of the block (§12 item 4's display (4a″)):

```
∀ gT, gT.Monic → gT.natDegree = (g i).natDegree → (∀ k, π ^ N ∣ ((g i) - gT).coeff k) → …
```

and the three closure guards are exactly what steps 3–4 already deliver: `(g' i).Monic` from the
Hensel lift, the degree pin by `natDegree_eq_of_map_eq` on both sides of `hgres`, and the
congruence by B.78(iii) `peel_congr`. Reflexivity (`gT := g i`, `π ^ N ∣ 0`) makes the closure
imply the frozen per-block clause, so no consumer loses anything it had.

## Proof — the blueprint's six legs

1. `s.Nonempty` (`s = ∅` forces `monicPoly a = 1`, against `0 < n` and `monicPoly_natDegree`),
   hence `0 < N` from any `hvis i` (`Visible` at `N = 0` is `∃ i, ¬ 1 ∣ …`).
2. Enter through landed `decidedAt_of_congr`: fix `b` with `π ^ N ∣ (b i - a i)`; B.78(i)
   `monicPoly_congr` gives `π ^ N ∣ (monicPoly a - monicPoly b).coeff j`, hence equal reductions.
3. Peel `monicPoly b`: the residual blocks `(φ‾ i) ^ (e i)` are pairwise coprime (B.46's
   `isCoprime_pow_of_not_dvd`, exactly B.67 step 1), so landed
   `exists_monic_factorization_finset` supplies monic `g' i`.
4. B.78(iii) `peel_congr` on the two peels of the `π ^ N`-congruent products gives
   `π ^ N ∣ ((g i) - (g' i)).coeff k`; degrees match by `natDegree_eq_of_map_eq`.
5. Per block, B.79(b) at `gT := g' i`: `typeOf (g' i) = order1Type π (φ i) (g i)`.
6. B.63a's `typeOf_prod` on the step-3 peel, substitute step 5, close with
   `FactorizationType.ext`.

DEPENDS (direct): B.46 (`isCoprime_pow_of_not_dvd`) · B.63a (`typeOf_prod`) · B.66
(`order1Type`) · B.75 (`Visible`) · B.78(i) (`monicPoly_congr`), B.78(iii) (`peel_congr`) ·
B.79(b) (`typeOf_congr_of_certificate`) · landed `Uniformity.Density.decidedAt_of_congr`,
`Uniformity.Density.monicPoly_monic`, `monicPoly_natDegree`,
`Uniformity.Hensel.exists_monic_factorization_finset`, `Uniformity.Hensel.natDegree_eq_of_map_eq`,
`Uniformity.FactorizationType.ext`.

**SIZE.** blueprint 55 lines; landed 62.

**TEETH.** `W12-T-SIGMA` (`EFF.W12.27`) → **Lean theorem** (this node); `W12-BLOCK` → **Lean
theorem** at B.78, consumed at step 4; `W12-ORACLE` (`EFF.W12.56`, 0 bad / 41,923 PARI σ-multiset
checks) → **executable regression** retained, with D-4(a)'s scope note (the PARI oracle cannot
score a `disc = 0` lift; the Lean theorem covers it — the H-11 cash).

SOURCE: `EFF.W12.27` (the certification sentence, at D-4(a)'s every-lift quantifier);
`EFF.W12.51` (`W12-BOX-7`); `EFF.W12.21` (branchwise σ); `EFF.HE3.16` (THEOREM HE3.A).

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through B.79(b) ← B.79(a) ←
B.63 — the 2026-08-16 owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `[DecidableEq ι]` is part of the frozen signature (`leanspec/Leanspec/ChapB.lean`, **B.80**,
-- and the blueprint's SIGNATURE block); the proof opens `classical` instead of consuming it.
-- The binder is KEPT so that the landed form matches the stub byte for byte; only the linter is
-- silenced.
set_option linter.unusedDecidableInType false in
/-- **B.80 — the full level-`N` decidedness certificate.** Per-block terminating, visible order-1
reads inside D-3's perimeter decide the whole level-`N` class of `a`, at the sum of the blocks'
order-1 data. `hperim` is signed over the block's level-`N` **window class** (amendment A-F.12). -/
theorem decidedAt_of_order1_certificate (hπ : Irreducible π) {n N : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hvis : ∀ i ∈ s, Visible π (φ i) (g i) N)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    -- [re-signed: A-F.12] the window-class closure, per block — §12 item 4 display (4a″)
    (hperim : ∀ i ∈ s, ∀ gT : Polynomial O, gT.Monic → gT.natDegree = (g i).natDegree →
      (∀ k, π ^ N ∣ ((g i) - gT).coeff k) →
      ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ gT → IsPure (φ i) gS u ℓ →
        ∀ hne' : (sideSet (φ i) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt (φ i) gS (sideMin (φ i) gS u ℓ hne') = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField (φ i)), ψ.Monic → Irreducible ψ →
            (∃ c : (resField (φ i))ˣ, resPoly π (φ i) gS u ℓ hne' H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ (φ i).natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g'' ∈ monicFactors gS,
                (φ i).natDegree * ψ.natDegree ∣ inertiaDegOf g'')) :
    Uniformity.Density.DecidedAt O n ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ N
      (Uniformity.Density.proj O n N a) := by
  classical
  -- ## step 1 — `s` is nonempty, hence `0 < N`
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exfalso
      rw [Finset.prod_empty] at hgprod
      have hdeg := Uniformity.Density.monicPoly_natDegree a
      rw [hgprod, Polynomial.natDegree_one] at hdeg
      omega
    · exact h
  obtain ⟨i₀, hi₀⟩ := hsne
  have hN : N ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hvis i₀ hi₀
    exact hj (by simp)
  -- ## step 3 (preparation) — the residual blocks are pairwise coprime
  have h₀mon : ∀ i ∈ s, (((φ i).map (IsLocalRing.residue O)) ^ (e i)).Monic :=
    fun i hi => ((hkey i hi).monic.map _).pow _
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsCoprime (((φ i).map (IsLocalRing.residue O)) ^ (e i))
        (((φ j).map (IsLocalRing.residue O)) ^ (e j)) := by
    intro i hi j hj hij
    refine isCoprime_pow_of_not_dvd (hkey i hi).irred (fun hdvd => hne i hi j hj hij ?_)
    have hprime : Prime ((φ i).map (IsLocalRing.residue O)) := (hkey i hi).irred.prime
    exact Polynomial.eq_of_monic_of_associated ((hkey i hi).monic.map _)
      ((hkey j hj).monic.map _)
      ((hkey i hi).irred.associated_of_dvd (hkey j hj).irred (hprime.dvd_of_dvd_pow hdvd))
  -- the representative's own reduction, as a product of the residual blocks
  have hfres : (Uniformity.Density.monicPoly a).map (IsLocalRing.residue O)
      = ∏ i ∈ s, ((φ i).map (IsLocalRing.residue O)) ^ (e i) := by
    rw [hgprod, Polynomial.map_prod]
    exact Finset.prod_congr rfl hgres
  -- ## step 2 — enter through the landed certificate/census interface
  refine Uniformity.Density.decidedAt_of_congr hπ ?_
  intro b hb
  have hcong : ∀ j, π ^ N ∣
      (Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b).coeff j :=
    monicPoly_congr (fun i => dvd_sub_comm.1 (hb i))
  have hbres : (Uniformity.Density.monicPoly b).map (IsLocalRing.residue O)
      = ∏ i ∈ s, ((φ i).map (IsLocalRing.residue O)) ^ (e i) := by
    have hsub : (Uniformity.Density.monicPoly a
        - Uniformity.Density.monicPoly b).map (IsLocalRing.residue O) = 0 := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact (dvd_pow_self π hN).trans (hcong k)
    rw [Polynomial.map_sub, sub_eq_zero] at hsub
    rw [← hsub]
    exact hfres
  -- ## step 3 — Hensel-peel the lift along the same residual data
  obtain ⟨g', hg'mon, hg'prod, hg'res, -⟩ :=
    Uniformity.Hensel.exists_monic_factorization_finset s
      (Uniformity.Density.monicPoly_monic b)
      (fun i => ((φ i).map (IsLocalRing.residue O)) ^ (e i)) h₀mon hcop hbres
  -- ## step 4 — the two peels are congruent block by block, with matching degrees
  have hblk : ∀ i ∈ s, ∀ k, π ^ N ∣ ((g i) - (g' i)).coeff k := by
    refine peel_congr hπ hgmon hg'mon h₀mon hcop hgres hg'res ?_
    intro k
    rw [← hgprod, ← hg'prod]
    exact hcong k
  have hdeg' : ∀ i ∈ s, (g' i).natDegree = (g i).natDegree := by
    intro i hi
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq (hg'mon i hi) (hg'res i hi),
      Uniformity.Hensel.natDegree_eq_of_map_eq (hgmon i hi) (hgres i hi)]
  -- ## step 5 — B.79(b) per block, the class closure instantiated at the lift's peel
  have hblocktype : ∀ i ∈ s, typeOf (g' i) = order1Type π (φ i) (g i) := by
    intro i hi
    exact typeOf_congr_of_certificate hπ (hkey i hi) (hgmon i hi) (he i hi) (hgres i hi)
      (hterm i hi) (hvis i hi) (hg'mon i hi) (hdeg' i hi) (hblk i hi)
      (hperim i hi (g' i) (hg'mon i hi) (hdeg' i hi) (hblk i hi))
  -- ## step 6 — the peel law, then `FactorizationType.ext`
  refine Uniformity.FactorizationType.ext ?_
  rw [hg'prod, typeOf_prod hg'mon]
  exact Finset.sum_congr rfl fun i hi => by rw [hblocktype i hi]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.decidedAt_of_order1_certificate
end AxCheck
