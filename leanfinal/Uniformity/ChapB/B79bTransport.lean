/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B79a
import Uniformity.ChapB.B74
import Uniformity.ChapB.B77a
import Uniformity.ChapB.B77b

/-!
# Uniformity.ChapB.B79bTransport — B.79 half (b)'s transport leg

# ⚠ NODE B.79b IS **NOT** LANDED. `typeOf_congr_of_certificate` IS ABSENT FROM THIS FILE.

This file is **not** a node file. It banks the one non-mechanical leg of B.79 half (b) —
`order1Type_congr`, the statement that B.66's order-1 datum is a function of the level-`N`
congruence class of a visible `g` — so that the reschedule of B.79b, after the signature defect
below is adjudicated, is a ten-line composition. The B.79b unit of 2026-08-16 found the node's
frozen signature **unprovable as signed**; it did not weaken it, and it did not bank a `sorry`.

## The defect: `hperim` is signed at `g`, the proof needs it at `g'`

B.79b's frozen stub (`leanspec/Leanspec/ChapB.lean`) reads

```lean
theorem typeOf_congr_of_certificate … (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g → IsPure φ gS u ℓ → … )
    {N : ℕ} (hvis : Visible π φ g N)
    {g' : Polynomial O} (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hgg' : ∀ i, π ^ N ∣ (g - g').coeff i) :
    typeOf g' = order1Type π φ g
```

and the blueprint's PROOF step 3 says of the perimeter clause: *"`hperim` for `g'` — its data
(slopes, residual factors) are **equal**, not just corresponding, by B.77's
`sideSet_congr`/`resPoly_congr`, so the clause transports by rewriting."* **That is false as
stated.** `hperim` is not a statement about the slope/residual data alone: it is universally
quantified over the **divisors** `gS ∣ g`, and its third disjunct
`∀ g'' ∈ monicFactors gS, φ.natDegree * ψ.natDegree ∣ inertiaDegOf g''` is a statement about the
inertia degrees of the monic factors of `gS`. To apply half (a) to `g'` one needs the same clause
over the divisors of `g'`, and

* nothing in the signature relates the divisor lattice of `g'` to that of `g` — the only
  hypotheses naming `g'` are `hg'`, `hdeg` and the coefficientwise congruence `hgg'`;
* B.73–B.77 transport `suppVal`, `sideSet`, `sideMin`/`sideMax`/`sideDeg`, `IsPure`, `resPoly`,
  `Visible` and `NeedsDescent`, and **none of them mentions `∣`, `monicFactors` or
  `inertiaDegOf`**; there is no landed congruence-invariance for `inertiaDegOf` anywhere in
  `leanfinal` (checked by grep, 2026-08-16);
* the missing statement — *`B-BOX-1` for a block transports across a level-`N` window
  congruence* — is of the same strength as the theorem being proved (B.79b asserts precisely that
  `typeOf`, hence the `(e,f)` data of the factors, is window-determined), so deriving it here
  would be circular.

**Everything else in B.79b closes.** The unit machine-checked the full skeleton with `hperim'`
as the single hole (scratch run, not committed): `0 < N` from `hvis`; `ḡ' = ḡ = φ̄ ^ μ` from
`hgg'` through `Ideal.Quotient.eq_zero_iff_mem` and `hπ.maximalIdeal_eq`; `Visible π φ g' N` by
B.76(iv) `visible_congr`; `dev φ g' 0 ≠ 0` by B.76(ii) + `npHgt_eq_top_iff`;
`¬ NeedsDescent π φ g'` by B.74's `needsDescent_congr`; then half (a) at `g'` and
`order1Type_congr` (this file) to land on `order1Type π φ g`.

**Proposed repair (owner call, not taken here).** Either (i) re-sign B.79b's `hperim` at `g'`
(`gS ∣ g'`) — the §12 item 4 dictionary clause instantiated at the polynomial the node's proof
actually dissects, which is the reading B.79b's own consumers can supply; or (ii) add a second
perimeter clause at `g'` alongside the one at `g`. Both are B-D10-class stub-stage repairs, of
exactly the kind §9's note anticipates (*"a divergence there is a stub-stage blueprint defect"*).
Note that the same question should be asked of **B.80**, whose per-block `hperim` is at `g i`
while its `DecidedAt` conclusion quantifies over the congruence class.

## What this file does prove

`order1Type_congr` : under `hvis : Visible π φ g N`, `hdeg`, and `hgg'`,

```
order1Type π φ g' = order1Type π φ g.
```

Both index finsets are equal, not merely corresponding:

1. `slopeFinset` — B.77a's `sideSet_congr` makes the defining condition of B.66a's
   `mem_slopeFinset` literally the same at `g` and at `g'` (the degree pins come from `hres`
   through landed `natDegree_eq_of_map_eq`, and `hdeg` carries the second one).
2. `resFactorFinset` at each slope — B.66a's `mem_resFactorFinset` reads "monic irreducible
   dividing the residual polynomial at the `sideMin` pin". The pinned abscissa agrees
   (`sideSet_congr` plus proof-irrelevant `Finset.min'`), the pinned **height** agrees (B.76(i)
   `npHgt_min_congr` together with the window guard, which puts both heights strictly below `N`),
   and then B.77b's `resPoly_congr` makes the residual polynomials themselves equal.
3. The `Multiset.bind` of B.66's definition is then congruent term by term.

**The window guard is consumed by name, not re-derived** — B.74's `H₀_lt_of_visible`, promoted
from `private` to public in the same commit (visibility only). That is amendment A-F.11's action
item for this unit; the item names the inner `suppVal_lt_of_vis`, but `H₀_lt_of_visible` is the
finished guard (`H₀ < N` at the `sideMin` pin = exactly `resPoly_congr`'s `hH₀`), so promoting it
also spares the consumer the HE-T-CAP chain. This is the content `HE-T-CAP` (`EFF.HE3.54`) tests:
one visibility hypothesis at abscissa `0` guards the whole side family.

DEPENDS: B.66 (`order1Type`, `order1Type_data`) · B.66a (`mem_slopeFinset`,
`mem_resFactorFinset`, `mem_slopeFinset_imp`) · B.74 (`H₀_lt_of_visible`) · B.76(i)
(`npHgt_min_congr`), B.76(iv) (`visible_congr`) · B.77a (`sideSet_congr`) · B.77b
(`resPoly_congr`) · B.39b (`sideSet_nonempty_gen`, through B.63) · landed
`Uniformity.Hensel.natDegree_eq_of_map_eq` · mathlib `Multiset.bind_congr`, `min_choice`.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound`** — the B.42 literature cite
is on the import path (through B.79a) but this declaration does not consume it.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
/-- **B.79 half (b), the transport leg.** B.66's order-1 datum is a function of the level-`N`
congruence class of a `Visible`-at-`N` polynomial: both canonical index finsets are literally
equal at `g` and at `g'`, so the data are. -/
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
