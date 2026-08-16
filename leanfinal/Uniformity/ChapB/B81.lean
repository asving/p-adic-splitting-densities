/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B63a
import Uniformity.ChapB.B79a
import Uniformity.ChapB.B80

/-!
# Uniformity.ChapB.B81 — eventual certification: the per-member level exists

**Chapter B, NODE B.81** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C. One signed
declaration.

*The statement.* With B.80's data **minus the level** — `a : Fin n → O`, order-0 data
`(φ i, e i)`, the peel `g i` — and per block `dev (φ i) (g i) 0 ≠ 0`,
`¬ NeedsDescent π (φ i) (g i)`, `hperim i`:

```
∃ N : ℕ, 0 < N ∧ DecidedAt O n (typeOf (monicPoly a)) N (proj O n N a)
```

— every terminating, in-genre order-1 member is eventually certified, at a level read off its
**own** polygon heights. The level is per-member and this chapter states no uniform law over any
family (D-4(c); R8-1's counterexample shows none exists even for the family of a single shape).

## `hperim` is level-quantified under a `Visible` guard — the A-F.12 re-sign, and why

This node has no level in its signature — that is the point of it — so B.80's window-class
closure cannot be stated at a named `N`. It is therefore carried universally quantified over the
level and **guarded by visibility**:

```
∀ N : ℕ, (∀ i ∈ s, Visible π (φ i) (g i) N) → ∀ i ∈ s, ∀ gT, … (4a″) at that `N` …
```

The guard is load-bearing, not decoration: without it the `N = 0` instance (`π ^ 0 = 1` divides
everything) would demand the perimeter for **every** monic polynomial of each block's degree.
Step 1 constructs exactly such an `N` (B.76(v) + B.76(iii)), so the proof discharges the guard
where it creates it; step 3's B.79(a) applications are then satisfied reflexively (`gT := g i`,
`π ^ N ∣ 0`).

## Proof — the blueprint's three legs

1. Per block, B.76(v) `exists_visible` with `hnz i` gives a level `M i`; take
   `N := (s.sup M) + 1`, so `0 < N` and B.76(iii) `visible_mono` makes every block visible at `N`.
2. B.80 at this `N`, its `hperim` supplied by `hperim N` applied to step 1's visibility:
   `DecidedAt O n ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ N (proj O n N a)`.
3. The σ is the member's own type: per block B.79(a) (its `hperim` = the closure at `gT := g i`)
   gives `typeOf (g i) = order1Type π (φ i) (g i)`; B.63a's `typeOf_prod` over `hgprod` gives
   `(typeOf (monicPoly a)).data = ∑ (typeOf (g i)).data`; `FactorizationType.ext` closes, and
   rewriting in step 2 concludes.

DEPENDS (direct): B.63a (`typeOf_prod`) · B.66 (`order1Type`) · B.76(iii) (`visible_mono`),
B.76(v) (`exists_visible`) · B.79(a) (`typeOf_eq_order1Type`) · B.80
(`decidedAt_of_order1_certificate`) · landed `Uniformity.FactorizationType.ext`.

**SIZE.** blueprint 40 lines; landed 27. The §2 SPLIT CANDIDATE (step 3 as `B81a`, steps 1–2 as
`B81b`) is NOT taken: the landed proof is 27 lines and step 3 is 6 of them, so the split would
cost an interface and buy nothing. Chapter C's menu-to-density weld can extract
`typeOf_eq_sum_order1Type` when it actually needs it — RE-PLAN candidate, flagged.

**⚠ WHAT "EVENTUAL" DOES AND DOES NOT BUY.** This node certifies **one member at a time**. It does
NOT say the decided proportion tends to anything (that is drainage, chapter I — forward
reference), and it does NOT bound `N` by the shape (refuted, D-4(c)). It is the order-1 kernel of
the drainage argument, with `hnz`/`hterm`/`hperim` delimiting exactly which members "terminating"
means: `¬ hnz` is `EFF.HE3.55`'s out-of-genre residue, `¬ hterm` is the descent locus (chapter C),
and the perimeter's conditional region carries `B-BOX-1` (H-7).

**TEETH.** `HE-BND` (`EFF.HE3.55`, 3,744 boundary reads, RE-SCOPED by R8-1) → **executable
regression** retained: the battery's saturation columns (`N = 6, 7`) are per-member eventuality
observed; its never-decided residue (28/51) decomposes as the battery says into out-of-genre
(`¬ hnz`, 25/49) + deeper (`¬ hterm`-or-deeper, 3/2) — this node's hypothesis frontier, measured.

SOURCE: `EFF.HE3.67` (R8-1's replacement bullet 3 at order 1 — step 1's per-member `N` IS the
deepest-consulted-height stratification, and the refusal to state more is the correction carried);
`EFF.HE3.55` (HE-BND); `EFF.W12.86` step 5 (at order 1 only its terminal clause, `hterm`).

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through B.80 ← B.79 ← B.63 —
the 2026-08-16 owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `[DecidableEq ι]` is part of the frozen signature (`leanspec/Leanspec/ChapB.lean`, **B.81**,
-- and the blueprint's SIGNATURE block); the proof opens `classical` and hands the binder on to
-- B.80. The binder is KEPT so that the landed form matches the stub; only the linter is silenced.
set_option linter.unusedDecidableInType false in
/-- **B.81 — eventual certification.** A terminating, in-genre order-1 member is decided at some
level: the level built from its own blocks' polygon heights. `hperim` is level-quantified under a
`Visible` guard (amendment A-F.12). -/
theorem exists_decidedAt_of_terminating (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    -- [re-signed: A-F.12] the level-quantified, visibility-guarded window-class closure
    (hperim : ∀ N : ℕ, (∀ i ∈ s, Visible π (φ i) (g i) N) →
      ∀ i ∈ s, ∀ gT : Polynomial O, gT.Monic → gT.natDegree = (g i).natDegree →
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
    ∃ N : ℕ, 0 < N ∧ Uniformity.Density.DecidedAt O n
      (typeOf (Uniformity.Density.monicPoly a)) N (Uniformity.Density.proj O n N a) := by
  classical
  -- ## step 1 — a level at which every block is visible, and it is positive
  have hex : ∀ i ∈ s, ∃ M : ℕ, Visible π (φ i) (g i) M :=
    fun i hi => exists_visible hπ (hnz i hi)
  choose! M hM using hex
  refine ⟨s.sup M + 1, Nat.succ_pos _, ?_⟩
  have hvis : ∀ i ∈ s, Visible π (φ i) (g i) (s.sup M + 1) := fun i hi =>
    visible_mono ((Finset.le_sup hi).trans (Nat.le_succ _)) (hM i hi)
  -- ## step 3 — the σ of step 2 is the member's own type
  have hblock : ∀ i ∈ s, typeOf (g i) = order1Type π (φ i) (g i) := by
    intro i hi
    refine typeOf_eq_order1Type hπ (hkey i hi) (hgmon i hi) (he i hi) (hgres i hi)
      (hnz i hi) (hterm i hi) ?_
    -- the closure at `gT := g i` — reflexivity, `π ^ N ∣ 0`
    exact hperim (s.sup M + 1) hvis i hi (g i) (hgmon i hi) rfl (fun k => by simp)
  have htype : typeOf (Uniformity.Density.monicPoly a)
      = ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ := by
    refine Uniformity.FactorizationType.ext ?_
    rw [hgprod, typeOf_prod hgmon]
    exact Finset.sum_congr rfl fun i hi => by rw [hblock i hi]
  -- ## step 2 — B.80 at this level, with the closure supplied at the visibility just built
  rw [htype]
  exact decidedAt_of_order1_certificate hπ hn a hkey he hne hgmon hgprod hgres hvis hterm
    (hperim (s.sup M + 1) hvis)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_decidedAt_of_terminating
end AxCheck
