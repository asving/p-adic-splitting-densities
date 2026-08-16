/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115c
import Uniformity.ChapH.H16

/-!
# Uniformity.ChapH.H114 — the α-locus law

**Chapter H, NODE H.114** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.2).

`card_alphaSlice` — at a realized slope `k` (`1 ≤ k`, `m k ≤ N − 1`),

`#{c | ∃ z, IsAlphaState π c k z} = (Q − 1) · Q ^ (m (N − 1) − k · clusterC (m + 1))`,

the slope written `clusterC (m+1) = (m+1).choose 2 = m (m+1) / 2` (H.13's binomial form — exact
in `ℕ`, no floor).  Out-of-window `k` carry no events (H.112 (ii)), so no law is stated there.

## The proof, in three lines

1. The α event PINS its centre (H.112's `alpha_event_unique`), so the locus is the disjoint union
   over `z` of the `(k, z)` slices, and the `z = 0` slice is empty (`z ≠ 0` is a clause of
   `HasChildAt`).
2. Each `(k, z)` slice fibres over the child state space by `alphaChild`, with EVERY fibre of
   size `Q ^ (k · clusterC m)` (H.115 clause (iii), `card_alphaFiber`) over `Q ^ (m (N − m k − 1))`
   child states (H.106's census) — so the slice has `Q ^ alphaExp m (N − m k − 1) k` elements.
3. The exponent recomposes: H.16(ii)'s subtraction-free identity
   `2 · alphaExp m W k + k (m (m+1)) = 2 (m (W + m k))` at `W = N − m k − 1` is exactly
   `alphaExp m W k = m (N − 1) − k · clusterC (m+1)`, and `(Q − 1)` counts the centres.

**On clause (ii).**  The blueprint's DEPENDS lists both counting clauses of H.115; this proof
consumes only clause (iii).  That is not a gap but a saving: `card_alphaFiber` asserts EVERY
fibre has `Q ^ (k · clusterC m) ≥ 1` elements, and a `Nat.card` that is nonzero forces the fibre
nonempty — so surjectivity (clause (ii), `alphaChild_surjective`, landed in `ChapH/H115b.lean`)
is subsumed rather than assumed.

DEPENDS: H.115c (`card_alphaFiber`) · H.112 (`alpha_event_unique`) · H.111 (`IsAlphaState`) ·
H.109 (`HasChildAt`, whose `z ≠ 0` clause empties the zero slice) · H.106 (`ClusterState`,
`card_clusterState`) · H.13 (`clusterC`), H.15 (`alphaExp`), H.16 (`two_mul_alphaExp_add`),
H.14 (`two_mul_clusterC`) · landed `residueCard`, `instFiniteRes` · mathlib
`Equiv.sigmaFiberEquiv`, `Nat.card_sigma`, `Finset.sum_erase`, `Finset.card_erase_of_mem`.

**ENVIRONMENT — ENV-H17** + `[Finite (ResidueField O)]` + `π` explicit.

## TEETH (GC-8)

Battery `P1(c) alpha locus law + window` of `verification/openmath/OM2_genindb_battery.py`
(exhaustive, 28 cells × 2 rings).  The `#guard`s below reproduce the closed form against the
factored count `(Q − 1) · Q ^ (k c(m)) · Q ^ (m (N − m k − 1))` at every realized slope of the
battery's `part1` plan — the two sides of step 3's exponent identity, as numerals.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

section Locus

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-! ## 0. Finiteness of the carrier

`ClusterState` is a `def`, so instance search does not see the subtype through it; the census
`card_clusterState` never needed the instance (`Nat.card` is total), but the fibrations below do. -/

instance instFiniteClusterState (m N : ℕ) : Finite (ClusterState O m N) := by
  unfold ClusterState
  infer_instance

/-! ## 1. One `(k, z)` slice -/

/-- **The `(k, z)` slice, counted.**  `alphaChild` fibres the slice over the window-`(N − m k)`
state space with constant fibre `Q ^ (k · clusterC m)`; the base has `Q ^ (m (N − m k − 1))`
points (H.106), so the slice has `Q ^ alphaExp m (N − m k − 1) k` points. -/
theorem card_alphaSliceAt {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) (hz : z ≠ 0) :
    Nat.card {c : ClusterState O m N // IsAlphaState π c k z}
      = residueCard O ^ alphaExp m (N - m * k - 1) k := by
  classical
  haveI : Fintype (ClusterState O m (N - m * k)) := Fintype.ofFinite _
  -- every fibre of the child map has `Q ^ (k · clusterC m)` points
  have hfib : ∀ d : ClusterState O m (N - m * k),
      Nat.card {x : {c : ClusterState O m N // IsAlphaState π c k z} //
          alphaChild π x.1 x.2 = d} = residueCard O ^ (k * clusterC m) := by
    intro d
    have e : {x : {c : ClusterState O m N // IsAlphaState π c k z} // alphaChild π x.1 x.2 = d}
        ≃ {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d} :=
      { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, y.2.choose⟩, y.2.choose_spec⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
    rw [Nat.card_congr e]
    exact card_alphaFiber hπ hm hN hk hw hz d
  -- sum the fibres over the base
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun x : {c : ClusterState O m N // IsAlphaState π c k z} => alphaChild π x.1 x.2)).symm,
    Nat.card_sigma, Finset.sum_congr rfl (fun d _ => hfib d), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    card_clusterState m (N - m * k) (by omega), ← pow_add, alphaExp]

/-! ## 2. The locus -/

/-- **H.114.** `#α(k) = (Q − 1) · Q ^ (m (N − 1) − k · clusterC (m+1))` at realized `k`. -/
theorem card_alphaSlice {π : O} (hπ : Irreducible π) {m N k : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) :
    Nat.card {c : ClusterState O m N // ∃ z, IsAlphaState π c k z}
      = (residueCard O - 1) * residueCard O ^ (m * (N - 1) - k * clusterC (m + 1)) := by
  classical
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  -- STEP 1: the α event pins its centre, so the locus splits over `z`
  have einner : ∀ z : ResidueField O,
      {x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} // x.2.choose = z}
        ≃ {c : ClusterState O m N // IsAlphaState π c k z} := by
    intro z
    exact ⟨fun x => ⟨x.1.1, by
        obtain ⟨⟨c, hex⟩, hcz⟩ := x
        exact hcz ▸ hex.choose_spec⟩,
      fun y => ⟨⟨y.1, ⟨z, y.2⟩⟩, (alpha_event_unique hπ hm
        (Exists.choose_spec (⟨z, y.2⟩ : ∃ z', IsAlphaState π y.1 k z')) y.2).2⟩,
      fun _ => Subtype.ext (Subtype.ext rfl), fun _ => Subtype.ext rfl⟩
  -- STEP 2: the zero slice is empty (`z ≠ 0` is a clause of `HasChildAt`)
  have hz0 : Nat.card {x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} //
      x.2.choose = (0 : ResidueField O)} = 0 := by
    rw [Nat.card_congr (einner 0)]
    haveI : IsEmpty {c : ClusterState O m N // IsAlphaState π c k (0 : ResidueField O)} :=
      ⟨fun x => x.2.2.2.2.2.1 rfl⟩
    exact Nat.card_of_isEmpty
  -- STEP 3: each nonzero slice, by §1
  have hterm : ∀ z : ResidueField O, z ≠ 0 →
      Nat.card {x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} // x.2.choose = z}
        = residueCard O ^ alphaExp m (N - m * k - 1) k := by
    intro z hz
    rw [Nat.card_congr (einner z)]
    exact card_alphaSliceAt hπ hm hN hk hw hz
  -- STEP 4: sum over the `Q − 1` admissible centres
  have hsum : Nat.card {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'}
      = ∑ z : ResidueField O,
          Nat.card {x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} //
            x.2.choose = z} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} => x.2.choose)).symm,
      Nat.card_sigma]
  have hcardQ : Fintype.card (ResidueField O) = residueCard O := Nat.card_eq_fintype_card.symm
  rw [hsum, ← Finset.sum_erase (f := fun z : ResidueField O =>
        Nat.card {x : {c : ClusterState O m N // ∃ z', IsAlphaState π c k z'} //
          x.2.choose = z}) Finset.univ hz0,
    Finset.sum_congr rfl (fun z hz => hterm z (Finset.ne_of_mem_erase hz)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, hcardQ]
  -- STEP 5: the exponent recomposition (H.16(ii))
  congr 1
  have hWmk : N - m * k - 1 + m * k = N - 1 := by omega
  have hc2 : 2 * clusterC (m + 1) = (m + 1) * m := by
    have h := two_mul_clusterC (m + 1)
    simpa using h
  have h16 := two_mul_alphaExp_add m (N - m * k - 1) k
  have h1 : k * (m * (m + 1)) = 2 * (k * clusterC (m + 1)) := by
    rw [show m * (m + 1) = (m + 1) * m from Nat.mul_comm _ _, ← hc2]
    ring
  rw [h1, hWmk] at h16
  congr 1
  omega

end Locus

end Uniformity.Density.Induction

/-! ## 3. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.card_alphaSliceAt
#print axioms Uniformity.Density.Induction.card_alphaSlice

end AxCheck

/-! ## 4. TEETH — the locus law against the factored count

The battery's `P1(c)` enumerates the α locus per cell.  The theorem's closed form is
`(Q − 1) · Q ^ (m (N − 1) − k c(m+1))`; the enumeration form is the factored count
`(Q − 1) · Q ^ (k c(m)) · Q ^ (m (N − m k − 1))` — centres × ghost fibre × child states.  The
plan is the battery's own `part1` plan crossed with its realized slopes. -/

section NumericLocus

private def locusCN (m : ℕ) : ℕ := m * (m - 1) / 2

private def locusPlan : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)]

private def locusK (m N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)

-- closed form = centres × ghost fibre × child census, at every realized slope
#guard locusPlan.all fun p =>
  (locusK p.2.1 p.2.2).all fun k =>
    (p.1 - 1) * p.1 ^ (p.2.1 * (p.2.2 - 1) - k * locusCN (p.2.1 + 1))
      == (p.1 - 1) * (p.1 ^ (k * locusCN p.2.1) * p.1 ^ (p.2.1 * (p.2.2 - p.2.1 * k - 1)))

-- the ℕ-subtraction guard of the displayed exponent: `k c(m+1) ≤ m (N − 1)` in the window
#guard locusPlan.all fun p =>
  (locusK p.2.1 p.2.2).all fun k => k * locusCN (p.2.1 + 1) ≤ p.2.1 * (p.2.2 - 1)

-- `clusterC` is the binomial, and the two slopes differ by `m`
#guard (List.range 8).all fun m => locusCN m == Nat.choose m 2
#guard (List.range 8).all fun m => locusCN (m + 1) == locusCN m + m

-- the battery's largest live cell `q = 2, m = 3, N = 6` at `k = 1`: `1 · 2 ^ (15 − 6) = 512`
#guard (2 - 1) * 2 ^ (3 * (6 - 1) - 1 * locusCN 4) == 512

end NumericLocus
