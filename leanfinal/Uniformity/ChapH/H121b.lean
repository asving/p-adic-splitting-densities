/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H121

/-!
# Uniformity.ChapH.H121b — the α leg (H.121 clause ii)

**Chapter H, NODE H.121 clause (ii)** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.3 —
the T-1 completion layer, dated extension 2026-08-16; provenance OM-2 §3.3 N-3, *"halpha holds
as an EQUALITY with the windowed range and the structure slope c = m(m+1)/2"*, sources
`EFF.GENIND.45` (the `S5.2` recursion) and `EFF.GENIND.152`).  Split-mandated part **b** of
H.121 (part a is `H121`, part c is owed).

* `clusterUndecided_alphaChild` — on an α state the verdict passes to the sheared child;
* `card_alphaUndecidedFiber` — the ghost fibre over a PRESCRIBED undecided child;
* `card_alphaUndecidedAt` — one `(k, z)` slice: `Q ^ (k · c(m)) · u(N − mk)`;
* `uCluster_alpha_leg` (clause ii) — the α leg as an EQUALITY at the UNBOUNDED windowed range.

## The argument

Three moves, in the order the count is assembled.

**1. The verdict is carried by the shear, in both directions.**  On an α state `c` the four
disjuncts of H.119's inversion collapse to one: `c` is not drain and not CS (both are conjuncts
of `IsAlphaState`), and it is not β (H.111's `alpha_not_beta` — the α witness IS a
full-multiplicity child, which β's fourth conjunct denies).  So `c` is undecided iff SOME α
witness has an undecided child; and H.112 (clause i)'s `alpha_event_unique` says the witness is
unique in BOTH slope and centre, so "some" is "the".  Definitional proof irrelevance does the
rest: two proofs of `IsAlphaState π c k z` give the same `alphaChild`, so no transport is
needed.  Backwards it is H.118's `alpha` constructor.  That is `clusterUndecided_alphaChild`
plus the `invFun` of the fibre equivalence.

**2. One `(k, z)` slice.**  Fibre the α-undecided states with event `(k, z)` over the map
`c ↦ alphaChild`, which by move 1 lands in the UNDECIDED child states.  Every fibre is H.115
(clause iii)'s ghost fibre `Q ^ (k · clusterC m)` (`card_alphaFiber`), so the slice is
`Q ^ (k · clusterC m) · u(N − mk)`.  This is H.114's `card_alphaSliceAt` with the base cut down
from all child states to the undecided ones — and it is exactly why the recursion's coefficient
is the STRUCTURE slope: normalized against the census `Q ^ (m(N−1))` the factor
`Q ^ (k · clusterC m)` recomposes with the base normalization into
`Q ^ (−k · clusterC (m+1))`, i.e. slope `c = m(m+1)/2` (H.16/H.17, fired in H.114).

**3. The two index sums.**  The α-undecided locus is the disjoint union of its `(k, z)` slices
over the realized events; disjointness is again `alpha_event_unique`.  The centre `z` runs over
the `Q − 1` NONZERO residues (`z ≠ 0` is a conjunct of `HasChildAt`), and the slope `k` runs
over the WINDOWED range `1 ≤ k`, `mk ≤ N − 1` — H.112 (clause ii)'s `alpha_content`, which
derives both bounds from the event itself, so no out-of-window slope is silently dropped.

## ⚠ FINDING F-H17.1 — the range is window-dependent

The realized slope range is `{k | 1 ≤ k ∧ mk ≤ N − 1}`, which MOVES with `N`.  No fixed `n₀`
covers it, so this equality does NOT inhabit the landed fixed-`n₀` `RecursionLegs` structure
(blueprint §17.0, finding F-H17.1); PA-H17.1 is the repair, and until it lands H.122 must replay
H.71's six steps locally against this display.  The window filter is not cosmetic: dropping it
would make the sum read `u(0)`, and `u(0) = 1` in this formalization (the window-`0` carrier is
a point and that point is a drain), so the unwindowed display is FALSE, not merely unmotivated.
The defeat is gated numerically in §5 (battery `P3 CC-3(i)`).

## ⚠ The S-1 fence

`uCluster` is the CONSERVATIVE complement `u_{m,1}`, never the semantic `undecidedCount`
(finding F-2).  Nothing here is a statement about the semantic undecided locus.

DEPENDS: H.111 (`IsAlphaState`, `alpha_not_beta`), H.112 (`alpha_content`,
`alpha_event_unique`), H.114 (`instFiniteClusterState`, the slice pattern), H.115 (`alphaChild`)
+ H.115c (`card_alphaFiber`), H.118 (`ClusterUndecided.alpha`), H.119 (`uCluster`,
`exists_witness_of_clusterUndecided`), H.121a (the split this leg feeds), H.13 (`clusterC`).

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `[Finite (ResidueField O)]` +
`[IsAdicComplete (maximalIdeal O) O]` + `π` explicit, every binder INLINE.  `(O : Type)` (not
`Type*`) in the signed statement: the frozen stub pins the universe, and H.119's
`exists_witness_of_clusterUndecided` is stated there too.

Note the signature carries NO `m ≤ 3`: the α leg is unconditional at every `m ≥ 2` (the
blueprint states it "at every `m ≥ 2`"), because nothing in the argument touches the CS bucket —
a CS state is not an α state by definition.

## TEETH (GC-8)

Battery `P3 halpha windowed, slope m(m+1)/2, EQUALITY` + `P3 CC-3(i)` of
`verification/openmath/OM2_genindb_battery.py`.  §5 runs three gates.  (1) At `m = 2`, where
the β bucket is EMPTY, the split of H.121a reduces to `hexR = drain + αleg`, so the α leg is
pinned EXACTLY by the landed closed form — checked at both battery characteristics through
window 8.  (2) The CC-3(i) DEFEAT: the same display with the window filter removed and the Lean
value `u(0) = 1` overshoots (`16 ≠ 12` at `q = 2, m = 2, N = 4`).  (3) At `m = 3` the α leg's
own values are pinned against `hexU`, together with the slope recomposition
`k · clusterC 3 = 3k`.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The verdict passes to the sheared child -/

/-- **The α shear carries the verdict.**  If an α state is conservatively undecided then its
(unique) sheared child is.  H.119's inversion offers four disjuncts; drain and CS are denied by
`IsAlphaState`'s own conjuncts, β by H.111's `alpha_not_beta`, and the surviving α disjunct is
matched to the given event by H.112's `alpha_event_unique` — after which the two `IsAlphaState`
proofs are definitionally equal, so the two `alphaChild`s are the same term. -/
theorem clusterUndecided_alphaChild {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m N k : ℕ} {z : ResidueField O} (hm : 2 ≤ m) {c : ClusterState O m N}
    (hα : IsAlphaState π c k z) (hu : ClusterUndecided O π m N c) :
    ClusterUndecided O π m (N - m * k) (alphaChild π c hα) := by
  rcases exists_witness_of_clusterUndecided hu hα.1 hα.2.1 with ⟨k', z', hα', hrec⟩ | ⟨hβ, -⟩
  · obtain ⟨hkk, hzz⟩ := alpha_event_unique hπ hm hα' hα
    subst hkk
    subst hzz
    exact hrec
  · exact absurd hβ (alpha_not_beta hα)

/-! ## 2. The ghost fibre over a prescribed undecided child -/

section Fibre

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The fibre of the shear over an undecided child.**  Forward, forget the verdict; backward,
H.118's `alpha` constructor rebuilds it from the child's.  So the fibre is H.115 (clause iii)'s
ghost fibre and has `Q ^ (k · clusterC m)` points. -/
theorem card_alphaUndecidedFiber {π : O} (hπ : Irreducible π) {m N k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1)
    (hz : z ≠ 0) (d : {d : ClusterState O m (N - m * k) //
      ClusterUndecided O π m (N - m * k) d}) :
    Nat.card {x : {c : ClusterState O m N //
        IsAlphaState π c k z ∧ ClusterUndecided O π m N c} //
        (⟨alphaChild π x.1 x.2.1, clusterUndecided_alphaChild hπ hm x.2.1 x.2.2⟩ :
          {d : ClusterState O m (N - m * k) // ClusterUndecided O π m (N - m * k) d}) = d}
      = residueCard O ^ (k * clusterC m) := by
  classical
  have e : {x : {c : ClusterState O m N //
        IsAlphaState π c k z ∧ ClusterUndecided O π m N c} //
        (⟨alphaChild π x.1 x.2.1, clusterUndecided_alphaChild hπ hm x.2.1 x.2.2⟩ :
          {d : ClusterState O m (N - m * k) // ClusterUndecided O π m (N - m * k) d}) = d}
      ≃ {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d.1} :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.1, congrArg Subtype.val x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, y.2.choose, ClusterUndecided.alpha y.1 y.2.choose
          (by rw [y.2.choose_spec]; exact d.2)⟩, Subtype.ext y.2.choose_spec⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  rw [Nat.card_congr e]
  exact card_alphaFiber hπ hm hN hk hw hz d.1

/-! ## 3. One `(k, z)` slice -/

/-- **The `(k, z)` slice of the α-undecided locus.**  H.114's `card_alphaSliceAt` with the base
cut down to the UNDECIDED child states: `Q ^ (k · clusterC m) · u(N − mk)`. -/
theorem card_alphaUndecidedAt {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) (hz : z ≠ 0) :
    Nat.card {c : ClusterState O m N //
        IsAlphaState π c k z ∧ ClusterUndecided O π m N c}
      = residueCard O ^ (k * clusterC m) * uCluster O π m (N - m * k) := by
  classical
  haveI : Fintype {d : ClusterState O m (N - m * k) //
    ClusterUndecided O π m (N - m * k) d} := Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun x : {c : ClusterState O m N //
          IsAlphaState π c k z ∧ ClusterUndecided O π m N c} =>
        (⟨alphaChild π x.1 x.2.1, clusterUndecided_alphaChild hπ hm x.2.1 x.2.2⟩ :
          {d : ClusterState O m (N - m * k) // ClusterUndecided O π m (N - m * k) d}))).symm,
    Nat.card_sigma,
    Finset.sum_congr rfl (fun d _ => card_alphaUndecidedFiber hπ hm hN hk hw hz d),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, uCluster,
    Nat.mul_comm]

end Fibre

/-! ## 4. The two index sums -/

/-- **H.121 (clause ii) — the α leg, as an EQUALITY at the UNBOUNDED windowed range.**
`#(α ∧ undecided)(N) = Σ_{1 ≤ k, mk ≤ N−1} (Q − 1) · Q ^ (k · clusterC m) · u(N − mk)`.

The locus is the disjoint union of its `(k, z)` slices (H.112's `alpha_event_unique`), the
centre runs over the `Q − 1` nonzero residues (`z ≠ 0` is a conjunct of `HasChildAt`), and the
slope runs over the windowed range (H.112's `alpha_content`, which DERIVES `1 ≤ k` and
`mk ≤ N − 1` from the event).  ⚠ The range moves with `N` (finding F-H17.1). -/
theorem uCluster_alpha_leg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {c : ClusterState O m N //
        (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c}
      = ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ m * k ≤ N - 1),
          (residueCard O - 1) * residueCard O ^ (k * clusterC m)
            * uCluster O π m (N - m * k) := by
  classical
  haveI : Fintype (ClusterState O m N) := Fintype.ofFinite _
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  -- the locus, cut into its `(k, z)` slices
  have hbi : Finset.univ.filter (fun c : ClusterState O m N =>
        (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c)
      = (((Finset.range N).filter (fun k => 1 ≤ k ∧ m * k ≤ N - 1))
            ×ˢ (Finset.univ.erase (0 : ResidueField O))).biUnion
          (fun p => Finset.univ.filter (fun c : ClusterState O m N =>
            IsAlphaState π c p.1 p.2 ∧ ClusterUndecided O π m N c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨⟨k, z, hα⟩, hu⟩
      obtain ⟨-, hk, hw⟩ := alpha_content hπ hm hN hα
      have hkm : k ≤ m * k := Nat.le_mul_of_pos_left k (by omega)
      exact ⟨(k, z), ⟨⟨by omega, hk, hw⟩, hα.2.2.2.2.1, trivial⟩, hα, hu⟩
    · rintro ⟨p, -, hα, hu⟩
      exact ⟨⟨p.1, p.2, hα⟩, hu⟩
  -- the slices are pairwise disjoint: the α event is unique
  have hdisj : Set.PairwiseDisjoint
      (↑(((Finset.range N).filter (fun k => 1 ≤ k ∧ m * k ≤ N - 1))
        ×ˢ (Finset.univ.erase (0 : ResidueField O))) : Set (ℕ × ResidueField O))
      (fun p : ℕ × ResidueField O => Finset.univ.filter (fun c : ClusterState O m N =>
        IsAlphaState π c p.1 p.2 ∧ ClusterUndecided O π m N c)) := by
    intro p _ q _ hpq
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rintro c ⟨hp, -⟩ ⟨hq, -⟩
    obtain ⟨hkk, hzz⟩ := alpha_event_unique hπ hm hp hq
    exact hpq (Prod.ext hkk hzz)
  have hcardQ : Fintype.card (ResidueField O) = residueCard O := Nat.card_eq_fintype_card.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hbi, Finset.card_biUnion hdisj,
    Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro k hkF
  rw [Finset.mem_filter, Finset.mem_range] at hkF
  obtain ⟨-, hk1, hkw⟩ := hkF
  have hterm : ∀ z ∈ Finset.univ.erase (0 : ResidueField O),
      (Finset.univ.filter (fun c : ClusterState O m N =>
        IsAlphaState π c k z ∧ ClusterUndecided O π m N c)).card
        = residueCard O ^ (k * clusterC m) * uCluster O π m (N - m * k) := by
    intro z hzm
    rw [← card_alphaUndecidedAt hπ hm hN hk1 hkw (Finset.ne_of_mem_erase hzm),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, hcardQ,
    Nat.mul_assoc]

end Uniformity.Density.Induction

/-! ## 5. TEETH

`hexR`/`hexU` are `OM2_genindb_battery.py`'s `hex3R_ref`/`hex3U_ref`, transcribed verbatim (the
same transcription H.119's and H.121a's gates pin, with the same reference values).
`drainCount q m N` is H.113's head census `q ^ ((m−1)(N−1))` and `alphaLeg q m N u c` is THIS
node's display, `Σ_{1 ≤ k, mk ≤ N−1} (q − 1) q ^ (k c) u(N − mk)` with `c = clusterC m`
(`clusterC 2 = 1`, `clusterC 3 = 3`).

### 5.1 The α leg pinned exactly, at `m = 2`

At `m = 2` the β bucket is EMPTY (H.118's `betaChild_mult_lt` would need `2 ≤ μ < 2`), so
H.121a's split reads `hexR = drain + αleg`, which pins the α leg on the nose at both battery
characteristics through window 8.

### 5.2 The CC-3(i) defeat — the window filter is FORCED

`alphaLegUnwindowed` is the same display with the filter relaxed from `mk ≤ N − 1` to
`mk ≤ N`, so it consults `u(0)`.  In this formalization `u(0) = 1` (the window-`0` carrier is a
single point, and that point is a drain), NOT the `0` a naive reference implementation returns —
so the unwindowed display OVERSHOOTS: at `q = 2, m = 2, N = 4` it gives `16` against the true
`12`.  The gate checks the overshoot and pins both values.

### 5.3 The α leg at `m = 3`, and the slope

The realized α-leg values at `m = 3` against `hexU`, pinned at both characteristics; plus
`k · clusterC 3 = 3 k`, the exponent this node's coefficient carries.

⚠ S-1: `hexR`/`hexU` are CONSERVATIVE-family closed forms; nothing here ties them to the
semantic `undecidedCount` (finding F-2). -/

section NumericGate

/-- The battery's `hex3R_ref` — ChapG `hex3R`, the `m = 2` conservative complement. -/
private def hexR (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The battery's `hex3U_ref` — ChapG `hex3U`, the cubic per-centre conservative complement. -/
private def hexU (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hexR q (N - 3 * k))).sum

/-- H.113's head census `q ^ ((m − 1)(N − 1))`. -/
private def drainCount (q m N : ℕ) : ℕ := q ^ ((m - 1) * (N - 1))

/-- THIS node's display: `Σ_{1 ≤ k, mk ≤ N−1} (q − 1) q ^ (k c) u(N − mk)`. -/
private def alphaLeg (q m N : ℕ) (u : ℕ → ℕ) (c : ℕ) : ℕ :=
  (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)).map fun k =>
    (q - 1) * q ^ (k * c) * u (N - m * k)).sum

/-- The same display with the window filter RELAXED to `mk ≤ N`, so that it consults `u(0)`. -/
private def alphaLegUnwindowed (q m N : ℕ) (u : ℕ → ℕ) (c : ℕ) : ℕ :=
  (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N)).map fun k =>
    (q - 1) * q ^ (k * c) * u (N - m * k)).sum

/-- The conservative complement AS LEAN COMPUTES IT at window `0`: the carrier is a point and
the point is a drain, so `u(0) = 1` — not the `0` of a naive reference implementation. -/
private def uLean (q M : ℕ) : ℕ := if M = 0 then 1 else hexR q M

-- 5.1: at `m = 2` the split has no β cell, so the α leg is pinned exactly
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 9).drop 1).all fun N =>
    hexR q N == drainCount q 2 N + alphaLeg q 2 N (hexR q) 1

-- 5.1: the α leg is nonempty from `N = 3` on (the recursion has content, `q = 2`)
#guard ((List.range 9).drop 1).map (fun N => alphaLeg 2 2 N (hexR 2) 1)
  == [0, 0, 2, 4, 16, 32, 96, 192]

-- 5.2: CC-3(i) — with the window relaxed the display reads `u(0) = 1` and OVERSHOOTS
#guard (drainCount 2 2 4 + alphaLegUnwindowed 2 2 4 (uLean 2) 1,
    drainCount 2 2 4 + alphaLeg 2 2 4 (uLean 2) 1, hexR 2 4) == (16, 12, 12)
#guard !(drainCount 2 2 4 + alphaLegUnwindowed 2 2 4 (uLean 2) 1 == hexR 2 4)

-- 5.2: the windowed display never consults window `0` (the two `u`s agree on it)
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 9).drop 1).all fun N =>
    alphaLeg q 2 N (uLean q) 1 == alphaLeg q 2 N (hexR q) 1

-- 5.3: the α leg at `m = 3`, pinned against `hexU`
#guard ((List.range 8).drop 1).map (fun N => alphaLeg 2 3 N (hexU 2) 3)
  == [0, 0, 0, 8, 32, 128, 640]
#guard ((List.range 8).drop 1).map (fun N => alphaLeg 3 3 N (hexU 3) 3)
  == [0, 0, 0, 54, 486, 4374, 46656]

-- 5.3: the exponent `k · clusterC m` at the two live degrees (`clusterC 2 = 1`,
-- `clusterC 3 = 3`)
#guard (List.range 6).all fun k => (k * 1, k * 3) == (k, 3 * k)

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.clusterUndecided_alphaChild
#print axioms Uniformity.Density.Induction.card_alphaUndecidedFiber
#print axioms Uniformity.Density.Induction.card_alphaUndecidedAt
#print axioms Uniformity.Density.Induction.uCluster_alpha_leg

end AxCheck
