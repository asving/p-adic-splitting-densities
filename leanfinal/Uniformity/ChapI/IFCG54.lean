/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG53
import Uniformity.ChapI.IFCG51
import Uniformity.ChapI.IFCG1

/-!
# Uniformity.ChapI.IFCG54 — THE E2 dd TOWER CLOSES CITE-FREE: the three
`ZcURLim (e2DdDecFam σ)` limits by translation self-similarity

**UNIT DDT** (wave C, 2026-08-31).  E2L (IFCG53) left the three named dd-recursion
terms `ZcURLim (e2DdDecFam σ)`, σ ∈ {ramPair, splitTail, inertTail}, as the E2 front's
only open premises, with a recorded discharge path through a two-block Hensel
decidedness transport.  This file closes all three by a STRICTLY LIGHTER, cite-free
mechanism:

## The mechanism (translation self-similarity)

The E2-dd recentring key is LINEAR: `x ↦ x + zπ^s` over the SAME `O`.  Translation is
an `O`-algebra automorphism of `O[x]`, so `typeOf` and `DecidedAt` transport through it
for free (IFCG1's landed `shiftVecN`/`coeffShiftEquivN` kit) — no OM cite, no Hensel
continuity, no mass-2 zero-cone consumption.  Concretely, with `δ = resDig π 1 (c 2)`,
the dd stratum at corner depth `s` with residual double root at `−t̄` (`ddPairs` pair
`(2t̄, t̄²)`) translates by `γ = −zπ^s` (`residue z = t̄`... sign fixed in-file) onto

    deepBox s = {v₀ ≥ 2s+2, v₁ ≥ s+2, v₂ = 1, v₃ ≥ 1}

— the dd digit conditions `d₁ = 2t̄δ`, `d₀ = t̄²δ` kill the level-`(s+1)` and
level-`(2s+1)` digits under translation (pure digit arithmetic, any residue
characteristic).  `deepBox s` is EXACTLY the deep tail of IFCG53's own genre partition
(genres `a/b/c` at corner depths `> s`), so the decided count recurses into ITSELF:

    #(decided σ ∩ cBox s dd)   = (q−1) · #(decided σ ∩ deepBox s)          (fibration)
    #(decided σ ∩ deepBox s)   = E_σ(s) + (q−1)·Σ_{s'>s} #(… deepBox s') + Bd(s)

with `E_σ(s)` = IFCG53's LANDED exact genre counts over the shifted windows and
`0 ≤ Bd(s) ≤ q^(3K)`.  The first-order unroll (`tail_sum_geom`) yields

    #(decided σ ∩ e2DdBox) = (q−1)·Σ_{j<K/2} q^j·(E_σ(j+1) + Bd(j+1)),

the boundary sum is `O(q^(3K+K/2)) = o(q^(4K))` (eaten by `ZcURLim.sandwich`), and the
per-stratum swap turns the main term into differences of `q^(−2t)`/`q^(−3t)` geometric
sums (`tendsto_geom_sum_k`).

## The values (uniform in q; PARI battery p ∈ {2,3,5} × s ∈ {1,2,3} × N = 4000 ✓)

    dd-ram   = (q−1)²·[1/((q²−1)q⁸) − 1/((q³−1)q⁸)]      = (q−1)/(q⁶(q+1)(q²+q+1))
    dd-split = dd-inert                                   = (q−1)/(2q⁷(q+1)(q²+q+1))

σ-sum = the dd measure `(q−1)²/(q⁷(q³−1))` exactly; in-sector fractions
ram `q/(q+1)`, split = inert = `1/(2(q+1))`, s-independent.

## Consequences

The three `zcURLim_e2DdDecFam_*` fires make IFCG53's `zcURLim_e2DecFam_*` (all three)
and `zcURLim_e2DecFam_all` UNCONDITIONAL, close the mass-4 splitTail/inertTail
`ConeRemainderLaw` rows CITE-FREE (Lean core + B.42), drop the ramPair row to
`FactorCorrespondenceAt 2` alone (via IFCG51's `zcURLim_e1DdDecFam`), and rewire the
census front `decidedSliceAt_all` with the E2 legs GONE.

## Axiom fence

Lean core `{propext, Classical.choice, Quot.sound}` plus EXACTLY the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited
through IFCG53's decided counts — never re-consumed.  The FC-2-conditional §9 rows
additionally inherit nothing new (IFCG51's fires are Lean-core conditional).  The C.33
cites must NOT occur.  Zero sorries.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
-- the sector limit families must mirror `ZcURLim`'s binder list byte-for-byte
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG54

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG1 (shiftVecN shiftVecN_def monicPoly_shiftVecN
  typeOf_shiftVecN shiftVecN_zero shiftVecN_add shiftVecN_shiftVecN_neg
  dvd_pow_shiftVecN_sub proj_shiftVecN_congr shiftVecN_apply coeffShiftEquivN
  coeffShiftEquivN_proj card_image_coeffShiftEquivN)
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG22 (classCoeffVal_le)
open Uniformity.Density.IFCG24 (ZcURLim card_setOf_le_resOrd card_setOf_resOrd_eq
  ConeRemainderLaw)
open Uniformity.Density.IFCG31 (ramPairType)
open Uniformity.Density.IFCG34 (e2Box mem_e2Box_iff type22 type41
  splitTailType inertTailType e2DecFam E1IrrLeafDecision e1DdDecFam)
open Uniformity.Density.IFCG36 (resDig resDig_mk card_setOf_resDig resOrd_eq_iff_resDig
  irrPairs ddPairs card_irrPairs card_ddPairs irrPairs_snd_ne_zero
  two_mul_card_irredOfDeg_two)
open Uniformity.Density.IFCG53 (splitPairs aBox bBox cPair cBox bdBox e2DdBox
  splitPairs_snd_ne_zero ddPairs_snd_ne_zero
  pair_trichotomy disjoint_splitPairs_irrPairs disjoint_splitPairs_ddPairs
  disjoint_irrPairs_ddPairs decidedAt_aBox decidedAt_bBox decidedAt_cIrrBox
  decidedAt_cSplitBox typeOf_e2_mem decided_inter_e2_eq_empty_of_shape Ta Vb Sc
  mem_Ta mem_Vb mem_Sc e2DdBox_eq mem_genre_cases card_aBox card_bBox card_bdBox_le
  digTriples card_digTriples card_cBox e2DdDecFam ZcURLim.sandwich tendsto_geom_sum
  zcURLim_e2DecFam_ramPair zcURLim_e2DecFam_splitTail zcURLim_e2DecFam_inertTail
  zcURLim_e2DecFam_all coneRemainderLaw_four_ramPair_of_dd
  coneRemainderLaw_four_splitTail_of_dd coneRemainderLaw_four_inertTail_of_dd
  decidedSliceAt_all_of_dd_limits)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the deep tail box and the translation transport of decidedness -/

section DeepBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The deep tail box at corner depth `s`**: the translated image of the dd stratum —
`e2Box` with the corner pushed past `2s+1` and the middle valuation past `s+1`. -/
def deepBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K s : ℕ) : Set (Coeff O 4 K) :=
  {c | 2 * s + 2 ≤ resOrd (c 0) ∧ s + 2 ≤ resOrd (c 1)
    ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3)}

theorem deepBox_subset_e2Box {K s : ℕ} (hs : 1 ≤ s) : deepBox O K s ⊆ e2Box O K := by
  rintro c ⟨h0, h1, h2, h3⟩
  exact (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩

/-- Above the visible window the deep box is EMPTY (`resOrd` caps at `K`). -/
theorem deepBox_eq_empty {K s : ℕ} (h : K < 2 * s + 2) :
    deepBox O K s = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [deepBox, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h0, -, -, -⟩
  have := resOrd_le (c 0)
  omega

end DeepBox

section ShiftDecided

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

private theorem coeffShiftEquivN_neg_apply {n N : ℕ} (γ : O) (c : Coeff O n N) :
    coeffShiftEquivN (O := O) n N (-γ) (coeffShiftEquivN (O := O) n N γ c) = c :=
  (coeffShiftEquivN (O := O) n N γ).left_inv c

/-- **Translation preserves decidedness** (one direction; the iff follows by
inverting): every lift of the translated class is the translate of a lift. -/
theorem decidedAt_shiftClass {π : O} (hπ : Irreducible π) {n N : ℕ}
    {σ : FactorizationType} (γ : O) {c : Coeff O n N}
    (h : DecidedAt O n σ N c) :
    DecidedAt O n σ N (coeffShiftEquivN (O := O) n N γ c) := by
  intro b hb
  have h2 := coeffShiftEquivN_proj hπ (n := n) (N := N) (-γ) b
  rw [hb, coeffShiftEquivN_neg_apply] at h2
  exact (typeOf_shiftVecN b (-γ)).symm.trans (h _ h2.symm)

/-- **The decidedness transport iff** across the class translation. -/
theorem decidedAt_shiftClass_iff {π : O} (hπ : Irreducible π) {n N : ℕ}
    {σ : FactorizationType} (γ : O) (c : Coeff O n N) :
    DecidedAt O n σ N (coeffShiftEquivN (O := O) n N γ c) ↔ DecidedAt O n σ N c := by
  constructor
  · intro h
    have h2 := decidedAt_shiftClass hπ (-γ) h
    rwa [coeffShiftEquivN_neg_apply] at h2
  · exact decidedAt_shiftClass hπ γ

end ShiftDecided

/-! ## §1 — the box transport: the dd fiber at root parameter `t` translates onto
`deepBox s` (pure digit arithmetic, any residue characteristic) -/

section BoxTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

-- the explicit quartic shift coefficients (n = 4 instances of `shiftVecN_apply`);
-- the choose/Fin/cast normalization is deterministic, then `ring`
private theorem sv4_simp_kit : True := trivial

private theorem sv4_0 (a : Fin 4 → O) (γ : O) :
    shiftVecN a γ 0 = γ ^ 4 + (a 0 + a 1 * γ + a 2 * γ ^ 2 + a 3 * γ ^ 3) := by
  rw [shiftVecN_apply, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    show Nat.choose 4 0 = 1 from rfl, show Nat.choose 0 0 = 1 from rfl,
    show Nat.choose 1 0 = 1 from rfl, show Nat.choose 2 0 = 1 from rfl,
    show Nat.choose 3 0 = 1 from rfl, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
  ring

private theorem sv4_1 (a : Fin 4 → O) (γ : O) :
    shiftVecN a γ 1 = 4 * γ ^ 3 + (a 1 + 2 * a 2 * γ + 3 * a 3 * γ ^ 2) := by
  rw [shiftVecN_apply, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    show Nat.choose 4 1 = 4 from rfl, show Nat.choose 0 1 = 0 from rfl,
    show Nat.choose 1 1 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl,
    show Nat.choose 3 1 = 3 from rfl, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
  ring

private theorem sv4_2 (a : Fin 4 → O) (γ : O) :
    shiftVecN a γ 2 = 6 * γ ^ 2 + (a 2 + 3 * a 3 * γ) := by
  rw [shiftVecN_apply, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    show Nat.choose 4 2 = 6 from rfl, show Nat.choose 0 2 = 0 from rfl,
    show Nat.choose 1 2 = 0 from rfl, show Nat.choose 2 2 = 1 from rfl,
    show Nat.choose 3 2 = 3 from rfl, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
  ring

private theorem sv4_3 (a : Fin 4 → O) (γ : O) :
    shiftVecN a γ 3 = 4 * γ + a 3 := by
  rw [shiftVecN_apply, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    show Nat.choose 4 3 = 4 from rfl, show Nat.choose 0 3 = 0 from rfl,
    show Nat.choose 1 3 = 0 from rfl, show Nat.choose 2 3 = 0 from rfl,
    show Nat.choose 3 3 = 1 from rfl, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat]
  ring

variable {π : O}

private theorem residue_pi_eq_zero (hπ : Irreducible π) : residue O π = 0 :=
  (IsLocalRing.residue_eq_zero_iff π).2
    ((IsLocalRing.mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit))

private theorem dvd_of_residue_eq_zero (hπ : Irreducible π) {x : O}
    (hx : residue O x = 0) : π ∣ x := by
  have h1 := (IsLocalRing.residue_eq_zero_iff x).1 hx
  rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1

private theorem proj_apply {n N : ℕ} (a : Fin n → O) (i : Fin n) :
    proj O n N a i = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a i) := rfl

/-- ★ **The forward box transport**: a dd-fiber class at corner depth `s` (residual
pair `(t+t, t·t)`, i.e. residual `(Y+t̄)²`) translates by `γ = −uπ^s` (`residue u = t`)
into the deep tail box — the dd digit conditions kill the two pinned digits. -/
theorem shift_mem_deepBox (hπ : Irreducible π) {K s : ℕ} (hs : 1 ≤ s)
    (hsK : 2 * s + 2 ≤ K) {t : ResidueField O} {u : O} (hu : residue O u = t)
    {c : Coeff O 4 K}
    (hc : c ∈ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O))) :
    coeffShiftEquivN (O := O) 4 K (-(u * π ^ s)) c ∈ deepBox O K s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3, hp⟩ := hc
  set δ := resDig π 1 (c 2) with hδdef
  have hδ : δ ≠ 0 := ((resOrd_eq_iff_resDig hπ (by omega) (c 2)).1 h2).2
  have hp' : cPair π (s' + 1) c = (t + t, t * t) := Set.mem_singleton_iff.1 hp
  have hd1 : resDig π (s' + 2) (c 1) = (t + t) * δ := by
    have h := congrArg Prod.fst hp'
    simp only [cPair] at h
    rw [show s' + 2 = s' + 1 + 1 from by omega]
    exact (div_eq_iff hδ).1 h
  have hd0 : resDig π (2 * s' + 3) (c 0) = (t * t) * δ := by
    have h := congrArg Prod.snd hp'
    simp only [cPair] at h
    rw [show 2 * s' + 3 = 2 * (s' + 1) + 1 from by omega]
    exact (div_eq_iff hδ).1 h
  -- lift and decompose
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  have hci : ∀ i : Fin 4, c i = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a i) := by
    intro i
    rw [← ha]
    rfl
  obtain ⟨w0, hw0⟩ : π ^ (2 * s' + 3) ∣ a 0 := by
    rw [← resOrd_ge_iff hπ (by omega : 2 * s' + 3 ≤ K) (a 0), ← hci 0]
    omega
  obtain ⟨w1, hw1⟩ : π ^ (s' + 2) ∣ a 1 := by
    rw [← resOrd_ge_iff hπ (by omega : s' + 2 ≤ K) (a 1), ← hci 1]
    omega
  obtain ⟨w2, hw2⟩ : π ^ 1 ∣ a 2 := by
    rw [← resOrd_ge_iff hπ (by omega : 1 ≤ K) (a 2), ← hci 2]
    omega
  obtain ⟨w3, hw3⟩ : π ^ 1 ∣ a 3 := by
    rw [← resOrd_ge_iff hπ (by omega : 1 ≤ K) (a 3), ← hci 3]
    omega
  -- the residues of the visible cofactors
  have hrw0 : residue O w0 = (t * t) * δ := by
    rw [← hd0, hci 0, resDig_mk hπ (by omega) (a 0), digAt_eq hπ hw0]
  have hrw1 : residue O w1 = (t + t) * δ := by
    rw [← hd1, hci 1, resDig_mk hπ (by omega) (a 1), digAt_eq hπ hw1]
  have hrw2 : residue O w2 = δ := by
    rw [hδdef, hci 2, resDig_mk hπ (by omega) (a 2), digAt_eq hπ hw2]
  -- the shifted class computes on the shifted lift
  have hshift : coeffShiftEquivN (O := O) 4 K (-(u * π ^ (s' + 1))) c
      = proj O 4 K (shiftVecN a (-(u * π ^ (s' + 1)))) := by
    rw [← ha, coeffShiftEquivN_proj hπ]
  rw [hshift]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- corner: `2s+2 ≤ v₀` — the dd condition kills the level-(2s+1) digit
    rw [proj_apply, resOrd_ge_iff hπ (by omega : 2 * (s' + 1) + 2 ≤ K)]
    have hb0 : shiftVecN a (-(u * π ^ (s' + 1))) 0
        = π ^ (2 * s' + 3) * (w0 - w1 * u + w2 * u ^ 2)
          + (π ^ (3 * s' + 4) * (-(w3 * u ^ 3)) + π ^ (4 * s' + 4) * u ^ 4) := by
      rw [sv4_0, hw0, hw1, hw2, hw3]
      ring
    have hres : residue O (w0 - w1 * u + w2 * u ^ 2) = 0 := by
      rw [map_add, map_sub, map_mul, map_mul, map_pow, hrw0, hrw1, hrw2, hu]
      ring
    obtain ⟨v0, hv0⟩ := dvd_of_residue_eq_zero hπ hres
    rw [show 2 * (s' + 1) + 2 = 2 * s' + 4 from by omega, hb0, hv0]
    exact ⟨v0 + (π ^ s' * (-(w3 * u ^ 3)) + π ^ (2 * s') * u ^ 4), by ring⟩
  · -- middle: `s+2 ≤ v₁` — the dd condition kills the level-(s+1) digit
    rw [proj_apply, resOrd_ge_iff hπ (by omega : s' + 1 + 2 ≤ K)]
    have hb1 : shiftVecN a (-(u * π ^ (s' + 1))) 1
        = π ^ (s' + 2) * (w1 - 2 * w2 * u)
          + (π ^ (2 * s' + 3) * (3 * w3 * u ^ 2) + π ^ (3 * s' + 3) * (-(4 * u ^ 3))) := by
      rw [sv4_1, hw1, hw2, hw3]
      ring
    have hres : residue O (w1 - 2 * w2 * u) = 0 := by
      rw [map_sub, map_mul, map_mul, map_ofNat, hrw1, hrw2, hu]
      ring
    obtain ⟨v1, hv1⟩ := dvd_of_residue_eq_zero hπ hres
    rw [show s' + 1 + 2 = s' + 3 from by omega, hb1, hv1]
    exact ⟨v1 + (π ^ s' * (3 * w3 * u ^ 2) + π ^ (2 * s') * (-(4 * u ^ 3))), by ring⟩
  · -- `v₂ = 1` exactly, with digit δ preserved
    rw [proj_apply]
    have hb2 : shiftVecN a (-(u * π ^ (s' + 1))) 2
        = π ^ 1 * (w2 + π * (π ^ s' * (-(3 * w3 * u)) + π ^ (2 * s') * (6 * u ^ 2))) := by
      rw [sv4_2, hw2, hw3]
      ring
    rw [resOrd_eq_iff_resDig hπ (by omega : 1 < K)]
    constructor
    · rw [resOrd_ge_iff hπ (by omega : 1 ≤ K), hb2]
      exact Dvd.intro _ rfl
    · rw [resDig_mk hπ (by omega : 1 < K), digAt_eq hπ hb2, map_add, map_mul,
        residue_pi_eq_zero hπ, hrw2, zero_mul, add_zero]
      exact hδ
  · -- `1 ≤ v₃`
    rw [proj_apply, resOrd_ge_iff hπ (by omega : 1 ≤ K)]
    have hb3 : shiftVecN a (-(u * π ^ (s' + 1))) 3
        = π ^ 1 * (w3 + π ^ s' * (-(4 * u))) := by
      rw [sv4_3, hw3]
      ring
    rw [hb3]
    exact Dvd.intro _ rfl

/-- ★ **The backward box transport**: a deep-tail class translates by `γ = +uπ^s`
(`residue u = t ≠ 0`) into the dd fiber at root parameter `t` — the two pinned digits
reappear as `(t+t)·δ` and `(t·t)·δ`, the corner is EXACT (`t²δ ≠ 0`). -/
theorem shift_mem_ddFiber (hπ : Irreducible π) {K s : ℕ} (hs : 1 ≤ s)
    (hsK : 2 * s + 2 ≤ K) {t : ResidueField O} (ht : t ≠ 0) {u : O}
    (hu : residue O u = t) {c : Coeff O 4 K} (hc : c ∈ deepBox O K s) :
    coeffShiftEquivN (O := O) 4 K (u * π ^ s) c
      ∈ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O)) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := hc
  set δ := resDig π 1 (c 2) with hδdef
  have hδ : δ ≠ 0 := ((resOrd_eq_iff_resDig hπ (by omega) (c 2)).1 h2).2
  -- lift and decompose
  obtain ⟨b, hb⟩ := proj_surjective O 4 K c
  have hci : ∀ i : Fin 4, c i = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (b i) := by
    intro i
    rw [← hb]
    rfl
  obtain ⟨v0, hv0⟩ : π ^ (2 * s' + 4) ∣ b 0 := by
    rw [← resOrd_ge_iff hπ (by omega : 2 * s' + 4 ≤ K) (b 0), ← hci 0]
    omega
  obtain ⟨v1, hv1⟩ : π ^ (s' + 3) ∣ b 1 := by
    rw [← resOrd_ge_iff hπ (by omega : s' + 3 ≤ K) (b 1), ← hci 1]
    omega
  obtain ⟨v2, hv2⟩ : π ^ 1 ∣ b 2 := by
    rw [← resOrd_ge_iff hπ (by omega : 1 ≤ K) (b 2), ← hci 2]
    omega
  obtain ⟨v3, hv3⟩ : π ^ 1 ∣ b 3 := by
    rw [← resOrd_ge_iff hπ (by omega : 1 ≤ K) (b 3), ← hci 3]
    omega
  have hrv2 : residue O v2 = δ := by
    rw [hδdef, hci 2, resDig_mk hπ (by omega) (b 2), digAt_eq hπ hv2]
  -- the shifted class computes on the shifted lift
  have hshift : coeffShiftEquivN (O := O) 4 K (u * π ^ (s' + 1)) c
      = proj O 4 K (shiftVecN b (u * π ^ (s' + 1))) := by
    rw [← hb, coeffShiftEquivN_proj hπ]
  -- the four decompositions of the shifted lift
  have ha0 : shiftVecN b (u * π ^ (s' + 1)) 0
      = π ^ (2 * s' + 3) * (v2 * u ^ 2
          + (π * (v0 * π ^ 0) + π * (v1 * u) + π ^ (s' + 1) * (v3 * u ^ 3)
            + π ^ (2 * s' + 1) * u ^ 4)) := by
    rw [sv4_0, hv0, hv1, hv2, hv3]
    ring
  have ha1 : shiftVecN b (u * π ^ (s' + 1)) 1
      = π ^ (s' + 2) * ((v2 * u + v2 * u)
          + (π * v1 + π ^ (s' + 1) * (3 * v3 * u ^ 2) + π ^ (2 * s' + 1) * (4 * u ^ 3))) := by
    rw [sv4_1, hv1, hv2, hv3]
    ring
  have ha2 : shiftVecN b (u * π ^ (s' + 1)) 2
      = π ^ 1 * (v2 + π * (π ^ s' * (3 * v3 * u) + π ^ (2 * s') * (6 * u ^ 2))) := by
    rw [sv4_2, hv2, hv3]
    ring
  have ha3 : shiftVecN b (u * π ^ (s' + 1)) 3
      = π ^ 1 * (v3 + π ^ s' * (4 * u)) := by
    rw [sv4_3, hv3]
    ring
  -- the two reborn digits
  have hres0 : residue O (v2 * u ^ 2
      + (π * (v0 * π ^ 0) + π * (v1 * u) + π ^ (s' + 1) * (v3 * u ^ 3)
        + π ^ (2 * s' + 1) * u ^ 4)) = (t * t) * δ := by
    simp only [map_add, map_mul, map_pow, hrv2, hu, residue_pi_eq_zero hπ]
    ring
  have hres1 : residue O ((v2 * u + v2 * u)
      + (π * v1 + π ^ (s' + 1) * (3 * v3 * u ^ 2) + π ^ (2 * s' + 1) * (4 * u ^ 3)))
      = (t + t) * δ := by
    simp only [map_add, map_mul, map_pow, map_ofNat, hrv2, hu, residue_pi_eq_zero hπ]
    ring
  have hres2 : residue O (v2 + π * (π ^ s' * (3 * v3 * u) + π ^ (2 * s') * (6 * u ^ 2)))
      = δ := by
    rw [map_add, map_mul, residue_pi_eq_zero hπ, hrv2, zero_mul, add_zero]
  rw [hshift]
  -- the three class digit facts
  have hD0 : resDig π (2 * s' + 3) (proj O 4 K (shiftVecN b (u * π ^ (s' + 1))) 0)
      = (t * t) * δ := by
    rw [proj_apply, resDig_mk hπ (by omega : 2 * s' + 3 < K), digAt_eq hπ ha0, hres0]
  have hD1 : resDig π (s' + 2) (proj O 4 K (shiftVecN b (u * π ^ (s' + 1))) 1)
      = (t + t) * δ := by
    rw [proj_apply, resDig_mk hπ (by omega : s' + 2 < K), digAt_eq hπ ha1, hres1]
  have hD2 : resDig π 1 (proj O 4 K (shiftVecN b (u * π ^ (s' + 1))) 2) = δ := by
    rw [proj_apply, resDig_mk hπ (by omega : 1 < K), digAt_eq hπ ha2, hres2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- corner EXACT: `v₀ = 2s+1`, digit `t²δ ≠ 0`
    rw [proj_apply, show 2 * (s' + 1) + 1 = 2 * s' + 3 from by omega,
      resOrd_eq_iff_resDig hπ (by omega : 2 * s' + 3 < K)]
    constructor
    · rw [resOrd_ge_iff hπ (by omega : 2 * s' + 3 ≤ K), ha0]
      exact Dvd.intro _ rfl
    · rw [resDig_mk hπ (by omega : 2 * s' + 3 < K), digAt_eq hπ ha0, hres0]
      exact mul_ne_zero (mul_ne_zero ht ht) hδ
  · -- middle: `s+1 ≤ v₁`
    rw [proj_apply, resOrd_ge_iff hπ (by omega : s' + 1 + 1 ≤ K), ha1,
      show s' + 1 + 1 = s' + 2 from by omega]
    exact Dvd.intro _ rfl
  · -- `v₂ = 1` exactly
    rw [proj_apply, resOrd_eq_iff_resDig hπ (by omega : 1 < K)]
    constructor
    · rw [resOrd_ge_iff hπ (by omega : 1 ≤ K), ha2]
      exact Dvd.intro _ rfl
    · rw [resDig_mk hπ (by omega : 1 < K), digAt_eq hπ ha2, hres2]
      exact hδ
  · -- `1 ≤ v₃`
    rw [proj_apply, resOrd_ge_iff hπ (by omega : 1 ≤ K), ha3]
    exact Dvd.intro _ rfl
  · -- the residual pair is `(t+t, t·t)`
    rw [Set.mem_singleton_iff]
    simp only [cPair]
    rw [show s' + 1 + 1 = s' + 2 from by omega,
      show 2 * (s' + 1) + 1 = 2 * s' + 3 from by omega, hD0, hD1, hD2,
      mul_div_cancel_right₀ _ hδ, mul_div_cancel_right₀ _ hδ]

end BoxTransport

/-! ## §2 — the root fibration: `#(decided ∩ cBox s dd) = (q−1) · #(decided ∩ deepBox s)` -/

section Fibration

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- The dd pairs are exactly the `(t+t, t·t)` with `t ≠ 0` (root parametrization,
char-free). -/
theorem mem_ddPairs_iff {F : Type*} [Field F] {p : F × F} :
    p ∈ ddPairs F ↔ ∃ t : F, t ≠ 0 ∧ p = (t + t, t * t) := by
  constructor
  · rintro ⟨hp2, L, hLm, hLd, hLe⟩
    obtain ⟨l, rfl⟩ : ∃ l, L = X + Polynomial.C l := ⟨L.coeff 0, hLm.eq_X_add_C hLd⟩
    have hsq : (X + Polynomial.C l : Polynomial F) ^ 2
        = X ^ 2 + Polynomial.C (l + l) * X + Polynomial.C (l * l) := by
      rw [Polynomial.C_add, Polynomial.C_mul]
      ring
    rw [hsq] at hLe
    have h1 : p.1 = l + l := by
      have := congrArg (fun G => Polynomial.coeff G 1) hLe
      simpa using this
    have h0 : p.2 = l * l := by
      have := congrArg (fun G => Polynomial.coeff G 0) hLe
      simpa using this
    have hl : l ≠ 0 := by
      intro h
      rw [h, mul_zero] at h0
      exact hp2 h0
    exact ⟨l, hl, Prod.ext h1 h0⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨mul_ne_zero ht ht, X + Polynomial.C t, Polynomial.monic_X_add_C t,
      Polynomial.natDegree_X_add_C t, ?_⟩
    rw [Polynomial.C_add, Polynomial.C_mul]
    ring

/-- The root parameter is unique (char-free: `(t−t')² = t·t − (t+t)·t' + t'·t'`). -/
theorem dd_root_unique {F : Type*} [Field F] {t t' : F}
    (h1 : t + t = t' + t') (h0 : t * t = t' * t') : t = t' := by
  have hsq : (t - t') ^ 2 = t * t - (t + t) * t' + t' * t' := by ring
  rw [h1, h0] at hsq
  have hz : (t - t') ^ 2 = 0 := by rw [hsq]; ring
  have := pow_eq_zero_iff (n := 2) (by omega) |>.1 hz
  exact sub_eq_zero.1 this

-- IFCG51/53's private biUnion counter, reproduced (the sanctioned replay).
private theorem ncard_biUnion_eq {α ι : Type*} [Finite α] (s : Finset ι)
    (f : ι → Set α)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hcons : (⋃ i ∈ Finset.cons a s ha, f i) = f a ∪ ⋃ i ∈ s, f i := by
        ext x
        simp [Finset.mem_cons, or_and_right, Set.mem_iUnion]
      have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
        rw [Set.disjoint_right]
        intro x hx hxa
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
        exact (Set.disjoint_left.1 (hdisj a (Finset.mem_cons_self a s) i
          (Finset.mem_cons_of_mem hi) (by rintro rfl; exact ha hi))) hxa hxi
      rw [hcons, Set.ncard_union_eq hd, Finset.sum_cons,
        ih (fun i hi j hj hij => hdisj i (Finset.mem_cons_of_mem hi) j
          (Finset.mem_cons_of_mem hj) hij)]

/-- ★ **The per-fiber count**: the decided part of the root-`t` dd fiber has EXACTLY
the decided-deepBox count — the translation bijection in counting form. -/
theorem card_decided_ddFiber (hπ : Irreducible π) {K s : ℕ} (hs : 1 ≤ s)
    (hsK : 2 * s + 2 ≤ K) (σ : FactorizationType) {t : ResidueField O} (ht : t ≠ 0) :
    Nat.card ((decidedSet O 4 σ K
        ∩ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O)))
        : Set (Coeff O 4 K))
      = Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s) : Set (Coeff O 4 K)) := by
  obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective (R := O) t
  have himg : coeffShiftEquivN (O := O) 4 K (-(u * π ^ s))
      '' (decidedSet O 4 σ K ∩ cBox π K s {(t + t, t * t)})
      = decidedSet O 4 σ K ∩ deepBox O K s := by
    ext x
    constructor
    · rintro ⟨c, ⟨hdec, hbox⟩, rfl⟩
      exact ⟨decidedAt_shiftClass hπ _ hdec, shift_mem_deepBox hπ hs hsK hu hbox⟩
    · rintro ⟨hdec, hbox⟩
      refine ⟨coeffShiftEquivN (O := O) 4 K (u * π ^ s) x,
        ⟨decidedAt_shiftClass hπ _ hdec, shift_mem_ddFiber hπ hs hsK ht hu hbox⟩, ?_⟩
      exact coeffShiftEquivN_neg_apply (u * π ^ s) x
  rw [← himg, card_image_coeffShiftEquivN]

/-- The decided dd stratum splits into the root fibers. -/
private theorem decided_dd_eq_biUnion (_hπ : Irreducible π) {K s : ℕ}
    (σ : FactorizationType) :
    letI : Fintype (ResidueField O) := Fintype.ofFinite _
    decidedSet O 4 σ K ∩ cBox π K s (ddPairs (ResidueField O))
      = ⋃ t ∈ Finset.univ.filter (fun t : ResidueField O => t ≠ 0),
          (decidedSet O 4 σ K
            ∩ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O))) := by
  letI : Fintype (ResidueField O) := Fintype.ofFinite _
  ext c
  constructor
  · rintro ⟨hdec, h0, h1, h2, h3, hp⟩
    obtain ⟨t, ht, hpt⟩ := mem_ddPairs_iff.1 hp
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_univ t, ht⟩)
      ⟨hdec, h0, h1, h2, h3, by rw [hpt]; exact rfl⟩
  · intro hc
    obtain ⟨t, htmem, hdec, h0, h1, h2, h3, hp⟩ := Set.mem_iUnion₂.1 hc
    have ht := (Finset.mem_filter.1 htmem).2
    exact ⟨hdec, h0, h1, h2, h3, mem_ddPairs_iff.2 ⟨t, ht, Set.mem_singleton_iff.1 hp⟩⟩

/-- ★★ **THE STRATUM FIBRATION COUNT**:
`#(decided σ ∩ cBox s dd) = (q−1)·#(decided σ ∩ deepBox s)`. -/
theorem card_decided_dd_stratum (hπ : Irreducible π) {K s : ℕ} (hs : 1 ≤ s)
    (hsK : 2 * s + 2 ≤ K) (σ : FactorizationType) :
    Nat.card ((decidedSet O 4 σ K ∩ cBox π K s (ddPairs (ResidueField O)))
        : Set (Coeff O 4 K))
      = (residueCard O - 1)
        * Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s) : Set (Coeff O 4 K)) := by
  letI : Fintype (ResidueField O) := Fintype.ofFinite _
  have hdisj : ∀ t ∈ Finset.univ.filter (fun t : ResidueField O => t ≠ 0),
      ∀ t' ∈ Finset.univ.filter (fun t : ResidueField O => t ≠ 0), t ≠ t' →
      Disjoint (decidedSet O 4 σ K
          ∩ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O)))
        (decidedSet O 4 σ K
          ∩ cBox π K s ({(t' + t', t' * t')}
            : Set (ResidueField O × ResidueField O))) := by
    intro t _ t' _ htt'
    rw [Set.disjoint_left]
    rintro c ⟨-, -, -, -, -, hp⟩ ⟨-, -, -, -, -, hp'⟩
    have h1 := Set.mem_singleton_iff.1 hp
    have h2 := Set.mem_singleton_iff.1 hp'
    rw [h1] at h2
    exact htt' (dd_root_unique (congrArg Prod.fst h2) (congrArg Prod.snd h2))
  have hcard : Nat.card ((decidedSet O 4 σ K ∩ cBox π K s (ddPairs (ResidueField O)))
      : Set (Coeff O 4 K))
      = ∑ t ∈ Finset.univ.filter (fun t : ResidueField O => t ≠ 0),
          Nat.card ((decidedSet O 4 σ K
            ∩ cBox π K s ({(t + t, t * t)} : Set (ResidueField O × ResidueField O)))
            : Set (Coeff O 4 K)) := by
    rw [Nat.card_coe_set_eq, decided_dd_eq_biUnion hπ σ, ncard_biUnion_eq _ _ hdisj]
    exact Finset.sum_congr rfl fun t _ => (Nat.card_coe_set_eq _).symm
  rw [hcard, Finset.sum_congr rfl (fun t htmem =>
    card_decided_ddFiber hπ hs hsK σ (Finset.mem_filter.1 htmem).2),
    Finset.sum_const, smul_eq_mul]
  congr 1
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  show Fintype.card (ResidueField O) - 1 = Nat.card (ResidueField O) - 1
  rw [Nat.card_eq_fintype_card]

end Fibration

/-! ## §3 — the self-similar partition: `decided σ ∩ deepBox s` re-partitions into
IFCG53's genre strata at depths `> s`, the dd part recursing through the fibration -/

section Partition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {π : O}

-- IFCG53's private type-inequality kit, reproduced (the sanctioned replay).
private theorem ne_of_data_ne {σ τ : FactorizationType} (h : σ.data ≠ τ.data) :
    σ ≠ τ := fun he => h (by rw [he])

private theorem ramPair_ne_splitTail : ramPairType ≠ splitTailType :=
  ne_of_data_ne (by decide)

private theorem ramPair_ne_inertTail : ramPairType ≠ inertTailType :=
  ne_of_data_ne (by decide)

private theorem splitTail_ne_inertTail : splitTailType ≠ inertTailType :=
  ne_of_data_ne (by decide)

-- IFCG53's private pairwise disjointness lemmas, reproduced (the sanctioned replay).
private theorem aBox_pairwise {K : ℕ} {S : Finset ℕ} (_hS : S ⊆ Ta K) :
    ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → Disjoint (aBox O K t) (aBox O K t') := by
  intro t _ t' _ hne
  rw [Set.disjoint_left]
  rintro c ⟨h0, -, -, -⟩ ⟨h0', -, -, -⟩
  exact hne (by omega)

private theorem cBox_dd_dec_pairwise {K : ℕ} (σ : FactorizationType) {S : Finset ℕ} :
    ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
    Disjoint (decidedSet O 4 σ K ∩ cBox π K s (ddPairs (ResidueField O)))
      (decidedSet O 4 σ K ∩ cBox π K s' (ddPairs (ResidueField O))) := by
  intro s _ s' _ hne
  rw [Set.disjoint_left]
  rintro c ⟨-, h0, -, -, -, -⟩ ⟨-, h0', -, -, -, -⟩
  exact hne (by omega)

/-- The dd strata at depths `> s` sit inside `deepBox s`. -/
private theorem cBox_dd_subset_deepBox {K s s' : ℕ} (hss' : s + 1 ≤ s')
    {P : Set (ResidueField O × ResidueField O)} :
    cBox π K s' P ⊆ deepBox O K s := by
  rintro c ⟨h0, h1, h2, h3, -⟩
  exact ⟨by omega, by omega, h2, h3⟩

/-- ★ **The ramPair deepBox identity**: genre (a) at depths `> s`, the dd recursion at
depths `> s`, and the boundary sliver. -/
private theorem decided_ramPair_inter_deepBox {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    decidedSet O 4 ramPairType K ∩ deepBox O K s
      = (⋃ t ∈ (Ta K).filter (fun t => s + 1 ≤ t), aBox O K t)
        ∪ ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
              (decidedSet O 4 ramPairType K ∩ cBox π K s' (ddPairs (ResidueField O))))
          ∪ (decidedSet O 4 ramPairType K ∩ deepBox O K s ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hdeep⟩
    obtain ⟨h0, h1, h2, h3⟩ := hdeep
    rcases mem_genre_cases hK hπ (deepBox_subset_e2Box hs ⟨h0, h1, h2, h3⟩) with
      ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s', hs', hC⟩ | ⟨s', hs', hC⟩ | hD | hBd
    · refine Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨ht, ?_⟩) hA)
      obtain ⟨hA0, -, -, -⟩ := hA
      omega
    · exact absurd (decidedAt_unique hdec
        (decidedAt_bBox hK hπ (mem_Vb.1 hv).1 (mem_Vb.1 hv).2 hB)) ramPair_ne_splitTail
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cSplitBox hK hπ (mem_Sc.1 hs').1 (mem_Sc.1 hs').2 hC))
        ramPair_ne_splitTail
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cIrrBox hK hπ (mem_Sc.1 hs').1 (mem_Sc.1 hs').2 hC))
        ramPair_ne_inertTail
    · rw [e2DdBox_eq] at hD
      obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hD
      refine Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hs', ?_⟩)
        ⟨hdec, hC⟩))
      obtain ⟨hC0, -, -, -, -⟩ := hC
      omega
    · exact Or.inr (Or.inr ⟨⟨hdec, h0, h1, h2, h3⟩, hBd⟩)
  · rintro (hA | hDd | hBd)
    · obtain ⟨t, ht, hA'⟩ := Set.mem_iUnion₂.1 hA
      obtain ⟨htT, hts⟩ := Finset.mem_filter.1 ht
      refine ⟨decidedAt_aBox hK hπ (mem_Ta.1 htT).1 (mem_Ta.1 htT).2 hA', ?_⟩
      obtain ⟨hA0, hA1, hA2, hA3⟩ := hA'
      exact ⟨by omega, by omega, hA2, hA3⟩
    · obtain ⟨s', hs', hdec, hC⟩ := Set.mem_iUnion₂.1 hDd
      exact ⟨hdec, cBox_dd_subset_deepBox (Finset.mem_filter.1 hs').2 hC⟩
    · exact ⟨hBd.1.1, hBd.1.2⟩

/-- ★★ **The ramPair deepBox count recursion**. -/
private theorem card_decided_deepBox_ramPair {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    Nat.card ((decidedSet O 4 ramPairType K ∩ deepBox O K s) : Set (Coeff O 4 K))
      = (∑ t ∈ (Ta K).filter (fun t => s + 1 ≤ t),
            Nat.card (aBox O K t : Set (Coeff O 4 K)))
        + ((residueCard O - 1)
            * (∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
                Nat.card ((decidedSet O 4 ramPairType K ∩ deepBox O K s')
                  : Set (Coeff O 4 K)))
          + Nat.card ((decidedSet O 4 ramPairType K ∩ deepBox O K s ∩ bdBox O K)
              : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
      (decidedSet O 4 ramPairType K ∩ cBox π K s' (ddPairs (ResidueField O))))
      (decidedSet O 4 ramPairType K ∩ deepBox O K s ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    intro c hcD hcBd
    obtain ⟨s', hs', -, hC⟩ := Set.mem_iUnion₂.1 hcD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hcBd.2
    have := (mem_Sc.1 (Finset.mem_filter.1 hs').1).2
    omega
  have hd1 : Disjoint (⋃ t ∈ (Ta K).filter (fun t => s + 1 ≤ t), aBox O K t)
      ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
          (decidedSet O 4 ramPairType K ∩ cBox π K s' (ddPairs (ResidueField O))))
        ∪ (decidedSet O 4 ramPairType K ∩ deepBox O K s ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcA hcX
    obtain ⟨t, ht, hA⟩ := Set.mem_iUnion₂.1 hcA
    obtain ⟨h0, -, -, -⟩ := hA
    rcases hcX with hD | hBd
    · obtain ⟨s', hs', -, hC⟩ := Set.mem_iUnion₂.1 hD
      obtain ⟨h0', -, -, -, -⟩ := hC
      omega
    · obtain ⟨h0', -, -, -⟩ := hBd.2
      have := (mem_Ta.1 (Finset.mem_filter.1 ht).1).2
      omega
  conv_lhs => rw [decided_ramPair_inter_deepBox hK hπ hs]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2,
    ncard_biUnion_eq _ _ (aBox_pairwise (Finset.filter_subset _ _)),
    ncard_biUnion_eq _ _ (fun i hi j hj hij => cBox_dd_dec_pairwise ramPairType i hi j hj hij)]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' hs' => ?_
  have hmem := mem_Sc.1 (Finset.mem_filter.1 hs').1
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    card_decided_dd_stratum hπ hmem.1 (by omega) ramPairType]

private theorem bBox_pairwise' {K : ℕ} :
    ∀ (v v' : ℕ), v ≠ v' → Disjoint (bBox O K v) (bBox O K v') := by
  intro v v' hne
  rw [Set.disjoint_left]
  rintro c ⟨-, h1, -, -⟩ ⟨-, h1', -, -⟩
  exact hne (by omega)

private theorem cBox_pairwise' {K : ℕ}
    {P P' : Set (ResidueField O × ResidueField O)} :
    ∀ (s s' : ℕ), s ≠ s' → Disjoint (cBox π K s P) (cBox π K s' P') := by
  intro s s' hne
  rw [Set.disjoint_left]
  rintro c ⟨h0, -, -, -, -⟩ ⟨h0', -, -, -, -⟩
  exact hne (by omega)

/-- ★ **The splitTail deepBox identity**: genres (b) and (c)-split at depths `> s`,
the dd recursion, and the boundary sliver. -/
private theorem decided_splitTail_inter_deepBox {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    decidedSet O 4 splitTailType K ∩ deepBox O K s
      = ((⋃ v ∈ (Vb K).filter (fun v => s + 2 ≤ v), bBox O K v)
          ∪ ⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
              cBox π K s' (splitPairs (ResidueField O)))
        ∪ ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
              (decidedSet O 4 splitTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
          ∪ (decidedSet O 4 splitTailType K ∩ deepBox O K s ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hdeep⟩
    obtain ⟨h0, h1, h2, h3⟩ := hdeep
    rcases mem_genre_cases hK hπ (deepBox_subset_e2Box hs ⟨h0, h1, h2, h3⟩) with
      ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s', hs', hC⟩ | ⟨s', hs', hC⟩ | hD | hBd
    · exact absurd (decidedAt_unique hdec
        (decidedAt_aBox hK hπ (mem_Ta.1 ht).1 (mem_Ta.1 ht).2 hA))
        ramPair_ne_splitTail.symm
    · refine Or.inl (Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hv, ?_⟩) hB))
      obtain ⟨-, hB1, -, -⟩ := hB
      omega
    · refine Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_filter.2 ⟨hs', ?_⟩) hC))
      obtain ⟨hC0, -, -, -, -⟩ := hC
      omega
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cIrrBox hK hπ (mem_Sc.1 hs').1 (mem_Sc.1 hs').2 hC))
        splitTail_ne_inertTail
    · rw [e2DdBox_eq] at hD
      obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hD
      refine Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hs', ?_⟩)
        ⟨hdec, hC⟩))
      obtain ⟨hC0, -, -, -, -⟩ := hC
      omega
    · exact Or.inr (Or.inr ⟨⟨hdec, h0, h1, h2, h3⟩, hBd⟩)
  · rintro ((hB | hC) | hDd | hBd)
    · obtain ⟨v, hv, hB'⟩ := Set.mem_iUnion₂.1 hB
      obtain ⟨hvV, hvs⟩ := Finset.mem_filter.1 hv
      refine ⟨decidedAt_bBox hK hπ (mem_Vb.1 hvV).1 (mem_Vb.1 hvV).2 hB', ?_⟩
      obtain ⟨hB0, hB1, hB2, hB3⟩ := hB'
      exact ⟨by omega, by omega, hB2, hB3⟩
    · obtain ⟨s', hs', hC'⟩ := Set.mem_iUnion₂.1 hC
      obtain ⟨hsS, hss⟩ := Finset.mem_filter.1 hs'
      exact ⟨decidedAt_cSplitBox hK hπ (mem_Sc.1 hsS).1 (mem_Sc.1 hsS).2 hC',
        cBox_dd_subset_deepBox hss hC'⟩
    · obtain ⟨s', hs', hdec, hC⟩ := Set.mem_iUnion₂.1 hDd
      exact ⟨hdec, cBox_dd_subset_deepBox (Finset.mem_filter.1 hs').2 hC⟩
    · exact ⟨hBd.1.1, hBd.1.2⟩

/-- ★★ **The splitTail deepBox count recursion**. -/
private theorem card_decided_deepBox_splitTail {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    Nat.card ((decidedSet O 4 splitTailType K ∩ deepBox O K s) : Set (Coeff O 4 K))
      = ((∑ v ∈ (Vb K).filter (fun v => s + 2 ≤ v),
            Nat.card (bBox O K v : Set (Coeff O 4 K)))
          + ∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
              Nat.card ((cBox π K s' (splitPairs (ResidueField O))) : Set (Coeff O 4 K)))
        + ((residueCard O - 1)
            * (∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
                Nat.card ((decidedSet O 4 splitTailType K ∩ deepBox O K s')
                  : Set (Coeff O 4 K)))
          + Nat.card ((decidedSet O 4 splitTailType K ∩ deepBox O K s ∩ bdBox O K)
              : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
      (decidedSet O 4 splitTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
      (decidedSet O 4 splitTailType K ∩ deepBox O K s ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    intro c hcD hcBd
    obtain ⟨s', hs', -, hC⟩ := Set.mem_iUnion₂.1 hcD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hcBd.2
    have := (mem_Sc.1 (Finset.mem_filter.1 hs').1).2
    omega
  have hdBC : Disjoint (⋃ v ∈ (Vb K).filter (fun v => s + 2 ≤ v), bBox O K v)
      (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
        cBox π K s' (splitPairs (ResidueField O))) := by
    rw [Set.disjoint_left]
    intro c hcB hcC
    obtain ⟨v, hv, hB⟩ := Set.mem_iUnion₂.1 hcB
    obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hcC
    obtain ⟨h0, h1, -, -⟩ := hB
    obtain ⟨h0', h1', -, -, -⟩ := hC
    omega
  have hd1 : Disjoint ((⋃ v ∈ (Vb K).filter (fun v => s + 2 ≤ v), bBox O K v)
      ∪ ⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
          cBox π K s' (splitPairs (ResidueField O)))
      ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
          (decidedSet O 4 splitTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
        ∪ (decidedSet O 4 splitTailType K ∩ deepBox O K s ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcBC hcX
    have hX : (∃ s', c ∈ cBox π K s' (ddPairs (ResidueField O))) ∨ c ∈ bdBox O K := by
      rcases hcX with hD | hBd
      · obtain ⟨s', -, -, hC⟩ := Set.mem_iUnion₂.1 hD
        exact Or.inl ⟨s', hC⟩
      · exact Or.inr hBd.2
    rcases hcBC with hcB | hcC
    · obtain ⟨v, hv, hB⟩ := Set.mem_iUnion₂.1 hcB
      obtain ⟨h0, h1, -, -⟩ := hB
      have hvV := mem_Vb.1 (Finset.mem_filter.1 hv).1
      rcases hX with ⟨s', hC⟩ | hBd
      · obtain ⟨h0', h1', -, -, -⟩ := hC
        omega
      · obtain ⟨h0', h1', -, -⟩ := hBd
        omega
    · obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hcC
      obtain ⟨h0, -, -, -, hp⟩ := hC
      have hsS := mem_Sc.1 (Finset.mem_filter.1 hs').1
      rcases hX with ⟨s'', hC'⟩ | hBd
      · obtain ⟨h0', -, -, -, hp'⟩ := hC'
        have hss' : s' = s'' := by omega
        subst hss'
        exact Set.disjoint_left.1 disjoint_splitPairs_ddPairs hp hp'
      · obtain ⟨h0', -, -, -⟩ := hBd
        omega
  conv_lhs => rw [decided_splitTail_inter_deepBox hK hπ hs]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2, Set.ncard_union_eq hdBC,
    ncard_biUnion_eq _ _ (fun i _ j _ hij => bBox_pairwise' i j hij),
    ncard_biUnion_eq _ _ (fun i _ j _ hij => cBox_pairwise' i j hij),
    ncard_biUnion_eq _ _ (fun i hi j hj hij => cBox_dd_dec_pairwise splitTailType i hi j hj hij)]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' hs' => ?_
  have hmem := mem_Sc.1 (Finset.mem_filter.1 hs').1
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    card_decided_dd_stratum hπ hmem.1 (by omega) splitTailType]

/-- ★ **The inertTail deepBox identity**: genre (c)-irreducible at depths `> s`, the
dd recursion, and the boundary sliver. -/
private theorem decided_inertTail_inter_deepBox {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    decidedSet O 4 inertTailType K ∩ deepBox O K s
      = (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
            cBox π K s' (irrPairs (ResidueField O)))
        ∪ ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
              (decidedSet O 4 inertTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
          ∪ (decidedSet O 4 inertTailType K ∩ deepBox O K s ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hdeep⟩
    obtain ⟨h0, h1, h2, h3⟩ := hdeep
    rcases mem_genre_cases hK hπ (deepBox_subset_e2Box hs ⟨h0, h1, h2, h3⟩) with
      ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s', hs', hC⟩ | ⟨s', hs', hC⟩ | hD | hBd
    · exact absurd (decidedAt_unique hdec
        (decidedAt_aBox hK hπ (mem_Ta.1 ht).1 (mem_Ta.1 ht).2 hA))
        ramPair_ne_inertTail.symm
    · exact absurd (decidedAt_unique hdec
        (decidedAt_bBox hK hπ (mem_Vb.1 hv).1 (mem_Vb.1 hv).2 hB))
        splitTail_ne_inertTail.symm
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cSplitBox hK hπ (mem_Sc.1 hs').1 (mem_Sc.1 hs').2 hC))
        splitTail_ne_inertTail.symm
    · refine Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hs', ?_⟩) hC)
      obtain ⟨hC0, -, -, -, -⟩ := hC
      omega
    · rw [e2DdBox_eq] at hD
      obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hD
      refine Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hs', ?_⟩)
        ⟨hdec, hC⟩))
      obtain ⟨hC0, -, -, -, -⟩ := hC
      omega
    · exact Or.inr (Or.inr ⟨⟨hdec, h0, h1, h2, h3⟩, hBd⟩)
  · rintro (hC | hDd | hBd)
    · obtain ⟨s', hs', hC'⟩ := Set.mem_iUnion₂.1 hC
      obtain ⟨hsS, hss⟩ := Finset.mem_filter.1 hs'
      exact ⟨decidedAt_cIrrBox hK hπ (mem_Sc.1 hsS).1 (mem_Sc.1 hsS).2 hC',
        cBox_dd_subset_deepBox hss hC'⟩
    · obtain ⟨s', hs', hdec, hC⟩ := Set.mem_iUnion₂.1 hDd
      exact ⟨hdec, cBox_dd_subset_deepBox (Finset.mem_filter.1 hs').2 hC⟩
    · exact ⟨hBd.1.1, hBd.1.2⟩

/-- ★★ **The inertTail deepBox count recursion**. -/
private theorem card_decided_deepBox_inertTail {K : ℕ} (hK : 3 ≤ K)
    (hπ : Irreducible π) {s : ℕ} (hs : 1 ≤ s) :
    Nat.card ((decidedSet O 4 inertTailType K ∩ deepBox O K s) : Set (Coeff O 4 K))
      = (∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
            Nat.card ((cBox π K s' (irrPairs (ResidueField O))) : Set (Coeff O 4 K)))
        + ((residueCard O - 1)
            * (∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
                Nat.card ((decidedSet O 4 inertTailType K ∩ deepBox O K s')
                  : Set (Coeff O 4 K)))
          + Nat.card ((decidedSet O 4 inertTailType K ∩ deepBox O K s ∩ bdBox O K)
              : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
      (decidedSet O 4 inertTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
      (decidedSet O 4 inertTailType K ∩ deepBox O K s ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    intro c hcD hcBd
    obtain ⟨s', hs', -, hC⟩ := Set.mem_iUnion₂.1 hcD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hcBd.2
    have := (mem_Sc.1 (Finset.mem_filter.1 hs').1).2
    omega
  have hd1 : Disjoint (⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
      cBox π K s' (irrPairs (ResidueField O)))
      ((⋃ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
          (decidedSet O 4 inertTailType K ∩ cBox π K s' (ddPairs (ResidueField O))))
        ∪ (decidedSet O 4 inertTailType K ∩ deepBox O K s ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcC hcX
    obtain ⟨s', hs', hC⟩ := Set.mem_iUnion₂.1 hcC
    obtain ⟨h0, -, -, -, hp⟩ := hC
    have hsS := mem_Sc.1 (Finset.mem_filter.1 hs').1
    rcases hcX with hD | hBd
    · obtain ⟨s'', -, -, hC'⟩ := Set.mem_iUnion₂.1 hD
      obtain ⟨h0', -, -, -, hp'⟩ := hC'
      have hss' : s' = s'' := by omega
      subst hss'
      exact Set.disjoint_left.1 disjoint_irrPairs_ddPairs hp hp'
    · obtain ⟨h0', -, -, -⟩ := hBd.2
      omega
  conv_lhs => rw [decided_inertTail_inter_deepBox hK hπ hs]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2,
    ncard_biUnion_eq _ _ (fun i _ j _ hij => cBox_pairwise' i j hij),
    ncard_biUnion_eq _ _ (fun i hi j hj hij => cBox_dd_dec_pairwise inertTailType i hi j hj hij)]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' hs' => ?_
  have hmem := mem_Sc.1 (Finset.mem_filter.1 hs').1
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    card_decided_dd_stratum hπ hmem.1 (by omega) inertTailType]

end Partition

/-! ## §4 — the unroll: the first-order recursion `U(s−1) = E(s) + q·U(s)` in closed
form, and the top-level dd count -/

section Unroll

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {π : O}

-- IFCG53's private window normal forms, reproduced (the sanctioned replay).
private theorem Sc_eq (K : ℕ) : Sc K = Finset.Ico 1 (K / 2) := by
  ext s
  rw [mem_Sc, Finset.mem_Ico]
  omega

private theorem Sc_filter_eq (K s : ℕ) :
    (Sc K).filter (fun s' => s + 1 ≤ s') = Finset.Ioo s (K / 2) := by
  ext x
  rw [Finset.mem_filter, mem_Sc, Finset.mem_Ioo]
  omega

/-- ★ **The top-level dd count**: the decided dd sector is `(q−1)` copies of the
deepBox tail sum. -/
private theorem card_decided_e2DdBox {K : ℕ} (hπ : Irreducible π)
    (σ : FactorizationType) :
    Nat.card ((decidedSet O 4 σ K ∩ e2DdBox π K) : Set (Coeff O 4 K))
      = (residueCard O - 1)
        * ∑ s ∈ Sc K,
            Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s) : Set (Coeff O 4 K)) := by
  have hunion : decidedSet O 4 σ K ∩ e2DdBox π K
      = ⋃ s ∈ Sc K, (decidedSet O 4 σ K ∩ cBox π K s (ddPairs (ResidueField O))) := by
    rw [e2DdBox_eq, Set.inter_iUnion₂]
  rw [hunion]
  rw [Nat.card_coe_set_eq,
    ncard_biUnion_eq _ _ (fun i hi j hj hij => cBox_dd_dec_pairwise σ i hi j hj hij),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hmem := mem_Sc.1 hs
  exact card_decided_dd_stratum hπ hmem.1 (by omega) σ

/-- ★ **The generic geometric unroll** for `U(s) = g s + q·U(s+1)` tails. -/
private theorem tail_sum_geom {q : ℝ} {T : ℕ} (D g : ℕ → ℝ)
    (hrec : ∀ s, s < T →
      (∑ s' ∈ Finset.Ioo s T, D s') = g s + q * ∑ s' ∈ Finset.Ioo (s + 1) T, D s') :
    ∀ n s, s + n = T →
      (∑ s' ∈ Finset.Ioo s T, D s') = ∑ j ∈ Finset.Ico s T, q ^ (j - s) * g j := by
  intro n
  induction n with
  | zero =>
      intro s hsT
      have hs : s = T := by omega
      subst hs
      simp
  | succ n ih =>
      intro s hsT
      have hsT' : s < T := by omega
      rw [hrec s hsT', ih (s + 1) (by omega), Finset.mul_sum,
        Finset.sum_eq_sum_Ico_succ_bot hsT', Nat.sub_self, pow_zero, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ico.1 hj
      rw [show j - s = (j - (s + 1)) + 1 from by omega, pow_succ]
      ring

/-- ★★ **THE UNROLLED COUNT** (generic in the per-`σ` genre term `A`): with the count
recursion as input, the decided dd-sector count is the geometric-weight resummation of
the genre terms plus the boundary slivers. -/
private theorem card_e2DdBox_unrolled {K : ℕ} (_hK : 3 ≤ K) (hπ : Irreducible π)
    (σ : FactorizationType) (A : ℕ → ℕ)
    (hAtop : ∀ s, K / 2 ≤ s → A s = 0)
    (hrec : ∀ s, 1 ≤ s →
      Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s) : Set (Coeff O 4 K))
        = A s + ((residueCard O - 1)
            * (∑ s' ∈ (Sc K).filter (fun s' => s + 1 ≤ s'),
                Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s') : Set (Coeff O 4 K)))
          + Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s ∩ bdBox O K)
              : Set (Coeff O 4 K)))) :
    ((Nat.card ((decidedSet O 4 σ K ∩ e2DdBox π K) : Set (Coeff O 4 K)) : ℝ))
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ∑ j ∈ Finset.Ico 0 (K / 2), ((residueCard O : ℕ) : ℝ) ^ j
            * (((A (j + 1) : ℕ) : ℝ)
              + ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K (j + 1) ∩ bdBox O K)
                  : Set (Coeff O 4 K)) : ℕ) : ℝ)) := by
  have hq1 : 1 ≤ residueCard O := le_trans (by omega) (two_le_residueCard O)
  -- the ℝ-recursion for the tail sums
  have hrecR : ∀ s, s < K / 2 →
      (∑ s' ∈ Finset.Ioo s (K / 2),
          ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s') : Set (Coeff O 4 K)) : ℕ) : ℝ))
        = (((A (s + 1) : ℕ) : ℝ)
            + ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K (s + 1) ∩ bdBox O K)
                : Set (Coeff O 4 K)) : ℕ) : ℝ))
          + ((residueCard O : ℕ) : ℝ)
            * ∑ s' ∈ Finset.Ioo (s + 1) (K / 2),
                ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s')
                  : Set (Coeff O 4 K)) : ℕ) : ℝ) := by
    intro s hsT
    by_cases hcase : s + 1 < K / 2
    · -- peel the bottom, then the count recursion at `s+1`
      rw [← Finset.Ico_add_one_left_eq_Ioo s (K / 2),
        Finset.sum_eq_sum_Ico_succ_bot hcase, Finset.Ico_add_one_left_eq_Ioo]
      have hcnt := hrec (s + 1) (by omega)
      rw [Sc_filter_eq K (s + 1)] at hcnt
      rw [hcnt]
      push_cast [Nat.cast_sub hq1]
      ring
    · -- the top of the window: everything vanishes
      have hempty1 : Finset.Ioo s (K / 2) = ∅ := by
        ext x
        simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
        omega
      have hempty2 : Finset.Ioo (s + 1) (K / 2) = ∅ := by
        ext x
        simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
        omega
      have hdeepempty : deepBox O K (s + 1) = (∅ : Set (Coeff O 4 K)) :=
        deepBox_eq_empty (by omega)
      rw [hempty1, hempty2, hdeepempty, hAtop (s + 1) (by omega)]
      simp
  -- unroll from `s = 0` and assemble
  have hunroll := tail_sum_geom
    (fun s' => ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s')
      : Set (Coeff O 4 K)) : ℕ) : ℝ))
    (fun s => ((A (s + 1) : ℕ) : ℝ)
      + ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K (s + 1) ∩ bdBox O K)
          : Set (Coeff O 4 K)) : ℕ) : ℝ))
    hrecR (K / 2) 0 (by omega)
  have hSc : Sc K = Finset.Ioo 0 (K / 2) := by
    rw [Sc_eq K, ← Finset.Ico_add_one_left_eq_Ioo]
    rfl
  calc ((Nat.card ((decidedSet O 4 σ K ∩ e2DdBox π K) : Set (Coeff O 4 K)) : ℕ) : ℝ)
      = (((residueCard O - 1 : ℕ) : ℕ) : ℝ)
        * ∑ s' ∈ Finset.Ioo 0 (K / 2),
            ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K s')
              : Set (Coeff O 4 K)) : ℕ) : ℝ) := by
        rw [card_decided_e2DdBox hπ σ, hSc]
        push_cast
        rfl
    _ = (((residueCard O : ℕ) : ℝ) - 1)
        * ∑ j ∈ Finset.Ico 0 (K / 2), ((residueCard O : ℕ) : ℝ) ^ j
            * (((A (j + 1) : ℕ) : ℝ)
              + ((Nat.card ((decidedSet O 4 σ K ∩ deepBox O K (j + 1) ∩ bdBox O K)
                  : Set (Coeff O 4 K)) : ℕ) : ℝ)) := by
        rw [hunroll, Nat.cast_sub hq1, Nat.cast_one]
        refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
        rw [Nat.sub_zero]

end Unroll

/-! ## §5 — the limit layer: the general-`k` geometric machine, the weight swap, and
the boundary error family -/

section LimitKit

open Filter Topology

/-- ★ **The general-`k` stratum-sum limit machine** (IFCG53's `tendsto_geom_sum`
generalized from `3t` to `kt`; consumed at `k = 2` alongside the landed `k = 3`). -/
private theorem tendsto_geom_sum_k {q : ℝ} (hq : 2 ≤ q) {k : ℕ} (hk : 1 ≤ k) (C : ℝ)
    (a e : ℕ) (T : ℕ → ℕ) (hT : Filter.Tendsto T Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun M => ∑ t ∈ Finset.Ico a (T M), C / q ^ (k * t + e))
      Filter.atTop (nhds (C * q ^ k / ((q ^ k - 1) * q ^ (k * a + e)))) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hqk : (0 : ℝ) < q ^ k := by positivity
  have h2k : (2 : ℝ) ≤ q ^ k := by
    calc (2 : ℝ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := pow_le_pow_right₀ (by linarith) hk
  have hr : |1 / q ^ k| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hqk]
    linarith
  have hgeo := (hasSum_geometric_of_abs_lt_one hr).mul_left (C / q ^ (k * a + e))
  have hfun : ∀ j : ℕ, C / q ^ (k * a + e) * (1 / q ^ k) ^ j
      = C / q ^ (k * (a + j) + e) := by
    intro j
    rw [show k * (a + j) + e = (k * a + e) + k * j from by ring, pow_add, pow_mul]
    rw [div_pow, one_pow, div_mul_div_comm, mul_one]
    congr 1
    rw [pow_add, pow_add, pow_mul, pow_mul]
  have hval : C / q ^ (k * a + e) * (1 - 1 / q ^ k)⁻¹
      = C * q ^ k / ((q ^ k - 1) * q ^ (k * a + e)) := by
    have h1 : q ^ k - 1 ≠ 0 := by intro h; linarith
    have h2 : (1 : ℝ) - 1 / q ^ k ≠ 0 := by
      have hlt : 1 / q ^ k < 1 := by rw [div_lt_one hqk]; linarith
      intro h
      linarith
    have h3 : q ^ (k * a + e) ≠ 0 := by positivity
    field_simp
  simp only [hfun] at hgeo
  rw [hval] at hgeo
  have htend := hgeo.tendsto_sum_nat
  have hTa : Filter.Tendsto (fun M => T M - a) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop] at hT ⊢
    intro b
    obtain ⟨N, hN⟩ := hT (b + a)
    exact ⟨N, fun M hM => by have := hN M hM; omega⟩
  have hcomp := htend.comp hTa
  refine hcomp.congr ?_
  intro M
  show ∑ j ∈ Finset.range (T M - a), C / q ^ (k * (a + j) + e)
    = ∑ t ∈ Finset.Ico a (T M), C / q ^ (k * t + e)
  rw [Finset.sum_Ico_eq_sum_range]

-- IFCG53's private window normal forms + tendstos, reproduced (sanctioned replays).
private theorem Ta_eq (K : ℕ) : Ta K = Finset.Ico 2 ((K + 1) / 2) := by
  ext t
  rw [mem_Ta, Finset.mem_Ico]
  omega

private theorem Vb_eq (K : ℕ) : Vb K = Finset.Ico 2 (K / 2 + 1) := by
  ext v
  rw [mem_Vb, Finset.mem_Ico]
  omega

private theorem tendsto_Ta_window : Filter.Tendsto (fun M : ℕ => (M + 4 + 1) / 2)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

private theorem tendsto_Vb_window : Filter.Tendsto (fun M : ℕ => (M + 4) / 2 + 1)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

private theorem tendsto_Sc_window : Filter.Tendsto (fun M : ℕ => (M + 4) / 2)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

/-- ★ **The weight swap**: the geometric-weighted sum of window tails equals the
per-stratum sum with truncated-geometric weights. -/
private theorem sum_weight_swap {T : ℕ} (W : Finset ℕ) (F G : ℕ → ℝ)
    (hW : ∀ t ∈ W, t - 1 ≤ T) :
    (∑ j ∈ Finset.Ico 0 T, G j * (∑ t ∈ W.filter (fun t => j + 2 ≤ t), F t))
      = ∑ t ∈ W, F t * (∑ j ∈ Finset.Ico 0 (t - 1), G j) := by
  have h1 : ∀ j, G j * (∑ t ∈ W.filter (fun t => j + 2 ≤ t), F t)
      = ∑ t ∈ W, ite (j + 2 ≤ t) (G j * F t) 0 := by
    intro j
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← Finset.sum_filter]
  have hfil : (Finset.Ico 0 T).filter (fun j => j + 2 ≤ t) = Finset.Ico 0 (t - 1) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
    have := hW t ht
    omega
  rw [hfil, ← Finset.sum_mul, mul_comm]

/-- The truncated-geometric multiplier: `(q−1)·Σ_{j<n} q^j = q^n − 1`. -/
private theorem geom_mul (q : ℝ) (n : ℕ) :
    (q - 1) * (∑ j ∈ Finset.Ico 0 n, q ^ j) = q ^ n - 1 := by
  rw [← Finset.range_eq_Ico, mul_comm, geom_sum_mul]

/-- The weight swap at shift 3 (the genre-(b) windows `v ≥ s+2`). -/
private theorem sum_weight_swap3 {T : ℕ} (W : Finset ℕ) (F G : ℕ → ℝ)
    (hW : ∀ t ∈ W, t - 2 ≤ T) :
    (∑ j ∈ Finset.Ico 0 T, G j * (∑ t ∈ W.filter (fun t => j + 3 ≤ t), F t))
      = ∑ t ∈ W, F t * (∑ j ∈ Finset.Ico 0 (t - 2), G j) := by
  have h1 : ∀ j, G j * (∑ t ∈ W.filter (fun t => j + 3 ≤ t), F t)
      = ∑ t ∈ W, ite (j + 3 ≤ t) (G j * F t) 0 := by
    intro j
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← Finset.sum_filter]
  have hfil : (Finset.Ico 0 T).filter (fun j => j + 3 ≤ t) = Finset.Ico 0 (t - 2) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
    have := hW t ht
    omega
  rw [hfil, ← Finset.sum_mul, mul_comm]

end LimitKit

/-! ## §5b — the pair-count value bridge (IFCG53 §7b privates, reproduced) -/

section PairCounts

variable {F : Type*} [Field F] [Finite F]

private theorem card_ne_zero_subtype : Nat.card {x : F // x ≠ 0} = Nat.card F - 1 := by
  have hset : ({δ : F | δ ≠ 0} : Set F) = Set.univ \ {0} := by
    ext δ
    simp
  rw [show {δ : F // δ ≠ 0} = ({δ : F | δ ≠ 0} : Set F) from rfl, Nat.card_coe_set_eq,
    hset, Set.ncard_sdiff (by simp : ({0} : Set F) ⊆ Set.univ), Set.ncard_univ,
    Set.ncard_singleton]

private theorem pairs_ne_zero_eq :
    {p : F × F | p.2 ≠ 0} = splitPairs F ∪ irrPairs F ∪ ddPairs F := by
  ext p
  constructor
  · intro hp
    rcases pair_trichotomy hp with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact splitPairs_snd_ne_zero h
    · exact irrPairs_snd_ne_zero h
    · exact ddPairs_snd_ne_zero h

private theorem card_pairs_ne_zero :
    Nat.card ({p : F × F | p.2 ≠ 0} : Set (F × F)) = Nat.card F * (Nat.card F - 1) := by
  have hequiv : (F × {x : F // x ≠ 0}) ≃ ({p : F × F | p.2 ≠ 0} : Set (F × F)) :=
    { toFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      invFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      left_inv := fun x => Prod.ext rfl (Subtype.ext rfl)
      right_inv := fun p => Subtype.ext rfl }
  rw [← Nat.card_congr hequiv, Nat.card_prod, card_ne_zero_subtype]

private theorem card_pair_partition :
    Nat.card (splitPairs F) + Nat.card (irrPairs F) + Nat.card (ddPairs F)
      = Nat.card F * (Nat.card F - 1) := by
  rw [← card_pairs_ne_zero, pairs_ne_zero_eq]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq (by
      rw [Set.disjoint_union_left]
      exact ⟨disjoint_splitPairs_ddPairs, disjoint_irrPairs_ddPairs⟩),
    Set.ncard_union_eq disjoint_splitPairs_irrPairs]

private theorem two_mul_card_irrPairs :
    2 * Nat.card (irrPairs F) = Nat.card F ^ 2 - Nat.card F := by
  letI : Fintype F := Fintype.ofFinite F
  rw [card_irrPairs, two_mul_card_irredOfDeg_two F]
  simp [Nat.card_eq_fintype_card]

end PairCounts

section ValueBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem hQF : Nat.card (ResidueField O) = residueCard O := rfl

private theorem digTriples_split_val :
    ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 2)) / 2 := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQ1 : 1 ≤ Nat.card (ResidueField O) := by rw [hQF]; omega
  have hpart := card_pair_partition (F := ResidueField O)
  have hirr := two_mul_card_irrPairs (F := ResidueField O)
  have hddc := IFCG36.card_ddPairs (F := ResidueField O)
  have hpartR : ((Nat.card (splitPairs (ResidueField O))) : ℝ)
      + ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      + ((Nat.card (ddPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) * (((residueCard O : ℕ) : ℝ) - 1) := by
    have h := congrArg (Nat.cast (R := ℝ)) hpart
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  have hirrR : 2 * ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hirr
    push_cast [hQF, Nat.cast_sub (show residueCard O ≤ residueCard O ^ 2 from
      Nat.le_self_pow (by norm_num) _)] at h
    exact_mod_cast h
  have hddR : ((Nat.card (ddPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) - 1 := by
    have h := congrArg (Nat.cast (R := ℝ)) hddc
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  have hsplitR : 2 * ((Nat.card (splitPairs (ResidueField O))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 2) := by
    linear_combination 2 * hpartR - hirrR - 2 * hddR
  have hdt := card_digTriples (splitPairs (ResidueField O))
  have hdtR : ((Nat.card (digTriples (ResidueField O)
      (splitPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((Nat.card (splitPairs (ResidueField O))) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdt
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  rw [hdtR]
  linear_combination ((((residueCard O : ℕ) : ℝ) - 1) / 2) * hsplitR

private theorem digTriples_irr_val :
    ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ))) / 2 := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQ1 : 1 ≤ Nat.card (ResidueField O) := by rw [hQF]; omega
  have hirr := two_mul_card_irrPairs (F := ResidueField O)
  have hirrR : 2 * ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hirr
    push_cast [hQF, Nat.cast_sub (show residueCard O ≤ residueCard O ^ 2 from
      Nat.le_self_pow (by norm_num) _)] at h
    exact_mod_cast h
  have hdt := card_digTriples (irrPairs (ResidueField O))
  have hdtR : ((Nat.card (digTriples (ResidueField O)
      (irrPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((Nat.card (irrPairs (ResidueField O))) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdt
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  rw [hdtR]
  linear_combination ((((residueCard O : ℕ) : ℝ) - 1) / 2) * hirrR

end ValueBridge

/-! ## §6 — the boundary error family and its vanishing -/

section ErrFam

open Filter Topology

/-- **The boundary error dominator**: `(1/q)^(K − K/2)` at `K = M+4` — the geometric
weight `q^(K/2)` times the boundary bound `q^(3K)`, normalized by `q^(4K)`. -/
private def EBd : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    (1 / ((residueCard O : ℕ) : ℝ)) ^ ((M + 4) - (M + 4) / 2)

private theorem tendsto_EBd (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) :
    Filter.Tendsto (EBd O π) Filter.atTop (nhds 0) := by
  have hq2 : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast two_le_residueCard O
  have h0 : (0 : ℝ) ≤ 1 / ((residueCard O : ℕ) : ℝ) := by positivity
  have h1 : 1 / ((residueCard O : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hexp : Filter.Tendsto (fun M : ℕ => (M + 4) - (M + 4) / 2)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨2 * b, fun M hM => by omega⟩
  exact hpow.comp hexp

/-- The dominator in ratio form: `q^(K/2)·q^(3K)/q^(4K) = EBd`. -/
private theorem EBd_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) :
    ((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2) * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = EBd O π M := by
  have hq2 : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℝ) ≠ 0 := by linarith
  show _ = (1 / ((residueCard O : ℕ) : ℝ)) ^ ((M + 4) - (M + 4) / 2)
  rw [div_pow, one_pow, ← pow_add,
    div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add,
    show (M + 4) / 2 + 3 * (M + 4) + ((M + 4) - (M + 4) / 2) = 4 * (M + 4) from by omega]

end ErrFam

/-! ## §7 — the ramPair fire: main family, decomposition identity, limit, sandwich -/

section RamFire

open Filter Topology

/-- **The ramPair main family**: the swapped per-stratum form
`Σ_t (q−1)²(q^(t−1) − 1)/q^(3t+5)` over the genre-(a) window. -/
private def ddMainRam : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    ∑ t ∈ Finset.Ico 2 ((M + 4 + 1) / 2),
      ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
        * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1))
        / ((residueCard O : ℕ) : ℝ) ^ (3 * t + 5)

/-- ★★ **The ramPair decomposition**: the dd family is the main family plus the
(nonnegative) boundary term. -/
private theorem e2DdDecFam_ram_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) (hπ : Irreducible π) (M : ℕ) :
    e2DdDecFam ramPairType O π M
      = ddMainRam O π M
        + (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((Nat.card ((decidedSet O 4 ramPairType (M + 4)
                  ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                  : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
  have hK : 3 ≤ M + 4 := by omega
  have hq1 : 1 ≤ residueCard O := le_trans (by omega) (two_le_residueCard O)
  have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast two_le_residueCard O
  have hAtop : ∀ s, (M + 4) / 2 ≤ s →
      (∑ t ∈ (Ta (M + 4)).filter (fun t => s + 1 ≤ t),
        Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4)))) = 0 := by
    intro s hs
    rw [Finset.filter_eq_empty_iff.2 (fun t ht => by
      have := mem_Ta.1 ht
      omega), Finset.sum_empty]
  have hcount := card_e2DdBox_unrolled hK hπ ramPairType
    (fun s => ∑ t ∈ (Ta (M + 4)).filter (fun t => s + 1 ≤ t),
      Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))))
    hAtop (fun s hs => card_decided_deepBox_ramPair hK hπ hs)
  show ((Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2DdBox π (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
  rw [hcount]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.Ico 0 ((M + 4) / 2)) =>
    mul_add (((residueCard O : ℕ) : ℝ) ^ j) _ _), Finset.sum_add_distrib,
    mul_add, add_div]
  congr 1
  -- THE MAIN TERM: swap, geometric multiplier, stratum count substitution
  have hcast : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
      * ((∑ t ∈ (Ta (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
          Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ j
        * (∑ t ∈ (Ta (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
            ((Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)) := by
    intro j _
    rw [Nat.cast_sum]
  rw [Finset.sum_congr rfl hcast]
  have hswap : (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
      * (∑ t ∈ (Ta (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
          ((Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)))
      = ∑ t ∈ Ta (M + 4),
          ((Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j) :=
    sum_weight_swap (Ta (M + 4)) _ _ (fun t ht => by
      have := mem_Ta.1 ht
      omega)
  rw [hswap, Finset.mul_sum, Finset.sum_div]
  rw [Ta_eq (M + 4)]
  show _ = ddMainRam O π M
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_Ico] at ht
  have hmem : t ∈ Ta (M + 4) := mem_Ta.2 ⟨ht.1, by omega⟩
  rw [show (((residueCard O : ℕ) : ℝ) - 1)
      * (((Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
        * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j))
      = ((Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
        * ((((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j)) from by ring,
    geom_mul]
  rw [card_aBox hK ht.1 (by omega)]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (show 1 ≤ residueCard O from hq1), Nat.cast_one]
  obtain ⟨Ex, hE1, hE2⟩ : ∃ Ex, 4 * (M + 4) - (3 * t + 5) = Ex
      ∧ 4 * (M + 4) = Ex + (3 * t + 5) := ⟨_, rfl, by omega⟩
  rw [hE1, hE2, pow_add,
    mul_comm (((residueCard O : ℕ) : ℝ) ^ Ex) (((residueCard O : ℕ) : ℝ) ^ (3 * t + 5))]
  rw [show (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
      * ((residueCard O : ℕ) : ℝ) ^ Ex * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1)
      = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
        * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1) * ((residueCard O : ℕ) : ℝ) ^ Ex
      from by ring]
  rw [mul_div_mul_right _ _ (pow_ne_zero Ex (by positivity))]

/-- ★★ **The ramPair main limit**: value `(q−1)³/((q²−1)(q³−1)q⁶)`. -/
private theorem zcURLim_ddMainRam : ZcURLim ddMainRam := by
  refine ⟨(Polynomial.X - 1) ^ 3,
    (Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 6), ?_, ?_⟩
  · refine mul_ne_zero ?_ (mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero)) <;>
      · intro h
        have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
        simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h4 : (4 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 2 := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ _ := by gcongr
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd2 : ((residueCard O : ℕ) : ℚ) ^ 2 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero hd2 (mul_ne_zero hd3 (pow_ne_zero _ hqQ0))
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hq0R : ((residueCard O : ℕ) : ℝ) ≠ 0 := by linarith
      -- split each term into the two geometric species
      have hM : ∀ M, ddMainRam O π M
          = (∑ t ∈ Finset.Ico 2 ((M + 4 + 1) / 2),
              ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                / ((residueCard O : ℕ) : ℝ) ^ (2 * t + 6))
            - ∑ t ∈ Finset.Ico 2 ((M + 4 + 1) / 2),
                ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                  / ((residueCard O : ℕ) : ℝ) ^ (3 * t + 5) := by
        intro M
        show (∑ t ∈ Finset.Ico 2 ((M + 4 + 1) / 2), _) = _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_Ico] at ht
        rw [mul_sub, mul_one, sub_div]
        congr 1
        rw [show 3 * t + 5 = (2 * t + 6) + (t - 1) from by omega, pow_add]
        exact mul_div_mul_right _ _ (pow_ne_zero (t - 1) hq0R)
      have hlim2 := tendsto_geom_sum_k (q := ((residueCard O : ℕ) : ℝ)) hq2R
        (k := 2) (by omega)
        ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 6 _
        tendsto_Ta_window
      have hlim3 := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 5 _
        tendsto_Ta_window
      have hval : ((((Polynomial.X - 1) ^ 3 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / ((Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 6)
            : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
              * ((residueCard O : ℕ) : ℝ) ^ 2
              / ((((residueCard O : ℕ) : ℝ) ^ 2 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (2 * 2 + 6))
            - (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 2 + 5)) := by
        rw [Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one]
        have hd2R : ((residueCard O : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by
          intro h
          exact hd2 (by exact_mod_cast h)
        have hd3R : ((residueCard O : ℕ) : ℝ) ^ 3 - 1 ≠ 0 := by
          intro h
          exact hd3 (by exact_mod_cast h)
        push_cast
        field_simp
        ring
      rw [hval]
      exact (hlim2.sub hlim3).congr (fun M => (hM M).symm)

/-- ★★★ **THE ramPair dd FIRE — CITE-FREE**:
`ZcURLim (e2DdDecFam ramPairType)`, value `(q−1)/(q⁶(q+1)(q²+q+1))`. -/
theorem zcURLim_e2DdDecFam_ramPair : ZcURLim (e2DdDecFam ramPairType) := by
  refine ZcURLim.sandwich (E := EBd) zcURLim_ddMainRam
    (fun O _ _ _ _ _ π _ => tendsto_EBd O π) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_ram_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    apply le_add_of_nonneg_right
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Nat.cast_nonneg _)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_ram_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    have hadd : ∀ a b c : ℝ, b ≤ c → a + b ≤ a + c := fun a b c h => by linarith
    refine hadd _ _ _ ?_
    have hK : 3 ≤ M + 4 := by omega
    have hBle : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2),
        ((Nat.card ((decidedSet O 4 ramPairType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ))
        ≤ ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by
      intro j _
      have h1 : Nat.card ((decidedSet O 4 ramPairType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4)) : Set (Coeff O 4 (M + 4)))
          ≤ Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) :=
        Nat.card_mono (Set.toFinite _) Set.inter_subset_right
      calc ((Nat.card ((decidedSet O 4 ramPairType (M + 4)
            ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ))
          ≤ ((Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ ((residueCard O ^ (3 * (M + 4)) : ℕ) : ℝ) := by
            exact_mod_cast card_bdBox_le hK
        _ = ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by push_cast; rfl
    calc (((residueCard O : ℕ) : ℝ) - 1)
        * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
            * ((Nat.card ((decidedSet O 4 ramPairType (M + 4)
                ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        ≤ (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr with j hj
          · linarith
          · exact hBle j hj
      _ = (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2) - 1)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          rw [← Finset.sum_mul, ← mul_assoc, geom_mul]
      _ ≤ ((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr
          linarith [sub_le_self (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2))
            (zero_le_one (α := ℝ))]
      _ = EBd O π M := EBd_eq O π M

end RamFire

/-! ## §8 — the splitTail fire -/

section SplitFire

open Filter Topology

/-- **The splitTail main family**: genre (b) plus genre (c)-split, swapped form. -/
private def ddMainSplit : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    (∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1),
      ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
        * (((residueCard O : ℕ) : ℝ) ^ (v - 2) - 1))
        / ((residueCard O : ℕ) : ℝ) ^ (3 * v + 4))
    + ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
        (((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
          * (((residueCard O : ℕ) : ℝ) ^ (s - 1) - 1))
          / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7)

/-- ★★ **The splitTail decomposition**. -/
private theorem e2DdDecFam_split_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) (hπ : Irreducible π) (M : ℕ) :
    e2DdDecFam splitTailType O π M
      = ddMainSplit O π M
        + (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
                  ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                  : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
  have hK : 3 ≤ M + 4 := by omega
  have hq1 : 1 ≤ residueCard O := le_trans (by omega) (two_le_residueCard O)
  have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast two_le_residueCard O
  have hAtop : ∀ s, (M + 4) / 2 ≤ s →
      ((∑ v ∈ (Vb (M + 4)).filter (fun v => s + 2 ≤ v),
          Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))))
        + ∑ t ∈ (Sc (M + 4)).filter (fun t => s + 1 ≤ t),
            Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4)))) = 0 := by
    intro s hs
    rw [Finset.filter_eq_empty_iff.2 (fun v hv => by
        have := mem_Vb.1 hv
        omega), Finset.sum_empty,
      Finset.filter_eq_empty_iff.2 (fun t ht => by
        have := mem_Sc.1 ht
        omega), Finset.sum_empty]
    rfl
  have hcount := card_e2DdBox_unrolled hK hπ splitTailType
    (fun s => (∑ v ∈ (Vb (M + 4)).filter (fun v => s + 2 ≤ v),
        Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))))
      + ∑ t ∈ (Sc (M + 4)).filter (fun t => s + 1 ≤ t),
          Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))))
    hAtop (fun s hs => card_decided_deepBox_splitTail hK hπ hs)
  show ((Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ e2DdBox π (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
  rw [hcount]
  have hexp : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
      * ((((∑ v ∈ (Vb (M + 4)).filter (fun v => j + 1 + 2 ≤ v),
            Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))))
          + ∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
              Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
                : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
        + ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
            ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)))
      = (((residueCard O : ℕ) : ℝ) ^ j
          * (∑ v ∈ (Vb (M + 4)).filter (fun v => j + 1 + 2 ≤ v),
              ((Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ))
          + ((residueCard O : ℕ) : ℝ) ^ j
            * (∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
                ((Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
                  : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)))
        + ((residueCard O : ℕ) : ℝ) ^ j
          * ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
              ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
              : Set (Coeff O 4 (M + 4))) : ℝ)) := by
    intro j _
    push_cast
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib,
    mul_add, add_div]
  congr 1
  rw [mul_add, add_div]
  show _ + _ = (∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1), _) + ∑ s ∈ Finset.Ico 1 ((M + 4) / 2), _
  congr 1
  · -- genre (b)
    have hswap : (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
        * (∑ v ∈ (Vb (M + 4)).filter (fun v => j + 1 + 2 ≤ v),
            ((Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)))
        = ∑ v ∈ Vb (M + 4),
            ((Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
            * (∑ j ∈ Finset.Ico 0 (v - 2), ((residueCard O : ℕ) : ℝ) ^ j) :=
      sum_weight_swap3 (Vb (M + 4)) _ _ (fun v hv => by
        have := mem_Vb.1 hv
        omega)
    rw [hswap, Finset.mul_sum, Finset.sum_div, Vb_eq (M + 4)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_Ico] at hv
    rw [show (((residueCard O : ℕ) : ℝ) - 1)
        * (((Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * (∑ j ∈ Finset.Ico 0 (v - 2), ((residueCard O : ℕ) : ℝ) ^ j))
        = ((Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * ((((residueCard O : ℕ) : ℝ) - 1)
            * (∑ j ∈ Finset.Ico 0 (v - 2), ((residueCard O : ℕ) : ℝ) ^ j)) from by ring,
      geom_mul]
    rw [card_bBox hK hv.1 (by omega)]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (show 1 ≤ residueCard O from hq1), Nat.cast_one]
    obtain ⟨Ex, hE1, hE2⟩ : ∃ Ex, 4 * (M + 4) - (3 * v + 4) = Ex
        ∧ 4 * (M + 4) = Ex + (3 * v + 4) := ⟨_, rfl, by omega⟩
    rw [hE1, hE2, pow_add,
      mul_comm (((residueCard O : ℕ) : ℝ) ^ Ex) (((residueCard O : ℕ) : ℝ) ^ (3 * v + 4))]
    rw [show (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
        * ((residueCard O : ℕ) : ℝ) ^ Ex * (((residueCard O : ℕ) : ℝ) ^ (v - 2) - 1)
        = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
          * (((residueCard O : ℕ) : ℝ) ^ (v - 2) - 1) * ((residueCard O : ℕ) : ℝ) ^ Ex
        from by ring]
    rw [mul_div_mul_right _ _ (pow_ne_zero Ex (by positivity))]
  · -- genre (c)-split
    have hswap : (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
        * (∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
            ((Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)))
        = ∑ t ∈ Sc (M + 4),
            ((Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
            * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j) :=
      sum_weight_swap (Sc (M + 4)) _ _ (fun t ht => by
        have := mem_Sc.1 ht
        omega)
    rw [hswap, Finset.mul_sum, Finset.sum_div, Sc_eq (M + 4)]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    rw [show (((residueCard O : ℕ) : ℝ) - 1)
        * (((Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j))
        = ((Nat.card ((cBox π (M + 4) t (splitPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * ((((residueCard O : ℕ) : ℝ) - 1)
            * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j)) from by ring,
      geom_mul]
    rw [card_cBox hK hπ ht.1 (by omega) (fun p hp => splitPairs_snd_ne_zero hp)]
    rw [Nat.cast_mul, Nat.cast_pow]
    obtain ⟨Ex, hE1, hE2⟩ : ∃ Ex, 4 * (M + 4) - (3 * t + 7) = Ex
        ∧ 4 * (M + 4) = Ex + (3 * t + 7) := ⟨_, rfl, by omega⟩
    rw [hE1, hE2, pow_add,
      mul_comm (((residueCard O : ℕ) : ℝ) ^ Ex) (((residueCard O : ℕ) : ℝ) ^ (3 * t + 7))]
    rw [show ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O))) : ℕ) : ℝ)
        * ((residueCard O : ℕ) : ℝ) ^ Ex * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1)
        = ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O))) : ℕ) : ℝ)
          * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1) * ((residueCard O : ℕ) : ℝ) ^ Ex
        from by ring]
    rw [mul_div_mul_right _ _ (pow_ne_zero Ex (by positivity))]

/-- ★★ **The splitTail main limit**: value `(q−1)³/(2(q²−1)(q³−1)q⁷)`. -/
private theorem zcURLim_ddMainSplit : ZcURLim ddMainSplit := by
  refine ⟨(Polynomial.X - 1) ^ 3,
    Polynomial.C 2 * ((Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1)
      * Polynomial.X ^ 7)), ?_, ?_⟩
  · refine mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (mul_ne_zero ?_ (mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero))) <;>
      · intro h
        have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
        simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h4 : (4 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 2 := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ _ := by gcongr
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd2 : ((residueCard O : ℕ) : ℚ) ^ 2 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_C]
      exact mul_ne_zero two_ne_zero
        (mul_ne_zero hd2 (mul_ne_zero hd3 (pow_ne_zero _ hqQ0)))
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hq0R : ((residueCard O : ℕ) : ℝ) ≠ 0 := by linarith
      have hM : ∀ M, ddMainSplit O π M
          = ((∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1),
              ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                / ((residueCard O : ℕ) : ℝ) ^ (2 * v + 6))
            - ∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1),
                ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                  / ((residueCard O : ℕ) : ℝ) ^ (3 * v + 4))
          + ((∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
              ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
                / ((residueCard O : ℕ) : ℝ) ^ (2 * s + 8))
            - ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
                ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
                  / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7)) := by
        intro M
        show (∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1), _) + (∑ s ∈ Finset.Ico 1 ((M + 4) / 2), _) = _
        congr 1
        · rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [Finset.mem_Ico] at hv
          rw [mul_sub, mul_one, sub_div]
          congr 1
          rw [show 3 * v + 4 = (2 * v + 6) + (v - 2) from by omega, pow_add]
          exact mul_div_mul_right _ _ (pow_ne_zero (v - 2) hq0R)
        · rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [Finset.mem_Ico] at hs
          rw [mul_sub, mul_one, sub_div]
          congr 1
          rw [show 3 * s + 7 = (2 * s + 8) + (s - 1) from by omega, pow_add]
          exact mul_div_mul_right _ _ (pow_ne_zero (s - 1) hq0R)
      have hb2 := tendsto_geom_sum_k (q := ((residueCard O : ℕ) : ℝ)) hq2R
        (k := 2) (by omega)
        ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 6 _
        tendsto_Vb_window
      have hb3 := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 4 _
        tendsto_Vb_window
      have hc2 := tendsto_geom_sum_k (q := ((residueCard O : ℕ) : ℝ)) hq2R
        (k := 2) (by omega)
        ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ) 1 8 _
        tendsto_Sc_window
      have hc3 := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ) 1 7 _
        tendsto_Sc_window
      have hval : ((((Polynomial.X - 1) ^ 3 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / ((Polynomial.C 2 * ((Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1)
            * Polynomial.X ^ 7)) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
          = ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
              * ((residueCard O : ℕ) : ℝ) ^ 2
              / ((((residueCard O : ℕ) : ℝ) ^ 2 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (2 * 2 + 6))
            - (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 2 + 4)))
          + (((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 2
              / ((((residueCard O : ℕ) : ℝ) ^ 2 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (2 * 1 + 8))
            - ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 1 + 7))) := by
        rw [digTriples_split_val, Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
        have hd2R : ((residueCard O : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by
          intro h
          exact hd2 (by exact_mod_cast h)
        have hd3R : ((residueCard O : ℕ) : ℝ) ^ 3 - 1 ≠ 0 := by
          intro h
          exact hd3 (by exact_mod_cast h)
        push_cast
        field_simp
        ring
      rw [hval]
      exact ((hb2.sub hb3).add (hc2.sub hc3)).congr (fun M => (hM M).symm)

/-- ★★★ **THE splitTail dd FIRE — CITE-FREE**:
`ZcURLim (e2DdDecFam splitTailType)`, value `(q−1)/(2q⁷(q+1)(q²+q+1))`. -/
theorem zcURLim_e2DdDecFam_splitTail : ZcURLim (e2DdDecFam splitTailType) := by
  refine ZcURLim.sandwich (E := EBd) zcURLim_ddMainSplit
    (fun O _ _ _ _ _ π _ => tendsto_EBd O π) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_split_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    apply le_add_of_nonneg_right
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Nat.cast_nonneg _)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_split_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    have hadd : ∀ a b c : ℝ, b ≤ c → a + b ≤ a + c := fun a b c h => by linarith
    refine hadd _ _ _ ?_
    have hK : 3 ≤ M + 4 := by omega
    have hBle : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2),
        ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ))
        ≤ ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by
      intro j _
      have h1 : Nat.card ((decidedSet O 4 splitTailType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4)) : Set (Coeff O 4 (M + 4)))
          ≤ Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) :=
        Nat.card_mono (Set.toFinite _) Set.inter_subset_right
      calc ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
            ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ))
          ≤ ((Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ ((residueCard O ^ (3 * (M + 4)) : ℕ) : ℝ) := by
            exact_mod_cast card_bdBox_le hK
        _ = ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by push_cast; rfl
    calc (((residueCard O : ℕ) : ℝ) - 1)
        * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
            * ((Nat.card ((decidedSet O 4 splitTailType (M + 4)
                ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        ≤ (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr with j hj
          · linarith
          · exact hBle j hj
      _ = (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2) - 1)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          rw [← Finset.sum_mul, ← mul_assoc, geom_mul]
      _ ≤ ((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr
          linarith [sub_le_self (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2))
            (zero_le_one (α := ℝ))]
      _ = EBd O π M := EBd_eq O π M

end SplitFire

/-! ## §9 — the inertTail fire -/

section InertFire

open Filter Topology

/-- **The inertTail main family**: genre (c)-irreducible, swapped form. -/
private def ddMainInert : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
      (((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
        * (((residueCard O : ℕ) : ℝ) ^ (s - 1) - 1))
        / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7)

/-- ★★ **The inertTail decomposition**. -/
private theorem e2DdDecFam_inert_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) (hπ : Irreducible π) (M : ℕ) :
    e2DdDecFam inertTailType O π M
      = ddMainInert O π M
        + (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((Nat.card ((decidedSet O 4 inertTailType (M + 4)
                  ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                  : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
  have hK : 3 ≤ M + 4 := by omega
  have hq1 : 1 ≤ residueCard O := le_trans (by omega) (two_le_residueCard O)
  have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast two_le_residueCard O
  have hAtop : ∀ s, (M + 4) / 2 ≤ s →
      (∑ t ∈ (Sc (M + 4)).filter (fun t => s + 1 ≤ t),
        Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
          : Set (Coeff O 4 (M + 4)))) = 0 := by
    intro s hs
    rw [Finset.filter_eq_empty_iff.2 (fun t ht => by
      have := mem_Sc.1 ht
      omega), Finset.sum_empty]
  have hcount := card_e2DdBox_unrolled hK hπ inertTailType
    (fun s => ∑ t ∈ (Sc (M + 4)).filter (fun t => s + 1 ≤ t),
      Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
        : Set (Coeff O 4 (M + 4))))
    hAtop (fun s hs => card_decided_deepBox_inertTail hK hπ hs)
  show ((Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ e2DdBox π (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
  rw [hcount]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.Ico 0 ((M + 4) / 2)) =>
    mul_add (((residueCard O : ℕ) : ℝ) ^ j) _ _), Finset.sum_add_distrib,
    mul_add, add_div]
  congr 1
  have hcast : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
      * ((∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
          Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ j
        * (∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
            ((Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)) := by
    intro j _
    rw [Nat.cast_sum]
  rw [Finset.sum_congr rfl hcast]
  have hswap : (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
      * (∑ t ∈ (Sc (M + 4)).filter (fun t => j + 1 + 1 ≤ t),
          ((Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)))
      = ∑ t ∈ Sc (M + 4),
          ((Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
            : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
          * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j) :=
    sum_weight_swap (Sc (M + 4)) _ _ (fun t ht => by
      have := mem_Sc.1 ht
      omega)
  rw [hswap, Finset.mul_sum, Finset.sum_div, Sc_eq (M + 4)]
  show _ = ddMainInert O π M
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_Ico] at ht
  rw [show (((residueCard O : ℕ) : ℝ) - 1)
      * (((Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
          : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
        * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j))
      = ((Nat.card ((cBox π (M + 4) t (irrPairs (ResidueField O)))
          : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ)
        * ((((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 (t - 1), ((residueCard O : ℕ) : ℝ) ^ j)) from by ring,
    geom_mul]
  rw [card_cBox hK hπ ht.1 (by omega) (fun p hp => irrPairs_snd_ne_zero hp)]
  rw [Nat.cast_mul, Nat.cast_pow]
  obtain ⟨Ex, hE1, hE2⟩ : ∃ Ex, 4 * (M + 4) - (3 * t + 7) = Ex
      ∧ 4 * (M + 4) = Ex + (3 * t + 7) := ⟨_, rfl, by omega⟩
  rw [hE1, hE2, pow_add,
    mul_comm (((residueCard O : ℕ) : ℝ) ^ Ex) (((residueCard O : ℕ) : ℝ) ^ (3 * t + 7))]
  rw [show ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O))) : ℕ) : ℝ)
      * ((residueCard O : ℕ) : ℝ) ^ Ex * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1)
      = ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O))) : ℕ) : ℝ)
        * (((residueCard O : ℕ) : ℝ) ^ (t - 1) - 1) * ((residueCard O : ℕ) : ℝ) ^ Ex
      from by ring]
  rw [mul_div_mul_right _ _ (pow_ne_zero Ex (by positivity))]

/-- ★★ **The inertTail main limit**: value `(q−1)³/(2(q²−1)(q³−1)q⁷)` (equal to the
splitTail value — the split/inert symmetry persists at every dd depth). -/
private theorem zcURLim_ddMainInert : ZcURLim ddMainInert := by
  refine ⟨(Polynomial.X - 1) ^ 3,
    Polynomial.C 2 * ((Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1)
      * Polynomial.X ^ 7)), ?_, ?_⟩
  · refine mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (mul_ne_zero ?_ (mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero))) <;>
      · intro h
        have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
        simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h4 : (4 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 2 := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ _ := by gcongr
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd2 : ((residueCard O : ℕ) : ℚ) ^ 2 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
      exact mul_ne_zero two_ne_zero
        (mul_ne_zero hd2 (mul_ne_zero hd3 (pow_ne_zero _ hqQ0)))
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hq0R : ((residueCard O : ℕ) : ℝ) ≠ 0 := by linarith
      have hM : ∀ M, ddMainInert O π M
          = (∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
              ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
                / ((residueCard O : ℕ) : ℝ) ^ (2 * s + 8))
            - ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
                ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
                  / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7) := by
        intro M
        show (∑ s ∈ Finset.Ico 1 ((M + 4) / 2), _) = _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mem_Ico] at hs
        rw [mul_sub, mul_one, sub_div]
        congr 1
        rw [show 3 * s + 7 = (2 * s + 8) + (s - 1) from by omega, pow_add]
        exact mul_div_mul_right _ _ (pow_ne_zero (s - 1) hq0R)
      have hc2 := tendsto_geom_sum_k (q := ((residueCard O : ℕ) : ℝ)) hq2R
        (k := 2) (by omega)
        ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ) 1 8 _
        tendsto_Sc_window
      have hc3 := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ) 1 7 _
        tendsto_Sc_window
      have hval : ((((Polynomial.X - 1) ^ 3 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / ((Polynomial.C 2 * ((Polynomial.X ^ 2 - 1) * ((Polynomial.X ^ 3 - 1)
            * Polynomial.X ^ 7)) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
          = ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 2
              / ((((residueCard O : ℕ) : ℝ) ^ 2 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (2 * 1 + 8))
            - ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 1 + 7)) := by
        rw [digTriples_irr_val, Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
        have hd2R : ((residueCard O : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by
          intro h
          exact hd2 (by exact_mod_cast h)
        have hd3R : ((residueCard O : ℕ) : ℝ) ^ 3 - 1 ≠ 0 := by
          intro h
          exact hd3 (by exact_mod_cast h)
        push_cast
        field_simp
        ring
      rw [hval]
      exact (hc2.sub hc3).congr (fun M => (hM M).symm)

/-- ★★★ **THE inertTail dd FIRE — CITE-FREE**:
`ZcURLim (e2DdDecFam inertTailType)`, value `(q−1)/(2q⁷(q+1)(q²+q+1))`. -/
theorem zcURLim_e2DdDecFam_inertTail : ZcURLim (e2DdDecFam inertTailType) := by
  refine ZcURLim.sandwich (E := EBd) zcURLim_ddMainInert
    (fun O _ _ _ _ _ π _ => tendsto_EBd O π) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_inert_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    apply le_add_of_nonneg_right
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Nat.cast_nonneg _)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DdDecFam_inert_eq π hπ M]
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast two_le_residueCard O
    have hadd : ∀ a b c : ℝ, b ≤ c → a + b ≤ a + c := fun a b c h => by linarith
    refine hadd _ _ _ ?_
    have hK : 3 ≤ M + 4 := by omega
    have hBle : ∀ j ∈ Finset.Ico 0 ((M + 4) / 2),
        ((Nat.card ((decidedSet O 4 inertTailType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ))
        ≤ ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by
      intro j _
      have h1 : Nat.card ((decidedSet O 4 inertTailType (M + 4)
          ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4)) : Set (Coeff O 4 (M + 4)))
          ≤ Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) :=
        Nat.card_mono (Set.toFinite _) Set.inter_subset_right
      calc ((Nat.card ((decidedSet O 4 inertTailType (M + 4)
            ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ))
          ≤ ((Nat.card (bdBox O (M + 4) : Set (Coeff O 4 (M + 4))) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ ((residueCard O ^ (3 * (M + 4)) : ℕ) : ℝ) := by
            exact_mod_cast card_bdBox_le hK
        _ = ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)) := by push_cast; rfl
    calc (((residueCard O : ℕ) : ℝ) - 1)
        * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
            * ((Nat.card ((decidedSet O 4 inertTailType (M + 4)
                ∩ deepBox O (M + 4) (j + 1) ∩ bdBox O (M + 4))
                : Set (Coeff O 4 (M + 4))) : ℝ)))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        ≤ (((residueCard O : ℕ) : ℝ) - 1)
          * (∑ j ∈ Finset.Ico 0 ((M + 4) / 2), ((residueCard O : ℕ) : ℝ) ^ j
              * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4)))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr with j hj
          · linarith
          · exact hBle j hj
      _ = (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2) - 1)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          rw [← Finset.sum_mul, ← mul_assoc, geom_mul]
      _ ≤ ((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2)
          * ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 4))
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
          gcongr
          linarith [sub_le_self (((residueCard O : ℕ) : ℝ) ^ ((M + 4) / 2))
            (zero_le_one (α := ℝ))]
      _ = EBd O π M := EBd_eq O π M

end InertFire

/-! ## §10 — CONSEQUENCES: the E2 front closes unconditionally; the mass-4 rows -/

section Consequences

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (zcURLim_e1DdDecFam)

/-- ★★★ The E2 depth-0 family limits, now UNCONDITIONAL: ramPair. -/
theorem zcURLim_e2DecFam_ramPair_final : ZcURLim (e2DecFam ramPairType) :=
  zcURLim_e2DecFam_ramPair zcURLim_e2DdDecFam_ramPair

/-- ★★★ The E2 depth-0 family limits, now UNCONDITIONAL: splitTail. -/
theorem zcURLim_e2DecFam_splitTail_final : ZcURLim (e2DecFam splitTailType) :=
  zcURLim_e2DecFam_splitTail zcURLim_e2DdDecFam_splitTail

/-- ★★★ The E2 depth-0 family limits, now UNCONDITIONAL: inertTail. -/
theorem zcURLim_e2DecFam_inertTail_final : ZcURLim (e2DecFam inertTailType) :=
  zcURLim_e2DecFam_inertTail zcURLim_e2DdDecFam_inertTail

/-- ★★★ **THE FULL `∀ σ` E2 CLOSURE, UNCONDITIONAL** — IFCG36's `hE2` premise is
GONE from the census scoreboard. -/
theorem zcURLim_e2DecFam_final (σ : FactorizationType) : ZcURLim (e2DecFam σ) :=
  zcURLim_e2DecFam_all zcURLim_e2DdDecFam_ramPair zcURLim_e2DdDecFam_splitTail
    zcURLim_e2DdDecFam_inertTail σ

/-- ★★★ **THE `{(1,1),(1,1),(2,1)}` MASS-4 ROW CLOSES CITE-FREE**
(Lean core + the owner-signed B.42, inherited; NO OM correspondence). -/
theorem coneRemainderLaw_four_splitTail : ConeRemainderLaw 4 splitTailType :=
  coneRemainderLaw_four_splitTail_of_dd zcURLim_e2DdDecFam_splitTail

/-- ★★★ **THE `{(1,2),(2,1)}` MASS-4 ROW CLOSES CITE-FREE**. -/
theorem coneRemainderLaw_four_inertTail : ConeRemainderLaw 4 inertTailType :=
  coneRemainderLaw_four_inertTail_of_dd zcURLim_e2DdDecFam_inertTail

/-- ★★ **The `{(2,1),(2,1)}` row on ONE premise**: the E2 leg is discharged; only
E1's dd term (conditional on `FactorCorrespondenceAt 2` via IFCG51) remains. -/
theorem coneRemainderLaw_four_ramPair_of_e1dd
    (h : ZcURLim (e1DdDecFam ramPairType)) : ConeRemainderLaw 4 ramPairType :=
  coneRemainderLaw_four_ramPair_of_dd h zcURLim_e2DdDecFam_ramPair

/-- ★★ **The `{(2,1),(2,1)}` row on `FactorCorrespondenceAt 2` ALONE** (IFCG51's
`zcURLim_e1DdDecFam` supplies the E1 leg). -/
theorem coneRemainderLaw_four_ramPair_of_fc2
    (hFC : FactorCorrespondenceAt 2) : ConeRemainderLaw 4 ramPairType :=
  coneRemainderLaw_four_ramPair_of_e1dd (zcURLim_e1DdDecFam hFC ramPairType)

/-- ★★★ **THE CENSUS FRONT, E2-FREE**: the all-degree decided slice now rests on
{`E1IrrLeafDecision`, `∀σ ZcURLim (e1DdDecFam σ)`, the `e ≥ 5` ramified laws, the
block bridges} — every E2 premise is DISCHARGED, cite-free. -/
theorem decidedSliceAt_all_of_e1dd_limits (hL : E1IrrLeafDecision)
    (hDd : ∀ σ : FactorizationType, ZcURLim (e1DdDecFam σ))
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_dd_limits hL hDd zcURLim_e2DdDecFam_ramPair
    zcURLim_e2DdDecFam_splitTail zcURLim_e2DdDecFam_inertTail hR hBr

/-- ★★★ **THE CENSUS FRONT on the staged cite**: `FactorCorrespondenceAt 2` replaces
the `∀σ` E1-dd premise (IFCG51), so the slice rests on {`E1IrrLeafDecision`,
`FactorCorrespondenceAt 2`, the `e ≥ 5` laws, the block bridges}. -/
theorem decidedSliceAt_all_of_fc2 (hL : E1IrrLeafDecision)
    (hFC : FactorCorrespondenceAt 2)
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_e1dd_limits hL (fun σ => zcURLim_e1DdDecFam hFC σ) hR hBr

end Consequences

end Uniformity.Density.IFCG54

end

/-! ## AXCHECK FOOTER — the translation transport, the box transport, the fibration,
and the two root lemmas expect Lean core `{propext, Classical.choice, Quot.sound}`;
the three dd fires, the unconditional E2 closures, and the two cite-free mass-4 rows
expect Lean core PLUS exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through
IFCG53's decided counts — never re-consumed.  The `_of_fc2` wirings are Lean-core
conditional (IFCG51's fires).  The C.33 cites must NOT occur. -/

#print axioms Uniformity.Density.IFCG54.deepBox_subset_e2Box
#print axioms Uniformity.Density.IFCG54.deepBox_eq_empty
#print axioms Uniformity.Density.IFCG54.decidedAt_shiftClass
#print axioms Uniformity.Density.IFCG54.decidedAt_shiftClass_iff
#print axioms Uniformity.Density.IFCG54.shift_mem_deepBox
#print axioms Uniformity.Density.IFCG54.shift_mem_ddFiber
#print axioms Uniformity.Density.IFCG54.mem_ddPairs_iff
#print axioms Uniformity.Density.IFCG54.dd_root_unique
#print axioms Uniformity.Density.IFCG54.card_decided_ddFiber
#print axioms Uniformity.Density.IFCG54.card_decided_dd_stratum
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DdDecFam_ramPair
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DdDecFam_splitTail
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DdDecFam_inertTail
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DecFam_ramPair_final
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DecFam_splitTail_final
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DecFam_inertTail_final
#print axioms Uniformity.Density.IFCG54.zcURLim_e2DecFam_final
#print axioms Uniformity.Density.IFCG54.coneRemainderLaw_four_splitTail
#print axioms Uniformity.Density.IFCG54.coneRemainderLaw_four_inertTail
#print axioms Uniformity.Density.IFCG54.coneRemainderLaw_four_ramPair_of_e1dd
#print axioms Uniformity.Density.IFCG54.coneRemainderLaw_four_ramPair_of_fc2
#print axioms Uniformity.Density.IFCG54.decidedSliceAt_all_of_e1dd_limits
#print axioms Uniformity.Density.IFCG54.decidedSliceAt_all_of_fc2
