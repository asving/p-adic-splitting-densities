/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H97r3
import Uniformity.ChapG.G36
import Uniformity.ChapG.G61c
import Uniformity.ChapG.G61I

/-!
# Uniformity.ChapH.H97r4 — the sharp peel branch and the `n = 3` counting recursion

**Chapter H, node-support file `H97r4`** (unit OM-1, `docs/openmath-campaign/
OM-1_n3-rate_2026-08-16.md`, steps S5 + S6 + S7). **This file is the unit's NEW
mathematics** — the step that upgrades the landed `q^(−N/2)` drainage rate to the rate-1
bound `RateSpecies` demands:

* **S5, the sharp peel reduction.** If an undecided level-`N` class has a lift with a
  unit-derivative root `r`, its quadratic cofactor class is `n = 2`-UNDECIDED at the SAME
  level (`decidedAt_of_peel_decided`, via the lossless congruences `exists_root_congr` /
  `peel_congr` of H97r1); and the record `c ↦ (r mod π^N, cofactor class)` is injective
  (the cubic is reconstructed from `(r, g)` by `ring` identities plus `F(r) = 0`). With
  chapter G's EXACT `n = 2` law `undecidedCount O 2 N = q^N` (G.36) this counts the branch:

      #(undecidedSet O 3 N ∩ peelBranch N) ≤ q^N · q^N = q^(2N)   (N ≥ 1).

  The landed alternative (leancheck `card_peelSet_le`, tangency-pinning) gives only
  `q^(5M)` at even levels `2M` — rate `q^(−N/2)`, not RateSpecies-shaped.
* **S6, the dichotomy.** `undecidedSet O 3 N ⊆ (∩ peelBranch) ∪ (∩ tripleSet)` for `N ≥ 1`:
  by the structure theorem (H97r1 `cubic_structure`) the only other residual shape is
  rootless, and those classes are `c3inert`-DECIDED at level 1 (G.61c) hence at level `N`
  (`preimage_decidedSet_subset`) — contradicting undecidedness. Adapts leancheck
  `N3Drain.undecidedSet_subset` (Tang form).
* **S7, the recursion.** Combining with H97r3's sharp triple count:

      undecidedCount O 3 (M+3) ≤ q^(2(M+3)) + q⁴ · undecidedCount O 3 M.

  Certification: `verification/om1_n3_rate_check.py` V-T2 (peel: zero decided cofactors,
  zero record collisions, counts within `q^(2N)`, the `n = 2` law re-verified numerically)
  and V-T3 (the recursion on enumerated counts, `p = 2, 3`).

**PROVENANCE.** `peel_const` and `proj_one_eq_liftRes1` are backports from the `leancheck`
sidecar @ `b00b0505` (`UniformityCheck/N3Base.lean`, `UniformityCheck/N3Drain.lean`),
namespace-adapted; everything else in this file is NEW (this unit), consuming only landed
`leanfinal` declarations and the H97r1–r3 ports.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. Two small ports -/

section Ports

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The constant term of the cofactor: `a₀ = -r · g₀` at a root `r`. (Port:
`N3Base.peel_const`.) -/
theorem peel_const (a : Fin 3 → O) (r : O) (hr : (monicPoly a).eval r = 0) :
    a 0 = -(r * peel a r 0) := by
  rw [cubic_eval] at hr
  simp only [peel_zero]
  linear_combination hr

variable [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The level-1 class of `a` is the residue coefficient vector of `a`, read through
`res1Equiv`. (Port: `N3Drain.proj_one_eq_liftRes1`.) -/
theorem proj_one_eq_liftRes1 (a : Fin 3 → O) : proj O 3 1 a = Menu.liftRes1 (resVec a) := by
  funext i
  refine (Menu.res1Equiv O).injective ?_
  show Menu.res1Equiv O (Ideal.Quotient.mk _ (a i)) = Menu.res1Equiv O ((Menu.res1Equiv O).symm (resVec a i))
  rw [Menu.res1Equiv_mk, RingEquiv.apply_symm_apply]
  rfl

end Ports

/-! ## 2. S5 — the sharp peel reduction -/

section PeelSharp

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The branch-(b) stratum, in root form.** A level-`N` class with a lift having a root at
which the derivative is a unit. By `cubic_structure`, every class outside `tripleSet` whose
residue cubic has any root at all lies here. -/
def peelBranch (N : ℕ) : Set (Coeff O 3 N) :=
  {c | ∃ (a : Fin 3 → O) (r : O), proj O 3 N a = c ∧ (monicPoly a).eval r = 0 ∧
    IsUnit ((monicPoly a).derivative.eval r)}

/-- **S5, the reduction (LEMMA B, sharpened).** If the quadratic cofactor's level-`N` class is
`σ′`-decided, the cubic's level-`N` class is decided (with type `(1,1) ::ₘ σ′`): any lift `a′`
has a root `r′ ≡ r (mod π^N)` (`exists_root_congr`), its cofactor is in the cofactor's class
(`peel_congr` — the peel is LOSSLESS), so its type is pinned. Contrapositively an undecided
cubic class has an `n = 2`-UNDECIDED cofactor class — the hinge that lets G.36's exact law
count the peel branch. -/
theorem decidedAt_of_peel_decided {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {N : ℕ}
    (hN : 1 ≤ N) {r : O} (hr : (monicPoly a).eval r = 0)
    (hu : IsUnit ((monicPoly a).derivative.eval r)) {σ' : FactorizationType}
    (hdec : DecidedAt O 2 σ' N (proj O 2 N (peel a r))) :
    DecidedAt O 3 ⟨(1, 1) ::ₘ σ'.data⟩ N (proj O 3 N a) := by
  refine decidedAt_of_congr hπ (fun a' hcong => ?_)
  obtain ⟨r', hr', hrr⟩ := exists_root_congr hπ hN hr hu hcong
  have hpeel := peel_congr (π := π) (N := N) hcong hrr
  have hproj : proj O 2 N (peel a' r') = proj O 2 N (peel a r) :=
    ((proj_eq_iff_dvd hπ (peel a r) (peel a' r')).2 hpeel).symm
  have htype : typeOf (monicPoly (peel a' r')) = σ' := hdec _ hproj
  apply FactorizationType.ext
  rw [cubic_peel a' r' hr', typeOf_linear_mul (monicPoly_monic (peel a' r')) r', htype]

/-- **S5, the count.** The undecided part of the peel branch injects into
`(root mod π^N) × (n = 2-undecided classes)`, and G.36 evaluates the second factor EXACTLY:

    #(undecidedSet O 3 N ∩ peelBranch N) ≤ q^N · q^N = q^(2N)   (N ≥ 1). -/
theorem card_undecidedPeel_le {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N) :
    Nat.card (undecidedSet O 3 N ∩ peelBranch (O := O) N : Set (Coeff O 3 N))
      ≤ residueCard O ^ (2 * N) := by
  classical
  -- (a) choose, for each class, a lift and a unit-derivative root
  have key : ∀ c : (undecidedSet O 3 N ∩ peelBranch (O := O) N : Set (Coeff O 3 N)),
      ∃ p : (Fin 3 → O) × O, proj O 3 N p.1 = (c : Coeff O 3 N) ∧
        (monicPoly p.1).eval p.2 = 0 ∧ IsUnit ((monicPoly p.1).derivative.eval p.2) := by
    rintro ⟨c, hcu, a, r, ha, hr, hu⟩
    exact ⟨(a, r), ha, hr, hu⟩
  choose f hf1 hf2 hf3 using key
  -- (b) the cofactor class is n = 2-UNDECIDED (the reduction, contrapositively)
  have hmemQ : ∀ c, proj O 2 N (peel (f c).1 (f c).2) ∈ undecidedSet O 2 N := by
    intro c σ' hdec
    have hdec3 := decidedAt_of_peel_decided hπ hN (hf2 c) (hf3 c) hdec
    rw [hf1 c] at hdec3
    exact c.2.1 _ hdec3
  -- (c) the record `c ↦ (r mod π^N, cofactor class)` is injective: the cubic is reconstructed
  -- from `(r, g)` — `a₂ = g₁ − r`, `a₁ = g₀ − g₁r` (ring identities), `a₀ = −r·g₀` (the root)
  have hinj : Function.Injective
      (fun c : (undecidedSet O 3 N ∩ peelBranch (O := O) N : Set (Coeff O 3 N)) =>
        ((Ideal.Quotient.mk ((maximalIdeal O) ^ N) (f c).2,
          (⟨proj O 2 N (peel (f c).1 (f c).2), hmemQ c⟩ :
            (undecidedSet O 2 N : Set (Coeff O 2 N)))) :
          Res O N × (undecidedSet O 2 N : Set (Coeff O 2 N)))) := by
    intro c c' hcc
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
    obtain ⟨e1, e2⟩ := hcc
    have hrr : π ^ N ∣ ((f c').2 - (f c).2) :=
      dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ N _).1 (Ideal.Quotient.eq.1 e1))
    have hg : ∀ i, π ^ N ∣ (peel (f c').1 (f c').2 i - peel (f c).1 (f c).2 i) :=
      (proj_eq_iff_dvd hπ _ _).1 e2
    have hg0 := hg 0
    have hg1 := hg 1
    simp only [peel_zero, peel_one] at hg0 hg1
    -- reconstruct the coefficient congruences
    have h2 : π ^ N ∣ ((f c').1 2 - (f c).1 2) := by
      have hid : (f c').1 2 - (f c).1 2
          = (((f c').1 2 + (f c').2) - ((f c).1 2 + (f c).2)) - ((f c').2 - (f c).2) := by ring
      rw [hid]
      exact dvd_sub hg1 hrr
    have h1 : π ^ N ∣ ((f c').1 1 - (f c).1 1) := by
      -- `a₁ = g₀ − g₁·r`
      have hid : (f c').1 1 - (f c).1 1
          = (((f c').1 1 + (f c').1 2 * (f c').2 + (f c').2 ^ 2)
              - ((f c).1 1 + (f c).1 2 * (f c).2 + (f c).2 ^ 2))
            - (((f c').1 2 + (f c').2) - ((f c).1 2 + (f c).2)) * (f c').2
            - ((f c).1 2 + (f c).2) * ((f c').2 - (f c).2) := by ring
      rw [hid]
      exact dvd_sub (dvd_sub hg0 (hg1.mul_right _)) (hrr.mul_left _)
    have h0 : π ^ N ∣ ((f c').1 0 - (f c).1 0) := by
      -- `a₀ = −r·g₀` at the chosen root, for BOTH classes
      have hc0 := peel_const (f c).1 (f c).2 (hf2 c)
      have hc0' := peel_const (f c').1 (f c').2 (hf2 c')
      have hid : (f c').1 0 - (f c).1 0
          = -(((f c').2 - (f c).2) * (peel (f c').1 (f c').2 0))
            - (f c).2 * ((peel (f c').1 (f c').2 0) - (peel (f c).1 (f c).2 0)) := by
        rw [hc0, hc0']
        ring
      rw [hid]
      exact dvd_sub (Dvd.dvd.neg_right (hrr.mul_right _)) ((hg 0).mul_left _)
    have hall : ∀ i, π ^ N ∣ ((f c').1 i - (f c).1 i) := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hfin : proj O 3 N (f c).1 = proj O 3 N (f c').1 :=
      (proj_eq_iff_dvd hπ _ _).2 hall
    rw [hf1 c, hf1 c'] at hfin
    exact Subtype.ext hfin
  -- (d) the count, through G.36's EXACT n = 2 law
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_res] at hle
  have h2card : Nat.card (undecidedSet O 2 N : Set (Coeff O 2 N)) = residueCard O ^ N := by
    have h := undecidedCount_two_eq (O := O) N
    simpa only [undecidedCount] using h
  rw [h2card, ← pow_add] at hle
  calc Nat.card (undecidedSet O 3 N ∩ peelBranch (O := O) N : Set (Coeff O 3 N))
      ≤ residueCard O ^ (N + N) := hle
    _ = residueCard O ^ (2 * N) := by ring_nf

end PeelSharp

/-! ## 3. S6 — the dichotomy -/

section Dichotomy

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **S6.** Every undecided class at level `N ≥ 1` has a unit-derivative root or is residually
a perfect cube: the residually-rootless shape of `cubic_structure` is `c3inert`-decided at
level 1 (G.61c) hence at level `N`, contradicting undecidedness. -/
theorem undecidedSet_subset_sharp {N : ℕ} (hN : 1 ≤ N) :
    undecidedSet O 3 N
      ⊆ (undecidedSet O 3 N ∩ peelBranch (O := O) N)
        ∪ (undecidedSet O 3 N ∩ tripleSet (O := O) N) := by
  intro c hc
  obtain ⟨a, ha⟩ := proj_surjective O 3 N c
  rcases cubic_structure a with ⟨r, hr, hu⟩ | hno | ⟨γ, hγ⟩
  · exact Or.inl ⟨hc, a, r, ha, hr, hu⟩
  · exfalso
    have hdec1 : DecidedAt O 3 c3inert 1 (Menu.liftRes1 (resVec a)) := inert3_decided hno
    have hmem : c ∈ (coeffFactor (O := O) 3 hN) ⁻¹' (decidedSet O 3 c3inert 1) := by
      show coeffFactor (O := O) 3 hN c ∈ decidedSet O 3 c3inert 1
      rw [← ha, coeffFactor_proj, proj_one_eq_liftRes1]
      exact hdec1
    exact hc c3inert (preimage_decidedSet_subset (O := O) hN hmem)
  · exact Or.inr ⟨hc, a, γ, ha, hγ⟩

end Dichotomy

/-! ## 4. S7 — the counting recursion -/

section Recursion

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **S7, THE SHARP RECURSION (ℕ form).** For every `M`,

    undecidedCount O 3 (M+3) ≤ q^(2(M+3)) + q⁴ · undecidedCount O 3 M.

The peel branch contributes at most `q^(2(M+3))` (S5, through G.36) and the triple branch at
most `q⁴·u(M)` (H97r3's mixed-precision count); S6 says there is nothing else. -/
theorem undecidedCount_three_recursion (M : ℕ) :
    undecidedCount O 3 (M + 3)
      ≤ residueCard O ^ (2 * (M + 3)) + residueCard O ^ 4 * undecidedCount O 3 M := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hN : 1 ≤ M + 3 := by omega
  have hsub := undecidedSet_subset_sharp (O := O) (N := M + 3) hN
  have hcard : undecidedCount O 3 (M + 3)
      ≤ Nat.card (undecidedSet O 3 (M + 3) ∩ peelBranch (O := O) (M + 3) :
          Set (Coeff O 3 (M + 3)))
        + Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
            Set (Coeff O 3 (M + 3))) := by
    rw [undecidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    calc (undecidedSet O 3 (M + 3)).ncard
        ≤ ((undecidedSet O 3 (M + 3) ∩ peelBranch (O := O) (M + 3))
            ∪ (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
  calc undecidedCount O 3 (M + 3)
      ≤ Nat.card (undecidedSet O 3 (M + 3) ∩ peelBranch (O := O) (M + 3) :
          Set (Coeff O 3 (M + 3)))
        + Nat.card (undecidedSet O 3 (M + 3) ∩ tripleSet (O := O) (M + 3) :
            Set (Coeff O 3 (M + 3))) := hcard
    _ ≤ residueCard O ^ (2 * (M + 3)) + residueCard O ^ 4 * undecidedCount O 3 M :=
        Nat.add_le_add (card_undecidedPeel_le hπ hN) (card_undecidedTriple_sharp hπ M)

end Recursion

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.peel_const
#print axioms Uniformity.Density.proj_one_eq_liftRes1
#print axioms Uniformity.Density.decidedAt_of_peel_decided
#print axioms Uniformity.Density.card_undecidedPeel_le
#print axioms Uniformity.Density.undecidedSet_subset_sharp
#print axioms Uniformity.Density.undecidedCount_three_recursion

end AxCheck
