/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C35
import Uniformity.ChapC.C44
import Uniformity.ChapC.C127

/-!
# Uniformity.ChapC.C48 — HETOW-3's full-side block identities: LANDED WHOLE

**Chapter C, NODE C.48** [lemma] [signed: A-C.1 — clauses (a)+(b); clause (c) is the
C.47 → C.40 chain, a fleet-time re-export, NOT signed here]
(`blueprint/CHAP-C_tower_grammar.md` §6; twin `leanspec/Leanspec/ChapC.lean`, the
`### NODE C.48` block).  **The signed statement is PROVED at its byte-frozen binder list.**

## The four conjuncts, and where each comes from

For `f` monic of degree `μ₂D₂`, `(u₂, e₂)`-pure with level residual `towerLabel^μ₂`
(the full-side hypotheses — the `towerLocus` membership data, unbundled):

1. `dvHgt F f 0 ≠ ⊤` — purity's LEFT endpoint: `0 ∈ dvSideSet` (the first conjunct of
   `IsDvPure`), and C.07's `DvOnSide` carries finiteness as its second conjunct.  One
   application of C.35's `dvOnSide_of_mem_dvSideSet`.
2. `¬ F.key ∣ f` — divisibility would make the `0`-digit vanish (`f %ₘ Φ′ = 0`), putting
   `dvHgt F f 0 = stageHeight 0 = ⊤` against conjunct 1.
3. `blockFactor L f = f` (at `L := T.levelDatum hπ`) — `f` itself carries the label
   (`HasLabel L f`: monic ✓, positive degree from `hμ₂`, purity is `hpure` on the nose since
   `L.u ≡ T.u₂`, `L.ℓ ≡ T.e₂`, and the residual clause is `hres` with `m := μ₂` since
   `L.r ≡ towerLabel T`), and every labelled divisor of `f` divides `f` trivially, so C.35's
   `blockFactor_eq_of_frontier` pins the `Classical.choice` — the `blockFactor_g₀` pattern
   (C67, 2026-08-20), run at the general full-side datum.
4. `mult₂ L f = μ₂` — `keyDeg₂ = (e₁f₁)·e₂·(deg towerLabel) = (e₁f₁)(e₂f₂) = D₂`
   (`towerLabel_spec`), so `mult₂ = μ₂D₂/D₂ = μ₂`.

## Guard audit (A-C.7 / D-CARRY)

* This node was a candidate row of `HX_SWEEP_2026-08-20.md` §2 and was CLEARED at §6.1:
  its exact-degree precondition `hdeg` is a HYPOTHESIS, so the D13/D-CARRY provenance gap
  cannot arise — the corpus guards this one correctly, and the proof below confirms it (the
  degree law is CONSUMED, never derived from the label).
* The `∀ (hne) (M₀) (hp)` residual hypothesis `hres` binds: purity supplies `0 ∈ dvSideSet`,
  so the side is nonempty and `DvOnSide` supplies the finite pin — the identical verdict
  C.51/C.52/C.53's headers record for the same block.
* Unconsumed signed hypotheses, kept byte-frozen: `hsq` (squarefreeness — clause (c)'s
  business), `hh`, `[IsAdicComplete]`, `[Finite (ResidueField O)]` (scope hypotheses of the
  §6 chain).  The linter is silenced rather than the signature respelled.

## Status

Sorry-free.  Axiom footprint: Lean core (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

set_option linter.unusedVariables false in
/-- **NODE C.48 — HETOW-3's full-side block identities (clauses (a)+(b)), PROVED.**  At a
monic squarefree `f` of exact degree `μ₂D₂`, `(u₂, e₂)`-pure with level residual
`towerLabel^μ₂`: the left digit is finite, the frame key does not divide `f`, `f` IS its own
`(λ, r)`-block, and the multiplicity reads `μ₂`. -/
theorem fullSide_block {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (hdeg : f.natDegree = μ₂ * T.D₂) (hpure : IsDvPure F f T.u₂ T.e₂)
    (hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂) :
    dvHgt F f 0 ≠ ⊤ ∧ ¬ F.key ∣ f ∧
    blockFactor (T.levelDatum hπ) f = f ∧ mult₂ (T.levelDatum hπ) f = μ₂ := by
  have hD₂ : 0 < T.D₂ := by
    rw [TowerDatum.D₂]
    exact Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (Nat.mul_pos T.he₂ T.hf₂)
  -- (1) the left endpoint is finite: purity's own `DvOnSide` at `0`
  have h1 : dvHgt F f 0 ≠ ⊤ := (dvOnSide_of_mem_dvSideSet hpure.1).2
  -- (2) key-freeness off (1)
  have h2 : ¬ F.key ∣ f := by
    intro hdvd
    have hz : dev F.key f 0 = 0 := by
      show f %ₘ F.key = 0
      exact (Polynomial.modByMonic_eq_zero_iff_dvd F.hmonic).mpr hdvd
    exact h1 (by rw [dvHgt, hz, F.stageHeight_zero])
  -- (3) `f` is its own block
  have hne : (dvSideSet F f T.u₂ T.e₂).Nonempty := ⟨0, hpure.1⟩
  have hlab : HasLabel (T.levelDatum hπ) f := by
    refine ⟨hf, by rw [hdeg]; exact Nat.mul_pos hμ₂ hD₂, hpure, hne, ?_⟩
    -- the pin: the side minimum's height is finite, hence a numeral
    have hminmem : dvSideMin F f T.u₂ T.e₂ hne ∈ dvSideSet F f T.u₂ T.e₂ :=
      Finset.min'_mem _ _
    have hfin : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) ≠ ⊤ :=
      (dvOnSide_of_mem_dvSideSet hminmem).2
    obtain ⟨M₀, hM₀⟩ := WithTop.ne_top_iff_exists.mp hfin
    exact ⟨M₀, hM₀.symm, μ₂, hμ₂, hres hne M₀ hM₀.symm⟩
  have h3 : blockFactor (T.levelDatum hπ) f = f :=
    blockFactor_eq_of_frontier (T.levelDatum hπ) hlab dvd_rfl (fun _ _ h => h)
  -- (4) the multiplicity: `keyDeg₂ = D₂`, so `mult₂ = μ₂D₂/D₂ = μ₂`
  have h4 : mult₂ (T.levelDatum hπ) f = μ₂ := by
    have hkd : (T.levelDatum hπ).keyDeg₂ = T.D₂ := by
      have hr : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
      rw [LevelDatum.keyDeg₂, hr, show (T.levelDatum hπ).ℓ = T.e₂ from rfl, TowerDatum.D₂]
      ring
    rw [mult₂, h3, hdeg, hkd]
    exact Nat.mul_div_cancel μ₂ hD₂
  exact ⟨h1, h2, h3, h4⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.fullSide_block

end AxCheck
