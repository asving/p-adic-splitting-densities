/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E57i1
import Uniformity.ChapE.E57i2
import Mathlib.Algebra.CharP.Algebra

/-!
# Uniformity.ChapE.E57i — DEC1-N3/N4/N5: the split row's ledger, field groups, and assembly

**Nodes DEC1-N3, DEC1-N4** of the GC-13 bridge plan
(`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md`, §3). `N5` (the assembly + firing) appends
to this file separately. Consumes the split row's parent `mixBlock`/`mixIface` (`E57i1`,
`DEC1-N1`), the second child `pureBlock₂`/`pureIface₂` (`E57i2`, `DEC1-N2`), and the landed
label-`1` child `E57pCert.pureBlock`/`pureIface` (`E57p.lean:535–591`, reused as-is).

**N3** builds the row's class ledger `splitCls = {a1, a2}` and block assignment `splitBlk`,
and discharges the ledger/product/disjointness field-group (`PartitionLeg`'s `hclsLin`,
`hclsHi`, `hprod`, `hdisj`, byte-copied from `scratch/DEC1_check.lean`'s `N3_spec`).

**N4** discharges the degree/purity/threshold field-group (`hdeg`, `hone`, `hpureLin`,
`hpureHi`, `hthr`, byte-copied from `N4_spec`) at the SAME row data.

TEMPLATE: `E57pCert.dup_partitionLeg_empty` (`E57p.lean:706–772`) for the ledger-membership
case bash and the Bézout-in-`FractionRing ℤ` coprimality pattern; `E57pCert.pureLeg`
(`E57p.lean:594–621`) for the per-class purity/threshold shapes.

DEPENDS: `Uniformity.ChapE.E57i1` (`mixBlock`, `mixIface`), `Uniformity.ChapE.E57i2`
(`pureBlock₂`, `pureIface₂`), `Uniformity.ChapE.E57p` (`E57pCert.pureBlock`/`pureIface`,
`PartitionLeg`, `ClassIx`, `classWeight`, transitively).

## Status

Sorry-free, axiom-free, `unsafe`-free: every declaration reports at most the Lean-core
triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial E57pCert

namespace E57iCert

/-! ## N3 — the split row's class ledger and block assignment -/

/-- class address of the factor `X + 1` (side `(1,1)`, linear label `1`, weight entry `1`). -/
def a1 : ClassIx ℚ := ((1, 1), Sum.inl ((1 : ℚ), 1))

/-- class address of the factor `X − 1` (side `(1,1)`, linear label `−1`, weight entry `1`). -/
def a2 : ClassIx ℚ := ((1, 1), Sum.inl ((-1 : ℚ), 1))

/-- the split row's two-class ledger. -/
def splitCls : Finset (ClassIx ℚ) := {a1, a2}

/-- the two class addresses are distinct (labels `1 ≠ −1` in `ℚ`). -/
theorem a1_ne_a2 : a1 ≠ a2 := by simp [a1, a2]; norm_num

/-- the split row's block assignment: `a1` (label `1`) to the landed `pureBlock`/`pureIface`,
everything else (i.e. `a2`, label `−1`) to `E57i2`'s `pureBlock₂`/`pureIface₂`. -/
noncomputable def splitBlk : ClassIx ℚ → Σ B' : BlockData flatCarrier,
    RungInterface.{0, 0, 0} flatCarrier B' :=
  fun c => if c = a1 then ⟨E57pCert.pureBlock, E57pCert.pureIface⟩
    else ⟨pureBlock₂, pureIface₂⟩

@[simp] theorem splitBlk_a1 : splitBlk a1 = ⟨E57pCert.pureBlock, E57pCert.pureIface⟩ := by
  simp [splitBlk]

@[simp] theorem splitBlk_a2 : splitBlk a2 = ⟨pureBlock₂, pureIface₂⟩ := by
  simp [splitBlk, if_neg (Ne.symm a1_ne_a2 : a2 ≠ a1)]

/-- **DEC1-N3** — the ledger/product/disjointness field-group at the split row: verbatim
`scratch/DEC1_check.lean`'s `N3_spec (mixIface) splitCls splitBlk` (the anti-drift pin). -/
theorem split_N3 :
    (∀ p q, ((p, Sum.inl q) ∈ splitCls) ↔ (p ∈ mixIface.sides ∧ q ∈ mixIface.linFac p)) ∧
    (∀ p q, ((p, Sum.inr q) ∈ splitCls) ↔ (p ∈ mixIface.sides ∧ q ∈ mixIface.hiFac p)) ∧
    (mixBlock.F = ∏ c ∈ splitCls, (splitBlk c).1.F) ∧
    (∀ c ∈ splitCls, ∀ c' ∈ splitCls, c ≠ c' →
      IsCoprime ((splitBlk c).1.F.map (algebraMap ℤ (FractionRing ℤ)))
        ((splitBlk c').1.F.map (algebraMap ℤ (FractionRing ℤ)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q
    simp only [splitCls, a1, a2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      Sum.inl.injEq, mixIface, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton, and_or_left]
  · intro p q
    simp [splitCls, a1, a2, mixIface]
  · show mixBlock.F = ∏ c ∈ ({a1, a2} : Finset (ClassIx ℚ)), (splitBlk c).1.F
    rw [Finset.prod_pair a1_ne_a2, splitBlk_a1, splitBlk_a2]
    show (X ^ 2 - 1 : Polynomial ℤ) = (X + 1) * (X - 1)
    ring
  · intro c hc c' hc' hne
    simp only [splitCls, Finset.mem_insert, Finset.mem_singleton] at hc hc'
    have hcop : IsCoprime ((E57pCert.pureBlock.F).map (algebraMap ℤ (FractionRing ℤ)))
        ((pureBlock₂.F).map (algebraMap ℤ (FractionRing ℤ))) := by
      show IsCoprime ((X + 1 : Polynomial ℤ).map (algebraMap ℤ (FractionRing ℤ)))
        ((X - 1 : Polynomial ℤ).map (algebraMap ℤ (FractionRing ℤ)))
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
      have h2 : (2 : FractionRing ℤ) ≠ 0 := by norm_num
      have hcc : (2 : FractionRing ℤ)⁻¹ + (2 : FractionRing ℤ)⁻¹ = 1 := by
        rw [← two_mul, mul_inv_cancel₀ h2]
      refine ⟨Polynomial.C ((2 : FractionRing ℤ)⁻¹), -Polynomial.C ((2 : FractionRing ℤ)⁻¹), ?_⟩
      have step : Polynomial.C ((2 : FractionRing ℤ)⁻¹) * (X + 1)
          + (-Polynomial.C ((2 : FractionRing ℤ)⁻¹)) * (X - 1)
          = Polynomial.C ((2 : FractionRing ℤ)⁻¹) + Polynomial.C ((2 : FractionRing ℤ)⁻¹) := by
        ring
      rw [step, ← Polynomial.C_add, hcc, Polynomial.C_1]
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · exact absurd rfl hne
    · rw [splitBlk_a1, splitBlk_a2]; exact hcop
    · rw [splitBlk_a1, splitBlk_a2]; exact hcop.symm
    · exact absurd rfl hne

/-! ## N4 — degree, purity, and threshold field-group at the split row -/

/-- `(X - 1 : Polynomial ℤ).natDegree = 1`. -/
theorem natDegree_X_sub_one : (X - 1 : Polynomial ℤ).natDegree = 1 := by
  have h : (X - 1 : Polynomial ℤ) = X + Polynomial.C (-1) := by
    simp [sub_eq_add_neg]
  rw [h]
  simpa using natDegree_X_add_C (-1 : ℤ)

/-- **DEC1-N4** — the degree/purity/threshold field-group at the split row: verbatim
`scratch/DEC1_check.lean`'s `N4_spec (mixIface) splitCls splitBlk` (the anti-drift pin). -/
theorem split_N4 :
    (∀ c ∈ splitCls, (splitBlk c).1.F.natDegree = classWeight mixIface c) ∧
    (∀ c ∈ splitCls, (splitBlk c).2.sides = {c.1}) ∧
    (∀ p q, (p, Sum.inl q) ∈ splitCls →
      ∃ k : ℕ, 1 ≤ k ∧ (splitBlk (p, Sum.inl q)).2.linFac p = {(q.1, k)} ∧
        (splitBlk (p, Sum.inl q)).2.hiFac p = 0) ∧
    (∀ p q, (p, Sum.inr q) ∈ splitCls →
      ∃ k : ℕ, 1 ≤ k ∧ 2 ≤ q.1 ∧ (splitBlk (p, Sum.inr q)).2.hiFac p = {(q.1, k)} ∧
        (splitBlk (p, Sum.inr q)).2.linFac p = 0) ∧
    (∀ c ∈ splitCls, (splitBlk c).1.T = mixBlock.T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [splitCls, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [splitBlk_a1]
      show (X + 1 : Polynomial ℤ).natDegree = classWeight mixIface a1
      have : (X + 1 : Polynomial ℤ).natDegree = 1 := by
        simpa using natDegree_X_add_C (1 : ℤ)
      rw [this]; show 1 = mixIface.classCount (1, 1) ((1 : ℚ), 1); simp [mixIface]
    · rw [splitBlk_a2]
      show (pureBlock₂.F).natDegree = classWeight mixIface a2
      show (X - 1 : Polynomial ℤ).natDegree = classWeight mixIface a2
      rw [natDegree_X_sub_one]
      show 1 = mixIface.classCount (1, 1) ((-1 : ℚ), 1); simp [mixIface]
  · intro c hc
    simp only [splitCls, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [splitBlk_a1]; show E57pCert.pureIface.sides = {(a1.1)}; simp [pureIface, a1]
    · rw [splitBlk_a2]; show pureIface₂.sides = {(a2.1)}; simp [pureIface₂, a2]
  · intro p q hq
    simp only [splitCls, a1, a2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      Sum.inl.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · show E57pCert.pureIface.linFac (1, 1) = {((1 : ℚ), 1)}; simp [pureIface]
      · show E57pCert.pureIface.hiFac (1, 1) = 0; simp [pureIface]
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · show pureIface₂.linFac (1, 1) = {((-1 : ℚ), 1)}; simp [pureIface₂]
      · show pureIface₂.hiFac (1, 1) = 0; simp [pureIface₂]
  · intro p q hq
    simp only [splitCls, a1, a2, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq <;> (exfalso; simp at hq)
  · intro c hc
    simp only [splitCls, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [splitBlk_a1]; rfl
    · rw [splitBlk_a2]; rfl

end E57iCert

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.E57iCert.splitCls
#print axioms Uniformity.Density.Ladder.E57iCert.splitBlk
#print axioms Uniformity.Density.Ladder.E57iCert.split_N3
#print axioms Uniformity.Density.Ladder.E57iCert.split_N4

end AxCheck
