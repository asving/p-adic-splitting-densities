/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H2.FreshLaws

/-!
# Scaffold/HDischarge/H2/FreshReduction — (b)'s counting face RETIRES
  [HDISCHARGE_H2 unit U5; wave 1, deps U1/U2]

The (b-RED) reduction of `lean/blueprints/HDISCHARGE_H2.md` §3.2 at the
carriers: **`freshReads_of_digitsProd`** (statement VERBATIM from §6 H2-U5)
derives `FreshReadsLaw` — the COUNTING face of (FRESH)(b) — from the
(a′)-package field `DigitsProdLaw` + the LED §5.1 uniformity shadow
`SlotUniformLaw`.  This EXHIBITS, inside Lean, the §3.2 residue display:
(b)'s CONSUMED counting face adds NO residue beyond (a′) + LED-uniformity
(whose engine-seam suppliers are (ADM)-FULL + the (GR-B) line clause) — the
STRUCTURAL clause (affine in ONE fresh digit, UNIT slope) is strictly more
and stays priced at (VTX-DEEP), not re-counted here.

Second deliverable: the DERIVED cardinality law (the demoted `FloorsProdLaw`,
a lemma, never a package row): `J.fiber ρ q = ∏ k ∈ W.boxSlots,
J.slotCount ρ k q` (`fiber_eq_prod_slotCount`), from `DigitsProdLaw` +
`FiberSumLaw` + the per-slot digit-sum row `SlotSumLaw` declared below.

**RATIFICATION POINT (blueprint §6 H2-U5, standing).**  `SlotSumLaw`
(Σ_{z<q^d} slotDigits ρ k z q = slotCount ρ k q) must be checked against
O-9 §5.1's read convention (z = 0 encodes "strictly above" — the
`FiberSumLaw` seam convention, review finding 10) BEFORE joining the
`FreshClauses` package.  Here it is a STANDALONE named row consumed only by
the derived lemma; `FreshClauses` is untouched.

**Finding (hypothesis inventory).**  The blueprint's prose lists
`SlotUniformLaw` among the derived cardinality lemma's inputs; the Fubini
route (sum the `DigitsProdLaw` factorization over the full alphabet box,
exchange sum and product, close each slot with `SlotSumLaw`) does NOT
consume it.  It is retained in the signature for blueprint fidelity —
dropping a hypothesis is a strengthening, so keeping it is the conservative
transcription — with the linter silenced; the ratification pass may delete it.

**CEN-J SCOPE GUARD note.**  The module docstring of `FreshLaws` reserves an
`hscope : ∀ k ∈ W.onLine, P.g k ≤ W.beta k` hypothesis for consuming
theorems *where the O-9 display requires it*.  The §6 H2-U5 display carries
NO `hscope`: both theorems here are law-to-law counting reductions at the
carriers (no LED charge value is computed), so the guard has no premise to
guard.  It enters with the CEN-J value consumption (BP_IV seam), not here.

**Falsifier gates (compiled, end of file).**  NEGATIVE control: a toy
census instance `Jbad` satisfying `DigitsProdLaw` but with a digit-skewed
junction-free slot — `SlotUniformLaw` fails and `FreshReadsLaw` FAILS
(1 ≠ 2 at q = 2), so `huni` is load-bearing: `DigitsProdLaw` alone does NOT
imply fresh reads.  POSITIVE control: the uniform toy `Juni` satisfies all
four rows and both theorems fire on it, with the derived product identity
checked at q = 3 — the hypothesis set is jointly satisfiable (non-vacuity).

Proof-route note: H2-U4 (`prodBox_jointUniform`) was listed as a proof-only
dependency; the landed proofs are corpus-free (direct `Finset.prod_congr` /
`Finset.sum_prod_piFinset`), so this file does not import it — the U5
statements were and remain U4-independent.
-/

namespace LeanUrat.Scaffold.HDischarge.H2

open LeanUrat.Scaffold Finset

variable {D : CensusData}

/-- (FRESH)(b-RED), the §3.2 reduction at the carriers [H2-U5, statement
    VERBATIM from blueprint §6]: the (a′) product-box field (`DigitsProdLaw`)
    + LED §5.1 per-slot uniformity (`SlotUniformLaw`) already yield the
    COUNTING face of clause (b) (`FreshReadsLaw`).  Junction slot: exempted
    by `huni`'s guard and pinned by the agreement hypothesis inside
    `FreshReadsLaw` — its read is (c)'s business (`JunctionPinLaw`), consumed
    at CEN-J §6.4 step 4, never here.

    O-9 PIN — §5.4 clause (b) counting shadow; consumed at §6.4 step 3.
    This theorem is the Lean form of §3.2's "residue NONE beyond (a′) +
    (ADM) + (GR-B)-line": (b)'s counting face retires into the package's
    other rows.  The STRUCTURAL affine-unit-slope wording is (TRANS-DEEP)-
    family transport, priced once at §3.3/§5 — NOT discharged here. -/
theorem freshReads_of_digitsProd (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) (hprod : DigitsProdLaw W P J)
    (huni : SlotUniformLaw W P J) : FreshReadsLaw W P J := by
  intro q ρ hρ z z' hz hz' hjc
  rw [hprod q ρ hρ z hz, hprod q ρ hρ z' hz']
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  by_cases hk : (k : Fin (W.ℓ + 1)) = W.ks
  · have hmem : W.ks ∈ W.onLine := hk ▸ k.2
    have hkeq : k = ⟨W.ks, hmem⟩ := Subtype.ext hk
    rw [hkeq, hjc hmem]
  · exact huni q ρ hρ k hk (z k) (z' k) (hz k) (hz' k)

/-- The per-slot digit-sum row [H2-U5 auxiliary; NOT a `FreshClauses` field]:
    summing an on-line slot's per-digit counts over the full F_{q^d} alphabet
    recovers its height-only count — the slot-local shadow of the `FiberSumLaw`
    seam (O-9 §5.1's read convention: z = 0 encodes "strictly above", so the
    alphabet box exhausts the slot fiber).

    RATIFICATION POINT (blueprint §6 H2-U5): this row must be checked against
    O-9 §5.1's read convention before joining the package; until ratified it
    is consumed ONLY by the derived lemma `fiber_eq_prod_slotCount` below. -/
def SlotSumLaw (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) : Prop :=
  ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
    ∀ k : ↥W.onLine,
      ∑ z ∈ Finset.range (q ^ D.d), J.slotDigits ρ k z q
        = J.slotCount ρ (k : Fin (W.ℓ + 1)) q

set_option linter.unusedVariables false in
/-- The DERIVED cardinality law [H2-U5, the demoted `FloorsProdLaw` — a
    lemma, not a package row]: on each ρ-fiber the height-only count is the
    product of the per-slot counts over the whole box.  Route: `FiberSumLaw`
    opens the fiber as the alphabet-box sum of `fiberDigits`; `DigitsProdLaw`
    factorizes each summand; sum-product exchange (`Finset.sum_prod_piFinset`)
    + the `SlotSumLaw` row close the on-line slots; `Finset.prod_sdiff`
    reassembles the box.

    `huni` is carried for blueprint fidelity only (module docstring FINDING:
    the Fubini route does not consume it).

    O-9 PIN — the §6.4 step-2/step-3 aggregation seam (review finding 10's
    fiber ↔ fiberDigits tie), height-only face. -/
theorem fiber_eq_prod_slotCount (W : WindowDatum D) (P : ParentShape D W)
    (J : JointStratum D W P) (hprod : DigitsProdLaw W P J)
    (hsum : FiberSumLaw W P J) (huni : SlotUniformLaw W P J)
    (hslot : SlotSumLaw W P J) :
    ∀ (q : ℕ) (ρ : ℕ), ρ < J.rhoCount q →
      J.fiber ρ q = ∏ k ∈ W.boxSlots, J.slotCount ρ k q := by
  intro q ρ hρ
  calc J.fiber ρ q
      = ∑ z : (↥W.onLine → Fin (q ^ D.d)),
          J.fiberDigits ρ (fun k => (z k).1) q := (hsum q ρ hρ).symm
    _ = ∑ z : (↥W.onLine → Fin (q ^ D.d)),
          (∏ k ∈ W.onLine.attach, J.slotDigits ρ k ((z k).1) q)
            * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q :=
        Finset.sum_congr rfl fun z _ => hprod q ρ hρ _ (fun k => (z k).isLt)
    _ = (∑ z : (↥W.onLine → Fin (q ^ D.d)),
          ∏ k ∈ W.onLine.attach, J.slotDigits ρ k ((z k).1) q)
            * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q := by
        rw [← Finset.sum_mul]
    _ = (∏ k ∈ W.onLine.attach,
          ∑ j : Fin (q ^ D.d), J.slotDigits ρ k (j.1) q)
            * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q := by
        rw [Finset.attach_eq_univ, ← Finset.sum_prod_piFinset,
          Fintype.piFinset_univ]
    _ = (∏ k ∈ W.onLine.attach, J.slotCount ρ (k : Fin (W.ℓ + 1)) q)
            * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q := by
        refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
        rw [Fin.sum_univ_eq_sum_range (fun j => J.slotDigits ρ k j q)]
        exact hslot q ρ hρ k
    _ = (∏ k ∈ W.onLine, J.slotCount ρ k q)
            * ∏ k ∈ W.boxSlots \ W.onLine, J.slotCount ρ k q := by
        rw [Finset.prod_attach W.onLine (fun k => J.slotCount ρ k q)]
    _ = ∏ k ∈ W.boxSlots, J.slotCount ρ k q := by
        rw [mul_comm]; exact Finset.prod_sdiff W.honLine_box

/-! ## Falsifier gates (blueprint H2-U5 gate: compile + falsifier)

A toy census datum (r = 0, all ledger entries 1, so m = period·d = 1) with a
2-slot window (ℓ = 1, n = 1, monic top): `boxSlots = onLine = {0}`, junction
`ks = Fin.last 1` erased with the top.  The junction-agreement hypothesis of
`FreshReadsLaw` is then vacuous, so fresh reads assert FULL digit-blindness
of the single on-line slot — exactly what a skewed `slotDigits` refutes. -/

section Falsifier

private def D₀ : CensusData where
  r := 0
  e := ![1]
  h := ![1]
  f := ![1]
  he := by decide
  hf := by decide
  triangular := by decide
  h_coprime := by decide

private lemma D₀_pd : D₀.period * D₀.d = 1 := by decide

private def W₀ : WindowDatum D₀ where
  ℓ := 1
  hℓ := le_rfl
  n := 1
  hn := by rw [D₀_pd]
  hn2 := by rw [D₀_pd]; omega
  beta := fun _ => 0
  onLine := {0}
  ks := Fin.last 1
  monicTop := true
  hmono := by rw [D₀_pd]; simp
  boxSlots := Finset.univ.erase (Fin.last 1)
  hbox := by simp
  honLine_box := by decide
  hks_line := by simp
  hks_top := fun _ => rfl

private def P₀ : ParentShape D₀ W₀ where
  N0 := 1
  hN0 := le_rfl
  g := fun _ => 0

/-- NEGATIVE control: digit-SKEWED single on-line slot (count z + 1 at digit
    z), `fiberDigits` DEFINED as the product-box formula, so `DigitsProdLaw`
    holds while `SlotUniformLaw` fails. -/
private def Jbad : JointStratum D₀ W₀ P₀ where
  N := 1
  hN := le_rfl
  rhoCount := fun _ => 1
  slotCount := fun _ _ _ => 1
  slotDigits := fun _ _ z _ => z + 1
  fiber := fun _ _ => 0
  fiberDigits := fun _ z _ => ∏ k ∈ W₀.onLine.attach, (z k + 1)

private lemma Jbad_prod : DigitsProdLaw W₀ P₀ Jbad := by
  intro q ρ hρ z hz
  show (∏ k ∈ W₀.onLine.attach, (z k + 1)) = _
  have hempty : W₀.boxSlots \ W₀.onLine = ∅ := by decide
  rw [hempty, Finset.prod_empty, mul_one]
  rfl

/-- The falsifier: `DigitsProdLaw` ALONE does not deliver fresh reads —
    `huni` is load-bearing in `freshReads_of_digitsProd`. -/
private lemma Jbad_not_freshReads : ¬ FreshReadsLaw W₀ P₀ Jbad := by
  intro h
  have h2 := h 2 0 (by norm_num [Jbad]) (fun _ => 0) (fun _ => 1)
    (fun _ => by decide) (fun _ => by decide)
    (fun hk => absurd hk (by decide))
  revert h2; decide

private lemma Jbad_not_uniform : ¬ SlotUniformLaw W₀ P₀ Jbad := by
  intro h
  have h2 := h 2 0 (by norm_num [Jbad]) ⟨0, by decide⟩ (by decide)
    0 1 (by decide) (by decide)
  revert h2; decide

/-- POSITIVE control: the uniform toy — every digit read counts 1, heights
    count the full alphabet q^d, fiber = q^d (one on-line slot). -/
private def Juni : JointStratum D₀ W₀ P₀ where
  N := 1
  hN := le_rfl
  rhoCount := fun _ => 1
  slotCount := fun _ _ q => q ^ D₀.d
  slotDigits := fun _ _ _ _ => 1
  fiber := fun _ q => q ^ D₀.d
  fiberDigits := fun _ _ _ => 1

private lemma Juni_prod : DigitsProdLaw W₀ P₀ Juni := by
  intro q ρ hρ z hz
  show (1 : ℕ) = (∏ _k ∈ W₀.onLine.attach, 1)
    * ∏ k ∈ W₀.boxSlots \ W₀.onLine, Juni.slotCount ρ k q
  have hempty : W₀.boxSlots \ W₀.onLine = ∅ := by decide
  rw [hempty, Finset.prod_empty, Finset.prod_const_one, mul_one]

private lemma Juni_uniform : SlotUniformLaw W₀ P₀ Juni :=
  fun _ _ _ _ _ _ _ _ _ => rfl

private lemma Juni_fiberSum : FiberSumLaw W₀ P₀ Juni := by
  intro q ρ hρ
  show ∑ _z : (↥W₀.onLine → Fin (q ^ D₀.d)), (1 : ℕ) = q ^ D₀.d
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hcard : W₀.onLine.card = 1 := by decide
  rw [hcard, pow_one]

private lemma Juni_slotSum : SlotSumLaw W₀ P₀ Juni := by
  intro q ρ hρ k
  show ∑ _z ∈ Finset.range (q ^ D₀.d), (1 : ℕ) = q ^ D₀.d
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]

/-- Positive gate 1: the reduction theorem FIRES on the uniform toy. -/
private lemma Juni_freshReads : FreshReadsLaw W₀ P₀ Juni :=
  freshReads_of_digitsProd W₀ P₀ Juni Juni_prod Juni_uniform

/-- Positive gate 2: the derived cardinality law fires, checked at q = 3
    (fiber = 3 = ∏ over the single box slot of the height count 3). -/
private lemma Juni_fiberProd :
    Juni.fiber 0 3 = ∏ k ∈ W₀.boxSlots, Juni.slotCount 0 k 3 :=
  fiber_eq_prod_slotCount W₀ P₀ Juni Juni_prod Juni_fiberSum Juni_uniform
    Juni_slotSum 3 0 (by norm_num [Juni])

private lemma Juni_fiberProd_value : Juni.fiber 0 3 = 3 := by decide

end Falsifier

end LeanUrat.Scaffold.HDischarge.H2
