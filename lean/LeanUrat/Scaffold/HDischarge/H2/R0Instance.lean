/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H2.FreshLaws

/-!
# Scaffold/HDischarge/H2/R0Instance — the canonical r = 0 (FRESH) instance
  [HDISCHARGE_H2 unit U6; wave 1, deps U1/U2 + landed C4]

Signatures of `canonicalJointR0` / `freshClauses_r0` VERBATIM from
`lean/blueprints/HDISCHARGE_H2.md` §6 (H2-U6).  This is the DE-VACUIFIER of
the H2 carrier layer (Carriers.lean docstring): the r = 0 (proved order-1)
face of (FRESH) — M08 §2.2's separation + the KEY1 standard-lift shape — as
construction + conformance over the landed C4 layer (M08 §2.1 block datum:
parent = the x^e block condition, N₀ = 1, floors g ≡ 1; `hg`/`hN0` pin that
reading in the theorem).

**Construction (prover freedom per the blueprint).**  `rhoCount := 1` (the
canonical r = 0 parent — the x^e block — has exactly ONE realization; this is
what makes every `FreshClauses` law non-vacuously quantified, the unit's
de-vacuity charge).  `slotCount` is the per-slot LED height count at the
JOINT floor max(β_k, g_k) (O-9 (E″), ℕ-subtraction = max(0,·) truncation);
`slotDigits` refines it by one F_{q^d}-alphabet layer (in-alphabet digits
uniform — M08 Lemma A's per-slot independence; out-of-alphabet reads count
0); `fiberDigits` IS the product box over the window slots (M08 §2.2's
separation made definitional: at r = 0 no cross-slot condition survives);
`fiber` aggregates it over the alphabet box (O-9 §5.1 read convention).

**Honesty perimeter.**  (i) `JunctionPinLaw` is VACUOUS at the theorem's
monic top (`hmono`), exactly M08's pinned-to-1 accounting — the pin content
is the engine-seam monicity constant, not re-proved here.  (ii) The tie of
these counting fields to the engine's constructed strata (the
`canonicalStratum1`/`census_r0_law` box census with its q-alphabet slots and
`padExp` padding) is the BP_IV wave-4 instantiation seam, NOT claimed by this
unit; what IS delivered is the package `FreshClauses` non-vacuously satisfied
by the canonical construction.  (iii) The demoted `SlotSumLaw`
(Σ_z slotDigits = slotCount) is NOT asserted (blueprint RATIFICATION POINT —
it holds for this construction only in the LED(i) regime m·N₀ − s(·) ≥ d).
-/

namespace LeanUrat.Scaffold.HDischarge.H2

open LeanUrat.Scaffold

/-- H2-U6 helper: the r = 0 per-slot height count at the JOINT floor
    max(β_k, g_k) — the (a′) LED charge shape at level N = N₀ (O-9 (E″);
    ℕ-subtraction = max(0,·), exact in the LED(i) regime). -/
noncomputable def r0SlotCount (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) (k : Fin (W.ℓ + 1)) (q : ℕ) : ℕ :=
  q ^ ((D.period * D.d) * P.N0 - D.s (max (W.beta k) (P.g k)))

/-- H2-U6 helper: the r = 0 per-digit count at an on-line slot — the height
    count refined by one F_{q^d}-alphabet layer, uniform on the alphabet
    (M08 Lemma A per-slot independence; the r = 0 reads carry NO junction
    dependence — the junction is the erased monic top), zero off-alphabet. -/
noncomputable def r0SlotDigits (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) (k : Fin (W.ℓ + 1)) (z q : ℕ) : ℕ :=
  if z < q ^ D.d then
    q ^ ((D.period * D.d) * P.N0 - D.s (max (W.beta k) (P.g k)) - D.d)
  else 0

open Classical in
/-- H2-U6 helper: the r = 0 fiber count at a prescribed on-line digit vector
    — THE PRODUCT BOX (M08 §2.2's separation as a definition: on-line slots
    contribute their digit counts, off-line box slots their height counts;
    out-of-alphabet vectors count 0). -/
noncomputable def r0FiberDigits (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) (z : ↥W.onLine → ℕ) (q : ℕ) : ℕ :=
  if ∀ k, z k < q ^ D.d then
    (∏ k ∈ W.onLine.attach, r0SlotDigits D W P k.1 (z k) q)
      * ∏ k ∈ W.boxSlots \ W.onLine, r0SlotCount D W P k q
  else 0

/-- H2-U6 helper: the r = 0 height-only fiber count — the digit-vector counts
    aggregated over the full F_{q^d}-alphabet box (O-9 §5.1 read
    convention). -/
noncomputable def r0Fiber (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) (q : ℕ) : ℕ :=
  ∑ z : (↥W.onLine → Fin (q ^ D.d)),
    r0FiberDigits D W P (fun k => (z k).1) q

set_option linter.unusedVariables false in
/-- The canonical r = 0 joint stratum built on `canonicalStratum1` (M08 §2.1
    block datum: parent = the x^e block condition, N₀ = 1, floors g ≡ 1). -/
noncomputable def canonicalJointR0 (D : CensusData) (hr : D.r = 0)
    (W : WindowDatum D) (P : ParentShape D W) : JointStratum D W P where
  N := P.N0
  hN := le_rfl
  rhoCount := fun _q => 1
  slotCount := fun _ρ k q => r0SlotCount D W P k q
  slotDigits := fun _ρ k z q => r0SlotDigits D W P k.1 z q
  fiber := fun _ρ q => r0Fiber D W P q
  fiberDigits := fun _ρ z q => r0FiberDigits D W P z q

section ProjectionLemmas

variable (D : CensusData) (hr : D.r = 0) (W : WindowDatum D)
  (P : ParentShape D W)

/-- Non-vacuity witness (the unit's de-vacuity charge): exactly one parent
    realization, so ρ = 0 satisfies every law's `ρ < rhoCount q` guard. -/
@[simp] theorem canonicalJointR0_rhoCount (q : ℕ) :
    (canonicalJointR0 D hr W P).rhoCount q = 1 := rfl

@[simp] theorem canonicalJointR0_N :
    (canonicalJointR0 D hr W P).N = P.N0 := rfl

@[simp] theorem canonicalJointR0_slotCount (ρ : ℕ) (k : Fin (W.ℓ + 1))
    (q : ℕ) :
    (canonicalJointR0 D hr W P).slotCount ρ k q = r0SlotCount D W P k q := rfl

@[simp] theorem canonicalJointR0_slotDigits (ρ : ℕ) (k : ↥W.onLine)
    (z q : ℕ) :
    (canonicalJointR0 D hr W P).slotDigits ρ k z q
      = r0SlotDigits D W P k.1 z q := rfl

@[simp] theorem canonicalJointR0_fiberDigits (ρ : ℕ) (z : ↥W.onLine → ℕ)
    (q : ℕ) :
    (canonicalJointR0 D hr W P).fiberDigits ρ z q
      = r0FiberDigits D W P z q := rfl

@[simp] theorem canonicalJointR0_fiber (ρ q : ℕ) :
    (canonicalJointR0 D hr W P).fiber ρ q = r0Fiber D W P q := rfl

end ProjectionLemmas

set_option linter.unusedVariables false in
theorem freshClauses_r0 (D : CensusData) (hr : D.r = 0)
    (W : WindowDatum D) (P : ParentShape D W)
    (hmono : W.monicTop = true) (hg : ∀ k, P.g k = 1) (hN0 : P.N0 = 1) :
    FreshClauses W P (canonicalJointR0 D hr W P) where
  floorsCharge := by
    intro q ρ hρ k hk
    rfl
  digitsProd := by
    intro q ρ hρ z hz
    change r0FiberDigits D W P z q = _
    rw [r0FiberDigits, if_pos hz]
    rfl
  fiberSum := by
    intro q ρ hρ
    rfl
  freshReads := by
    intro q ρ hρ z z' hz hz' _hks
    change r0FiberDigits D W P z q = r0FiberDigits D W P z' q
    simp only [r0FiberDigits]
    rw [if_pos hz, if_pos hz']
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    simp only [r0SlotDigits]
    rw [if_pos (hz k), if_pos (hz' k)]
  junctionPin := by
    intro hfalse
    rw [hmono] at hfalse
    exact absurd hfalse (by simp)

/-- De-vacuity gate: at every q ≥ 1 the canonical r = 0 fiber is POSITIVE —
    the constructed instance satisfies `FreshClauses` with genuinely nonzero
    counts (no empty-carrier satisfaction). -/
theorem canonicalJointR0_fiber_pos (D : CensusData) (hr : D.r = 0)
    (W : WindowDatum D) (P : ParentShape D W) {q : ℕ} (hq : 0 < q) (ρ : ℕ) :
    0 < (canonicalJointR0 D hr W P).fiber ρ q := by
  have hd : 0 < q ^ D.d := pow_pos hq _
  rw [canonicalJointR0_fiber, r0Fiber]
  refine Finset.sum_pos (fun z _ => ?_) ⟨fun _ => ⟨0, hd⟩, Finset.mem_univ _⟩
  have hz : ∀ k : ↥W.onLine, ((z k : Fin (q ^ D.d)) : ℕ) < q ^ D.d :=
    fun k => (z k).2
  rw [r0FiberDigits, if_pos hz]
  exact Nat.mul_pos
    (Finset.prod_pos fun k _ => by
      rw [r0SlotDigits, if_pos (hz k)]; exact pow_pos hq _)
    (Finset.prod_pos fun k _ => pow_pos hq _)

end LeanUrat.Scaffold.HDischarge.H2
