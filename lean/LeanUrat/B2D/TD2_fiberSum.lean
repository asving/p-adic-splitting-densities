/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD3_digitsProd

/-!
# B2D/TD2_fiberSum — `FiberSumLaw` at the ledger instance: PROVED
  [B2DEF_LEAN unit TD-2; wave 2b]

Blueprint §5 TD-2. moves_ref: §B2-DEF D.3(e)(ii) bottom-up display
"w ≥ γ ⟺ all lower digits vanish" (MOVES :2170–2173). deps: TD-0.
difficulty: medium. REUSE: T3/T5 (through TD-0's clauses); at the abstract datum
the proof is the partition count: summing the member-cylinder cards over the
`Fin (q₀^d)` digit box recovers the height-only card (`semantics` +
`digit_range`).

STATEMENT ROUND 2 (v2, 2026-08-02): the lawfulness hypothesis is now
`LedgerLawfulV2` (TDDefsV2's finite-box semantics). Under v1 this law was
VACUOUSLY satisfiable (both sides forced 0 — the TD-0/TD-3 refutation's
adjacent consequence, `TD3_countermodel.lean` docstring); at v2 the members
partition over their read vectors on a FINITE carrier, so the sum is a
genuine partition count.

PROVED (TD mop-up wave, 2026-08-08 wallclock 2026-08-02) — AT THE v2
STATEMENT, byte-unchanged. **v3-seam audit (the a1e14ef re-key protocol,
applied before proving)**: the TD-3 round-2 seams do NOT implicate this law —
the partition argument reads `semantics` + `digit_range` ONLY (no member
existence: an empty stratum sums 0 = 0; no parent/box-slot factorization: the
count is fibered over read vectors, never decomposed over blocks), and both
round-2 countermodels `cmL3`/`cmL4` SATISFY the v2 statement. Deliberately NOT
re-keyed to v3 (the TD-1 precedent: weaker hypothesis = stronger theorem,
non-vacuous by `td_lawfulV2`); v3-lawful instances consume it through
`extends`. Import widened TDDefsV2 → TD3_digitsProd for the shared box-vector
plumbing (`boxExt`) only; the statement is v2 as before.

Proof: at q = q₀ both sides pass through `LedgerSemanticsV2` to finite-box
`blockCount`s over `supportUnion`; the general partition step
`blockCount_read_partition` (proved here) fibers the member count over the
total read map into the `Fin (q₀^d)` box (`digit_range` keeps members'
reads in the box, so the off-range default branch is never hit); off q₀ the
law is vacuous by the [R2-C1] support constraint
(`ledger_rhoCount_off_support`). -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **The read-fiber partition step** (general; TD-2's core): block counts of
"`cond` ∧ the reads equal `z`" summed over the FULL `Fin m` read box recover
the block count of `cond` alone — members partition by their read vector,
which `hrange` keeps inside the box. The `Fin m` box carrier is total (the
off-range default is never hit on members), so no member is dropped and no
vector is double-counted. -/
theorem blockCount_read_partition {ι : Type*} [Fintype ι] [DecidableEq ι] (q m : ℕ) (hm : 0 < m)
    (B : Finset Coord) (cond : (Coord → ℕ) → Prop) (rd : ι → Coord)
    (hrange : ∀ x, cond x → ∀ k : ι, x (rd k) < m) :
    ∑ z : ι → Fin m,
        blockCount q B (fun x => cond x ∧ ∀ k : ι, x (rd k) = (z k : ℕ))
      = blockCount q B cond := by
  classical
  -- every block count over B is a filter card on the finite box-vector carrier
  have hcard : ∀ c : (Coord → ℕ) → Prop,
      blockCount q B c
        = (Finset.univ.filter (fun v : ↥B → Fin q => c (boxExt q B v))).card := by
    intro c
    unfold LedgerStratumData.blockCount
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  -- the total read map into the box (the off-range default is never hit on members)
  set f : (↥B → Fin q) → (ι → Fin m) := fun v k =>
    if h : boxExt q B v (rd k) < m then ⟨boxExt q B v (rd k), h⟩ else ⟨0, hm⟩
    with hf
  -- fiberwise decomposition of the member count over the read box
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := Finset.univ.filter (fun v : ↥B → Fin q => cond (boxExt q B v)))
    (t := Finset.univ) (fun v _ => Finset.mem_univ (f v))
  rw [hcard cond, hfiber]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hcard]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun hc => ?_
  constructor
  · -- reads equal z ⟹ the total read map hits z
    intro hz
    funext k
    have hk := hrange _ hc k
    simp only [hf]
    rw [dif_pos hk]
    exact Fin.ext (hz k)
  · -- the total read map hits z ⟹ the reads equal z
    intro hz k
    have hk := hrange _ hc k
    have h1 := congrFun hz k
    simp only [hf] at h1
    rw [dif_pos hk] at h1
    exact congrArg Fin.val h1

set_option linter.unusedVariables false in
/-- **TD-2**: the (F) aggregation seam at the ledger instance — digit-level
counts aggregate to the height-only fiber count. PROVED at the v2 statement
(v3-seam audit in the module docstring: not implicated). `hscope`/`hclean`
are the standing CEN-J/LED(i) guards of the TD statement family — the
partition argument never draws on them. -/
theorem ledger_fiberSum (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    FiberSumLaw W P L.ledgerJoint := by
  intro q ρ hρ
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    rw [(hL.semantics ρ hρ0).1]
    simp only [(hL.semantics ρ hρ0).2]
    exact blockCount_read_partition L.q0 (L.q0 ^ D.d)
      (pow_pos (by have := L.hq0; omega) D.d) L.supportUnion
      (L.inStratum ρ) L.slotCoord (hL.digit_range ρ hρ0)
  · rw [ledger_rhoCount_off_support L q hq] at hρ
    omega

end LeanUrat.B2D

#print axioms LeanUrat.B2D.blockCount_read_partition
#print axioms LeanUrat.B2D.ledger_fiberSum
