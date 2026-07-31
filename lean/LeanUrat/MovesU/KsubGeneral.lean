/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers
import LeanUrat.MovesS.N2ScsData

/-!
# M09 — the `cl11_ksub` ledger row at GENERAL n: `KsubM1C1T` from DEG-CONS alone

Open-math unit M09 (`lean/notes/openmath/M09-cl11-general_attempt.md`), landed per
the dual-agreement record in `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
(OPEN-MATH FIRST RETURNS, 2026-07-31): **DUAL-PROVED** — Fable and the Codex twin
produced INDEPENDENT IDENTICAL proofs (pigeonhole from `DegCons.size_sum` alone:
m·e ≤ e forces m = 1; c ≤ m and c ≠ 0 force c = 1).  Formalization record:
`lean/notes/M09_FORMALIZED_2026-07-31.md`.

## Result

`KsubM1C1T T` is a theorem of DEG-CONS alone, at every n and every table: if all
members of an outcome at a degree-e state (1 ≤ e ≤ n) have size e, the DEG-CONS
sum law Σ sizes ≤ e reads m·e ≤ e, and e ≥ 1 forces m = 1; the continuing members
are a filter-sublist of the members, so c ≤ m = 1, and c ≠ 0 gives c = 1.

## KEEP-AND-SUPPLY wiring (Q6 record; row deletion is a future queue decision)

Both `cl11_ksub` rows are KEPT unchanged; THIS module is their derived supply:

* `BridgeKernels.cl11_ksub` (BridgeKernels.lean:267, type `KsubM1C1T C.T`) — any
  future `BridgeKernels` instantiation supplies the row by
  `UCarriers.cl11_ksub_general C`.
* `CapstoneLedger.cl11_ksub` (DefsLedger.lean:794, type `KsubM1C1T C.T`) — same
  supply; the IB-F3 assembly (`bridgeCapstoneLedger`, BridgeMk.lean:121) keeps its
  verbatim `cl11_ksub := BD.BK.cl11_ksub` transport (no definition change), with
  the BK-side row now derivable at source.
* n = 2 instance: `ksubM1C1T_n2` (SynK1_ksubN2.lean, the SYN2-K1 roster walk)
  REMAINS the recorded instance discharge; `ksubM1C1T_n2_viaGeneral` below
  re-derives it from the general theorem + `n2hdc` (N2ScsData.lean), exhibiting
  the subsumption WITHOUT touching the SYN2-K1 record.

No new axiom, no new obligation: the proof consumes only the carried `C.hdc`
(CL-11's DEG-CONS), which remains the carried burden it already was.

No sorries in this file; Lean-core footprint (see EOF comment).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open LeanUrat.MovesS

/-- M09 GENERAL n: the (K-SUB) m = 1 classification `KsubM1C1T` holds at ANY table
    satisfying DEG-CONS (`MovesS.DegCons`) — pigeonhole on the member-size sum:
    all members of size e, sizes summing to ≤ e, forces m = 1; c ≤ m and c ≠ 0
    force c = 1.  Consumes only `DegCons.size_sum` (not even `size_pos`). -/
theorem ksubM1C1T_of_degCons {n : ℕ} (T : MovesS.TableShape n)
    (hdc : MovesS.DegCons T) : KsubM1C1T T := by
  intro e he τ o hall hc
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hlen : 1 ≤ (T.odata e τ o).mem.length :=
    List.length_pos_iff.mpr (T.odata e τ o).hm
  -- the size sum is m·e
  have hmap : (T.odata e τ o).mem.map Member.size
      = List.replicate (T.odata e τ o).mem.length e := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hb
    exact hall μ hμ
  have hsum : (T.odata e τ o).mem.length * e ≤ e := by
    have := hdc.size_sum e he τ o
    rwa [hmap, List.sum_replicate, smul_eq_mul] at this
  -- pigeonhole: m·e ≤ e with e ≥ 1 forces m ≤ 1
  have hm1 : (T.odata e τ o).mem.length = 1 := by
    rcases Nat.lt_or_ge (T.odata e τ o).mem.length 2 with h | h
    · omega
    · exfalso
      have : 2 * e ≤ (T.odata e τ o).mem.length * e :=
        Nat.mul_le_mul_right e h
      omega
  have hcm : (T.odata e τ o).c ≤ (T.odata e τ o).m :=
    List.length_filter_le _ _
  refine ⟨hm1, ?_⟩
  have hme : (T.odata e τ o).m = 1 := hm1
  omega

/-- The ledger-row form: at ANY real carrier pack `C : UCarriers n` the
    `cl11_ksub` row (`BridgeKernels.cl11_ksub` / `CapstoneLedger.cl11_ksub`,
    both of type `KsubM1C1T C.T`) is DERIVABLE from the carried `C.hdc`
    (CL-11 DEG-CONS) — THE keep-and-supply term for both rows, at every n
    and every p. -/
theorem UCarriers.cl11_ksub_general {n : ℕ} (C : UCarriers n) :
    KsubM1C1T C.T :=
  ksubM1C1T_of_degCons C.T C.hdc

/-- M09 Corollary 2 (the `KsubM1C1T` docstring's parenthetical, made precise):
    under full DEG-CONS the ∃-a-size-e-member guard already forces m = 1 and
    all-members-size-e — so the two published guard readings of (K-SUB)
    coincide (the converse direction is immediate from `Outcome.hm`).
    This direction consumes both `size_pos` and `size_sum`. -/
theorem ksub_exists_form {n : ℕ} (T : MovesS.TableShape n)
    (hdc : MovesS.DegCons T) :
    ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
      (∃ μ ∈ (T.odata e τ o).mem, μ.size = e) →
      (T.odata e τ o).mem.length = 1 ∧ ∀ μ ∈ (T.odata e τ o).mem, μ.size = e := by
  intro e he τ o hex
  obtain ⟨μ, hμ, hsz⟩ := hex
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  obtain ⟨s, t, hst⟩ := List.append_of_mem hμ
  have hsum : ((T.odata e τ o).mem.map Member.size).sum ≤ e := hdc.size_sum e he τ o
  rw [hst] at hsum
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hsz] at hsum
  have hs0 : (s.map Member.size).sum = 0 ∧ (t.map Member.size).sum = 0 := by omega
  have hsnil : s = [] := by
    by_contra hne
    obtain ⟨ν, hν⟩ := List.exists_mem_of_ne_nil _ hne
    have hν' : ν ∈ (T.odata e τ o).mem := by rw [hst]; simp [hν]
    have h1 : 1 ≤ ν.size := hdc.size_pos e τ o ν hν'
    have hle : ν.size ≤ (s.map Member.size).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map_of_mem hν)
    omega
  have htnil : t = [] := by
    by_contra hne
    obtain ⟨ν, hν⟩ := List.exists_mem_of_ne_nil _ hne
    have hν' : ν ∈ (T.odata e τ o).mem := by rw [hst]; simp [hν]
    have h1 : 1 ≤ ν.size := hdc.size_pos e τ o ν hν'
    have hle : ν.size ≤ (t.map Member.size).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map_of_mem hν)
    omega
  have heq : (T.odata e τ o).mem = [μ] := by rw [hst, hsnil, htnil]; rfl
  refine ⟨by rw [heq]; rfl, ?_⟩
  intro ν hν
  rw [heq] at hν
  simp only [List.mem_singleton] at hν
  rw [hν]; exact hsz

/-- SUBSUMPTION CROSS-CHECK (records stay): the SYN2-K1 roster walk's conclusion
    `KsubM1C1T n2T` re-derived from the general theorem + the instance DEG-CONS
    term `n2hdc` (N2ScsData.lean).  `ksubM1C1T_n2` (SynK1_ksubN2.lean) is NOT
    edited — it remains the recorded n = 2 instance discharge and a roster-walk
    cross-check of this theorem. -/
theorem ksubM1C1T_n2_viaGeneral : KsubM1C1T n2T :=
  ksubM1C1T_of_degCons n2T n2hdc

end LeanUrat.MovesU

/-
#print axioms record (2026-07-31, this file at landing):

  LeanUrat.MovesU.ksubM1C1T_of_degCons     : [propext, Classical.choice, Quot.sound]
  LeanUrat.MovesU.UCarriers.cl11_ksub_general : [propext, Classical.choice, Quot.sound]
  LeanUrat.MovesU.ksub_exists_form         : [propext, Classical.choice, Quot.sound]
  LeanUrat.MovesU.ksubM1C1T_n2_viaGeneral  : [propext, Classical.choice, Quot.sound]

Lean-core only; zero sorries.
-/
