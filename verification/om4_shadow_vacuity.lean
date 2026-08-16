import Leanspec.ChapE
/-!
# OM-4 machine witness: the landed E.39/E.40 `Prop` shadows are TRIVIALLY TRUE

`LB1Carrier` (E.39) and `MP1Carrier` (E.40) are chapter E's Lean carriers for the two
carried-open T2 obligations `(LB1)` (`EFF.T2.18`, ledger HYP.41) and `(MP1)` (`EFF.T2.23`,
ledger HYP.42).  Chapter I's `LadderObligations` (E.44) bundles them as the Display-A
conjunct `LB1 ∧ MP1`.

This file PROVES both carriers outright, for EVERY carrier/block, from nothing:

* `LB1Carrier`'s committed conclusion asks only for a block list whose `F`s multiply to
  `B.F` with matching degree sum — satisfied by the singleton `[⟨B, I⟩]` (the node's own
  SIGNATURE NOTE abbreviates away the per-block purity/length clauses, and nothing left
  excludes the trivial self-block).
* `MP1Carrier`'s committed conclusion asks for `Nonempty (RungInterface C B')` plus a purely
  numerical `(e,f)` clause.  The interface is a NUMERICAL SHADOW: nothing ties its side/
  residual data to the polynomials, so a one-side all-in-one-class interface can be
  fabricated for ANY block (`mkTrivialInterface` below), and the `(e,f)` clause is met by
  `(C.eC, C.fC)` via the carrier's own `hef`.

CONSEQUENCE (the OM-4 finding, `docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3):
as landed, the two `Prop`s carry NO mathematical content — a consumer could "discharge" the
Display-A conjunct `LB1 ∧ MP1` in Lean without doing the open mathematics, so the capstone's
conditionality census must not read these carriers as recording the obligations until the
stub stage lands the full `BlockSuite`/emission records (E.39/E.40 SIGNATURE NOTEs; the
E.40 strengthening is amendment-level, owner gate).  This does NOT weaken any landed
statement — both definitions are byte-untouched; the file only PROVES them.

Check from the repo root with:
    cd leanspec && lake env lean ../verification/om4_shadow_vacuity.lean
-/

namespace LeanspecE

universe uO uK uW

/-- A rung interface for ANY block, fabricated from the numerical shadow alone: one side
`(B.T + 1, 1)`, one linear residual class of multiplicity `B.μ`, all root counts
`C.D * B.μ`, rank carrier `PUnit`. -/
noncomputable def mkTrivialInterface {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : RungInterface.{uO, uK, uW} C B where
  sides := {(B.T + 1, 1)}
  hside_cop := by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp
                  exact ⟨Nat.coprime_one_right _, le_refl 1⟩
  hside_node := by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp
                   simp
  len := fun _ => B.μ
  hlen_pos := fun p _ => B.hμ
  hlen_sum := by simp
  linFac := fun _ => {((0 : K), B.μ)}
  hiFac := fun _ => 0
  hresdeg := by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
  rootCount := fun _ => C.D * B.μ
  haccount := by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
  classCount := fun _ _ => C.D * B.μ
  classCountHi := fun _ _ => C.D * B.μ
  hnonempty := by
    intro p hp
    refine ⟨fun q _ => ?_, fun q hq => ?_⟩
    · exact Nat.mul_pos C.hD B.hμ
    · simp at hq
  hforce := by
    intro p hp
    simp only [Finset.mem_singleton] at hp; subst hp
    refine ⟨fun q _ => ?_, fun q hq => ?_⟩
    · simpa using Nat.mul_le_mul_left C.D B.hμ
    · simp at hq
  hexhaust := by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; simp
  W := PUnit.{uW + 1}
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := PUnit.unit

/-- **The E.39 shadow is trivially true** (for every carrier, block, and rank-carrier
universe): the committed conclusion is satisfied by the singleton block list `[⟨B, I⟩]`. -/
theorem lb1Carrier_shadow_trivial {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : LB1Carrier.{uO, uK, uW} C B := by
  intro I _
  exact ⟨[⟨B, I⟩], by simp, by simp⟩

/-- **The E.40 shadow is trivially true**: the interface demand is met by the fabricated
numerical-shadow interface, and the `(e,f)` clause by the carrier's own `(eC, fC)`. -/
theorem mp1Carrier_shadow_trivial {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : MP1Carrier.{uO, uK, uW} C B := by
  intro Λ _ _ B' _ _
  exact ⟨⟨mkTrivialInterface.{uO, uK, uW} C B'⟩,
         C.eC, C.fC, C.hef.symm, dvd_rfl, dvd_rfl⟩

/-- **The E.44 record is therefore trivially true as well** — the Display-A conjunct
`LB1 ∧ MP1`, as landed, is dischargeable with no mathematics. -/
theorem ladderObligations_shadow_trivial {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : LadderObligations.{uO, uK, uW} C B :=
  ⟨lb1Carrier_shadow_trivial C B, mp1Carrier_shadow_trivial C B⟩

-- Footprint discipline: the witnesses must use Lean core only (no `sorry`, no repo axiom).
#print axioms lb1Carrier_shadow_trivial
#print axioms mp1Carrier_shadow_trivial
#print axioms ladderObligations_shadow_trivial

end LeanspecE
