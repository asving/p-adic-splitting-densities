/-  MovesV unit `skeleton_finite` — SKELETON FINITENESS AT EVERY n.
    Lean side of O-13 Theorem 1 (letters; = T-4 SP-FIN), per the VERIFIED
    O-13 leaf `lean/notes/openmath/O13_phaseB_attempt_rev2.md` (2-pass
    accepted; the catalogue-encoding route): letters inject into the
    explicit finite code type `MovesSp.Code n = Fin (n²+3n+12) → Fin (n+2)`
    via `MovesSp.encode` — the injectivity + cardinality work is ALREADY
    formalized in `MovesSp/SP2_encodeInj`/`SP2_encodeCard`/`SP2_finThm`
    (theorem `MovesSp.SP_FIN`, sorry-free, Lean-core). This unit transports
    it across the definitional equivalence `Skeleton n ≃ ↥(SnRaw n)`
    (a `Skeleton n` IS a catalogue-membered species, MovesV/Defs:181) and
    closes the n = 0 corner (SP_FIN's row carries 1 ≤ n): at n = 0 the
    catalogue is EMPTY — RootStage 0 forces W = 0 against WellTyped's
    1 ≤ W, and SuccStep only extends existing members — so `Skeleton 0`
    is `IsEmpty`, hence finite.

    CONSUMER RECORD (the hfin hypothesis row census, 2026-07-31):
    `hfin : Finite (Skeleton n)` rows live at V7_ts:70 (`tableShape_inst`,
    the row's origin), TV_E1 (ctsTable/ctsTable_pins/measuredOf chain),
    TV_E3, TV_E4, TV_E5a, TV_F2b, TV_G3:447, and the TV-E7 assembly
    `ledgerIV_inst_assembly` (TV_E7:56). Every such row is now
    dischargeable at EVERY n by `skeleton_finite n` (or by the `Finite`
    instance below via `inferInstance`). NOT wired here: whether
    `ledgerIV_inst` (V7_livC:71, the one live sorry waiting on exactly
    this) gains `hfin` or has it discharged instance-side remains the
    TV-E7-header EXECUTION-TIME RATIFICATION ITEM (statement fence —
    the hfin row addition was a TV_E7-header escalation, PARKED under the
    math-first regime); its in-place fill is ALSO import-blocked (TV_E6/
    TV_E7 import V7_livC). This unit supplies the instance theorem ONLY.

    SUBSUMPTION NOTE (files untouched by design): the ad-hoc per-n
    instances `skeleton1_finite` (TV_E8:32, via V1_witnessC's Subsingleton)
    and `skeleton3_finite` (V2_skeleton:15, via SP_FIN at n = 3) are
    SUBSUMED by `skeleton_finite`; they stand as compiled historical
    witnesses and nothing is re-pointed.

    M1 HYGIENE CHECK (2026-07-31): no compiled countermodel or negation
    witness in-corpus concerns `Finite (Skeleton n)` (grep over
    quarantine + *negWitness*/*counter* files: the only "skeleton" hits,
    HC2/U10d_negWitness:53 and HC2/HK05_countermodelGate:93, use the word
    informally for E-phase sorried statements) — the new global `Finite`
    instance changes no countermodel's scope.

    deps: MovesV/Defs (Skeleton), MovesSp/SP2_finThm (SP_FIN).
    Consumers: none at HEAD (wiring parked, see above). -/
import LeanUrat.MovesV.Defs
import LeanUrat.MovesSp.SP2_finThm

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- A `Skeleton n` is DEFINITIONALLY a catalogue member: the structure
`⟨sp, mem⟩` (MovesV/Defs:181) against the subtype `↥(MovesSp.SnRaw n)` —
both directions are `rfl` by structure eta. -/
def skeletonEquivSnRaw (n : ℕ) : Skeleton n ≃ ↥(MovesSp.SnRaw n) where
  toFun s := ⟨s.sp, s.mem⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The n = 0 corner: the catalogue at n = 0 is EMPTY. Root case:
`RootStage 0` pins `s.W = 0` while `Coherent`'s `WellTyped` clause demands
`1 ≤ s.W`. Step case: a `SuccStep` extension of a member needs a member,
so the induction hypothesis closes it outright. -/
theorem inCatalogue_zero_elim {s : MovesSp.Species}
    (h : MovesSp.InCatalogue 0 s) : False := by
  induction h with
  | root hroot =>
      obtain ⟨⟨_, _, _, hW⟩, hcoh, _⟩ := hroot
      have h1 := hcoh.1.2.2.1
      omega
  | step _ _ ih => exact ih

instance : IsEmpty (Skeleton 0) :=
  ⟨fun s => inCatalogue_zero_elim s.mem⟩

/-- THE UNIT THEOREM (O-13 Theorem 1, Lean side): `Skeleton n` is finite
at EVERY n — n = 0 by catalogue emptiness, n ≥ 1 by the SP-FIN encoding
injection (`MovesSp.SP_FIN`) transported across `skeletonEquivSnRaw`.
Discharges every `hfin : Finite (Skeleton n)` hypothesis row (consumer
census in the file header; wiring parked per the statement fence). -/
theorem skeleton_finite (n : ℕ) : Finite (Skeleton n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · infer_instance
  · haveI : Finite ↥(MovesSp.SnRaw n) := ((MovesSp.SP_FIN n hn).1).to_subtype
    exact Finite.of_equiv _ (skeletonEquivSnRaw n).symm

instance (n : ℕ) : Finite (Skeleton n) := skeleton_finite n

/-- Noncomputable `Fintype`, as a def NOT an instance (mathlib practice:
keep the `Finite` instance global, mint `Fintype` at use sites). -/
@[reducible] noncomputable def skeletonFintype (n : ℕ) : Fintype (Skeleton n) :=
  Fintype.ofFinite _

/-- SP-FIN's explicit p-free crude bound, transported to `Skeleton n`
(at n = 0 the count is 0). -/
theorem skeleton_card_le (n : ℕ) :
    Nat.card (Skeleton n) ≤ (n + 2) ^ (n ^ 2 + 3 * n + 12) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.card_of_isEmpty]
  · calc Nat.card (Skeleton n)
        = Nat.card ↥(MovesSp.SnRaw n) := Nat.card_congr (skeletonEquivSnRaw n)
      _ ≤ (n + 2) ^ (n ^ 2 + 3 * n + 12) := (MovesSp.SP_FIN n hn).2

end LeanUrat.MovesV
