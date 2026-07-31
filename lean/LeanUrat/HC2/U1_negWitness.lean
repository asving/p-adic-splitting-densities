/-
Unit U1-NEG — the COMPILED NEGATION WITNESS for the retired `hcoh`-keyed `keys_exist`
(HC-2 campaign; N-1 remediation round, 2026-07-28; the `U27_OBSTRUCTION` durability pattern).

WHAT IS REFUTED. The pre-N-1 unit U1 stated
  `keys_exist : HistoryCoherent H → ∃ keys, (interior key law) ∧ (landing at EVERY read)`
(conclusion = D5's `KeysLawful`, spelled out). The N-1 adjudication (blueprint §9 F-1)
retired it as FALSE — LAST-READ RECORD FREEDOM: `HistoryCoherent`'s ONLY access to any
node's `.lift` is the parent-side `IsRecenteringCore` clause under the `i+1 < len` guard,
and NO `Node` Prop field mentions `lift`; so the LAST node's `lift` is a free record field,
while `LandingKey`'s recentering leg demands `ν.lift ≠ 0` OF THE RECORD — a demand no key
choice can repair (the four recentering conjuncts never mention `Φtop`). This file compiles
that mechanism:

* `U1neg.zeroLast` — THE SURGERY: the `{ν with lift := 0}` record update on the LAST node.
* `U1neg.zeroLast_coherent` — the surgery PRESERVES `HistoryCoherent` (and `root_iff`,
  inside the `History` construction): the machine-checked "free record field" claim.
* `U1neg.zeroLast_no_keys` — if the last node is a RECENTERING, the zeroed history admits
  NO lawful key tower, for EVERY key choice (key-independence, machine-checked).
* `retiredKeysExist_false_of_witness` — the retired ∀-sentence (`RetiredKeysExistStmt`,
  verbatim conclusion shape) is FALSE at `(p, F)` GIVEN any coherent history whose last
  node is a recentering.

HONESTY PERIMETER (the one leg NOT compiled here — recorded, not hidden). The refutation
is unconditional over its hypothesis class; the INHABITATION of that class (a concrete
2-node coherent history `[root, recentering]`) is NOT yet compiled: any 2-node coherent
history requires `TransitionCoreL` at the root read, i.e. a constructed CHILD STAGE
(`TransitionData.child_slotmin` + digit laws at the child key) — exactly the B2-heart
carry-algebra kernel that is HC-1's S9 frontier. [STALE POINTER CORRECTED 2026-07-30
verify-2 fold-in: this sentence formerly cited "`S9r_childR`'s open construction" and
"K1_vertexPin's named sorry" as the blockers; both are now PROVED sorry-free/Lean-core
(re-verified 2026-07-30). The standing inhabitation blocker is task #44's
`HistoryCoherent` read-pair keying repair + the 2-node `ReadsOf` gate sub-project —
NOT a sorry.] The fleet note pre-recorded this dependency ("needs a concrete
2-node coherent history — HC-1 S9-adjacent construction"); when the 2-node gate lands
(wave 4), instantiate `retiredKeysExist_false_of_witness` with it to close the last leg.
The 1-node increment-leg countermodel (F-1's "σ.e = 2, h′ = 1, g = 1 leaves the required
weight odd") is likewise blocked on a NEW ramified stage build: any legal `Stage` has
constant-coefficient weights `c·v₂` (`hwmul` on constants + torsion-freeness), and missing
the odd target weight forces `c = 2` — a genuinely ramified-quadratic weight whose
residual laws need `ℤ₂[√2]` arithmetic; queued with the same kernel, NOT attempted here.

deps: HC2 Defs (`HistoryCoherent`, `KeysLawful`, `LandingKey` via MovesC).
axioms: Lean core only (verified at the foot of the file).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace U1neg

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Index-transport for `getElem` (equal indices, proof-irrelevant bounds). -/
private lemma getElem_idx {α : Type*} {l : List α} {i j : ℕ} (hij : i = j)
    (hi : i < l.length) : l[i]'hi = l[j]'(hij ▸ hi) := by
  subst hij
  rfl

/-- The last index is in range (histories are nonempty). -/
lemma last_lt (H : History p F) : H.nodes.length - 1 < H.nodes.length :=
  Nat.sub_lt (List.length_pos_iff.mpr H.nonempty) Nat.one_pos

/-- The last node with its `lift` record field ZEROED. Every other field — including every
Prop field: none of `Node`'s Prop fields mentions `lift` — is carried verbatim, so every
non-`lift` projection of `lastZeroed H` is DEFINITIONALLY that of the last node. -/
noncomputable def lastZeroed (H : History p F) : Node p F :=
  { H.nodes[H.nodes.length - 1]'(last_lt H) with lift := 0 }

/-- **THE SURGERY** (the F-1 adjudication's `{ν with lift := 0}` record update): replace
the last node by its lift-zeroed copy. `root_iff` survives because `species` is untouched. -/
noncomputable def zeroLast (H : History p F) : History p F where
  nodes := H.nodes.set (H.nodes.length - 1) (lastZeroed H)
  nonempty := by
    intro hnil
    have h0 := congrArg List.length hnil
    rw [List.length_set] at h0
    exact H.nonempty (List.eq_nil_of_length_eq_zero h0)
  root_iff := by
    intro j hj
    have hj' : j < H.nodes.length := by rwa [List.length_set] at hj
    rw [List.getElem_set]
    split
    · next heq =>
        have hnode : H.nodes[H.nodes.length - 1]'(last_lt H) = H.nodes[j]'hj' :=
          getElem_idx heq (last_lt H)
        have hlz : lastZeroed H = { (H.nodes[j]'hj') with lift := 0 } := by
          unfold lastZeroed
          rw [hnode]
        rw [hlz]
        exact H.root_iff j hj'
    · exact H.root_iff j hj'

@[simp] lemma zeroLast_length (H : History p F) :
    (zeroLast H).nodes.length = H.nodes.length := List.length_set

lemma zeroLast_getElem (H : History p F) (j : ℕ) (hj : j < (zeroLast H).nodes.length) :
    (zeroLast H).nodes[j]'hj =
      if H.nodes.length - 1 = j then lastZeroed H
      else H.nodes[j]'(by rw [← zeroLast_length H]; exact hj) :=
  List.getElem_set hj

/-- The surgery does not touch any node's `e`, so the frame-stretch data is unchanged. -/
lemma zeroLast_map_e (H : History p F) :
    (zeroLast H).nodes.map Node.e = H.nodes.map Node.e := by
  show (H.nodes.set (H.nodes.length - 1) (lastZeroed H)).map Node.e = H.nodes.map Node.e
  rw [List.map_set]
  have he : Node.e (lastZeroed H) = (H.nodes.map Node.e)[H.nodes.length - 1]'(by
      rw [List.length_map]; exact last_lt H) := by
    rw [List.getElem_map]
    rfl
  rw [he, List.set_getElem_self]

lemma zeroLast_strFrame (H : History p F) (i : ℕ) :
    (zeroLast H).strFrame i = H.strFrame i := by
  unfold History.strFrame
  rw [List.map_take, List.map_take, zeroLast_map_e]

/-- **COHERENCE IS PRESERVED** — the machine-checked half of the F-1 record ("the record
update preserves coherence"): every `HistoryCoherent` clause reads nodes only through
non-`lift` projections EXCEPT the parent-side recentering clause, whose parent is interior
(`i + 1 < len` guards it away from the modified last slot). -/
theorem zeroLast_coherent {H : History p F} (hcoh : HistoryCoherent H) :
    HistoryCoherent (zeroLast H) := by
  obtain ⟨hroot, hslope, hgam, htrans⟩ := hcoh
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- root frame degree: `σ` untouched
    intro hj
    have hj' : 0 < H.nodes.length := by rwa [zeroLast_length] at hj
    rw [zeroLast_getElem H 0 hj]
    split
    · next heq =>
        have hnode : H.nodes[H.nodes.length - 1]'(last_lt H) = H.nodes[0]'hj' :=
          getElem_idx heq (last_lt H)
        have hlz : lastZeroed H = { (H.nodes[0]'hj') with lift := 0 } := by
          unfold lastZeroed
          rw [hnode]
        rw [hlz]
        exact hroot hj'
    · exact hroot hj'
  · -- absolute-scale slope law: reads `line`, `e`, `Dwidth`, `h` (+ strFrame) — lift-free
    intro i hi'
    have hi : i < H.nodes.length := by rwa [zeroLast_length] at hi'
    rw [zeroLast_strFrame, zeroLast_getElem H i hi']
    split
    · next heq =>
        have hnode : H.nodes[H.nodes.length - 1]'(last_lt H) = H.nodes[i]'hi :=
          getElem_idx heq (last_lt H)
        have hlz : lastZeroed H = { (H.nodes[i]'hi) with lift := 0 } := by
          unfold lastZeroed
          rw [hnode]
        rw [hlz]
        exact hslope i hi
    · exact hslope i hi
  · -- γ-tie: reads `gam`, `e`, `ustar`, `s0`, `wSide`, `h` (+ strFrame) — lift-free
    intro i hi'
    have hi : i < H.nodes.length := by rwa [zeroLast_length] at hi'
    rw [zeroLast_strFrame, zeroLast_getElem H i hi']
    split
    · next heq =>
        have hnode : H.nodes[H.nodes.length - 1]'(last_lt H) = H.nodes[i]'hi :=
          getElem_idx heq (last_lt H)
        have hlz : lastZeroed H = { (H.nodes[i]'hi) with lift := 0 } := by
          unfold lastZeroed
          rw [hnode]
        rw [hlz]
        exact hgam i hi
    · exact hgam i hi
  · -- transitions: the parent (which alone is read at `.lift`, in `IsRecenteringCore`)
    -- has index `i < len − 1`, hence is NEVER the modified slot; the child is read only
    -- through `σ`, `s0`, `wSide`, `Dwidth`, `line` — lift-free.
    intro i hi'
    have hi : i + 1 < H.nodes.length := by rwa [zeroLast_length] at hi'
    have hine : H.nodes.length - 1 ≠ i := by omega
    rw [zeroLast_getElem H i (by rw [zeroLast_length]; omega),
      zeroLast_getElem H (i + 1) hi', if_neg hine]
    by_cases hlast : H.nodes.length - 1 = i + 1
    · rw [if_pos hlast]
      have hnode : H.nodes[H.nodes.length - 1]'(last_lt H) = H.nodes[i + 1]'hi :=
        getElem_idx hlast (last_lt H)
      have hlz : lastZeroed H = { (H.nodes[i + 1]'hi) with lift := 0 } := by
        unfold lastZeroed
        rw [hnode]
      rw [hlz]
      exact htrans i hi
    · rw [if_neg hlast]
      exact htrans i hi

/-- **NO LAWFUL KEYS, FOR EVERY KEY CHOICE** — the machine-checked other half of the F-1
record: when the last node is a recentering, its landing law demands `ν.lift ≠ 0` OF THE
RECORD (the four recentering conjuncts of `LandingKey` never mention the key), and the
zeroed record refutes it outright. -/
theorem zeroLast_no_keys (H : History p F)
    (hrec : (H.nodes[H.nodes.length - 1]'(last_lt H)).species = ReadSpecies.recentering) :
    ¬ ∃ keys : ℕ → Polynomial ℤ_[p], KeysLawful (zeroLast H) keys := by
  rintro ⟨keys, -, hland⟩
  have hlt : H.nodes.length - 1 < (zeroLast H).nodes.length := by
    rw [zeroLast_length]
    exact last_lt H
  have hlast := hland (H.nodes.length - 1) hlt
  rw [zeroLast_getElem H (H.nodes.length - 1) hlt, if_pos rfl] at hlast
  have hrec' : (lastZeroed H).species = ReadSpecies.recentering := hrec
  exact (hlast.1 hrec').2.1 rfl

end U1neg

/-- **The RETIRED sentence, verbatim** (at a fixed `(p, F)`): the pre-N-1 `keys_exist`
statement — `hcoh`-keyed, with its original spelled-out conclusion (= D5's `KeysLawful`,
definitionally). Kept as a named `Prop` so the refutation below is pinned to the exact
retired statement, the `U27_OBSTRUCTION` durability pattern. -/
def RetiredKeysExistStmt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (H : History p F), HistoryCoherent H →
    ∃ keys : ℕ → Polynomial ℤ_[p],
      (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
      (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))

/-- **THE NEGATION WITNESS**: given ANY coherent history whose last node is a recentering,
the retired `hcoh`-keyed `keys_exist` sentence is FALSE at `(p, F)` — apply it to the
lift-zeroed surgery of the witness and contradict the last read's landing law. The
inhabitation input is the HC-1 S9-adjacent 2-node construction (see the header's honesty
perimeter); everything downstream of it is compiled here, key-independent. -/
theorem retiredKeysExist_false_of_witness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (Hw : History p F) (hcoh : HistoryCoherent Hw)
    (hrec : (Hw.nodes[Hw.nodes.length - 1]'(U1neg.last_lt Hw)).species
      = ReadSpecies.recentering) :
    ¬ RetiredKeysExistStmt p F := by
  intro hall
  obtain ⟨keys, hpair⟩ := hall (U1neg.zeroLast Hw) (U1neg.zeroLast_coherent hcoh)
  exact U1neg.zeroLast_no_keys Hw hrec ⟨keys, hpair⟩

/-- The same refutation phrased on D5's `KeysLawful` (the consumer-facing form of the
retired conclusion). -/
theorem keysLawful_of_hcoh_false_of_witness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (Hw : History p F) (hcoh : HistoryCoherent Hw)
    (hrec : (Hw.nodes[Hw.nodes.length - 1]'(U1neg.last_lt Hw)).species
      = ReadSpecies.recentering) :
    ¬ ∀ (H : History p F), HistoryCoherent H →
        ∃ keys : ℕ → Polynomial ℤ_[p], KeysLawful H keys := by
  intro hall
  exact U1neg.zeroLast_no_keys Hw hrec
    (hall (U1neg.zeroLast Hw) (U1neg.zeroLast_coherent hcoh))

#print axioms LeanUrat.MovesJ.retiredKeysExist_false_of_witness
#print axioms LeanUrat.MovesJ.keysLawful_of_hcoh_false_of_witness

end LeanUrat.MovesJ
-- 
-- ═══ HK-06 WAVE NOTE (2026-07-31, task #44, wave executor) ═══
-- Scope of this dated note: the recorded honesty perimeter (HK-25's recentering-ended H₂ʳ 
-- variant): the HK-06 wave LANDED (task #44) — the HK-22 wall is gone and the gate carriers 
-- (HC2/HK23_twoNodeGatePos.lean: σVgate/ν₀ram/H₂ram) now exist, so HK-25's inhabitation build 
-- is UNBLOCKED as a post-wave unit (BP2 Block G); the coherence-preservation lemmas of THIS file 
-- recompiled green under the (S-a) leg (the zeroLast surgery touches only lift, which the re-keyed 
-- leg still ignores).
