/-
Unit G2.gatesClassifier  (MovesD campaign, ratification repair D6, 2026-07-28)
[Finding D6 (gap) ACCEPTED as typed obligations: G1 stated only the SHAPE-side gate
numbers (W = 7, M = 1, Nshape = 5, A′ = 11, NPband = 5, A(P̂₀) = 14); the sealed
CLASSIFIER-side falsifiers were a prose omission note. Here they become NAMED Prop defs —
NOT sorried theorems, NO proofs: the obligations are TYPED, owner = the classifier
corpora (HC-1 supplies the pinned policy, HC-2 the presentations/tree; discharge =
providing instances and proving these Props at them).]
moves_ref: §D4-R.6 seal predictions (note 5344–5372): "(1) C_P̂*(2) = 3 and C_P̂*(3) = 48,
by direct enumeration of realizable value assignments — L11's enc′ with (NA)/(HV)
applied; … (3) the counts #{f mod p^N ∈ S(P̂*,⊤)} = C_P̂*(p)·p^{3N−11}, TWO pinned levels
per prime, both ≥ N(P̂*) = 5 (L12): p = 2: N = 6: 3·2⁷ = 384; N = 7: 3·2¹⁰ = 3072;
p = 3: N = 5: 48·3⁴ = 3888; N = 6: 48·3⁷ = 104976" + mult ≡ 1 (§0.6 gate; F1's
moves_ref: "Gate-checked at §0.6 — C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1").
P̂* IS constructible in MovesD vocabulary (G1's `PhatStar` + `PhatStar_wf`); the gates
are stated over it with `pol`/`F`/`S` parametric — the note's numbers hold at THE
canonical policy (POL-PIN/W4-5, unit PolPin) with the ambient field and presentations
the classifier corpora supply.
STILL MISSING (documented, per the charge): prediction (5)'s FC8/FC9 PARTITION checks —
their stratum lists (valuation lumps, digit-value cells, δ-cells {w(B₀) = 4, …} ∪ DEEP)
are census-resolution vocabulary (§S0 of the seal), not expressible over MovesD's
Box/event/mult exports; they stay with the census/HC-2 wave.
deps: Defs, G1 (PhatStar, PhatStar_wf), PolPin (referenced in docstrings only).
sketch: none — Prop defs only, by design.  difficulty: n/a (no proofs).
hypothesis_fields: n/a.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.G1_gates

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

/-- P̂* as a point of the note's shape universe `Shape 3` (G1's record + certificate). -/
def PhatStarShape : Shape 3 := ⟨PhatStar, PhatStar_wf⟩

section
variable {F : Type*} [Field F] [Finite F]

/-- **GATE (classifier side, TYPED OBLIGATION — no proof here)**: C_P̂*(2) = 3
(§D4-R.6 seal prediction (1), note 5346–5347; the closed form N₂(2)·1·3 = 1·1·3, note
5334–5339). Owner: HC-1/HC-2 at the pinned policy (W4-5 `OffsetPPin`) and their ambient
field. -/
def Gate_CD_q2 (pol : CanonPolicy 2 F) : Prop :=
  PhatStarShape.CD pol = 3

/-- **GATE (classifier side, TYPED OBLIGATION)**: C_P̂*(3) = 48 (§D4-R.6 seal prediction
(1), note 5346–5347; the closed form 3·2·8 = 48, note 5342). -/
def Gate_CD_q3 (pol : CanonPolicy 3 F) : Prop :=
  PhatStarShape.CD pol = 48

/-- **GATE (classifier side, TYPED OBLIGATION)**: mult_P̂* ≡ 1 on the event (§0.6 gate:
"C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1") — every box point of S(P̂*,⊤) lies in EXACTLY one
class fiber. Stated over any presentation family S at any level/prime. -/
def Gate_multOne {p : ℕ} [Fact p.Prime] {N m : ℕ} {pol : CanonPolicy p F}
    (S : Presented p F 3 N m pol PhatStarShape) : Prop :=
  ∀ x ∈ S.event, S.mult x = 1

/-- **GATE (classifier side, TYPED OBLIGATION)**: the four sealed finite-level event
counts, §D4-R.6 prediction (3) (note 5349–5355): #{f mod p^N ∈ S(P̂*,⊤)} =
C_P̂*(p)·p^{3N−11} at the two pinned levels per prime. Instances below at (p, N, count):
(2, 6, 384), (2, 7, 3072), (3, 5, 3888), (3, 6, 104976); m = 3N throughout. -/
def Gate_eventCount {p : ℕ} [Fact p.Prime] {N m : ℕ} {pol : CanonPolicy p F}
    (S : Presented p F 3 N m pol PhatStarShape) (count : ℕ) : Prop :=
  Nat.card ↥S.event = count

/-- p = 2, N = 6: 3·2⁷ = 384 of 2¹⁸ (note 5352). -/
def Gate_eventCount_q2_N6 {pol : CanonPolicy 2 F}
    (S : Presented 2 F 3 6 18 pol PhatStarShape) : Prop :=
  Gate_eventCount S 384

/-- p = 2, N = 7: 3·2¹⁰ = 3072 of 2²¹ (note 5353). -/
def Gate_eventCount_q2_N7 {pol : CanonPolicy 2 F}
    (S : Presented 2 F 3 7 21 pol PhatStarShape) : Prop :=
  Gate_eventCount S 3072

/-- p = 3, N = 5: 48·3⁴ = 3888 of 3¹⁵ (note 5354). -/
def Gate_eventCount_q3_N5 {pol : CanonPolicy 3 F}
    (S : Presented 3 F 3 5 15 pol PhatStarShape) : Prop :=
  Gate_eventCount S 3888

/-- p = 3, N = 6: 48·3⁷ = 104976 of 3¹⁸ (note 5355; FC7's stated deviation — the sole
second admissible p = 3 level). -/
def Gate_eventCount_q3_N6 {pol : CanonPolicy 3 F}
    (S : Presented 3 F 3 6 18 pol PhatStarShape) : Prop :=
  Gate_eventCount S 104976

end

end LeanUrat.MovesD
