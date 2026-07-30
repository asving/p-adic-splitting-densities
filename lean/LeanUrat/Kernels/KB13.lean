/-
Kernels/KB13 — BP4-c7 E-phase skeleton for unit KB13 [ATTEMPT]: (R) at the
canonical instance — the canonical-instance leg of BP3 TV-A1's named
`TrackRepOn` (the (c2) covering, MOVES 7112-7119)
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.B + §4 KB13 + the F8 consumer
edge; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block; BP3
TV-A1 = lean/LeanUrat/MovesT/TV_A1.lean, built).

CONSUMER FENCE (REV 2, F8 — binding, same as KB12): the target Prop is
TV-A1's `TrackRepOn` at the canonical carriers — NOT the abstract E5
`hD4R0K` sorry (owner HC-2/D4R0K).  Consumers: BP1's per-prime `UInstance`
rows + the Q7-gated KB15 bridge only; no canonical→abstract implication is
claimed.

GATE SEQUENCING (REV 2, F5): the CM-first twin KB14 (sibling, python + the
G1 CellData in-corpus witness attempt) runs BEFORE any prover here.

RECORDED RESOLUTIONS (statement transcription):
· The (c2) sketch "a simple factor's read is hen-terminal, no continuing
  child" splits into TWO named laws (⚑ each, Q4 hypothesis shape):
  `RootTrackMem` — a realized root child's track IS a normalized factor of
  the point's level-0 reduction (realized children ride actual reduction
  tracks); `HenAtSimple` — at a SIMPLE factor (multiplicity 1, matching the
  corpus's own simple-track keying in `henDegrees`, MovesT/Defs.lean) NO
  realized root child carries that track (m_i = 1 ⟹ τ-hen leaf, MOVES
  7112-7119).  Their conjunction assembles `TrackRepOn` (count ≥ 1 by
  membership; count = 1 excluded by hen) — the head below.
· The multiplicity is read in `UniqueFactorizationMonoid.normalizedFactors
  (redPoly χ y)`, VERBATIM the TrackRepOn spelling (TV_A1.lean).

deps: KB14 (CM gate — runs FIRST; sibling), MovesD/MovesT root-read
vocabulary (`redPoly`, `TreeModel.child`), MovesT TV-A1.
Fallback: the obstruction record naming which of the two laws fails at the
canonical carriers (the KB12/KB13 shared fallback genre).

Build: cd lean && lake build LeanUrat.Kernels.KB13
-/
import LeanUrat.MovesT.TV_A1

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- KB13 (⚑ named law — track membership): a realized root child's track is
an actual normalized factor of the point's level-0 reduction `redPoly χ x`
(realized children ride reduction tracks; the ∃-direction cousin is
`W41ChildCover`/`ChildCover`, which force a child AT a repeated factor —
this law is the converse containment, nowhere in the displayed laws).
NEVER proved here; the KB13 attempt is its canonical-instance discharge. -/
def RootTrackMem (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (x : Box p m) (ν : Node p F), T.child none ν x →
    trackOf ν ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)

/-- KB13 (⚑ named law — hen termination at simple factors): at a SIMPLE
(multiplicity-1) factor of the level-0 reduction, the read τ-hen-halts and
carries NO continuing child on that track (the (c2) covering case analysis,
MOVES 7112-7119: "m_i = 1 gives τ-hen"; multiplicity keyed = 1 exactly as
the corpus's `henDegrees` filter).  NEVER proved here; canonical-instance
discharge is the attempt. -/
def HenAtSimple (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (x : Box p m) (ψ : Polynomial (ZMod p)),
    Multiset.count ψ
      (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)) = 1 →
    ∀ ν : Node p F, T.child none ν x → trackOf ν ≠ ψ

/-- KB13 (HEAD — (R) at the canonical instance): the two named laws force
TV-A1's `TrackRepOn` at every reduction datum g.  deps: KB14 (gate),
`RootTrackMem`, `HenAtSimple`.  Sketch: fix y ∈ rootCell χ g and a realized
child ν; `hmem` puts trackOf ν among the normalized factors, so its count
is ≥ 1 (`Multiset.one_le_count_iff_mem`); if the count were 1, `hhen` at
ψ := trackOf ν contradicts `T.child none ν y`; hence count ≥ 2. -/
theorem kb13_trackRepOn_canonical (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (hmem : RootTrackMem T χ trackOf)
    (hhen : HenAtSimple T χ trackOf)
    (g : Fin n → ZMod p) :
    TrackRepOn T χ trackOf g := by
  sorry

end LeanUrat.Kernels
