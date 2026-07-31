/-
Kernels/KB12 — BP4-c7 E-phase skeleton for unit KB12 [ATTEMPT]: (U) at the
canonical instance — the canonical-instance leg of BP3 TV-A1's named
`TrackUniqOn` (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.B + §4 KB12 +
the F8 consumer edge; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md
BP4 block; BP3 TV-A1 = lean/LeanUrat/MovesT/TV_A1.lean, built).

CONSUMER FENCE (REV 2, F8 — binding): the target Prop is TV-A1's
`TrackUniqOn`, INSTANTIATED at the canonical carriers — NOT the abstract E5
`hD4R0K` sorry (MovesT/E5_rootSplit.lean:343; owner HC-2/D4R0K, hoisted to
named hypotheses by BP3 TV-A1..A5).  KB12's only advertised consumers are
BP1's per-prime `UInstance` instance rows and the Q7-gated KB15 bridge; NO
canonical→abstract implication is claimed or planned here.

GATE SEQUENCING (REV 2, F5): the CM-first twin KB14 (the (U)/(R)
countermodel probe, python + the G1 CellData in-corpus witness attempt) is
a SIBLING unit and runs BEFORE any prover is assigned here.

RECORDED RESOLUTIONS (statement transcription):
· "two realized root children on one track share side/digit data (functions
  of f)" is typed as the NAMED law `RootChildDataFn` (⚑): agreement in every
  Node field EXCEPT possibly the lift, spelled as the structure-update
  equality `{ ν with lift := ν'.lift } = ν'` (the same idiom as
  `CanonPolicy.blind`, MovesD/Defs.lean:358).  This is EXACTLY the
  blueprint's fallback-named "child-datum-is-function-of-f law" — if the
  canonical carriers do not grant it, the obstruction record names it and
  it stays a hypothesis.
· "the canonical lift (KB8a/b determinism)" enters through the TreeModel's
  OWN laws: realized root children of root species carry `pol.liftOf` —
  the helper `kb12_rootChild_canonLift` below derives it from `mem_single`
  + `mem_realizable` (`IsCanonPres ⟹ IsCanon` at the singleton history).
  The tie of THE policy to the enum-model offP determinism (KB8a/b) is the
  ⚑ seam unit KB11's territory (POL-PIN), not consumed here.
· The root-species side condition is typed as the small companion law
  `RootChildRootSpecies` (⚑) — `mem_single` is only invocable at
  root-species nodes.

deps: KB14 (CM gate — runs FIRST; sibling, python), KB8b (the determinism
content's intended witness — seams via KB11, not imported),
MovesD.CanonPolicy vocabulary + MovesT TV-A1.

Build: cd lean && lake build LeanUrat.Kernels.KB12
-/
import LeanUrat.MovesT.TV_A1

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- KB12 (⚑ named law — THE "child-datum-is-function-of-f" law, the
blueprint's own fallback name): at any root-cell point, two realized root
children sharing a track agree in EVERY node datum except possibly the
recorded lift (side/digit data are functions of (point, track) at the
root).  Spelled as the structure-update equality, the `CanonPolicy.blind`
idiom.  NEVER proved here; the KB12 attempt is its discharge at the
canonical carriers, fallback = obstruction record. -/
def RootChildDataFn (T : TreeModel p F n N m pol)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (x : Box p m) (ν ν' : Node p F), T.child none ν x → T.child none ν' x →
    trackOf ν = trackOf ν' → { ν with lift := ν'.lift } = ν'

/-- KB12 (⚑ named companion law): realized root children are ROOT-species
reads (the structural side condition `mem_single` demands; §C.0's root read
ν₀).  Expected derivable at the canonical instance; carried named per Q4. -/
def RootChildRootSpecies (T : TreeModel p F n N m pol) : Prop :=
  ∀ (x : Box p m) (ν : Node p F), T.child none ν x →
    ν.species = ReadSpecies.root

/-- KB12 (helper — the canonical-lift leg): a realized root child of root
species carries the canonical lift.  deps: TreeModel laws only.  Sketch:
form the singleton history ⟨[ν], …⟩ (root_iff holds by `hsp`);
`T.mem_single` turns `T.child none ν x` into membership; `T.mem_realizable`
yields `pol.IsCanonPres`, whose first conjunct `IsCanon` at index 0 is
`ν.lift = pol.liftOf ν`. -/
theorem kb12_rootChild_canonLift (T : TreeModel p F n N m pol)
    (x : Box p m) (ν : Node p F) (hchild : T.child none ν x)
    (hsp : ν.species = ReadSpecies.root) :
    ν.lift = pol.liftOf ν := by
  -- the `mem_single` side condition at the root-species node
  have h1 : (([ν] : List (Node p F)) ≠ [] ∧
      ∀ (j : ℕ) (hj : j < ([ν] : List (Node p F)).length),
        ((([ν] : List (Node p F))[j]'hj).species = ReadSpecies.root ↔ j = 0)) := by
    refine ⟨by simp, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
    subst hj0
    simpa using hsp
  -- membership of the singleton history, then realizability ⟹ IsCanonPres
  have hmem : T.mem (some ⟨[ν], h1.1, h1.2⟩) x := (T.mem_single ν h1 x).mpr hchild
  have hcanon : pol.IsCanon ⟨[ν], h1.1, h1.2⟩ :=
    (T.mem_realizable ⟨[ν], h1.1, h1.2⟩ x hmem).2.2.1
  simpa using hcanon 0 (by simp)

/-- KB12 (HEAD — (U) at the canonical instance): the two named laws force
TV-A1's `TrackUniqOn` at every reduction datum g.  deps: KB14 (gate),
`RootChildDataFn`, `RootChildRootSpecies`, `kb12_rootChild_canonLift`.
Sketch: `hdata` gives `{ ν with lift := ν'.lift } = ν'` — all-but-lift
agreement; `hroot` + `kb12_rootChild_canonLift` pin both lifts canonical:
ν.lift = pol.liftOf ν and ν'.lift = pol.liftOf ν'; `pol.blind` transports
liftOf across the update (liftOf ν' = liftOf { ν with lift := _ } =
liftOf ν), so ν'.lift = ν.lift; rewriting the update at the equal lift
gives ν = ν'. -/
theorem kb12_trackUniqOn_canonical (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (hdata : RootChildDataFn T trackOf)
    (hroot : RootChildRootSpecies T)
    (g : Fin n → ZMod p) :
    TrackUniqOn T χ trackOf g := by
  intro y _hy ν ν' hc hc' htr
  -- all-but-lift agreement (the named data law)
  have hupd : ({ ν with lift := ν'.lift } : Node p F) = ν' := hdata y ν ν' hc hc' htr
  -- both lifts are canonical (root species + the TreeModel laws)
  have hl : ν.lift = pol.liftOf ν :=
    kb12_rootChild_canonLift T y ν hc (hroot y ν hc)
  have hl' : ν'.lift = pol.liftOf ν' :=
    kb12_rootChild_canonLift T y ν' hc' (hroot y ν' hc')
  -- `blind` transports liftOf across the update: liftOf ν' = liftOf ν
  have hLo : pol.liftOf ν' = pol.liftOf ν := by
    rw [← hupd]; exact pol.blind ν ν'.lift
  -- hence the lifts agree, and the update collapses to ν
  have hlift : ν'.lift = ν.lift := by rw [hl', hLo, ← hl]
  have hν : ({ ν with lift := ν'.lift } : Node p F) = ν := by rw [hlift]
  exact hν.symm.trans hupd

end LeanUrat.Kernels
