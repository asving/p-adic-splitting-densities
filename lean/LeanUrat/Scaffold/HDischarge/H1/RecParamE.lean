/-
HDISCHARGE_H1 — `H1/RecParamE.lean`: the REC-PARAM e-half, compiled AT ITS DERIVABLE
SCOPE (the BM2_TRACE_2026-08-02.md §3 (C-a) wiring finding, executed; unit note
`lean/notes/openmath/H1_BM2_2026-08-06.md` §S2 case (b) / §S4 (i-c) sub-obligation
REC-PARAM).

WHAT IS COMPILED HERE (sorry-free; no new axioms; no existing statement touched):
* `recParam_e_of_transition` — the e-half of REC-PARAM as a WIRING derivation, at the
  exact scope the trace found derivable: in a coherent history, when the recentering
  node's stage WAS FORGED BY A NON-RECENTERING TRANSITION (the displayed hypothesis
  `hprev`) and the recentering transition is INTERIOR (the displayed `i + 2 < len`,
  so `HistoryCoherent`'s recentering leg fires `IsRecenteringCore`), then
  (a) the stage's own pair is unramified: `σᵢ₊₁.e = 1` (`IsRecentering`'s first
      conjunct, through `IsRecenteringCore.base`);
  (b) the stage pair IS the node's read pair: `σᵢ₊₁.e = νᵢ₊₁.e`
      (`TransitionData.child_e`, `Moves/DefsT.lean:150`, through the coherence leg's
      `TransitionCoreL` at the child node's pair);
  (c) hence the node's read stride is 1: `νᵢ₊₁.e = 1`.
  Clause (b) is the tie the trace named missing ("the corpus never TIES νᵢ.e at
  recentering legs"); (a)+(b) together derive (c) from the TRANSITION LAWS, with no
  appeal to the species predicate.

WHAT IS NOT CLAIMED:
* The g-half of REC-PARAM (νᵢ₊₁.g = 1 derived from wiring) is NOT this unit's target
  and is NOT proved here: no Stage field records a `g`, so the σ-level route used for
  the e-half has no g-analogue — the trace's "tied NOWHERE" verdict stands AT THE
  STAGE/WIRING LEVEL.
* SCOPE CORRECTION FOR THE NOTE'S NEXT REVISION (a finding, recorded here and in the
  ledger, NOT folded into the note by this unit): at the NODE level the trace's
  "a Lean history could record νᵢ.g = 7 at a recentering node and stay coherent" is
  FALSE — `Node.hspecRec` (`MovesC/Defs.lean`, the §C.0 species law) is a STRUCTURE
  FIELD giving `species = recentering → e = 1 ∧ g = 1`, so no species-recentering
  node with g ≠ 1 is even constructible. That field is, however, exactly the "priced
  at (1, 1) by fiat" layer REC-PARAM's display distinguishes from a genuine tower
  derivation (the predicate BUILDS the pair in; whether engine recentering firings
  HAVE this shape is S-1/SITE-EXH-side and stays open). THIS file's lemma is the
  non-fiat derivation for the e-half; consumers wanting the node-level pair
  unconditionally at species-recentering nodes should cite `Node.hspecRec` directly.
* Nothing here touches (K1)+(K2)/REC-SL's stage-law legs, GRADED-READ, or SITE-EXH
  (all open; see `H1/Conformance.lean`'s residue display).
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **REC-PARAM, e-half, at its derivable scope** (BM2_TRACE §3 (C-a); unit note §S2
case (b)): in a coherent history, at an INTERIOR recentering read whose frame stage
came from a NON-RECENTERING transition (both hypotheses displayed — do NOT read this
as the unconditional identification), the frame stage's stride is 1
(`IsRecentering`, via the recentering coherence leg), the stage stride IS the node's
recorded read stride (`TransitionData.child_e`, via the non-recentering coherence
leg's `TransitionCoreL` keyed at the child node's pair), and hence the node's read
stride is 1.  The g-half is NOT claimed (no stage field records g; the node-level
`Node.hspecRec` supplies it by species fiat, not by wiring — see the file header). -/
theorem recParam_e_of_transition (H : History p F) (hH : HistoryCoherent H)
    (i : ℕ) (hi2 : i + 2 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hrec : (H.nodes[i+1]'(by omega)).species = ReadSpecies.recentering) :
    (H.nodes[i+1]'(by omega)).σ.e = 1 ∧
    (H.nodes[i+1]'(by omega)).σ.e = (H.nodes[i+1]'(by omega)).e ∧
    (H.nodes[i+1]'(by omega)).e = 1 := by
  obtain ⟨-, -, -, hstep⟩ := hH
  -- the transition at i (non-recentering): `child_e` ties the forged stage's stride
  -- to the CHILD node's recorded read stride (the (S-a) keying)
  obtain ⟨-, hnonrec, -, -, -, -, -⟩ := hstep i (by omega)
  obtain ⟨-, σV, -, -, htcl⟩ := hnonrec hprev
  have htie : (H.nodes[i+1]'(by omega)).σ.e = (H.nodes[i+1]'(by omega)).e :=
    htcl.base.child_e
  -- the transition at i+1 (recentering, INTERIOR by hi2): `IsRecentering`'s first
  -- conjunct pins the frame stage's stride to 1
  obtain ⟨hrecleg, -, -, -, -, -, -⟩ := hstep (i+1) (by omega)
  have hσe : (H.nodes[i+1]'(by omega)).σ.e = 1 := (hrecleg hrec).base.1
  exact ⟨hσe, htie, by rw [← htie]; exact hσe⟩

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.recParam_e_of_transition
