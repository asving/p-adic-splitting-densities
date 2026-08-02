/-
HDISCHARGE_H1 — `H1/RecParamE.lean`: the REC-PARAM e-half, compiled AT ITS DERIVABLE
SCOPE (the BM2_TRACE_2026-08-02.md §3 (C-a) wiring finding, executed; unit note
`lean/notes/openmath/H1_BM2_2026-08-06.md` §S2 case (b) / §S4 (i-c) sub-obligation
REC-PARAM).

WHAT IS COMPILED HERE (sorry-free; no new axioms; no existing statement touched):
* `k0_actual_of_recentering` [REV 10, the pass-8 finding-1 fold] — THE TRANSPORT
  LEMMA: at any species-recentering node, the synthetic conclusion
  `K0Conformant σ 1 1 Φ` TRANSPORTS to the node's ACTUAL pair
  `K0Conformant ν.σ ν.g ν.e Φ` — because `Node.hspecRec` (the §C.0 species law,
  a STRUCTURE FIELD) gives `ν.e = 1 ∧ ν.g = 1`, so the actual pair IS (1, 1).
  This supplies the ORIGINAL node-level REC-PARAM proposition ("the identification
  of the node's actual (e_i, g_i) with (1, 1)") outright; what it does NOT supply
  is the stronger wiring-provenance obligations (see the REV-10 scope note below).
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
  recentering legs" — REV 12: that trace verdict was itself too broad; see the
  REC-WIRE-G bullet below); (a)+(b) together derive (c) from the TRANSITION LAWS,
  with no appeal to the species predicate.
* `recentering_natDegree_eq` + `recParam_eg_of_recentering` [REV 12 — **REC-WIRE-G
  DISCHARGED**, the pass-10 GAP-1 route compiled]: the STAGE KERNEL
  (`IsRecentering σ σ' cc tt → σ'.Φ.natDegree = σ.Φ.natDegree`; no `Node` in the
  type, so the species fiat is unusable BY TYPE) and the WIRING COROLLARY (coherent
  history + interior recentering read ⟹ `νᵢ.e = 1 ∧ νᵢ.g = 1`, via the kernel + the
  coherence width law `Dwidthᵢ₊₁ = νᵢ.e·νᵢ.g·Dwidthᵢ` + both `Node.hDwidth` links +
  `Stage.hdeg`: `e·g·d = d`, `d ≥ 1` ⟹ `e·g = 1`). Every hypothesis comes from
  `HistoryCoherent`; `Node.hspecRec` is nowhere invoked.

WHAT IS NOT CLAIMED (REV-12 scope note — residuals after REC-WIRE-G):
* [REV 12 — the pass-10 CRITICAL-2 correction; supersedes the REV-10 "tied NOWHERE"
  wording here] The accurate narrow form of the trace's g-half finding: no `Stage`
  FIELD directly records a `g`, and the e-half's `child_e` route has no direct
  g-analogue — but the tie was NOT "nowhere at the stage/wiring level": it runs
  through the coherence width law (`Node.childWidth` + `HistoryCoherent`'s `Dwidth`
  chain + `Node.hDwidth`), compiled above as `recParam_eg_of_recentering`. What
  stays open on this flank is S-1/SITE-EXH-side only: whether engine recentering
  FIRINGS have the recorded shape at all.
* The e-half's came-from-a-non-recentering-transition hypothesis removal: DISCHARGED
  for the read-stride conclusion by `recParam_eg_of_recentering` (clause (c) with no
  `hprev`); `recParam_e_of_transition`'s clause (b) stage-node tie remains
  transition-case-scoped as displayed.
* Node-level context (the [REV 9] finding, now consumed by the transport lemma): at
  the NODE level the trace's "a Lean history could record νᵢ.g = 7 at a recentering
  node and stay coherent" is FALSE — `Node.hspecRec` (`MovesC/Defs.lean`, the §C.0
  species law) is a STRUCTURE FIELD giving `species = recentering → e = 1 ∧ g = 1`,
  so no species-recentering node with g ≠ 1 is even constructible.
* Nothing here touches (K1)+(K2)/REC-SL's stage-law legs, GRADED-READ, or SITE-EXH
  (all open; see `H1/Conformance.lean`'s residue display).
-/
import LeanUrat.MovesC.Defs
import LeanUrat.Scaffold.HDischarge.H1.Conformance

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **THE TRANSPORT LEMMA** (REV 10, the pass-8 finding-1 fold): at a
species-recentering node the compiled SYNTHETIC conclusion `K0Conformant σ 1 1 Φ`
transports to the node's ACTUAL read pair — `Node.hspecRec` (a structure field,
the §C.0 species law) gives `ν.e = 1 ∧ ν.g = 1`, so the actual pair IS (1, 1).
This IS the original node-level REC-PARAM proposition ("the identification of the
node's actual (e_i, g_i) with (1, 1)"), supplied. It rides the species structure
field (the fiat layer): the stage/wiring-level provenance obligations
(REC-WIRE-G; the e-half's transition-hypothesis removal) remain open and are NOT
claimed by this lemma. -/
theorem k0_actual_of_recentering (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (hspec : ν.species = ReadSpecies.recentering)
    (hK : K0Conformant ν.σ 1 1 Φhat) :
    K0Conformant ν.σ ν.g ν.e Φhat := by
  obtain ⟨he, hg⟩ := ν.hspecRec hspec
  rw [he, hg]
  exact hK

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

/-- **THE REC-WIRE-G STAGE KERNEL** [REV 12 — the pass-10 GAP-1 fold]: a recentering
does not move the key degree — `IsRecentering`'s own conjuncts `σ'.Φ = σ.Φ − tt` and
`inC σ.Φ tt` (i.e. `deg tt < deg σ.Φ`, `Moves/Defs.lean:67`) force
`σ'.Φ.natDegree = σ.Φ.natDegree` by lower-degree subtraction.  NO `Node` occurs in
this statement: the non-fiat routing is enforced BY THE TYPE — the species fiat
`Node.hspecRec` is not even expressible here, which is exactly the provenance
constraint pass 10 found the REVISION-11 top-level proposition unable to encode. -/
theorem recentering_natDegree_eq {σ σ' : Stage p F} {cc : ↥σ.K}
    {tt : Polynomial ℤ_[p]} (h : IsRecentering σ σ' cc tt) :
    σ'.Φ.natDegree = σ.Φ.natDegree := by
  obtain ⟨-, -, -, hin, -, -, -, hΦ', -⟩ := h
  rw [hΦ']
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_sub_eq_left_of_degree_lt hin)

/-- **REC-WIRE-G, DISCHARGED — the wiring corollary** [REV 12]: in a coherent history,
at an INTERIOR recentering read (the read's own transition fires: `i + 1 < len`), the
node's ACTUAL read pair is `νᵢ.e = 1 ∧ νᵢ.g = 1` — derived from the WIRING, not the
species fiat.  The route (every hypothesis supplied by `HistoryCoherent` itself, none
by `Node.hspecRec`):
(1) the recentering coherence leg fires `IsRecenteringCore νᵢ.σ νᵢ₊₁.σ` at the
    recorded center/lift; its `base` feeds the stage kernel
    `recentering_natDegree_eq`, giving `deg Φᵢ₊₁ = deg Φᵢ`;
(2) the coherence width law (`MovesC/Defs.lean:743`) gives
    `νᵢ₊₁.Dwidth = νᵢ.childWidth = νᵢ.e · νᵢ.g · νᵢ.Dwidth`;
(3) both `Node.hDwidth` frame links (`MovesC/Defs.lean:418`) convert (1)+(2) into
    `νᵢ.e · νᵢ.g · d = d` at `d = νᵢ.σ.Φ.natDegree`, and `Stage.hdeg` gives `d ≥ 1`,
    so `νᵢ.e · νᵢ.g = 1`, forcing both factors to 1.
Consequence: the e-half conclusion `νᵢ.e = 1` now holds WITHOUT
`recParam_e_of_transition`'s came-from-a-non-recentering-transition hypothesis
`hprev` — this corollary subsumes that lemma's clause (c) (its clause (b) stage-node
tie `σ.e = ν.e` remains transition-case content). -/
theorem recParam_eg_of_recentering (H : History p F) (hH : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hrec : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering) :
    (H.nodes[i]'(by omega)).e = 1 ∧ (H.nodes[i]'(by omega)).g = 1 := by
  obtain ⟨-, -, -, hstep⟩ := hH
  obtain ⟨hrecleg, -, -, -, -, hwidth, -⟩ := hstep i hi1
  -- (1) the stage kernel at the history-fired recentering transition
  have hker : (H.nodes[i+1]'hi1).σ.Φ.natDegree
      = (H.nodes[i]'(by omega)).σ.Φ.natDegree :=
    recentering_natDegree_eq (hrecleg hrec).base
  -- (2)+(3) the width chain closes into e·g·d = d
  have hchain : (H.nodes[i]'(by omega)).e * (H.nodes[i]'(by omega)).g *
      (H.nodes[i]'(by omega)).Dwidth = (H.nodes[i]'(by omega)).Dwidth := by
    calc (H.nodes[i]'(by omega)).e * (H.nodes[i]'(by omega)).g *
        (H.nodes[i]'(by omega)).Dwidth
        = (H.nodes[i]'(by omega)).childWidth := rfl
      _ = (H.nodes[i+1]'hi1).Dwidth := hwidth.symm
      _ = (H.nodes[i+1]'hi1).σ.Φ.natDegree := (H.nodes[i+1]'hi1).hDwidth
      _ = (H.nodes[i]'(by omega)).σ.Φ.natDegree := hker
      _ = (H.nodes[i]'(by omega)).Dwidth := ((H.nodes[i]'(by omega)).hDwidth).symm
  have hDpos : 0 < (H.nodes[i]'(by omega)).Dwidth := by
    rw [(H.nodes[i]'(by omega)).hDwidth]
    exact (H.nodes[i]'(by omega)).σ.hdeg
  have heg : (H.nodes[i]'(by omega)).e * (H.nodes[i]'(by omega)).g = 1 :=
    Nat.eq_of_mul_eq_mul_right hDpos (by rw [one_mul]; exact hchain)
  exact (mul_eq_one_iff_of_one_le (H.nodes[i]'(by omega)).he
    (H.nodes[i]'(by omega)).hg).mp heg

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.recParam_e_of_transition
#print axioms LeanUrat.Scaffold.HDischarge.H1.k0_actual_of_recentering
#print axioms LeanUrat.Scaffold.HDischarge.H1.recentering_natDegree_eq
#print axioms LeanUrat.Scaffold.HDischarge.H1.recParam_eg_of_recentering
