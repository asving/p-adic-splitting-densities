/-
HDISCHARGE_H1 §5.1 — `H1/Defs.lean`: the (GR-B)/(H1) hypothesis rows (wave 0; units
H1-U1..U4 + the §5.3 `DevBound` row, which the §5.1 REV-2 bracket lands in this file).
Statements transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H1.md` §5.1/§5.3
(REVISION 2, compile-probed 2026-08-05; re-probed same day after the pass-1 Codex
findings 8/10/11 restructures: link fields + `faithful_at` recorded-site form; the
TOTAL Cor-5.15 form is the SEPARATE gated unit H1-U14, never a row field here).

These are HYPOTHESIS ROWS ONLY (BP_II §0 discipline: hypothesis rows as named
structures, no new axioms): interface carriers for the §3.1 (H1) row — the graded
dictionary at orders ≥ 2, (GR-B)(2′)/(3)/(4) + (H1)(d1)/(d2) keyed to the creating
read. Never cite any row in this file as evidence for (H1); non-vacuity enters at
wave 1 (`Order1.lean`, H1-U5..U7) and the math leaves A-M2/B-M1. The `DevBound` row
is STAGING for `kp_step` (H1-U8) only [REV 2, finding 11]: member (b) retires only
with OP-B1 PROVED (the row derived, never assumed).

Per synthesis pass 3 finding F2 (docs/SYNTHESIS_PASS3_2026-08-05.md): these rows are
the ONE shared carrier the five consuming fleets (H2 line clauses, H3 `hclass`, H6
`OL2min`, H7 `KLoc` frame, H8 `supply_cell` owner) re-key to.

The Lean layer is stated at the wired instance O = ℤ_p (`Polynomial ℤ_[p]`, the
corpus's carrier); the arbitrary-DVR generality lives in the math leaves (GD23 §1.1
discipline) — these rows are the corpus FACE of the discharge, not its scope ceiling.
-/
import LeanUrat.MovesGr.Defs
import LeanUrat.MovesC.Defs
import LeanUrat.HC2.Defs

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- H1-U2 — the key-compliance block (KPa)+(KPirr) = (H1)(d1)+(d2), at a stage σ'
carrying the state key, over a genuine graded model M (MovesGr). Hypothesis ROW at
orders ≥ 2; THEOREM target at the base (H1-U5) and at KP-STEP's conclusion (H1-U8). -/
structure KPBlock (σ' : Stage p F) (M : GenuineStageModel σ') where
  ψhom : M.S.Gr
  homog : ∃ (γ : ℤ) (x : M.S.grPiece γ), ψhom = DirectSum.of (fun γ => M.S.grPiece γ) γ x
  kpa_init : letI := M.Rg.ring; ∃ u : (M.S.Gr)ˣ, M.S.initialForm σ'.Φ = (u : M.S.Gr) * ψhom
  kpirr : letI := M.Rg.ring; Prime ψhom
  kpa_block : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
    B.natDegree < σ'.Φ.natDegree → ¬ ψhom ∣ M.S.initialForm B

/-- H1-U3 — (GR-B-KEY) clauses (3)+(4) keyed to the creating read ν (MovesC.Node: ν.σ
the parent stage, ν.ψ the residual factor over ↥ν.σ.K) and the state model, WITH the
ν↔σ' link laws as fields [REV 2, finding 8: the rev-1 row carried no compatibility
between ν, σ', M, KB and asserted the ∀f (total Cor-5.15) law — over-quantified for a
hypothesis row; the row now carries the LINK plus the RECORDED-SITE law only (what
WGEO consumption needs, supplied by SideReads(iii)'s HasAnchorK witness + ν.hOrd);
the TOTAL form is the SEPARATE gated extension H1-U14, never a row field].
Semantic-guardian flag (blueprint §5.1): `faithful_at`'s guard choice is the
E-PHASE-flagged σ.R-rendering of the frame residual (HC2 `SideReads` (iii) note) —
the same convention U31's gate adjudicated; any strengthening to the total form goes
through H1-U14's falsifier gate first. -/
structure GrBKeyLaws (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (KB : KPBlock σ' M) : Prop where
  link_e : σ'.e = ν.e
  link_h : σ'.h = ν.h
  link_prev : σ'.wPrev = ν.σ.w
  link_key : IsNodeLift ν σ'.Φ
  key_res : ∃ (c : (↥ν.σ.K)ˣ) (k : ℤ),
    ν.σ.R σ'.Φ = LaurentPolynomial.C (c : ↥ν.σ.K) * LaurentPolynomial.T k *
      Polynomial.toLaurent ν.ψ
  faithful_at : letI := M.Rg.ring; ∀ f : Polynomial ℤ_[p], f ≠ 0 →
    HasAnchorK (ν.σ.R f) ν.a ν.Ranch →
    (KB.ψhom ^ ν.μ ∣ M.S.initialForm f ∧ ¬ KB.ψhom ^ (ν.μ + 1) ∣ M.S.initialForm f)

/-- H1-U4 — the (H1)(d) site block: what Step 6's Lean consumers fire per order-≥ 2
site. Site-realization is the CONSUMER's predicate (Step-6 wiring supplies it);
membership here is by the (ν, σ', M) data alone — read order, never key degree. -/
def Key1SiteBlock (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') : Prop :=
  ∃ KB : KPBlock σ' M, GrBKeyLaws ν σ' M KB

/-- The (s5)/OP-B1 degree-block input as its own probed row (blueprint §5.3, landed
here per §5.1's REV-2 bracket): the KEY-INITIAL-FORM divisibility block stated
directly (equivalent to the ψ̂hom block modulo the `kpa_init` unit; the ȳ-degree
DERIVATION of this row is OP-B1's math, and the row RETIRES into a proved lemma when
OP-B1 lands — until then it is an explicit hypothesis of `kp_step` (H1-U8),
displayed, never silently assumed) [REV 2, findings 10/11]. -/
structure DevBound (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') :
    Prop where
  block : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
    B.natDegree < σ'.Φ.natDegree → ¬ (M.S.initialForm σ'.Φ ∣ M.S.initialForm B)

end LeanUrat.Scaffold.HDischarge.H1
