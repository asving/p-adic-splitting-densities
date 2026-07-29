/-  MovesV unit V3-1 `entshape_postsplit` (RE-SCOPED Codex-5; RE-TARGETED
    REV 6, Codex5-23) — post-split typing: label injectivity in σ_sel + the
    SelMatches semantic leg via MovesD's PROVED E8_rankInj.
    Also the §8-listed obligation `eligibleImage_finite` (owner: THIS file). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- (a) the LABEL layer's σ_sel injectivity. -/
theorem entshape_selRec_ne {n : ℕ} (ε ε' : EntShapeV n)
    (h : ε.selRec ≠ ε'.selRec) : ε ≠ ε' :=
  fun he => h (by rw [he])

/-- (b) the SEMANTIC LEG: distinct realized selection indices at slot r admit
NO COMMON SelMatches label (E8_rankInj/E7 territory, consumed through the
realized index inequality). -/
theorem selmatches_separates {n : ℕ} {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {pol : MovesD.CanonPolicy p F} (ε : EntShapeV n)
    (i i' : MovesD.PrefIdx n pol ε.Phat) (r : ℕ) (hr : r < ε.selRec.length)
    (R : MovesD.ShapeRead) (ν ν' : MovesC.Node p F)
    (hbr : branchingRead? n ε.Phat r = some R)
    (hν : nodeAt i r = some ν) (hν' : nodeAt i' r = some ν')
    (hne : MovesD.selRank R.w ν % R.mbar ≠ MovesD.selRank R.w ν' % R.mbar) :
    ¬ (SelMatches ε i ∧ SelMatches ε i') := by
  rintro ⟨h1, h2⟩
  exact hne ((h1 r hr R ν hbr hν).symm.trans (h2 r hr R ν' hbr hν'))

/-- the §2.D FINITENESS OBLIGATION (typed row at REV 9, Codex-8 M-1),
stated at exactly the docstring's route. -/
theorem eligibleImage_finite {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (w : ℕ) (ν : MovesC.Node p F) :
    Finite {q : Polynomial F //
      MovesD.EligibleImage p w ν.g ν.μ (MovesD.RanchImage ν) q} := by
  sorry

end LeanUrat.MovesV
