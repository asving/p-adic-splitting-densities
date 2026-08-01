/- H1 blueprint compile probe — NOT a landed unit; deleted after probing. -/
import LeanUrat.MovesGr.Defs
import LeanUrat.MovesC.Defs
import LeanUrat.HC2.Defs

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- PROBE H1-U2: the key-compliance block (KPa)+(KPirr) at a staged graded model. -/
structure KPBlock (σ' : Stage p F) (M : GenuineStageModel σ') where
  ψhom : M.S.Gr
  homog : ∃ (γ : ℤ) (x : M.S.grPiece γ), ψhom = DirectSum.of (fun γ => M.S.grPiece γ) γ x
  kpa_init : letI := M.Rg.ring; ∃ u : (M.S.Gr)ˣ, M.S.initialForm σ'.Φ = (u : M.S.Gr) * ψhom
  kpirr : letI := M.Rg.ring; Prime ψhom
  kpa_block : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
    B.natDegree < σ'.Φ.natDegree → ¬ ψhom ∣ M.S.initialForm B

/-- PROBE H1-U3: (GR-B) clauses (3)+(4) keyed to the creating read. -/
structure GrBKeyLaws (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (KB : KPBlock σ' M) : Prop where
  key_res : ∃ (c : (↥ν.σ.K)ˣ) (k : ℤ),
    ν.σ.R σ'.Φ = LaurentPolynomial.C (c : ↥ν.σ.K) * LaurentPolynomial.T k *
      Polynomial.toLaurent ν.ψ
  faithful : letI := M.Rg.ring; ∀ (f : Polynomial ℤ_[p]) (a : ℤ) (Rf : Polynomial ↥ν.σ.K),
    f ≠ 0 → HasAnchorK (ν.σ.R f) a Rf →
    ∀ μf : ℕ, OrdPsiPoly ν.ψ Rf μf ↔
      (KB.ψhom ^ μf ∣ M.S.initialForm f ∧ ¬ KB.ψhom ^ (μf + 1) ∣ M.S.initialForm f)

/-- PROBE H1-U13: the (H1)(d) site block. -/
def Key1SiteBlock (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') : Prop :=
  ∃ KB : KPBlock σ' M, GrBKeyLaws ν σ' M KB

/-- PROBE H1-U8 statement shape (kp_step). -/
theorem kp_step_probe (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h) :
    Nonempty (KPBlock σ' M) := sorry

/-- PROBE: TransitionCoreL arity check. -/
example (σV σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) : Prop :=
  TransitionCoreL σV σ' Φhat e' h' zbar

/-- PROBE: HistoryCoherent + ReadsOf name checks. -/
example (H : History p F) : Prop := HistoryCoherent H

end LeanUrat.Scaffold.HDischarge.H1
