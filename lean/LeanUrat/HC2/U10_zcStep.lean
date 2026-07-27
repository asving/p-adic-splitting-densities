/-
Unit U10.zc_step  (HC-2 campaign, E-phase — blueprint §5 Layer B: THE HARD CORE OF THE
HARD CORE; the pre-declared escalation-risk center)
moves_ref: §C C.1.5 (per-step conditional exactness): "(1) multiplies the mass by exactly
vol_nom(E_fresh(ν_{i+1})); (2) re-establishes (ZC)".
deps: U3–U7, S (zcSeed, Theta_uni, pres_block), C0.pinTransport, C2.freshFree, C3.lineDom,
hreal (per-step `TransitionAdmissible` via `Realizable`).  difficulty: HARD ×4.
PRE-SPLIT (mandatory, blueprint): U10a floor-monotone downset transport; U10b fresh-cut
downset exactness; U10c interior zeros; U10d rim-lead placement/confinement. The E-phase
renderings below are the elaborator's best-faith decomposition (flagged in MANIFEST;
prover refinement authorized). Whatever step resists derivation is a candidate zcSeed law
(D5's fence) — via the stuck rule, NEVER a silent axiom.
hypothesis_fields: S.zcSeed, hreal.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- U10a — floor-monotone downset TRANSPORT: pins standing before read `i+1` that stay
interior to the NEW rim sit at-or-below the NEW floor (at the new frame's heights). -/
theorem zc_step_transport {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+1)).pinned j = true →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
        ≤ H.floorH (i+2) (boxChart n N j).2 := by
  sorry

/-- U10b — fresh-cut downset EXACTNESS: an interior at-or-below-new-floor coordinate is
pinned after read `i+1` (old pin or fresh cut — the downset grows by exactly the strip
zeros + the sub-line levels). -/
theorem zc_step_freshExact {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
          ≤ H.floorH (i+2) (boxChart n N j).2 →
      (mkSigma H n N S vOf (i+2)).pinned j = true := by
  sorry

/-- U10c — interior ZEROS: interior pins of the new state solve to the literal 0. -/
theorem zc_step_interiorZero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+2)).pinned j = true →
      ∀ f : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf (i+2)).solve j f = 0 := by
  sorry

/-- U10d — rim-lead PLACEMENT/CONFINEMENT: every pin of the new state sits inside the
standing read's constraint region (base index < the OLD rim = `prevRim (i+2)`'s
predecessor region; no fresh pin escapes the factor interior — §C rim rule / DOM(3)). -/
theorem zc_step_confine {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N), (mkSigma H n N S vOf (i+2)).pinned j = true →
      (boxChart n N j).2 < H.prevRim n (i + 1) := by
  sorry

/-- U10 assembled — the inductive step: (ZC) at prefix `i+1` re-establishes (ZC) at
prefix `i+2` (the `i+1` instance of `JetSetup.zc` from the `i` instance). -/
theorem zc_step {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (ih : ZCData (mkSigma H n N S vOf (i+1)) (boxChart n N) (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) :
    ZCData (mkSigma H n N S vOf (i+2)) (boxChart n N) (H.htH (i+2)) (H.floorH (i+2))
      ((H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) := by
  sorry

end LeanUrat.MovesJ
