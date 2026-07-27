/-
Unit U9.zc_root  (HC-2 campaign, E-phase — blueprint §5 Layer B, the (ZC) base)
moves_ref: §C C.2 proof "initialized at the root (C.1.5's base = D.8 + D.11 at ν₀)".
deps: U7, D6/D7, S.zcSeed, U11.  difficulty: hard — PRE-SPLIT (mandatory): U9a downset ⊆,
U9b ⊇, U9c interior_zero (the two `ZCData` fields, split).
hypothesis_fields: S.zcSeed.
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

/-- U9a — root downset, ⊆ direction: after the root read, every interior pin sits
at-or-below the frame-1 floor. -/
theorem zc_root_downset_mp {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      (mkSigma H n N S vOf 1).pinned j = true →
      ((H.htH 1 (boxChart n N j) : ℚ) : WithBot ℚ) ≤ H.floorH 1 (boxChart n N j).2 := by
  sorry

/-- U9b — root downset, ⊇ direction: every interior at-or-below-floor coordinate is
pinned (the root band exhausts the downset; root_height puts the floor at ≥ 1). -/
theorem zc_root_downset_mpr {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      ((H.htH 1 (boxChart n N j) : ℚ) : WithBot ℚ) ≤ H.floorH 1 (boxChart n N j).2 →
      (mkSigma H n N S vOf 1).pinned j = true := by
  sorry

/-- U9c — root interior zeros: interior pins solve to the literal constant 0. -/
theorem zc_root_interior_zero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      (mkSigma H n N S vOf 1).pinned j = true →
      ∀ f : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf 1).solve j f = 0 := by
  sorry

/-- U9 assembled — the i = 0 instance of `JetSetup.zc` for the constructed chain. -/
theorem zc_root {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ZCData (mkSigma H n N S vOf 1) (boxChart n N) (H.htH 1) (H.floorH 1)
      ((H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth) := by
  sorry

end LeanUrat.MovesJ
