/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V3_readLift

/-!
# HC1.V4_readLanding — (BOX)+(VERTEX) at the ReadFrame (blueprint §10, V4)

V′-KERNEL unit (blueprint §10.1): for f ≠ 0 with anchored RV-data of ψ-order μ,
the Φ̂-development satisfies

* (VERTEX) `wV(B_μ) + μ·e★h★g = wV(f)` with `B_μ ≠ 0`;
* (BOX)    `wV(B_m) + m·e★h★g > wV(f)` for every m < μ with `B_m ≠ 0`;
* the vertex digit with its explicit unit `z̄^{−μ·m̂★}` (`m̂★ = −t★h★g`), for
  consumers that want it (the L5_landVertexDigit shape, transposed to RV).

moves_ref: D.8 (BOX)/(VERTEX) VERBATIM (MOVES 2469–2490: the displayed proof —
K1 + D.1(e) + D.3(d) distinct ψ-orders — consumes NOTHING beyond the ReadFrame
pack; S6/valgrp are untouched, which is what makes Finding 3 harmless).  The
Lean pattern: L5_landVertex/L5_landVertexDigit transplanted to the pack.
deps: V3. difficulty: HARD-ish but bounded (one L5-sized file).

**FENCE (per §10.1): the (TRANSPORT) leg is NOT needed by any of the three
discharges — it is fenced OUT of this unit (recorded as available follow-on);
this file states (BOX)+(VERTEX)+the vertex digit only.**
E-phase: statement per §10.1, `sorry` body.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

/-- Unit V4: the D.8 landing at the ReadFrame — (VERTEX), (BOX), and the vertex
digit with its explicit unit `z̄^{μ·t★·h★·g}` (the `−μm̂★` normalization),
transposing L5_landVertex/L5_landVertexDigit to the regrade pack.  The
(TRANSPORT) leg is fenced OUT (see header). -/
theorem V4_readLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hdeg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K)
    (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) :
    (B μ ≠ 0 ∧
      childW σ σ.Φ estar hstar (B μ)
          + (μ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))
        = childW σ σ.Φ estar hstar f) ∧
    (∀ m, m < μ → B m ≠ 0 →
      childW σ σ.Φ estar hstar f
        < childW σ σ.Φ estar hstar (B m)
            + (m : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
    (∀ zbar : Fˣ, Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 →
      ∃ q : LaurentPolynomial ↥σ.K,
        V.D.Rv f = (Polynomial.toLaurent ψ) ^ μ * q ∧
        ¬ (Polynomial.toLaurent ψ ∣ q) ∧
        LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) (V.D.Rv (B μ))
          = ((zbar ^ ((μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ)) : Fˣ) : F) *
            LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) q) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V4_readLanding
