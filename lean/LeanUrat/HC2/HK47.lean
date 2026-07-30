/-
Unit HK-47  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton;
NEW unit at REVISION 2, finding 9)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-47.

INFORMAL STATEMENT (blueprint): "The S9→(NEW) interface, NAMED (the K-4 obligation made
compilable): (a) the frame-pair lift conversion, named — `IsReadLift σ ψ g σ.e σ.h Φ̂ ↔
IsStandardLift σ ψ g Φ̂` (the recorded `IsNodeLift ν₀` is `IsReadLift` at the root read
pair = frame pair, `isNodeLift_iff`); (b) the assembled `TransHyp bStage ψ₂ 2 Φ̂ (ν₁.e)
(ν₁.h) zbar₀`, hiaug checked concretely (`ν₁.h > ν₁.e·bStage.w Φ̂` — HK-18 chooses ν₁'s
data to satisfy it). If (a)'s shapes fail to match, STOP and report the exact mismatch
(a K-4 seam residue, surfaced — never papered over)."  deps: HK-13 (StageCoreL bStage
facts, not needed for the statements), HK-15 (σ₁ — enters only through HK-18's
parameterized ν₁gate in the pair-tie lemma), HK-18.

E-PHASE RESOLUTIONS (recorded):
(R-a) The blueprint's bare iff display is stated AT THE GATE STAGE `U31.bStage` (the
  unit's charge is the gate interface, and the iff is FALSE for a general σ: `IsReadLift`
  weights read σ.w where `IsStandardLift` reads σ.wPrev — at bStage both fields are the
  SAME function `bw`, and σ.t = 0 collapses both position exponents to 0, so the shapes
  match; this is exactly the K-4 seam check the unit exists to compile). Two side
  hypotheses `ψ.Monic` and `ψ.natDegree = g` are ADDED: `IsStandardLift` carries them as
  leading conjuncts while `IsReadLift` does not, so the bare → direction is otherwise
  underivable — the minimal faithful completion of the display (they are TransHyp fields
  hmonic/hdeg at every use site, so no consumer strengthens).
(R-b) The blueprint's `(ν₁.e) (ν₁.h)` binders are the LITERALS (1, 3) — ν₁ is HK-18's
  data and its recorded pair is definitionally (1, 3) (`HK18.ν₁gate_pair`); binding the
  literals breaks the ν₁-before-σ₁ circularity (HK-15 builds σ₁ at this pair, then ν₁'s
  frame is σ₁). zbar₀ := `U31.ν₀.zbar` (the root node's recorded residue root — HK-18's
  ν₀gate records the same unit).

PROOF SKETCH (P-phase):
(a) both directions are clause-by-clause transports: at bStage, w ≡ wPrev ≡ bw
  (definitional) and t = 0, so realizer weight/position clauses coincide; e' = σ.e = 1
  makes the Φhat display identical; → adds the (hmon, hdeg) conjuncts from the
  hypotheses, ← drops them.
(b) fields: hmonic/hirr/hdeg = U31's private ψ₂ lemmas (de-privatize or reprove);
  hne_z: ψ₂ ≠ X by coeff-0 (1 ≠ 0); hg: 1 ≤ 2; hlift: `IsStandardLift bStage ψ₂ 2 fq`
  with U31's landing witness (tt₀ = C 4 at wPrev = bw-weight 2 = 1·(2−0), tt₁ = C 2 at
  weight 1, positions T(−0·…) = T 0; fq = X² + tt₁·X + tt₀ — `landingKey_ν₀`'s
  realizer re-read at the frame pair via (a)); he'/hh': 1 ≤ 1, 1 ≤ 3; hcop:
  gcd 1 3 = 1; hiaug: (3 : ℤ) > 1·bw fq = 2 (bw_eq NF_θ_fq — THE concrete steepness
  check); hroot: aeval r₀ (ψ₂.map subtype) = 0 from U31's r₀ properties.
Difficulty routine-opus ~50 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK18
import LeanUrat.HC1.DefsTower

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK47

open HK18

/-- HK-47 deliverable (a): THE FRAME-PAIR LIFT CONVERSION at the gate stage — at
`U31.bStage` (where w = wPrev = bw and t = 0), the read-pair lift predicate at the
frame pair (σ.e, σ.h) = (1, 1) IS the D.5 standard-lift predicate. The (hmon, hdeg)
hypotheses complete `IsStandardLift`'s leading conjuncts (E-phase resolution R-a). -/
theorem readLift_iff_standardLift (ψ : Polynomial ↥U31.bStage.K) (g : ℕ)
    (hmon : ψ.Monic) (hdeg : ψ.natDegree = g) (Φhat : Polynomial ℤ_[2]) :
    IsReadLift U31.bStage ψ g U31.bStage.e U31.bStage.h Φhat ↔
      IsStandardLift U31.bStage ψ g Φhat := by
  sorry

/-- HK-47 deliverable (a), consumer form (the K-4 seam made compilable): the recorded
root-read lift `IsNodeLift ν₀gate Φ̂` (= `IsReadLift` at the root read pair = frame
pair, `isNodeLift_iff`) converts to the `TransHyp.hlift` shape. -/
theorem nodeLift_to_standardLift (Φhat : Polynomial ℤ_[2]) :
    IsNodeLift ν₀gate Φhat → IsStandardLift U31.bStage U31.ψ₂ 2 Φhat := by
  sorry

/-- HK-47 deliverable (b): THE ASSEMBLED TRANSITION HYPOTHESIS at the gate — the full
D.3–D.7 increment interface for the root read (bStage, ψ₂, g = 2) landing on
Φ̂ = fq, keyed at the NEXT pair (ν₁.e, ν₁.h) = (1, 3) (E-phase resolution R-b), with
zbar₀ = the recorded residue root. hiaug is the concrete steepness 3 > 1·bStage.w fq
= 2. Feeds `S9c_coreAssembly` at hEG : 1 < bStage.e·g = 2 (HK-16/HK-17). -/
theorem transHyp_gate :
    LeanUrat.HC1.TransHyp U31.bStage U31.ψ₂ 2 U31.fq 1 3 U31.ν₀.zbar := by
  sorry

/-- The assembled pair IS ν₁'s recorded read pair (rfl-grade; the blueprint's
`(ν₁.e) (ν₁.h)` binders resolved — resolution R-b's certificate). -/
theorem transHyp_pair_matches (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) :
    (ν₁gate σ₁ hΦ).e = 1 ∧ (ν₁gate σ₁ hΦ).h = 3 :=
  ν₁gate_pair σ₁ hΦ

end HK47

end LeanUrat.MovesJ
