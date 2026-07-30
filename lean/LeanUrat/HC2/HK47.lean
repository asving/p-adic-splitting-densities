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
(R-a) The blueprint's bare iff display is stated AT THE GATE STAGE — keyed at `bStageP`
  (RATIFIED RE-KEY 2026-07-30, see below), NOT a general σ: the iff is FALSE for a
  general σ (`IsReadLift` weights read σ.w where `IsStandardLift` reads σ.wPrev). At
  bStageP: σ.w = bw and σ.wPrev = gaussVal, which AGREE ON THE COEFFICIENT CARRIER
  `inC X` (constants: both are v₂ of the constant) — the realizer clauses constrain
  `tt k` to that carrier, and σ.t = 0 collapses both position exponents to 0, so the
  shapes match; this is exactly the K-4 seam check the unit exists to compile. (At the
  pre-re-key literal `U31.bStage` the two fields were the same function `bw` — the
  agreement leg of the P-phase proof upgrades from byte-identity to the carrier
  agreement `gaussVal ≡ bw on inC X`, an HK-13 supply.) Two side hypotheses `ψ.Monic`
  and `ψ.natDegree = g` are ADDED: `IsStandardLift` carries them as
  leading conjuncts while `IsReadLift` does not, so the bare → direction is otherwise
  underivable — the minimal faithful completion of the display (they are TransHyp fields
  hmonic/hdeg at every use site, so no consumer strengthens).
(R-KEY, RATIFIED 2026-07-30) Every "bStage" occurrence is keyed at `bStageP` (HK-13's
  base-pin re-dress), not the literal `U31.bStage`: `StageCoreL U31.bStage` is REFUTABLE
  (`reps = []` refutes `reps_nonempty`/`p_is_rep`; `wPrev = bw`, `bw X = 1` refutes
  `prevIaug`), and (b)'s `TransHyp.hlift = IsStandardLift` reads σ.wPrev — at the
  literal it would read the junk `bw` off-carrier choice. bStageP differs from
  `U31.bStage` ONLY in (wPrev := gaussVal, reps := [C 2], Tvec := [(C 2,1)]); the
  recorded gate data (w = bw, R = bR, Φ = X, (e,h,s,t) = (1,1,1,0), K = K₂, ψ₂, fq,
  ν₀.zbar) are byte-identical. Full record: `HK13_bStageCoreP1a.lean` module header.
(R-b) The blueprint's `(ν₁.e) (ν₁.h)` binders are the LITERALS (1, 3) — ν₁ is HK-18's
  data and its recorded pair is definitionally (1, 3) (`HK18.ν₁gate_pair`); binding the
  literals breaks the ν₁-before-σ₁ circularity (HK-15 builds σ₁ at this pair, then ν₁'s
  frame is σ₁). zbar₀ := `U31.ν₀.zbar` (the root node's recorded residue root — HK-18's
  ν₀gate records the same unit).

PROOF SKETCH (P-phase):
(a) both directions are clause-by-clause transports: at bStageP, w = bw and
  wPrev = gaussVal agree on the carrier `inC X` (constants — where the realizers live)
  and t = 0, so realizer weight/position clauses coincide; e' = σ.e = 1
  makes the Φhat display identical; → adds the (hmon, hdeg) conjuncts from the
  hypotheses, ← drops them.
(b) fields: hmonic/hirr/hdeg = U31's private ψ₂ lemmas (de-privatize or reprove);
  hne_z: ψ₂ ≠ X by coeff-0 (1 ≠ 0); hg: 1 ≤ 2; hlift: `IsStandardLift bStageP ψ₂ 2 fq`
  with U31's landing witness (tt₀ = C 4 at wPrev-weight gaussVal (C 4) = 2 = 1·(2−0)
  (= the old bw-weight — constants), tt₁ = C 2 at
  weight 1, positions T(−0·…) = T 0; fq = X² + tt₁·X + tt₀ — `landingKey_ν₀`'s
  realizer re-read at the frame pair via (a)); he'/hh': 1 ≤ 1, 1 ≤ 3; hcop:
  gcd 1 3 = 1; hiaug: (3 : ℤ) > 1·bw fq = 2 (bw_eq NF_θ_fq — THE concrete steepness
  check; w is untouched by the re-dress); hroot: aeval r₀ (ψ₂.map subtype) = 0 from
  U31's r₀ properties.
Difficulty routine-opus ~50 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK18
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.HC1.DefsTower

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK47

open HK18

/-- HK-47 deliverable (a): THE FRAME-PAIR LIFT CONVERSION at the gate stage — at
`bStageP` (RATIFIED RE-KEY 2026-07-30: the literal `U31.bStage` hosts a refutable
`StageCoreL` — HK-13's finding; here w = bw and wPrev = gaussVal agree on the realizer
carrier `inC X`, and t = 0), the read-pair lift predicate at the
frame pair (σ.e, σ.h) = (1, 1) IS the D.5 standard-lift predicate. The (hmon, hdeg)
hypotheses complete `IsStandardLift`'s leading conjuncts (E-phase resolution R-a). -/
theorem readLift_iff_standardLift (ψ : Polynomial ↥bStageP.K) (g : ℕ)
    (hmon : ψ.Monic) (hdeg : ψ.natDegree = g) (Φhat : Polynomial ℤ_[2]) :
    IsReadLift bStageP ψ g bStageP.e bStageP.h Φhat ↔
      IsStandardLift bStageP ψ g Φhat := by
  sorry

/-- HK-47 deliverable (a), consumer form (the K-4 seam made compilable): the recorded
root-read lift `IsNodeLift ν₀gate Φ̂` (= `IsReadLift` at the root read pair = frame
pair, `isNodeLift_iff`) converts to the `TransHyp.hlift` shape. Coherently keyed:
`ν₀gate.σ = bStageP` after the ratified re-key (HK-18 R-3 / HK-13's finding). -/
theorem nodeLift_to_standardLift (Φhat : Polynomial ℤ_[2]) :
    IsNodeLift ν₀gate Φhat → IsStandardLift bStageP U31.ψ₂ 2 Φhat := by
  sorry

/-- HK-47 deliverable (b): THE ASSEMBLED TRANSITION HYPOTHESIS at the gate — the full
D.3–D.7 increment interface for the root read (bStageP, ψ₂, g = 2) landing on
Φ̂ = fq, keyed at the NEXT pair (ν₁.e, ν₁.h) = (1, 3) (E-phase resolution R-b), with
zbar₀ = the recorded residue root. hiaug is the concrete steepness 3 > 1·bStageP.w fq
= 2 (w = bw, untouched by the re-dress). Feeds `S9c_coreAssembly` at
hEG : 1 < bStageP.e·g = 2 (HK-16/HK-17). RATIFIED RE-KEY 2026-07-30: keyed at
`bStageP`, not the refutable-core literal `U31.bStage` — hlift reads σ.wPrev, sound
only at the base pin (resolution R-KEY / HK-13's finding record). -/
theorem transHyp_gate :
    LeanUrat.HC1.TransHyp bStageP U31.ψ₂ 2 U31.fq 1 3 U31.ν₀.zbar := by
  sorry

/-- The assembled pair IS ν₁'s recorded read pair (rfl-grade; the blueprint's
`(ν₁.e) (ν₁.h)` binders resolved — resolution R-b's certificate). -/
theorem transHyp_pair_matches (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) :
    (ν₁gate σ₁ hΦ).e = 1 ∧ (ν₁gate σ₁ hΦ).h = 3 :=
  ν₁gate_pair σ₁ hΦ

end HK47

end LeanUrat.MovesJ
