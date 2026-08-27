/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp6b
import Uniformity.ChapC.C132fd1
import Uniformity.ChapC.C107ac14

/-!
# Uniformity.ChapC.C132sg2 — the μ₃ consumer wiring: `gentow5w_two` at `(2,1,21)` (M3-SG2)

**[M3-SG2, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 row M3-SG,
second half, and §7's final wiring row): the amended GENTOW consumers fired at the landed
UNCONDITIONAL depth-2 calculus (`C132kp6b.s2Mu3_calculus_nonempty`).

## Part 0 — the packaged calculus (§7's endpoint, campaign exit gate 3)

* `s2Mu3Calculus` — §7's endpoint def verbatim (doc names `s2Mu3SourceData`/`s2Mu3SourceLaws`
  ↦ the landed `C132fd0.s2SourceDataTwo`/`s2SourceLawsTwo_of`, its two suppliers now the
  landed M3-RP10b `s2Mu3_hex` and M3-KP6b `s2Mu3_hconv`).  Deliberately a `def`, NOT a global
  `instance` (C130pk's rule: no `[FGMNCalculus …]` binder may be silently satisfied);
  the blueprint's "scoped/local instance" exposure is §7's own prescription — "A local
  `letI := s2Mu3Calculus …` then feeds the amended `gentow5w_two`" — enacted in Part 3.
* `s2_mu3_calculus_discharge` — exit gate 3's literal type, proved solely through
  `fgmn_model_calculus_nonempty`; plus six anti-drift `rfl` pins (the C130sg genre).

## Part 1 — the amended `gentow5w_two` at `(2,1,21)`: SEVEN of EIGHT legs discharged

`gentow5w_two_at_mu3_of_norm` / `s2Mu3_gentow5w_two_of_norm`.  Per-hypothesis record:

* `he' : 0 < 2`, `hf' : 0 < 1` — DISCHARGED (numerals).
* `hcop : Nat.Coprime 21 2` — DISCHARGED (`decide`).
* `hfloor : 2 * Econst 2 < 21` — DISCHARGED: the machine-checked `20 < 21` through
  `s2Bridge_Econst` (`Econst 2 = E₂`, rfl) and `s2Tower_data` (`E₂ = 10`, rfl).
* `hprev : 2 ≤ 1 → PrevGrade 21` — DISCHARGED VACUOUSLY (the A-C.17 fence: at `f' = 1`
  the premise `2 ≤ f'` is false; the branch is cancellation-only, no `PrevGrade 21` is
  asserted — exactly the amendment's design, since `S2Mu3PrevGrade 21` is FALSE at odd 21).
* `hnormdeg` — DISCHARGED: M3-FD1's `s2Mu3_B1_degree_supply` (`deg (16Φ′) = 2 < 4`).
* `hnormz` — DISCHARGED: M3-FD1's `s2Mu3_B1_nonzero_supply`.
* `hnorm` — **BLOCKED-BECAUSE (carried, and REFUTED at the μ₃ instance)**: M3-FD1's
  certificate `s2Mu3_B1_exact_grade_supply_impossible` (via C132rp9: every polynomial of
  degree `< 4` has EVEN μ₃ grade, and the sole `d = 1` normalizer `chainNormBelow 2 21 =
  16Φ′` has degree 2, while the requested grade `21` is odd).  Landed here as
  `s2Mu3_gentow5w_two_hnorm_refuted`, the same ∀-shape negated at `s2Mu3Calculus`.

So the SIGNED conclusion `GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)` is
landed CONDITIONALLY on exactly `hnorm`, and `hnorm` is proved FALSE at this instance:
campaign exit gate 4 ("fires … using the lower-normalizer supply") CANNOT close as
written — the B-1 exact-grade family of the A-C.17/A-C.18 amended signature is
unsatisfiable at `(2,1,21)` with the canonical chain.  Flagged for the next A-C
amendment round (grade re-target of the `hnorm` family); nothing is weakened here.

## Part 3 — `gentow2_A_supply` (NODE C.103) at the μ₃ point: honest partial exposure

`s2Mu3_gentow2_A_supply` — the §7/§8 OPEN-A-SUPPLY disposition enacted: everything the μ₃
packaging supplies is discharged (the local `letI` instance, `hkey : keyAt 2 = composedKey`
by `rfl`, `hκ : 2·1·5 = 10 < 21`, `he'`/`hf'`/`hcop`, `hh : 1 ≤ h`, `hπ := h2`); the
genuinely independent inputs remain explicit binders, NOT landed (checked, none exists in
the corpus): `ρ` (the eval iso `fld 2 ≃+* AdjoinRoot ψ₂` — the OPEN-EVAL-ISO/OPEN-DICT-3-MU3
boundary), the digit string `c` with `c 0 ≠ 0`, `hliftdeg` (the `t = 0` lift-degree bound
`< D₂ = 4`), and `hadm` (admissibility of `recipe3`'s residual).  Per the campaign's
OPEN-A-SUPPLY row: "the μ₃ instance enables C.103 but does not choose its digit string or
prove `hliftdeg`/`hadm`; those remain explicit inputs."

Sorry-free, no new axiom, no statement touched, no existing file touched.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Uniformity.Density.Tower.C132sg2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp6
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132fd0 Uniformity.Density.Tower.C132fd1

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — the packaged μ₃ calculus (§7's endpoint def; exit gate 3) -/

/-- ★★★ **the μ₃ calculus, packaged** (§7's endpoint def, landed names): the CC-16
projection `fgmnCalculusOf` at the canonical chain, the M3-FD0 data record, and the laws
record fired by the two landed suppliers.  Deliberately a `def`, not an `instance`
(C130pk's rule); expose locally via `letI` (§7's own prescription, enacted in Part 3). -/
@[implicit_reducible] noncomputable def s2Mu3Calculus :
    FGMNCalculus (s2DepthTwo h2 hq) 2 1 21 :=
  fgmnCalculusOf (s2DepthTwoKeyChain h2 hq) (s2SourceDataTwo h2 hq)
    (s2SourceLawsTwo_of h2 hq (C132rp10b.s2Mu3_hex h2 hq) (C132kp6b.s2Mu3_hconv h2 hq))

/-- ★★★ **campaign exit gate 3**: the literal type, proved solely through
`fgmn_model_calculus_nonempty` (the packaging theorem, `C130pk.lean`). -/
theorem s2_mu3_calculus_discharge :
    Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  fgmn_model_calculus_nonempty (s2DepthTwoKeyChain h2 hq) (s2SourceDataTwo h2 hq)
    (s2SourceLawsTwo_of h2 hq (C132rp10b.s2Mu3_hex h2 hq) (C132kp6b.s2Mu3_hconv h2 hq))

/-- anti-drift: the packaged key ladder IS the canonical chain's. -/
theorem s2Mu3Calculus_keyAt :
    (s2Mu3Calculus h2 hq).keyAt = (s2DepthTwoKeyChain h2 hq).keyAt := rfl

/-- anti-drift: the packaged exact-grade predicate IS the μ₃ table's `S2Mu3ExactGrade`. -/
theorem s2Mu3Calculus_ExactGrade :
    (s2Mu3Calculus h2 hq).ExactGrade = S2Mu3ExactGrade h2 hq := rfl

/-- anti-drift: the packaged preceding-group predicate IS `S2Mu3PrevGrade` (evenness). -/
theorem s2Mu3Calculus_PrevGrade :
    (s2Mu3Calculus h2 hq).PrevGrade = S2Mu3PrevGrade := rfl

/-- anti-drift: the packaged normalized residual IS the landed μ₃ operator. -/
theorem s2Mu3Calculus_Rres :
    (s2Mu3Calculus h2 hq).Rres = s2Mu3NormRes h2 hq := rfl

/-- anti-drift: the packaged key-polynomial predicate IS `S2Mu3KeyPoly`. -/
theorem s2Mu3Calculus_KP :
    (s2Mu3Calculus h2 hq).KP = S2Mu3KeyPoly h2 hq := rfl

/-- anti-drift: the packaged initial equivalence IS `S2Mu3InitialEquiv`. -/
theorem s2Mu3Calculus_nuEquiv :
    (s2Mu3Calculus h2 hq).nuEquiv = S2Mu3InitialEquiv h2 hq := rfl

/-! ## Part 1 — the amended `gentow5w_two` fired at `(2,1,21)`, `hnorm` carried -/

/-- ★★ **the A-C.17/A-C.18-amended `gentow5w_two` at the μ₃ point, general instance form**:
for ANY depth-2 calculus at `(2,1,21)` carrying the canonical chain pin, all supply legs
are discharged (module docstring's per-hypothesis record) EXCEPT the exact-grade family
`hnorm`, carried as the sole hypothesis.  The `hprev` fence is vacuous at `f' = 1`. -/
theorem gentow5w_two_at_mu3_of_norm (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt)
    (hnorm : ∀ d, 0 < d → d ≤ 1 → I.ExactGrade (d * 21) (I.chainNormBelow 2 (d * 21))) :
    GENTOW5W (s2DepthTwo h2 hq) 2 1 21 I := by
  have hE : (s2DepthTwo h2 hq).Econst 2 = 10 :=
    (s2Bridge_Econst h2 hq).trans (s2Tower_data h2 hq).2.2.2.2
  exact C107ac14.gentow5w_two (s2DepthTwo h2 hq) 2 1 21 I
    (by norm_num) (by norm_num) (by decide)
    (by rw [hE]; norm_num)
    (fun hcon => absurd hcon (by norm_num))
    hnorm
    (s2Mu3_B1_degree_supply h2 hq I hkey)
    (s2Mu3_B1_nonzero_supply h2 hq I hkey)

/-- ★★ the packaged-instance corollary: the SIGNED conclusion
`GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)`, conditional on exactly
`hnorm` — which Part 2 proves FALSE at this instance (the honest record). -/
theorem s2Mu3_gentow5w_two_of_norm
    (hnorm : ∀ d, 0 < d → d ≤ 1 →
      (s2Mu3Calculus h2 hq).ExactGrade (d * 21)
        ((s2Mu3Calculus h2 hq).chainNormBelow 2 (d * 21))) :
    GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq) :=
  gentow5w_two_at_mu3_of_norm h2 hq (s2Mu3Calculus h2 hq) rfl hnorm

/-! ## Part 2 — BLOCKED-BECAUSE: the carried `hnorm` is FALSE at the μ₃ instance -/

/-- ★★ **BLOCKED-BECAUSE certificate at the consumer's own shape**: the one carried
hypothesis of `s2Mu3_gentow5w_two_of_norm` is unsatisfiable — M3-FD1's impossibility
(`16Φ′` has even μ₃ grade; `21` is odd) read through the `rfl` grade pin.  The amended
`gentow5w_two`'s B-1 exact-grade family cannot be supplied at `(2,1,21)`. -/
theorem s2Mu3_gentow5w_two_hnorm_refuted :
    ¬ (∀ d, 0 < d → d ≤ 1 →
      (s2Mu3Calculus h2 hq).ExactGrade (d * 21)
        ((s2Mu3Calculus h2 hq).chainNormBelow 2 (d * 21))) :=
  s2Mu3_B1_exact_grade_supply_impossible h2 hq (s2Mu3Calculus h2 hq) rfl

/-! ## Part 3 — `gentow2_A_supply` (NODE C.103) exposed at the μ₃ point

The local-instance exposure (§7's `letI` prescription) feeding the landed C.103 supply
theorem.  What packaging supplies is discharged; the genuinely independent inputs `ρ`, `c`,
`hc0`, `hliftdeg`, `hadm` remain explicit binders — NOT landed anywhere (module docstring's
OPEN-A-SUPPLY / OPEN-EVAL-ISO record); an honest defer, per the blueprint row ("as soon as
its independent `c`/`hliftdeg`/`hadm` inputs are supplied"). -/

/-- ★ **NODE C.103 at the μ₃ point** (`C99r.gentow2_A_supply` through the packaged
instance): the recipe-key certificate at `(2,1,21)` over `s2Tower`, with `hkey`/`hκ` and
all numeral legs discharged by packaging, conditional on exactly the five independent
inputs the campaign's OPEN-A-SUPPLY row leaves to the caller. -/
theorem s2Mu3_gentow2_A_supply
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (ρ : (s2DepthTwo h2 hq).fld 2 ≃+* AdjoinRoot (s2Tower h2 hq).ψ₂)
    (c : ℕ → AdjoinRoot (towerLabel (s2Tower h2 hq))) (hc0 : c 0 ≠ 0)
    (hliftdeg : ∀ t, t < 1 →
      (k2DigitLift (s2Tower h2 hq) (c t) ((1 - t) * 21)).natDegree < (s2Tower h2 hq).D₂)
    (hadm : Irreducible ((s2Mu3Calculus h2 hq).Rres
        (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c)) ∧
      ((s2Mu3Calculus h2 hq).Rres (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c)).natDegree = 1 ∧
      ((s2Mu3Calculus h2 hq).Rres (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c)).coeff 0 ≠ 0) :
    (s2Mu3Calculus h2 hq).KP (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c) ∧
      Irreducible (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c) ∧
      ¬ (s2Mu3Calculus h2 hq).nuEquiv (C99r.recipe3 (s2Tower h2 hq) 2 1 21 c)
          (composedKey (s2Tower h2 hq)) := by
  letI I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21 := s2Mu3Calculus h2 hq
  have hh : 1 ≤ (s2Frame h2 hq).h := by
    have hval := (s2Frame_data h2 hq).2.2.1
    omega
  have hκ : (s2Tower h2 hq).e₂ * (s2Tower h2 hq).f₂ * (s2Tower h2 hq).u₂ < 21 := by
    obtain ⟨he₂, hf₂, hu₂, -, -⟩ := s2Tower_data h2 hq
    rw [he₂, hf₂, hu₂]
    norm_num
  exact C99r.gentow2_A_supply (s2Tower h2 hq) h2 hh (s2DepthTwo h2 hq) 2 1 21
    (I := I) rfl ρ hκ (by norm_num) (by norm_num) (by decide) c hc0 hliftdeg hadm

end S2

end Uniformity.Density.Tower.C132sg2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus
#print axioms Uniformity.Density.Tower.C132sg2.s2_mu3_calculus_discharge
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_keyAt
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_ExactGrade
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_PrevGrade
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_Rres
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_KP
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3Calculus_nuEquiv
#print axioms Uniformity.Density.Tower.C132sg2.gentow5w_two_at_mu3_of_norm
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3_gentow5w_two_of_norm
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3_gentow5w_two_hnorm_refuted
#print axioms Uniformity.Density.Tower.C132sg2.s2Mu3_gentow2_A_supply

end AxCheck
