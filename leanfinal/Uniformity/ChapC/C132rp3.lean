/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp2

/-!
# Uniformity.ChapC.C132rp3 — the μ₃ graded ADD/zero laws (μ₃ campaign, node M3-RP3)

**[M3-RP3, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP3): a
mechanical port of the μ₂ coefficientwise/polynomial ADD-law engine
(`C130rp2.lean:168-183` the slot-floor bridge, `:246-296` the generic `twistRead`
zero/add bank, `:440-510` the μ₂ `graded_add` assembly) to the just-landed μ₃ total
operator `s2Mu3GradedRes` (C132rp2) and its recursive coefficient `s2Mu3Coeff` (C132rp1).

## What lands, and what does NOT (the zero law is ALREADY landed)

The campaign row's sketch names two obligations, `graded_zero_of_above` and exact-grade
additivity. The FIRST is **already discharged**: C132rp2's own Part 2 lifted C132rp1's
coefficient-level `s2Mu3Coeff_eq_zero_of_above` straight to the polynomial
(`s2Mu3GradedRes_zero_of_above`), because that node's division of labor put the
coefficient-level zero-above law among RP-1's landed inputs. Re-proving it here would be a
byte-identical duplicate, so this node instead records a SHAPE PIN
(`s2Mu3GradedRes_zero_of_above` already has EXACTLY the `FGMNSourceLaws.graded_zero_of_above`
field type at the μ₃ occurrence, checked below) and spends its budget on the genuinely
missing SECOND obligation: the μ₃ analogue of published Corollary 4.12(1).

## The ADD law, one level up

`s2Mu3Coeff`'s gate (`S2Mu3SlotOnGrade`) tests the INNER μ₂ value of a development
coefficient for EXACT equality with the on-line grade `m = (β − 21s)/2`, so additivity needs
the same "floor bridge, cancellation absorbed" argument the μ₂ engine used — one level up,
against `dv2Pin`/`dv2Supp` (C.11) rather than `dvHgt`/`dvSupp` (C.06/C.07), and reading OFF
the gate through the landed μ₂ zero-above law `s2GradedRes_zero_of_above` (C130rp1) instead
of a frame-level `twistRead` vanishing fact (there is no frame read at this recursive layer):

* `le_dv2Pin_of_le_dv2Supp` — the level-2 slot floor from a cleared-support floor (mirror of
  `C130rp2.le_dvHgt_of_le_dvSupp`, one level up, S2-specialized at `(u₂, ℓ₂) = (21, 2)`).
* `s2Mu3Coeff_eq_eval_of_le` — the coefficient floor bridge (mirror of
  `C130rp2.s2GradedCoeff_eq_twistRead_of_le`): on the gate, `s2Mu3Coeff` is the landed μ₂
  graded read at `m`; strictly above it, the SAME landed read vanishes
  (`s2GradedRes_zero_of_above`), so the two cases display the SAME formula.
* `s2Mu3Coeff_add` — the coefficientwise ADD law (strong form, mirror of
  `C130rp2.s2GradedCoeff_add`): on a common `dv2Supp`-floor `β`, cancellation slots (both
  summands on-line, the sum strictly above) are absorbed rather than case-split, via `dev`
  additivity (B32a) plus the μ₂ operator's OWN landed add law (`s2GradedRes_add_of_le`,
  C130rp2) applied at the shared inner grade `m`.
* `s2Mu3GradedRes_add_of_le` / `s2Mu3GradedRes_add` — the polynomial lift (mirror of
  `C130rp2.s2GradedRes_add_of_le` / `.s2GradedRes_add`): the strong `dv2Supp`-floor form, and
  the `FGMNSourceLaws.graded_add` field-shape form (published Cor 4.12(1)) at the μ₃
  occurrence, both by `Polynomial.ext` against the master coefficient law
  (`s2Mu3GradedRes_coeff`, C132rp2).

## What this node does NOT claim (honesty scope)

No multiplicativity (published Cor 4.12(2)/(3): M3-RP5/RP6/KP-family), no normalization
(M3-RP8), no `FGMNSourceData`/`FGMNSourceLaws` record (M3-FD0). No law in the μ₂ Part 1/5 ADD
bank failed to port (BLOCKED-BECAUSE: none — the one genuinely new step is climbing the
SECOND recursion layer, i.e. reading the floor bridge through `s2GradedRes_zero_of_above`
rather than a frame-level `twistRead` fact; every other step is the μ₂ argument shape
verbatim). The OPEN-RP1-TRANSPORT faithfulness split stays exactly as C132rp1/rp2 left it; no
theorem here touches it.

**DEPENDS.** C132rp2 (`s2Mu3GradedRes`, `s2Mu3GradedRes_coeff`, `s2Mu3GradedRes_zero_of_above`)
· C132rp1 (`s2Mu3Coeff`, `S2Mu3SlotOnGrade`, `s2Mu3SlotOnGrade_iff`,
`s2Mu3Coeff_eq_zero_of_grade_lt`, `s2Mu3Coeff_eq_eval`, `dv2Hgt_eq_dvSupp`) · C132rp0
(`S2Mu3ExactGrade`, `S2Mu3AboveGrade`, `S2Mu3ExactGrade_iff_dv2Supp`) · C132nv1 (`s2Φ₂_monic`,
`s2Φ₂_natDegree`) · C132nv0 (`dv2Pin_top_of_gt`) · C130rp2 (`s2GradedRes_add_of_le`,
`weight_read` via `C130nv2`) · C130rp1 (`s2GradedRes_zero_of_above`, `s2GradedRes`) · C130rp0
(`S2AboveGrade`, `S2AboveGrade_iff_dvSupp`) · C130s2 (`s2Tower`, `s2Frame`,
`s2DepthTwoKeyAt`) · C130s6 (`min_dvSupp_le_dvSupp_add`) · B32a (`dev_add_of_monic`) · C118a
(`smul_top_pos`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch and the μ₂ porting pattern.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the level-2 floor bridge (S2-specialized mirror of `C130rp2` Part 1)

`dv2Supp` (C.11) has EXACTLY `dvSupp`'s shape one recursion layer up
(`(Finset.range (f.natDegree+1)).inf (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂*j:ℕ∞))`), so the
"slot floor from a cleared-support floor" argument ports verbatim, specialized here at the S2
μ₃ side `(u₂, ℓ₂) = (21, 2)` and key `Ψ = Φ₂ := s2DepthTwoKeyAt h2 hq 2`. -/

/-- the level-2 term bound (S2-specialized mirror of `C131y.dvSupp_le_term`, one level up):
`dv2Supp` is bounded by ANY single slot's weighted term. Kept generic in `(u₂, ℓ₂)` — as
`weight_read` is — so the numeral instantiation happens only at the call site, never inside
the proof (the numeral/`Nat.cast` seam this avoids is C.11's own documented coercion seam). -/
private theorem dv2Supp_le_term (f : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (s : ℕ) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f u₂ ℓ₂
      ≤ ℓ₂ • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f s
          + (u₂ * s : ℕ∞) := by
  by_cases hs : s ≤ f.natDegree
  · rw [dv2Supp]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  · rw [dv2Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) f (not_le.mp hs),
      C118a.smul_top_pos hℓ₂, top_add]
    exact le_top

/-- ★ **the level-2 slot floor from a cleared-support floor** (S2-specialized mirror of
`C130rp2.le_dvHgt_of_le_dvSupp`, one level up): the μ₃-campaign engine node RP-3 needs, and
RP-5's convolution recursion will need again. Generic in `(u₂, ℓ₂)` for the same
numeral-seam reason as `dv2Supp_le_term`; RP-3 instantiates it at `(21, 2)`. -/
theorem le_dv2Pin_of_le_dv2Supp {u₂ ℓ₂ β m s : ℕ} {f : Polynomial O} (hℓ₂ : 0 < ℓ₂)
    (hβ : (β : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f u₂ ℓ₂)
    (hm : ℓ₂ * m + u₂ * s = β) :
    (m : ℕ∞) ≤ dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f s := by
  have h : (β : ℕ∞)
      ≤ ℓ₂ • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f s
        + (u₂ * s : ℕ∞) := le_trans hβ (dv2Supp_le_term h2 hq f u₂ hℓ₂ s)
  rcases eq_or_ne
      (dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f s) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, C130nv2.weight_read] at h
  rw [← hc]
  have hnat : β ≤ ℓ₂ * c + u₂ * s := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ₂ * m ≤ ℓ₂ * c) hℓ₂

/-! ## Part 2 — the coefficient floor bridge (mirror of
`C130rp2.s2GradedCoeff_eq_twistRead_of_le`)

On the gate, `s2Mu3Coeff` reads the landed μ₂ operator at the true inner grade
(`s2Mu3Coeff_eq_eval`); strictly above it, the gate is false (the exact-equation cannot hold
past a strict inequality) AND the SAME landed μ₂ read vanishes there
(`s2GradedRes_zero_of_above`) — so both cases display the identical formula, and additivity
below is `dev` additivity plus the μ₂ operator's OWN add law, not a fresh case split. -/

/-- ★ **the μ₃ coefficient floor bridge**: if the inner development coefficient's landed μ₂
value sits AT OR ABOVE the on-line grade `m` (`2m + 21s = β`), the μ₃ coefficient equals the
landed μ₂ graded read of the development coefficient at `m`. -/
theorem s2Mu3Coeff_eq_eval_of_le {β t m : ℕ} {g : Polynomial O}
    (hm : 2 * m + 21 * (β % 2 + 2 * t) = β)
    (hge : (m : ℕ∞)
        ≤ dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
            (β % 2 + 2 * t)) :
    s2Mu3Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2GradedRes h2 hq m (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))) := by
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact s2Mu3Coeff_eq_eval h2 hq
      ((s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨m, heq.symm, hm⟩) heq.symm
  · have hgate : ¬ S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t) := by
      intro hgate
      obtain ⟨m', hm', hβ⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
      rw [hm'] at hlt
      have : m < m' := by exact_mod_cast hlt
      omega
    have habove : S2AboveGrade h2 hq m (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)) := by
      rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hlt
      exact (S2AboveGrade_iff_dvSupp h2 hq).mpr hlt
    unfold s2Mu3Coeff
    rw [if_neg hgate, s2GradedRes_zero_of_above h2 hq habove, Polynomial.eval_zero]

/-! ## Part 3 — ★ NODE RP-3: the coefficientwise ADD law (mirror of `C130rp2.s2GradedCoeff_add`)

On a common `dv2Supp`-floor, every μ₃ coefficient is additive — including cancellation slots
(both summands on-line, the sum above), absorbed via `dev` additivity plus the landed μ₂
operator's OWN add law read at the shared inner grade `m`. -/

theorem s2Mu3Coeff_add {β t : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2)
    (hh : (β : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) h 21 2) :
    s2Mu3Coeff h2 hq β (g + h) t
      = s2Mu3Coeff h2 hq β g t + s2Mu3Coeff h2 hq β h t := by
  rcases Nat.lt_or_ge β (21 * (β % 2 + 2 * t)) with hlt | hge21
  · rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hlt, add_zero]
  · have hm : 2 * ((β - 21 * (β % 2 + 2 * t)) / 2) + 21 * (β % 2 + 2 * t) = β := by omega
    have hgeg := le_dv2Pin_of_le_dv2Supp h2 hq (by norm_num) hg hm
    have hgeh := le_dv2Pin_of_le_dv2Supp h2 hq (by norm_num) hh hm
    have hmin : min
        (dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))
        (dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) h (β % 2 + 2 * t))
        ≤ dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g + h)
            (β % 2 + 2 * t) := by
      rw [dv2Pin, dv2Pin, dv2Pin,
        dev_add_of_monic (s2Φ₂_monic h2 hq) g h (β % 2 + 2 * t),
        dv2Hgt_eq_dvSupp h2 hq, dv2Hgt_eq_dvSupp h2 hq, dv2Hgt_eq_dvSupp h2 hq]
      exact C130s6.min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (by norm_num) _ _
    have hgegh := le_trans (le_min hgeg hgeh) hmin
    rw [s2Mu3Coeff_eq_eval_of_le h2 hq hm hgegh,
      s2Mu3Coeff_eq_eval_of_le h2 hq hm hgeg,
      s2Mu3Coeff_eq_eval_of_le h2 hq hm hgeh,
      dev_add_of_monic (s2Φ₂_monic h2 hq) g h (β % 2 + 2 * t)]
    rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hgeg
    rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hgeh
    rw [s2GradedRes_add_of_le h2 hq hgeg hgeh, Polynomial.eval_add]

/-! ## Part 4 — the polynomial lift (mirror of `C130rp2.s2GradedRes_add_of_le`) -/

/-- ★ **RP-3, the graded ADD law (strong form)**: `R_β(g + h) = R_β(g) + R_β(h)` whenever
both inputs have a common cleared `dv2Supp`-value `≥ β` — no hypothesis on the sum
(cancellation included). -/
theorem s2Mu3GradedRes_add_of_le {β : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2)
    (hh : (β : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) h 21 2) :
    s2Mu3GradedRes h2 hq β (g + h) = s2Mu3GradedRes h2 hq β g + s2Mu3GradedRes h2 hq β h := by
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_add, s2Mu3GradedRes_coeff, s2Mu3GradedRes_coeff, s2Mu3GradedRes_coeff,
    s2Mu3Coeff_add h2 hq hg hh]

/-! ## Part 5 — ★ NODE RP-3, the `FGMNSourceLaws.graded_add` field-shape form (published
Corollary 4.12(1)) at the μ₃ occurrence, and the RP-2 zero-law's shape pin -/

set_option linter.unusedVariables false in
/-- ★ **NODE RP-3, the graded ADD law** (published Cor 4.12(1), the `FGMNSourceLaws.graded_add`
binder pattern verbatim at the μ₃ occurrence): exact + exact + exact-sum inputs give
`R_β(g + h) = R_β(g) + R_β(h)`.  The exact-sum hypothesis `hgh` is carried for field-shape
fidelity only — `s2Mu3GradedRes_add_of_le` proves the law without it. -/
theorem s2Mu3GradedRes_add {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hh : S2Mu3ExactGrade h2 hq β h)
    (hgh : S2Mu3ExactGrade h2 hq β (g + h)) :
    s2Mu3GradedRes h2 hq β (g + h) = s2Mu3GradedRes h2 hq β g + s2Mu3GradedRes h2 hq β h :=
  s2Mu3GradedRes_add_of_le h2 hq
    (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg).symm)
    (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm)

/-- shape pin: `s2Mu3GradedRes_add` has EXACTLY the `FGMNSourceLaws.graded_add` field shape
(`C130fg.lean:202-204`) at the μ₃ occurrence. -/
example : ∀ β (g h : Polynomial O),
    S2Mu3ExactGrade h2 hq β g → S2Mu3ExactGrade h2 hq β h → S2Mu3ExactGrade h2 hq β (g + h) →
      s2Mu3GradedRes h2 hq β (g + h) = s2Mu3GradedRes h2 hq β g + s2Mu3GradedRes h2 hq β h :=
  fun _ _ _ hg hh hgh => s2Mu3GradedRes_add h2 hq hg hh hgh

/-- shape pin (RP-3's honesty note): `s2Mu3GradedRes_zero_of_above`, landed at RP-2, already
has EXACTLY the `FGMNSourceLaws.graded_zero_of_above` field shape (`C130fg.lean:198-199`) at
the μ₃ occurrence — RP-3 discharges no further zero-law obligation, only ADD. -/
example : ∀ β (g : Polynomial O), S2Mu3AboveGrade h2 hq β g → s2Mu3GradedRes h2 hq β g = 0 :=
  fun _ _ h => s2Mu3GradedRes_zero_of_above h2 hq h

end S2

end Uniformity.Density.Tower.C132rp3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp3.le_dv2Pin_of_le_dv2Supp
#print axioms Uniformity.Density.Tower.C132rp3.s2Mu3Coeff_eq_eval_of_le
#print axioms Uniformity.Density.Tower.C132rp3.s2Mu3Coeff_add
#print axioms Uniformity.Density.Tower.C132rp3.s2Mu3GradedRes_add_of_le
#print axioms Uniformity.Density.Tower.C132rp3.s2Mu3GradedRes_add

end AxCheck
