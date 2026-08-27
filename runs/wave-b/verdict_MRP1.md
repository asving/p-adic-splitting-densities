# MRP1 verdict — node M3-RP1 LANDED (gate + ε-factor + recursive coefficient)

Unit MRP1, 2026-08-27. Charge: `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 row M3-RP1
(GENUINELY-NEW): define the grade-line gate `2·μ₂(A_s) + 21·s = β` and the μ₃ coefficient
via the landed μ₂ graded/normalized read and the FGMN ε-factor; pin proof independence.

## What landed — `leanfinal/Uniformity/ChapC/C132rp1.lean` (663 lines)

**The gate** `S2Mu3SlotOnGrade β g s := 2 • dv2Pin L Φ₂ g s + 21·s = β` — `dv2Supp`'s own
term shape at outer `(21, 2)` (DEC3R §2.3; MADJ layering respected: the inner `(5, 2)` is
sealed inside `L`). Pins: natural normal form (`s2Mu3SlotOnGrade_iff`), the campaign
display with the LANDED `s2Hgt₂` as the inner μ₂ read (`s2Mu3SlotOnGrade_iff_hgt₂`),
parity `s₃(β) = β % 2` (`s2Mu3SlotOnGrade_parity`), the inner exact-grade pin
(`s2Mu3SlotOnGrade_inner_exact` — FGMN eq (10)'s `μ₂(a_s) = α_j` conjunct, RP-5's
consumable), and the `dv2Supp ≤ β` bridge (`dv2Supp_le_of_mu3SlotOnGrade`, RP-2's
zero-above input). Def 3.12's grade-line integers omega-certified at BOTH levels
(`s2Mu3_def312_level3` / `_level2` / `_level2_exists`, `s2Mu3_bezout_level2`).

**The ε-factor** (FGMN Def 3.12 at `i = 2`, `(e₂,h₂) = (2,5)`, Bézout `(ℓ₂,ℓ₂′) = (1,−2)`):
transcribed exponent `s2Mu3EpsExp m = −2·(m%2) − (m − 5(m%2))/2`, parametric factor
`s2Mu3EpsOf z m = z ^ s2Mu3EpsExp m`. **The S2 collapse, PROVED**: `fld 2` has 2 elements
(`s2Fld₂_card`), so `s2Mu3EpsOf z m = 1` for EVERY nonzero letter (`s2Mu3EpsOf_eq_one`),
the evaluation point `z₂` is pinned to `1` (`s2Mu3_eval_letter_pinned`), and the collapsed
operator `s2Mu3Eps = 1` is letter-independent (`s2Mu3Eps_eq_epsOf`) and a unit
(`s2Mu3Eps_ne_zero`, Def 3.12's `∈ 𝔽₃^*`).

**The coefficient** `s2Mu3Coeff β g t` = gated `ε · eval 1 (s2GradedRes ((β−21s)/2)
(dev Φ₂ g s))` at abscissa `s = β%2+2t` — Def 3.13's `ε₂(α_j)·R_{2,α_j}(a_{s_j})(z₂)`
through the LANDED μ₂ operator. Proof-independence pins: letter display
(`s2Mu3Coeff_letter_display` — the literal published shape for every nonzero `z₂`), true
height (`s2Mu3Coeff_eq_eval`), the graded/normalized two-read collapse
(`s2Mu3Coeff_eq_eval_normRes`, via C130rp8's reconstruction — the `y^{j₀}` strip is
invisible at `y = 1`), slot completeness (`s2Mu3Coeff_slot`). Zero laws: `⊤`-slot,
past-degree, past-grade, above-grade (coefficient level; RP-2 lifts to the polynomial).
Teeth: `tooth_mu3_gate_Φ₂`, `tooth_inner_exact_Φ₂`,
`tooth_mu3Coeff_Φ₂ : s2Mu3Coeff 21 Φ₂ 0 = 1` (eq (11) at μ₃, firing through BOTH landed
levels: `dev Φ₂` then `s2GradedRes` at inner grade 0), `tooth_mu3Coeff_ne_zero`,
`tooth_mu3Coeff_above` (grade 20 vanishes). Fresh inner tooth `s2GradedRes_zero_one`.

## OPEN-RP1-TRANSPORT disposition (FLAGGED FOR REVIEW QUEUE)

The transport claim (repo read = published Def 3.13 coefficient) splits into three legs;
only the honest split is asserted (file docstring "Faithfulness note", campaign addendum
[MRP1 2026-08-27]):

1. **DERIVED (Lean theorems here):** the μ₃-level ε-factor, the `z₂`-evaluation, and the
   graded-vs-normalized inner-read agreement all collapse at S2, proved for every nonzero
   letter. One un-formalized leg: the paper's own p. 15 remark `z_i ≠ 0` for `i > 0`,
   consumed as the explicit `hz : z ≠ 0` binder — never silently.
2. **INHERITED, NOT RE-DERIVED (remains OPEN):** `s2GradedRes` = published `R_{2,α}` is
   C130rp1's standing C.22/C.25 ϖ-read trust boundary; whether the landed μ₂ read carries
   the paper's level-2 ε₁-normalization is GENTOW2-B′'s per-grade unit `u(β)` question
   (`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:489-523`). No theorem asserts or
   consumes it.
3. **NOT LANDED:** concrete `z₂` (OPEN-LETTERS); `F₃ ≅ fld 2` (OPEN-DICT-3-MU3). Neither
   is needed by any theorem here, because of leg 1.

## Verification

From `leanfinal/`: `lake env lean Uniformity/ChapC/C132rp1.lean` — exit 0, zero errors,
zero warnings, zero `sorry`, zero `axiom` declarations (grep-verified). Scope fence
respected: no roll-up/leanspec/other-file edits; assembled polynomial operator left to
M3-RP2 per the row split.

## AxChk footer (verbatim `#print axioms` output)

```
'Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3_def312_level2_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3_bezout_level2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.S2Mu3SlotOnGrade' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.dv2Hgt_eq_dvSupp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_iff_hgt₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3SlotOnGrade_inner_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.dv2Supp_le_of_mu3SlotOnGrade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3EpsExp' does not depend on any axioms
'Uniformity.Density.Tower.C132rp1.s2Mu3EpsExp_eq' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3EpsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Fld₂_eq_one_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3EpsOf_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Eps_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Eps_eq_epsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Eps_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3_eval_letter_pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_letter_display' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_eval_normRes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_dv2Pin_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_natDegree_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_grade_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2Mu3Coeff_eq_zero_of_above' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp1.s2GradedRes_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.tooth_mu3_gate_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.tooth_inner_exact_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp1.tooth_mu3Coeff_above' depends on axioms: [propext, Classical.choice, Quot.sound]
```
