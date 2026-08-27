# VERDICT — unit MKP6B (node M3-KP6b): hconv DISCHARGED, THE UNCONDITIONAL DEPTH-2 CALCULUS FIRED

**Node** M3-KP6b, the μ₃ campaign's LAST node · **Unit** MKP6B (Fable math tier) · 2026-08-27
**Landed** `leanfinal/Uniformity/ChapC/C132kp6b.lean` (840 lines, NEW; no existing file touched)
**Build** `lake env lean Uniformity/ChapC/C132kp6b.lean` GREEN (round 3; rounds 1–2 fixed only
cast-normal-form/`zero_le`-resolution/`modByMonic_add_div`-signature frictions, no math changes).
Zero `sorry`, zero new axioms. Prereq `lake build Uniformity.ChapC.C132rp10b` run first (olean was missing).

## The star

```
theorem s2Mu3_calculus_nonempty : Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  C132rp10b.s2Mu3_calculus_nonempty_of_conv h2 hq (s2Mu3_hconv h2 hq)
```

UNCONDITIONAL — rp10b's conditional fired with the landed `hconv`. The shape-fit is machine-checked:
`s2Mu3_hconv` is passed directly into rp10b's hypothesis slot, which is byte-identical to
`C132fd0.s2SourceLawsTwo_of`'s `hconv` (C132fd0.lean:115–117). Both S2 socket suppliers are now closed
(`hex` = rp10b's `s2Mu3_hex`, `hconv` = this node).

## What was proved (the μ₂ dictionary of C130kp7 Parts 1–6, ported one level up)

1. `s2Mu3Minimal_natDegree_four_dvd` — monic μ₃-minimal ⟹ 4 ∣ deg. **Mechanism deviation from the
   μ₂ template (flagged)**: μ₂'s hand-built coefficient-matching multiplier does NOT port
   (Φ₂ = Φ′² + 4x has no vanishing-coefficient pattern). Replaced by `Q := Φ₂^(m+1) /ₘ g`: the division
   identity makes g·Q − Φ₂^(m+1) = −(Φ₂^(m+1) %ₘ g) of degree < deg g automatically, and the grade
   comparison μ₃(g·Q) ≤ 21m + 2(c_r + c_{4−r}) ≤ 21m + 20 < 21(m+1) uses the three fresh inner monic
   digit bounds c₁,c₂,c₃ = 2,5,7 (top-digit stage heights; r = 2 is tight: 20 < 21).
2. `s2Mu3Minimal_exactGrade` — μ₃(g) = 21·(deg g/4) (truncation g − Φ₂^m; kp7 Part-2 port).
3. `s2Mu3KeyPoly_slotZero` — keys of deg > 4 have slot 0 on the grade line (deflation + primality +
   the grade ledger β = 21+γ ∧ γ = β+γ′; kp7 Part-3 port).
4. The bank: `s2Mu3KeyPoly_exactGrade`, `s2Mu3KeyPoly_gradedRes_coeff_zero_ne_zero` (ntd = 0, so
   `s2Mu3KeyPoly_normRes_eq_gradedRes` — the strip is trivial on keys), `s2Mu3KeyPoly_normRes_natDegree`
   (deg ψ = deg g/8), `s2Mu3KeyPoly_natDegree_pin` (deg g/4 = 1 ∨ deg g/4 = 2·deg ψ — no IsUnit split
   needed: m ≥ 1 + the disjunction pins m from ψ alone).
5. `s2Mu3_residual_to_initial` (the converse = the orchestrator's steps 1–4; steps 2–4 are exactly the
   graded-piece IFF, re-derived file-local), `s2Mu3_hconv` (the exact hypothesis shape),
   `s2Mu3_initial_iff_residual` (both directions; forward = kp6's landed `s2Mu3_initial_to_residual`).

## Orchestrator-plan reconciliation

Steps (2)(3)(4) of the charge are subsumed by the file-local copy of C132kp4's private
`initialEquiv_iff_gradedRes` (difference kill via `s2Mu3GradedRes_add_of_le` + `_ne_zero_of_exact`,
min bound via `s2Hgt₃_add_ge`, both disjunct branches) — verified, not assumed. Step (1)'s "port the μ₂
dictionary" required porting kp7's Parts 1–3 as well (kp1–kp5 supply no arbitrary-key degree pins, as
kp6's header records); done above, with the one mechanism substitution flagged in item 1.

File-local private copies (privates elsewhere, re-derived verbatim modulo numerals):
kp7's `stageHeight_one`/`stageHeight_le_one_of_monic_linear`/`grade_le_of_dvHgt_le`(μ₃ form);
kp4's `s2Mu3GradedRes_neg_of_le`, `initialEquiv_iff_gradedRes`, `innerGradedRes_coeff_eq_zero_of_pos`,
`eval_one_innerGradedRes`, `mu3Coeff_ne_zero_of_slot`, `mu3Dvd_phi2_of_not_slotZero`.

## Honesty

- Non-vacuous: `S2Mu3KeyPoly` is inhabited (kp4's `s2Mu3KeyPoly_Φ₂`, the m = 1 fiber of the dictionary).
- No statement changed anywhere; consumers (`fd0`, `sg`, `rp10b`) untouched.
- New statements flagged for human review per the trust boundary: the three structure mechanisms,
  the degree dictionary, and the converse (header lists them).

## AxChk footer (all twelve, from the green run)

Every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]` — Lean core only — for:
`s2Mu3Minimal_natDegree_four_dvd`, `s2Mu3Minimal_exactGrade`, `s2Mu3KeyPoly_slotZero`,
`s2Mu3KeyPoly_exactGrade`, `s2Mu3KeyPoly_gradedRes_coeff_zero_ne_zero`,
`s2Mu3KeyPoly_normRes_eq_gradedRes`, `s2Mu3KeyPoly_normRes_natDegree`, `s2Mu3KeyPoly_natDegree_pin`,
`s2Mu3_residual_to_initial`, `s2Mu3_hconv`, `s2Mu3_initial_iff_residual`, **`s2Mu3_calculus_nonempty`**.
