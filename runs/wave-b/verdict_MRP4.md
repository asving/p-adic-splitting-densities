# Verdict — unit MRP4, μ₃ campaign node M3-RP4 (endpoint/carry arithmetic)

**File delivered:** `leanfinal/Uniformity/ChapC/C132rp4.lean` (new; only file written by
this unit besides this verdict). Builds clean from `leanfinal/`:
`lake env lean Uniformity/ChapC/C132rp4.lean` exits 0 — zero errors, zero warnings, zero
`sorry`, zero new `axiom`. (Per repo convention, verified with `lake env lean`, never bare
`lake build`.)

## What this node proves (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP4)

The row asks for three things at the μ₃ numerals `(e₃, h₃) = (2, 21)`: on-line slot parity,
endpoint sums, and the carry exponent `(β%2)(β'%2)`.

1. **Parity — reused, not re-proved.** `s2Mu3SlotOnGrade_parity` was already landed in
   `C132rp1.lean` (node M3-RP1). This unit does not restate or re-prove it; it BUILDS on it
   directly inside `s2Mu3SlotOnGrade_abscissa_sum` (Part 3 below).
2. **The carry exponent** (Part 1): `s2Mu3Carry β β' := (β%2)*(β'%2)` and **U14's carry
   formula** `s2Mu3Carry_parity : β%2 + β'%2 = (β+β')%2 + 2*s2Mu3Carry β β'`
   (`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §5's four-way parity check,
   the exact fact `s2GradedCoeff_mul_aux`'s `hcpar` needs at μ₂, `C130rp4.lean:635-637`,
   now named and reusable). Since `e₃ = e₂ = 2`, this identity is level-independent — a
   genuine verbatim reuse, no numeral change at all.
3. **Endpoint sums**, at three levels, each REUSE-WITH-NUMERALS off landed μ₂/μ₃ material:
   - `s2Mu3_abscissa_sum` (Part 2): the pure `ℕ` index identity
     `(β%2+2t) + (β'%2+2(T-t)) = (β+β')%2 + 2(T+carry)` for `t ≤ T` — the μ₃ analogue of
     `C130rp4.lean`'s reindexing step (`himg`, lines 574–582), isolated so M3-RP5's future
     convolution proof can cite it instead of re-deriving it inline.
   - `s2Mu3SlotOnGrade_abscissa_sum` (Part 3): the same sum re-expressed against the actual
     gate `S2Mu3SlotOnGrade` (C132rp1), using the landed parity pin on both input slots.
   - `s2Mu3_def312_add` (Part 4): Definition 3.12's `u`-coordinate addition law
     `u₃(α+β) = u₃(α)+u₃(β)+c·h₃` at `h₃ = 21`, stated in the same solved-linear-equation
     idiom as C132rp1's `s2Mu3_def312_level3` and proved by REUSING that lemma at `β` and at
     `β'` (not by introducing a fresh division-based `u₃` definition or re-deriving the line
     arithmetic).
4. Two numeral teeth (`tooth_carry_Φ₂Φ₂`, `tooth_def312_add_Φ₂Φ₂`) at the odd×odd pair
   `β = β' = 21` — COR412 §5's flagged non-vacuous carry genre (carry `1`, not `0`).

## Honesty scope (what this node does NOT claim)

* No convolution, no polynomial-level product law, no `s2Mu3GradedRes` assembly — that is
  M3-RP5/RP6. In particular `s2Mu3SlotOnGrade_abscissa_sum` does **not** assert that on-line
  slots of `g` and `z` combine into an on-line slot of `g*z`; the μ₂ precedent
  (`C130rp4.lean`'s `s2GradedCoeff_mul_aux`, using `dev_mul_conv_split`/`carry_floor`/
  `twistRead` additivity) shows that step needs the real convolution machinery. This node
  supplies only the numeral bookkeeping that machinery will index by.
* No use of M3-NV4's conditional minimizer apparatus (`Dv2OnSide`/`dv2SideMin`,
  `s2_dv2OnSide_mul_endpoint_at_21`): the numeral `h₃ = 21` used everywhere here is already
  pinned by C132rp1 (itself inheriting `(u₃,ℓ₃) = (21,2)` from NV4/NV1), so no additional
  NV4 theorem is consumed to validate it — reading `C132nv4.lean` (per the campaign row's
  named input) confirmed the numeral provenance rather than supplying new content to cite.
* `s2Mu3Carry_parity` restates the general COR412 §5 formula only at `e₃ = 2`; no general-`e`
  claim is made.

## Rules compliance

No `sorry`, no new `axiom`. Only `leanfinal/Uniformity/ChapC/C132rp4.lean` was written;
`leanspec/`, roll-ups, and `C132rp2.lean` (a sibling unit's file) were not touched. No
`git add`/`git commit` taken.

## `#print axioms` (AxCheck footer, `lake env lean` run 2026-08-27)

```
s2Mu3Carry                        : (no axioms)
s2Mu3Carry_eq_zero_or_one         : propext, Quot.sound
s2Mu3Carry_parity                 : propext, Quot.sound
s2Mu3_abscissa_sum                : propext, Quot.sound
s2Mu3SlotOnGrade_abscissa_sum     : propext, Classical.choice, Quot.sound
s2Mu3_def312_add                  : propext, Classical.choice, Quot.sound
tooth_carry_Φ₂Φ₂                  : (no axioms)
tooth_def312_add_Φ₂Φ₂             : propext, Classical.choice, Quot.sound
```

All footprints are Lean-core only (`propext`, `Classical.choice`, `Quot.sound`); no
declared literature cite is consumed by this arithmetic-only node.
