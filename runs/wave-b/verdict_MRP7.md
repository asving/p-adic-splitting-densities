# Verdict — unit MRP7: node M3-RP7 LANDED (μ₃ campaign, `graded_scalar_nonzero`)

Date: 2026-08-27 · Authority: `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP7
("At exact grade and degree `< deg Φ₂ = 4`, prove the coefficient-zero nonzero law; provide
the exact `graded_scalar_nonzero` field shape"). Tier: REUSE-WITH-NUMERALS (BLOCKED-BECAUSE
over invention — one small new bridging fact was unavoidable; see below).

File landed: `leanfinal/Uniformity/ChapC/C132rp7.lean` (new file, node tag `[M3-RP7,
2026-08-27]`). No other file touched; `C132rp5.lean` (sibling-owned) untouched;
roll-ups/leanspec untouched.

## What lands

* `exists_mu3SlotOnGrade_of_exact` — the μ₃ inf-attainment gate witness, ported from
  `C130rp6.exists_slotOnGrade_of_exact` (`dvSupp`→`dv2Supp`); self-contained, no M3-RP5/RP6
  dependency.
* Private bridge (genuinely new content, Part 2): `key_natDegree_two` (private copy, per the
  corpus's own private-copy convention), `s2GradedRes_coeff_eq_zero_of_pos`,
  `s2GradedRes_eq_C_coeff_zero`, `eval_one_s2GradedRes_eq_coeff_zero` — under `deg A < 4`, the
  μ₂ operator `s2GradedRes h2 hq m A` is supported only at `y⁰` (every abscissa `t ≥ 1` is
  ruled off-line by the SAME contradiction `C130rp8.lean:245-255` uses for `s ≥ 2`), so it
  equals `C (coeff 0)` and its evaluation at the C132rp1-collapsed letter `1` returns that same
  scalar. This bridges C132rp1's `Polynomial.eval 1 (s2GradedRes …)` reads back to the landed
  μ₂ `coeff 0` fact — needed because μ₃'s recursive coefficient reads the μ₂ operator through
  an evaluation, unlike μ₂'s own direct `coeff 0`.
* ★ `s2Mu3GradedRes_coeff_zero_ne_zero_of_exact` — the μ₃ analogue of
  `s2GradedRes_coeff_zero_ne_zero_of_exact` (`C130rp8.lean:241-259`): exact μ₃ grade + `deg g
  < 4` ⟹ `(s2Mu3GradedRes β g).coeff 0 ≠ 0`.
* `s2Mu3KeyChain_keyAt_two_natDegree` — re-citation (not re-derivation) of
  `s2KeyChain_keyAt_two_natDegree` (`C130rp8.lean:263-265`): the fence numeral `4` is SHARED
  between the μ₂ and μ₃ occurrences because both fix the same ambient tower `r = 2`
  (`FGMNSourceLaws.graded_scalar_nonzero`'s fence is `(K.keyAt r).natDegree`, `r` baked into
  `W`'s type, `W := s2DepthTwo h2 hq` for both).
* ★ `s2Mu3_graded_scalar_nonzero` — the field-shape theorem at the concrete chain
  `s2DepthTwoKeyChain h2 hq`, citing `s2KeyChain_keyAt_two_natDegree` verbatim
  (`C130rp8.lean:273-281`'s exact shape).
* ★ `s2Mu3_graded_scalar_nonzero_fills` — the FD-0 pin for any `FGMNSourceData (s2DepthTwo h2
  hq) K 2 1 21` (`C130rp8.lean:287-301`'s exact shape, `u' = 21` in place of `5`).
* `tooth_mu3_scalar_fires` — non-vacuity at the constant `1` (exact μ₃ grade `0`, degree `0 <
  4`). `Φ₂` itself cannot serve as the tooth here (unlike μ₂'s frame key `Φ′`, degree `2 < 4`):
  `deg Φ₂ = 4` fails the very fence stated against `deg Φ₂`.

## What this node does NOT claim

No `ChainRealization`/socket instance (M3-FD0/M3-SG); no additivity/multiplicativity/
normalization of the μ₃ operator (M3-RP3/RP5/RP6/RP8); no recipe/key-existence content
(M3-RP9/RP10). The OPEN-RP1-TRANSPORT faithfulness split (C132rp1's docstring) is untouched —
every theorem here is about the repo's own operators.

## Build results

- `cd leanfinal && lake env lean Uniformity/ChapC/C132rp7.lean` (per repo CLAUDE.md: never bare
  `lake build`) — SUCCESS, zero errors, zero warnings, zero `sorry`.
- All dependency `.olean`s (`C130rp8`, `C132rp0`, `C132rp1`, `C132rp2`) were already built; no
  scoped rebuild was needed.
- `#print axioms` on every new declaration — Lean-core only:

```
Uniformity.Density.Tower.C132rp7.exists_mu3SlotOnGrade_of_exact               [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.C132rp7.s2Mu3GradedRes_coeff_zero_ne_zero_of_exact   [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.C132rp7.s2Mu3KeyChain_keyAt_two_natDegree            [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.C132rp7.s2Mu3_graded_scalar_nonzero                  [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.C132rp7.s2Mu3_graded_scalar_nonzero_fills            [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.C132rp7.tooth_mu3_scalar_fires                      [propext, Classical.choice, Quot.sound]
```

(Private helpers `key_natDegree_two`, `s2GradedRes_coeff_eq_zero_of_pos`,
`s2GradedRes_eq_C_coeff_zero`, `eval_one_s2GradedRes_eq_coeff_zero` are not independently
axiom-checked, per the corpus's convention for private-copy bridging facts.)

Honesty: 0 `sorry`, 0 new `axiom`, no statement invented beyond the row's sketch and the μ₂
porting pattern; no other file touched; no git commit taken.
