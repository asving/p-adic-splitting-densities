# Verdict — unit MFD1: μ₃ B-1 supply

Date: 2026-08-27  
Node: M3-FD1, `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6

Status: **BLOCKED-BECAUSE the requested exact-grade leg is false; degree and nonzero legs
landed.**

## Result

New file: `leanfinal/Uniformity/ChapC/C132fd1.lean`. No existing Lean file, roll-up,
leanspec file, or sibling file was changed; no git commit.

The `0 < d ≤ 1` family reduces to `d = 1`. At that index the landed A-C.18 definition and
C.97 exponent pin give

```text
chainNormBelow 2 21 = 2^4 Φ' = 16 Φ'.
```

The file proves:

* the exact identity above;
* `natDegree (16 Φ') = 2`, hence the requested degree supply `2 < 4`;
* `16 Φ' ≠ 0`, hence the requested nonzero supply;
* the named blocker `s2Mu3_B1_exact_grade_supply_impossible`.

The blocker is forced by the landed value/grade stack, not by a missing proof technique.
`C132rp9.s2Mu3_recipe_grade_twenty_one_vacuous` proves that every polynomial of degree
below `4` has no exact μ₃ grade `21`; its specialization
`s2Mu3_chainNormBelow_not_exact` refutes the sole requested B-1 exact-grade member. Thus the
three-family supply cannot be passed to `gentow2_Bpp` at `(r,e',f',u')=(2,2,1,21)`.
Per the row's REUSE-WITH-NUMERALS boundary, no replacement grade or new value formula was
invented.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C132fd1.lean
```

Exit 0. Zero `sorry`, zero `sorryAx`, zero new axiom, zero `unsafe`.

## AxChk footer

All seven declarations print only Lean/mathlib core footprints:

```text
s2Mu3_B1_d_eq_one:
  [propext, Quot.sound]
s2Mu3_chainNormBelow_two_twenty_one_eq_sixteen:
  [propext, Classical.choice, Quot.sound]
s2Mu3_chainNormBelow_tooth_natDegree:
  [propext, Classical.choice, Quot.sound]
s2Mu3_chainNormBelow_tooth_ne_zero:
  [propext, Classical.choice, Quot.sound]
s2Mu3_B1_degree_supply:
  [propext, Classical.choice, Quot.sound]
s2Mu3_B1_nonzero_supply:
  [propext, Classical.choice, Quot.sound]
s2Mu3_B1_exact_grade_supply_impossible:
  [propext, Classical.choice, Quot.sound]
```

AxChk: **PASS — no `sorryAx`, no project axiom, no newly declared axiom.**
