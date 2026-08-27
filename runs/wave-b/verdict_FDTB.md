# Verdict FDTB — the deepTwist supplier bridge: μ₃'s GENTOW5WCleared → DT0's DeepGentowSupplier

Unit FDTB (Fable), 2026-08-27.  Landed file: `leanfinal/Uniformity/ChapI/IFC1.lean`
(new; imports IFC0 + C132sg3; no existing file touched).  Build:
`lake env lean Uniformity/ChapI/IFC1.lean` — clean, zero sorry, zero new axiom.

## (1) The demand, read exactly

`IFC0.DeepGentowSupplier n` demands, at every arising joint witness
(`CanonicalDeepTwistConfig … A R w r n`), the flat family
`∀ j, 3 ≤ j → j < r → Gauge.GentowW (A j) (q j) (R j) (w j)` with D.44's raw identity
`GentowW A q R w = ∀ s : ℕ, R (N.n (s·q)) = (A.theta q s)·w^s` — ALL exponents `s`, at
the witness's OWN exports (C130vw `ArenaFamilyViewEq`: `R j` = chain node `towerRead`,
`w j` = `peelUnit j`, arena = `gaugeArenaFamily0`).  A-C.21 (verdict_ANORM) did NOT touch
D-side `GentowW`; it re-indexed the C-side carrier — signed twin `GENTOW5WCleared`
(law `Rgr(e'·((f'−t)·u')) (chainNormBelow r ((f'−t)·u')) · thetaRatioCleared (f'−t)
= w^(f'−t)`, witness in `W.fld r`); the pre-A-C.21 `GENTOW5W` is FALSE at the μ₃ point.

## (2) The gap, precisely — three independent components

* **RANGE**: the cleared carrier supplies exponents `s = f'−t ∈ [1, f']` only (ONE
  exponent, `s = 1`, at μ₃'s `f' = 1`); D.44 also demands `s = 0` and the `s > f'` tail.
* **WIRING (GC-13, OPEN)**: nothing landed relates FGMN reads (`Rgr`/`chainNormBelow`/
  `thetaRatioCleared`) to the witness's gauge exports (`towerRead`/arena `theta`/
  `peelUnit`).  The exact missing identifications, through a receiver `φ : W.fld r →+* Kt`:
  `hread : R (N.n (s·q)) = φ (Rgr (e'·(s·u')) (chainNormBelow r (s·u')))` and
  `htheta : (A.theta q s)·φ (thetaRatioCleared s) = 1`.  Given these, the translation is
  pure CommRing algebra — PROVED in IFC1.  BLOCKED-BECAUSE for the unconditional bridge:
  discharging hread/htheta at the realized S2 export data is the missing campaign.
* **DEPTH**: demand bites only at `r ≥ 4` witnesses; the only landed witness (S2
  frontier) has `r = 2` — its demand is empty (machine-pinned).  The S2 depth-2 instance
  supplies NO `GentowW` at any arising level j; the μ₃ endpoint is a SHAPE tooth.

## (3) Landed in IFC1.lean (node [FDTB, 2026-08-27]) — all proved, Lean-core

* `GentowWWindow` — D.44's identity on `1 ≤ s ≤ f'` (NEW STATEMENT, review-flagged).
* `gentowW_iff_zero_window_tail` — EXACT: `GentowW ↔ zero-clause ∧ window ∧ tail`.
* `GentowWWindow.of_gentowW` — projection.
* `gentowWWindow_of_cleared_law` — translation core (pinned witness + hunit).
* ★ `gentowWWindow_of_gentow5wCleared` — `GENTOW5WCleared` + hread + htheta ⟹
  `∃ w, GentowWWindow` (w = receiver image of the C-side peel witness).
* ★ `s2Mu3_gentowWWindow` — the μ₃ tooth: consumes UNCONDITIONAL
  `C132sg3.s2Mu3_gentow5w_two` at `(2,1,21)`; residue = the two wiring equations at s=1.
* `deepGentow_demand_vacuous_of_shallow` — the `r ≤ 3` vacuity pin.

Honesty: hread/htheta shapes carry the D-D12 fence (only dischargeable at a witness's
own exports; cooked instantiations prove nothing — module docstring).  No swallowing:
no relation between canonical and arena reads is stated; the ϑ half is untouched.
REVIEW FLAGS: `GentowWWindow` def + the hread/htheta hypothesis shapes.

## Remains open (interface note, also in the module docstring)

GC-13 wiring at realized exports · the s=0 clause + s>f' tail · any depth-≥4 witness ·
`DeepVarthetaSupplier` (all of it) · CIFACE's degree-2 non-vacuity teeth.

## AxChk footer (verbatim `lake env lean` output, 2026-08-27)

```
'Uniformity.Density.IFC1.GentowWWindow' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.IFC1.gentowW_iff_zero_window_tail' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.IFC1.GentowWWindow.of_gentowW' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.IFC1.gentowWWindow_of_cleared_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC1.gentowWWindow_of_gentow5wCleared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC1.s2Mu3_gentowWWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC1.deepGentow_demand_vacuous_of_shallow' depends on axioms: [propext, Quot.sound]
```
