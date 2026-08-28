# Verdict: UNIT MH0A6 — MH.0a, MH.0c-remainder, MH.6

**Date:** 2026-08-28
**File landed:** `leanfinal/Uniformity/ChapC/C133mh0.lean` (new file; no existing file touched)
**Verify command:** `cd leanfinal && ~/.elan/bin/lake env lean Uniformity/ChapC/C133mh0.lean`
**Result:** exit 0, zero `sorry`, zero new `axiom`; every `#print axioms` footprint is exactly
`[propext, Classical.choice, Quot.sound]` (Lean-core only). Compiled clean on the first full
write (one small tactic fix mid-way, on `twistRead_one`'s `slotIdx_unique` witness).

All three nodes: **PROVED**, no BLOCKED-BECAUSE needed — every clause the doc asked for landed
without weakening.

## MH.0a — `stageHeight_key`

`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §9 row MH.0a.

```
theorem stageHeight_key (F : KeyFrame O π) :
    F.stageHeight F.key = ((F.e₁ * F.f₁) * F.h : ℕ)
```

Derived from `F.hpure` (`IsPure X F.key F.h F.e₁`, B.34) at its right endpoint
`F.key.natDegree / (X : Polynomial O).natDegree = F.e₁ * F.f₁` (via `F.hdeg`): the order-0 Gauss
height there is `0` (`F.key.coeff (F.e₁*F.f₁) = 1` by monicity, and `gaussVal (C 1) = 0` via a
private `gaussVal_C'` plus mathlib's `IsDiscreteValuationRing.addVal_one` — no `Irreducible π`
hypothesis needed). The on-side equation then collapses to `stageHeight F.key = F.h * D′`.
30 lines including the private helper, inside the doc's 30–50 estimate. No `hπ` needed (a
simplification versus the doc's implicit framing — `addVal_one` is unconditional).

## MH.0c remainder — `twistExp_zero`, `twistRead_one`

The two C.22 definitional chases left open after `C133mh1` landed the TW-δ cocycle row.

```
theorem twistExp_zero (F : KeyFrame O π) : F.twistExp 0 = 0

theorem twistRead_one (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (hh : 0 < F.h) :
    F.twistRead H₀ hpin 0 (1 : Polynomial O) = 1
```

`twistExp_zero`: immediate from C.16's `twistExp_spec` at `k = 0` (`slotIdx 1 * 0 = slotIdx 0 +
e₁ * twistExp 0`, i.e. a sum of two naturals is `0`; `F.he₁ : 0 < e₁` kills the wrong
`mul_eq_zero` disjunct).

`twistRead_one`: needs `0 < F.h` (the doc's §1 standing nondegeneracy — at the degenerate `h = 0`
frame the window `T(0)` is not a singleton, so the clause is genuinely conditional on
nondegeneracy, matching the whole document's framing). `slotIdx 0 = 0` by `slotIdx_unique` at the
trivial witness; `slotWindow F 0 = {0}` by `Finset.eq_singleton_iff_unique_mem` (the only
`t < f₁` with `e₁·t·F.h ≤ 0` is `t = 0`, using `F.he₁.ne'` and `hh.ne'`); the lone term reduces
through `digAt_zero` (residue of `1` is `1`) and `Polynomial.coeff_one_zero`, times
`stageLetter^0 = 1`.

## MH.6 — the perturbation law M4 (`dv_pure_add_of_lt` + three named clause lemmas)

`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §4.3's "perturbation law M4" bullet / §9 row
MH.6, the dv-twin of B41a's `pure_add_of_lt`.

**A genuinely useful finding surfaced while locating the atoms**: C131y (built for the unrelated
C.72 shadow-band theorem) already carries a *stronger*, fully general residual-invariance
theorem `dvResPoly_add_deep` — no purity, no monicity, just `dvSupp F A u ℓ = m` and
`m < dvSupp F B u ℓ` — whose proof consumes only bare `u ℓ hℓ hcop`, never its `LevelDatum`
wrapper's residual label `r`. Rather than manufacture an unused dummy `r : Polynomial
(F.stageField H₀ hpin)` just to match that signature (itself nontrivial: monic + irreducible +
nonzero constant term over an abstract stage field), this file re-derives the same handful of
small private support lemmas at bare `u, ℓ` — mechanical transcriptions of C131y's own
Part-2/Part-3 private helpers (`coord_lt_of_onSide_of_deep`, `dvOnSide_nat_eq`,
`read_height_lt_of_deep`), dropping only the `LevelDatum` indirection — and assembles the
residual clause directly. Every atomic fact consumed is landed and public:
`C131y.dvSupp_le_term`, `C131y.dvSideSet_add_deep`, `C131y.dvHgt_add_eq_left_of_lt`,
`dvSideLen_eq`/`dvOnSide_modEq` (C.08), `dev_add_of_monic` (B32a), and
`C131ae.twistRead_add_eq_left_of_lt` (the doc's named atom, used verbatim for the final digit
substitution). `C131y.dvHgt_add_min` (the doc's fourth named atom) was not needed in the end —
the ultrametric inequality it supplies is subsumed by the direct `dvSideSet_add_deep` route
(the equality-off-ties argument goes through the strict-inequality lemma
`dvHgt_add_eq_left_of_lt` directly, never needing the weaker two-sided `min ≤` bound).

Landed declarations (`u, ℓ` bare naturals, `hℓ : 0 < ℓ`, `hcop : Nat.Coprime u ℓ` — the ambient
admissible-direction hypotheses standing throughout the doc's §1 frame, genuinely consumed by
the `ℓ`-spacing argument inside `read_height_lt_of_deep'`):

* `dv_purity_add_of_lt` — `IsDvPure F (x + y) u ℓ` from `IsDvPure F x u ℓ` (side-set invariance
  transfers both endpoints).
* `dv_height_add_of_lt` — `dvHgt F (x+y) (dvSideMin F (x+y) u ℓ hne') = (Mx : ℕ∞)`, the height
  `M₀` preserved.
* `dv_resPoly_add_of_lt` — **the crux**: `dvResPoly F H₀ hpin (x+y) u ℓ hne' Mx hpinM' =
  dvResPoly F H₀ hpin x u ℓ hxne Mx hMx`, proved by `Finset.sum_congr` after aligning
  `dvSideDeg`/`dvSideMin` across the (unchanged) side set, discharging each coefficient via
  `dev_add_of_monic` + `twistRead_add_eq_left_of_lt` fed by the ported `read_height_lt_of_deep'`
  bound.
* `dv_monic`/degree preservation is inlined into the bundle via mathlib's
  `Polynomial.Monic.add_of_left` + `Polynomial.degree_add_eq_left_of_degree_lt` (no dv-machinery
  needed — a plain `O[X]` fact).
* `dv_pure_add_of_lt` — the bundled theorem, all five clauses (monic, degree, purity, height,
  residual) in one package, matching B41a's `pure_add_of_lt` conclusion shape one level up.

~190 lines for MH.6 (helpers + four theorems), above the doc's 80–140 estimate — the overage is
entirely the mechanical `LevelDatum`-stripping transcription of C131y's private machinery, not
new mathematics.

## Honest scope notes

* No BLOCKED-BECAUSE: all clauses named in the task landed as stated, unweakened.
* MH.6 did not need `dvHgt_add_min` in the end (see above) — a simplification, not a gap; the
  doc's atom list was a sizing guide, and the direct route needed one fewer atom.
* Did not touch, import, or reference `leanfinal/Uniformity/ChapC/C133mh3.lean` (per the task's
  isolation instruction — that file was left to the concurrently-editing agent).
* No existing file was edited; `C133mh0.lean` is new.

## Verification transcript

```
$ cd leanfinal && ~/.elan/bin/lake env lean Uniformity/ChapC/C133mh0.lean
'Uniformity.Density.Tower.C133mh0.stageHeight_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.twistExp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.twistRead_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.dv_purity_add_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.dv_height_add_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.dv_resPoly_add_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh0.dv_pure_add_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
$ echo $?
0
```
