# CC-13 verdict — the FGMN source carrier

**LANDED.**

## Deliverable

One new file: `leanfinal/Uniformity/ChapC/C130fg.lean` (imports only landed `C130k`).
No other file touched; roll-ups and leanspec untouched; nothing committed.

## Declarations (namespace `Uniformity.Density.Tower`)

| declaration | sort | content |
|---|---|---|
| `FGMNSourceData W K e' f' u'` | `Type` | the U9 §2 next-augmentation objects: `nextValue` (realized `μ_(r+1)`, cleared grades), **polynomial-valued** `gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)` (`R_(r+1,β)` in `F_(r+1)[y] ≃ (W.fld r)[y]`), `normalizedResidual` (`R_(r+1)`), `keyPolynomial` (`KP(μ_(r+1))`), `initialEquiv` (`∼_(μ_(r+1))`), `letter` (`z_i` transported) |
| `FGMNSourceData.ExactGrade` | `def … : Prop` | `nextValue g = β` — U9 §2's `μ_(r+1)(g) = β/e(μ_r)` after clearing |
| `FGMNSourceData.AboveGrade` | `def … : Prop` | `β < nextValue g` — `P_β⁺`, defined from the SAME `nextValue` |
| `FGMNSourceLaws W K e' f' u' S` | `Prop` (all-Prop fields) | the thirteen named source obligations of design §4.3's table (Lemma 3.14; Cor 4.12(1)/(2)/(3); Thm 4.1 + Cor 4.9(1) with the essential `deg g < deg keyAt r` fence; Def 1.6/3.13 + eq (11) recipe; Thm 5.7 existence with irreducible `ψ`; Lemma 5.2(2) criterion; Lemma 1.8 + Cor 1.10 + Gauss; Prop 1.7(4); eq (11) `0 < r`-fenced; Prop 5.6(2)⇔(3); §3.3 letters) |
| `ChainRealization W Kt L e' f' u'` | `Type 1` | the assembled layer: `receiver`/`keys`/`normalizer`/`node`/`fgmn`/`fgmnLaws` + `grade_compat` + `letter_compat` |

OPEN-DICT signatures (U7 §8, cited in each field docstring): OPEN-DICT-1 = the shared
`keys : KeyChain W` parametrizing both `node` and `fgmn`; OPEN-DICT-2 = `grade_compat`;
OPEN-DICT-3 = `receiver` + the `Polynomial (W.fld r)` residual codomains (transport
boundary); OPEN-DICT-4 = `letter_compat`. None is a proof or a `True` body.

## Verification

```
cd leanfinal
lake env lean Uniformity/ChapC/C130fg.lean       # exit 0
lake build Uniformity.ChapC.C130fg               # completed, 8630 jobs
```

`#print axioms` (in-file, all five new declarations): `[propext, Classical.choice,
Quot.sound]` — Lean core only. No `sorry`, no new axiom, no `unsafe`.

## Anti-drift and fit checks

- Normalized code (docstrings/comments stripped) of `FGMNSourceData` → `ChainRealization`
  diffed against the elaboration authority `leanfinal/scratch/U11_carrier_check.lean`:
  **IDENTICAL**.
- S2 instantiability-in-principle probe (`/tmp/cc13_fit_probe.lean`, not landed): over
  landed `s2DepthTwo h2 hq` / `s2DepthTwoKeyChain h2 hq` (C130s2) with `(e',f',u') =
  (2,1,5)`, `FGMNSourceData`, `FGMNSourceLaws`, `ExactGrade`/`AboveGrade`, and
  `ChainRealization` all elaborate — exit 0, no instance constructed (that is CC-17).

## Notes for downstream nodes

- `FGMNSourceLaws` lives in `Prop` (Lean's minimal-sort inference; same as the scratch
  authority). CC-14/CC-15 consume its fields for the coefficient-zero regressions.
- `ChainRealization` is landed here per C130k's node map ("`ChainRealization` and the
  A-C.11 packaging (CC-13/CC-16)"); the `toCalculus` packaging and the actual leanspec
  `FGMNCalculus` codomain remain CC-16. `RealizedInput` remains CC-8.
