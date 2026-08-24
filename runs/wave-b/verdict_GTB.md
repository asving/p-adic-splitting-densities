# Unit GTB verdict — GENTOW2 chain nodes C.102–C.104

## Verdict

Overall: **SUPPLY / BLOCKED** (1 of 3 nodes landed; 2 content-blocked, honestly reported).

| node | leanspec name | verdict | reason |
|---|---|---|---|
| C.104 | `repoRead` | **LANDED** | Byte-identical `def` twin of `dv2Res`; no new axiom needed (the leanspec node is already a `def`, not an `axiom`). |
| C.102 | `letter_formula` | **BLOCKED** | `FGMNCalculus` has exactly one field mentioning `letterZ` (`letterZ_ne_zero`, pure nonvanishing). No class field relates `letterZ` to `ρ` or to `AdjoinRoot.root T.ψ₂`. Audited gap **OPEN-EVAL-ISO**/**OPEN-LETTERS** (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §5). |
| C.103 | `gentow2_A` | **BLOCKED** | The only route to `I.KP g` is `KP_criterion`, which needs `(Rres g).coeff 0 ≠ 0` as its 5th antecedent. The signed `hadm` hypothesis supplies only `Irreducible (Rres g)` and `(Rres g).natDegree = f'` — it omits the `ψ₃(0) ≠ 0` analog that the informal source theorem (`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` S4, lines 187–188) states explicitly as a hypothesis. No other class field derives it generically (would need `Rres_recipe` + `Rgr_ne_zero`, both gated behind `I.ExactGrade`, which has no law connecting it to `k2DigitLift` — audited gap **OPEN-DICT-2**). The `Monic`/`natDegree` legs also need a `k2DigitLift` degree companion that `C56a.lean` explicitly defers. |

A third, purely mechanical prerequisite blocks even *stating* C.102/C.103: `TowerDatum.deepTower`
(the unlabeled §10-preamble axiom just above leanspec NODE C.99,
`leanspec/Leanspec/ChapC.lean:2420-2427`) is not landed anywhere in `leanfinal` (confirmed by a
repo-wide grep; independently flagged already at `Uniformity/ChapC/C84.lean:110`). This unit does
not attempt to supply it: it is shared §10 infrastructure other in-flight nodes (C.100/C.101) also
need, and per the two content gaps above, supplying it would not by itself unblock C.102 or C.103
— their gaps are in the `FGMNCalculus` field list, not in `DeepTower`.

**No `sorry`, no new axiom, no `unsafe`, no statement weakening.** Where blocked, no Lean
declaration was emitted at all (rather than a fake/weakened one); the reasons are recorded in the
file's module docstring and here.

## Wanted fields (for whoever next touches the `FGMNCalculus` field list or re-signs `hadm`)

* **C.102:** a class law of the shape `letterZ (i+1) * letterZ i ^ k = <explicit AdjoinRoot-root
  read>`, discharging `OPEN-EVAL-ISO`/`OPEN-LETTERS`. Not in the U7 (`FGMNCALCULUS_FIELDLIST
  _2026-08-24.md`) or U9 (`FGMN_ADJUDICATION_2026-08-24.md`) field lists.
* **C.103:** either (a) re-sign `hadm` in `leanspec/Leanspec/ChapC.lean` (NODE C.103, ~line 2553)
  to add `(I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0`, mirroring the informal theorem's
  `ψ₃(0) ≠ 0` hypothesis, or (b) discharge `OPEN-DICT-2` (an `ExactGrade` ↔ `k2DigitLift` bridge
  law) plus the `C56a.lean`-deferred `k2DigitLift` degree/grade companion lemmas.

## File and declarations

New file: `leanfinal/Uniformity/ChapC/C102gt.lean`.

Declarations:

1. `Uniformity.Density.Tower.repoRead` (C.104) — LANDED.

`#print axioms Uniformity.Density.Tower.repoRead` → `[propext, Classical.choice, Quot.sound]`
(Lean core only).

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C102gt.lean
```

Expected output: exactly one line, `'Uniformity.Density.Tower.repoRead' depends on axioms:
[propext, Classical.choice, Quot.sound]`. Exit 0.
