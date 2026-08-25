# Unit GT5 verdict — GENTOW5 `𝒲`-family consumer matrix (leanspec C.89/C.90)

## Verdict

Overall: **SPLIT — 2 of 5 LANDED, 3 BLOCKED (named, source-anchored gaps)**. No `sorry`, no
new `axiom`, no `unsafe`, no statement weakening. Deliverable:
`leanfinal/Uniformity/ChapC/C107gt5.lean` (new file, imports `C130pk` only).

| node | signed name | kind | verdict | one-line reason |
|---|---|---|---|---|
| C.89 | `GENTOW5W` | def | **LANDED** | Byte-faithful twin; the definition IS the carrier — no proof obligation. |
| C.89 | `Wle` | def | **LANDED** | Byte-faithful twin; cumulative closure of `GENTOW5W` over truncations, no proof obligation. |
| C.89 | `gentow5w_two` | axiom | **BLOCKED** | Docstring's own route ("the `i=2` discharge from C.99") needs `gentow2_Bpp`'s four supply families (`hprev`, `hnorm`, `hnormdeg`, `hnormz`); none is in this axiom's binders. |
| C.89 | `gentow5w_one_shape` | axiom | **BLOCKED** | Same gap as above, plus a second: ties `Rgr`/`chainNorm` to `letterZ 1 ^ k`, which no class field expresses (OPEN-LETTERS/OPEN-EVAL-ISO). |
| C.90 | `gentow5_key_certificate` | axiom | **BLOCKED** | `hadm` supplies only 2 of `KP_criterion`'s 5 antecedents (missing `(Rres Φnext).coeff 0 ≠ 0`); the source's own admissibility clause states all three residual conjuncts explicitly. |

## Quoted gaps

**`gentow5w_two`/`gentow5w_one_shape`** — the standing adjudication already names this exact
cascade (`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` §2):

> "**Cascade flag (not enacted here):** C.89's `gentow5w_two` (docstring: "the i = 2 discharge
> from C.99") and `gentow5w_one_shape` will need the same three families when their landing
> unit runs; flagged for the next A-C amendment."

and §10 item 3: "**C.89 cascade** — `gentow5w_two`/`gentow5w_one_shape` consume the C.99 genre
and will need the B-1 supply binders when their unit runs." That amendment was never enacted
for these two names (absent from the A-C.12 verdict table and from every later A-C amendment
commit; `rg -n "gentow5w" docs/in-progress/*.md` finds only these two cascade-flag lines). The
landed `C.99` twin (`gentow2_Bpp`, `C99r.lean`) needed, beyond `he'/hf'/hcop/hfloor`:
`hprev : I.PrevGrade u'` ([A-C.13]) and the three B-1 families
`hnorm`/`hnormdeg`/`hnormz` (`∀ d, 0 < d → d ≤ f' → …` on `I.ExactGrade`/degree/nonzero of
`I.chainNorm r (d*u')`) — none of which appear in `gentow5w_two`'s or `gentow5w_one_shape`'s
signed binders (`ChapC.lean:3775–3787`). `gentow5w_one_shape` additionally needs a tie between
`I.Rgr`/`I.chainNorm` and `I.letterZ 1 ^ k`; the sibling gap is recorded verbatim by GTB
(`runs/wave-b/verdict_GTB.md`, C.102 row): "No class field relates `letterZ` to `ρ` or to
`AdjoinRoot.root T.ψ₂`. Audited gap **OPEN-EVAL-ISO**/**OPEN-LETTERS**."

**`gentow5_key_certificate`** — the signed `hadm` (`ChapC.lean:3803–3804`):

```lean
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f') :
```

supplies 2 conjuncts; `FGMNCalculus.KP_criterion` needs 5, the 5th being
`(Rres g).coeff 0 ≠ 0`. The informal source states its admissibility notion with the matching
third conjunct explicitly (`lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md`, ll.793–796):

> "`psi_{i+1}^{(w_i)}` is GENTOW2-A-ADMISSIBLE at each value of `w_i` — monic irreducible of
> degree `f_{i+1}` with **nonzero constant term** ..."

This is the identical genre GTB recorded for the sibling node C.103 pre-resign
(`runs/wave-b/verdict_GTB.md`): "The only route to `I.KP g` is `KP_criterion`, which needs
`(Rres g).coeff 0 ≠ 0` as its 5th antecedent. The signed `hadm` hypothesis supplies only
`Irreducible (Rres g)` and `(Rres g).natDegree = f'`... No other class field derives it
generically." C.103's own gap was later repaired by amendment A-C.12
(`gentow2_A`'s `hadm` now carries the third conjunct, `C99r.lean`). **That amendment's verdict
table lists C.99/C.100/C.101/C.102/C.103/C.85/C.88/C.106 only — C.90
(`gentow5_key_certificate`) is absent and has not been touched by any enacted A-C amendment**
(`rg -n "gentow5_key_certificate" docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` — no
hit). Secondary, non-decisive observation: even with the third conjunct supplied,
`KP_criterion`'s degree antecedent additionally needs `keyAt_deg` at `1 ≤ r`, a binder
`gentow5_key_certificate` also never supplies (`r = 0` is not excluded).

## Why the def twins needed no proof

`GENTOW5W` and `Wle` are `Prop`-valued definitions, not theorems — the C.89 module docstring
says it directly: "no axiom asserts it, the definition IS the carrier". Per
`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §6, both signatures type only against
the accessor set `keyAt, ExactGrade, Rgr, Rres, KP, nuEquiv, letterZ` (here: `Rgr`, `keyAt`
through `chainNorm`/`thetaRatio`, and the class itself through `Wle`'s `DeepTower.trunc`
argument) — all landed in `C130pk.lean` — so the twins elaborate with zero proof obligation.
`GENTOW5W` was explicitly deferred at DT2 as "FGMNCalculus-adjacent"
(`Uniformity/ChapC/C141defs.lean`'s "Not landed" list) and is landed by this unit.

## File and declarations

New file: `leanfinal/Uniformity/ChapC/C107gt5.lean` (imports `Uniformity.ChapC.C130pk` only).

Declarations (namespace `Uniformity.Density.Tower`):

| declaration | kind | axiom footprint |
|---|---|---|
| `GENTOW5W` | def | `[propext, Classical.choice, Quot.sound]` |
| `Wle` | def | `[propext, Classical.choice, Quot.sound]` |

No declaration emitted for `gentow5w_two`, `gentow5w_one_shape`, `gentow5_key_certificate`
(per the GTA precedent: a substitute would require re-signing the leanspec binders — outside
this unit's authority, `leanspec/` is read-only here — or a new axiom, both excluded).

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C107gt5.lean
```

Expected: exit 0, exactly two lines —

```text
'Uniformity.Density.Tower.GENTOW5W' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.Wle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`rg -n "sorry|^axiom|unsafe" leanfinal/Uniformity/ChapC/C107gt5.lean` matches only the
docstring's quoted leanspec source (documentation, no live declaration).
