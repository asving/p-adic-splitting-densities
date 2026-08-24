# CC-16 verdict — FGMN packaging (the A-C.11 class twin + ChainRealization → Nonempty)

**LANDED** (no BLOCKED, no SUPPLY, no deviation from the enacted A-C.11 shapes).

## Deliverable

One new file: `leanfinal/Uniformity/ChapC/C130pk.lean` (imports `C130la` + `C130lb` only).
No other file touched; leanspec read-only; roll-ups and in-flight unit files untouched
(C131w.lean, C130s6.lean, C130in.lean, C130pt.lean, C131ae.lean not mine); nothing committed.

## Declarations (namespace `Uniformity.Density.Tower`)

| declaration | kind | content |
|---|---|---|
| `FGMNCalculus` | **class** | the leanfinal twin of leanspec's enacted A-C.11 class (NODE C.92 re-sign, `leanspec/Leanspec/ChapC.lean:1331`) — moves the UNLANDED signed name `FGMNCalculus` to CARRIER |
| `FGMNCalculus.chainNorm` | noncomputable def | byte-faithful twin of leanspec L2431 (the `n̂_{i+1}(k)` monomial realizer) |
| `FGMNCalculus.thetaRatio` | noncomputable def | byte-faithful twin of leanspec L2439 (GC-14's normalizer-ratio ϑ-carrier) |
| `ChainRealization.toCalculus` | `@[implicit_reducible]` def | the design-§7 projection map — every field from CC-13 carrier data + CC-14/CC-15 theorems, point-free; NOT an instance (the attribute is the compiler-required marking for a def of class type, as in the U11 scratch; it registers no instance) |
| `chainRealization_calculus_nonempty` | theorem | `ChainRealization W Kt L e' f' u' → Nonempty (FGMNCalculus W e' f' u')`, body `⟨A.toCalculus⟩` — NO new axiom |

Anti-drift teeth: 8 `example`-`rfl` pins, one per data field of `toCalculus`, each stating
its design-§7 table row definitionally (incl. `Rgr = fun β g => (gradedResidual β g).coeff 0`,
U9 Q2 through CC-14's `FGMNSourceData.Rgr`).

## Field-match audit (mechanical byte-diff, leanspec L1331–1385 vs C130pk L96–150)

`diff` output: the two class bodies are **byte-identical except ONE line** — the binder line
`(W : DeepTower F H₀ hpin r)` ↦ `(W : DeepTower.{0, uKt} F H₀ hpin r)`, the single design-§7
vocabulary substitution (leanfinal's explicit universes). The same holds for both consumer
defs (`{W : DeepTower F H₀ hpin r}` ↦ `{W : DeepTower.{0, uKt} F H₀ hpin r}`; all other
lines byte-equal). Per-field:

| A-C.11 field | leanspec shape = leanfinal shape | fill in `toCalculus` |
|---|---|---|
| `keyAt : ℕ → Polynomial O` | byte-equal ✓ | `A.keys.keyAt` |
| `keyAt_one : keyAt 1 = F.key` | byte-equal ✓ | `A.keys.keyAt_one` |
| `keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i` | byte-equal ✓ | `A.keys.keyAt_degree i ⟨hi, hir⟩` (`StageLive` defeq) |
| `ExactGrade : ℕ → Polynomial O → Prop` | byte-equal ✓ | `A.fgmn.ExactGrade` |
| `AboveGrade : ℕ → Polynomial O → Prop` | byte-equal ✓ | `A.fgmn.AboveGrade` |
| `Rgr : ℕ → Polynomial O → W.fld r` | byte-equal ✓ | `A.fgmn.Rgr` (CC-14; = coeff-0 read, `rfl` tooth) |
| `Rres : Polynomial O → Polynomial (W.fld r)` | byte-equal ✓ | `A.fgmn.normalizedResidual` |
| `KP : Polynomial O → Prop` | byte-equal ✓ | `A.fgmn.keyPolynomial` |
| `nuEquiv : Polynomial O → Polynomial O → Prop` | byte-equal ✓ | `A.fgmn.initialEquiv` |
| `letterZ : ℕ → W.fld r` | byte-equal ✓ | `A.fgmn.letter` |
| `Rgr_zero_of_above` | byte-equal ✓ | CC-14 `fgmnLaws.Rgr_zero_of_above` |
| `Rgr_add` | byte-equal ✓ | CC-14 `fgmnLaws.Rgr_add` |
| `Rgr_mul` (with exact-grade conjunct) | byte-equal ✓ | CC-14 `fgmnLaws.Rgr_mul` |
| `Rgr_ne_zero` (U9 degree fence) | byte-equal ✓ | CC-14 `fgmnLaws.Rgr_ne_zero` |
| `Rres_mul` | byte-equal ✓ | CC-14 `fgmnLaws.Rres_mul` |
| `Rres_recipe` | byte-equal ✓ | CC-15 `fgmnLaws.Rres_recipe` (point-free; `Rgr` defeq coeff-0) |
| `Rres_exists` (`Irreducible ψ`, `0 < r`) | byte-equal ✓ | CC-15 `fgmnLaws.Rres_exists` |
| `KP_criterion` (nonzero-constant leg) | byte-equal ✓ | CC-15 `fgmnLaws.KP_criterion` |
| `KP_irred` | byte-equal ✓ | CC-15 `fgmnLaws.KP_irred` |
| `KP_keyAt` (`0 < r`) | byte-equal ✓ | CC-15 `fgmnLaws.KP_keyAt` |
| `Rres_keyAt` (`0 < r`) | byte-equal ✓ | CC-15 `fgmnLaws.Rres_keyAt` |
| `nuEquiv_iff_Rres` (both `KP` hyps) | byte-equal ✓ | CC-15 `fgmnLaws.nuEquiv_iff_Rres` |
| `letterZ_ne_zero` (live range) | byte-equal ✓ | CC-15 `fgmnLaws.letterZ_ne_zero` |

## Honesty

The class stays a HYPOTHESIS CARRIER (C.92 adjudication: `fgmn_calculus_exists` UNDECLARED
per `C92_VACUITY`); the packaging theorem is conditional on a `ChainRealization`, whose
`fgmnLaws` remain genuine source hypotheses — discharge is CC-17's realized S2 carrier. No
instance declared, no `sorry`, no new axiom, no `unsafe`, no `True` body.

## Verification

```
cd leanfinal
lake build Uniformity.ChapC.C130la Uniformity.ChapC.C130lb   # fresh oleans, exit 0
lake env lean Uniformity/ChapC/C130pk.lean                   # exit 0, zero warnings
```

`#print axioms` (in-file, all 5 new declarations): `[propext, Classical.choice, Quot.sound]`
— Lean core only. Census (`python3 spec/census_driver.py`): `FGMNCalculus`,
`FGMNCalculus.chainNorm`, `FGMNCalculus.thetaRatio` all now CARRIER-landed at
`C130pk.lean:96/157/166`; UNLANDED 171.
