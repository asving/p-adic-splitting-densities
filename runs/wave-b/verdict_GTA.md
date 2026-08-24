# Unit GTA verdict — GENTOW2 nodes C.99–C.101

## Verdict

Overall: **BLOCKED**. No signed declaration can be proved from the current
`FGMNCalculus` fields; C.100/C.101 additionally depend on the unlanded
`TowerDatum.deepTower` preamble.

| node | signed declarations | verdict | blocking gap |
|---|---|---|---|
| C.99 | `gentow2_Bpp`, `theta_letter_valued` | **BLOCKED** | The source assumes exact-grade ladder monomials and nonzero graded reads, but the signature supplies no `ExactGrade` facts for `chainNorm` and the class has no such bridge. The letter companion also needs the absent `OPEN-LETTERS` law. |
| C.100 | `gentow2_Bp`, `gentow2_Bp_unit_iff` | **BLOCKED** | The source uses the canonical evaluation identification; the signed statement provides an arbitrary `ρ` with no coherence law. No class field connects `Rgr` to `repoRead` (`OPEN-EVAL-ISO`). The iff depends on the blocked equality. The A-C.11 `natDegree < T.D₂` re-sign was preserved; the deleted `hfree` was not reintroduced. |
| C.101 | `gentow2_B` | **BLOCKED** | `Rres_recipe` requires exact-grade and degree-bound premises for every `k2DigitLift`; the source states these recipe-data hypotheses, but the signed theorem omits them and no class field derives them (`OPEN-DICT-2`). It also inherits `OPEN-EVAL-ISO`. |

## Quoted omitted source inputs

C.99, S5.2, lines 740–744:

> “`N := n̂₂(u₃)`, `M := n̂₂(u₃d)`: ladder monomials, `deg < m₃`, single-point
> `N₃`-polygon, exact grades `κ̄` resp. `β_t` (B-1).”

C.100, S5.1 `(R-repo)`, lines 500–509:

> “the GENHN-2′ coherent read ... through the CANONICAL EVALUATION identification
> `k(L2) ≅ F₃` [Prop. 1.15].”

C.101, S5 statement, lines 303–315:

> “Let the recipe data be as in the r3 box: `k̂_t ∈ K[x]` with
> `deg k̂_t < deg Φ₂`, `dv₂`-height `u₃(f₃-t)`, and K₂-digit residual class `c_t`.”

These are inputs to the prose proofs, not conclusions derivable from the signed binders.
They cannot be added silently.

## Mechanical prerequisite

Repo-wide name search finds `TowerDatum.deepTower` and `TowerDatum.deepTower_data` only as
leanspec axioms and in prose describing their absence; neither is declared in leanfinal.
Therefore the C.100/C.101 signed types cannot presently elaborate there. Supplying this
shared infrastructure would still leave the content gaps above.

## Deliverable and declarations

New file: `leanfinal/Uniformity/ChapC/C99gt.lean`, with the required module docstring.

Declarations: none. Emitting a substitute would require statement strengthening/re-signing
or new axioms. Accordingly the per-declaration `#print axioms` requirement is vacuous.

No `sorry`, new `axiom`, `unsafe`, or statement weakening; no other unit file, roll-up, or
leanspec file touched.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C99gt.lean
```

Expected: exit 0 with no output.
