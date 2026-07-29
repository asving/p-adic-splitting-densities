# MovesV round-8 Codex verdict (2026-07-29): REJECT 6/3 — N1 counting tie REAL, HMC stays open (sweep confirmed); DECISIVE: the N2 enriched toy violates StepSys zc laws (ext_zc forces the flag-0 history zc; zc_ne demands a witness in the refined flag-0 cell) — third witness failure; CutRealization ignores Pr (encode untied to fiber); Defs closure (spWord etc.), gcellDenom placeholder, M.rep nonexistent, C.Outc type error, manifest inaccuracies, V1-3 roster overflow

I’ll audit this as a verifier, not an editor. I’ll first locate the REV-8 source and built corpora, then check §6.7 row-by-row, independently re-run the HMC/mark-count logic, spot-check at least 15 manifest entries at HEAD, and finish with a fresh defect sweep and an N/M verdict.

The local shell launcher is unavailable in this workspace (its sandbox helper is missing), so I’m switching to the connected document-control path for read-only inspection. I’ll preserve the same audit scope; no files will be changed.

The central count tie is real: `tmark_inj` makes the census biject its image, `RealizesC` defines exactly that image, and the length-one surjections give `Tgam = cntraw`; no `.cons` recursion was added, so that repair alone does not close HMC. However, the N2 separation construction has a decisive consistency problem: it declares the `h₁ = 0` intermediate history non-`zc`, while `StepSys.ext_zc` and `StepSys.zc_ne` force realized extensions/refined cells to have `zc` witnesses. I’m now consolidating that with the cut, closure, and built-interface failures.

# Verdict: REJECT (6 N / 3 M)

REV 8 repairs N1’s counting tie and keeps HMC formally open, but several other dispositions are not real. Most decisively, the enriched N2 witness is inconsistent with `StepSys`’s own `zc` laws, and N3 still permits selection-ignoring censuses.

The local grep launcher failed because the workspace lacks its `bwrap` helper. I therefore checked the supplied current built-source excerpts directly; I do not represent the manifest check as an independently executed shell grep.

## §6.7 disposition audit

| Row | Result | Finding |
|---|---|---|
| N1 | PASS | `tmark_inj` identifies the census with its image; `RealizesC` is exactly that image. Thus `tgam_eq_chains` is real. Length-one surjectivity gives `tgam_last`; `marks_chains` is legitimately derived. |
| N2 | FAIL | The enriched toy cannot satisfy `StepSys.ext_zc` or `StepSys.zc_ne`; details below. The displayed cover also contains an unbound `hb`. |
| N3 | FAIL | `CutRealization` proves only an arbitrary bijection with a cut index set. It never connects `encode i` to `Pr.fiber i`, so selection-ignoring tagged censuses still pass. |
| N4 | PASS at statement level | `markCard`, `MStep`, `mReading`, and `mEvt` are displayed, and the intended tag/key disjointness route is coherent. |
| N5 | PASS at statement level | Both history transports use `d.2.symm ▸ x`; the two cast-helper bodies are displayed. |
| N6 | FAIL | Several Defs-layer dependencies remain undisplayed or forward-referenced, including `spWord`, `IsBranchingLetter`, `letterMenuCard`, `SelfLoopLetter`, `speciesTagOf`, and `monicTopOf`. |
| N7 | FAIL | `μcellVal` and `jcellPG` are displayed, but `jcellPG` consumes `gcellDenom`, whose promised closed declaration is absent. |
| N8 | FAIL | `tCountV` uses nonexistent `M.rep`; built `MeasuredSide` supplies only `Rep` and `rep_ne`. Its continuing/terminal total dispatch is also left as prose. |
| M1 | FAIL, minor | `realized_isSlot` is displayed, but the claimed finiteness of the `EligibleImage` subtype is only a docstring, not a typed `Finite`/`Fintype` result. |
| M2 | PASS | The three sum faces now obtain their `OKat` witnesses from their own bundled `hOk … hq` clauses. |
| F-GAP-1 | FAIL | Several manifest homes are absent, contradictory, or not actual `path:line` entries. |
| F-GAP-2 | PASS | The TmplEvents tie roster is correctly seven: two last-event iff ties, `real_marks`, `marks_realize`, `tmark_inj`, and two last-surjectivity ties. |
| F-GAP-3 | PASS | The two historical `Tγ = chainCount` attributions are bracket-corrected. |

## N findings

### N-1 — The N2 separation witness violates `zc` invariants

The toy specifies:

> `ext m₁ x h₁ a := if h₁ = 0 then 0 else 1`

and:

> `zc at int := (· = 1) — the flag-0 history is NOT a (ZC) representative`

But `StepSys` requires:

> `ext_zc … : zc x → zc (ext m x h a)`

The toy also says the first-step assignment at `h₁ = 0` exists. Starting from its required `zc` source witness, `ext_zc` therefore forces the resulting flag-0 history to satisfy `zc`, directly contradicting `zc := (· = 1)`.

The refined construction fails again because every `StepSys`, including `R.S'`, requires:

> `zc_ne : ∀ q₀ ∈ Pools, ∀ α, ∃ x, zc x`

Yet the refined flag-0 cell is described as having `S'.Hist := PUnit` and `zc' := zc ∘ histOf`, with `histOf` returning flag 0. That cell has no `zc'` witness.

Consequently the otherwise-correct four-point arithmetic

- `1 = 1 + 0`,
- `1 = 0 + 1`,
- `0 = 0 + 0`,

does not inhabit the displayed types. The claims “both refined composites factor” and `¬HMC ∧ HMCAug` are not established.

Additionally, both cover laws use:

> `(hb p)`

without an actual `let hb := …` or displayed declaration. The prose “notation local to this display” does not bind a Lean identifier.

### N-2 — `CutRealization` is still selection-ignoring by type

`CutRealization` takes:

> `(Pr : MovesD.Presented …)`

but none of its fields uses `Pr`. In particular:

```lean
encode : {i // cut.lands i} → B
encode_mem : ∀ i, encode i ∈ inst
encode_surj : ∀ b ∈ inst, ∃ i, encode i = b
```

There is no condition such as `encode i ∈ Pr.fiber i`, nor any canonical box-realization relation.

Thus an instance may:

1. choose arbitrary disjoint `entInst` tags for different `selRec` labels;
2. choose a `lands_sel`-bounded cut of the matching cardinality;
3. biject that cut arbitrarily to those tags.

`ent_sel` and `ent_cut` both pass, while the census remains unrelated to the selected prefixes’ realized fibers. Therefore the answer to the charge’s question is: **yes, a selection-ignoring instance can still pass by type.**

### N-3 — The Defs layer remains unclosed

`EntShapeV.template?` consumes `spWord`, `IsBranchingLetter`, `letterMenuCard`, and `SelfLoopLetter`. No closed declarations for these appear before that use. Indeed `spWord` is still assigned to downstream unit V3-3a, recreating the forward-reference problem.

Likewise `ReadFits` consumes `speciesTagOf` and `monicTopOf`, but the only supplied text is:

> “Defs-local one-line projections…”

No declarations or bodies are displayed. §7 nevertheless claims all six are displayed in §2.D.

`snocP` itself is self-contained and correctly avoids the nonexistent `ShapePrefix.snoc`; the surrounding reconstruction layer is not closed.

### N-4 — `gcellDenom` remains a placeholder

`jcellPG` contains:

```lean
qpow := (gcellDenom XsC d c).1
geomDenoms := (gcellDenom XsC d c).2.1
geom_denom_dvd := (gcellDenom XsC d c).2.2
```

But no declaration or body for `gcellDenom` is displayed. It is alternately described as:

- a closed §2.H declaration, and
- a V3-9c mini-lemma.

If it lives in V3-9c, §2.H’s Defs-layer `jcellPG` forward-references a downstream unit. If it lives in §2.H, its promised declaration is missing. N7 is therefore not repaired.

### N-5 — V7-9 does not inhabit built `PolyGeomLaws`

The proposed definition reads:

> `((M.rep e τ) q₀ hq).1`

Built `MeasuredSide` has `Rep` and:

```lean
rep_ne : … → Nonempty (Rep e τ)
```

It has no `rep` projection. A classical choice could be constructed, but REV 8 neither defines one nor lists it in the manifest.

Furthermore, `dOf o` is used as a continuing `MoveData` for a total `Out` argument, while terminal handling is only the phrase:

> “the +T twin over cntrawT/mdomT”

No displayed total route dispatch selects the continuing versus terminal carrier. Hence `tCountV` is not yet an ℕ-valued total definition of the built field, despite the correct empty-domain and off-pool intentions.

### N-6 — Fresh §2.H type error

`JCells.bcells` is declared with:

```lean
(o : C.Outc s m)
```

But `CtsFamily` has no `Outc` field or displayed accessor. The carrier is:

```lean
(C.bd s).Outc m
```

No `CtsFamily.Outc` abbreviation appears in §2.C or §7. This is a new Defs elaboration failure independent of the round-7 findings.

## M findings

### M-1 — Nat.card finiteness remains prose

The `RealizedBranching` docstring explains why the subtype should be finite, but no instance or theorem provides:

```lean
Finite {q : Polynomial F // EligibleImage … q}
```

The safe observation that an infinite subtype makes `Nat.card = 0` does not satisfy the claimed “honest-card” record. The bridge theorem itself is conditionally sound because it accepts `hcard` as a premise.

### M-2 — V1-3 breaks the ≤4-lemma unit rule

V1-3 is still labelled:

> `ROSTER (3)`

but now owns at least:

- `xhdd_exact`,
- `mem_chainCount_pos`,
- `treal_iff_tgam`,
- `tgam_eq_chains`,
- `tgam_last`,
- its terminal twin,
- `marks_chains`,
- and the induction lemma `chains_card`.

No split or census adjustment was made. The global “98 units” census therefore does not reflect REV 8’s own roster discipline.

### M-3 — The closure manifest is not accurate

Examples:

- `consumedDeltas` is declared in built `MovesS/Defs.lean`, but §7 groups it under `MovesS/Interfaces.lean` and supplies only “LegAgree’s row context”.
- The `D4R1_SUM`/`D0b_thmCtop`/`D4R4_all` row does not provide a real `path:line` for two entries, contrary to §7’s binding rule.
- `speciesTagOf`, `monicTopOf`, `spWord`, `IsBranchingLetter`, `letterMenuCard`, `SelfLoopLetter`, and `gcellDenom` are claimed as displayed homes despite the missing declarations.
- `M.rep`, consumed by V7-9, has no manifest row and no built declaration.

## Manifest spot-check

Direct comparison against the supplied current built sources:

| Identifier | Result |
|---|---|
| `MovesD.ShapePrefix` | PASS |
| absence of `ShapePrefix.snoc` | PASS |
| `MovesC.History.snoc` | PASS |
| `MovesD.EncTargetP` | PASS |
| `MovesD.encIdx` | PASS |
| `MovesS.TableShape` | PASS |
| `MovesS.MeasuredSide.Rep` | PASS |
| `MovesS.MeasuredSide.entCount` | PASS |
| `MovesS.LedgerIV.xhd_no_orphan` | PASS |
| `MovesS.LedgerIV.d4r0` | PASS |
| `MovesS.RatBurdens.jPCell` | PASS |
| `MovesS.RatBurdens.jcell_interp` | PASS |
| `MovesS.PolyGeomLaws.tCount` | PASS |
| `MovesS.PolyGeomLaws.tcount_deg` | PASS |
| `MovesS.PolyGeomLaws.scount_deg` | PASS |
| `MovesS.KmatHyp` | PASS |
| `MovesS.DetHyp` | PASS |
| `MovesS.LegAgree` | PASS |
| `MovesS.W17ii` | PASS |
| `RS4Chain.legs_read` | PASS |
| `RS4Chain.wsh17_pin` | PASS |
| `consumedDeltas` manifest home | FAIL |
| `gcellDenom` displayed home | FAIL |
| `speciesTagOf`/`monicTopOf` displayed homes | FAIL |
| `spWord` Defs-layer home | FAIL |
| `M.rep` | MISSING |

## HMC conclusion

The N1 additions do **not** create a composite decomposition:

- at `.cons`, `tmark` is only injective into `Chains`;
- no law decomposes `tinst (.cons …)` over first assignments;
- a composite mark supplies a tail chain, not a positive tail census;
- separate one-step and tail marks cannot be combined into a composite mark.

Therefore HMC remains underivable from the displayed general laws. The defect is that REV 8’s claimed `¬HMC ∧ HMCAug` witness does not inhabit those laws—not that HMC has accidentally become closed.