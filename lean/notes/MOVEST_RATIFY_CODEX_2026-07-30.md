# MovesT AS-BUILT RATIFICATION (Codex, 2026-07-30): REJECT M — the per-site adjudication NOT IMPLEMENTED (siteCellEvent prices node-in-branchSet over a UNION of cells, not the exact site-owned joint cell — the cellEventE shape is the right form); TREE-N missing the stability statement; hjcm decoratively unused; S2_sibFalse RED (caught — MovesT is outside the root graph, the build claims missed it); the G1 record correction (2 admissions are BLOCKED-FALSE, not gated). Local ratifications: verdict gates, ns split, sibling indexing, oneF, ChildCover. Repairs charged.

I’ll audit the actual `MovesT` sources against the quoted note, focusing first on statement surfaces and all remaining `sorry` dependencies, then check compilation and classify each mismatch as faithful, narrower, stronger, or vacuous.

The central issue is already visible at the statement layer: the note requires an exact full joint cell at each read site, while the Lean carrier prices membership of a node in a branch set. I’m tracing the consequences through `JCmultiAt`, site-level `(SIB)`, and `TREE-EXP`; this distinction is structural, not cosmetic.

## Verdict: REJECT (M — material)

The corpus is not statement-faithful to §T-ASSEMBLY in both directions. The decisive defect is the read-site keying: Lean prices a branch-membership stratum, not the note’s site-owned full joint cell. Several downstream laws are consequently keyed to an object weaker than the adjudicated one.

### 1. Per-site TREE-EXP keying — material mismatch

The note requires:

> “each site s carrying in T its full JOINT CELL c_s … in general FINER than any single branch’s (side, ψ) node stratum”

Lean defines:

> `siteCellEvent ... es ν := {x | x ∈ entEvent ... es ∧ ν ∈ CA.branchSetOf (CA.cellOf es x)}`

in [Defs.lean](/tmp/leanratify_t/lean/LeanUrat/MovesT/Defs.lean).

This is the event that a node belongs to the branch set of whatever cell `x` realizes. It is generally a union of cells containing `ν`; it does not identify one exact full joint cell. No law says:

```lean
ν ∈ branchSetOf c → c = c_site
```

or otherwise makes the node determine the full cell. The code’s assertion that a `Node` carries the full decorated outcome does not establish that missing injectivity.

Classification: **weaker and differently keyed than the note; M**.

“Every site charged once” is represented syntactically by

```lean
n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H
```

but the object charged at each site is not the adjudicated `c_s`.

### 2. `(JC-multi)` is disconnected from its alleged joint cell

`JCmultiAt` takes an implicit cell `c` through:

```lean
ss : SideSplit T CA c fd
```

but prices:

```lean
Nat.card ↥(siteCellEvent T CA χ es ν) * ...
  = Nat.card ↥(entEvent T χ es)
```

The priced event does not mention `c`. There is no premise tying the side decomposition of `c` to the cell(s) represented by `siteCellEvent es ν`.

Likewise, `SiteLedger.cellAt H` supplies the split cell, while `state_cell` uses only `H.lastNode`:

```lean
stateEvent T (some H)
  = siteCellEvent T CA χ (parentSt H) H.lastNode
```

Thus the side system may belong to `cellAt H` while the priced event is merely a node-membership stratum over potentially several cells.

Classification: **under-keyed / missing cell-event identification; M**.

### 3. Site-level `(SIB)` has the same missing tie

`SibCountAt` conditions on:

```lean
stateEvent T (some H)
```

and takes `c` only to obtain `branchSetOf c`. It contains no assertion that `stateEvent T (some H)` is the note’s exact `Σ_c`, or even that every member of the state realizes `c`.

The global `SibCount` carrier is much closer to the note—it uses `cellEventE ... es c` and prescribed finite `ContFiber` events. But TREE-EXP’s internal split recursion instead consumes `SibCountAt`, whose conditioning-cell connection is absent.

Classification: **global/root face largely faithful; recursive site face not faithful; M**.

### 4. TREE-EXP relies on stronger scaffold data that does not repair the key

`TreeScaffold` provides useful decomposition, covering, and glue fields. But it only sets:

```lean
(splitFrame H hH).c = L.cellAt H
```

It never proves that this cell is the exact cell realized throughout `stateEvent T (some H)`.

Also, the `hjcm` hypothesis is present in `treeExp` but not used by its proof. Multi-side pricing is effectively obtained through the stronger `SitePresents`/`FreshData` setup rather than through the declared open `(JC-multi)` law. The advertised conditionality therefore does not reflect the actual proof dependency.

Classification: **formal recursion assembled, but around the wrong site object and stronger unproved presentation/scaffold interfaces; M**.

### 5. `TREE-N` does not state the note’s stability theorem

The note states that a fixed finite tree fiber becomes an exact union of level-`N` residue classes for every `N ≥ thr(T)`.

Lean’s `treeN` proves only:

```lean
card(fiber at this N) * p ^ AofTr = p ^ (n * N)
```

for an independently supplied model, assignment, ledger, and scaffold at that `N`. Its `hthr` premise is unused, and there is no cross-level identification of the tree fiber or proof of cylinder stability.

Classification: **mass identity at one finite level, not finite-level stability; M**.

### 6. `NsPricing` / `NsGrowth` / `nsNull` split — honest but narrower

This part is honestly documented:

> “this corpus states ONLY the truncated-ratio limit; continuity-from-above and the profinite class NEVER enter.”

`ns_null` proves the finite tower ratio. `NsPricing` and `NsGrowth` are separately declared open owner propositions, while `nsNull_of_pricing_growth` supplies only the abstract analysis lemma.

That is a sensible as-built split, but it does not formalize the note’s claimed profinite `(ns-null)` proof. Therefore it cannot support bidirectional statement faithfulness to the note without an explicit amendment of the note’s status.

Classification: **honestly narrower, but material relative to the note; M**.

### 7. Verdict and eligibility gates — substantially faithful

These portions are generally soundly represented:

- `Vd`, `henVerdict`, `irrVerdict`, and `nsVerdict` match VP-1/VP-2.
- `IrrHalts`, `NsHalts`, `tau_disjoint`, and `tau_total` encode the verdict partition under the declared `KBTot` perimeter.
- `HenLift`, `OmSat`, and `OmSatTot` are hypothesis-only citation interfaces, appropriately not claimed proved.
- `eligibleT` is cell data.
- `CellAssign` genuinely installs `ChildCover` as a mandatory field.
- `constFalse_no_cellAssign` correctly rejects the forbidden root-childless implementation.
- Member-indexed Finset products preserve sibling individuation; no symmetry factor is inserted.
- `oneF`, fiber disjointness, and the decided-set/pre-halt dictionary are appropriately scoped.

Classification: **ratifiable locally**, but insufficient to save the assembly verdict.

### 8. Non-vacuity and residual-status failures

Two further material problems prevent ratification:

1. In [S2_sibFalse.lean](/tmp/leanratify_t/lean/LeanUrat/MovesT/S2_sibFalse.lean), `sibCA : CellData ...` ends after `child_cell_red` and does not provide the newly mandatory `child_red_uniform` field. On the supplied source, that structure literal cannot elaborate.

2. Two of G1’s four admissions are not merely “Q1-gated.” The source itself labels both `toyModel.mem_realizable` and `toyModelB.mem_realizable`:

> “BLOCKED-FALSE at the blueprint’s own tables”

and says:

> “No leaf-σ re-pin can discharge this sorry; the fix requires a blueprint-level re-adjudication.”

Thus the requested description “G1’s four Q1-gated — all disclosed” is inaccurate. Two admitted obligations are known false for their pinned carriers. See [G1_toyGate.lean](/tmp/leanratify_t/lean/LeanUrat/MovesT/G1_toyGate.lean).

The E5 `(U)+(R)` pair is, by contrast, accurately fenced and disclosed.

### Bottom line

Ratifiable components include the verdict alphabet and gates, amended finite `(ns)` machinery, sibling indexing, ONE-F, root-cell charge, and W4-1 `ChildCover` bundling.

But the central adjudication is not implemented:

```text
note: exact site-owned full joint cell
Lean: node ∈ branchSetOf(cellOf entrance x)
```

That discrepancy propagates into `SitePresents`, `state_cell`, `JCmultiAt`, `SibCountAt`, and TREE-EXP. Together with the non-statement of TREE-N stability and the known-false G1 admissions, it requires **REJECT (M)**.