# RATIFICATION ROUND 4 (2026-08-01): MovesU RATIFY (0 material / 1 minor doc — THE CAPSTONE CORPUS RATIFIED); MovesT RATIFY (every prior finding repaired-or-recorded; no new material defect); MovesV REJECT 3M/2N (the seam-pin records overclaim vs their equivalence types; ValB_Stmt still exports the table count where the note wants the realized Tgam count — the repaired val_b sits beside the capstone, not in it; the five-class census missing TH12/TH3c). The last V round charged.

==== ratify4_u ====
I’ll verify the round-4 changes against the actual workspace, including compilation if the project is runnable, then re-audit all prior findings and the four highlighted seams. The 13 bare premises will be judged under the stated wave-4 boundary rule: accuracy and completeness of the record, not absence of typing.

# RATIFY (0/1)

**0 material defects / 1 minor documentation defect.**

The corpus now meets the stated ratification criterion. The previous semantic failures are either repaired with typed statements or accurately exposed as explicit boundary records.

## Round-4 decisive items

- **Positive-level chart guard — repaired.**

  ```lean
  chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N)
  ```

  The impossible `Fin n → Fin 0` obligation is gone.

- **Chart inhabitability — proved.**

  ```lean
  def chartWitness ...
  theorem chartWitness_inj ...
  ```

  For every `N > 0`, `i ↦ digitIdx n N i ⟨0,hN⟩` supplies an injective chart. The record accurately discloses that `TreePin` says nothing at `N = 0`; this is no longer a hidden contradiction. Level zero remains covered conditionally by the typed `TreeSeam`.

- **Canonical-tree completeness — repaired.**

  ```lean
  vt_surj : ∀ ...,
    V.typemult = σ.1 → V.thr n ≤ N →
    MovesT.Realizes ... V →
    ∃ T : F.Tree σ, vt σ T = V
  ```

  Together with `vt_inj`, `vt_typemult`, `vt_thr`, `vt_real`, and `canonical_pin`, this eliminates the former proper-subfamily bypass for the relevant realized corpus.

- **β-leg roster — repaired.**

  ```lean
  legEquiv : ∀ b, D.legIdx b ≃ LegRoster C.T (blk b).1
  legSt_pin : ...
  betaLeg_pin : ...
  ```

  `LegRoster` is keyed to actual states, split outcomes, and continuing-member positions. The equivalence supplies both injectivity and coverage; `legSt_pin` prevents relabeling targets.

- **Wave-4 boundary record — accurate.**

  The docstring expressly says:

  ```text
  These 13 premises are UNPINNED (True-instantiable) pending the
  wave-D carriers
  ```

  It correctly enumerates exactly 13 rows: six REL rows, `rs0Lump`, `trackRule`, `dnLattice`, `m1m5Echo`, `x1aDict`, `m4bConst`, and `jcInvHist`. It names their owners, distinguishes the already-typed faces, and prohibits representing the residuals as typed or discharged. Under the charge’s explicit boundary-record rule, this is honest conditional form.

## Prior findings

| Prior finding | Current classification |
|---|---|
| Bare ledger tags | Repaired for built vocabulary; remaining 13 accurately recorded as the wave-4 boundary |
| Direct `finiteness_stack`/`solve_stack` assumptions | Repaired: derived from `TreeSeam` and `SolveSeam` |
| Solve/tree/classifier objects unpinned | Repaired through `r_is_solve`, `TreePin`, and `vt_surj` |
| Surrogate `(REG-p)` roster | Repaired through `RegPin`, real-table pins, and `LegRoster` bijection |
| Strengthened/incomplete `RegP` | Repaired: formal definition is `(r1) ∧ (r2)`; `R_defined` and `R_agree` are derived |
| `(U-n)` omitted from capstone | Repaired: exported as the first conjunct under `RegP` |
| No genuine \(\mathbb Z_p\) bridge | Repaired conditionally through `ZpBridge`, `ramIdx`, `resDeg`, and `lift_true ↔ ZpReads` |
| Enlarged `sq2_partial` hypotheses | Repaired: only `TreeSeam` remains |
| Existential `R` not identified | Repaired by `R = S.R` and `r_is_solve` |
| Evaluated checksum assumed | Repaired: `SolveSeam.rs4_eval` derives it |
| CL-7 bound instance-dependent | Repaired: `K7.Tbound` precedes the prime quantifier and serves every prime |
| N=0 chart inconsistency | Repaired by `0 < N` guard and witness |
| Selected tree subfamily | Repaired by `vt_surj` |
| Duplicated/omitted β legs | Repaired by `legEquiv` and `legSt_pin` |

## Remaining minor documentation defect

This sentence in the `RegP` docstring is literally inaccurate:

```text
every index family nonempty-pinned
```

`JIdx`, `WIdx`, and `legIdx` are only cardinality-pinned and may correctly be empty when their real rosters are empty. Nearby documentation states the correct policy:

```text
J/W/leg families pinned BY EQUATION ONLY — no positivity
```

This is a stale comment, not a proposition-level defect: the equations and image pins prevent artificial omission of nonempty real rosters.

The Lean build could not be executed because the managed sandbox lacks `bubblewrap`. The verdict is therefore a statement-semantic ratification; none of the conclusions above depends on proof compilation.
==== ratify4_t ====
I’ll verify the current workspace rather than rely only on the pasted corpus: enumerate every `sorry`/axiom, inspect the repaired keying and package seams, and compile the `MovesT` target if the project tooling is present. I’ll judge the six fenced admissions by the accuracy of their records, as requested.

## Verdict: RATIFY

The round-4 corpus merits ratification under the stated criterion. Every previous material finding is either repaired in the theorem interfaces or preserved as an accurate, explicit boundary record. I found no new unrecorded material defect.

Key verification:

- Per-site keying is repaired by:

  > `branchCellOf : EntSt ... → Node ... → Box ... → Cell`

  and

  > `siteCellEvent ... es ν c := ... branchCellOf es ν x = c`

  Sibling sites therefore use different read maps. `branch_cell_joint` correctly says each member-keyed read factors through the entrance joint read. The scope of `f1_two_leaf_discharge` is accurately described: it machine-checks structural/event-level satisfiability, not the full external F1 census.

- `(JC-multi)` now prices the same site-owned cell and member-keyed event:

  > `JCmultiAt ... es ν ... ss`

  with `ss : SideSplit ... c fd` and `siteCellEvent ... es ν c`.

- The former `c`/`cSplit` divergence is gone. `SibCountAt` has one cell, and:

  > `hframe_cell ... : (splitFrame H hH).c = L.cellAt H`

  ties the scaffold roster to the conditioning cell.

- `TREE-EXP` consumes the repaired rows. Its `hsibT` uses the single `L.cellAt H`; its `hjcm` uses `H.lastNode`. The stronger presented-face absorption of `(JC-multi)` is explicitly disclosed by `presents_imply_jcMultiAt`, so the dependency is not hidden.

- `TREE-N` stability is both typed and integrated:

  > `tree_n := TreeNStmt ... ∧ TreeNStableStmt ...`

  in `RS1GivenPackage`. This closes the former integration defect.

- The old shared-read forcing is quarantined as historical text. The surviving theorem `shared_read_forces` is correctly restricted to one shared map and does not reintroduce the retired obstruction.

- `S2` supplies both `child_red_uniform` and the new member-keyed fields, so the former incomplete structure literal is repaired.

### Six admissions

All six are accurately fenced:

1. `E5_rootSplit`: `hD4R0K` — named `(U) ∧ (R)` root-child boundary, owner HC-2/D4R0K.
2. `E11_treeN`: `treeN_stable` — named typed cross-level stability row.
3. `G1`: `toyModel.mem_realizable` — explicitly **BLOCKED-FALSE** for the pinned toy.
4. `G1`: `toyModelB.mem_realizable` — likewise explicitly **BLOCKED-FALSE**.
5. `G1`: `twoNodeKcardH` — task-#44 construction boundary.
6. `G1`: `toy_v8_wchain` — task-#44 dependent boundary.

The two false toy obligations are not mislabeled as mathematical results or silently used as canonical `CellAssign` instances. Their failure mode and required re-adjudication are stated plainly. Under the supplied rule that recorded wave-4 boundaries count as honest form, they do not require rejection.

Other remaining conditional content—`SibCount`/`SibCountAt`, `JCmultiAt`, `HenLift`, `OmSat`, `OmSatTot`, `KBTotTower`, `PCI`, `NsPricing`, `NsGrowth`, `RepPrefixClosed`, `LeafReg`, `RepNorm`, X.3 and REL/XRB inputs—is named and typed or explicitly excluded from the claimed scope. The finite-only `(ns-null)` result is accurately distinguished from the open profinite owner legs.

I could not rerun Lean because the workspace command launcher failed before execution (`bubblewrap` unavailable). The verdict is therefore a source/interface and dependency audit of the supplied current corpus, not an independent rebuild.
==== ratify4_v ====
I’ll verify the round-4 corpus itself, not just the pasted excerpts. I’m checking every historical rejection point, all `sorry`/axiom-bearing declarations, the renamed VAL(b) and COMP rows, and whether the witness-pinned seam records accurately exclude unrelated degenerate witnesses under your boundary-record rule.

# Verdict: REJECT (3M/2N)

The principal logical repairs are real: the false entrance-totality theorem is gone, COMP-h is no longer hidden inside `CompCarrier`, and COMP-Σ now contains the marked-event `HasSum`. But the current corpus still does not merit RATIFY. The decisive defects are the inadequately pinned MovesV→MovesS seam, CTS-M exposing the table count rather than the realized `Tgam` count, and the still-incomplete semantic census.

## Material findings

### M1 — The seam boundary records claim stronger witness pinning than their types provide

All three vacuous `∨ True` statements are gone, and the three Phase-B obligations are named sorries. That part is repaired.

But the records repeatedly claim that their new clauses:

> “exclude every degenerate unrelated witness”

The actual pins are only:

```lean
Nonempty (T.VType ≃ VLabel n)
∀ e, Nonempty (T.State e ≃ StateOf n e)
∀ q₀ ∈ V.Pools, ∀ N, Nonempty (V.Box q₀ N) →
  Fintype.card (M.Box q₀ N) = Fintype.card (V.Box q₀ N)
```

These do not tie:

- `T.Out`, `T.odata`, `T.Wloc`, or `T.Wstate` to `C`;
- `M.Pools`, cells, events, masses, rows, entrances, or marked values to `V`;
- the witness to the particular result of `tableShape_inst`.

Worse, the supposedly pinned carrier is itself:

> `StateOf ... := {p : Σ s : Skeleton n, PUnit // skBlk p.1 = e}`

It omits the required CTS `CellIdx`. Correspondingly, `tableShape_inst` still installs:

> `Wloc := ... 0`  
> `Wstate := ... 0`

The concrete measured constructors demonstrate the remaining freedom:

> `Cell := ... PEmpty`  
> `μcell := ... 0`  
> `rowVal := ... 0`  
> `EntShape := ... PEmpty`

A box-cardinality equality does not prevent any of this. Thus `ledgerIV_inst`, `ratBurdens_exists`, and `scs_data_supply` are named boundary rows, but their records inaccurately say they are witness-pinned to the real CTS measured system.

Classification: **M — the historical seam finding remains rejection-forcing.**

### M2 — Realized VAL(b) exists, but CTS-M still exports only table-side `chainCount`

The local repair is good:

- `val_b_table` proves the assignment-chain product;
- `RealizationComplete` is a named typed surjectivity obligation;
- `tgam_eq_chainCount_of_complete` bridges the counts;
- `val_b` proves the `Tgam`-keyed product under that obligation.

However, the capstone still defines:

> `ValB_Stmt ... := ... chainCount ... = pathProdPoly ...`

and `ctsM.val_b_chain` is discharged with:

> `exact val_b_table ...`

`CtsmLedger` has no `RealizationComplete` field or corresponding `ctsM` argument. Consequently CTS-M still does not expose the note’s actual realized linked-count conclusion; the correctly repaired `Tgam` theorem sits beside the capstone rather than in it.

The ownership comment also overstates the available route when it suggests entrance no-stray laws discharge completeness. Positivity/no-stray proves that at least one realized mark exists; it does not prove surjectivity from marks onto every combinatorial `Chains` element.

Classification: **M — the local theorem is honest, but the advertised CTS-M surface remains one direction too weak.**

### M3 — The sealed census claim is still not represented semantically in both directions

The polynomial identities are substantive, and the repaired `(2,2) ↦ T21` key is correct. But the previous census-scope finding remains.

`rootTable_census` proves semantic counts for only:

```lean
(3,1) ↦ TH3
(2,2) ↦ T21
(1,3) ↦ T3
```

It still has no semantic class-count theorem for `TH12` or `TH3c`, despite the surrounding text describing the five-class census.

Likewise `blk2_census` still concludes:

```lean
split equality ∧
  (one-root equality ∨ zero-root/inert equality)
```

rather than separately identifying split, inert, and double classes. Gate B remains dyadic arithmetic plus a supplied `CoprimeLiftPack`, not the claimed exhaustive residue census theorem.

There is no named boundary row accurately saying that the full “178 exact checks” remain external/evidence-only at this semantic layer.

Classification: **M — selected formulas are proved, but the stated sealed census is still stronger than the kernel theorem surface.**

## Narrow findings

### N1 — The vacuous gate theorem remains

`degcons_kmat_gate` still states:

```lean
(∀ e, ... → KmatHyp T e) → DegCons T → True
```

and proves it by `trivial`. It establishes neither gate property.

Classification: **N — governance-local vacuity, unchanged.**

### N2 — W17ii is fenced, but its own record admits the universal statement may be false

The sole banked clause remains a universally quantified theorem with `sorry`. Its comment accurately records that an infinite-domain, constant-weight countermodel may exist and may require a summability guard.

Under the campaign’s boundary rule this is an honestly disclosed exclusion, but it cannot be counted as proved content.

Classification: **N — accurately fenced banked duty.**

## Prior findings now repaired or honestly bounded

- The false `template_total` has been deleted. `template_total_of_perimeter` is scoped, and `TTNeg.template_total_false` records the compiled countermodel.
- `writeHeights` consumers now require `Order0Perimeter`; the old contradictory unscoped shim is gone.
- The narrow order-0 reconstruction is explicitly recorded as a Phase-B boundary rather than advertised as general reconstruction.
- `CompCarrier.μhatN_law` is gone. Its remaining fields are measure/census-definition laws.
- `CompProduct` and `IotaLvlStable` are named typed open rows supplied explicitly to `ctsM`.
- `comp_sigma_hasSum` repairs the marked-event series conclusion.
- `SolveCond_Stmt` no longer concludes `True`; the complete solve implication is an explicit named hypothesis.
- `hmark` is accompanied by its refuting model and is honestly exposed.
- `MarkFiberTie` is explicitly named rather than silently assumed.
- HMC remains an explicit antecedent and is not produced by CTS-M.

The supplied text contains the advertised four proof holes: the three Phase-B seam duties and banked W17ii. Their number is not the rejection ground; the inaccurate strength of the seam pins is.

A fresh `rg` scan and Lean rebuild were unavailable because the execution sandbox failed at its missing `bubblewrap` launcher. This verdict is therefore a dependency-and-statement audit of the complete corpus supplied in the charge.
