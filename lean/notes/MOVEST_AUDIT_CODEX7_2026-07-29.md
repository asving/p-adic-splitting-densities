# MovesT round-7 Codex verdict (2026-07-29): REJECT 5/1 — 14/19 rows PASS; residues: ChildCover not installed as a CellAssign field; OmSat needs the TOTALITY clause; NsBridgeStmt missing the decay premise; toy leaves violate hspecInc (e*g=1 must be recentering); T-F4 false at the empty shape

I’ll audit the 19-row disposition against the REV-7 text and the supplied built MovesD source, then separately sweep for newly introduced statement/typing defects. I’ll treat the orchestrator rulings as binding and test whether their implementations actually realize them.

Verdict: **REJECT (5 CRITICAL / 1 GAP).**

Four headline REV-7 repairs are not real: OM-SAT remains vacuous, `NsBridgeStmt` lacks the decay premise needed for nullity, the toy node roster is inconsistent/incomplete, and T-F4 is false at the empty shape. In addition, `ChildCover` is defined but not actually installed in the stated `CellAssign` interface.

## Disposition audit

| Row | Result | Finding |
|---|---|---|
| Codex-6 #1 / Fable G-1 — per-track `root_total` | PASS | The quantifiers are correctly `∀ ψ … → ∃ ν, trackOf ν = ψ ∧ child …`; `KBTotTower` and `VPPinned.covering` both carry the same `trackOf`. |
| Codex-6 #2 — W4-1 covering | **CRITICAL** | See finding 1 below. `ChildCover` itself has the right per-track formula, and its falsifier is logically genuine, but the clause is not actually a field of `CellAssign` or threaded through the cited consumers. |
| Codex-6 #3 — OM-SAT realized membership | **CRITICAL** | See finding 2. Adding membership inside `ClusterFactorOf` does not cure implication-vacuity. |
| Codex-6 #4 — closed `windowBlockHts`/`hScale`/`hRes` | PASS | The displayed bodies use the built `History.htH`, `History.floorH`, and last-node `μ * Dwidth`; no unresolved `slot0Block` remains. |
| Codex-6 #5 — typed `NsBridgeStmt` | **CRITICAL** | See finding 3. Its premises do not imply its conclusion. |
| Codex-6 #6 — all toy Node data pinned | **CRITICAL** | See finding 4. The purported full roster is incomplete and conflicts with the built species law. |
| Codex-6 #7 — closed `bandFresh`/`shapeExp` | PASS | `bandFresh` is now explicitly defined from built `ShapePrefix.bandS` and `Nshape`; `shapeExp` is its cardinality. |
| Codex-6 #8 — event/mult re-key | **CRITICAL** | Names are correctly re-keyed to `Presented.event`/`mult`, but T-F4 is false under their new empty-shape semantics. |
| g1 — F1 witness overclaim | PASS | The claim is honestly downgraded to cardinal consistency, with a concrete E-phase witness obligation. |
| g2 — `NPIDPin` re-key | PASS | The text targets `NPIDPin`, `NthrSup`, `noteNP`, and `D4R4_all_noteRange` by their current names. |
| g3 — W4-5 and seam census | PASS | W4-5 is present, and the 20-entry tally recomputes as 1 + 4 + 12 + 3. |
| g4 — `wsh17_pin = W17ii` | PASS | The row now says the instance must prove the actual `W17ii` proposition. |
| g5 — `legs_read` | PASS | S-10 records the new `LegAgree` supply burden. |
| g6 — continuing-only `deltaFactors` | PASS | S-10 explicitly records the narrowing and retires the old all-split-member reading. |
| Fable C-1 — `.red` guards | PASS locally | Both guards now include `x0 = 0 ∧ x1 = 0`; the quoted 24→0 and 192→0 violation calculations are correct. |
| Fable C-2 — `cellLevel` | PASS locally | With `n = 2`, `levelIdx c < 4` covers exactly coordinates `0,…,5`, including every displayed guard coordinate. |
| Fable G-1 | PASS | Same repair as Codex-6 #1. |
| Fable G-2 | PASS | Same repair as g2. |
| Fable G-3 | FAIL | Its W4-5/count/citation legs are repaired, but its event/mult leg inherits the T-F4 empty-shape failure. |

## Critical findings

1. **CRITICAL — `ChildCover` is not actually installed in the W4-1 interface.**

The revision repeatedly claims:

> “`CellAssign` carries the per-track root covering”

But the displayed `CellAssign` structure ends with `child_cell_red`; it has no `child_cover` field. `ChildCover` is subsequently declared as a standalone predicate.

The falsifier itself is sound:

> `(∀ ν x, ¬ T.child none ν x) → … → ¬ ChildCover T CA χ trackOf`

On a supplied window-opening input, constant-false `child` contradicts the existential in `ChildCover`. Thus it genuinely refutes `ChildCover`.

The missing step is making `ChildCover` mandatory at the interface. The prose says an `hccov` hypothesis is taken where full root covering is consumed, but the displayed T-E5, `TreeExpFin`, `TreeNStmt`, `VPPinned`, and `rs1GivenOfMovesT` signatures contain no `hccov : ChildCover …`. `RootSplitData.hcov` is merely “the head is a chain,” not this covering law.

Consequently, constant-false `child` can still instantiate the displayed `CellAssign`; it only fails an optional predicate that no shown package requires. The claimed W4-1 contract installation is therefore incomplete.

2. **CRITICAL — the OM-SAT degree escape remains implication-vacuity.**

The repaired definition is still:

> `ClusterFactorOf … → IrrHalts H → Irreducible fη ∧ …`

and the new realized-membership condition lies inside `ClusterFactorOf`:

> `trackOf (H.nodes.head hne) ∈ normalizedFactors (f.map …)`

For a junk `trackOf`, including a degree-\(>n\) irreducible, `ClusterFactorOf` simply has no witnesses. Hence `OmSat` becomes easier to prove: its antecedent is always false. Adding another conjunct to an already empty antecedent cannot establish non-vacuity.

No displayed clause states the needed totality direction, such as:

> every realized saturated history has some `fη` satisfying `ClusterFactorOf`.

`KBTotTower.root_total` only produces a root child; it does not connect that child/history to an integral `fη`, `ReadsOf`, and the `ClusterFactorOf` package. The claimed “degree-\(>n\) escape dies” is therefore false.

3. **CRITICAL — `NsBridgeStmt` does not imply nullity.**

Its essential type is:

> `Antitone μcap → Tendsto μcap atTop (nhds μclass) → finite-level-read-off → μclass = 0`

Nothing states that `μcap M → 0` as \(M\to\infty\), nor supplies the \(p^{-|Z_M|}\) bound with \(|Z_M|\to\infty\). The finite read-off clause concerns each fixed \(M\) as the digit level \(N'\to\infty\); it does not control the later \(M\to\infty\) limit.

For example, the abstract data `μcap M = 1`, `μclass = 1`, with every finite read-off ratio equal to 1, satisfy all three logical premises but contradict the conclusion.

The type also does not identify `μclass` with the actual `(τ-ns)` class mass beyond naming it, or identify `μcap` with conditional cap masses through an equality. Thus it is neither a faithful typed version of the continuity-from-above proof nor a dischargeable general interface.

4. **CRITICAL — the toy Node roster cannot support the claimed builds and decide checks.**

The table pins every leaf as:

> “leaves `.increment`”  
> “tAνa/tAνb ↦ `(1,1,1,1,…)`”  
> “tBνc/tBνd ↦ `(1,1,1,1,…)`”

But the supplied built MovesD source requires:

> `hspecInc : species = ReadSpecies.increment → 1 < e * g`

For these leaves, the required conclusion is `1 < 1`, false. They cannot become the displayed `ShapeRead`s, and the claimed lawful shape/read checks cannot elaborate as specified. With `e = g = 1`, the matching species is the recentering case, not increment.

The alleged full roster is also incomplete: it pins only `line.slope`, not the complete `line` value, especially its intercept. The text nevertheless claims every Node data field, including `line`, is pinned.

There is a further unverified realizability problem: `Ranch := 0`, `ψ := X`, and positive `μ` are asserted while `TreeModel.mem_realizable` must prove `Realizable` for the toy histories. No displayed obligation shows that this zero anchor has the required finite `ψ`-order or matches `pat`. Therefore the claimed “all proof fields decide” and unchanged tree census cannot be certified from the displayed tables.

5. **CRITICAL — T-F4 is false at the empty shape under the built `mult`.**

The built source explicitly gives:

> `Presented.mult_empty_shape … : S.mult x = 1`

But `PrefIdx` remains History-indexed, and the same source explains that it is empty at `reads = []` because `History` has no empty chain.

T-F4 states without an `hne` premise:

> `S.mult x = card {i : PrefIdx … // … ∧ PreHalt …} + card {i … // … ∧ ¬ PreHalt …}`

At the empty shape this computes to:

\[
1 = 0 + 0,
\]

not the claimed `1 = 1 + 0`. The blueprint’s assertion that the RHS contains “the ∅-shape’s single root class” contradicts the built carrier: that root class exists only in the option-level `PrefOpt` design, not in `PrefIdx`.

This is exactly why the built incidence theorem gained an `hne : reads ≠ []` premise. Merely changing `multO` to `mult` does not repair T-F4.

## Gap

**GAP — the closed height accessor is textually closed but its exactness claim is not justified on its stated domain.**

`hRes` uses:

> `(H.floorH H.nodes.length 0).unbot' 0`

while asserting that `⊥` occurs only at prefix length zero. That requires positivity/interiority facts about the last window. They are intended on lawful realized histories, but `hRes` itself accepts every `History` and its stated exactness is not accompanied by a lawfulness hypothesis or theorem. This does not recreate the former undefined-name defect, but the “exact on every nonempty history” claim is stronger than the displayed support.

The decisive failures are the four requested semantic seams—OM-SAT, ns-null, toys, and event/mult—plus the missing mandatory integration of `ChildCover`.