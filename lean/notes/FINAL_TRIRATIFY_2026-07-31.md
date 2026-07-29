# FINAL TRI-RATIFICATION VERDICTS (2026-07-31): U REJECT 4/0 (TreePin uninhabitable at N=0 — Fin(n*0) empty, the inst premise inconsistent; the 13 explicit Prop parameters still unpinned — ADJUDICATED: the wave-4 boundary, recorded not typed; TreePin needs the completeness direction; the betaLeg roster needs injectivity/coverage). T REJECT M (the exact-cell repair landed locally BUT the site-keying defect stands: co-realized siblings share (parentSt, x) so cellOf cannot distinguish — THE FIX: the branch is part of the child site entrance state; + the c/cSplit two-keying). V REJECT 6M/4N (template_total SEMANTICALLY FALSE by in-corpus-constructible countermodel — the negation-free check insufficient; valB = a table-side lemma, the note VAL(b) needs the realization-completeness premise; muhatN_law circular — must be the measure-definition law with COMP-h DERIVING the product; the seam duties remain sorried).

==== finalratify_u ====
I’m auditing this as statement semantics again, with special attention to whether the 13 explicit theorem parameters are an acceptable honest conditional form rather than pretending to be typed owner statements. I’ll also check the actual workspace/build and trace the new TreePin, RegPin, Cl7Kernel, \( \mathbb Z_p \) bridge, and derived checksum seams for quantifier or roster defects.

# REJECT (4 CRITICAL / 0 GAP)

Several round-3 repairs are genuine, but the final statement remains unratifiable. Most decisively, `TreePin` is uninhabitable for every `n ≥ 2`, making `theoremU`’s `inst` premise impossible.

## CRITICAL 1 — `TreePin` is impossible at `N = 0`

Quote:

```lean
chart : ∀ N : ℕ, Fin n → Fin (n * N)
```

For `N = 0`, this demands:

```lean
Fin n → Fin 0
```

But `theoremU` assumes `2 ≤ n`, so `Fin n` is inhabited while `Fin 0` is empty. Therefore no `TreePin` can exist, hence no `UInstance` can exist, hence:

```lean
inst : ∀ (p : ℕ) (hp : p.Prime), UInstance ...
```

is an inconsistent premise.

This makes the capstone vacuous before any ledger mathematics is considered. The chart must be restricted to positive levels, or its type redesigned.

## CRITICAL 2 — The 13 explicit `Prop` parameters still impose no mathematical obligations

Quote:

```lean
(rel1 rel2a rel2b rel2d rel2e rel3 : Prop)
(rs0Lump trackRule dnLattice : Prop)
(m1m5Echo x1aDict m4bConst jcInvHist : Prop)
...
(hrel1 : rel1) ...
```

Making these parameters visible is more honest than hiding them in a structure, but it does not repair their proposition semantics. A caller can instantiate every one with `True` and provide `True.intro`.

Because their meanings occur only in comments and parameter names, the theorem does not require the actual REL.1, REL.2, TRACK-RULE, denominator-lattice, M1/M5, X.1a, M4b, or JC-INV statements. They are also unused in the proof.

Thus the former bare-`Prop` defect is repaired for the rows now reaching `MovesX`, `MovesRBase`, `MovesV`, and `MovesT`, but not for these 13 rows. Visibility is not semantic pinning.

## CRITICAL 3 — `TreePin` still pins only a selected subfamily, not the complete canonical-tree corpus

Quote:

```lean
vt : ∀ σ, F.Tree σ → MovesT.VTree p (ZMod p)
vt_inj : ∀ σ, Function.Injective (vt σ)
```

and:

```lean
canonical_pin : ...
  X.canonical N f = some σ ↔
    ∃ T : F.Tree σ, ... ∧ (vt σ T).fiberAt ...
```

There is no converse completeness/surjectivity statement saying that every complete finite realizable canonical `MovesT.VTree` of type `σ` is represented by some `T : F.Tree σ`.

Consequently an instance may choose a proper subfamily of `MovesT.VTree`, define `X.canonical` to recognize exactly that subfamily, and satisfy `canonical_pin`. The pin therefore does not yet identify `F.Tree σ` with the note’s complete family; it identifies it with an injectively embedded selected family.

The independently assumed:

```lean
seam.count_tie
```

then supplies the desired count law for that selected family, rather than deriving it from `MovesT.treeN` for the complete canonical corpus.

## CRITICAL 4 — The β-leg roster can duplicate labels and omit real consumed legs

Quote:

```lean
legSt : ∀ b : D.Block,
  D.legIdx b → (e' : {e' // e' ∈ Finset.Icc 1 n}) × C.T.State e'.1
```

with only:

```lean
leg_pin : ∀ b, D.legCount b = ∑ ...
```

and:

```lean
betaLeg_pin : ...
  D.betaLeg b l δ =
    MovesS.powSubst ...
      (∑ σ' ∈ C.chain.Sigmas, MovesS.blockSolve ... (legSt b l) ...)
```

`leg_pin` fixes only the number of abstract labels. Nothing makes `legSt` injective, surjective, or keyed to the actual source outcome/member/continuation roster. Multiple abstract labels may map to the same real block/state while another consumed β-leg is omitted.

Since `entryList` quantifies over the abstract `D.legIdx`, such duplication can remove required real β-values from `(r2)`. This is precisely the surrogate-roster problem the pin was intended to eliminate.

## Repairs that do land

- `UpstreamTyped` contains real owner-corpus statements rather than bare tags.
- `RegP` is now syntactically `(r1) ∧ (r2)`; the independent `S.R` clauses were removed.
- `bterm_pin` removes the former per-row existential choice.
- `bsplit_pin` reaches the real `MovesS.bSplit`.
- `act_pin` is sufficient for the stated derived `R_agree`.
- `SolveSeam.R_defined`, `R_agree`, and `rs4_eval` are genuinely derived.
- `zf_factor` now fixes each pair as:

  ```lean
  (MovesT.ramIdx h, MovesT.resDeg h)
  ```

  and the remaining HC-2/IP-1 obligations are explicitly disclosed.
- `Cl7Kernel` has the correct p-uniform binder order, and `UInstance.cl7_slice` uses the same `K7.Tbound` for every prime. However, the untyped `trackRule` and `dnLattice` residues remain non-obligations because of Critical 2.

I could not run the Lean build because the managed command sandbox again failed to launch: `bubblewrap` is unavailable. The rejection grounds above are proposition-level and do not depend on compilation.

**Verdict: REJECT (4 CRITICAL / 0 GAP).**
==== finalratify_t ====
I’ll verify the repaired surfaces and their actual proof dependencies, then run a source-wide `sorry`/axiom and compile sweep if the workspace contains the project. I’ll distinguish faithful open obligations from contradictions or under-keyed statements.

## Verdict: REJECT (M — material)

Several requested repairs are present, but the central exact-cell representation remains structurally incapable of modeling distinct co-realized sibling sites. A new two-cell split also makes site-level `(SIB)` differently keyed from the note.

### Repaired findings

1. Exact-cell syntax: repaired locally.

> `siteCellEvent ... es c := {x | x ∈ entEvent ... es ∧ CA.cellOf es x = c}`

This is now an exact fiber, not the former node-in-`branchSet` union.

2. `(JC-multi)` key: repaired.

> `Nat.card ↥(siteCellEvent T CA χ es c) * ...`

The priced event now mentions the `SideSplit`’s own cell, and `splitAt` is indexed by `cellAt H`.

3. `hjcm`: consumed.

In `cone_charge`, the multi-side branch explicitly uses:

> `hjcm H ⟨hH, h2⟩ h2`

and rewrites it using `hsplit_exp` and `state_cell`. `presents_imply_jcMultiAt` also correctly proves that the stronger ledger presentation fields already imply this instance.

Classification: repaired, although the open burden is effectively embedded in the stronger `SiteLedger` fields.

4. TREE-N stability: statement added and honestly open.

> `def TreeNStable ...`
>
> `theorem treeN_stable ... : TreeNStable Tat χat Tr := by sorry`

This does express cross-level cylinder dependence for a fixed tree. Classification: repaired at the statement layer, disclosed open.

There is still an integration limitation: `RS1GivenPackage.tree_n` remains `TreeNStmt`, which contains only the single-level mass identity, not `TreeNStable`. Thus the stability statement exists but is not carried by the advertised RS.1 package.

5. S2: repaired.

`sibCA` now supplies:

> `child_red_uniform := by ...`

and the `.red` cell is refined by `x 0`, resolving the earlier missing-field/elaboration defect.

6. G1 record: corrected.

The header now accurately distinguishes:

> `toyModel.mem_realizable / toyModelB.mem_realizable — BLOCKED-FALSE`

from:

> `twoNodeKcardH / toy_v8_wchain — OPEN-BLOCKED`

Classification: status record repaired. The two `mem_realizable` admissions remain known-false pinned-carrier axioms; they were documented, not mathematically discharged.

### Material remaining defect: the “exact cell” is still not per-site keyed

`siteCellEvent` is keyed only by `es` and `c`:

> `CA.cellOf es x = c`

For two co-realized sibling sites with the same `parentSt`, `state_cell`

> `stateEvent T (some H) = siteCellEvent ... (parentSt H) (cellAt H)`

forces their exact cells—and hence state events—to coincide whenever they share a fiber witness. The corpus itself acknowledges this:

> “this forcing is now a MACHINE-CHECKED INSTANCE-LEVEL OBSTRUCTION … at co-realized sibling sites with distinct pins”

That is precisely the nondegenerate F1 situation: the sibling continuation events have distinct pins. The supplied toys avoid the contradiction only because:

> “their sibling leaf states coincide by table”

So the exact-cell syntax is repaired, but the carrier still lacks the site/branch/frame index needed to represent distinct sibling reads. This is a central representational defect, not merely an unproved owner theorem.

Classification: **incorrectly keyed at branching sites; M**.

### New material mismatch: conditioning cell and branch-roster cell are separated

The note uses one cell `c` both for `Σ_c` and for its branch set. Lean now defines:

> `SibCountAt ... (c cSplit : CA.Cell) ...`

and conditions on:

> `siteCellEvent ... es c`

while taking the sibling product over:

> `CA.branchSetOf cSplit`

TREE-EXP supplies these as:

> conditioning cell: `L.cellAt H`  
> roster cell: `(sc.splitFrame H hH).c`

There is deliberately no equality between them. The `TreeScaffold` documentation calls this a:

> “DISCLOSED DEVIATION”

and says the note’s single cell datum is split across two entrance keyings.

Thus an arbitrary split-cell roster can be attached to an unrelated exact conditioning cell, provided the separately assumed `SibCountAt` equation holds. This repairs the earlier missing tie by replacing it with a stronger, differently keyed hypothesis—not by formalizing the note’s single `Σ_c` branching cell.

Classification: **statement mismatch / under-connected scaffold; M**.

### Other prior residuals

The profinite `(ns-null)` discrepancy remains. The corpus still states:

> “ONLY the truncated-ratio limit; continuity-from-above and the profinite class NEVER enter.”

`NsPricing` and `NsGrowth` remain separate open propositions. This is honest, but narrower than the note’s claimed profinite nullity proof.

The root recursion also retains the disclosed `hD4R0K` admission in `fiber_root_split`; it is not a new defect, but TREE-EXP remains dependent on that fenced `sorry`.

I could not independently rerun Lean because the execution sandbox launcher was unavailable, so this is a statement-and-proof-dependency audit of the supplied corpus. The rejection does not depend on compilation: the per-site collapse and the `c`/`cSplit` mismatch are visible directly in the theorem interfaces.
==== finalratify_v ====
I’m checking the repaired dependency graph directly, with special attention to whether the new hypotheses merely expose open duties or still smuggle conclusions. I’ll also sweep every `sorry`, the seam constructors, and the exact `Tgam`/`chainCount` and `μhatN` laws before issuing the N/M verdict.

# Verdict: REJECT (6M/4N)

The original contradictory `writeHeights_total_unscoped` shim is genuinely gone, and the three existential replacements use the correct quantifier direction. But the corpus still contains a false universal `template_total`, the MovesS seam remains disconnected and degenerate, VAL(b) still does not identify the note’s realized count, and COMP-h is still assumed by its carrier.

## Material findings

### M1 — The old shim is repaired, but `template_total` is still a false universal theorem

The repaired threading is sound:

> `writeHeights_total_of_perimeter ... (hs : Order0Perimeter εT h)`

and consumers such as `ledgerIV_comp_once`, `initRat_comp`, `comp_agg`, and `ctsM` now require `EntDomOrder0`. The prior direct contradiction with `WHNeg.writeHeights_total_false` is therefore removed.

However, the corpus still asserts with `sorry`:

> `template_total {n} (ε : EntShapeV n) : (ε.template?).isSome`

The surrounding source itself records that `SpWordNeg.P3` is a valid `ShapeWF` prefix that extends to an `EntShapeV`, while:

> `spWordFits_impossible ... : ¬ SpWordFits 3 P3 ws`

For the resulting entrance shape, `spWord 3 P3 = []`, hence `collapseRuns [] = []`; the first test inside `template?` is `w ≠ []`, so `template? = none`. Thus the theorem is semantically false even if no separately named `¬ template_total` declaration was committed.

“Negation-free” is not sufficient for soundness: the countermodel is constructible from the checked witness already in the corpus.

Classification: **M — rejection-forcing logical unsoundness.**

### M2 — `valB` is honest as a table-chain lemma, but it is not the note’s VAL(b)

The corpus proves:

> `chainCount S γ x h = (pathProdPoly V γ).eval q₀`

But its process-side count satisfies only:

> `Tgam = card {c : Chains ... // RealizesC ... c}`

and:

> `Tgam ≤ chainCount`

There is no surjectivity/completeness statement saying every assignment chain is process-realized.

The coupling toy is therefore an honest separation result, but it confirms the missing bridge rather than repairing it. The note defines \(T_\gamma(x,h)\) as chains realizing \((\gamma,h)\); that corresponds to `Tgam`/the `RealizesC` subtype, not unrestricted `chainCount`.

XHD conditionality does not close this gap. XHD-d establishes positivity and domain exactness, while XHD-u establishes row-count uniformity and height rectangularity; neither says every combinatorial chain is realized by a mark.

Classification: **M — `valB` should be labeled a table-side product lemma unless a realization-completeness hypothesis is added.**

### M3 — COMP-h remains circular, and the series leg is still absent from the capstone

`CompCarrier` directly assumes:

> `μhatN ... = ιN ... * pathProdPoly.eval ... * gProd ...`

Then `comp_h_step` closes by:

> `exact cc.μhatN_law ...`

Consequently, the carrier field is the finite-level COMP-h conclusion itself. It is not merely a carrier law connecting event fibers to censuses: its statement contains the complete multiplicative identity and mentions neither `tevt`, a fiber decomposition, nor an assignment-chain bijection.

There is also still a series-level disconnect:

- `comp_hsum` is a genuine `HasSum`, but its total uses `cc.ιN` at `compLvl`.
- `iotaEps` uses `cc.ιN` at `entLvl`.
- No stabilization theorem equates those entrance masses across levels.
- `CompSigma_Stmt` contains only the algebraic equality
  > `iotaEps * pathProd * gcVal = iotaEps * stepProdVal`
  and no marked-event `HasSum`.

Thus the capstone still does not state or derive the note’s marked-event COMP-Σ identity.

Classification: **M — circular premise plus weakened composition conclusion.**

### M4 — The existential quantifier repair is logically correct, but the seam remains unconnected

These replacements are preferable to the false arbitrary-\((T,M)\) statements:

> `∃ T M, Nonempty (MovesS.LedgerIV T M)`

> `∃ T M, Nonempty (MovesS.RatBurdens T M)`

> `∃ T, Nonempty (MovesS.SCSData T)`

The arbitrary-\((T,M)\) formulation would indeed be false. But the existential conclusions do not state that their witnesses are the table and measured system constructed from the supplied `C`, `V`, or `X`.

The implemented constructors still expose the old defect:

> `StateOf ... := {p : Σ s : Skeleton n, PUnit // skBlk p.1 = e}`

rather than states carrying `CellIdx`, and `tableShape_inst` sets:

> `Wloc := ... 0`  
> `Wstate := ... 0`

The measured constructors still use combinations of:

> `Cell := ... PEmpty`  
> `EntShape := ... PEmpty` or `Unit`  
> `μcell := ... 0`  
> `rowVal := ... 0`

Hence the existential sorry duties can be witnessed by systems unrelated to the CTS objects unless explicit equivalences and field ties are added.

Classification: **M — the vacuous disjunctions are gone, but the substantive MovesV→MovesS seam is not formalized.**

### M5 — `EntDomOrder0` is safely scoped but materially narrower than the note

`Order0Perimeter` requires:

> `εT.word = [s]`

and `EntDomOrder0` requires every point of every supplied entrance domain to satisfy that perimeter. Therefore any template with a nonempty certified domain is forced to be one-letter.

This safely prevents the former unscoped reconstruction, but it does not formalize the note’s general finite height-forgetting template/instantiation bijection. Multi-letter, self-loop-free entrance templates can only be handled by making their domains empty or by remaining outside the supplied perimeter.

Classification: **M — sound conditional theorem, materially incomplete entrance reconstruction.**

### M6 — The census-scope finding stands

The revised root census repairs the `(2,2) ↦ T21` keying, but the formal census still covers only three semantic profiles. `blk2_census` still concludes a disjunction rather than all three separately identified outcomes, and gate B remains arithmetic plus a supplied `CoprimeLiftPack`, not the complete claimed enumeration theorem.

Classification: **M — selected evidence formalized, not the sealed 178-check claim as a theorem.**

## Narrow findings

### N1 — SolveCond’s statement is repaired, but the entire solve is assumed

The `→ True` conclusion is gone. `SolveCond_Stmt` now correctly displays:

> `EscapeE0Rec → ActiveValueAgree → HMC → EntCount → InitRat_Stmt →`  
> `MovesS.DetHyp ... ∧ NeumannRec L`

But `ctsM` takes:

> `(hsolve : SolveCond_Stmt L)`

and copies it into the conclusions. This is sound and transparent, but it does not derive the solve from E0, HMC, ENT-COUNT, and INIT-RAT; it assumes the complete desired implication.

Classification: **N — faithful named open burden, not a proved CTS-M leg.**

### N2 — A separate `→ True` escape remains

`degcons_kmat_gate` still concludes:

> `(∀ ... KmatHyp ...) → MovesS.DegCons T → True`

and is discharged by `trivial`. It establishes neither `KmatHyp` nor `DegCons`.

Classification: **N — governance/gate-local vacuity.**

### N3 — `hmark` remains an explicit perimeter enlargement

The refuting `emult = 0` model justifies requiring positivity, but the note’s continuing-mark construction should ultimately derive it rather than add it to `ctsM`.

Classification: **N — sound repair, extra hypothesis.**

### N4 — W17ii remains banked

`w17ii_wave4` still contains its disclosed `[3t]`-owned `sorry`, and `w17ii_pin` depends on it.

Classification: **N — transparent exclusion, incompatible with unconditional full-tree ratification.**

The decisive rejection grounds are the false `template_total`, the missing `Tgam` realization bridge, circular `μhatN_law`, and the still-disconnected MovesS seam.

Execution caveat: a fresh filesystem scan/build could not run because the command sandbox failed before execution due to the unavailable `bubblewrap` launcher. This is therefore a statement-and-dependency audit of the supplied round-2 corpus.
