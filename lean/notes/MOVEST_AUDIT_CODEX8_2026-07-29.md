# MovesT round-8 Codex verdict (2026-07-29): REJECT 6/4 — "the principal REV-8 repairs are mathematically sound"; ALL required judgments PASS (re-fence, toy cover failure, NsBridge counter-model, gamma/line/residual arithmetic, OmSatTot, record-19); criticals = the closure/elaboration layer (UnramifiedOfDeg undeclared, ramIdx/resDeg vs Mathlib API + instances, toy decls as prose, List-vs-Finset, CellAssign coercion) + ONE semantic (IsLumpLocus missing the literal-zero clause)

I’ll audit this as a verifier, not a repair pass. I’ll first locate the REV-8 source and built Lean tree, then mechanically check the manifest/references and independently recompute the key countermodels and toy arithmetic before issuing a classified verdict.

The local command runner is currently failing before execution because its sandbox helper (`bwrap`) is unavailable. I’m testing the available read-only access path now; if it remains unavailable, I’ll clearly separate text-verifiable findings from path/line checks that could not be independently executed.

The central REV-8 repairs are textually present. Two issues are already emerging in the fresh sweep: the closure manifest claims a declaration for `UnramifiedOfDeg` that the displayed Lean does not actually provide, and at least one §2.11 jet helper appears to treat the built `FreshData.clauses` list as a `Finset`. I’m checking the relevant Mathlib and built-signature assumptions before classifying them.

The key arithmetic checks are clean: the toy cover failure is real at \(g=(1,0)\), the γ values are exactly \(3,4,6\), and the anchored residuals have ψ-orders \(2,1,1\) as claimed. The revised `NsBridgeStmt` also kills the old \(\mu_{\rm cap}\equiv1\) model at the new growth premise.

The likely rejection is now coming from the new closure layer itself: several manifest entries are comments or pseudo-bodies rather than Lean declarations, and the proposed `ramIdx`/`resDeg` definitions do not match Mathlib’s current ideal API or have the instances needed for arbitrary `g`.

## Verdict: REJECT (6 CRITICAL / 4 GAP)

The principal REV-8 repairs are mathematically sound, but the new closure-manifest standard is not met. Several displayed declarations cannot elaborate or are absent despite being listed as closed.

### Required judgments

- W4-1 re-fence: substantively correct. `CellAssign` now extends `CellData` with mandatory `child_cover`, and `constFalse_no_cellAssign` makes the constant-false model uninhabited whenever a window-opening reduction exists. This honors the ruling that the interface itself reject the degeneracy.
- Consumer non-vacuity: not re-established. The five full-`CellAssign` consumers have no instantiating toy or concrete canonical witness. This is honestly disclosed through the F1 witness obligation and the `CellData`-only toy fence.
- Toy cover failure: correct. At \(g=(1,0)\),
  \[
  \bar f=X^2+1=(X+1)^2\quad\text{over }\mathbf F_2.
  \]
  Thus \(X+1\) occurs twice, but every `toyChildA none` witness requires `x 0 = 0`, whereas the root cell fixes `x 0 = 1`. No child exists.
- `NsBridgeStmt`: repaired correctly. For \(\mu_{\rm cap}\equiv1\), pricing gives \(p^{Z(M)}=1\); since \(p\ge2\), this forces \(Z(M)=0\), contradicting `Tendsto Z atTop atTop`. Conversely pricing plus growth gives \(\mu_{\rm cap}\to0\), and uniqueness of real limits yields `μclass = 0`.
- Toy γ computation: correct:
  - head: \(1\cdot1+2\cdot1=3\);
  - slope-2 leaf: \(1\cdot2+1\cdot2=4\);
  - slope-3 leaf: \(1\cdot3+1\cdot3=6\).
- Full line pins: correct under the built `Line.at = intercept − slope·x` convention:
  \(3-1\cdot2=1\), \(4-2\cdot1=2\), \(6-3\cdot1=3\).
- Anchored residuals: correct. Heads have
  \(R=X^2+1=(X+1)^2\), hence order 2; leaves have \(R=X+1\), hence order 1. The displayed 22 Node proof fields are all accounted for at the node level.
- G1b: honestly disclosed. The node proof walk does not establish `mem_realizable`; the remaining `IsNodeLift`/`TransitionCoreL`/`TransitionAdmissible`/`IsCanonPres` work is explicitly left as the G1b hand bridge.
- `OmSatTot`: it supplies the previously missing existence direction. Combined with the shared `trackOf`, it closes the recorded constant/degree-\(>n\) witness-free escape. Record 19’s re-attribution is materially right: membership alone never cured implication vacuity.

### CRITICAL findings

1. **Missing `UnramifiedOfDeg` declaration**

   `HenLift` consumes:

   > `Irreducible gh.1 ∧ UnramifiedOfDeg gh.1 ψ.natDegree`

   but no Lean declaration of `UnramifiedOfDeg` is displayed. A comment saying

   > ``UnramifiedOfDeg g d := ramIdx g = 1 ∧ resDeg g = d``

   is not a declaration. The manifest nevertheless lists it as declared in §2.7. This directly violates §8.

2. **`ramIdx`/`resDeg` do not elaborate and do not provide the claimed invariants**

   The displayed form

   > `Ideal.ramificationIdx (algebraMap ...) maximalIdeal maximalIdeal`

   does not match the current Mathlib API, whose ordinary use is an ideal of the extension ring followed by the base ring, e.g. `P.ramificationIdx R` and `P.inertiaDeg R`. [Mathlib’s documentation shows this signature](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RamificationInertia/Basic.html#Ideal.sum_ramification_inertia_eq_finrank_fiber).

   More fundamentally, `ramIdx g` is defined for arbitrary `g`, but `IsLocalRing (AdjoinRoot g)`, the required maximality/domain data, and the relevant finite-extension instances do not exist for arbitrary polynomials. OmSat’s later irreducibility hypothesis cannot supply typeclass instances needed while elaborating this total definition.

3. **Manifested toy identifiers are not Lean declarations**

   Displayed theorems consume `tAν₁`, `tAνa`, `tAνb`, `tBν₁`, `tBνc`, `tBνd`, the six histories, and `toySplitB`. They occur only in prose/comment tables, not structure-literal declarations.

   Likewise `RejectsRootOnlyChildless` is used in displayed Lean but only described afterward in a bracket note. The manifest’s claim that these are declared at T-G1/T-D2 is false.

4. **§2.11 does not elaborate over the built `FreshData.clauses` carrier**

   The blueprint itself says:

   > “`FreshData.clauses` is a LIST”

   but displayed code treats it as a `Finset`, notably:

   > `(J.fresh r).clauses.biUnion (fun cl => cl.support)`

   inside a `Finset.biUnion`, and:

   > `(fd.clauses : Set _)`

   No list-to-finset conversion, duplicate policy, or displayed coercion exists. The `FreshClause := LevelClause` abbreviation does not repair the carrier mismatch.

5. **`IsLumpLocus` omits the literal-zero values**

   Its displayed body constrains only the pin roster:

   > `Z.pinned c = true ↔ c ∈ interiorFreshIdx J M`

   It does not constrain `Z.solve` to zero. Therefore a locus pinning the correct coordinates to nonzero digits satisfies `IsLumpLocus`, yet its `SHZ` is not the zero-digit lump used by `NsLumpFamily.vanish`.

   The comment promising an E-phase “literal-zero VALUE clause” is precisely missing load-bearing statement content. Consequently the T-C5 → T-C6 → T-C7 identification of the priced locus with \(L_M\) is not established.

6. **Full-`CellAssign` closures use an undisplayed parent coercion**

   Several consumers correctly write `CA.toCellData`, but others use the full structure where `CellData` is required:

   > `SibCount T CA χ`

   > `JCmultiAt T CA χ ...`

   in `TreeNStmt` and related closures. `extends CellData` supplies the projection `toCellData`; it does not make the omitted coercion part of the displayed interface. No `Coe CellAssign CellData` instance is declared or manifested. These displayed terms therefore do not elaborate as written.

### GAP findings

1. **No non-vacuity witness for the five full-interface consumers**

   The repair is installed, but no `CellAssign` toy, `TreeExpFin` instance, `TreeNStmt` family, or `VPPinned` family is exhibited. The blueprint discloses this honestly through the F1 E-phase witness obligation.

2. **G1b remains open**

   The node-level 22-field walk is correct, but no actual `toyModel`/`toyModelB` exists until the transition, realizability, and canonical-presentation proofs are constructed. Thus the gates are planned, not yet demonstrated inhabitable.

3. **The `hRes` exactness scope is not supplied by the cited jet fields**

   REV 8 says exactness is restricted to `HistLawful`, then claims presented jets’ `coherent`/`realizable` fields put them on that domain. Elsewhere the blueprint explicitly states that `HistoryCoherent` does not imply `HistLawful` and leaves the implication fenced on Q1. The exactness claim is therefore only owner-postulated, not sourced.

4. **At least one built-path manifest pointer is wrong**

   `emptyFiber` is displayed in the supplied current `MovesD/Defs.lean`, but §8 points it to `MovesD/D11a_multSum.lean:62-note`. A reference in a note is not the source declaration required by the manifest rule.

### Closure spot-check

At least fifteen supplied built references are consistent with the excerpts: `Box`, `topLocus`, `ShapeRead`, `ShapePrefix`, `ShapeWF`, `Shape`, `CanonPolicy`, `PrefSet`, `PrefIdx`, `reprOf`, `Presented.event`, `Presented.mult`, `History.snoc`, `TreeModel`, `D4R_CYL`, `ClassFiberWelldef`, `Node`, `HistoryCoherent`, `JetSetup`, `C4_conditionalMass`, `C6_thmC_b`, `LedgerIV`, `RS1Meas`, and `HC2.ReadsOf`.

That does not save §8: a single unresolved displayed identifier is a shipping blocker, and several exist here.

The local grep runner itself failed before execution because its sandbox helper `bwrap` is unavailable. The path checks above therefore use the supplied current-source excerpts; the Mathlib API finding was independently checked against official documentation.