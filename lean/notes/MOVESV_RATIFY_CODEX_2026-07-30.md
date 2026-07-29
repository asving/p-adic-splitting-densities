# MovesV AS-BUILT RATIFICATION (Codex, 2026-07-30): REJECT 3N/6M — M1 SOUNDNESS: the sorried writeHeights_total_unscoped + its compiled negation = derivable False, consumed unquarantined (STOP-THE-LINE repair launched); M4 vacuous seam units (the OR-True escape hatch, PUnit states, zero tables); M3 SolveCond reduced to True + the muhatN circularity question; M2 the VAL(b)/Tgam bridge (adjudication: the note conditionality); M5 the scoping erasure (= M1 root); M6 the census scope. RATIFIED LOCALLY: XHDd/Tgam keying, the HMC toys, marked events, the table algebra, StepSys non-vacuity. NEW FENCE RULE: a sorried statement whose negation is proved in-tree is an INCONSISTENCY GENERATOR — delete or quarantine, never ship.

I’ll audit the actual `MovesV` tree rather than relying only on the pasted snapshot. I’ll trace each requested statement family to its theorem and hypotheses, check the two `sorry` sites and axiom propagation, and specifically test whether any theorem closes `HMC` at universal scope.

The first pass has surfaced two high-risk seams I’m checking directly: whether `Tgam` really is the note’s fresh-chain count, and whether the disclosed order-0 shim can derive `False` together with its checked counterexample. Both affect the global verdict, not just local proof coverage.

# Verdict: REJECT (3N/6M)

The local mathematics contains substantial clean work, but the as-built statement surface is not faithful to §V-TABLES in both directions. Several conclusions are weaker than the note, while several proofs assume stronger—sometimes essentially concluding—hypotheses.

Here `M` means material to ratification; `N` means narrow or governance-local.

## Material findings

### M1 — The order-0 shim makes the combined corpus inconsistent

[V3_spwordD.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V3_spwordD.lean) asserts with `sorry`:

> `writeHeights_total_unscoped ... : (writeHeights? εT h).isSome`

The checked counterexample in `V3_spword_negWitness2.lean` asserts:

> `WHNeg.writeHeights_total_false : ¬ (writeHeights? WHNeg.T0 WHNeg.h0).isSome`

Together they produce `False` directly:

```lean
WHNeg.writeHeights_total_false
  (writeHeights_total_unscoped WHNeg.T0 WHNeg.h0)
```

Consequently, although no ordinary named theorem constructs universal HMC, the combined environment can prove any `HMC TE D` by `False.elim`. Therefore the charged statement “HMC is open and nothing closes it” is true only at the intended declaration graph, not in the logical theory containing every MovesV file.

This shim is also consumed by `ctsm`’s aggregate proof and `ledgerIV_comp_once`; it is not quarantined from the ratified capstone.

There are actually two sorry-bearing declarations in this order-0 family—`template_total` and `writeHeights_total_unscoped`—plus the banked W17ii sorry.

Classification: **M — rejection-forcing.**

### M2 — VAL(b) is not connected to the direct `Tgam` count

The XHDd keying itself is good:

> `no_orphan ... 0 < Tgam TE γ x h → (dom γ).Mem h`  
> `no_stray ... (dom γ).Mem h → ... 0 < Tgam TE γ x h`

and `tgam_eq_chains` identifies `Tgam` with a realized-chain subtype count. This faithfully avoids using a merely shape-level product as the domain key.

But [V2_valB.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V2_valB.lean) proves:

> `chainCount S γ x h = (pathProdPoly V γ).eval q₀`

It does not prove the note’s required identification:

```text
actual linked count Tγ(x,h) = ∏ Tᵢ
```

There is no bridge `Tgam = chainCount`. Indeed the checked coupling toy deliberately supplies a point with:

> `0 < chainCount ... ∧ Tgam ... = 0`

That is useful for refuting HMC/product assumptions, but it also shows the stated `valB` theorem is not VAL(b) as formulated in the note. The capstone field `val_b_chain` inherits this mismatch.

Classification: **M — XHDd passes locally; VAL(b) fails faithfulness.**

### M3 — COMP-h is assumed through `CompCarrier`, not derived from the note’s hypotheses

`CompCarrier.μhatN_law` already contains the essential conclusion:

> `μhatN ... = ιN ... * pathProdPoly.eval ... * gProd ...`

The subsequent `comp_h` producer obtains the result from that field. Thus the displayed inputs `C15Pack`, `XHDw`, `XHDu`, domain membership, and mark tie do not derive the multiplication law; the law arrives as carrier data.

This introduces an extra hypothesis stronger than the note’s ledger. It is effectively the desired COMP-h identity at finite level.

There is also a conclusion weakening:

> `CompSigma_Stmt` is only  
> `ι · pathProd · gcVal = ι · stepProdVal`

It does not state the note’s marked-event series identity

```text
Σₕ μ̂(ε,γ,h) = ι · ∏(T·G).
```

`comp_hsum` supplies a separate `HasSum`, but the capstone does not assemble that series with `comp_sigma`. Likewise `aggMass` is an algebraically defined aggregate rather than an exposed sum of the marked-event carrier.

`SolveCond_Stmt` is more severely weakened:

```lean
ActiveValueAgree ... → HMC ... → EntCount ... → ... → True
```

and is discharged by `trivial`; it proves none of the note’s Neumann-series, determinant, or rational-solve conclusion.

Classification: **M — circular strengthening of premises and weakening of conclusions.**

### M4 — The MovesS seam is vacuous and loses CTS cells

[V7_ts.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V7_ts.lean) defines the seam state as essentially:

> `Σ s : Skeleton n, PUnit`

rather than the note’s `(s, α)` with `α : CellIdx`. It also installs `Wloc = 0` and `Wstate = 0`, rather than transporting the CTS bounds.

The measured-side constructors in [V7_msA.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V7_msA.lean) and [V7_msC.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V7_msC.lean) use empty cells, zero events, zero masses, or Kronecker-only `kstep`. They do not instantiate the CTS measured system constructed earlier.

Three assembly statements are propositionally vacuous:

```lean
Nonempty (MovesS.LedgerIV T M) ∨ True
Nonempty (MovesS.RatBurdens T M) ∨ True
Nonempty (MovesS.SCSData T) ∨ True
```

and are proved with `Or.inr trivial`.

This fails the requested non-vacuity and both-direction faithfulness. It also means the table/count work is not connected to the downstream object claimed by the note.

Classification: **M — rejection-forcing.**

### M5 — Entrance reconstruction is only locally scoped, then unsafely unscoped

The sound reconstruction results require restrictive premises such as:

- one-letter/non-self-loop shape,
- `AnchorAdmissible`,
- `SpeciesCoherent`,
- `SpWordPinned`,
- self-loop-free word.

Those are reasonable refutation-driven conditional lemmas. They are not, however, the note’s general template/instantiation bijection over every entrance template.

The specific theorem `writeHeights_total` is much narrower than “all self-loop-free shallow templates”: it is essentially the one-letter case. The bijection results remain conditional on additional pinning hypotheses not present in CTS-M’s perimeter.

That would be an honest incomplete formalization if the scopes remained visible. Instead, the false `writeHeights_total_unscoped` wrapper erases them and is used by aggregate consumers.

Classification: **M — locally faithful conditionality, globally over-scoped and unsound.**

### M6 — The sealed census claims are only partially represented

The local algebra is valuable:

- all five root-table polynomials and the sum identity are proved;
- the A2 chart and affine-weight identity are proved;
- the block-2 polynomial partition is proved;
- gate-B dyadic arithmetic is proved.

But the theorem-level census is materially weaker than the note’s “178 exact checks”:

- `rootTable_census` checks only three profiles, not all five root rows;
- `blk2_census` concludes a disjunction and does not separately establish all split/inert/double counts;
- `gateB_mass` and `gateB_shadow_check` are arithmetic identities, not an exhaustive enumeration of `f mod 2^N`;
- `gateB_threshold` restates the supplied `CoprimeLiftPack` specification rather than proving the complete level-3 event-determinacy/census claim;
- no full gate `ValA`/`CtsFamily` instance connects these toy results to CTS-M.

Thus the toys support selected formulas, but do not kernel-ratify the note’s reported gate.

Classification: **M — evidence formalized, sealed-gate claim not formalized.**

## Narrow findings

### N1 — PART-2 needs an extra `hmark` hypothesis

`ctsm` takes:

> `c.isLeft → 1 ≤ markWeight L.V c`

The refutation documenting why arbitrary `emult = 0` breaks the algebra is sound. Semantically, however, the note’s continuing marks already have positive multiplicity. The formalization has exposed a missing structure invariant as a new capstone hypothesis rather than deriving it from the marked-cell construction.

Classification: **N — faithful repair idea, perimeter enlargement.**

### N2 — `MarkFiberTie` is an additional open burden

The marked carrier itself is well typed:

- `mEvt` tags boxes by the mark coordinate;
- distinct marked readings are disjoint;
- `EqualProjInstance` correctly demonstrates equal ordinary projections with distinct marks.

Those match the note’s marked-space law. But `MarkFiberTie` is separately assumed and then consumed by composition. It is not one of the note’s named hypotheses and should either be derived from the D4R finite-level carrier or recorded in the acceptance perimeter.

Classification: **N — marked typing ratified; census tie needs explicit ownership.**

### N3 — W17ii is correctly disclosed but cannot be part of a full ratification

[V7_w17ii.lean](/tmp/leanratify_v/lean/LeanUrat/MovesV/V7_w17ii.lean) cleanly separates:

- clause (i), proved from `wsh_ok/wsh_interp`;
- clause (ii), the banked `[3t]` shallow-height sum, left as `sorry`.

This is well governed and does not masquerade as a proof. Nevertheless, “every MovesV file” cannot receive an unconditional ratification while `w17ii_pin` depends on it.

Classification: **N — transparent, deliberately banked exclusion.**

## What does ratify locally

The following statement families are faithful in isolation:

- `StepSys` has genuine pool, history, ZC, and outgoing non-vacuity fields.
- HMC is absent from `CtsmLedger` and remains an explicit antecedent of `comp_sigma`/`comp_agg`.
- The positive and negative HMC toys show that the proposition is neither structurally tautological nor definitionally false.
- `XHDd` is keyed to `Tgam`, not the formal path product.
- The disjoint semilinear-component convention is represented in `SemilinPart`.
- Marked events are tagged and disjoint in marked space, without claiming ordinary-projection disjointness.
- The local table polynomial identities, degree bounds, A2 chart, geometric sum witness, and gate arithmetic are substantive kernel proofs.
- VAL(a)’s abstract statement carries direct table-count and cell-count semantics, although no full table-build instance discharges it.

These successes do not repair the capstone/seam failures above.

The decisive rejection grounds are the contradictory unscoped shim, VAL(b)’s missing `Tgam` bridge, assumed composition identity, vacuous MovesS assembly, and weakened solve/gate conclusions.

Execution caveat: I could not perform a fresh Lean rebuild because the provided command sandbox failed before execution with a missing `bubblewrap` launcher. The verdict is therefore a statement-and-dependency audit of the supplied as-built sources, not a new compilation result.