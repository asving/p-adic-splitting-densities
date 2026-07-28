# MovesS RATIFICATION — Codex verdict (deferred final, 2026-07-28)
# Charge: as-built statement ratification vs §S-RESUM 11557-12577 + re-judging the three adjudicated items
# RE-JUDGMENT OUTCOME: adjudication (a) junk-block UPHELD, (c) J-RAT un-builtness UPHELD (type demanded), (b) consumed-legs re-raised sharper (halted members). ORCHESTRATOR: ALL FIVE findings ACCEPTED. Repair charge: /tmp/ratrepair_s_charge.md (executed this session).

I’ll audit the declarations as typed—not their proof bodies—and separately re-run the three adjudicated scope questions against the cited note text. I’ll treat the seven `sorry` seams only as contracts, as requested, and will report only semantic statement defects or vacuous hypothesis packaging.

I find five statement-level critical defects. The algebraic helper lemmas, routing, boundary convention, triangular solve, active-matrix linear algebra, rational-function evaluation, and the explicit \(n=2\) device are otherwise faithful at the level claimed.

1. CRITICAL — relevant wild-pool active-value agreement is not packaged

Note display:

> “At every NON-all-active pool \(q₀\) … CTS-M(ii-c)’s ACTIVE-VALUE AGREEMENT burden … PER POOL”
>
> “a \(\beta_{e_j,\tau_j}(p^{\delta_j})\) leg at \(\delta>1\) … equals the active-subsystem solve there must pass BEFORE it may be read off”

Lean instead restricts the reusable read-off package to all-active pools:

```lean
structure ReadOffBundle ...
    (S : Set ℚ) (hS : S ⊆ allActivePools M) ...
```

The relevant-leg field supplies only `PoolHyp`:

```lean
legs_reg : ∀ p : ℕ, (p : ℚ) ∈ PrimePools → RegP T M RB p hK F
```

with:

```lean
def RegP ... : Prop :=
  ∀ e ... ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp ... ((p : ℚ) ^ (δ : ℕ)))
```

`PoolHyp` contains E0, activity, inactive-column vanishing, and evaluated active entries, but no `AVAgree` for the consumed symbolic β-coordinate. Consequently, a base-changed wild leg can be used by `bSplitMeas`/`Rsh` without the note-required prior active-subsystem read-off check. Outer `rsh_interp` may even hide an ill-defined intermediate leg by cancellation.

The absence of a junk-block determinant hypothesis is not itself a defect: the note says those determinants are recorded, and that zero is not a failure. The critical mismatch is that the accompanying per-pool active-value gate is not inherited at the relevant non-all-active pools.

2. CRITICAL — `consumedDeltas` includes unconsumed halted legs

Note display:

> “δ ranging over 1 AND every base-change index a β… leg of \(b_e^{split}\) or RS.1-SH consumes”

and, for halted members:

> “τ-halted members contribute FACTOR 1 … β is evaluated only at block-state members”

Lean collects δ from every member of every split outcome:

```lean
if routeOf (T.odata e τ o) = .split
then ((T.odata e τ o).mem.map Member.δ).toFinset else ∅
```

Thus halted members—whose factor is exactly `1` and which consume no β evaluation—enlarge `consumedDeltas`. `RegP` then demands E0/ACT packages at extra pools not required by §S-RESUM. This is a silent strengthening.

The multiplicative interpretation of nested continuing legs is otherwise correct: `nested_delta_mem` and `powSubst_mul` properly use products of absolute δ-indices.

3. CRITICAL — the J-RAT contract has the wrong granularity

PLAN-SYNC note display:

> “(J-RAT) — owner [1v], deliverable the PER-CELL rational tables (per branching digit cell of each outcome class \(o\) at each state \(\tau\): the cell-count polynomial …)”
>
> “a deliverable BEYOND PART-1’s TOTAL cell-partition mass”

Lean provides only one presentation per outcome:

```lean
jP : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
```

and only aggregate interpolation:

```lean
j_interp : ...
  routeOf (T.odata e τ o) = .split →
  ... = M.rowVal e τ o q₀
```

There is no `M.Cell e τ` argument, no per-cell presentation, and no field relating presentations to individual cell fibers before summation.

Leaving the proof and actual tables to owner `[1v]` is consistent with the note. Leaving their required type absent is not. The current contract records only an aggregate \(J_{\tau,o}\), so the “each cell once” presentation cannot be audited or supplied through this interface.

4. CRITICAL — CL-17(ii) is represented by a vacuous proposition

Note display:

> “CL-17 duty (ii) — that every \(W_{\hat S}\) is PRODUCED by the stated rational machinery … remains OPEN here”

Lean packages this as:

```lean
wsh17_pin : Prop
```

and the checksum theorem takes:

```lean
(C : RS4Chain ...) (h17 : C.wsh17_pin) ...
```

but `h17` is unused in `rs4_rational_step`.

An instance may set `wsh17_pin := True`; nothing connects it to `WshP`, `shDom`, `shWeightH`, the height sum, counts, or shallow events. This is precisely a degenerate satisfiable hypothesis package, not a typed CL-17(ii) contract.

The specialized `n2Wsh17Device` is substantive, but it does not repair the generic `RS4Chain` type consumed by the theorem.

5. CRITICAL — `(iv)-POLY` count semantics are not typed

Note display:

> “T is one polynomial … and each cell size one polynomial … valued correctly at every prime power”
>
> “CTS-M(iv)-POLY (CL-6, with V.2’s EXPONENT-MAP AUDIT)”

`PolyGeom` stores two arbitrary bounded polynomials:

```lean
structure PolyGeom where
  countT : Polynomial ℚ
  ...
  countS : Polynomial ℚ
  ...
  geom : Qq
```

For TG, the only semantic connection is the value of their product:

```lean
tg_interp : ...
  ((evalAt ... (tgP ...).val : ℚ) : ℝ) = M.rowVal ...
```

There are no fields saying `countT` evaluates to the T-table count or `countS` to the cell/state count. One can take both count polynomials to be `1` and absorb the entire row mass into `geom`, while satisfying the displayed degree bounds and interpolation. Therefore the typed burden is materially weaker than CL-6 and cannot express the exponent-map/count-table audit.

Other re-examination results:

- The boundary ownership (`bdy_edge`, `bdy_node_shadow`, `bdy_mass_split`) matches the entering-read convention.
- `(m,c)` routing, multi-member terminal verdicts, halted-factor-one semantics, and strict smaller-block recursion match the note.
- Empty active blocks are intentionally allowed by the note’s “realized states only” scope; their vacuous E0 and determinant \(1\) are not defects.
- The \(n=2\) construction is honestly typed as a consistency device rather than evidence for the general owner-side tables.
- The deferred `sorry` declarations were not penalized for openness; the findings above concern their surrounding contract types.

Counts: 5 critical, 0 gaps.

REJECT (5 crit / 0 gap)