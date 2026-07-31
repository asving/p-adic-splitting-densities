# M09-cl11-general — problem brief (neutral, self-contained)

## One-line statement

Prove, for every n ≥ 1, the "equal-degree continuation is (m = 1, c = 1)"
classification law for the abstract classifier table carried by the
formalization's hypothesis ledger — or exhibit the obstruction that makes it
fail / makes it depend on data not carried by the ledger.

## Background: what the table is

The corpus formalizes a uniformity theorem: for each degree n and each
splitting type σ (a multiset of pairs (e, f) with Σ e·f = n), the density of
monic degree-n polynomials over ℤ_p whose factorization over ℚ_p has type σ is
given by ONE rational function R_σ(q) evaluated at q = p, for all primes p
simultaneously. The engine is an Okutsu–Montes / MacLane-style classifier: a
polynomial is resolved block by block, where a partially-resolved block of
degree e sits in some classifier *state*, and each further Newton-polygon /
residual-factorization event is an *outcome* that splits the block into
sub-blocks ("members"), each member either *halting* with a final verdict (an
(e, f) pair recording ramification and residue degree of a finished factor) or
*continuing* into a new state of the member's own degree.

The Lean corpus abstracts this into a data structure `TableShape n` ("the
table", "the roster"). The fields relevant here (Lean file
`lean/LeanUrat/MovesS/Defs.lean`), translated:

- `State e` — for each block degree e, a finite type of classifier states.
- `VType` — a finite type of verdict letters, structurally pinned to be
  exactly the pairs (e, f) ∈ ℤ≥1 × ℤ≥1 with e·f ≤ n (via an equivalence
  `vEquiv`), with degree function `vdeg (e, f) = e·f`.
- `Out e τ` — for each state τ at degree e, a finite type of outcomes.
- `odata e τ o` — the outcome's data: a nonempty finite list `mem` of
  *members*. A member μ has
  - `μ.size ∈ ℕ` — the degree of the sub-block it spawns,
  - `μ.δ ∈ ℤ≥1` — a base-change factor (irrelevant here),
  - `μ.status` — either a verdict letter in `VType` (the member halts) or a
    state in `State (μ.size)` (the member continues).

Derived quantities, for an outcome o with member list `mem`:

- m(o) := length of `mem` (number of members);
- c(o) := number of members whose status is a continuation
  (so 0 ≤ c(o) ≤ m(o)).

The outcomes are routed by (m, c): c = 0 is a terminal row; c ≠ 0 with m = 1
is a "kernel column" row (the block continues whole — these rows populate the
transition matrix K_e of the resolvent linear system); c ≠ 0 with m ≥ 2 is a
"split" row. The source proof note displays the law in question as: "equal-e
continuation rides EXCLUSIVELY in K_e's (c = 1, m = 1) rows."

## The precise obligation

Lean statement (`lean/LeanUrat/MovesU/DefsCarriers.lean`):

```lean
def KsubM1C1T {n : ℕ} (T : MovesS.TableShape n) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    (∀ μ ∈ (T.odata e τ o).mem, μ.size = e) → (T.odata e τ o).c ≠ 0 →
    (T.odata e τ o).m = 1 ∧ (T.odata e τ o).c = 1
```

In standard language:

> **(K-SUB, m = 1 classification).** For every block degree e with
> 1 ≤ e ≤ n, every state τ at degree e, and every outcome o of τ: if every
> member of o has size exactly e, and o has at least one continuing member,
> then o has exactly one member and exactly one continuing member.

The obligation (ledger row `cl11_ksub`) is this Prop instantiated at the table
`C.T` of a *carrier pack* `C`, inside two hypothesis-ledger structures
(`CapstoneLedger` in `lean/LeanUrat/MovesU/DefsLedger.lean:794`,
`BridgeKernels` in `lean/LeanUrat/MovesU/BridgeKernels.lean:263`), both of the
form

```lean
  cl11_ksub : KsubM1C1T C.T
```

where `C : UCarriers n` is a parameter of the surrounding structure.

## The ambient hypothesis surface (what a proof may use)

`UCarriers n` (`lean/LeanUrat/MovesU/DefsCarriers.lean:81`) bundles:

```lean
structure UCarriers (n : ℕ) where
  T : MovesS.TableShape n
  MS : MovesS.MeasuredSide T
  RB : MovesS.RatBurdens T MS
  hdc : MovesS.DegCons T
  hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e
  Fam : MovesS.ShapeFam T
  chain : MovesS.RS4Chain T MS RB hdc hK Fam
```

Field glosses:

- `MS` (measured side): the p-adic counting carrier — residue-box event
  spaces, cell masses, transition-mass functions. Analytic data over T.
- `RB` (rationality burdens): the rational-function tables in ℚ(q)
  interpolating the measured masses. Analytic data over T.
- `Fam`, `chain`: a finite family of resolution shapes and the resummation
  chain (the measured linear-system package). Analytic data over T.
- `hdc : DegCons T` — a pure roster constraint, stated
  (`lean/LeanUrat/MovesS/Defs.lean:139`):

```lean
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e (τ : T.State e) (o : T.Out e τ),
    ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e
```

  In words (the note's "DEG-CONS", CL-11's degree law): every member of every
  outcome has size ≥ 1, and for 1 ≤ e ≤ n the member sizes of any outcome at
  a degree-e state sum to at most e. (Semantics: a factorization event of a
  degree-e block produces factors whose degrees total at most e.)

- `hK : … KmatHyp T e` — a second pure roster constraint
  (`lean/LeanUrat/MovesS/Defs.lean:502`):

```lean
abbrev KmatHyp (T : TableShape n) (e : ℕ) : Prop :=
  ∀ (τ : T.State e) (o : T.Out e τ), routeOf (T.odata e τ o) = .kcol →
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e
```

  where `routeOf o = .kcol` means c(o) ≠ 0 and m(o) = 1. In words: in any
  single-member continuing outcome, the member has size exactly e.

A proof of the row may use any of these fields (they are in scope wherever
the row is stated); alternatively an obstruction analysis should identify
which additional table property would be needed and exhibit a table
satisfying all pack constraints but violating `KsubM1C1T`.

## What is already proved in the corpus

- **n = 2 instance** (`lean/LeanUrat/MovesU/SynK1_ksubN2.lean`):
  `ksubM1C1T_n2 : KsubM1C1T n2T` — a finite roster walk over the concrete
  n = 2 table `n2T` (three outcomes at the degree-2 layer: the kernel row has
  (m, c) = (1, 1) by evaluation; the split row's members have size 1,
  refuting the all-size-2 guard; the inert row has c = 0). Lean-core
  footprint.
- **DEG-CONS at n = 2** (`lean/LeanUrat/MovesS/N2DegScs.lean`,
  `n2_degcons_scs`): the concrete n = 2 table satisfies `DegCons`.
- **Well-formedness face** (`lean/LeanUrat/MovesU/DefsCarriers.lean`,
  `menuWFT_holds`): for EVERY table T and every outcome, m ≥ 1, c ≤ m, and
  c ≠ 0 implies some member is continuing — proved structurally for all n
  (m ≥ 1 is the nonemptiness of `mem`; c ≤ m is the filter-length bound).
  This discharged the neighboring ledger row `cl13_wf` outright.
- **DegCons production at general tables** (`lean/LeanUrat/MovesV/V2_degcons.lean`,
  `V7_tsGate.lean`): the MovesV gate derives `MovesS.DegCons T` for tables
  arising from the tree-solve construction.

Note `KsubM1C1T` is NOT true of an arbitrary `TableShape n`: nothing in
`TableShape` alone prevents an outcome with two continuing members both of
size e. The question is precisely whether the carried pack constraints pin it
down at every n, or whether it is genuinely new instance information (as the
n = 2 roster walk treated it).

## What a proof must deliver

Either

1. a proof of `KsubM1C1T C.T` for all n ≥ 1 from the fields of an arbitrary
   `C : UCarriers n` (this discharges the ledger row at every n), stating
   exactly which fields are consumed; or
2. a proof for the intended real table at each n by other means, with the
   construction of that table made precise; or
3. an obstruction: a table (or pack) satisfying all carried constraints but
   violating `KsubM1C1T`, together with an analysis of what additional
   hypothesis the ledger would need to carry.

Statements must be faithful to the quoted Lean forms (the Lean statement is
normative); any proposed weakening or strengthening must be flagged as a
statement-change event.
