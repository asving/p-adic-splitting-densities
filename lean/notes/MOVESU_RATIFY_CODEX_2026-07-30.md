# MovesU AS-BUILT RATIFICATION (Codex, 2026-07-30): REJECT 7/2 — the CL ledger is bare Props (instance-selectable); finiteness_stack/solve_stack ASSUME the operative identities (a semantic shortcut through the ledger); (REG-p) roster instance-chosen; the Z_p bridge absent (trueType arbitrary); theoremU conclusion omits the (U-n) bracket + the active-value clause. ADJUDICATION: all findings ACCEPTED — this is the INSTANTIATION PHASE charge, now executable against the built wave-3/4 corpora. The faithful-portions list (SplittingType/Box/boxN/un_bracket/squeeze_limit) stands.

I’m auditing this strictly as statement semantics: quantifier order, whether each hypothesis type itself encodes the named obligation, the exposed conclusion, and the exact `(REG-p)` gate. I’ll treat comments and intended future instantiations as non-binding.

REJECT (7 CRITICAL / 2 GAP)

The Lean proofs may be complete, but the statements do not faithfully encode the conditional Theorem U in the note.

### CRITICAL 1 — The capstone obligations are bare, freely instantiable `Prop` tags

Quote:

```lean
structure KernelStatements where
  escapeE0 : Prop
  weightCharge : Prop
  progressX2 : Prop
  ...
  rs1Assembly : Prop
  jRat : Prop
  jcInv : Prop
```

These types encode none of the mathematical content of CL-1…CL-19. An instance may set every field to `True`. The comment admitting that doing so is an “instantiation-fidelity violation” does not repair the theorem statement: Lean checks types, not comments or future owner audits.

Consequently fields such as

```lean
cl1 : K.escapeE0
cl2 : K.weightCharge
...
cl19 : K.jcInv
```

do not pin per-pool escape, progress constants, relative measures, sibling laws, rational tables, or joint invariance. This directly violates the requested non-vacuity criterion.

### CRITICAL 2 — The operative mathematical conclusions are assumed directly

Quote:

```lean
finiteness_stack : ∀ σ N,
  (X.decided σ N : ℝ≥0∞) =
    (p : ℝ≥0∞) ^ (n * N) *
      ∑ T ∈ F.thrSlice σ N, F.mass σ T
```

and

```lean
solve_stack : RegP S D → ∀ σ,
  F.seriesSum σ ≠ ⊤ ∧
  F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
  0 ≤ evalℝ S σ p
```

These are essentially the precise intermediary conclusions needed for SQ.2. The bare CL fields have no typed connection to them. Thus the corpus proves the squeeze from an assumed fiber-count identity and an assumed solve identification, rather than from typed versions of TRACK-COUNT, TREE-N, E0, REL.3, RS.1-SH, and the other ledger obligations.

This is a semantic shortcut through the capstone ledger.

### CRITICAL 3 — `SolveData`, `FiberSeries`, and the classifier are not pinned to the note’s objects

Quotes:

```lean
structure SolveData (n : ℕ) where
  R : SplittingType n → RatFunc ℚ
```

```lean
structure FiberSeries ... where
  Tree : SplittingType n → Type
  mass : ∀ σ, Tree σ → ℝ≥0∞
  thr : ∀ σ, Tree σ → ℕ
```

```lean
canonical : ∀ N, Box p n N → Option (SplittingType n)
trueType : ∀ N, Box p n N → Option (SplittingType n)
```

Nothing in their types says:

- `S.R` is the Cramer/adjugate solution of `(R_e)`;
- `F.Tree σ` consists of complete finite realizable canonical trees;
- `F.mass` is Haar mass of the corresponding canonical fibers;
- `canonical` is the note’s \(T_{\rm can}^{\tau}\);
- `trueType` is actual factorization type over \(\mathbb Z_p\).

The aggregate `finiteness_stack` and `solve_stack` equalities constrain some resulting numbers, but do not pin these objects to the note’s constructions.

### CRITICAL 4 — `(REG-p)` quantifies over an instance-chosen surrogate roster

The note requires the actual pools, blocks, matrix rows, cells, shallow shapes, and β-entries consumed by the fixed solve. Lean instead permits the instance to choose all of them:

```lean
depthSet : Finset ℕ
Block : Type
bidx : Block → Type
JIdx : Block → Type
WIdx : Type
legIdx : Block → Type
```

There is no typed relationship between `RegData` and `SolveData.R`, the real block system, or the actual RS.1-SH assembly.

Moreover, despite the comment claiming that every index family is nonempty-pinned, only `Block` and `bidx e` are nonempty. These may all be empty:

```lean
cellCount : Block → ℕ
JIdx_card : Fintype.card (JIdx e) = cellCount e

shapeCount : ℕ
WIdx_card : Fintype.card WIdx = shapeCount

legCount : Block → ℕ
legIdx_card : Fintype.card (legIdx e) = legCount e
```

Taking these counts as zero removes every J, \(W_{\widehat S}\), or β obligation from `entryList`. Even the counts themselves are freely chosen, rather than equated to an independently typed table or assembly roster.

Thus `(r1)` and `(r2)` have the right surface syntax but not the note’s quantification domain.

### CRITICAL 5 — The regularity gate is strengthened in one place and incomplete in another

Lean defines:

```lean
def RegP ... :=
  (∀ q₀ ∈ D.Pool, ∀ e, ...) ∧
  (∀ σ, DefinedAt (S.R σ) (p : ℚ))
```

The displayed note says `(REG-p) holds iff` the pool/block conditions `(r1)` and `(r2)` hold. Definedness and active agreement of \(R_\sigma(p)\) are stated as consequences of that schema, not as an additional independent clause. Lean adds `DefinedAt (S.R σ) p` because it lacks the typed assembly relations needed to derive it. That is a silent strengthening of `(REG-p)`.

Conversely, Lean does not require active-value agreement for `S.R σ`:

```lean
DefinedAt (S.R σ) (p : ℚ)
```

There is no equation saying its literal evaluation is its ACT active value, although SQ.4 explicitly says both readings coincide under `(REG-p)`.

For the determinant, the added `DefinedAt` is effectively redundant with a nonzero field evaluation; that part is not the central defect.

### CRITICAL 6 — `theoremU` does not expose the two-sided `(U-n)` bracket

Its conclusion contains only:

```lean
Tendsto (X.dmass σ) atTop (𝓝 ...)
```

plus the true-type limit and `env → 0`.

The finite-level statement

```lean
(evalℝ S σ p - X.env N) * p ^ (n * N)
  ≤ X.decided σ N
∧ X.decided σ N
  ≤ evalℝ S σ p * p ^ (n * N)
```

exists separately as `un_bracket`, and is used internally in the proof, but it is not a conjunct of `theoremU`.

Therefore `theoremU`’s conclusion is not the requested “two-sided bracket + env→0 forcing the identity” display exactly. A proof may use a stronger intermediate fact without the theorem statement exposing that fact.

### CRITICAL 7 — “Splitting density over \(\mathbb Z_p\)” is not stated

The alleged identification conclusion is:

```lean
Tendsto ((inst p hp).X.trueDmass σ) atTop
  (𝓝 (evalℝ ⟨R⟩ σ p))
```

But `trueDmass` counts values of the arbitrary function:

```lean
trueType : ∀ N, Box p n N → Option (SplittingType n)
```

`VPSound` only says:

```lean
canonical N f = some σ → trueType N f = some σ
```

There is no \(\mathbb Z_p\) object, lift, actual factorization predicate, Haar-measure statement, or HC-2 bridge in the theorem’s types. Hence clause (ii) proves equality with an instance-chosen label density, not the note’s splitting density.

### GAP 1 — Several local theorems carry silently enlarged hypothesis slices

For example, `sq2_partial` only states the finite partial-sum identity, but requires `FinStack`, which includes:

```lean
cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN
cl10_vpsound : VPSound X
```

VP-SOUND and the full CL-10 package are not hypotheses of the local partial-sum statement itself. They belong to the eventual full `(U-n)` ledger. This makes the standalone theorem stronger in hypotheses than its quoted note claim.

### GAP 2 — The existential `R` is not propositionally identified as the solve output

The theorem states:

```lean
∃ R : SplittingType n → RatFunc ℚ, ...
```

while `(REG-p)` remains expressed using the separate input `S`:

```lean
RegP S (inst p hp).D
```

The proof happens to choose `R := S.R`, but the conclusion contains neither `R = S.R` nor a typed statement that `R` is the Cramer/RS.1-SH solution. The witness choice in the proof does not make that characterization part of the exported proposition.

### Faithful portions

The following pieces match their limited arithmetic or vocabulary roles:

- `SplittingType n` correctly encodes a multiset of positive pairs with \(\sum ef=n\).
- `Box p n N` and `boxCard` encode the monic coefficient box and \(p^{nN}\) cardinality.
- `boxN` is the exact Option-fiber count identity.
- `tonelli_partial_le` states only extended-value partial-sum domination.
- `sq3_arith` faithfully isolates the tag-free checksum arithmetic.
- `squeeze_limit` faithfully expresses the tag-free limit forcing.
- `un_bracket`, viewed only as an implication from its supplied assumptions, has the correct two inequalities and is guarded by `p.Prime` and `RegP`.

Those correct derived units cannot cure the defective types of their assumptions or the missing bracket in the capstone conclusion.

**Verdict: REJECT.** The decisive failures are the bare `Prop` ledger, instance-selectable solve/regularity rosters, absent \(\mathbb Z_p\)-factorization bridge, and omission of `(U-n)` from `theoremU`’s exported conclusion.