# E8 BLOCK CHARGE + Codex adversarial verdict (2026-07-29)

The charge handed to Codex (fresh context, quote-and-classify), followed by the full verdict.

---

# Adversarial verification charge: is `treeExp` (T-E8) provable as stated?

You are a fresh-context adversarial verifier. Quote each offending passage and classify:
CRITICAL ERROR (breaks the chain) vs JUSTIFICATION GAP. Fix nothing. Then give a verdict
on each of CLAIM A / B / C below. All definitions below are verbatim from a Lean 4 corpus
(mathlib types; `Box p m := Fin m → ZMod p`; `History p F` = nonempty lists of `Node`s with
root-species-iff-index-0; `H.IsPrefixOf H'` = list prefix; `TreeModel.mem : Option History → Box → Prop`
with laws `mem_single` (one-node histories ↔ `T.child none ν`), `mem_snoc`-style child laws,
and monotonicity `mem_of_prefix` is PROVED in the corpus).

## The target theorem (statement fenced; currently `sorry`)

```lean
theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (hsib : SibCount T CA χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H hH.1 h2))
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m
```

Note the exponent sums `L.siteExp H` over ALL chains H of the tree (each chain = one "site").

## Key definitions (verbatim)

```lean
def stateEvent (T) (o : Option (History p F)) : Set (Box p m) := {x | T.mem o x}

def entEvent (T) (χ) : EntSt p F n → Set (Box p m)
  | .amb => Set.univ
  | .red g _ => rootCell χ g            -- rootCell χ g = {x | ∀ b, x (χ b) = g b}
  | .st H => stateEvent T (some H)

def cellEventE (T) (CA) (χ) (es : EntSt p F n) (c : CA.Cell) : Set (Box p m) :=
  {x | x ∈ entEvent T χ es ∧ CA.cellOf es x = c}     -- cellOf : EntSt → Box → Cell (a FUNCTION)

structure SiteLedger (Tr T CA χ) where
  sys : History p F → Locus p m × FreshData p m
  cellAt : History p F → CA.Cell
  parentSt : History p F → EntSt p F n
  hparent : ∀ H ∈ Tr.chains, match parentSt H with
    | .amb => False
    | .red _ _ => H.nodes.length = 1
    | .st H' => H'.IsPrefixOf H ∧ H'.nodes.length + 1 = H.nodes.length ∧ H' ∈ Tr.chains
  presents : ∀ H ∈ Tr.chains,
    SitePresents T CA χ (parentSt H) (cellAt H) (sys H).1 (sys H).2
    -- SitePresents: cellEventE T CA χ es c = {x | Sigma.IsSolution x ∧ fd.sat x}
    --             ∧ entEvent T χ es = {x | Sigma.IsSolution x}
  sides : History p F → ℕ
  hsides : ∀ H ∈ Tr.chains, 1 ≤ sides H
  state_cell : ∀ H ∈ Tr.chains, sides H = 1 →
    stateEvent T (some H) = cellEventE T CA χ (parentSt H) (cellAt H)
  splitAt : ∀ H ∈ Tr.chains, 2 ≤ sides H → SideSplit T CA (cellAt H) (sys H).2
  hsplit_k : ...k = sides H
  free / freshCoords / hfresh / spectator_sol / hcard : ... -- (freshCoords H).card = (sys H).2.mstar

def SiteLedger.siteExp (L) (H) : ℕ := (L.sys H).2.mstar
```

`VTree.fiberAt` clause (i): `∀ H, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)` where
`PrunedMem T H x := T.mem (some H) x ∧ (no proper nonempty prefix τ-halts at x)`.
`Realizes T χ Tr := ∃ x, Tr.fiberAt T χ x`.

The PROVED step lemma T-E6 (fiber_seg_step), for `H ∈ Tr.chains`, `L.sides H = 1`, and any
`E` with `SpectatorFor (L.freshCoords H) E`:
```
Nat.card ↥(stateEvent T (some H) ∩ E) * p ^ L.siteExp H = Nat.card ↥(entEvent T χ (L.parentSt H) ∩ E)
```

TreeScaffold provides per-chain split frames (only at chains H with 2 ≤ (CA.branchSetOf (L.cellAt H)).card),
with `hframe : es = parentSt H ∧ c = cellAt H ∧ jointExp = siteExp H`, `hscope` (scope = the SubtreeFiber
event over the tree's own chains strictly below parentSt H), and `subtree_part`
(each branch ν's event S ν is `Set.univ` OR a ContFiber event over some Cν ⊆ Tr.chains with
**∀ H' ∈ Cν, H.IsPrefixOf H'** — all members extend the KEY chain H).

## CLAIM A (the shared-cell forcing — I believe this is a 20-line derivation)

Assume the full treeExp hypothesis row, and let H₁, H₂ ∈ Tr.chains with
`L.parentSt H₁ = L.parentSt H₂`, `L.sides H₁ = 1`, `L.sides H₂ = 1`. Then:

1. From `hreal` get x₀ with `Tr.fiberAt T χ x₀`; clause (i) gives `PrunedMem`, hence
   `T.mem (some Hⱼ) x₀`, i.e. x₀ ∈ stateEvent(H₁) ∩ stateEvent(H₂).
2. `state_cell` rewrites both: x₀ ∈ cellEventE(es, cellAt H₁) ∩ cellEventE(es, cellAt H₂)
   with the SAME es. Since cellOf es x₀ is a single value, `cellAt H₁ = cellAt H₂`.
3. Hence `stateEvent(H₁) = stateEvent(H₂)` (both equal the same cellEventE).
4. T-E6 at both (E = univ) gives p^{siteExp H₁} · |stateEvent H₁| = |entEvent es| =
   p^{siteExp H₂} · |stateEvent H₂|, and |stateEvent H₁| = |stateEvent H₂| > 0 (x₀ ∈ it),
   so `siteExp H₁ = siteExp H₂` (p prime > 1).

In particular: two DISTINCT sibling chains (same immediate parent H₀, so hparent forces
parentSt Hⱼ = .st H₀ for both when length ≥ 2) that are both one-side sites are forced to
have EQUAL state events and EQUAL siteExp.

## CLAIM B (countermodel: treeExp as stated is FALSE for some abstract instance)

Build the tree: head chain H₀ (one track, siteExp H₀ = w ≥ 0 arbitrary), and two children
H₁ = H₀.snoc ν₁, H₂ = H₀.snoc ν₂, both maximal, both τ-irr leaves (node data chosen so
IrrHalts holds; hdet fine). Ledger: sides = 1 at all three sites; parentSt Hⱼ = .st H₀;
cellAt H₁ = cellAt H₂ = c* — the model's cell partition at entrance .st H₀ has ONE cell c*
whose branch set is {ν₁, ν₂}, and the model's `mem`/`child` are rigged so that BOTH branches
are realized exactly on the c*-cell event: child(H₀,νⱼ) x ⟺ cellOf (.st H₀) x = c*
(this satisfies child_cell). Choose the presented systems: sys Hⱼ = (Σ, fd) with
{Σ sol} = stateEvent H₀ and fd pinning e* > 0 fresh coordinates, with
cellEventE(.st H₀, c*) = {Σ ∧ fd} of density p^{-e*} inside stateEvent H₀ — the SAME
(Σ, fd) for both children (allowed: presents only demands the displayed set equalities).
Then state_cell holds for H₁ and H₂ (their state events both equal the c* cell event by the
rigging), E6's identities hold (|c*|·p^{e*} = |stateEvent H₀|), spectator laws hold by
choosing fd's support disjoint from Σ's dependence, SibCount can be arranged in a
product-structure model (branch realization is DETERMINISTIC given the cell, and the two
subtree events for the leaf children coincide with the cell event, so all the SIB product
identities degenerate to trivial identities), the scaffold's frames at H₁/H₂ take
S ν₁ = S ν₂ = Set.univ and hdecomp holds because on c* both leaves are realized and halted
(their subtree conditions are implied by the cell + x-independent tree facts).
The correct total pinning from the whole box down to the fiber is
n + siteExp H₀ + e*   (the c* pins beyond stateEvent H₀ are pinned ONCE),
but the theorem's exponent is n + siteExp H₀ + siteExp H₁ + siteExp H₂ = n + siteExp H₀ + 2e*.
So the displayed identity fails by a factor p^{e*} — hence treeExp is UNPROVABLE as stated
(any proof would have to exclude this instance, and no hypothesis does).

Sanity check on the exponents: |fiber| = |rootCell g ∩ (head stuff) ∩ c*-event| =
p^m / p^{n + siteExp H₀ + e*}, while the theorem claims |fiber| · p^{n + siteExp H₀ + 2e*} = p^m.

The toy gate instance in the corpus dodges this because its sibling leaves carry mstar 0
(e* = 0), which the blueprint itself records as "the consistent form" and flags as an
E-PHASE WATCH ITEM: "the per-chain AofTr accounting at SHARED split cells and hframe's
jointExp = siteExp tie are the clauses to re-derive".

## CLAIM C (canonical joint-unsatisfiability at F1's shape)

The canonical F1 instance (censused): one head chain, two RAM τ-irr leaf children b₁, b₂
in a single-side window; each leaf's read pins ONE fresh digit (censused conditional mass
5^{-1} each: N(S₁ ∩ Σ_c) = 5^7 < N(Σ_c) = 5^8), so canonically
stateEvent(b₁) ≠ stateEvent(b₂) (different digit pins, neither contains the other).
But CLAIM A forces stateEvent(b₁) = stateEvent(b₂) under the hypothesis row (both are
one-side sites). So the canonical F1-shaped instance CANNOT satisfy the ledger row
(specifically state_cell at both leaves simultaneously) — the REV-6
"joint-satisfiability record" (which checked only the head site's numbers) is refuted at
the leaf sites.

## Your charge

1. Verify or break CLAIM A step by step (quote the exact definitional step that fails, if any).
2. Attack CLAIM B: name a hypothesis of treeExp (or a law of CellData/SiteLedger/TreeScaffold/
   SibCount/VTree.fiberAt as quoted) that the countermodel necessarily violates. Be concrete.
   In particular check: fiberAt clauses (ii)/(iv)/(v)/(vi), hleaf/hns_leaf, SibCount's full
   quantification (all entrances es, all cells, all admissible S prescriptions incl. mixed
   ContFiber/univ ones), JCmultiAt (vacuous here since sides ≡ 1?), RedCellPartition +
   child_red_uniform at the root, and E5's proved identity (must HOLD in the model).
3. Verdict per claim: CONFIRMED / BROKEN (with the breaking quote) / GAP (what's missing).
4. If you believe treeExp IS provable as stated, sketch the step that prices the shared-cell
   double charge away.

---

## Codex output (gpt-5.6-sol, session 019fad67-215c-7920-907e-7d1fb08a3e19)

codex
## Verdict

- CLAIM A: **CONFIRMED**, subject only to routine Lean lemmas (`univ` is spectator, cancellation, injectivity of powers).
- CLAIM B: **GAP**. The proposed countermodel is not shown to satisfy the full hypothesis structures. Nothing quoted proves it impossible, but it is not yet a countermodel.
- CLAIM C: **CONFIRMED**, conditional on the stated census that both leaves have `sides = 1`, the same entrance state, and unequal state events.

Therefore the supplied argument does **not** establish that `treeExp` is unprovable. It does establish a strong shared-cell collapse lemma that any proof or model must respect.

I could not inspect the omitted corpus fields because the local command sandbox is unavailable, and the definitions are not publicly indexed. Conclusions concerning omitted clauses are consequently marked as gaps rather than guessed.

## CLAIM A

### Steps 1–3

These are valid.

From:

> `∀ H, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)`

and `hreal : ∃ x, Tr.fiberAt T χ x`, every `H ∈ Tr.chains` satisfies `PrunedMem T H x₀`, whose first conjunct is `T.mem (some H) x₀`. Thus `x₀` lies in both state events.

For each `Hⱼ`, `state_cell` gives:

> `stateEvent T (some H) = cellEventE T CA χ (parentSt H) (cellAt H)`

Membership in `cellEventE` includes exactly:

> `CA.cellOf es x = c`

Since both entrances are definitionally the same `es`, one obtains:

```lean
CA.cellOf es x₀ = L.cellAt H₁
CA.cellOf es x₀ = L.cellAt H₂
```

hence `L.cellAt H₁ = L.cellAt H₂`. Rewriting `state_cell` then proves equality of the state events.

There is no hidden disjointness or choice assumption here: functionality of `cellOf` suffices.

### Step 4

T-E6 with `E = Set.univ` gives, after simplifying intersections:

```lean
card(stateEvent H₁) * p ^ siteExp H₁ = card(entEvent es)
card(stateEvent H₂) * p ^ siteExp H₂ = card(entEvent es)
```

The state events are equal and nonempty because they contain `x₀`. Cancelling their positive finite cardinality gives:

```lean
p ^ siteExp H₁ = p ^ siteExp H₂
```

and primality gives `1 < p`, hence injectivity of `e ↦ p^e`.

The only minor proof obligations not literally included in the quotation are:

- `SpectatorFor coords Set.univ`;
- finiteness of these subtypes;
- the standard natural-number cancellation and power-injectivity lemmas.

These are implementation details, not conceptual gaps.

### Sibling specialization

This is also correct. For a child history of length at least two, `hparent` rules out:

> `| .amb => False`

and:

> `| .red _ _ => H.nodes.length = 1`

so the parent is `.st H'`. The remaining conditions say that `H'` is a prefix exactly one node shorter. For `H = H₀.snoc ν`, uniqueness of a list prefix of that length gives `H' = H₀`.

No offending passage exists in CLAIM A.

## CLAIM B

No quoted law immediately contradicts the shared-child idea. In particular, the supplied definitions do not say distinct branches must have disjoint events. But several indispensable parts of the alleged model are asserted rather than constructed.

### 1. Full `fiberAt` characterization

Offending passage:

> “The correct total pinning from the whole box down to the fiber is  
> `n + siteExp H₀ + e*`”

Classification: **JUSTIFICATION GAP**.

Clause (i) alone does not establish this equality of events. A point is in `fiberAt` only after all other `fiberAt` clauses hold. To justify the cardinality formula, B must prove an exact set identity such as:

```lean
{x | Tr.fiberAt T χ x}
  = root-event ∩ head-event ∩ c*-event
```

Clauses (ii)/(iv)/(v)/(vi) might impose additional conditions or make the proposed `Tr` invalid. Saying they are “x-independent tree facts” is insufficient without their statements and witnesses.

### 2. VTree leaf laws

Offending passage:

> “both maximal, both τ-irr leaves (node data chosen so IrrHalts holds; hdet fine)”

Classification: **JUSTIFICATION GAP**.

This addresses `hdet` only. It does not verify `hleaf`, `hns_leaf`, or the omitted VTree closure/leaf clauses. “Chosen so” is not a construction of compatible node data.

No necessary violation can be inferred from the quoted material, but satisfaction is unproved.

### 3. SibCount

Offending passage:

> “SibCount can be arranged in a product-structure model … so all the SIB product identities degenerate to trivial identities”

Classification: **JUSTIFICATION GAP**, and the largest one.

The stated check concerns only the intended entrance/cell and the all-`univ` leaf prescription. The structure reportedly quantifies over:

- every entrance `es`;
- every cell;
- every admissible family `S`;
- mixed `ContFiber`/`Set.univ` prescriptions.

To discharge this, B must classify every admissible prescription and verify the identity for each. In particular, it must prove either:

1. every `ContFiber` option below a maximal leaf is actually `Set.univ`; or
2. the relevant mixed intersections satisfy the required product identity.

The sentence “degenerate to trivial identities” does not establish either.

### 4. TreeScaffold frames

Offending passage:

> “the scaffold’s frames at H₁/H₂ take `S ν₁ = S ν₂ = Set.univ` and `hdecomp` holds”

Classification: **JUSTIFICATION GAP**.

TreeScaffold requires frames for every chain meeting its branching-cardinality condition, not merely an exhibited convenient frame at the two leaves. The proposed construction must verify:

- all required chains, including possibly `H₀`;
- `hframe`, especially `jointExp = siteExp H`;
- the exact `hscope` event;
- every branch case of `subtree_part`;
- the actual set equality in `hdecomp`.

Assigning `S ν = univ` is not by itself proof of `hscope` or `hdecomp`.

### 5. Root laws and RedCellPartition

Offending passage:

> “RedCellPartition + child_red_uniform at the root”

B does not actually supply a verification of this; it only requests that it be checked.

Classification: **JUSTIFICATION GAP**.

The root model must simultaneously satisfy `mem_single`, the red-cell partition, `RootCellsOf`, and `child_red_uniform`. A product-coordinate model may well do so, but the relevant root event, tracks, and children must be defined and checked. Nothing quoted shows a necessary contradiction.

### 6. E5

Offending passage:

> “Sanity check on the exponents: `|fiber| = …`”

Classification: **JUSTIFICATION GAP**.

A proved E5 identity must hold automatically once its premises are satisfied. B has not derived its asserted head-event cardinality from E5 or shown that its definitions meet E5’s premises. The numerical expression is a consistency target, not verification.

### 7. `JCmultiAt`

The statement:

> “JCmultiAt (vacuous here since sides ≡ 1?)”

is correct. Under `sides H = 1`, the premise `2 ≤ L.sides H` is impossible, so `hjcm` is vacuous even if `H ∈ multiSites`.

### Net assessment of B

I cannot name a quoted hypothesis that the model **necessarily** violates. Shared child events and repeated ledgers are not prohibited by the displayed definitions.

But the repeated phrases “can be arranged,” “rigged,” and “degenerate to trivial identities” leave most of the high-quantification structures uninstantiated. Consequently B is not a countermodel yet, and its conclusion:

> “hence treeExp is UNPROVABLE as stated”

is a **CRITICAL ERROR in the claimed conclusion**: the preceding construction has not established existence of a full instance.

## CLAIM C

Assuming the census is accurate:

```lean
parentSt b₁ = parentSt b₂
sides b₁ = 1
sides b₂ = 1
stateEvent b₁ ≠ stateEvent b₂
```

CLAIM A yields:

```lean
stateEvent b₁ = stateEvent b₂
```

This is an immediate contradiction. Therefore the F1-shaped canonical data cannot satisfy both leaf instances of `state_cell`.

Offending earlier record:

> “the REV-6 ‘joint-satisfiability record’ (which checked only the head site’s numbers)”

Classification: **CRITICAL ERROR** for that joint-satisfiability claim. Checking only the head cannot certify the full ledger when `state_cell` quantifies over every chain.

This does not refute `treeExp`; it refutes that particular F1-shaped object as a witness to its hypothesis row.

## Final assessment of T-E8

The shared-cell double charge is a genuine danger, and CLAIM A proves that two one-side siblings cannot represent two different positive-cost leaf events. However, CLAIM B has not yet shown that a duplicated positive-cost shared cell survives the full `VTree`, `SibCount`, and `TreeScaffold` interfaces.

So the adversarial verdict is:

**`treeExp` is not shown false by the material supplied. Its provability remains unresolved; the proposed countermodel has major justification gaps.**
tokens used
37,478
## Verdict

- CLAIM A: **CONFIRMED**, subject only to routine Lean lemmas (`univ` is spectator, cancellation, injectivity of powers).
- CLAIM B: **GAP**. The proposed countermodel is not shown to satisfy the full hypothesis structures. Nothing quoted proves it impossible, but it is not yet a countermodel.
- CLAIM C: **CONFIRMED**, conditional on the stated census that both leaves have `sides = 1`, the same entrance state, and unequal state events.

Therefore the supplied argument does **not** establish that `treeExp` is unprovable. It does establish a strong shared-cell collapse lemma that any proof or model must respect.

I could not inspect the omitted corpus fields because the local command sandbox is unavailable, and the definitions are not publicly indexed. Conclusions concerning omitted clauses are consequently marked as gaps rather than guessed.

## CLAIM A

### Steps 1–3

These are valid.

From:

> `∀ H, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)`

and `hreal : ∃ x, Tr.fiberAt T χ x`, every `H ∈ Tr.chains` satisfies `PrunedMem T H x₀`, whose first conjunct is `T.mem (some H) x₀`. Thus `x₀` lies in both state events.

For each `Hⱼ`, `state_cell` gives:

> `stateEvent T (some H) = cellEventE T CA χ (parentSt H) (cellAt H)`

Membership in `cellEventE` includes exactly:

> `CA.cellOf es x = c`

Since both entrances are definitionally the same `es`, one obtains:

```lean
CA.cellOf es x₀ = L.cellAt H₁
CA.cellOf es x₀ = L.cellAt H₂
```

hence `L.cellAt H₁ = L.cellAt H₂`. Rewriting `state_cell` then proves equality of the state events.

There is no hidden disjointness or choice assumption here: functionality of `cellOf` suffices.

### Step 4

T-E6 with `E = Set.univ` gives, after simplifying intersections:

```lean
card(stateEvent H₁) * p ^ siteExp H₁ = card(entEvent es)
card(stateEvent H₂) * p ^ siteExp H₂ = card(entEvent es)
```

The state events are equal and nonempty because they contain `x₀`. Cancelling their positive finite cardinality gives:

```lean
p ^ siteExp H₁ = p ^ siteExp H₂
```

and primality gives `1 < p`, hence injectivity of `e ↦ p^e`.

The only minor proof obligations not literally included in the quotation are:

- `SpectatorFor coords Set.univ`;
- finiteness of these subtypes;
- the standard natural-number cancellation and power-injectivity lemmas.

These are implementation details, not conceptual gaps.

### Sibling specialization

This is also correct. For a child history of length at least two, `hparent` rules out:

> `| .amb => False`

and:

> `| .red _ _ => H.nodes.length = 1`

so the parent is `.st H'`. The remaining conditions say that `H'` is a prefix exactly one node shorter. For `H = H₀.snoc ν`, uniqueness of a list prefix of that length gives `H' = H₀`.

No offending passage exists in CLAIM A.

## CLAIM B

No quoted law immediately contradicts the shared-child idea. In particular, the supplied definitions do not say distinct branches must have disjoint events. But several indispensable parts of the alleged model are asserted rather than constructed.

### 1. Full `fiberAt` characterization

Offending passage:

> “The correct total pinning from the whole box down to the fiber is  
> `n + siteExp H₀ + e*`”

Classification: **JUSTIFICATION GAP**.

Clause (i) alone does not establish this equality of events. A point is in `fiberAt` only after all other `fiberAt` clauses hold. To justify the cardinality formula, B must prove an exact set identity such as:

```lean
{x | Tr.fiberAt T χ x}
  = root-event ∩ head-event ∩ c*-event
```

Clauses (ii)/(iv)/(v)/(vi) might impose additional conditions or make the proposed `Tr` invalid. Saying they are “x-independent tree facts” is insufficient without their statements and witnesses.

### 2. VTree leaf laws

Offending passage:

> “both maximal, both τ-irr leaves (node data chosen so IrrHalts holds; hdet fine)”

Classification: **JUSTIFICATION GAP**.

This addresses `hdet` only. It does not verify `hleaf`, `hns_leaf`, or the omitted VTree closure/leaf clauses. “Chosen so” is not a construction of compatible node data.

No necessary violation can be inferred from the quoted material, but satisfaction is unproved.

### 3. SibCount

Offending passage:

> “SibCount can be arranged in a product-structure model … so all the SIB product identities degenerate to trivial identities”

Classification: **JUSTIFICATION GAP**, and the largest one.

The stated check concerns only the intended entrance/cell and the all-`univ` leaf prescription. The structure reportedly quantifies over:

- every entrance `es`;
- every cell;
- every admissible family `S`;
- mixed `ContFiber`/`Set.univ` prescriptions.

To discharge this, B must classify every admissible prescription and verify the identity for each. In particular, it must prove either:

1. every `ContFiber` option below a maximal leaf is actually `Set.univ`; or
2. the relevant mixed intersections satisfy the required product identity.

The sentence “degenerate to trivial identities” does not establish either.

### 4. TreeScaffold frames

Offending passage:

> “the scaffold’s frames at H₁/H₂ take `S ν₁ = S ν₂ = Set.univ` and `hdecomp` holds”

Classification: **JUSTIFICATION GAP**.

TreeScaffold requires frames for every chain meeting its branching-cardinality condition, not merely an exhibited convenient frame at the two leaves. The proposed construction must verify:

- all required chains, including possibly `H₀`;
- `hframe`, especially `jointExp = siteExp H`;
- the exact `hscope` event;
- every branch case of `subtree_part`;
- the actual set equality in `hdecomp`.

Assigning `S ν = univ` is not by itself proof of `hscope` or `hdecomp`.

### 5. Root laws and RedCellPartition

Offending passage:

> “RedCellPartition + child_red_uniform at the root”

B does not actually supply a verification of this; it only requests that it be checked.

Classification: **JUSTIFICATION GAP**.

The root model must simultaneously satisfy `mem_single`, the red-cell partition, `RootCellsOf`, and `child_red_uniform`. A product-coordinate model may well do so, but the relevant root event, tracks, and children must be defined and checked. Nothing quoted shows a necessary contradiction.

### 6. E5

Offending passage:

> “Sanity check on the exponents: `|fiber| = …`”

Classification: **JUSTIFICATION GAP**.

A proved E5 identity must hold automatically once its premises are satisfied. B has not derived its asserted head-event cardinality from E5 or shown that its definitions meet E5’s premises. The numerical expression is a consistency target, not verification.

### 7. `JCmultiAt`

The statement:

> “JCmultiAt (vacuous here since sides ≡ 1?)”

is correct. Under `sides H = 1`, the premise `2 ≤ L.sides H` is impossible, so `hjcm` is vacuous even if `H ∈ multiSites`.

### Net assessment of B

I cannot name a quoted hypothesis that the model **necessarily** violates. Shared child events and repeated ledgers are not prohibited by the displayed definitions.

But the repeated phrases “can be arranged,” “rigged,” and “degenerate to trivial identities” leave most of the high-quantification structures uninstantiated. Consequently B is not a countermodel yet, and its conclusion:

> “hence treeExp is UNPROVABLE as stated”

is a **CRITICAL ERROR in the claimed conclusion**: the preceding construction has not established existence of a full instance.

## CLAIM C

Assuming the census is accurate:

```lean
parentSt b₁ = parentSt b₂
sides b₁ = 1
sides b₂ = 1
stateEvent b₁ ≠ stateEvent b₂
```

CLAIM A yields:

```lean
stateEvent b₁ = stateEvent b₂
```

This is an immediate contradiction. Therefore the F1-shaped canonical data cannot satisfy both leaf instances of `state_cell`.

Offending earlier record:

> “the REV-6 ‘joint-satisfiability record’ (which checked only the head site’s numbers)”

Classification: **CRITICAL ERROR** for that joint-satisfiability claim. Checking only the head cannot certify the full ledger when `state_cell` quantifies over every chain.

This does not refute `treeExp`; it refutes that particular F1-shaped object as a witness to its hypothesis row.

## Final assessment of T-E8

The shared-cell double charge is a genuine danger, and CLAIM A proves that two one-side siblings cannot represent two different positive-cost leaf events. However, CLAIM B has not yet shown that a duplicated positive-cost shared cell survives the full `VTree`, `SibCount`, and `TreeScaffold` interfaces.

So the adversarial verdict is:

**`treeExp` is not shown false by the material supplied. Its provability remains unresolved; the proposed countermodel has major justification gaps.**
