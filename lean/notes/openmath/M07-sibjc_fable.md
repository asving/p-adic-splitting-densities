# M07-sibjc — attempt (Fable, 2026-07-31)

Target: the `BK.sibjc` hypothesis row (`SibJcRows` at the pinned canonical-tree
instance) — see `M07-sibjc_brief.md` for the full unfolded statement. This
file: (i) a structural audit of the three typed fields, producing three
explicit adversarial-instantiation routes that make **each field plausibly
FALSE as typed** (the strongest one reuses the project's own sealed census
integers); (ii) the positive mathematics: a reduction of the intended laws to
four named kernels, with the depth-0 counting core proved rigorously and the
(JC-multi)-as-consumed form proved modulo the site-ledger fields; (iii) exact
open lemmas; (iv) numeric tests.

Notation from the brief: Box = (𝔽_p)^{n·N}; dec(x) the decoded monic degree-n
ℤ_p-polynomial; T = the pinned canonical tree model at level N (mem/child =
realized OM runs of dec(x)); CA a cell assignment; Σ_c the conditioning event;
S_ν the prescribed-finite-subtree continuation events; m = branch-roster size.

---

## 1. The decisive structural fact: `CellData` has no adaptedness law

The mother note's (SIB) conditions on "the site's full joint cell c_s, the
complete realized stratum datum of that read" — a function of the data the
site's reads have already consumed (a "past-measurable" object). The Lean
carrier `CellData` (MovesT/Defs.lean:335) constrains `cellOf` only by:

* `cell_local` — cellOf es is a function of the coordinates in
  {j : levelOf j < cellLevel es}, where **`levelOf` and `cellLevel` are the
  CA's own free data** (choose levelOf ≡ 0, cellLevel ≡ 1: no constraint);
* the branch-roster laws (`child_cell` iff at chain states; inclusions at
  `.amb`/`.red`; `child_red_uniform`) — these constrain only which NODES sit
  in a cell's roster, never which digits a cell may read;
* `branch_cell_joint` — the site read map factors through the joint read (any
  coarsening is lawful).

Consequence: **a lawful CA may key cells on the sibling branches' future
digits.** Since `SibJcRows` universally quantifies over CA (and over es, ν₀,
c, and for `jc_multi` over fd, ss), the rows assert the independence/pricing
laws also at such future-reading cells — where they are false for the same
reason that conditioning on {X = Y} destroys independence of (X, Y).

All three routes below are stated conditionally on:

**(OL-2) CellAssign inhabitedness at the pinned instance** — there exists at
least one lawful CA at (pol, Tm N, chart, trackOf) for some trackOf. This
needs two instance facts: (a) child rosters are finite (policy-canonicity
should pin the root/residue data of a child; without it no `branchSetOf`
Finset exists and every row is **vacuously true** — itself a defect worth
recording); (b) `child_cover` is realizable, i.e. L1-totality (a repeated
residual factor opens a realized window child) holds at the pinned model.
Given any one lawful CA, each route below modifies only `Cell`/`cellOf`/
`branchSetOf`/`branchCellOf` in ways that preserve every `CellData`/
`CellAssign` law (checked field-by-field in §2.4).

---

## 2. Route 1 (the sharpest): correlation cells refute `sib` — with the gate's own integers

Work at the sealed F1 instance (verification/CASE_SIB_SEALED_PREDICTIONS.md):
p = 5, n = 4, level-0 reduction R₀ = (z−1)²(z−2)² over 𝔽₅, branch roster
{b₁ (track z−1), b₂ (track z−2)}, both continuing (μ = 2). On the box B22 the
canonical 14-pin window cell Σ* has 390,625 = 5⁸ members; the two branches'
depth-1 RAM digits v₁, v₂ ∈ 𝔽₅ are, by the gate's censused finding P2, exactly
jointly uniform on Σ* (all 25 pairs equally often, 15,625 each).

**The adversarial CA.** Take any lawful CA₀ (OL-2) and refine:
Cell := CA₀.Cell × Option Bool,
cellOf es x := (CA₀.cellOf es x, if x ∈ Σ* then some (decide (v₁(x) = v₂(x)))
else none), branchSetOf (c, _) := CA₀.branchSetOf c, branchCellOf likewise
diagonal-refined. (Σ* and the digit forms v_r are explicit functions of the
box digits — the gate's S2 algebra; everything is a total function of x.)

**Lawfulness.** Refining cells preserves: `child_cell` (iff: the roster map
ignores the new component and the old iff transports along the refinement);
`child_root_sub`, `child_cell_red` (inclusions, same transport);
`child_red_uniform` (a refined cell is a subset of an old cell, on which child
behavior was already constant); `cell_local` (set cellLevel := big, levelOf as
in CA₀ ∧ v-supports); `branch_cell_joint` (diagonal refinement still factors);
`child_cover` (roster map unchanged). `hCellFin` ✓.

**The instantiation.** es := the F1 `.red` entrance (reduction ḡ with track
z−1), c := (c₀, some true) where c₀ := CA₀'s cell containing Σ* — to keep the
arithmetic pinned, take CA₀'s red-cells at F1 to BE Σ* (if CA₀'s cells are
coarser/finer, refine/merge the first component on Σ* likewise; the same laws
transport). Then

    Σ_c = Σ* ∩ {v₁ = v₂},  #Σ_c = 390,625/5 = 78,125.

Roster: {b₁, b₂}, guard 2 ≤ 2 ✓. Events: fix a ≠ 0 and let S_r := the
ContFiber event "branch r's continuation is exactly the depth-1 RAM τ-irr leaf
with recorded endpoint digit a" (Tsub = {[b_r], [b_r, ν'_a]}, leafSpec = the
irr verdict, nsSpec = false; on Σ* this event is exactly {v_r = a}: the iff
clause of ContFiber excludes every other realized continuation, and the RAM
leaf's remaining node data are Σ*-constants). Then, using P2-uniformity:

    #(Σ_c ∩ S₁ ∩ S₂) = #(Σ* ∩ {v₁ = v₂ = a}) = 15,625
    #(Σ_c ∩ S₁) = #(Σ* ∩ {v₁ = v₂} ∩ {v₁ = a}) = 15,625 = #(Σ_c ∩ S₂)

    LHS of (SIB) = 15,625 · 78,125 = 5¹³
    RHS of (SIB) = 15,625 · 15,625 = 5¹²  —  **fails by a factor 5.**

So `sib` as typed is refuted at this instantiation, PROVIDED (OL-2) and the
transcription of the F1 events into ContFiber form survive Lean-level
scrutiny. Status: **PLAUSIBLE-FALSE-AS-TYPED, countermodel-first discipline
applies** (compile it before any proof attempt). Note this does NOT touch the
intended mathematics: the conditioning event {v₁ = v₂} is not a stratum datum
of the site's own read; the note's Σ_c never admits it.

## 2.1 Route 2: `jc_multi` — the empty side split

`SideSplit T CA c fd` for fd := ⟨[], nil⟩ (no clauses) exists whenever
branchSetOf c contains ≥ 2 nodes whose `line.slope`s take ≥ 2 distinct values:
take k := the number of distinct slopes, hullSlope := the sorted list,
sideOf := slope lookup, clausesOf := ∅, sideSpan := ∅ (all partition/
disjointness/support laws hold trivially). `IsMultiSideSite` ✓. Then
`JCmultiAt` demands

    #(siteCellEvent es ν₀ c) · p⁰ = #(entEvent es),

i.e. the site cell event EQUALS the entrance event in cardinality — false at
every realized proper cell (e.g. at F1's Σ*: 5⁸ against the 4-pin rootCell's
5¹⁸ members of B22). A realized multi-slope roster exists at any genuinely
two-sided window (n ≥ 3 boxes with a two-sided first polygon; or, entirely
adversarially, a junk cell value whose roster is two junk nodes with distinct
slopes — rosters of never-realized cell values are unconstrained). Same (OL-2)
conditionality; otherwise the field is refuted by pure bookkeeping — the
quantifier ∀ fd ss forgets that fd must be the site's OWN presented system.

## 2.2 Route 3: `sib_at`/`jc_multi` — unrealized cells and coarsened site reads

Two more independent instantiation defects of the site-keyed fields:

* **Unrealized cell values.** `JCmultiAt` has the entrance event on the RIGHT:
  choose c outside the image of branchCellOf es ν₀ (adversarially always
  possible: enlarge Cell by a fresh value; rosters of unrealized values are
  free): LHS = 0, RHS = #(entEvent es) > 0 (es := `.amb` gives p^{nN}).
* **Coarsened site reads.** `branch_cell_joint` permits branchCellOf es ν₀ :=
  a coarsening of cellOf es; taking c a coarse value merging two joint cells
  with different continuation statistics (e.g. one where the roster's subtree
  events have positive mass and one where they are impossible) breaks
  `SibCountAt`'s product by the mixture inequality: with U = C₁ ⊔ C₂,
  per-C₁ exactness, and S₁ ∩ S₂ ∩ C₂ = ∅: LHS/RHS = 1 + #C₂/#C₁ > 1.
  (`sib_at`'s ν₀ is arbitrary — not required to lie in the roster, not
  required to be the site's own branch node.)

## 2.3 Why the intended (adapted) `.st`/`.red` laws resist these attacks

For cells that ARE functions of the site's own realized read data (the note's
strata), the mechanism that survives is not "product" but **uniformity**: the
gate's P2 finding is that the stacked sibling word vector is exactly uniform
on the product alphabet on each canonical cell. Uniform conditional laws with
cell-independent alphabets are preserved under mixing cells of the same
shape — which is why the canonical statement tolerates the coarsenings that
`child_cell` (same roster) still allows, and why the adversarial routes above
must reach for future-reading or cross-shape mixtures to break the typed form.
This is diagnostic: any repaired row should quantify over cells that are
(i) adapted (past-measurable) and (ii) shape-complete, or should simply be
keyed to the designated canonical CA / the `SiteLedger` sites, matching how
`treeN` consumes the laws.

## 2.4 Recommended statement repairs (designer-queue material, not executed)

R1 (minimal): add to `CellData` an adaptedness field — `cellOf es` factors
through the site's realized read/stratum data (concretely: through the pair
(roster, the presented locus of `SitePresents`), or through the digit
positions consumed by the site's reads). R2 (structural): replace ∀ CA in
`SibJcRows` by the designated wave-D canonical CA. R3 (consumption-exact):
restate the rows quantified over a `SiteLedger` for a realized tree — exactly
the `hsibT`/`hjcm` shapes `treeN` consumes — so `presents`/`state_cell`/
`hsplit_exp`/`spectator_sol` become available hypotheses. R3 makes `jc_multi`
PROVABLE outright (Lemma B below).

---

## 3. The positive mathematics: reduction + the proved cores

### 3.1 Lemma A (depth-0 factorization counting) — PROVED (known result; self-contained new write-up)

**Lemma A.** Let p be prime, K ≥ 1, and ū₁, …, ū_m ∈ 𝔽_p[z] monic, pairwise
coprime, deg ū_j = d_j, n := Σ d_j. Let
A_j := {g ∈ (ℤ/p^K)[x] monic, deg d_j, g mod p = ū_j} and
U := {f ∈ (ℤ/p^K)[x] monic, deg n, f mod p = Π ū_j}. Then multiplication
(g₁, …, g_m) ↦ Π g_j is a **bijection** Π_j A_j → U. In particular
#U = Π_j #A_j = Π_j p^{(K−1)d_j}, at every K.

*Proof.* By induction on m it suffices to treat m = 2 (ū₁ and ū₂⋯ū_m are
coprime). Well-definedness is clear (monic·monic = monic, reduction is
multiplicative).

Injectivity: let gh = g'h' with ḡ = ḡ' = ū, h̄ = h̄' = v̄, all monic of the
right degrees. Let k ≥ 1 be maximal with g ≡ g', h ≡ h' (mod p^k) (k ≥ 1
since all reduce to ū, v̄). If k ≥ K we are done. Else write g' = g + p^k a,
h' = h + p^k b with deg a < d₁, deg b < d₂ (differences of monic polynomials
of equal degree) and (ā, b̄) ≠ (0, 0) by maximality of k. Expanding
0 = g'h' − gh = p^k (a h + b g) + p^{2k} a b and dividing by p^k, reduction
mod p gives ā v̄ + b̄ ū = 0 in 𝔽_p[z]. Hence ū ∣ ā v̄; coprimality gives
ū ∣ ā; deg ā < deg ū forces ā = 0, then b̄ ū = 0 forces b̄ = 0 —
contradiction. ∎(inj)

Surjectivity: given f ∈ U, construct (g_k, h_k) with g_k h_k ≡ f (mod p^k) by
induction; k = 1 is the hypothesis. Step: given monic lifts g, h of ū, v̄ with
f − gh = p^k r (deg r < n since both are monic of degree n), pick by Bézout
(s̄ū + t̄v̄ = 1) and division-with-remainder polynomials ā, b̄ ∈ 𝔽_p[z] with
r̄ = ā v̄ + b̄ ū, deg ā < d₁, deg b̄ < d₂ (write r̄t̄ = qū + ā; then
b̄ := r̄s̄ + qv̄ has degree < d₂ by degree count). Set g' := g + p^k A,
h' := h + p^k B for lifts A, B of ā, b̄ of the same degrees: then
g'h' ≡ gh + p^k (Ah + Bg) ≡ f − p^k r + p^k r ≡ f (mod p^{k+1}), and g', h'
remain monic of degrees d₁, d₂. Iterate to k = K. ∎

**Corollary A′ (depth-0 product identity).** If, under the bijection of Lemma
A, events S_j ⊆ U are pullbacks of per-factor events E_j ⊆ A_j (S_j =
pr_j^{−1}(E_j)), and Σ ⊆ U is a pullback of per-factor cells C_j, then

    #(Σ ∩ ⋂_j S_j) · #Σ^{m−1} = Π_j #(Σ ∩ S_j)

(both sides equal Π_j #(E_j ∩ C_j) · (Π_i #C_i)^{m−1}). ∎

This is exactly `SibCount`'s shape at depth-0 sites, and (with all reductions
distinct-irreducible-power) the coprimality hypothesis is automatic. The
measure form of Lemma A is standard in the density-of-splitting literature
(label: (a) known — e.g. the factorization/mass lemmas in Bhargava–Cremona–
Fisher–Gajović, *The density of polynomials of degree n over ℤ_p having
exactly r roots in ℚ_p*, and in Del Corso–Dvornicich; exact lemma numbers not
verified in this session — flagged for lookup). The finite-level bijection
form above is what the count-face rows need.

### 3.2 Lemma B ((JC-multi) as consumed) — PROVED modulo the ledger fields

**Lemma B (disjoint-support pricing).** Let E ⊆ (𝔽_p)^m and let cl₁, …, cl_s
be clauses with pairwise disjoint supports, each satisfying the exact count
law #{y supported on supp(cl) : cl.sat y} · p^{codim(cl)} = p^{|supp(cl)|},
and suppose membership in E does not depend on the coordinates in ⋃ supp(cl)
(spectator hypothesis). Then

    #(E ∩ {x : ∀ i, cl_i.sat x}) · p^{Σ_i codim(cl_i)} = #E.

*Proof.* Factor (𝔽_p)^m = (coords outside ⋃ supp) × Π_i (𝔽_p)^{supp(cl_i)}.
By the spectator hypothesis E = E′ × Π_i full; by support-locality (`dep`)
each sat-set is full × A_i × full with #A_i · p^{codim_i} = p^{|supp_i|}
(count law). Multiply. ∎

At a `SiteLedger` site, `presents` gives siteCellEvent = {Σ-solutions ∧
fd.sat} and entEvent = {Σ-solutions}; `spectator_sol` + `free` give the
spectator hypothesis; `FreshData.disj` gives disjoint supports; `hsplit_exp`
converts the side-split exponent Σ_j sideExp(j) to fd.mstar = Σ codim. Hence
**JCmultiAt holds at every ledgered site** — (JC-multi) in its consumed form
is elementary; the entire difficulty of the area is inhabiting the presented
faces (which is the HC-2 §C engine: the U10 (ZC) ladder builds exactly the
locus/fresh systems with the `count` and spectator properties). The
`SideSplit` layer adds nothing to the counting: the side decomposition only
regroups the clause list. Label: (c) new (trivial given the ledger; recorded
because it relocates the open content of jc_multi entirely into the ledger
inhabitation + the typed-form repair R3).

### 3.3 The general-depth reduction ((SIB) for adapted cells)

Reduce adapted (SIB) at an arbitrary realized site to four kernels:

* **K-FACT (stage factorization; literature, already pinned in
  `docs/GMN_citations.md`).** On the site's stratum, dec(x) factors over ℤ_p
  compatibly with the branch roster: distinct polygon sides split off coprime
  factors (GMN Thm 1.15 order 1; Thm 3.1 order r) and distinct residual
  factors split further (GMN Thm 1.19; Thm 3.7). Write dec(x) = f₀ · Π_j f_j
  with f_j the sub-cluster factor of roster member ν_j and f₀ the off-site
  rest.
* **K-LOC (locality of continuations).** For x in the cell, the continuation
  reads of branch ν_j coincide with the OM reads of the factor f_j, up to
  cell-constant normalization. Mechanism: residual multiplicativity (the
  "product in order r" — GMN Thm 2.26 per the corpus's axiom-faithfulness
  record): along branch j's type the co-factors have ω = 0, so they
  contribute a polygon translation and a residual unit scalar that are
  **constant on the cell**; hence a prescribed-subtree event of ν_j is the
  pullback of an event of f_j alone. (This is the note's [2r] REL.2 duty.)
* **K-JAC (Jacobian constancy).** ρ(c) := Σ_{i<j} v_p(Res(f_i, f_j)) is
  constant on the cell. Mechanism: siblings separate at the site with
  distinct residual factors (or distinct sides), so EVERY cross-pair of roots
  θ_i of f_i, θ_j of f_j has v(θ_i − θ_j) exactly the height determined by
  the shared prefix + the separating side's slope (distinct residue classes
  after the frame normalization — no deeper cancellation is possible), and
  these heights are cell data. Summing over root pairs, ρ(c) is pinned.
  Supporting literature: OM-data formulas for discriminants/resultants
  (E. Nart et al., local computation of differents/discriminants — precise
  reference flagged for lookup).
* **K-COUNT (finite-level change of variables).** The multiplication map
  (f_j)_j ↦ Π f_j has derivative given by the Sylvester matrix; its
  determinant is ± Π_{i<j} Res(f_i, f_j) (classical). For N large relative
  to (thresholds of c) + ρ(c), the level-N multiplication map over the cell
  is injective on factor-tuples-mod-p^N up to fibers of the **constant** size
  p^{ρ(c)·(m−1)-bookkeeping}, uniformly over the cell (Smith normal form +
  a Newton-iteration absorption of the quadratic terms). Depth 0 with ρ = 0
  is Lemma A.

**Assembly.** Given K-FACT + K-LOC, the cell and the events S_j are pullbacks
of per-factor data; given K-JAC + K-COUNT, the level-N counting measure on the
cell is the product of per-factor counting measures times the constant
p^{−ρ(c)}-type factor; the constant cancels in the (SIB) identity
(#(Σ_c ∩ ⋂S) · #Σ_c^{m−1} = Π #(Σ_c ∩ S_j) is invariant under scaling the
correspondence's fiber size, as both sides scale by the m-th power). This
matches the gate's own recorded mechanism ("constant-valuation Jacobian
factors; constancy on Σ_c, not unit value, pushes the uniform mass to product
measure").

Status of the kernels: K-FACT — known, citable, already in the declared GMN
import perimeter. K-LOC — derivation sketched above from residual
multiplicativity; not fully proved here (the recentering/lift bookkeeping is
exactly the HC-2 D.10/U17a area); OPEN as a precise lemma. K-JAC — proof
sketch above is essentially complete for same-side siblings; the multi-side
case needs the min-slope bookkeeping; OPEN but routine. K-COUNT — OPEN, the
genuinely new quantitative lemma (the note's stacked (SIB-STEP) in factor
coordinates); the small-N edge (N not large relative to ρ(c) + thresholds)
must be handled by the realizability guards (a cell realized at level N has
thr ≤ N, but the needed buffer is ~2ρ; whether the row's all-N claim survives
at the boundary is UNRESOLVED and is a second reason to expect the typed
all-N form to need a guard).

### 3.4 Literature-axiom eligibility

As typed, `SibJcRows` states strictly MORE than any literature statement I can
identify: (i) the ∀-CA quantification (no published statement quantifies over
abstract cell assignments — and per §2 it makes the rows false-or-vacuous);
(ii) all-N exactness including the small-N boundary; (iii) depth ≥ 1 joint
independence in exact count form (the note's own record: done at no depth ≥ 1
in accepted text; my K-COUNT is the missing quantitative piece). The depth-0
slice (Corollary A′) DOES match known results up to phrasing. Verdict:
NOT literature-axiom-eligible as typed; after repair R3, the jc_multi field
becomes a theorem (Lemma B) and the sib fields reduce to K-LOC/K-JAC/K-COUNT
with only K-FACT citable.

---

## 4. Open lemmas (exact statements of the remaining gaps)

* **OL-1 (K-COUNT).** Fix a realized site stratum Σ_c (canonical cell) at
  level N with branch factors f₁, …, f_m and ρ := Σ_{i<j} v_p(Res(f_i,f_j))
  (constant by K-JAC). Claim: the map x ↦ (f_j mod p^{K_j})_j (with the cell's
  per-branch precision offsets K_j determined by c) is a surjection of Σ_c
  onto the product of the per-branch strata with all fibers of equal size,
  for every N ≥ thr(c). [The note's (SIB-STEP), factor-coordinate form.]
* **OL-2 (inhabitation).** Existence of a lawful `CellAssign` at the pinned
  model: finiteness of realized child rosters + L1-totality (`child_cover`).
  Decides vacuous-vs-refutable for the typed rows and is prerequisite to the
  §2 countermodels.
* **OL-3 (K-LOC precise form).** Continuation reads of ν_j on Σ_c = OM reads
  of f_j after a cell-constant frame change (statement must fix the
  recentering/lift convention; the HC-2 `StageTransHyp`/D.10 area is exactly
  this bookkeeping in Lean).
* **OL-4 (small-N boundary).** Either both sides of (SIB)/(JC-multi)
  degenerate consistently for N < thr(c) + buffer, or the rows need N-guards.

---

## 5. Relation to the HC-2 ladder (U10/U17a/U21/U26 + HK15)

The ladder is the PER-BRANCH engine, not the joint law: U10 (`zc_step`) is the
single-chain per-step exact-count conditional ((ZC) re-establishment) that
inhabits the clause `count`/spectator structure Lemma B consumes; U17a/U21/U26
are the presentation-normalization bookkeeping (lift independence, vertex
transport, representative independence) that K-LOC needs; HK15 builds a
concrete child stage carrier (the F4 gate instance). None of them touches
K-COUNT — the cross-sibling quantitative kernel has no owner unit at HEAD.
If the §2 countermodels compile, the repair (R1–R3) should be adjudicated
BEFORE any prover effort is spent on the typed rows.

---

VERDICT: PARTIAL — the three fields of `SibJcRows` are plausibly FALSE AS
TYPED (three explicit adversarial-instantiation routes over the lawful-but-
unadapted cell-assignment quantifier, the sharpest reusing the sealed F1
census: 5¹³ ≠ 5¹²; all conditional on CellAssign inhabitedness, else the rows
are vacuous); the intended mathematics is REDUCED to four named kernels
(K-FACT citable = GMN 1.15/1.19/3.1/3.7; K-LOC/K-JAC sketched; K-COUNT the one
genuinely new quantitative lemma), with the depth-0 counting core (Lemma A +
Corollary A′) proved rigorously and (JC-multi) in its ledger-consumed form
proved modulo the site-ledger fields (Lemma B). Not literature-axiom-eligible
as typed. Recommended: compile the §2 countermodels, then repair R3.

## NUMERIC-TESTS

All exact integer counting; sympy suffices for 1–3, cypari2 (factorpadic) for
4–5. Reuse `verification/case_sib_gate.py`'s B22 enumeration where marked.

1. **Correlation-cell breakage (Route 1 core).** p = 5, n = 4, the F1 B22
   census (5⁸ members of the 14-pin cell Σ*). For each a ∈ {1,…,4} compute
   N₁ := #(Σ* ∩ {v₁ = v₂}), N₂ := #(Σ* ∩ {v₁ = v₂ = a}).
   CONFIRMS Route 1 if N₂·N₁ ≠ N₂² (predicted: N₁ = 78,125, N₂ = 15,625,
   ratio 5). REFUTES Route 1's arithmetic (and rescues the typed row at this
   instance) only if the gate's P2 uniformity fails — which would contradict
   the sealed census.
2. **Lemma A brute force — EXECUTED (2026-07-31, this session).** For
   p ∈ {2, 3}, K ∈ {2, 3}, coprime tuples ū including non-squarefree powers,
   exhaustive enumeration of monic lifts mod p^K, checking bijectivity of
   multiplication onto U (injectivity by product hashing, surjectivity by set
   equality). All six instances EXACT:
   (p=2,K=2, z²·(z+1)) #U=8=Π#A bij ✓; (p=2,K=2, (z²+z+1)·(z+1)) 8 ✓;
   (p=2,K=2, z²·(z+1)²) 16 ✓; (p=2,K=3, z²·(z+1)²) 256 ✓;
   (p=3,K=2, z²·(z+1)·(z+2), m=3) 81 ✓; (p=2,K=2, z·(z+1)·(z²+z+1), m=3)
   16 ✓. Script pattern: `/tmp/lemA.py` (pure Python, reproduce anywhere).
3. **Beyond the gate perimeter: mixed-shape continuing pair at n = 5.**
   p ∈ {2, 3}, f̄ = (z−a)²(z−b)³ (a ≠ b): two CONTINUING branches of
   different shapes (μ = 2 and μ = 3) — the face the gate could not reach at
   n ≤ 4. Enumerate the joint cell (level-0 cell + both branches' full first
   window data) in the minimal word-sufficient box (mirror FC4's
   construction; at p = 2 expect ≤ 2²⁰ points); compute the exact joint
   contingency of the two branches' next-read words. CONFIRMS (SIB)'s
   intended form if the stacked law is exactly uniform on the product
   alphabet on every cell; a single non-uniform cell REFUTES the intended
   mathematics (not just the typed form) and is a stop-the-line event.
4. **K-JAC constancy.** Same F1 cell: for every member x of a sampled
   sub-box (or all 5⁸), factor dec(x) with PARI `factorpadic` (p = 5,
   precision ≥ 12), group the two quadratic cluster factors f₁, f₂, compute
   v₅(Res(f₁, f₂)). CONFIRMS K-JAC if the value is constant on the cell;
   record the constant and repeat on a second cell (different pinned digit
   values) — cross-cell variation is allowed, within-cell variation REFUTES
   K-JAC as stated.
5. **K-COUNT equal fibers.** Same setup: for k = 4, 5, 6 count the fibers of
   x ↦ (f₁ mod 5^k, f₂ mod 5^k) over Σ*. CONFIRMS K-COUNT if the fiber-size
   histogram is a single spike (size 5^{ρ′} for a k-independent offset ρ′
   matching test 4's constant); a multi-spike histogram REFUTES the
   equal-fibers form and would force a weaker (SIB) mechanism.
6. **Route 2 bookkeeping (no computation).** Record the pinned integers:
   #Σ* = 5⁸ vs #(rootCell ∩ B22) = 5¹⁸ — any realized proper cell witnesses
   #(cell) ≠ #(entrance), which is all the empty-side-split route needs once
   a lawful CA is exhibited (OL-2).
