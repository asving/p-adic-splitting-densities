# O13 verification package, REV 2 — finiteness and p-independence of the degree-n species menu

*(Self-contained package for a fresh-context adversarial verifier. Everything needed is
defined below in standard mathematical language; no external documents are required.
Charge: quote-and-classify each defect as CRITICAL ERROR (breaks the chain) or
JUSTIFICATION GAP (assume and continue); fix nothing. §7 lists what to check.*

*Rev note: a prior hostile pass on rev 1 returned SOUND-WITH-GAPS — Theorems 1, 2, 3, 5
correct as stated; gaps: the tree-level run collapse was informal (no definition for
possibly-infinite trees), one sentence overstated ("a run's letter has a self-loop",
false for singleton runs), whole-tree finiteness after collapse was not proved, and two
value-side claims exceeded what the displayed proofs establish. Rev 2 adds the formal
definitions D9/D10 and Lemmas E/T′, fixes the overstatement, and draws the
proved/ambient boundary explicitly ((VAL-DIV), §6). Verify from scratch; do not assume
the prior pass.)*

## §0 The claim

Fix an integer n ≥ 1. We define below, from the integer n ALONE, a finite alphabet 𝒮_n
of "letters" (D1/D4), a directed "menu" graph on it (D5), a set Sk(n) of "skeletons" —
finite rooted trees labeled by letters (D8) — and the run-collapse of possibly-infinite
labeled trees (D9/D10). The claims to verify:

> **Theorem 1.** |𝒮_n| ≤ (n+2)^{n²+3n+12}. The definition of 𝒮_n mentions no prime.
> **Theorem 2.** The menu graph's self-loops are exactly its "full" letters of tag REC;
> after deleting self-loops the graph is acyclic, and every self-loop-free directed walk
> visits ≤ 6n² vertices.
> **Theorem 3.** |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}. The definition of Sk(n) mentions no
> prime.
> **Lemma T′ (collapse).** Every pre-skeleton (D9) — a possibly-INFINITE labeled tree —
> run-collapses (D10) to a skeleton, hence to a member of the finite set Sk(n); its run
> lengths are parameters in ℤ≥1 ∪ {∞}, never data of the collapsed tree.
> **Theorem 5.** (Classical ramification envelope; Serre's different bound.) For every
> prime p and every finite separable extension L/K of degree m ≤ n, K a complete
> discretely valued field with perfect residue field of characteristic p and v_K(p) = 1:
> v_K(disc(L/K)) ≤ (m−1) + m·v_p(m) ≤ (n−1) + n·log₂ n — a bound independent of p.

Semantic context (GLOSS, not consumed by any proof; the one semantic clause that IS
consumed is displayed as assumption (COMP) in §5): the letters are the value-free,
height-free records of single "reads" of the Montes/Okutsu (higher Newton polygon)
factorization process applied to a monic degree-n polynomial over ℤ_p — D is the degree
of the current key polynomial, w the residue degree of the current coefficient pool,
W the window width of the current development, (e, s₀, ℓ) the read side's slope
denominator, left endpoint, and normalized length, λ the (degree, multiplicity) pattern
of the side's residual-polynomial factorization over the finite residue field, sel the
factor the branch descends at, and the flanks the other sides' spans. Slope numerators
(heights), digit values, and repetition counts of self-loop reads are deliberately NOT
fields. The theorems say: this record system, over all primes at once, is one finite
p-free list. (A consumer building a linear solve INDEXED by these records therefore has
one p-independent finite index set. Whether such a solve's coefficients and pivots are
also p-independent is an ambient-theory matter — see (VAL-DIV), §6 — no such claim is
made, proved, or used in this package.)

## §1 Definitions

Fix n ≥ 1. All numbered clauses below are (in)equalities between nonnegative integers,
parameterized by n only.

**D1 (letters).** A *letter* is a tuple
s = (tag, D, w, W, e, s₀, ℓ, a, d, S, λ, sel, F_L, F_R) where
tag ∈ {ROOT, INC, REC}; D, w, W, e, ℓ, d ∈ ℤ≥1; s₀, a ∈ ℤ≥0; S a finite subset of ℤ≥0;
λ a finite nonempty multiset of pairs (g, μ) ∈ ℤ≥1 × ℤ≥1; sel either the symbol ⊥ or a
pair belonging to λ; F_L, F_R finite (possibly empty) sequences of positive integers.
Write w′ := e·ℓ. The tuple must satisfy:

- (C1) Σ F_L = s₀ and s₀ + w′ + Σ F_R = W.
- (C2) a = ⌊s₀ / e⌋.
- (C3) S = {a, a+1, …, a+ℓ} and d = ℓ + 1.
- (C4) Σ_{(g,μ) ∈ λ} g·μ = ℓ (sum with multiplicity).
- (C5) sel = ⊥ ⟺ W = 1.
- (B1) D ≤ n.  (B2) w ≤ n.
- (B3) s₀ + w′ ≤ W;  a + ℓ ≤ W;  d ≤ w′ + 1;  W ≤ ⌊n/D⌋.
- (B4) if sel = (g, μ) then g·μ ≤ ℓ.
- (B5) e ≤ n; ℓ ≤ n; s₀ ≤ n; d ≤ n + 1; W ≤ n; every (g, μ) ∈ λ has g ≤ n and μ ≤ n;
  e ≤ w′; a ≤ ⌊(W − w′)/e⌋.

(Some clauses are implied by others — e.g. the first clause of (B3) by (C1), (B4) by
(C4) + sel ∈ λ, d ≤ w′+1 by (C3); the redundancy is retained deliberately, for fidelity
to the source system. Note W ≤ ⌊n/D⌋ ⇒ D·W ≤ n.)

**D2 (stage; root letters).** stage(s) := (tag, D, w, W). A *root letter* is a letter
with tag = ROOT and (D, w, W) = (1, 1, n). A letter with sel = ⊥ is *terminal*, else
*continuing*.

**D3 (successor relation).** For a continuing letter s with sel = (g, μ) and stride
e = e(s), and any letter s′: s → s′ iff
D(s′) = e·g·D(s), w(s′) = g·w(s), W(s′) = μ, and
tag(s′) = INC if e·g ≥ 2, tag(s′) = REC if e = g = 1.
(The relation constrains s′ only through its stage; terminal letters have no
successors.) The *child stage* of s is (INC/REC as above, e·g·D, g·w, μ).

**D4 (the catalogue 𝒮_n).** 𝒮_n := the least set of letters containing every root
letter and closed under →: if s ∈ 𝒮_n and s → s′ then s′ ∈ 𝒮_n. Equivalently: call a
stage *reachable* if it is (ROOT, 1, 1, n) or the child stage of some member of 𝒮_n;
𝒮_n = all letters whose stage is reachable.

**D5 (menu graph).** Vertex set 𝒮_n; one directed edge s → s′ for each pair in the
successor relation. A *self-loop* is an edge s → s.

**D6 (full letters).** A letter is *full* if sel = (1, W).

**D7 (walks and collapse).** A *walk* is a finite or infinite sequence s₁ → s₂ → … in
the menu graph. Its *collapse* replaces each maximal run of consecutive EQUAL letters
by one occurrence. A *collapsed walk* is a walk with no two consecutive equal letters.

**D8 (skeletons).** A *skeleton* is a finite rooted tree T, a labeling s(·) of its
nodes by members of 𝒮_n, and a partial annotation v(·) of its LEAVES by symbols from
{z, ep, ns}, such that:
- (S1) the root's label is a root letter;
- (S2) for every edge ν → ν′ (child), s(ν) → s(ν′) in the menu graph — in particular
  s(ν) is continuing and every child's label sits at the child stage of s(ν);
- (S3) SIBLING COHERENCE: for each node ν with selection sel(s(ν)) = (g, μ), the
  children of ν are partitioned into *groups*; all labels within one group share the
  fields (e, s₀, ℓ, a, d, S, λ, F_L, F_R) — call these the group's side data — and
  differ only in sel; for each pair (g′, μ′), the number of children in a group G whose
  label selects (g′, μ′) is at most the multiplicity of (g′, μ′) in G's λ; and the
  intervals [s₀(G), s₀(G) + e(G)·ℓ(G)) of distinct groups are pairwise disjoint
  subintervals of [0, μ);
- (S4) COLLAPSEDNESS: no edge has s(ν′) = s(ν);
- (S5) annotations sit on leaves only.
Sk(n) := the set of skeletons up to isomorphism of labeled annotated rooted trees
(children unordered).

**D9 (pre-skeletons; NEW in rev 2).** A *pre-skeleton* is a rooted tree T̂ — finite or
infinite; "tree" means every non-root node has one parent and every node has a finite
path to the root — with a labeling s(·) of nodes by members of 𝒮_n and a partial
annotation v(·) of its leaves by {z, ep, ns}, satisfying (S1), (S2), (S3), (S5) of D8.
(So a skeleton is exactly a FINITE pre-skeleton that also satisfies (S4).)

**D10 (run-collapse of a pre-skeleton; NEW in rev 2).** Let T̂ be a pre-skeleton. A
node is an *entry node* if it is the root or its label differs from its parent's label.
Every node ν has a finite chain of ancestors-or-self containing at least one entry node
(the root), hence a unique deepest one: ent(ν). For an entry node x, the *run* of x is
run(x) := {ν : ent(ν) = x} — equivalently (checked in Lemma T′, step 0) the set of
descendants-or-self ν of x such that every label on the path x → ν equals s(x). The
*collapse* T̄ of T̂ is:
- nodes: the entry nodes of T̂; root: the root of T̂;
- parent of a non-root entry node x: parent_T̄(x) := ent(parent_T̂(x)) — a strict
  T̂-ancestor of x, so iterating parent_T̄ strictly decreases depth and terminates at
  the root: T̄ is a rooted tree;
- labels: s(·) restricted to entry nodes;
- annotations: v̄(x) := v(ν) if run(x) is finite, its deepest member ν is a leaf of T̂,
  and v(ν) is defined; otherwise v̄(x) is undefined;
- the *run length* |run(x)| ∈ ℤ≥1 ∪ {∞} is recorded as a PARAMETER alongside T̄; it is
  NOT part of T̄'s data (two pre-skeletons differing only in run lengths have the same
  collapse).

Every clause of D1–D10 quantifies over integers, multisets of integer pairs, integer
compositions, and trees labeled by such data, with all bounds functions of n — no
prime, residue field, or valuation appears. This is the p-independence asserted in
Theorems 1 and 3; the verifier should confirm it by inspection.

## §2 Theorem 1 and proof

**Theorem 1.** The set of ALL letters (D1) with parameter n — hence a fortiori
𝒮_n ⊆ it — has at most (n+2)^{n²+3n+12} members, and its definition mentions no prime.

*Proof.* We inject letters into integer vectors of length n²+3n+12 with entries in
{0, 1, …, n+1} (that is, n+2 possible values per entry).

Ranges first: tag encodes as 0/1/2 ≤ n+1 (n ≥ 1). D, w ≤ n by (B1)/(B2); W, e, ℓ, s₀ ≤ n
by (B5); a ≤ a + ℓ ≤ W ≤ n by (B3); d ≤ n+1 by (B5). By (C3) and a + ℓ ≤ W ≤ n,
S ⊆ {0, …, n}. For (g, μ) ∈ {1..n}², let c(g, μ) := the multiplicity of (g, μ) in λ;
then c(g, μ)·g·μ ≤ ℓ ≤ n by (C4), so c(g, μ) ≤ n; and every member of λ lies in
{1..n}² by (B5), so the matrix c determines λ. A finite sequence of positive integers
with sum m ≥ 0 corresponds bijectively to the set of its proper partial sums, a subset
of {1, …, m−1}; for F_L the span is s₀ ≤ n and for F_R it is W − s₀ − w′ ≤ W ≤ n
(nonnegative by (C1)), and both spans are recoverable from the fields (s₀; W, s₀, w′),
so each flank is determined by its cut set ⊆ {1, …, n−1}, encoded as an indicator
vector of length n (padded).

The vector: tag (1 entry) + D, w, W (3) + e, ℓ, a, s₀, d (5) + indicator of S (n+1)
+ the matrix c (n² entries) + sel as a pair with ⊥ ↦ (0,0) (2) + two flank indicators
(2n). Total 1+3+5+(n+1)+n²+2+2n = n²+3n+12. Every field of the letter is recovered from
the vector (λ from c; flanks from spans + cut sets; the redundant S, d ride along), so
the map is injective, giving the bound. p-freeness: inspection of D1–D4 (§1, last
paragraph). ∎

Remark (not consumed): dropping the redundant S, d coordinates gives the leaner bound
(n+2)^{n²+2n+8}; the stated constant matches the source system's, and only finiteness
is consumed downstream.

## §3 Theorem 2 and proof

**Theorem 2.** In the menu graph on 𝒮_n:
(i) at each fixed stage there is at most one full letter, and its remaining fields are
forced: e = 1, s₀ = a = 0, ℓ = W, d = W+1, S = {0..W}, λ = {(1, W)} (as a multiset with
one member), F_L = F_R = (); moreover a full letter has W ≥ 2;
(ii) the self-loops are exactly the full letters of tag REC;
(iii) define ρ(s) := (D, t, n−W, φ) ∈ ℤ⁴, where t = 0/1/2 for tag ROOT/INC/REC and
φ = 0 if s is full, else 1, ordered lexicographically. Then ρ strictly increases along
every non-self-loop edge. Consequently the menu graph minus self-loops is acyclic;
every collapsed walk has pairwise-distinct letters and length ≤ |range ρ| ≤
n·3·n·2 = 6n²; and the number of collapsed walks is ≤ (|𝒮_n| + 1)^{6n²}.

*Proof.* (i) Let sel = (1, W). By (C5), W ≠ 1, so W ≥ 2. By (B4), 1·W ≤ ℓ; by (B3),
a + ℓ ≤ W with a ≥ 0, so ℓ ≤ W; hence ℓ = W and a = 0. By (C4), the members of λ sum
(g·μ-weighted) to ℓ = W, and the member (1, W) already contributes W, so λ = {(1, W)}.
By (B3), s₀ + e·ℓ ≤ W with e·ℓ = e·W, forcing e = 1 and s₀ = 0. By (C1), F_L is a
composition of 0 (empty) and Σ F_R = W − 0 − W = 0 (empty). (C2)/(C3) force a = 0,
d = W+1, S = {0..W}. Every field is thus determined by (tag, D, w, W).

(ii) If s → s then, comparing stages: D = e·g·D forces e·g = 1 (D ≥ 1), so e = g = 1
and tag(s) = REC (D3's tag rule); and W = μ, so sel = (g, μ) = (1, W): s is full of tag
REC. Conversely a full REC letter s has e = 1 (part (i)) and sel = (1, W), so its child
stage is (REC, 1·1·D, 1·w, W) = stage(s); since s is a letter at that stage, D3 gives
s → s.

(iii) Let s → s′ with s′ ≠ s, sel(s) = (g, μ), e = e(s).
Case e·g ≥ 2: D(s′) = e·g·D > D. Rank rises in the first coordinate.
Case e = g = 1 and μ < W(s): D(s′) = D; tag(s′) = REC so t′ = 2 ≥ t; if t < 2 the
second coordinate rises; if t = 2 then n − W(s′) = n − μ > n − W(s), the third rises
with the first two equal.
Case e = g = 1 and μ = W(s): then sel(s) = (1, W(s)), i.e. s is full, φ(s) = 0. Here
D(s′) = D, w(s′) = w, W(s′) = W(s), tag(s′) = REC. If t < 2 the second coordinate
rises. If t = 2, then s and s′ share the stage (REC, D, w, W); by (i)'s uniqueness and
s′ ≠ s, s′ is not full, so φ(s′) = 1 > 0 = φ(s), the fourth coordinate rises with the
first three equal.
In all cases ρ(s) <_lex ρ(s′). A directed cycle avoiding self-loops would force
ρ(s) <_lex ρ(s), absurd — acyclicity. Along a collapsed walk consecutive letters are
distinct, so ranks strictly increase and all letters are pairwise distinct; the walk
length is at most |range ρ| ≤ (#D values)·(#t)·(#(n−W))·(#φ) = n·3·n·2 = 6n²
(D ∈ {1..n} by (B1)+D ≥ 1; W ∈ {1..n} so n−W ∈ {0..n−1}). Counting: a collapsed walk
is a sequence of ≤ 6n² letters, so there are ≤ Σ_{k ≤ 6n²} |𝒮_n|^k ≤ (|𝒮_n|+1)^{6n²}
of them. ∎

## §4 The tree level: Lemmas B, L, E, T, T′ and Theorem 3

Throughout, ν is a node with label s(ν); for continuing labels write
sel(s(ν)) = (g, μ), stride e, key degree D.

**Lemma B (branching; scope: PRE-skeletons — finiteness never used).** Every node of a
pre-skeleton (D9) has at most μ ≤ n children (μ = its label's selection multiplicity);
terminal-labeled nodes have none.

*Proof.* Terminal labels have no successors (D3), so no children by (S2). For a
continuing ν, count children by (S3)'s groups. Within a group G, the number of children
is Σ_{(g′,μ′)} #{children in G selecting (g′,μ′)} ≤ Σ_{(g′,μ′) ∈ λ_G} 1 (with
multiplicity) = |λ_G| ≤ Σ_{(g′,μ′) ∈ λ_G} g′·μ′ = ℓ_G by (C4) (every member has
g′μ′ ≥ 1). Distinct groups have disjoint intervals of lengths e_G·ℓ_G inside [0, μ),
so Σ_G e_G·ℓ_G ≤ μ, hence #children ≤ Σ_G ℓ_G ≤ Σ_G e_G·ℓ_G ≤ μ ≤ n ((B5) on the
parent's λ member). Scope note: the proof used only (S2), (S3), (C4), (B5), D3 — all AT
the node ν; neither finiteness of the tree nor (S4) entered. So the bound holds at
every node of every pre-skeleton, in particular of every skeleton. ∎

**Lemma L (leaf budget and node count; scope: skeletons, i.e. finite).** Every skeleton
has at most n leaves and at most 6n³ nodes.

*Proof.* Define the selection budget σ(ν) := e·g·μ·D if s(ν) is continuing, σ(ν) := 1
if terminal.
(a) At the root: D = 1, W = n (S1); g·μ ≤ ℓ by (B4); so σ = e·g·μ ≤ e·ℓ = w′ ≤ W = n
by (B3). (If the root is terminal — forced when n = 1 — then σ = 1 ≤ n.)
(b) For a continuing node ν with children: the children sit at the child stage with key
degree D′ = e·g·D and window W′ = μ (D3). If μ = 1: every letter at that stage is
terminal ((C5)), and by Lemma B there is at most one child; so Σ_{children} σ = 1 ≤
e·g·D·μ = σ(ν) (all factors ≥ 1). If μ ≥ 2: every child label is continuing ((C5)),
with σ(ν′) = e″·g″·μ″·D′ where e″ = e_G is its group's stride and (g″, μ″) its
selection. Within a group G, the multiplicity cap of (S3) gives
Σ_{ν′ ∈ G} g″·μ″ ≤ Σ_{(g′,μ′) ∈ λ_G} g′·μ′ = ℓ_G by (C4); so
Σ_{ν′ ∈ G} σ(ν′) ≤ D′·e_G·ℓ_G, and summing groups (disjoint intervals in [0, μ)):
Σ_{children} σ(ν′) ≤ D′·Σ_G e_G·ℓ_G ≤ D′·μ = e·g·D·μ = σ(ν).
(c) By induction on the (finite) subtree: #leaves(ν) ≤ σ(ν). Leaves: 1 ≤ σ. Internal:
#leaves(ν) = Σ_{children} #leaves(ν′) ≤ Σ σ(ν′) ≤ σ(ν) by (b).
So #leaves(T) ≤ σ(root) ≤ n by (a). Node count: every node is an ancestor-or-self of
some leaf; along a root-to-leaf path consecutive labels are distinct ((S4)) menu-edge
neighbors ((S2)), so by Theorem 2(iii) the path has ≤ 6n² nodes; hence
#nodes ≤ (#leaves)·6n² ≤ 6n³. ∎

**Lemma E (equal-label children are only children; NEW in rev 2).** Let T̂ be a
pre-skeleton, ν a node, ν′ a child of ν with s(ν′) = s(ν) =: s. Then s has a self-loop
— hence is full of tag REC with all fields forced as in Theorem 2(i) — and ν′ is the
ONLY child of ν.

*Proof.* By (S2), s → s: a self-loop. By Theorem 2(ii) s is full of tag REC; by 2(i),
e(s) = 1, s₀(s) = 0, ℓ(s) = W(s), λ(s) = {(1, W(s))}, sel(s) = (1, W(s)), and
W(s) ≥ 2. In (S3) at ν the selection is sel(s) = (g, μ) = (1, W(s)), so μ = W(s).
Groups: ν′'s group has side data equal to the corresponding fields of s (ν′'s label IS
s), so its interval is [s₀, s₀ + e·ℓ) = [0, W(s)) = [0, μ) — the full window. A second
group would need its interval — nonempty, since e·ℓ ≥ 1 — to be a subinterval of
[0, μ) disjoint from [0, μ): impossible. So ALL children of ν lie in ν′'s group and
share its side data, in particular λ = {(1, W(s))}. By (S2) every child's label sits at
the child stage of s, whose window is μ = W(s) ≥ 2, so by (C5) no child is terminal;
by D1 each child's sel is then a member of its λ = {(1, W(s))}, i.e. every child
selects (1, W(s)). (S3)'s multiplicity cap bounds the children selecting (1, W(s)) by
the multiplicity of (1, W(s)) in λ, which is 1. So ν′ is the only child. ∎

**Lemma T (walk tails; rev-2 wording).** Any walk in the menu graph (finite or
infinite) has at most 6n² maximal runs of consecutive equal letters. In particular an
infinite walk is eventually constant, and its final (infinite) run's letter has a
self-loop.

*Proof.* Collapsing any finite prefix yields a collapsed walk, of length ≤ 6n² by
Theorem 2(iii); so no prefix has more than 6n² runs, hence neither does the whole
sequence. An infinite walk therefore has an infinite final run; that run contains
consecutive equal letters s → s — an edge of the walk, i.e. a self-loop. (Nothing is
claimed for singleton runs: a run of length 1 need not have a self-loop letter. Nothing
below needs it: tree-level collapse rides Lemma E, where the self-loop comes directly
from (S2) at an equal-label EDGE.) ∎

**Lemma T′ (the collapse theorem; NEW in rev 2).** Let T̂ be any pre-skeleton — finite
or infinite — and T̄ its collapse (D10). Then T̄ is a skeleton; in particular its
isomorphism class is a member of the finite set Sk(n), and it has ≤ n leaves and ≤ 6n³
nodes. Run lengths take values in ℤ≥1 ∪ {∞} and are parameters, not data of T̄.

*Proof.* Step 0 (the two descriptions of run(x) in D10 agree). Let x be an entry node
and ν a descendant-or-self of x. If every label on the path x → ν equals s(x), then
every node y with x < y ≤ ν has s(y) = s(parent(y)), so y is not an entry node, and
ent(ν) = x. Conversely if ent(ν) = x then every y with x < y ≤ ν is a non-entry node,
so s(y) = s(parent(y)); induction down the path gives all labels equal to s(x).

Step 1 (runs are chains). Suppose ν, ν′ ∈ run(x) are incomparable in the ancestor
order. Their deepest common ancestor z satisfies x ≤ z, and z ∈ run(x) (z lies on the
path x → ν, all of whose labels are s(x) by step 0). The children c ≠ c′ of z on the
paths toward ν and ν′ also lie on those paths, so s(c) = s(c′) = s(x) = s(z). Lemma E
at z (equal-label child c) makes c the ONLY child of z — contradicting c′ ≠ c. So
run(x) is a chain; it is closed under taking parents down to x (step 0), so its
consecutive members are parent–child: run(x) = {x = ν₀, ν₁, …}, ν_{i+1} a child of
ν_i, either finite with final member ν_k or infinite.

Step 2 (children in T̄). By Lemma E, each non-final member ν_i has its run-internal
equal-label child ν_{i+1} as its ONLY child. Hence: if run(x) is infinite, no member
has any child outside the run, so x has NO children in T̄. If run(x) is finite with
final member ν_k, every T̂-child c of ν_k has s(c) ≠ s(ν_k) (an equal-label child
would lie in run(x) by step 0, contradicting finality of ν_k), so each such c is an
entry node with parent_T̄(c) = ent(ν_k) = x. The T̄-children of x are therefore
EXACTLY the T̂-children of ν_k.

Step 3 ((S1)–(S5) for T̄). (S1): T̄'s root is T̂'s root, same label. (S2)+(S4): a
T̄-child c of x is a T̂-child of ν_k with s(ν_k) = s(x) (step 0), so T̂'s (S2) gives
s(x) → s(c), and s(c) ≠ s(x) (step 2). (S3): the T̄-children of x are the T̂-children
of ν_k, with the same labels; s(ν_k) = s(x) has the same selection (g, μ); so T̂'s
(S3) at ν_k transfers verbatim to x in T̄. (S5): v̄(x) is defined only when run(x) is
finite with final member ν_k an annotated leaf; then ν_k has no children, so by step 2
x is a T̄-leaf.

Step 4 (finiteness). Along any root-to-node path x₀, …, x_m in T̄, consecutive labels
are menu-edge related and distinct (step 3), so s(x₀), …, s(x_m) is a collapsed walk:
m + 1 ≤ 6n² by Theorem 2(iii) — every T̄-node has depth < 6n². Every T̄-node has ≤ n
children: its T̄-children are the T̂-children of ν_k (step 2), bounded by Lemma B at
ν_k (pre-skeleton scope). By induction on d, T̄ has ≤ n^d nodes at depth d, so
|T̄| ≤ Σ_{d=0}^{6n²−1} n^d < ∞. No appeal to König's lemma or choice is made.

Step 5 (conclusion). T̄ is a finite labeled annotated rooted tree satisfying
(S1)–(S5): a skeleton (D8), so its class lies in Sk(n); Lemma L gives ≤ n leaves and
≤ 6n³ nodes. Run lengths lie in ℤ≥1 ∪ {∞} by D10, recorded outside T̄'s data. ∎

**Theorem 3.** |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}, and D8 mentions no prime.

*Proof.* By Lemma L a skeleton has N ≤ 6n³ nodes. Choosing any linear order on each
node's children maps every isomorphism class to at least one ORDERED rooted tree on N
nodes with node labels in 𝒮_n and leaf annotations in {∅, z, ep, ns}; distinct classes
never share an ordered representative, so #classes ≤ #(ordered labeled annotated
trees). The number of ordered rooted trees on N nodes is the Catalan number
C_{N−1} ≤ 4^N; labels contribute ≤ |𝒮_n|^N and annotations ≤ 4^N. Hence
|Sk(n)| ≤ Σ_{N=1}^{6n³} 16^N·|𝒮_n|^N ≤ (16·|𝒮_n|)^{6n³+1}
≤ ((n+2)^4·(n+2)^{n²+3n+12})^{7n³} = (n+2)^{7n³(n²+3n+16)},
using Theorem 1, 16 ≤ (n+2)^4, and 6n³+1 ≤ 7n³ for n ≥ 1. p-freeness: §1's closing
inspection covers D8 (and D9/D10). ∎

## §5 The displayed interface (consumed, NOT to be verified here)

> **(COMP) — completeness of the record system (the package's ONE consumed semantic
> condition).** For every prime p and every monic separable-or-not degree-n polynomial
> f over ℤ_p: the canonical OM/cluster classification tree of f — nodes = the reads of
> the higher-Newton-polygon factorization process, branching = one child per
> (window-polygon side, distinct irreducible residual factor) pair, halted branches
> carrying verdicts from {z, ep, ns} — is, with each read's value-free record as its
> node label and the verdicts as leaf annotations, a PRE-SKELETON in the sense of D9:
> the first read's record is a root letter (S1); consecutive reads' records are
> menu-edge related (S2); sibling reads obey (S3) (they read sides of ONE polygon, with
> disjoint spans, selecting distinct factors); verdicts sit on halted ends only (S5).

**Status and residual, disclosed in full.** (COMP) is NOT proved here, and the verifier
is not asked to re-derive it. Its standing in the source project: the per-branch half
(each read's record is a letter; consecutive records are menu-edge related) is a
theorem there (dual-verified, named SP-COMP), itself still conditional on exactly ONE
undischarged residual — the TOTALITY of the verdict-pinning rule (that the rule assigns
every halted branch its verdict). The sibling half ((S3)) is the source project's
canonical-tree branching architecture (dual-accepted). The honest chain:

  Corollary below ⇐ (COMP) ⇐ SP-COMP + branching architecture ⇐ verdict-pin totality.

Every consumer of the Corollary inherits the entire chain. Theorems 1, 2, 3, 5 and
Lemmas B, E, L, T, T′ consume NO part of it (audit item 10).

**Corollary (conditional exactly on (COMP)).** For every prime p and every monic
degree-n f over ℤ_p, the run-collapse of f's classification tree is a member of the
ONE p-independent finite set Sk(n). Moreover Sk(n) is a SUPERSET menu: its clauses are
necessary conditions, so membership of a shape in Sk(n) never asserts realizability at
any particular p — which members carry mass at a given p is value data (the consumer
zero-extends over unrealized members).

*Proof.* (COMP) states that the realized tree, so labeled and annotated, is a
pre-skeleton — finite or infinite branches alike. Lemma T′ collapses it to a skeleton,
a member of Sk(n), with run lengths exported as parameters in ℤ≥1 ∪ {∞}. ∎

## §6 Theorem 5: the Serre envelope; the wild corner with the proved/ambient boundary

**Proposition (Serre, *Local Fields* (GTM 67), Ch. III §6, Prop. 13 — cited, standard).**
Let L/K be a finite totally ramified separable extension of degree e of complete
discretely valued fields, residue characteristic p. The different exponent
d = v_L(𝔇_{L/K}) satisfies e − 1 ≤ d ≤ e − 1 + v_L(e), and d = e − 1 iff p ∤ e.

**Theorem 5.** Let K be complete discretely valued, v_K(p) = 1, residue field perfect
of characteristic p, and L/K separable of degree m = e·f ≤ n (e = ramification index,
f = residue degree). Then
v_K(disc(L/K)) ≤ f(e−1) + f·e·v_p(e) = (m − f) + m·v_p(e) ≤ (m−1) + m·v_p(m)
≤ (m−1) + m·log₂ m ≤ (n−1) + n·log₂ n.
In particular B(n, p) := max_{m ≤ n} [(m−1) + m·v_p(m)] ≤ (n−1) + n·log₂ n for every
prime p, with B(n, p) = n − 1 whenever p > n (the tame case).

*Proof.* Let K^ur be the maximal unramified subextension of L/K, so [K^ur : K] = f and
L/K^ur is totally ramified of degree e. Unramified extensions have trivial different
and the different is multiplicative in towers (Serre III §4, Prop. 8), so
𝔇_{L/K} = 𝔇_{L/K^ur}. Then disc(L/K) = N_{L/K}(𝔇_{L/K}), and
v_K(N_{L/K}(𝔪_L^d)) = f·d, so v_K(disc) = f·d with d = v_L(𝔇_{L/K^ur}) ≤
e − 1 + v_L(e) by the Proposition (residue extension trivial, hence the separability
hypothesis holds). Since e ∈ ℤ and v_{K^ur} = v_K on integers with v_K(p) = 1,
v_L(e) = e·v_{K^ur}(e) = e·v_p(e). So v_K(disc) ≤ f(e−1) + f·e·v_p(e). Now f ≥ 1 gives
m − f ≤ m − 1; e | m gives v_p(e) ≤ v_p(m); and p^{v_p(m)} ≤ m with p ≥ 2 gives
v_p(m) ≤ log₂ m. Monotonicity in m ≤ n gives the envelope; p > n ≥ m ≥ e forces
p ∤ e, v_p(m) = 0. ∎

(The upper bound is achieved: x^{2^k} − 2 over ℚ₂ has e = 2^k, d = e − 1 + e·k, e.g.
e = 4: d = 11 = 3 + 4·2 — so the wild excess term is not slack.)

**The wild corner — exactly what is PROVED (theorem-grade, to audit):**
1. No clause of D1–D10 records a different exponent, discriminant valuation, slope
   height, digit value, or run length; run lengths appear only as the D10 collapse
   PARAMETER, with domain ℤ≥1 ∪ {∞} — an integer domain fixed by the definitions,
   independent of p. D1–D10 mention no prime (§1 closing inspection).
2. Nothing in D1–D10 or Theorems 1–3 assumes tame ramification; no clause degenerates
   at p ≤ n. The residual pattern λ is well-typed at every p because residue fields of
   local fields are finite, hence perfect (irreducible residual factors are separable;
   repeated factors are carried by the multiplicity coordinate μ, at tame and wild p
   alike).
3. Theorem 5 is a p-uniform envelope for ONE family of forgotten values — the
   discriminant/different budgets of realized extensions of degree ≤ n — with all
   wildness confined to the m·v_p(e) term. It does NOT bound other omitted quantities
   (run lengths may be infinite; slope heights are unbounded over varying f), and it is
   consumed by NO theorem or lemma of this package (audit item 9).
4. Historical note (orientation only): an earlier proof of menu finiteness in a coarser
   vocabulary consumed Theorem 5 to cap its recursion depth. In the present vocabulary
   the depth cap is Theorem 2(iii) — pure integer combinatorics — and Theorem 5 is
   pinned only as the value-side envelope statement above.

**(VAL-DIV) — the value-division picture (AMBIENT CLAIM — NOT a theorem of this
package; consumed by NOTHING in it; recorded so the package's scope is unmistakable).**
The ambient project intends the division: every p-dependence of the assembled
factorization/density theory sits in VALUES attached to the p-free index sets — which
letters/skeletons carry mass at a given p, the masses as functions of the residue
cardinality, the distributions of parameters on intended p-free domains (slope heights
in ℕ², normalized slopes in (1/lcm(1,…,n))·ℤ, run lengths in ℤ≥1 ∪ {∞}) — and never
in 𝒮_n, the menu graph, or Sk(n). Of that picture, THIS package proves exactly: the
index sets are finite and p-free (Theorems 1–3), and run lengths enter only as the D10
parameter with p-free domain ℤ≥1 ∪ {∞} (Lemma T′). The height/slope domain clauses and
the exhaustiveness of the division are semantic assertions about the factorization
process — neither defined nor provable from D1–D10; the verifier is NOT asked to
assess them, only to confirm that no displayed proof uses them. Likewise no claim is
made here about the coefficients, pivots, or resummations of any solve built over
these index sets; this package supplies the index set alone.

## §7 Verification checklist

1. §1 p-freeness: confirm by inspection that D1–D10 mention only n and integer data.
2. Theorem 1: the entry ranges (each listed field within {0..n+1}), the flank cut-set
   bijection (span recoverability from (C1)), and injectivity of the encoding.
3. Theorem 2(i): the forcing chain (W ≥ 2 via (C5); ℓ = W and a = 0 via (B4)+(B3);
   λ = {(1,W)} via (C4); e = 1, s₀ = 0 via (B3); flanks empty via (C1)).
4. Theorem 2(iii): the three-case rank analysis — especially the last case's appeal to
   same-stage uniqueness (that s′ shares ALL FOUR stage coordinates with s, including
   w(s′) = 1·w = w).
5. Lemmas B and L: the ledger inequalities — especially (C4)'s use as an equality with
   multiplicity, the μ = 1 corner (terminal children), that group strides e_G enter
   through e_G·ℓ_G ≤ interval length — and Lemma B's scope note (no finiteness used).
6. Lemma E: the self-loop obtained from (S2) alone at an equal-label edge; the forcing
   via Theorem 2(i)/(ii); the exclusion of terminal siblings (child window
   μ = W(s) ≥ 2 + (C5)); the single-group and multiplicity-1 steps.
7. D10 well-definedness (existence/uniqueness of ent(ν); parent_T̄ strictly decreases
   depth) and Lemma T′: step 0's equivalence, step 1's chain argument, step 2's
   only-child bookkeeping (infinite runs childless; finite runs export exactly the
   final member's children), step 3's clause-by-clause (S1)–(S5) transfer, step 4's
   finiteness count Σ_{d<6n²} n^d with NO König/choice appeal, step 5's application of
   Lemma L.
8. Lemma T (walks) and Theorem 3's counting (Catalan bound, geometric sum, exponent
   arithmetic).
9. Theorem 5: the tower computation and the envelope inequalities; AND the independence
   claim — that no step of Theorems 1–3 or Lemmas B/E/L/T/T′ consumes Theorem 5 or any
   tameness hypothesis.
10. Conditionality hygiene: the ONLY consumed semantic input is (COMP), displayed in §5
    with its residual chain, consumed exclusively by the §5 Corollary; (VAL-DIV) (§6)
    is consumed by nothing; Theorems 1, 2, 3, 5 and all lemmas must stand without both.

**Status labels.** Theorems 1 and 2 restate, with complete proofs, results established
in the source project (its letter-finiteness and DAG lemmas); Lemmas B, L, T and
Theorem 3 are compositions claimed new by rev 1 of this package (a prior hostile pass
verified Theorems 1–3 and 5 correct); D9, D10, Lemma E, and Lemma T′ are claimed new
by rev 2 (they formalize what rev 1 left informal); Theorem 5's Proposition is
classical (Serre), its corollary form known in the source project; the §6 analysis is
exposition with its proved/ambient boundary drawn. Numerical evidence (reproducible by
re-implementing D1–D5 as a ~150-line enumerator): catalogue sizes |𝒮_n| = 1, 15, 53,
197, 509, 1460 for n = 1..6, with |𝒮₃| = 53 matching a sealed hand catalogue built
independently in the source project; the self-loop characterization and rank
monotonicity hold on all built edges (8224 at n = 6); the longest collapsed path is
exactly 2n for 2 ≤ n ≤ 6 (versus the proved 6n² — an observed pattern, a conjecture,
consumed nowhere).
