# O13 verification package — finiteness and p-independence of the degree-n species menu

*(Self-contained package for a fresh-context adversarial verifier. Everything needed is
defined below in standard mathematical language; no external documents are required.
Charge: quote-and-classify each defect as CRITICAL ERROR (breaks the chain) or
JUSTIFICATION GAP (assume and continue); fix nothing. §7 lists what to check.)*

## §0 The claim

Fix an integer n ≥ 1. We define below, from the integer n ALONE, a finite alphabet 𝒮_n
of "letters" (Definition D1/D4), a directed "menu" graph on it (D5), and a set Sk(n) of
"skeletons" — finite rooted trees labeled by letters (D8). The claims to verify:

> **Theorem 1.** |𝒮_n| ≤ (n+2)^{n²+3n+12}. The definition of 𝒮_n mentions no prime.
> **Theorem 2.** The menu graph's self-loops are exactly its "full" letters of tag REC;
> after deleting self-loops the graph is acyclic, and every self-loop-free directed walk
> visits ≤ 6n² vertices.
> **Theorem 3.** |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}. The definition of Sk(n) mentions no
> prime.
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
p-free list — so a linear solve indexed by it is a single p-independent finite system.

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

Every clause of D1–D8 quantifies over integers, multisets of integer pairs, and integer
compositions, with all bounds functions of n — no prime, residue field, or valuation
appears. This is the p-independence asserted in Theorems 1 and 3; the verifier should
confirm it by inspection.

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

## §4 The tree level: Lemmas B, L, T and Theorem 3

Throughout, T is a skeleton (D8) and ν a node with label s(ν); for continuing labels
write sel(s(ν)) = (g, μ), stride e, key degree D.

**Lemma B (branching).** Every node of a skeleton has at most μ ≤ n children (μ = its
label's selection multiplicity); terminal-labeled nodes have none.

*Proof.* Terminal labels have no successors (D3), so no children by (S2). For a
continuing ν, count children by (S3)'s groups. Within a group G, the number of children
is Σ_{(g′,μ′)} #{children in G selecting (g′,μ′)} ≤ Σ_{(g′,μ′) ∈ λ_G} 1 (with
multiplicity) = |λ_G| ≤ Σ_{(g′,μ′) ∈ λ_G} g′·μ′ = ℓ_G by (C4) (every member has
g′μ′ ≥ 1). Distinct groups have disjoint intervals of lengths e_G·ℓ_G inside [0, μ),
so Σ_G e_G·ℓ_G ≤ μ, hence #children ≤ Σ_G ℓ_G ≤ Σ_G e_G·ℓ_G ≤ μ ≤ n ((B5) on the
parent's λ member). ∎

**Lemma L (leaf budget and node count).** Every skeleton has at most n leaves and at
most 6n³ nodes.

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
(c) By induction on the subtree: #leaves(ν) ≤ σ(ν). Leaves: 1 ≤ σ. Internal:
#leaves(ν) = Σ_{children} #leaves(ν′) ≤ Σ σ(ν′) ≤ σ(ν) by (b).
So #leaves(T) ≤ σ(root) ≤ n by (a). Node count: every node is an ancestor-or-self of
some leaf; along a root-to-leaf path consecutive labels are distinct ((S4)) menu-edge
neighbors ((S2)), so by Theorem 2(iii) the path has ≤ 6n² nodes; hence
#nodes ≤ (#leaves)·6n² ≤ 6n³. ∎

**Lemma T (tails; run collapse is total, infinite branches included).** Let s₁ → s₂ → …
be any walk in the menu graph (finite or infinite). Then the sequence has at most 6n²
maximal runs of consecutive equal letters. In particular an infinite walk is eventually
constant, at a letter with a self-loop; so collapsing runs sends every walk — infinite
ones included — to a collapsed walk of length ≤ 6n², and (given assumption (COMP) of
§5) every classification tree, including those with non-terminating branches, collapses
to a FINITE skeleton, the infinite final runs becoming childless nodes (their run
lengths, like all run lengths, are parameters in ℕ ∪ {∞}, not skeleton data).

*Proof.* Collapsing any finite prefix yields a collapsed walk, of length ≤ 6n² by
Theorem 2(iii); so no prefix has more than 6n² runs, hence neither does the whole
sequence. An infinite walk therefore has an infinite final run; consecutive equal
letters s → s witness a self-loop. Well-definedness of tree collapse: a run's letter
has a self-loop, hence is full of tag REC (Theorem 2(ii)); by Theorem 2(i) a full
child label spans its whole window (s₀ = 0, e·ℓ = W) — so by (S3)'s disjointness no
sibling group fits beside it: a full child is an only child. Thus every non-final
member of a run has exactly one child (the run's continuation), branching can occur
only at the run's exit, and collapsing the run to one node (children := the last
member's children) loses no branching structure and creates no attachment ambiguity. ∎

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
inspection covers D8. ∎

## §5 The displayed interface (consumed, NOT to be verified here)

> **(COMP) — completeness of the record system (consumed).** For every prime p and
> every monic separable-or-not degree-n polynomial f over ℤ_p: the canonical
> OM/cluster classification tree of f — nodes = the reads of the higher-Newton-polygon
> factorization process, branching = one child per (window-polygon side, distinct
> irreducible residual factor) pair — has the properties: every read's value-free
> record is a letter of 𝒮_n; the first read's record is a root letter; consecutive
> reads' records are menu-edge related; sibling reads obey (S3) (they read sides of ONE
> polygon, with disjoint spans, selecting distinct factors); and halted branches carry
> a verdict from {z, ep, ns}.

(COMP) is a theorem of the source project (its per-branch half is the dual-verified
theorem there called SP-COMP, conditional there on one named residual — the totality of
the verdict-pinning rule; its sibling half is the project's canonical-tree architecture).
It is stated here so the package is honest about what bridges combinatorics to
semantics; the verifier is NOT asked to re-derive it.

**Corollary (conditional exactly on (COMP)).** For every prime p and every monic
degree-n f over ℤ_p, the run-collapse of f's classification tree is a member of the
ONE p-independent finite set Sk(n). Moreover Sk(n) is a SUPERSET menu: its clauses are
necessary conditions, so membership of a shape in Sk(n) never asserts realizability at
any particular p — which members carry mass at a given p is value data (the consumer
zero-extends over unrealized members).

*Proof.* (COMP) gives (S1), (S2), (S3), and the annotation typing for the realized tree
with runs uncollapsed; Lemma T collapses it (finite branches and infinite ones alike)
to a finite labeled tree satisfying (S4) as well — maximal runs collapse to single
nodes, and an exit child never repeats the run letter (it would extend the maximal
run). Lemma L and Theorem 3 bound and enumerate the result. ∎

## §6 Theorem 5: the Serre envelope, and the wild corner

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

**The wild corner — where p enters, and why the menu never sees it (the analysis to
audit, not a new theorem).** The classical worry about "one menu for all p": at wild
primes p ≤ n, ramification invariants blow up relative to tame primes (Theorem 5's
excess m·v_p(m); the count of degree-m extensions explodes by the mass formula), so any
menu that RECORDED ramification data would be p-dependent. The design fact to audit:
1. No clause of D1–D8 records a different exponent, discriminant valuation, slope
   height, digit value, or run length. Wild growth lands in the struck PARAMETERS —
   height pairs in ℕ², run depths in ℕ ∪ {∞}, slopes in the p-free lattice
   (1/lcm(1,…,n))·ℤ (denominators e ≤ n) — whose DOMAINS are p-free; only their
   realized distributions depend on p.
2. Nothing in D1–D8 or Theorems 1–3 assumes tame ramification; no clause degenerates at
   p ≤ n. The residual pattern λ is well-typed at every p because residue fields of
   local fields are finite, hence perfect (irreducible residual factors are separable;
   repeated factors are carried by the multiplicity coordinate μ, at tame and wild p
   alike).
3. Theorem 5 is the value-side guarantee: even the FORGOTTEN ramification budgets obey
   the p-uniform envelope (n−1) + n·log₂ n, with all wildness confined to the m·v_p(m)
   term. So the p-dependence of the assembled theory sits entirely in VALUES (which
   letters/skeletons carry mass at a given p, the masses as functions of the residue
   cardinality q, the parameter distributions) — never in the index sets 𝒮_n, the menu
   graph, or Sk(n), which are one list for all p by construction.
4. Historical note (for orientation only): an earlier proof of menu finiteness in a
   coarser vocabulary consumed Theorem 5 to cap its recursion depth. In the present
   vocabulary the depth cap is Theorem 2(iii) — pure integer combinatorics — and
   Theorem 5 is NOT consumed by Theorems 1–3; verifying that independence is part of
   the audit (§7, item 7).

## §7 Verification checklist

1. §1 p-freeness: confirm by inspection that D1–D8 mention only n and integer data.
2. Theorem 1: the entry ranges (each of the listed fields within {0..n+1}), the flank
   cut-set bijection (span recoverability from (C1)), and injectivity of the encoding.
3. Theorem 2(i): the forcing chain (W ≥ 2 via (C5); ℓ = W and a = 0 via (B4)+(B3);
   λ = {(1,W)} via (C4); e = 1, s₀ = 0 via (B3); flanks empty via (C1)).
4. Theorem 2(iii): the three-case rank analysis — especially the last case's appeal to
   same-stage uniqueness (that s′ shares ALL FOUR stage coordinates with s, including
   w(s′) = 1·w = w).
5. Lemmas B and L: the ledger inequalities — especially (C4)'s use as an equality with
   multiplicity, the μ = 1 corner (terminal children), and that group strides e_G enter
   through e_G·ℓ_G ≤ interval length.
6. Lemma T: the eventually-constant argument and the only-child property of full
   children (Theorem 2(i) + (S3) disjointness); Theorem 3's counting (Catalan bound,
   geometric sum, exponent arithmetic).
7. Theorem 5: the tower computation and the envelope inequalities; AND the independence
   claim — that no step of Theorems 1–3 secretly consumes Theorem 5 or any tameness
   hypothesis.
8. Conditionality hygiene: the ONLY semantic input is (COMP), displayed in §5 and
   consumed only by the §5 Corollary; Theorems 1, 2, 3, 5 must stand without it.

**Status labels.** Theorems 1 and 2 restate, with complete proofs, results established
in the source project (its letter-finiteness and DAG lemmas); Lemmas B, L, T and
Theorem 3 are new compositions claimed by this package; Theorem 5's Proposition is
classical (Serre), its corollary form known in the project; the §6 analysis is new
exposition. Numerical evidence (reproducible by re-implementing D1–D5 as a ~150-line
enumerator): the catalogue sizes |𝒮_n| = 1, 15, 53, 197, 509, 1460 for n = 1..6, with
|𝒮₃| = 53 matching a sealed hand catalogue built independently in the source project;
the self-loop characterization and rank monotonicity hold on all built edges (8224 at
n = 6); the longest collapsed path is exactly 2n for 2 ≤ n ≤ 6 (versus the proved 6n²
— the 2n value is an observed pattern, a conjecture, consumed nowhere).
