# O13 Phase-B attempt — skeleton/menu finiteness at general n (leaf O-13)

*(2026-07-31, Phase-B prover, THE MATHEMATICAL COMPLETION campaign. Leaf per
`docs/MATH_COMPLETION_TREE_2026-08-01.md` §2.3/§3 item 14: "the set of species-skeletons
(tree shapes with letter data) at degree n is finite, p-independent"; census row
`hfin : Finite (Skeleton n)`; June B-6's modern face. Companion self-contained package
for the adversarial verifier: `O13_phaseB_verifybrief.md`. Falsifier artifact:
`O13_menu_check.py` (this directory), run FIRST per the charge — all checks PASS.)*

## VERDICT: PROVED (document level), with the inherited conditionality displayed

The leaf's claim is proved at general n in the T-4 (§M-SPECIES) vocabulary, at three
nested levels — letters, branch words, and TREE skeletons — each finite with an explicit
p-free bound. The one non-obvious discovery: **the Serre different bound is NOT needed
for menu finiteness** in the modern vocabulary (the tree's expected reduction
anticipated it for the depth cap; the actual depth cap is T-4's SP-DAG rank argument,
pure integer combinatorics). The Serre bound is pinned here anyway (Thm 5) because it is
what certifies the VALUE-side p-uniformity at the wild corner — exactly the "p lands in
the values, not the menu shape" content the leaf charges. Conditionality: the finiteness
theorems are UNCONDITIONAL bookkeeping over the dual-accepted §B2-DEF/§M-SPECIES
vocabulary; only the completeness clause (realized trees spell inside the menu) inherits
T-4 SP-COMP's already-displayed residual (the D4R.0-K(c) verdict pin, owner [3t] VP) —
no NEW conditionality is added by this leaf.

## §0 Grounding (what this leaf is, and who consumes it)

The campaign's target (U-GEN)(iii) produces each density R_σ as the σ-entry of a finite
linear solve (I − K(q))C = b(q) over ℚ(q) "whose state menu, coefficients, and
non-vanishing pivots carry NO dependence on p". O-13 owes the STATE-MENU half: the index
set of that solve — the species letters (states), the menu edges (transitions), and the
tree shapes (assembly patterns) reachable by the OM classifier at degree n — must be ONE
finite list serving every prime, wild included. The Lean-side consumer is the standing
hypothesis row `hfin : Finite (Skeleton n)` (consumed by `MovesV/TV_E2.lean`,
`TV_G3.lean`; `Skeleton n` := a catalogue-membered `MovesSp.Species`, i.e. exactly a
letter of 𝒮_n^raw — so `hfin` = Theorem 1 below; it is Lean-proved only at n = 1, 3
via the sealed catalogue, which is why the tree lists the leaf as open at general n).

Prior state: T-4 (§M-SPECIES, dual-accepted 2026-07-27) already holds two GENERAL-n
theorems — SP-FIN (the letter alphabet 𝒮_n^raw is finite, ≤ (n+2)^{n²+3n+12}, p-free by
typing) and Lemma SP-DAG (the loop-collapsed menu graph is a DAG; every collapsed walk
has ≤ 6n² letters) — plus entrance-word finiteness. What was missing for the leaf's
"tree shapes with letter data": the TREE-level composition (branching bound, leaf
budget, run-collapse well-definedness incl. infinite branches, and the assembled
skeleton count), and the wild-corner analysis with the Serre statement pinned. Those
are this note's new content (Thms 3–5, Lemmas B/L/T).

## §1 FALSIFIER FIRST (per the leaf charge) — all checks PASS

`O13_menu_check.py` enumerates 𝒮_n^raw MECHANICALLY from the (G1)–(G6)+(B1)–(B5)
clauses as transcribed in `lean/LeanUrat/MovesSp/Defs.lean` (the E-phase transcription
of the dual-accepted rev-8 §M-SPECIES text), builds the menu graph, and checks the
load-bearing lemmas. Results (2026-07-31, python3, this machine):

| n | \|𝒮_n^raw\| | reachable stages | longest collapsed path | SP-DAG bound 6n² | menu edges |
|---|------------|------------------|------------------------|------------------|-----------|
| 1 | 1          | 1                | 1                      | 6                | 0         |
| 2 | 15         | 5                | 4                      | 24               | 21        |
| 3 | **53**     | 8                | 6                      | 54               | 121       |
| 4 | 197        | 18               | 8                      | 96               | 616       |
| 5 | 509        | 26               | 10                     | 150              | 2246      |
| 6 | 1460       | 36               | 12                     | 216              | 8224      |

- **Sealed-catalogue reproduction**: |𝒮₃^raw| = 53 exactly, over exactly the 8 sealed
  stages with the sealed group counts (ROOT(1,1,3): 21; POST-REC (1,1,3)/(1,1,2)/(1,1,1):
  21/6/1; POST-INC (2,1,1)/(2,2,1)/(3,1,1)/(3,3,1): 1 each). |𝒮₁| = 1 (the confirming
  root letter, = Lean's `sk1`).
- **Self-loop characterization** (SP-DAG(i)): at every n ≤ 6, {s : s ∈ SUCC(s)} equals
  exactly the set of full POST-REC letters, with every field forced (e = 1, s₀ = a = 0,
  ℓ = W, λ = {(1,W)}, flanks empty) and uniqueness per stage confirmed.
- **Rank monotonicity** (SP-DAG(ii)): ρ = (D, tagord, n−W, 1−[full]) strictly
  lex-increases along ALL non-self-loop edges (8224/8224 at n = 6) ⇒ DAG confirmed.
- **Headroom**: the n = 4 skeleton enumeration (the tree's named falsifier) gives 197
  letters vs the crude bound 6^40 ≈ 1.3×10³¹, and longest collapsed path 8 vs 96. The
  observed longest path is exactly 2n for 2 ≤ n ≤ 6 (recorded as an EMPIRICAL pattern —
  a conjecture, not consumed; 6n² is what is proved and used).
- **Encoding-range audit**: every letter's SP-FIN encoding entries lie in {0..n+1} — the
  encoding proof's premise holds on the built catalogues.
- **Window-locality observation** (new, supports the CTS lumping): the letter count at a
  stage depends only on W (1, 6, 21, 68, 189, 513 for W = 1..6), as the side/residual/
  flank fields are window-local; (tag, D, w) enter only through reachability and the
  W ≤ ⌊n/D⌋ budget.

No check failed; the falsifier found nothing to refute.

## §2 The statement package (full proofs in the verify brief; new proofs also §3 here)

All objects are as in §M-SPECIES SP.1–SP.4 (= `MovesSp/Defs.lean`). Fix n ≥ 1.

- **Theorem 1 (letters; = T-4 SP-FIN, known, restated).** 𝒮_n^raw is finite,
  |𝒮_n^raw| ≤ (n+2)^{n²+3n+12}, and its defining clauses mention no prime: one list
  serves every p. [Discharges the math of the Lean row `hfin : Finite (Skeleton n)`.]
- **Theorem 2 (branch words; = T-4 SP-DAG, known, restated).** Self-loop edges are
  exactly the full POST-REC letters; ρ = (D, tagord, n−W, 1−[full]) strictly increases
  along every other menu edge; hence the collapsed menu graph is a DAG, every collapsed
  walk has ≤ 6n² pairwise-distinct letters, and the collapsed-word menu has size
  ≤ (|𝒮_n^raw|+1)^{6n²}.
- **Lemma B (branching, NEW).** In a sibling-coherent letter tree, every node has ≤ μ ≤ n
  children (μ = the node's selection multiplicity).
- **Lemma L (leaf budget, NEW).** Every skeleton has ≤ n leaves; hence ≤ 6n³ nodes.
- **Lemma T (tail, NEW).** Along any (even infinite) branch of a realized tree, the
  letter sequence has ≤ 6n² alternations, hence is eventually constant at a self-loop
  letter; loop-collapse therefore sends EVERY realized T_can(f) — non-separable locus
  included — to a FINITE tree.
- **Theorem 3 (skeletons, NEW — the leaf's theorem).** The set Sk(n) of species-skeletons
  (finite rooted trees, nodes labeled by 𝒮_n^raw letters, edges by the menu relation,
  sibling-coherent, run-collapsed, leaves optionally V_term-annotated) is finite:
  |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)} — and p-independent: no clause of its definition
  mentions p. Height pairs (h_r, u*_r) ∈ ℕ², run depths ∈ ℕ∪{∞}, and slope weights in
  the lattice (1/lcm(1..n))ℤ are PARAMETERS on p-free domains, never skeleton data.
- **Theorem 4 (completeness, conditional — inherited only).** For every p and every
  monic degree-n f over ℤ_p, the loop-collapse of T_can(f)'s catalogue-word tree is a
  member of Sk(n). Consumes: T-4 SP-COMP (per-read letter/edge membership; conditional
  on exactly the D4R.0-K(c) verdict-pin residual, owner [3t] VP), the dual-accepted
  §D4-R branching architecture (children = (side, distinct residual factor) pairs of one
  window polygon — sibling coherence), and Lemma T. The skeleton clauses are NECESSARY
  conditions, so Sk(n) is a SUPERSET menu (same discipline as Out): emptiness of a
  listed shape at a given p is value data, zero-extended by the consumer.
- **Theorem 5 (the wild corner; Serre pinned — known ingredients, role analysis new).**
  See §4.

## §3 The new proofs (Lemmas B/L/T, Theorem 3)

**Sibling coherence (the tree-level clause, added to the letter/word data of T-4).**
Children of a node ν are partitioned into GROUPS (the sides of ν's child window):
within a group all letters share the side/residual/flank fields (e, s₀, ℓ, a, λ, flanks)
and differ only in selection; for each shape (g′, μ′) the number of children in a group
selecting (g′, μ′) is at most the multiplicity of (g′, μ′) in the group's λ (distinct
factors, F1 discipline: same-shape factors give EQUAL letters — children form a
multiset); distinct groups' side intervals [s₀, s₀ + eℓ) are pairwise disjoint within
[0, μ), μ = the parent's selection multiplicity (= the child window span, D.8/D.10).
This is exactly the §D4-R L5 polygon geometry (every side listed, disjoint spans), so
realized trees satisfy it; it is stated as a skeleton clause, not proved from letters.

**Lemma B.** #children(ν) = Σ_groups #children(G) ≤ Σ_G |λ_G| ≤ Σ_G ℓ_G ≤ Σ_G e_G·ℓ_G
≤ μ ≤ n. (|λ_G| ≤ Σ_{(g,μ″)∈λ_G} gμ″ = ℓ_G is the partition identity (G4); the last two
steps are e ≥ 1 and the disjoint-intervals clause; μ ≤ n is (B5).) ∎

**Lemma L.** Define the selection budget σ(ν) := e·g·μ·D for a continuing letter
(sel = (g, μ), stride e, key degree D), σ(ν) := 1 for a terminal (⊥) letter. Three
claims: (a) at the root, σ ≤ n: g·μ ≤ ℓ ((B4), sel ∈ λ), so σ = e·g·μ·1 ≤ e·ℓ = w′ ≤ W
= n ((B3)). (b) Σ_{children} σ(ν′) ≤ σ(ν): children sit at stage (D′, ·, μ), D′ = e·g·D.
If μ = 1: all child letters are terminal ((G6)) and by Lemma B there is ≤ 1 child, so
Σ = 1 ≤ σ(ν) (all factors ≥ 1). If μ ≥ 2: all children continuing ((G6));
group by side: Σ_{ν′ ∈ G} e_G·g′μ′·D′ ≤ e_G·D′·Σ_{distinct slots of λ_G} g′μ′
≤ e_G·ℓ_G·D′ (multiplicity-respecting distinctness), and Σ_G e_G ℓ_G ≤ μ (disjoint
intervals), so Σ ≤ D′·μ = σ(ν). (c) #leaves(subtree at ν) ≤ σ(ν), by induction: a leaf
has 1 ≤ σ; an internal node has #leaves = Σ #leaves(ν′) ≤ Σ σ(ν′) ≤ σ(ν) by (b).
Hence #leaves ≤ σ(root) ≤ n. Node count: every node is an ancestor-or-self of some
leaf; by Theorem 2 + run-collapsedness every root-to-leaf path is a collapsed walk,
≤ 6n² nodes; so #nodes ≤ n·6n² = 6n³. ∎

**Lemma T.** Every finite prefix of the branch's letter word is a walk in the menu
graph; collapsing self-loop repeats gives a collapsed walk, ≤ 6n² letters (Thm 2).
So the full (possibly infinite) word has ≤ 6n² blocks of consecutive-equal letters;
an infinite word therefore has an infinite final block, whose letter s satisfies
s ∈ SUCC(s) (consecutive equal letters are a menu self-loop) — the run's collapse is
one node with depth parameter ∞ and no continuation child. ∎
[Corner display: within a run, each node has exactly ONE child: the run letter is full
(Thm 2's characterization), a full child letter spans the whole window ([0, W), flanks
empty), and sibling coherence leaves no disjoint interval for a sibling — so branching
happens only at run exits, and collapsing a maximal run (children of the collapsed node
:= children of its LAST member) is well-defined with no attachment-depth ambiguity.]

**Theorem 3.** By Lemma L a skeleton has ≤ 6n³ nodes; fix a canonical planar order on
children (any). The map (skeleton) ↦ (ordered rooted tree on N ≤ 6n³ nodes, node
labeling by 𝒮_n^raw, leaf annotation by {∅, z, ep, ns}) is injective. #ordered rooted
trees on N nodes = Catalan(N−1) ≤ 4^N; labelings ≤ |𝒮_n^raw|^N; annotations ≤ 4^N. So
|Sk(n)| ≤ Σ_{N≤6n³} 16^N·|𝒮_n^raw|^N ≤ (16·|𝒮_n^raw|)^{6n³+1} ≤ (n+2)^{7n³(n²+3n+16)}
(using |𝒮_n^raw| ≤ (n+2)^{n²+3n+12}, 16 ≤ (n+2)⁴, 6n³+1 ≤ 7n³ at n ≥ 1).
p-independence: every clause quantifies over integers, multisets of integer pairs, and
compositions with bounds in n alone; no prime, no residue field, no valuation appears.
The SAME set Sk(n) therefore serves every p — realizability at a given p (which members
have nonzero mass) is the consumer's value data, zero-extended per the SUPERSET duty. ∎

## §4 The wild corner (Theorem 5): where p enters, and why the menu never sees it

**The pinned classical statement (known — Serre, Local Fields (GTM 67), Ch. III §6,
Prop. 13; verified numerically tight in `L5fix_complete.md` §5(b), e.g. x⁴−2/ℚ₂:
d = 11 = 3 + 4·2).** L/K finite separable totally ramified of degree e, K complete
discretely valued, residue char p. The different exponent d = v_L(𝔇_{L/K}) satisfies
e − 1 ≤ d ≤ e − 1 + v_L(e), with d = e − 1 iff p ∤ e (tame). For a leaf of degree
d° = e·f ≤ n over an absolutely unramified base, tower multiplicativity + trivial
unramified different give the discriminant exponent v_K(disc) ≤ f(e−1) + f·e·v_p(e)
≤ (d°−1) + d°·v_p(d°), hence the June B-6 menu bound
B(n,p) := max_{d°≤n}[(d°−1) + d°·v_p(d°)] ≤ (n−1) + n·log₂ n — p-UNIFORM because
v_p(m) ≤ log_p m ≤ log₂ m (wildness fires only at p | e, so p ≤ e ≤ n).

**Where wildness enters the classifier, exhaustively, and where each entry lands:**
1. **Different/discriminant wild excess** (d°·v_p(d°) above): a VALUE budget on realized
   ramification data. p-uniformly capped by (n−1) + n·log₂ n. Never a letter field.
2. **Residual factorization patterns**: residue fields are finite hence PERFECT, so the
   (degree, multiplicity) multiset λ is well-typed at every p — no separability
   hypothesis is consumed anywhere in (G1)–(G6)/(B1)–(B5). Wild p changes WHICH λ fire
   (e.g. Artin–Schreier-type patterns at p ≤ n, or λ = {(1,1)³} empty at q ∈ {2,3}) —
   realizability, i.e. table VALUES (CTS-M(ii) zero-extension), never the list.
3. **Self-loop run lengths / carry propagation at p ≤ n**: the depth PARAMETERS
   (domains ℕ∪{∞}, p-free); their distributions are p-dependent values, resummed by the
   solve's matrix fixpoint (I − K_e)^{−1}, never bounded and never letter data.
4. **The budgets and stage laws themselves**: (B1)–(B5) and D′ = e·g·D etc. contain no
   tameness hypothesis — they transcribe §B2-DEF move laws proved in the carry-algebra
   language uniformly in p (dual-accepted; consumed as interface).

**Role display (the honest sharpening vs the tree's expected reduction).** The tree
predicted "T-4 entrance-finiteness + B-6's different-bound depth cap compose". They do —
but in the modern vocabulary the depth cap is ALREADY combinatorial (Thm 2's rank
argument), so the Serre bound is not consumed by Thms 1–4 at all. Its live role: (i) it
is the mechanism of the JUNE-vocabulary proof (B-6, `L5fix_complete.md` §2 — that
vocabulary counts recentering levels without collapsing runs, so it genuinely needs the
different cap); (ii) at the modern interface it certifies that even the FORGOTTEN values
(realized ramification budgets) obey a p-uniform envelope — the guarantee that no wild
prime can smuggle p-dependence back in through the parameter side of the menu/parameter
split. Both faces land p-dependence in VALUES; the menu SHAPE is p-free by typing.
That is the leaf's actual content, and it is what (U-GEN)(iii) consumes.

## §5 Conditionality ledger, labels, and consumers

- **Unconditional** (given the dual-accepted §B2-DEF/§M-SPECIES/§D4-R vocabulary as
  DEFINITIONS): Theorems 1, 2, 3, Lemmas B, L, T, the Serre envelope computation.
  No new axiom, no new open lemma is introduced.
- **Conditional, inherited only**: Theorem 4 (completeness) rides T-4 SP-COMP — its sole
  residual is the D4R.0-K(c) verdict pin (owner [3t] via VP), already on the ledger.
  Sibling coherence is consumed from §D4-R's dual-accepted polygon/branching geometry.
- **Labels**: Thm 1/Thm 2/entrance finiteness = (a) known within the campaign (T-4,
  dual-accepted at document level), restated with complete self-contained proofs in the
  brief. Serre Prop. 13 + the B(n,p) bound = (a) known (literature + June B-6). Lemmas
  B/L/T + Theorem 3 + the wild-corner role analysis = (c) claimed new (the composition
  the leaf asked for). Longest-collapsed-path = 2n: numerically-supported CONJECTURE.
- **Consumers**: the Lean hypothesis row `hfin : Finite (Skeleton n)` (TV_E2/TV_G3,
  currently discharged only at n = 1, 3) is mathematically discharged by Theorem 1 at
  every n; formalizing the encoding injection is a finite, mechanical Lean unit (the
  enumerator in `MovesSp/DefsEnum.lean` + a Fintype instance from the encoding map) —
  flagged as the natural follow-up, NOT done here (no Lean edits per charge).
  (U-GEN)(iii)'s "state menu … carries no dependence on p" consumes Thms 1–3;
  the [1v]/CTS templates consume the word menu (Thm 2); [3]'s tree assembly consumes
  Sk(n) (Thms 3–4).

## §6 Files

- `lean/notes/openmath/O13_phaseB_attempt.md` — this note.
- `lean/notes/openmath/O13_phaseB_verifybrief.md` — self-contained verifier package
  (all definitions unfolded, complete proofs, no repo pointers).
- `lean/notes/openmath/O13_menu_check.py` — the falsifier/enumerator (all checks pass,
  n ≤ 6; §1 table reproducible by `python3 O13_menu_check.py`).
