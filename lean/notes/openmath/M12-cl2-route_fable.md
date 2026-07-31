# M12-cl2-route — Attempt: weight-charge bookkeeping along classifier routes

Prover: Fable (Claude), 2026-07-31. Companion brief:
`M12-cl2-route_brief.md` (read first; notation from there is reused freely).

**Result in one paragraph.** The route form `X3aRouteP` reduces — by chains
already machine-checked in the corpus — to two statements at the real-classifier
instance: a cap on the recentering count and a mod-p wildness implication. I give
an informal-rigorous proof of both from a four-clause named interface (X1), (X2),
(X3′), (X4) whose clauses are standard Okutsu–Montes facts about the intended
engine, together with an explicit constant s(n) = 2·D(n) + 1 (D(n) = the
key-weight lattice denominator, candidate D(n) | n!, = n on the unramified-frame
slice). The core mechanism is a single telescoping resolution radius priced
against the pair-sum form of the discriminant, v_p(disc f) = 2·Σ_{i<j}
v(θᵢ − θⱼ); it is the branch-general form of the self-loop budget already
paper-proved in-corpus (L5fix Invariant 2), and it deliberately avoids the
adjudicated X1B double-charge trap (no per-node table value is ever summed).
Verdict: **REDUCED** — to (X1)–(X4) at the engine, each a sharply stated open
lemma of the instantiation wave, with the assembly and all valuation-theoretic
steps proved here.

---

## 1. The residual surface after the machine-checked reductions

Everything in this section is compiled, sorry-free, and was re-verified by
reading this pass (file:line as of 2026-07-31):

- KD5 (`Kernels/KD5.lean:38`): X1aAlignP ⟨true,false⟩ ∧ WeightChargeFullP ⟹
  X3aRouteP (right disjunct). The alignment leg is the separate ledger row
  `cl15_align`, so it is a given for THIS obligation.
- KD10 (`Kernels/KD10.lean:50`): KeyWeightData KW + WeightCapP c + REC-DISC +
  (2·KW.D·c ≤ s) ⟹ WeightChargeFullP.
- KD6 (`Kernels/KD6.lean:154`): `countKeyWeight n` — the population count
  w(H) := #recT1(H) + #t4(H) is a compiled KeyWeightData instance with
  lattice denominator KW.D = 1.
- KD2/KD2a (`Kernels/WeightChargeRed.lean`): REC-DISC follows from the named
  hypothesis `RecImpliesWild` plus the unconditional mod-p discriminant lemma.

Instantiating KD10 at `countKeyWeight` (so KW.D = 1, and `WeightCapP` reads
"#recT1(H) + #t4(H) ≤ c·(1 + v_p(disc f))"), the ENTIRE remaining content of
`cl2_route` is exactly:

> **(L-A)** `RecImpliesWild`: on a stratum history of f off disc = 0, one
> recentering-population node forces f mod p to be non-squarefree.
>
> **(L-B)** the count cap: #recT1(H) + #t4(H) ≤ c(n)·(1 + v_p(disc f)) for an
> n-only c(n), on every stratum history off disc = 0.

(then s(n) := any integer ≥ 2·c(n); KD10's case split uses (L-A) to absorb the
"+1" on histories that have any recentering at all). Sections 2–3 prove (L-A)
and (L-B) at the intended instance, modulo the named interface. Everything
below is mathematics about the canonical classification tree; no Lean object is
touched.

## 2. The cluster-side mathematics

### 2.0 Setup and two standard identities

Fix a prime p and f ∈ ℤ_p[x] monic of degree n with disc f ≠ 0. Let
θ₁, …, θ_n ∈ ℚ̄_p be its roots (distinct, integral); v the unique extension of
v_p to ℚ̄_p, v(p) = 1. Define the **pair budget**

    (D1)   P := Σ_{i<j} v(θᵢ − θⱼ)  ∈ (1/D')·ℤ_{≥0},   v_p(disc f) = 2P,

from disc f = Π_{i<j}(θᵢ − θⱼ)²; every summand is ≥ 0 (integrality). [Known.]

    (D2)   v(f'(θᵢ)) = Σ_{j≠i} v(θᵢ − θⱼ) ≤ P            for each i,

from f'(θᵢ) = Π_{j≠i}(θᵢ − θⱼ). [Known.]

    (D3)  (Hensel–Newton certificate) If E/ℚ_p is finite, c ∈ O_E and
          v(f(c)) > 2·v(f'(c)), then f has a unique root θ with
          v(θ − c) = v(f(c)) − v(f'(c)) > v(f'(c)), and the factor x − θ of f
          over E is certified by the data (f(c), f'(c)) alone. [Known: Hensel's
          lemma over complete fields, Newton form.]

### 2.1 The interface (the engine dictionary — the named open lemmas)

The canonical tree T_can(f) is the project's digit-reading Okutsu–Montes engine.
The four clauses below are the exact duties this attempt leaves to the
real-instance wave; each is annotated with the standard-theory fact that makes
it true of the intended engine. H ranges over branch histories, ν over
continuing nodes, "child state of ν" = the engine state after ν's read and
selection.

**(X1) Tracked cluster and resolution radius.** Each branch state carries a
nonempty set S ⊆ {θ₁, …, θ_n} (the tracked roots), a center c (an algebraic
integer in the current frame closure), and a radius r ∈ ℚ_{≥0}, such that every
θ ∈ S satisfies v(θ − c) ≥ r; along the branch S is nested (shrinks) and r is
nondecreasing.
  [Intended reading: S = the roots of the residual-selection chain's factor;
  c = the root of the current key polynomial φ nearest the cluster; the Okutsu
  bound converts the engine's key value into proximity: v(φ(θ)) ≥ w forces
  v(θ − α) ≥ w − C_φ for the nearest root α of φ, where C_φ = Σ_{β ≠ α}
  v(α − β) is a fixed co-different sum. r = w − C_φ in absolute v-units.]

**(X2) Lattice and strict climb at recenterings.** r takes values in
(1/D(n))·ℤ for an n-only D(n) ≥ 1, and the child state of every
recentering-population node (`recT1` or `t4`) has r_child ≥ r + 1/D(n).
  [Intended reading: the corpus's D.10 strict weight climb (derived) + the
  weight-lattice duty (`dnLattice`, candidate D(n) | n!; D(n) = n when all
  frames of the branch stay unramified). Note this radius functional is
  immune to KD9's observed zero-gain-at-key-creation phenomenon: climb is
  demanded only at the two recentering populations, exactly as the compiled
  KD6 carrier requires.]

**(X3′) Singleton certificate threshold.** If ν is continuing and its child
state has |S| = 1, say S = {θ}, then r_child ≤ 2·v(f'(θ)) + κ₀ with κ₀ = 1.
  [Intended reading: a singleton tracked cluster means the branch is Newton-
  polishing one simple root; the engine's Hensel-type certificate ((τ-hen),
  cap N_V = 1 in the corpus's TB-CAP, PROVED there) fires at the first read
  whose window exhibits (D3)'s condition; continuing therefore bounds the
  radius by the Newton threshold plus one read of slack.]

**(X4) First-read wildness.** If T_can(f) has any continuing node at all, then
f̄ := f mod p is not squarefree.
  [Intended reading: the root-level read factors f̄; every multiplicity-1
  residual factor is certified at the read itself (Hensel for degree-1 and
  unramified factors, the residual-polynomial theorem otherwise), so a
  continuing node presupposes a residual factor of multiplicity μ ≥ 2, i.e. a
  repeated factor of f̄. This clause IS `RecImpliesWild` strengthened from
  "recentering node" to "continuing node"; the corpus already stated the
  weaker form as the named KD2b hypothesis with the same discharge owner.]

### 2.2 The two pricing lemmas (proved, given the interface)

**Lemma A (pair leg).** If a continuing node's child state has |S| ≥ 2 and
radius r, then r ≤ P.
*Proof.* Pick θ ≠ θ' ∈ S. By (X1), v(θ − c) ≥ r and v(θ' − c) ≥ r, so by the
ultrametric inequality v(θ − θ') ≥ min(v(θ − c), v(c − θ')) ≥ r. But
v(θ − θ') is one summand of P and all summands are ≥ 0, so v(θ − θ') ≤ P. ∎
[Status: elementary given (X1); the mechanism is the branch-general form of the
in-corpus L5fix Invariant 2 (the self-loop pair budget, where ALL (m choose 2)
pairs drop per loop); for the count form a single pair per node suffices.]

**Lemma B (singleton leg).** If a continuing node's child state has |S| = {θ}
and radius r, then r ≤ 2·v(f'(θ)) + 1 ≤ 2P + 1.
*Proof.* The first inequality is (X3′); the second is (D2). ∎

**Corollary (uniform obstruction bound).** Every continuing node's child state
has r ≤ 2P + 1 = v_p(disc f) + 1. (Lemma A gives P ≤ 2P ≤ 2P + 1; S ≠ ∅ by
(X1), so the two cases are exhaustive.)

### 2.3 The count theorem

**Theorem WC (weight-charge, count form; claimed new, conditional on
(X1)–(X3′)).** For every branch history H of T_can(f), f monic of degree n with
disc f ≠ 0:

    #recT1(H) + #t4(H)  ≤  D(n)·(v_p(disc f) + 1).

*Proof.* Let ν(1), …, ν(k) be the recentering-population nodes of H in branch
order, k := #recT1(H) + #t4(H). Write rᵢ for the radius of ν(i)'s child state.
By (X2), r is nondecreasing along the branch and climbs by ≥ 1/D(n) at each
ν(i), and radii are ≥ 0 at the root, so rᵢ ≥ i/D(n); in particular
r_k ≥ k/D(n). Every ν(i) is continuing (populations are defined only on
continuing nodes — `popOf?` returns none otherwise), so the Corollary applies
to ν(k): r_k ≤ v_p(disc f) + 1. Chain: k ≤ D(n)·(v_p(disc f) + 1). ∎

**Corollary WC′ (the KD-shaped cap).** `WeightCapP` holds at the compiled
count carrier `countKeyWeight n` (KW.D = 1) with c := D(n):
#recT1(H) + #t4(H) ≤ D(n)·(1 + v_p(disc f)). This is verbatim Theorem WC.

**Corollary (L-A).** `RecImpliesWild` holds at the intended engine: a
recentering-population node is continuing, so (X4) applies. With the compiled
KD2a this gives REC-DISC (1 ≤ v_p(disc f) on any history with a recentering).

**Assembly (the route form).** Feed KD10 with KW := `countKeyWeight n`
(KW.D = 1), c := D(n) (nonneg), hcap := WC′, hrecdisc := (L-A) ∘ KD2a, and any
constants pack with s ≥ 2·D(n); then `WeightChargeFullP` holds, and KD5 with
the `cl15_align` row closes `X3aRouteP` through the right disjunct. Explicit
constant: **s(n) = 2·D(n)** suffices (KD10's own arithmetic absorbs the "+1"
via REC-DISC); s(n) = 2·D(n) + 1 if one prefers to avoid the case split.
Sanity: at n = 3 with the unramified-slice value D = 3 this gives s = 6; the
sealed probe candidate s(3) = 2 (max observed ratio 1/3, quartic cylinder
1/10) is safely inside it.

### 2.4 Why this does not re-run into the X1B refutation

The adjudicated countermodel (155,648 violations at p = 2; exact off-box
witness f = (x−36)(x−117)(x−18), p = 3) kills any bookkeeping that SUMS
per-node side/table values along a branch: successive window reads of one
cluster re-price the same pair differences. Theorem WC never sums a per-node
quantity against the budget; it compares a single monotone state variable (the
radius) at ONE node (the last recentering) against the budget, and converts
state into count only through the lattice quantum. Re-pricing the same pair at
many nodes is harmless: each node's obstruction certifies where the radius
STANDS, not what the node ADDS. This is exactly the count-vs-CUM distinction
the adjudication drew, and the design reason the count form survives while the
cumulative form is refuted.

## 3. Worked consistency check, and the sharper ind-form (conjecture only)

### 3.1 A recentering run priced exactly

Family: F_k = (x − a)² − 2^{2k+1}u over ℤ₂, u a unit, a ∈ ℤ₂ with all read
digits nonzero. Roots a ± 2^{(2k+1)/2}√u; internal pair valuation k + 1/2 + 1;
v₂(disc F_k) = 2k + 3. The digit branch: at read level j ≤ k the window hull of
F_k(c_j + t) has vertices (0, 2j), (2, 0) (the middle point (1, 1+j) lies
strictly above), a single side of slope j with e = 1, ℓ = 2, residual a perfect
square — a `recT1` landing; at level k + 1 the constant-term valuation freezes
at 2k + 1, the hull steepens to slope (2k+1)/2, e = 2 — a terminal ramified
certificate. So the branch has exactly k recenterings. Budgets: P = k + 3/2, so
Theorem WC's cap D·(2P + 1) = D·(2k + 4) holds with 4-fold room; the GMN index
is ind(F_k) = k (lattice points (1, 1), …, (1, k) under the final side), so the
run is even priced 1:1 by ind. The refuted cumulative reading would have
charged Σ_{j≤k} j ≈ k²/2 — the double-charge in miniature.
[Machine-verified 2026-07-31 (a = −1, u = 1, k = 1..4, direct hull walk):
#rec = k, ind = k, v₂(disc) = 2k+3, cap holds — exact at all four k.]

### 3.2 The ind-form (POP-IND), left as a conjecture

The KD7 carrier `DifferentBudget` wants the sharper cap
#rec ≤ c₁·(1 + ind f) (index, not discriminant). Evidence FOR: (i) §3.1's run
is priced 1:1 by ind; (ii) the singleton leg for a degree-1 factor is priced by
v(f'(θ)) = the cross-resultant sum, which sits inside ind by the additivity
ind(f) = Σᵢ ind(fᵢ) + Σ_{i<j} v_p(Res(fᵢ, fⱼ)); (iii) KD9's empirical cap fits
(min c = 2/7 and 8/25, declining in vdisc). The unresolved leg: a tracked
irreducible factor F whose internal pair valuations are dominated by the
DIFFERENT part v_p(disc L_F) (outside 2·ind(F)) — my Lemma A prices such runs
only against P. §3.1 suggests the best-center polygon always re-captures the
run inside ind_r (the lattice points under the steepened side), but I have not
proved this at general Okutsu depth. **Status: conjecture with a proof sketch;
NOT needed for the obligation** (WeightCapP is the vdisc form, and KD10
consumes it directly — the DifferentBudget/ind route is optional sharpening).

## 4. Literature

- (P2) identity v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ): classical
  index–discriminant formula; already pinned in `docs/GMN_citations.md` (GMN,
  Trans. AMS 364 (2012), §4 index machinery, Thm 4.18 environment). [Known;
  in-corpus citation infrastructure exists.]
- Pair-sum discriminant budget for self-loop chains: IN-CORPUS,
  `lean/notes/L5fix_complete.md` §1.2 (Invariant 2): each self-loop drops
  D_t = ½v(disc g_t) by ≥ (m choose 2), chain length ≤ D₀. My Lemma A is its
  branch-general count-form generalization. [New proof of a known-in-corpus
  mechanism.]
- Bauch–Nart–Stainsby, "Complexity of OM factorisations of polynomials over
  local fields", LMS J. Comput. Math. 16 (2013) 139–171: analyzes the Montes
  algorithm's iteration/refinement count in terms of δ = v_p(disc f); the
  closest published analogue of WEIGHT-CHARGE. **Flagged: I cannot state their
  refinement-count lemma precisely from memory; the exact statement must be
  pulled before any literature-axiom use.** Note also the object mismatch: the
  published bound is about a particular algorithm's run, not this project's
  canonical digit-reading tree, so at best it transfers mechanism, not the
  statement — NOT literature-axiom-eligible as-is.
- Guàrdia–Nart–Pauli, "Single-factor lifting and factorization of polynomials
  over local fields", J. Symbolic Comput. 47 (2012): Newton-type convergence
  of single-factor lifting with the type's different as the obstruction — the
  published home of the (X3′) mechanism at general Okutsu depth. [Same flag.]
- Hensel/Krasner (D3): any standard reference (e.g. Neukirch II.4). [Known.]

## 5. Honest gap census

Open, with owners (all four are engine-dictionary statements, the same seam
family as (ALIGN)/`RecImpliesWild` — owner HC-2/OM real-instance wave):
1. (X1) the cell⇒disk dictionary: engine cells refine to disks around key
   roots at radius w − C_φ (Okutsu bound). This is where the D.0 raw-frame ↔
   normalized-value bookkeeping enters; it is a *pointwise* transport, strictly
   weaker than the (ALIGN-rec) per-order index transport (no index accounting,
   no double-count question — only proximity).
2. (X2) lattice + strict climb: D.10's climb is already recorded DERIVED
   in-corpus; the lattice denominator D(n) is the standing `dnLattice` duty.
   The new content is only "in absolute v-units, one lattice step ≥ 1/D(n)".
3. (X3′) the singleton certificate threshold with slack κ₀ = 1: from TB-CAP's
   (τ-hen) N_V = 1 (PROVED in-corpus) + (D3) read in the window.
4. (X4) first-read wildness: multiplicity-1 residual factors certify at the
   read. (= `RecImpliesWild`'s discharge, already the recorded KD2b owner.)

Also open, independently: `cl15_align` (the route's alignment leg) — NOT
attacked here; it is its own ledger row and its own open-math item (M-series
sibling). Nothing in this attempt weakens or restates it.

What is UNCONDITIONALLY done here: (D1)–(D3) + Lemmas A/B + Theorem WC +
Corollaries, i.e. the entire valuation-theoretic assembly from (X1)–(X4) to
`X3aRouteP`, with explicit s(n) = 2·D(n) + 1 and full KD-carrier compatibility
(the statement shapes were checked against the compiled KD6/KD7/KD10 so the
instantiation wave can transcribe without restatement).

## 6. NUMERIC-TESTS

All runnable with the existing verification/ stack (python3 + sympy + cypari2;
the n = 3 walkers in `case_mn3_gate.py` / `x_n3_probes.py` are gate-validated).
Tests T1–T4 refute interface/lemma shapes; T5–T6 refute constants only.

**T1 (radius-vs-budget, the Corollary).** Boxes: exhaustive monic cubics,
p = 2 level 8 (2²⁴) and p = 3 level 5 (3¹⁵), read-exact f only (reuse the X1A
censoring). At every continuing node record the absolute climb ledger
r := Σ over recentering-population prefix nodes of h_r/(frame ramification at
the node). CHECK: r ≤ v_p(disc f) + 1 at every node of every branch. Output:
violation list (f, branch, node, r, vdisc); 0 expected. Any violation refutes
the (X1)+(X2) radius reading as I stated it (not the kernel).

**T2 (pair witness).** On the p = 3 box (roots computable exactly for the
split/partially-split f via `pari.factorpadic` at precision 40): for every
continuing node whose tracked cluster has ≥ 2 roots, verify some pair with
v(θ − θ') ≥ r (r from T1's ledger). Tests Lemma A's engine reading directly.

**T3 (singleton tail).** For every f in either box with a certified degree-1
factor x − a (a ∈ ℤ_p to box precision): the maximal consecutive run of `t4`
nodes on the branch tracking a, AFTER the tracked cluster reaches size 1, must
be ≤ 2·v_p(f'(a)) + 1 (f'(a) exact via the integer lift). Tests (X3′).

**T4 (RecImpliesWild / X4).** Exhaustive on both cubic boxes + the quartic
RS-conditioned cylinder 2²⁶: every f whose tree has ANY continuing node has
non-squarefree f mod p. (KD1 verified the recentering-node special case; this
is the stronger X4 form.) Output: count of continuing-f with squarefree
reduction; 0 expected.

**T5 (the count bound at the theorem's constant).** Both cubic boxes +
quartic cylinder: #recT1 + #t4 per branch ≤ (2n + 2)·v_p(disc f) — my s(n)
with D = n (unramified-slice value) plus slack. Also report the empirical
max ratio (known: 1/3 cubic, 1/10 quartic) as the running headroom record.

**T6 (new degrees).** Random samples, 10⁵ monic quartics and quintics per
p ∈ {2, 3, 5}, coefficients uniform in [0, p¹²): walk the tree (extend the
walker; the quartic engine exists in the state-probe stack), test T1 + T5.
Any T5 violation kills only the candidate constant; a T1 violation is a
finding against the radius reading and must be adjudicated, never patched.

**T7 (the §3.2 ind-form conjecture).** On the p = 3 cubic box: compute
ind(f) = Σᵢ ind(fᵢ) + Σ_{i<j} v_p(Res(fᵢ, fⱼ)) via `factorpadic` (per-factor
index from v_p(poldisc) minus the field-discriminant valuation, obtained by
`nfdisc` on a high-precision global lift of each factor — Krasner guarantees
the p-part matches at precision ≫ 2·v_p(disc f)). CHECK: #rec ≤ 4·ind(f) + 1.
A violation refutes the c₁ = 4 candidate (and if #rec > c·(1 + ind) for
growing c along a family, refutes the ind-form shape itself, leaving the
proved vdisc form as the route's carrier).

VERDICT: REDUCED — X3aRouteP at the real instance is reduced, with all
assembly machine-checked (KD5/KD6/KD10 + KD2a) and the valuation-theoretic
core proved here (Lemmas A/B, Theorem WC, s(n) = 2·D(n) + 1), to the four
named engine-interface lemmas (X1) cell⇒disk, (X2) lattice+climb, (X3′)
singleton certificate, (X4) first-read wildness — each standard-OM-true,
sharply stated, owner HC-2/OM instance wave — plus the pre-existing sibling
row cl15_align for the alignment leg.
