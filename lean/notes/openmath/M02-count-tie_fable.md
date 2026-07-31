# M02-count-tie — attempt (Fable, 2026-07-31)

Target: `TreeSeam.count_tie` (DefsLedger.lean:235) at the intended bridge
instance (carrier `bridgeTree`, mass `bridgeMass`, classifier
`bridgeCanonical`, assignment `bridgeTreeOf`, model tower `bridgeTm =
canTreeModelN (canPolicy p)`).  Notation as in the brief
(`M02-count-tie_brief.md`): Φ_N(V) := {x ∈ digit box at level N :
V.fiberAt (Tm N) (chart N) x}, c_V(N) := #Φ_N(V), t_V := V.thr n (≥ 1),
lvl V := max(t_V, 1) = t_V.

**Headline.** (1) As typed, the row is *refutable at the intended instance*:
the carrier `bridgeTree` admits trees with ns-marked leaves, and for those the
exact count law provably fails (§2 — an explicit degree-2 family; the failure
is arithmetic, not delicate).  The note's own TREE-N always carried the
ns-free hypothesis; the Lean row dropped it.  Minimal repair: add `NsFree V`
(no ns-marked leaf, `MovesT.NsFree`, Defs.lean:1484) to the carrier
`bridgeTree`.  (2) For the repaired (ns-free) carrier the row REDUCES, by a
fully rigorous and short argument (§3–§4), to ONE cross-level cylinder law
CYL (§4), strictly weaker than the corpus's currently-typed locality kernel;
and (3) the currently-typed kernel `BridgeReadLocality` is itself too strong —
refutable at the intended instance (§5) — so the recorded discharge chain
needs the same per-site repair.  §6 gives the open lemmas the repaired row
rests on and the literature adjacency.  §7 verdict, §8 numeric tests.

Everything in §1, §3, §4 is rigorous modulo explicitly cited Lean lemmas/pin
fields.  §2 and §5 are informal-rigorous refutations at the *intended
semantics* of the canonical read machine (`MovesJ.ReadsOf`); their one
unverified step is flagged inline.  Labels: (a) known, (b) new proof of
known, (c) claimed new.

---

## 1. Plumbing: the row is equivalent to a fiber-count scaling law  [(c), rigorous]

**Lemma A (count = fiber count).**  Fix a pinned instance (any `TreePin`,
DefsLedger.lean:344).  Let σ, N ≥ 1, T : F.Tree σ with F.thr σ T ≤ N.  Then
the map f ↦ boxeq N f is a bijection

  { f : Box p n N // canonical N f = some σ ∧ treeOf σ N f = T }
    ≃ { x : digit box (n·N) // (vt σ T).fiberAt (Tm N) (chart N) x }.

*Proof.*  Well-defined: for decided f with treeOf f = T, `treeOf_pin` gives
(vt σ (treeOf f)).fiberAt … (boxeq f), i.e. (vt σ T).fiberAt (boxeq f).
Injective: boxeq is an Equiv.  Surjective: given x = boxeq f fibering vt σ T,
`canonical_pin` (⟸ direction, witness ⟨T, thr ≤ N, fib⟩) gives
canonical N f = some σ; then `treeOf_pin` gives (vt σ (treeOf f)).fiberAt x,
and two trees fibering the same point have equal underlying VTrees
(`MovesT.vtree_eq_of_fiberAt`, MovesT/F3_dictSum.lean:45, PROVED Lean-core),
so vt σ (treeOf f) = vt σ T, and `vt_inj` gives treeOf f = T.  ∎

All ingredients are `TreePin` fields or landed Lean-core lemmas; at the
bridge instance the pin fields hold by construction (BridgeD6/D7/D17/D18,
sorry-free at HEAD).  The N = 0 corner of the row is vacuous at the instance:
bridgeThr = `VTree.thr n = … ⊔ 1 ≥ 1` (Defs.lean:734), so thr ≤ N forces
N ≥ 1.  (At the *abstract* seam an instance with a threshold-0 tree would owe
the N = 0 case separately; the pin is silent there — recorded residue.)

**Lemma B (the row ⇔ scaling).**  At the bridge instance (mass =
`bridgeMass`, D12), for fixed T with t := t_V, the count_tie clause for
(σ, T) at all N ≥ t is equivalent to

  (SCALE_T)   c_V(N) = c_V(t) · p^{n(N − t)}   for all N ≥ t,   V := vt σ T.

*Proof.*  By Lemma A the RHS of count_tie is c_V(N).  The LHS is
(c_V(t)/p^{nt})·p^{nN} in ℝ≥0∞; cross-multiplication is legal since
(p : ℝ≥0∞)^{nt} is finite and nonzero, and ℕ-casts are injective.  ∎

So the entire mathematical content of M02 is (SCALE_T): *the fiber count of a
complete finite canonical tree multiplies by exactly p^n per precision level,
from its threshold on.*  Equivalently: Φ_N(V) is a union of full level-t
cylinders whose level-t shadows are exactly Φ_t(V).

## 2. Refutation of the row as typed: ns-leaf trees violate (SCALE) [(c)]

The carrier `bridgeTree n p σ = {V // V.typemult = σ.1 ∧ RealizedSelf n p V}`
(BridgeD3) carries **no ns-free clause**, so count_tie quantifies over trees
with ns-marked leaves.  For those the note itself asserts the *opposite*
behavior (E12 `treeN_ns`: normalized fiber count → 0), and one can see the
failure concretely:

**The exact-square family (n = 2, any p, k := 1).**  Fix a residue u₀ ∈ 𝔽_p^×.
Consider level-N classes f with dec f = (X − b)², b = p·(u₀ + p·s) — i.e. the
class of an *exact square* with v_p(b) = 1, first side slope read = 1 on the
track X̄, residual root u₀.  On such dec f the canonical machine performs one
lawful side read ν₀ (slope-1 side of the polygon of (X−b)² w.r.t. X: points
(0,2), (1,1), (2,0); e = 1, repeated residual (z − u₀)², μ = 2), the window
re-opens at the refined track, and the refined φ-expansion of an exact square
is degenerate — no polygon side exists, no child node is realizable, and
`NsHalts` fires at the realized chain [ν₀] (this is `NsHalts`' defining
purpose: "CELLS whose window admits no side (J(f) = ∅)", Defs.lean:223).  Let
V₀ be the VTree with chains = prefix-closure of {[ν₀]}, nsLeaf marked at the
maximal chain, leafV = nsVerdictOf, henV = ∅.  Clause-by-clause check of
`fiberAt` at such f (against Defs.lean:518): (i) the run set is exactly
{[ν₀]} (the reduction X̄² has the single track X̄, no simple factors);
(ii) ¬IrrHalts (accE·accF = 1 ≠ 2 = childWidth·μ), NsHalts holds, marking and
verdict match (nsVerdictOf = μ·{(accE, accF)} = 2·{(1,1)}); (iii) henPayload =
∅ ✓; (iv) vacuous; (v) typemult = {(1,1),(1,1)}, sum 2 = n ✓; (vi) heads =
{[ν₀]}, trackDeg = 2 = (multiplicity 2)·(deg 1) of the repeated factor X̄ ✓.
So V₀ ∈ bridgeTree n p σ₀ with σ₀ = {(1,1),(1,1)} (it is self-realized at its
own level), and — this is the poison — **the classifier decides exact squares,
with verdict "totally split"**.

Now count.  A point x lies in Φ_N(V₀) iff dec x is an exact square of the
displayed shape: if dec x is NOT an exact square, its discriminant has some
finite valuation d, the refined window of the *exact integer polynomial*
dec x has a genuine side (visible at slope reads of height ≤ d), a child IS
realized, and clause (i) fails for V₀.  [Flagged step: this and the ns-halt
above are the intended semantics of `MovesJ.ReadsOf`/`memCan` — the canonical
model's mem/child read the exact decoded polynomial (`canTreeModel`,
TreeCan.lean:317: mem depends on x only through dec x), so no precision cap
protects V₀'s fiber; I have not machine-traced `ReadsOf` on these inputs, and
`canPolicy` is designer-sorried at HEAD, so no compiled countermodel is
possible today.]  Hence

  c_{V₀}(N) = #{ b = p(u₀ + ps) mod p^N } = p^{N−2}   (N ≥ 2),

one free parameter b above level 2 — while (SCALE) demands growth p^{2(N−t)}.
Already count_tie at N and N+1 forces c(N+1) = p²·c(N); the family gives
c(N+1) = p·c(N).  **Contradiction.**  (Consistency check: c(N)/p^{2N} =
p^{−N−2} → 0, exactly `treeN_ns`'s asserted limit — the corpus's own ns
theorem contradicts count_tie on any ns tree with nonempty fibers at
infinitely many levels.)

**Corroboration that this is a statement bug, not intended content.**
(i) The note's TREE-N (MOVES 7559–7574, quoted in the T blueprint) is stated
for trees "complete finite realizable with all leaves (τ-irr)/(τ-hen)" — the
ns leaves are excluded; the machine-checked discharge candidate `treeN`
(E11_treeN.lean:42) carries `hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H`.  The
Lean seam row has no such guard, so the designed chain IB-D20/D21 could never
have closed it for the full carrier.  (ii) The same ns family refutes, at the
intended instance, `canonical_stable` (a `ClassifierSpec` FIELD, supplied via
BridgeD8 from the transfer row): an exact-square class decided σ₀ at level N
has refinements that are non-squares deciding to other types (or undecided).
(iii) It also makes `VPSound` unsatisfiable (a square class's lifts realize
several true types, but the classifier emits σ₀).  One repair kills all
three.

**Minimal repair (proposed).**

```lean
def bridgeTree (n p : ℕ) [Fact p.Prime] (σ : SplittingType n) : Type :=
  {V : MovesT.VTree p (ZMod p) //
     V.typemult = σ.1 ∧ RealizedSelf n p V ∧ MovesT.NsFree V}
```

Effects: exact squares (and every window-degenerate locus) fiber NO carried
tree, so `bridgeCanonical` returns `none` there — they drain into the
undecided envelope env(N), which is precisely the M9/Phase-B design (the
drainage/hExhaust story) and what `treeN_ns` prices.  count_tie's ∀T then
ranges over ns-free trees, matching `treeN`'s scope; `canonical_pin`,
`vtree_eq_of_fiberAt`, Lemmas A/B are untouched (they never used the ns
clause).  Statement-fence note: this is a definition change on the bridge
carrier (sanctioned-genre: instance repair, not a theorem weakening); flagged
for sign-off per the axiom/statement policy.

## 3. The repaired row: reduction to one cylinder law  [(c), rigorous]

Assume the ns-free carrier.  Fix an ns-free, self-realized V with t := t_V.

**CYL(V) (the one open kernel needed).**  For all levels M, M′ ≥ t and points
x ∈ digit box(n·M), x′ ∈ digit box(n·M′) whose underlying coefficient classes
agree mod p^t (equivalently, in the level-major dressing: agreeing on the
first n·t digits):

    x ∈ Φ_M(V)  ⟺  x′ ∈ Φ_{M′}(V).

**Theorem (count_tie from CYL).**  CYL(V) for all carried V implies
count_tie at the (repaired) bridge instance.

*Proof.*  By Lemmas A/B it suffices to prove (SCALE_T).  Fix N ≥ t.  The
reduction map π : Box p n N → Box p n t is exactly p^{n(N−t)}-to-1.  By
CYL(V) with M = M′ = N, membership in Φ_N(V) is constant on π-fibers, so
Φ_N(V) = π^{-1}(S) with S := {g ∈ Box p n t : some lift lies in Φ_N(V)};
hence c_V(N) = p^{n(N−t)}·#S.  By CYL(V) with (M, M′) = (N, t) applied to a
lift f of g and g itself (they agree mod p^t trivially), g ∈ S ⟺ boxeq g ∈
Φ_t(V); hence #S = c_V(t).  ∎

Both applications go through the compiled layout dressing
(`blockInterleave`, MovesT/ReadLocality.lean:168 — a proved bijection between
the coefficient-major slot i·N + k and the level-major slot k·n + i, with the
gate `blockInterleave_bridgeChart`), so "first n·t digits" and "agree mod
p^t" are interchangeable; this is bookkeeping already landed in BridgeD5.

Two remarks.  (1) This route needs **neither** the (SIB) nor the (JC-multi)
counting kernels, nor any site ledger/scaffold instance data: the recorded
chain IB-D21 ("count_tie from `MovesT.treeN` + sibjc rows + D20") routes
through the per-level exponent identity and is strictly heavier — it
additionally needs the D20 pack to exist at every level with
level-independent site exponents.  `treeN` remains valuable as the *value*
statement (c_V(t) = p^{nt − A(V,L)}), but count_tie itself never needs the
value, only the scaling.  (2) CYL(V) is exactly the conjunction of the
corpus's `TreeNStable` (fixed-level cylinder face, M = M′) and the two-sided
level transfer (M ≠ M′); the corpus's `TransferRow.fiber_transfer` is its
up-direction and `treeN_stable`'s `TreeNStable` its fixed-level face — CYL is
their common closure and is implied by the corpus's `ReadLocality` row (the
proof of `transferRow_of_readLocality`, BridgeD5:491, PROVED, runs precisely
this composition and works verbatim in both directions since `child_local`
imposes no order on M, M′).

## 4. But the currently-typed locality kernel is too strong  [(c)]

`MovesT.ReadLocality` (ReadLocality.lean:111) demands `child_local` at
**every** site (o, ν) — quantified over all histories and nodes, not over the
tree's own sites — once N ≥ Tr.thr n.  Its ∀-tree closure
`BridgeReadLocality` (BridgeD5:179) therefore asserts, upon choosing any tree
V with thr = 1 (e.g. any purely-Hensel tree, chains = ∅; thr = sup ∅ ⊔ 1 = 1):
*the entire child relation at every site and every level is a function of the
level-0 digits.*  That is false at any faithful OM model: take x, x′ at level
2 with dec x = X² − pc, dec x′ = X² − p²c (p odd, c a unit).  They agree on
all level-0 digits; the slope-½ root read is realized on x and not on x′.
Hence `BridgeReadLocality` is refutable at the intended instance (same
caveat as §2: informal at HEAD because `canPolicy`/`ReadsOf` tracing is
blocked; but any model on which the machine distinguishes first-side slopes —
which it must, to classify at all — refutes it).  Note this does NOT
contradict the corpus's compiled artifacts: `probeChildModel`
(BridgeN3b) already showed the law is not interface-derivable, and all
landed uses are conditionals.

**Repair (proposed).**  Guard the locality per site, not per tree: for every
site (o, ν) there is a modulus L(o, ν) — computable from the node data alone,
the shape/band threshold `(shapeOfH H n).Nshape ⊔ siteLevel n (some H)` of
H := the chain ending at ν — such that child at (o, ν) is a cylinder in the
digits below n·L(o, ν), uniformly across working levels ≥ L(o, ν).  Then
`Tr.thr n` majorizes L on Tr's own sites BY DEFINITION of `VTree.thr`, and
the CYL derivation (§3) needs, beyond the per-site law, only:
* (leaf stability) τ-irr is x-free (`IrrHalts` reads node data only — already
  definitional), and the ns-freeness of leaves under the repaired carrier
  removes the one x-dependent halt clause from `fiberAt`'s clause (ii);
* (roster completeness) the *all-and-only* clause (i) and the ¬NsHalts side
  conditions in clauses (ii)/(iv) quantify over sites OUTSIDE the tree; these
  are handled not by per-site locality of arbitrary sites but by
  **bounded-level completeness**: on the fiber, every realized run is one of
  Tr's chains extended by at most one read, and the nonexistence of further
  children at a chain site is a read of the site's own joint cell at its band
  level (the note's "per site: the joint cell's literal system at its B(iii)
  level; per branch: D4R.4's exact level-N realization; per leaf: TB-CAP's
  level-N_V cylinders", MOVES 7566–7570).

## 5. What remains genuinely open (the honest distance)

With the carrier repair, count_tie reduces to CYL(V) for ns-free carried
trees, and CYL(V) rests on three open lemmas about the canonical read machine
(all owner HC-2/D4R0K in the corpus's bookkeeping; none currently has a Lean
proof or a directly citable literature form):

* **L1 (per-site read locality).**  For a lawful history H·ν, whether
  `ReadsOf (dec x) (H·ν)` holds depends only on x's digits at levels
  < L(H, ν) := Nshape(shapeOfH H) ⊔ siteLevel(H) — i.e. each polygon-side /
  residual read of the machine factors through the corresponding truncation
  of dec x.  (Newton-polygon reads at slope h/e read coefficient digits up to
  height ≤ the side's rim; residual factorizations read the side's digit
  vector — this is the standard bounded-precision property of one Montes
  step.)
* **L2 (no new runs on the fiber, bounded).**  If x ∈ Φ_t(V) (V ns-free,
  t = thr V), then for every extension x′ (any level ≥ t, same class mod
  p^t), every realized run on dec x′ is a prefix of a chain of V or a chain
  of V extended within its (already-read) window roster — no read of level
  ≥ t creates or destroys a run.  This is where τ-irr saturation is used: a
  saturated leaf (accE·accF = width·μ) admits no lawful extension node at
  all (an algebraic fact about the node laws, x-free); and a Hensel track
  (simple reduction factor) admits none past its level-0 read.
* **L3 (realization transfer).**  V realized at level t ⟹ realized at every
  level ≥ t, and conversely fibering at level N ≥ t descends to level t
  (this is L1+L2 assembled; stated separately because the corpus types it as
  `TransferRow`).

**Literature adjacency [(a), precisely stated; not directly citable].**  The
mathematical content of L1–L3 is the bounded-precision correctness of the
Montes algorithm: (α) J. Guàrdia, J. Montes, E. Nart, *Newton polygons of
higher order in algebraic number theory*, Trans. AMS 364 (2012) 361–416 —
the OM machine and its invariants; (β) J. Guàrdia, E. Nart, S. Pauli,
*Single-factor lifting and factorization of polynomials over local fields*,
J. Symbolic Comput. 47 (2012) 1318–1346 — factorization from f mod p^ν with
explicit precision ν (their ν is discriminant-based, ν = v_p(disc f) + 1
genre, not tree-intrinsic); (γ) the folklore Krasner-type statement: if f, g
monic of degree n with f ≡ g mod p^{2v_p(disc f)+1} then their factorization
data correspond (attribution uncertain — flag for lookup; a convenient
citable proxy is [β, Prop. 3.6-adjacent precision lemmas] or standard
continuity-of-factorization arguments).  None of these matches the Lean row's
*exact tree-intrinsic threshold* `VTree.thr` or the corpus-internal `ReadsOf`
machine, so M02 is NOT literature-axiom-eligible as it stands: a citation
would still owe the (machine ↔ Montes) dictionary, which is the same work as
L1–L2.  The discriminant-based bounds ARE citable for a *weaker* row (a
cylinder law with threshold max(thr V, 2v(disc)+1)-style), but count_tie as
typed pins the threshold to `VTree.thr`.

## 6. Summary of claims

1. [(c), rigorous] count_tie at any pinned instance ⇔ (SCALE): per-tree fiber
   counts scale by p^n per level above the tree's threshold (Lemmas A, B).
2. [(c), informal-rigorous] As typed the row is FALSE at the intended
   instance: ns-leaf trees are in the carrier, decide degenerate loci, and
   their fiber counts scale with defect (exact-square family, §2); the
   corpus's own `treeN_ns` limit is incompatible with count_tie on any ns
   tree with infinitely-often-nonempty fibers.  Repair: `NsFree` in
   `bridgeTree` (one clause; also rescues `canonical_stable` and `VPSound`).
3. [(c)] The recorded discharge intermediary `BridgeReadLocality` is
   refutable at the intended instance (all-sites quantifier, §4); per-site
   guarded repair proposed.  The count_tie chain does not need it: CYL (§3)
   suffices and needs no SIB/JC kernels, no D20 pack.
4. [open] CYL for ns-free carried trees = L1 + L2 + L3 (§5) — the OM
   bounded-precision content; adjacent to but not discharged by
   Guàrdia–Montes–Nart / Guàrdia–Nart–Pauli precision results.

VERDICT: REFUTED — the row as typed fails at the intended instance (ns-leaf
trees; §2), with a one-clause carrier repair under which the row REDUCES to
the explicit open cylinder lemmas L1–L3 (§3, §5); the per-level value
identity is already machine-checked (`treeN`) modulo the separate SIB/JC
obligations, but is not needed for count_tie itself.

## NUMERIC-TESTS

Runnable with PARI (`gp` at ~/.local/bin/gp; cypari2 absent from the default
python3 on this box); n = 2 unless noted.  For a level-N class f
(coefficients mod p^N), "certificate of f" := the multiset {(e_i, f_i)} of
(ramification, residue-degree) pairs of `factorpadic` applied to a lift at
precision ≥ N + 10.  **T1 and T2 were EXECUTED 2026-07-31** (scripts
preserved at `verification/openmath/m02_t1_scaling.gp` and
`verification/openmath/m02_t2_nsrefute.gp`; run `gp -q <file>`); T3–T5 are
proposed.

* **T1 (scaling above threshold — confirms the ns-free row).  EXECUTED,
  CONFIRMS.**  p = 3, N = 2..4: all p^{2N} classes; a class is *stable* if
  its canonical lift and 5 lifts perturbed by p^N·(1+random) share one
  certificate; bucket key = (certificate, min(v₃(disc), 2N)).  Result:
  every genuine bucket scales by exactly p² = 9 from its threshold level —
  split/v0: 27→243→2187; inert/v0: 27→243→2187; ram/v1: 18→162→1458;
  split/v2: 27→243; inert/v2: 27→243; ram/v3 first genuinely decided at
  N = 4 with 162 (= 9·18 — the same stratum shape as ram/v1 one level
  deeper).  Two stray entries ([ram, v3] → 3 at N = 3; [inert, v4] → 1 at
  N = 4) are quantified false positives of the 5-lift proxy (classes with
  disc ≡ 0 mod p^N whose 5 random lifts happened to agree; expected counts
  ≈ 4 and ≈ 0.4 under the (2/3)^5 / (2/3·1/2)^5 acceptance model — a
  sharper test should use ≥ 25 lifts or the exact decidedness criterion
  v(disc) determined below level N).  Sanity: decided fraction at N = 2 is
  72/81, the undecided 9 classes = disc ≡ 0 mod 9 ✓.
* **T2 (the ns refutation's arithmetic).  EXECUTED, CONFIRMS §2.**  p = 3,
  the exact-square class (X−3)² held to level 8: its three displayed lifts
  factor as
  `(X−3)² + 3⁹ → [(2,1)]` (ramified), `(X−3)² − 3⁸ → [(1,1),(1,1)]`
  (split), `(X−3)² − 2·3⁸ → [(1,2)]` (inert) — one level-8 class, all three
  splitting types among its lifts.  So any classifier deciding the
  exact-square locus (as the unrepaired carrier forces via the ns tree V₀ of
  §2) violates soundness; and #S_N = 3^{N−2} (1, 3, 9, 27, 81 at
  N = 2..6) scales by p, while count_tie would force p² — the counting
  contradiction, computed.
* **T3 (treeN value spot-check, optional).**  p = 5, n = 2: for the bucket
  "v(disc) = 1, ramified" (t = 2): verify #B(N) = c·5^{2(N-2)} with c =
  #B(2), and c·5^{-4} equals the known Igusa-zeta-derived mass of that
  stratum ((p−1)/p² · 1/p-genre; cross-check against
  `verification/cert_crosschecks.py` values for the n = 2 density table).
* **T4 (threshold necessity).**  Same buckets as T1: verify that scaling
  FAILS below threshold (e.g. the v(disc) = 2 buckets between N = 1 and
  N = 2), confirming the row's thr-gate is not droppable.
* **T5 (n = 3 smoke test).**  p = 2, 3; N = 1..3; same as T1 with p^{3N}
  classes and p³ scaling; includes wild cubics (p = 3) — the most likely
  place for a surprise; any stable bucket violating p³-scaling above its
  first level REFUTES the repaired row and would be a major finding.
