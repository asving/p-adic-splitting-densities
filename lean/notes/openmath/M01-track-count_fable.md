# M01-track-count — attempt (Fable, 2026-07-31)

Obligation: `Cl7Kernel` (MovesU/DefsLedger.lean:199; p-uniform L(n)/D(n)/w*(N)/
T(n,N) with laws `track_restarts`/`zero_gain`/`genuine_bound`) +
`BK.slice_bound` (MovesU/BridgeKernels.lean:216), at the intended instance:
canonical Okutsu–Montes trees of monic degree-n polynomials over ℤ_p, branch
histories = the trees' read sequences, one datum serving every prime.

HEADLINE.  The `track_restarts` clause AS TYPED is refuted at the intended
instance: it bounds the full recentering POPULATION of a history by an n-only
constant, and that population grows linearly in v_p(disc f) at fixed n — an
explicit two-root cluster family witnesses this at every prime, already at
n = 2 (§1, machine-checked mechanism).  This is an overshoot of the source
note's TRACK-COUNT, which bounds only track-OPENING events (§2).  The other
three clauses are genuinely open but correct-looking, and I reduce them to
four cleanly stated engine lemmas, two of which are standard Montes theory;
along the way the note's candidate L(n) ≤ n² is established in the sharper
form L(n) = (n−1) + 2⌊log₂ n⌋ conditional on those lemmas, and one new
UNCONDITIONAL list-combinatorics lemma (provable in Lean today) is exhibited
that makes a repaired `track_restarts` row derivable from the degree budget
alone (§3).  Repair recommendation in §4.

---

## §1 The refutation of `track_restarts` at the intended instance

`track_restarts` demands: there is L = L(n) with, at EVERY prime p, every
f ∉ discZero, every stratum history H,

    (T-const)   #T1-recenterings(H) + #T4(H) ≤ L.

No threshold/level hypothesis is available.  By the carrier law `gmnLink`,
every branch history of the canonical tree of every f is a stratum history,
so (T-const) must bound the recentering population of full branches.

### Lemma 1.1 (one digit per recentering; the caterpillar)

Fix a prime p and m ≥ 1.  Let

    a := p + p² + ⋯ + p^m + p^{m+2},    b := a + p^{m+1},
    f_m := (x − a)(x − b)  ∈ ℤ_p[x]   (monic, deg 2, disc = (a−b)² ≠ 0,
                                        v_p(disc f_m) = 2(m+1)).

Then the canonical Newton-polygon walk on f_m — in the sense pinned by the
source note's §B2-DEF D.10 (recentering = replace the center c by c + d·p^λ,
where λ is the slope of the unique side of the polygon of f_m(y+c) and d the
root of its repeated linear residual factor) — performs EXACTLY m recentering
reads before the two roots separate, and every one of them is a
T1-recentering node (side data ℓ = 2, e = 1, h = λ, selection (g,μ) = (1,2),
isIncrement = false).

*Proof.*  Induct on k = 0,…,m−1 with center c_k := p + ⋯ + p^k (c_0 := 0).
Both roots satisfy v_p(a − c_k) = v_p(b − c_k) = k+1 (their base-p digits
agree up to position m, all equal to 1 in positions 1..m, and c_k matches
exactly the first k of them).  Hence the Newton polygon of f_m(y + c_k) is a
single side from (0, 2(k+1)) to (2, 0): slope −(k+1)/1, so e = 1, h = k+1,
horizontal length 2, residual degree ℓ = 2.  Its residual polynomial has
roots = the position-(k+1) digits of a − c_k and b − c_k, both equal to 1:
the residual factors as (z − 1)², a repeated linear factor.  The selection is
(g, μ) = (1, 2) with e·g = 1: not a key-growth event — by the note's own row
dictionary (X.1a table, row T1 with e = 1, g = 1) this is a D.10 recentering,
isIncrement = false, population `recT1`.  D.10 recenters: c_{k+1} = c_k +
1·p^{k+1}.  After the m-th recentering, c_m = p + ⋯ + p^m and now
v_p(a − c_m) = m+2 ≠ m+1 = v_p(b − c_m): the polygon has two sides of
distinct slopes — the cluster separates and both members halt (two leaves of
type (1,1)).  No other continuing read occurs.  ∎

Machine check: `verification/openmath/m01_quad_walker.py` (run 2026-07-31)
implements exactly this walk with exact integer valuations and confirms
#recenterings = m for p ∈ {2,3,5}, m = 1..10; on 200 randomized families it
confirms the general form #recenterings = #{nonzero shared digit positions
below v_p(a−b)}.

### Theorem 1 (refutation at the intended instance, every n ≥ 2, every p)

For every n ≥ 2, every prime p, and every constant L there exist monic f of
degree n over ℤ_p with disc f ≠ 0 and a branch history H of its canonical
tree with #recT1(H) + #t4(H) > L.  Hence no `Cl7Kernel` instance over
carriers faithful to the intended semantics exists: (T-const) fails already
at any single prime, before p-uniformity is even in play.

*Proof.*  Take m := L+1 and f := f_m · g where g is any monic degree-(n−2)
polynomial over ℤ_p whose reduction mod p is separable, prime to x, and
squarefree-coprime to f̄_m = x² (for p = 2 and any n−2 ≥ 1 take an
irreducible lift of an irreducible degree-(n−2) polynomial over 𝔽_2 with
nonzero constant term; for n = 2 take g = 1).  The level-0 read separates the
x²-cluster from g's factors (distinct residual factors of the root read), so
the branch following the x²-cluster carries exactly the walk of Lemma 1.1:
m = L+1 recentering nodes.  disc f = disc f_m · disc g · Res(f_m, g)² has
v_p < ∞ (all three factors nonzero: the roots of f_m are ≢ the roots of g
mod p).  By `gmnLink` this branch's history is a stratum history of f.  ∎

Remarks.
(i)  This is not a Lean countermodel of the bare structure `Cl7Kernel n KC`
     (junk carriers with empty `inStratum`-reachable histories inhabit it);
     it shows the structure is uninhabitable over every FAITHFUL carrier
     pack, i.e. the capstone's K7 premise can never be discharged at the
     real instance as typed.
(ii) The corpus's own census had already flagged this: KD1-P3 (probe record
     2026-07-30) tabulates max(#recT1 + #t4) = 1, 2, 3, 4 at vdisc = 2, 4,
     6, ≥8 on the exhaustive cubic 2²⁴ box — the trend of Lemma 1.1
     (#rec ≈ vdisc/2 − 1), recorded GROWING; escalation E-1
     (BRIDGE_BP4_KERNELS_2026-07-30.md) already calls the row "plausibly
     false".  Theorem 1 upgrades "plausibly" to a proof at the D.10
     semantics, for every n and p, with an explicit family.
(iii) Consistency with the note: §X-EXHAUST X.1b prices the recentering
     population against v_p(disc f) (kernel WEIGHT-CHARGE, sealed candidate
     s(3) = 2) — the note NEVER claims an n-only bound on that population;
     and SQ.0(c) bounds d_zero only through the N-dependent budget
     L·D·w*(N).  The family does NOT refute `zero_gain`: its branch has
     threshold ≈ m+2, so the m recenterings are priced against w*(N) ≳ m,
     which a linear w* delivers.

### Known-result status

The mechanism of Lemma 1.1 — the Montes/MacLane refinement chain advances
one residual digit per step, so refinement counts on a branch are Θ(v_p(disc))
and not bounded in n — is (a) KNOWN: it is the reason single-factor-lifting
acceleration exists (Guàrdia–Montes–Nart, "Single-factor lifting and
factorization of polynomials over local fields", J. Symbolic Computation 47
(2012) 1318–1346, replaces the Montes algorithm's linear, one-digit-per-
refinement convergence by quadratic convergence; complexity discussions there
and in GMN, "A new computational approach to ideal theory in number fields",
Found. Comput. Math. 13 (2013) 729–762, bound refinement counts by
O(v_p(disc)) — exact statement numbers to be confirmed at lookup).  What is
(c) new here is only the consequence against this Lean row.

---

## §2 Faithfulness analysis: the Lean row states MORE than its citation

The row's docstring cites SQ.0/TRACK-COUNT (MOVES 12925–13018).  TRACK-COUNT
(quoted in the brief) bounds the number of track-OPENING events — (t1) key
creations, (t2) branch openings, (t3) ladder RESTARTS, where (t3) counts
only "a recentering node at which the current monotone weight ladder is
abandoned … and a new ladder begins" — NOT the recentering population.  A
maximal chain of recenterings whose key weight climbs monotonically (which,
by the accepted D.10 content quoted in X.1b, is what every consecutive
recentering chain does — census: zero climb-breaks over 3.9M recentering
members) is ONE ladder of arbitrary length, contributing 0 or 1 openings.
The transcription `countPop .recT1 + countPop .t4 ≤ L` counts every rung of
every ladder.  In the caterpillar the m recenterings form a single unbroken
ladder: the note's count is 1, the Lean row's count is m.

So: Lean row ⇒ note's TRACK-COUNT, strictly; the converse fails; and the
extra strength is exactly what Theorem 1 kills.  The same overshoot is
inherited by `SlotsG5_trackRule` resolution (h1), which pins (t3) to the same
Pop counters "by definition".  Downstream, KD3/KD4 (WeightChargeRed.lean) are
implications FROM (T-const) and remain sound but now have an unsatisfiable
premise at the intended instance; the schedulable WeightCharge route (KD10,
vdisc-relative) is unaffected.

---

## §3 The positive side: reductions, and what is provable now

Fix the intended instance.  Four engine lemmas, stated exactly; A and B are
standard/or carried, C and D are the genuinely open seams.

- **Lemma A (key-degree budget).**  Along any branch history, every
  continuing increment node (T1-increment, T2, or T3) multiplies the key
  degree by its e·g ≥ 2 (T1-inc: e·g ≥ 2 by the row dictionary; T2/T3:
  g = 1, e ≥ 2), and the key degree never exceeds n.  Hence per history
  #incT12 + #t3 ≤ ⌊log₂ n⌋.   [(a) known: Montes types satisfy
  m_{r+1} = e_r·f_r·m_r and m_r ≤ deg F ≤ n for types attached to a factor F
  of f — Guàrdia–Montes–Nart, "Newton polygons of higher order in algebraic
  number theory", Trans. AMS 364 (2012) 361–416 (exact numbering at lookup).
  The Lean corpus carries the e-only half as `HistWF.degProd`; the e·g form
  is the needed strengthening.]

- **Lemma B (branch-degree consumption).**  At a branching node the member
  sub-block degrees are ≥ 1 and sum to at most the parent block degree
  [carried in-corpus: DEG-CONS `size_pos`/`size_sum` on `UCarriers`].  Hence
  along one history, Σ over branching nodes of (#members − 1) ≤ n − 1.

- **Lemma C (run-break locality; OPEN, the (t3) charging seam).**  Within a
  maximal chain of consecutive recentering nodes of one history, the key
  weight strictly climbs in one common lattice (D.10's accepted strict climb
  + within-frame convexity); a monotone ladder is abandoned only at an
  intervening increment node (frame/lattice rescale) or at the history's
  branching nodes.  [Warrant: §B2-DEF D.10 as quoted at X.1b; census KD9:
  zero zero-gain recenterings over 735,744 + 3,194,880 members; zero
  (t3)-breaks on both TRACK-probe boxes.  What is missing is exactly the
  cross-frame comparability bookkeeping — the note's (ALIGN-rec) flavor
  duty.]

- **Lemma D (height/weight budget on decided branches; OPEN but displayed
  "derived" at SQ.0(a)/(b)).**  There are explicit h*(N), w*(N) (affine in N,
  n-only coefficients) with: on branches of threshold ≤ N every read height
  ≤ h*(N) and every key weight ≤ w*(N); and all key weights lie in
  (1/D(n))·ℤ with D(n) := lcm(1,…,n)  [weights have denominator dividing the
  cumulative ramification e₁⋯e_r ≤ n by `degProd`; lcm(1..n) | n! gives the
  note's "D(n) | n!" candidate].

- **Lemma E (corner; OPEN, minor).**  For n ≥ 2, a branch history containing
  a continuing node has threshold ≥ 1.

### 3.1 Unconditional, Lean-provable today (list combinatorics)

Define runCount(H) := the number of maximal blocks of consecutive
recentering-population nodes (pop ∈ {recT1, t4}) in the sublist of continuing
nodes of H.  Since `popOf?` is total on continuing nodes with values in
{incT12, recT1, t3, t4}, any two consecutive blocks are separated by at least
one node of population incT12 or t3.  Therefore

    (R)   runCount(H) ≤ countPop H .incT12 + countPop H .t3 + 1,

by induction on H.  No engine content; provable over `MovesX.XHistory n` as
it stands.

### 3.2 TRACK-COUNT proper (the note's statement), conditional

Assume A, B, C.  Charging table per history H:
(t1) key creations = increment nodes: ≤ ⌊log₂ n⌋   [A];
(t2) branch openings: ≤ n − 1                       [B];
(t3) ladder restarts: each restart is preceded (as the ladder-break C
     localizes it) by an increment or branching node of H, injectively by
     "nearest preceding break": ≤ ⌊log₂ n⌋ + (n−1) — and if breaks occur
     only at increments (C's strong form), ≤ ⌊log₂ n⌋.
Total:  L(n) := (n − 1) + 2⌊log₂ n⌋   (weak-C form: + (n−1) more), in all
cases ≤ n² for n ≥ 2 — the note's sealed candidate holds with room.  Census
fit: observed max openings incl. the base frame = 4 = L(3) at n = 3; 3 ≤ 7 =
L(4) at n = 4.

### 3.3 `genuine_bound`, conditional on A + E only

#incT12 ≤ ⌊log₂ n⌋ ≤ n·N for every N ≥ 1 [A]; for N = 0 the hypothesis
threshold ≤ 0 forces (by E) no continuing node, so #incT12 = 0.  Notably the
note's ledger route (Theorem C / A(η) ≤ nN, with its flagged-open
strict-increment sub-claim) is NOT needed for this clause: the degree budget
alone over-delivers.

### 3.4 `zero_gain`, conditional on A + C + D

d_zero(H) = #recT1 + #t3 + #t4.  Each maximal recentering run climbs one
ladder in (1/D(n))·ℤ inside a weight window of width ≤ w*(N) [C + D], so has
length ≤ D(n)·w*(N) — this step is exactly the corpus's PROVED abstract
ladder lemma `kd6_ladder_count_le` applied per run.  #runs ≤ ⌊log₂ n⌋ + 1
[(R) + A].  Hence
  d_zero ≤ (⌊log₂ n⌋+1)·D(n)·w*(N) + ⌊log₂ n⌋ ≤ L(n)·D(n)·w*(N)
for the L(n) of §3.2 (using w* ≥ 1, D ≥ 1).  The Lean row's shape is met
verbatim.

### 3.5 `slice_bound`, conditional on A + B + C + D (p-uniform T(n,N))

Let a canonical tree of verdict type σ have threshold ≤ N.  Each of its ≤ n
branches (leaves carry disjoint factors of degree ≥ 1) has history length
≤ B(n,N) := 1 + ⌊log₂ n⌋ + L(n)·D(n)·w*(N)  [§3.3 + §3.4].  Each node's
letter datum (e, ℓ, h, s₀, u₀, sel) ranges over an explicit p-free alphabet:
e, ℓ ≤ n, g, μ ≤ n, h ≤ h*(N) [D], and the frame coordinates satisfy s₀ ≤ n,
u₀ ≤ B(n,N)·h*(N)·n (cumulative constrained height along the branch).  So
the alphabet has size ≤ 𝒜(n,N) := n⁴·(h*(N)+1)·(n·B(n,N)·h*(N)+1)·n², and a
tree is determined by its set of branch histories (at the built corpus a
`MovesT.VTree` IS its chain set; `TreePin.vt_inj` transports this to
`F.Tree σ`), giving

    T(n,N) := (𝒜(n,N) + 1)^{ n·(B(n,N)+1) },

independent of p.  Crude but explicit; this is SQ.0's "CONCLUSION (given
(a)–(d))" arithmetic, made concrete.

Status summary: slice_bound and zero_gain are REDUCED to A (known math,
needs the e·g strengthening of `degProd`), B (carried), C (the one real
charging seam — the note's TRACK-COUNT danger, localized to run-break
locality), D (the SQ.0(a)/(b) budget with the lcm(1..n) lattice), E (minor).
No clause needs anything p-dependent: p-uniformity is automatic because
every bound above is combinatorial in the letter data.

---

## §4 Recommended disposition (statement repair; requires sign-off)

Replace the population count in `track_restarts` by the run count, which the
X vocabulary already expresses (no weight field needed):

```lean
-- counts maximal blocks of consecutive {recT1,t4}-population nodes
-- within H.filter (·.continuing); Lean-definable by List recursion
track_restarts : ... → runCount H ≤ L
```

Then: (R) + Lemma A derive the repaired row with L(n) = ⌊log₂ n⌋ + 1; the
note's TRACK-COUNT face is faithfully weaker than or equal to the (t3)
reading; `zero_gain`/`genuine_bound`/`slice_bound` keep their exact shapes
and their §3 reductions; `SlotsG5_trackRule` (h1) must be re-pointed off the
raw Pop counters at the same time.  If instead the row is kept as typed, the
capstone's K7 premise is permanently undischargeable (Theorem 1) and
`theoremU` can never fire at the real instance — the fence status should say
"refuted at the intended instance", not "open".

VERDICT: REFUTED (the `track_restarts` clause as typed, at the intended
instance — explicit family, every p, every n ≥ 2; mechanism machine-checked
and matching the corpus's own KD1 census).  The remaining clauses
(`zero_gain`, `genuine_bound`, `slice_bound`) and the note's true TRACK-COUNT
are REDUCED to Lemmas A–E above, with L(n) = (n−1) + 2⌊log₂ n⌋ ≤ n²,
D(n) = lcm(1,…,n), and an explicit p-free T(n,N); one new unconditional
lemma (R) is Lean-provable immediately.

---

## NUMERIC-TESTS

T1 (RUN, PASSED 2026-07-31): `verification/openmath/m01_quad_walker.py` —
exact-valuation D.10 walk on (x−a)(x−b).  Output: #recenterings = m for the
§1 family, p ∈ {2,3,5}, m = 1..10 (vdisc = 2m+2 row printed); #recenterings
= #nonzero shared digit positions on 200 randomized families (p = 3,
m ≤ 20).  Confirms Lemma 1.1's induction exactly; any constant-L candidate
dies at m = L+1.

T2 (proposed, engine-level): pad the §1 family to cubics f_m·(x−u), u a unit
with u ≢ roots mod 2, p = 2, m = 1..12, and walk each through the project's
exact cubic walker (`verification/x_n3_probes.py` run_box translation, or the
KD1 walker) at N = m+4.  CONFIRMS Theorem 1 if `countPop .recT1 + .t4` on
the cluster branch equals m (monotone in m); REFUTES my engine-reading if the
engine compresses the run into O(1) nodes (then this attempt's Theorem 1
fails and the row could be true — decisive discriminator).

T3 (proposed): re-walk the exhaustive cubic box (2²⁴, N = 8, p = 2) and the
quartic cylinder (2²⁶, N = 10) computing per-history runCount (maximal
consecutive {recT1,t4} blocks) and #incT12 + #t3.  CONFIRMS (R) if
runCount ≤ #incT12 + #t3 + 1 with zero exceptions, and the repaired row if
runCount ≤ ⌊log₂ n⌋ + 1 (= 2 at n = 3, 4).  Expected from the KD1/KD9
histograms: max runCount 1–2.

T4 (proposed, Lemma A falsifier): same boxes; check max #incT12 + #t3 ≤
⌊log₂ n⌋ (= 1 at n = 3; = 2 at n = 4) per history.  ANY history with two
increment nodes at n = 3 refutes Lemma A's e·g ≥ 2 reading and voids §3.2,
§3.3 — the single most valuable cheap falsifier of this attempt.

T5 (proposed, Lemma D lattice): same boxes; verify every consumed side value
and key weight lies in (1/lcm(1..n))·ℤ (KD9 reported all gains in 1·ℤ there;
stress with a p = 2, e = 3 wild family, e.g. Eisenstein-cubic clusters, where
denominators 3 must appear at n ≥ 3... expected in (1/3)ℤ).

T6 (proposed, TRACK-COUNT fit): recount the TRACK-probe (t1)+(t2)+(t3) on
both boxes against L(3) = 4, L(4) = 7 (§3.2).  Already on file: max 3 (4
incl. base frame) at n = 3, 2 (3) at n = 4 — PASSES; a future exceedance
kills the §3.2 constants but not the reduction shape.
