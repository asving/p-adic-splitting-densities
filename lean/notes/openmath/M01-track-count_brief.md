# M01-track-count — problem brief (neutral, self-contained)

## One-line statement

For each degree n, produce four p-INDEPENDENT quantities — L(n) ∈ ℕ, D(n) ∈ ℕ,
w*(N) : ℕ → ℕ, T(n,N) : ℕ → ℕ — and prove, for the canonical Okutsu–Montes
factorization trees of monic degree-n polynomials over ℤ_p, simultaneously at
EVERY prime p: (i) a bound L(n) on the "recentering population" of every branch
history, (ii) the zero-gain budget d_zero(H) ≤ L(n)·D(n)·w*(N) on branches
decided by level N, (iii) the genuine-increment bound ≤ n·N on such branches,
and (iv) the slice bound: at most T(n,N) canonical trees of any fixed verdict
type have decision threshold ≤ N.  (Or: refute a clause at the intended
instance and say exactly which; the Lean statement below is normative.)

## Background: the ambient project and the object

The corpus formalizes a uniformity theorem: for each degree n and each
*splitting type* σ — a multiset of pairs (e,f) with all entries ≥ 1 and
Σ e·f = n — the density of monic degree-n polynomials over ℤ_p whose
factorization over ℚ_p has ramification/residue-degree type σ equals a single
rational function R_σ(q) evaluated at q = p, for all primes p simultaneously.
The engine is an Okutsu–Montes / MacLane-style classifier: for f monic of
degree n over ℤ_p (nonzero discriminant), a canonical factorization tree
T_can(f) is grown by iterated Newton-polygon reads.  Each *continuing node* of
the tree is one read: a side S of the Newton polygon of the current
approximation ("key" / key polynomial φ, in a recentered coordinate frame),
together with a *selection* of one irreducible factor of the residual
polynomial of S.  The letter data of a node:

- e ≥ 1, h ≥ 1 with gcd(e,h) = 1: the side has slope −h/e in lowest terms;
- ℓ ≥ 1: the residual degree of the side (horizontal length = e·ℓ; the
  residual polynomial of S has degree ℓ);
- (s₀,u₀): the lattice coordinates of the side's initial point (its frame);
- selection = (g,μ) with 1 ≤ g, 1 ≤ μ, μ·g ≤ ℓ: the chosen irreducible
  residual factor has degree g and multiplicity μ; selection = ⊥ means the
  node is terminal (a leaf read);
- a Boolean isIncrement: whether the node *grows the key* (the new key degree
  is e·g times the old — a genuinely higher-order type in Montes terms) or
  *recenters* (a MacLane/Montes refinement: same key degree, better center;
  the source note calls this a "D.10 recentering", possible only when the
  read has e = 1).

A *branch history* H is the list of node letters along one root-to-leaf branch
of T_can(f).  The *stratum* of H is the set of f' in the monic box sharing the
history (same read data); *threshold(H)* is the least N such that the stratum
of H is a finite union of level-N digit cylinders (i.e. is determined by the
coefficients mod p^N; the decomposition note's Theorem 2.1 supplies
finiteness of this N per stratum).  A tree is *decided at level N* (threshold
≤ N) when every branch is terminal and certified by level-N data.

## The Lean form (normative)

From `lean/LeanUrat/MovesX/Defs.lean` (abridged; all laws included):

```lean
structure XNode (n : ℕ) where
  e ell h s0 u0 : ℕ
  sel : Option (ℕ × ℕ)
  isIncrement : Bool
  epos : 1 ≤ e;  hpos : 1 ≤ h;  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false

abbrev XHistory (n : ℕ) := List (XNode n)

def rowOf (ν : XNode n) : Row :=      -- rows T1..T5
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3) else .T4

inductive Pop | incT12 | recT1 | t3 | t4   -- populations of continuing nodes

def popOf? (ν : XNode n) : Option Pop :=   -- none on terminal nodes
  ... (T1 & isIncrement → incT12 | T2 → incT12 | T1 & ¬isIncrement → recT1
       | T3 → t3 | T4 → t4)

def countPop (H : XHistory n) (c : Pop) : ℕ := (H.filter (popOf? · = some c)).length
def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
```

Row semantics: T1 = any side with residual degree ℓ ≥ 2 (increments and
recenterings both occur); T2 = ℓ = 1, e ≥ 2, h ≥ 2 (increment); T3 = ℓ = 1,
e ≥ 2, h = 1 (increment); T4 = ℓ = 1, e = 1 (recentering); T5 = terminal.
So `countPop H .recT1 + countPop H .t4` counts ALL recentering nodes of H,
and `countPop H .incT12` counts the T1/T2 genuine increments.

The carrier interface: `MonicBox n p` = monic degree-n polynomials over ℤ_p;
`discZero` its zero-discriminant locus; `vdisc f` = v_p(disc f).  `GMNIndex`
packages an index function `ind : MonicBox n p → ℕ` and an abstract stratum
relation `inStratum : MonicBox n p → XHistory n → Prop` with the law
2·ind(f) ≤ vdisc(f) off discZero.  `XCtx n p` packages, per f, a rooted
branch type `Branch f` with `hist : Branch f → XHistory n`, well-formedness
`HistWF` (only the last node may be terminal; the product of e over
continuing increment nodes is ≤ n), and `threshold : Branch f → ℕ` (Theorem
2.1's per-stratum N₀).  `XFamily n` carries `ctx p` and `gmn p` for EVERY
prime p, with `gmnLink : every branch's history lies in its own stratum`.
These are HYPOTHESIS structures: the intended instance (owner: the wave-D /
classifier-engine work) is the canonical-tree data just described, and any
proof of the present obligation is about that intended instance.

From `lean/LeanUrat/MovesU/DefsLedger.lean:199` (verbatim, the obligation):

```lean
structure Cl7Kernel (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C) where
  L : ℕ
  Dden : ℕ
  wstar : ℕ → ℕ
  Tbound : ℕ → ℕ
  hL : 1 ≤ L
  hD : 1 ≤ Dden
  track_restarts : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (H : MovesX.XHistory n), f ∉ MovesX.discZero n p →
    (KC.XF.gmn p).inStratum f H →
    MovesX.countPop H MovesX.Pop.recT1 + MovesX.countPop H MovesX.Pop.t4 ≤ L
  zero_gain : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f) (N : ℕ), (KC.XF.ctx p).threshold b ≤ N →
    MovesX.dTotal ((KC.XF.ctx p).hist b)
        - MovesX.countPop ((KC.XF.ctx p).hist b) MovesX.Pop.incT12
      ≤ L * Dden * wstar N
  genuine_bound : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f) (N : ℕ), (KC.XF.ctx p).threshold b ≤ N →
    MovesX.countPop ((KC.XF.ctx p).hist b) MovesX.Pop.incT12 ≤ n * N
```

Note the binder order: L, Dden, wstar, Tbound are fixed BEFORE any prime is
quantified — one datum must serve every prime simultaneously (this kills the
trivial "per-p finite maximum" instantiation).  `KC : KernelCarriers` carries
the XFamily; `KC.XF.gmn p` and `KC.XF.ctx p` are the per-prime carrier data.

From `lean/LeanUrat/MovesU/BridgeKernels.lean:216`, the consumption row (the
CL-7 slice bound; `F : FiberSeries n p X` carries a type `Tree σ` of
"complete finite realizable canonical trees of verdict type σ", a threshold
`thr : Tree σ → ℕ`, and `thrSlice σ N : Finset (Tree σ)` characterized by
`T ∈ thrSlice σ N ↔ thr σ T ≤ N`):

```lean
  slice_bound : ∀ (σ : SplittingType n) (N : ℕ),
    (F.thrSlice σ N).card ≤ K7.Tbound N
```

i.e. the number of decidable-by-level-N canonical trees of any one splitting
type is at most T(n,N), the SAME T(n,N) at every prime.

## The source-note displays this transcribes

The proof note (MOVES, §U-SQUEEZE SQ.0, lines 12925–13018) owns this kernel
area.  Its display, abridged:

- (a) HEIGHT BUDGET [derived]: on branches with threshold ≤ N every read
  height h is ≤ h*(N) (each move constrains digit levels ≥ an affine function
  of its heights, and every constrained level is ≤ N);
- (b) KEY-WEIGHT BUDGET [derived given (a)]: every key weight ≤ w*(N);
- (c) MULTI-TRACK ZERO-GAIN BOUND [open]: d_zero(H) ≤ L(n)·D(n)·w*(N), where
  d_zero = #continuing non-genuine-increment nodes, via (c1) an assignment of
  every zero-gain move to one of ≤ L(n) monotone weight TRACKS (keys,
  branches, and ladder restarts each open a track), (c2) a common denominator
  D(n) with all key weights in (1/D(n))·ℤ so each zero-gain move climbs its
  track by ≥ 1/D(n), (c3) a displayed interval of width ≤ w*(N) containing
  every track's weight;
- (d) LEDGER BUDGET: #genuine-increment nodes ≤ n·N on threshold-≤-N branches.

and the note's named open lemma, quoted verbatim:

> **TRACK-COUNT (OPEN).** Every degree-n canonical history H admits a track
> assignment as in (c1) with at most L(n) tracks, L(n) explicit — i.e. the
> number of track-OPENING events (key creations, branch openings, ladder
> RESTARTS) in H is bounded by a function of n alone, uniformly in p, N, and
> depth.  The danger is precisely the restarts: each restart must be charged
> to a monotone consumable (a key-degree drop, a branch-budget decrement, or
> a weight-lattice coarsening) that can occur ≤ f(n) times; the candidate
> L(n) ≤ n² is NOT accepted without that charging argument.

with the sealed per-node event recognitions ((TRK-RULE), same note): (t1) key
creation; (t2) branch opening (each member beyond the designated continuing
one); (t3) LADDER RESTART — "a recentering node at which the current monotone
weight ladder is abandoned (the strict-climb chain broken by the frame
change) and a new ladder begins on the same branch."

Also relevant, from the same note's §X-EXHAUST X.1b (accepted engine
content): each recentering strictly increases the current key's weight — "the
new key's weight is the consumed side's value, > the old key's weight, and
subsequent side values only grow within the frame" — and its own open kernel
WEIGHT-CHARGE: #{recentering nodes of H} ≤ s(n)·v_p(disc f) with explicit
s(n) (status OPEN there).

## What is already proved / recorded in the corpus

1. `bridge_slice_finite` (BridgeKernels.lean:182, PROVED, Lean-core): at each
   fixed prime p and level N, the threshold-≤-N slice of the (realized,
   σ-typed) canonical tree family is FINITE — by pigeonhole into the level-N
   coefficient box (a p-DEPENDENT count; no p-uniform bound).
2. `TreeSeam.finiteness_stack` (DefsLedger.lean:243, PROVED): the partition
   identity decided_σ(N) = p^{nN} · Σ_{thr(T)≤N} μ(fiber T), consuming the
   Finset structure of the slice.
3. `kd6_ladder_count_le` (Kernels/KD6.lean:100, PROVED from carrier laws):
   for ANY functional w : XHistory n → ℚ taking values in (1/D)ℤ,
   non-decreasing under appending any node and climbing ≥ 1/D at every
   recentering-population node, #recT1(H) + #t4(H) ≤ D·(w(H) − w([])).
4. `kd2a_vdisc_pos_of_not_squarefree` (Kernels/WeightChargeRed.lean:94,
   PROVED): f̄ not squarefree mod p ⇒ vdisc f ≥ 1; and machine-checked
   implications (KD3/KD4, same file): a constant recentering bound of
   `track_restarts`'s shape + "a recentering forces vdisc ≥ 1" together give
   the note's WEIGHT-CHARGE.
5. `HistWF.degProd` (MovesX/Defs.lean:129, carried law): along a history the
   product of e over continuing increment nodes is ≤ n.
6. The note derives (not yet in Lean): #T3 nodes per branch ≤ ⌊log₂ n⌋ (each
   T3 multiplies the key degree by e ≥ 2).
7. Status rows: the `slice_bound` docstring records "OWNER: [4]; TRACK-COUNT
   is permanently fenced, so this row is carried, never discharged this
   campaign."  A blueprint escalation (BRIDGE_BP4_KERNELS_2026-07-30.md,
   E-1) records that the constant-L face `Cl7Kernel.track_restarts` "has NO
   supported general route in any blueprint and is plausibly false
   (fixed-degree increasing-vdisc stress family)"; no prover is assigned to
   it this campaign.
8. Recorded computational data (verification/probe_results_2026-07-30.txt,
   units KD1/KD9/TRACK-probe; exhaustive boxes, p = 2):
   - cubic box (all 2²⁴ coefficient triples mod 2⁸): per-f maximum of
     `countPop .recT1 + countPop .t4` by vdisc: vd 2 → 1, vd 4 → 2, vd 6 → 3,
     vd ≥ 8 → 4 (trend recorded GROWING); run-length histogram of consecutive
     recentering chains {1: 642624, 2: 83968, 3: 9152};
   - quartic cylinder (2²⁶ at N = 10): max count 2 at vd 24–38, histogram
     {1: 3047424, 2: 147456};
   - (TRK-RULE) track-OPENING counts on the same boxes: max 3 (cubic), max 2
     (quartic); ZERO (t3) ladder restarts observed; zero recenterings with
     zero key-weight gain (the strict climb held everywhere probed).

## What a proof must deliver

At the intended instance (canonical Okutsu–Montes trees over ℤ_p, histories =
branch read sequences, stratum/threshold as above), with all four data
p-independent and explicit:

1. `track_restarts`: #T1-recenterings + #T4 nodes ≤ L(n) for EVERY stratum
   history of every f with disc ≠ 0 — note: no threshold/level hypothesis is
   available in this clause;
2. `zero_gain` and `genuine_bound` on threshold-≤-N branches, as displayed;
3. `slice_bound`: #(canonical trees of verdict type σ with threshold ≤ N)
   ≤ T(n,N) at every p.

A refutation of a clause at the intended instance is equally a deliverable —
then the exact failing clause, the witness family, and a faithfulness
analysis (does the Lean row state MORE than the source note's TRACK-COUNT /
SQ.0 display it cites?) are required.  Statement changes to the frozen Lean
structures require explicit sign-off; the statement-fence applies.
