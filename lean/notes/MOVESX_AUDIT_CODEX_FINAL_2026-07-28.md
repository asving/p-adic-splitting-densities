# MovesX §X-EXHAUST — Codex FINAL CONFIRMATION audit of blueprint REV 4 (2026-07-28)
# Verdict: ACCEPT (0 crit / 0 gap) — full raw Codex transcript below

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa400-ef3b-7d11-8ead-f50a7c46447b
--------
user

You are the semantic auditor for a Lean formalization blueprint. You verify
FAITHFULNESS of proposed Lean statements to a frozen mathematical note; you fix
nothing. Quote each offending unit spec and classify: CRITICAL (the Lean
statement says something different from, weaker than, stronger than, or vacuously
satisfiable relative to the note's display) vs GAP (ambiguity, missing
hypothesis-field, underspecified Defs dependency). Then give counts and a verdict
line 'ACCEPT' or 'REJECT (n crit / m gap)'.

Check EVERY unit spec for, in one pass:
1. FAITHFULNESS: the `statement` field says exactly what the quoted `moves_ref`
   display says — same quantifier order, same side conditions, same edge cases
   (empty menus, m = 1, N = 0, the (BDY) conventions).
2. NON-VACUITY: no statement satisfiable by an empty/degenerate instance of its
   own hypothesis structures (the trap that killed the pre-rebase chain — check
   each structure has an inhabitation story or an explicit instance unit).
3. HYPOTHESIS FIDELITY: every open kernel the note attaches to a claim appears in
   `hypothesis_fields` — never silently dropped, never silently strengthened into
   a definition, never smuggled into an axiom (the axiom policy allows PUBLISHED
   statements only).
4. DEFS SOUNDNESS: the proposed Defs skeleton — no definition that secretly
   decides an open question (a def that computes what the note only hypothesizes
   exists); typing plausible in Lean 4 + Mathlib.
5. DECOMPOSITION: units genuinely short (one display each); flag any unit whose
   sketch cannot fit its statement (a hidden multi-lemma unit).

The note text is the sole ground truth. Do not trust the blueprint's prose
summaries of the note; check against the quoted displays and the pasted note.
Write NOTHING to disk. Output: the numbered findings, counts, verdict.

This is the FINAL CONFIRMATION pass on REV 4. History: you rejected rev 1 (14/11) and rev 2 (11/2); a fresh independent auditor rejected rev 3 at 2/2 (X2BridgeP finite-branch qualifier; a Mathlib signature) and verified all arithmetic and derivation chains clean; rev 4 made the four surgical repairs (§6 cumulative table). SETTLED architecture (audit execution, not design): all kernels are Props over the one shared XFamily n (concrete MonicBox/vdisc via Polynomial.discr); ValExt-free unconditional statements with the valuation-extension content inside the tail-derivation units; XG.3/XG.4 derive X.3 from note-cited inputs. Sweep end to end one last time; re-derive the arithmetic spot values yourself (tail count 4 at (n,p,D)=(2,2,0), 1/4 at D=4; the branch bound 2·dTotal ≤ (2s+1)·vdisc + 2⌊log₂n⌋). A clean pass = ACCEPTED for formalization.

THE FROZEN NOTE (ground truth):
## §X-EXHAUST — the discriminant-tail exhaustion (assembly note 7, = plan [5])

*(2026-07-27. Assembly note [5] per ASSEMBLY_PLAN_2026-07-26.md §5, drafted
under the REV 15 DRAFTING RULING: X.1a/X.1b unconditional drafting ([2a]
dual-accepted; decomp §3 accepted perimeter), X.2 in hypothesis-displayed
form (its M4a-tail leg a NAMED [2b]-owed hypothesis, discharged at [2b]'s
acceptance, alongside the standing CONDITIONAL-ON-X.1b tag). Consumes: the
decomposition note (MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md, ACCEPTED) —
Lemma 3.2 (depth ⟹ ind ⟹ disc; GMN pins (P1)–(P3) verbatim in
GMN_citations.md §"§4 index machinery"), Lemma 3.3 (the elementary
discriminant tail (3b)), Cor 3.4 (the Desc_d envelope (3c)), Thm 2.1
(N-stability); the dual-accepted §B2-DEF (D.0 scale bookkeeping, D.8/D.10
landings, D.10's weight-climb, D.11's per-move ledger, D.12's literature
dictionary); the dual-accepted §M-SPECIES (the letter fields (e, h, ℓ,
selection) this note's table is keyed by); the dual-accepted §D4-R (T_can,
branch histories) and §T-ASSEMBLY ((TGT)'s undecided complement, (NS-ROUTE),
TB-CAP — the objects X.3 must type against). OPEN KERNELS of this note,
named up front: X.1a's residue (X1a-ALIGN) — the raw-table → per-order-index
dictionary; X.1b WEIGHT-CHARGE (an OPEN kernel with its own STALL-probe; NO
derivation is claimed below); X.2 PROGRESS — the linear coercivity. Nothing
below asserts a closed envelope: every conditional display carries its tag.)*

**What this note is.** The exhaustion tie-in: the campaign's wall sidestep
(PROJECT_STATE: "exhaustion via pointwise depth ⟹ disc + the elementary
discriminant tail — no per-depth identities") restated in MOVES vocabulary,
in four layers. X.1a: a per-species INDEX TABLE turning classifier depth
into GMN index, hence into v_p(disc f) — pointwise, measure-free. X.1b: the
budget for the UNCERTIFIED nodes — those with no positive per-side bound
(T3/T4) or with an undischarged ALIGN sub-clause (the open kernel
WEIGHT-CHARGE). X.2: the quantitative dichotomy threshold ⟹ deep-or-tall,
whose two mass legs are this note's only measure inputs. X.3: the density
form (TGT) consumes — undecided mass → 0 — assembled from X.1a + the
elementary tail, with every conditionality displayed. The SELFLOOP wall
stays sidestepped: no per-depth count identity, no pivot, no child-law
identification is used anywhere in this section.

### X.0 Objects (the two-track depth split; plan §5 REV 2)

Fix n and a prime p. H ranges over branch HISTORIES: finite chains
(ν₀, …, ν_k) of a canonical tree T_can(f) (§D4-R L2/L3), each node νᵢ a read
with §M-SPECIES letter fields (tag; D, w, W; e, h, ℓ = w′/e; λ; selection
(g, μ) or ⊥; flank) in its own frame (§B2-DEF D.0's raw side coordinates).
Definitions, per the plan's REV 2 redesign (the rev-1 premise "every MOVES
node is a unit GMN event" is WITHDRAWN — pass-1 obstruction 7):

- d_total(H) := #{continuing nodes of H} (selection ≠ ⊥; level-0 cluster
  OPENINGS are NOT nodes — (P3) caveat (iii), the x² − p exclusion; NB the
  §M-SPECIES ROOT-tag LETTERS are genuine side READS and ARE nodes).
- (CD) CERTIFIED DEPTH — pinned ONCE here, used in every display below
  (rev 2; pass-1 findings 1–2):
    d_cert(H) := #{continuing nodes ν of H whose table row carries a
    positive per-side index bound (rows T1, T2) AND whose ALIGN sub-clause
    — (ALIGN-inc) for increments, (ALIGN-rec) for D.10 recenterings — is
    DISCHARGED at cite time};   d_unc(H) := d_total(H) − d_cert(H).
  At today's discharge state (neither sub-clause displayed) d_cert ≡ 0;
  given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the
  T1 recenterings. The SEMANTIC quantity d_gen^sem := #{nodes with actual
  per-order gain ind_r ≥ 1 in Thm 4.18's accounting} is hereby DEFINED and
  used NOWHERE below: the table certifies per-side LOWER bounds only, and
  a row-T3/T4 "0" means "no positive bound certified from this side" —
  NEVER "actual ind_r = 0" (polygon placement, other sides, and cross
  terms are never inspected). d_unc's population: all T3 and T4 nodes
  always, plus every T1/T2 node whose sub-clause is undischarged.
- max h(H) := the largest slope height h_r over H's reads (raw, in-frame);
  convention max h(∅) := 0 for a read-free history (rev 4, pass-3
  finding 1 — no empty max is ever taken).
- threshold(H) := the least N such that H's stratum is a finite union of
  level-N digit cylinders (Thm 2.1's N₀; §C's N(H, Z) at trivial Z).
- Desc_d := the union of all strata still descending at certified depth
  ≥ d (the decomposition note's object, keyed here by d_cert per (CD)).
- Undec(N) := the level-N undecided set: f in the monic box whose level-N
  digit data does not certify a complete τ-halted tree with every leaf
  cap-detected ((τ-irr)/(τ-hen) with their TB-CAP caps, [3t] §T.2). Per
  (NS-ROUTE)(NS-d), ns-leaf f's lie in Undec(N) at EVERY N.

The TWO-TRACK DESIGN: X.1a certifies which species consume index (feeding
d_cert); everything it cannot certify is charged to d_unc and handed to
X.1b's budget. The tracks meet only in X.2's envelope arithmetic.

### X.1a The index table (the genuine-event dictionary; kernel with residue (X1a-ALIGN))

**The claim (the displayed pointwise inequality chain).** For every branch
history H of every monic separable f:

  (X.1a)  stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) },

with d_cert per (CD) — conditional exactly on the sub-clauses certifying
the counted nodes; at zero discharge d_cert ≡ 0 and (X.1a) is trivially
true. Via the chain: per-node certified bound (THE TABLE below) → sum
ind(f) ≥ Σ_{orders r along H} ind_r ≥ d_cert(H) (GMN Thm 4.18(1); all terms
≥ 0, so ONE branch's events lower-bound the whole tree's index — no
multiplicity correction is needed for a lower bound, F1-safe) → the index–
discriminant identity v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ) ≥ 2·ind(f)
((P2); reducible case via Def 4.11 + disc(PQ) = disc P·disc Q·Res(P,Q)²).
The first inclusion is the definition of Desc; the second is the displayed
chain. Measure enters NOWHERE here.

**The GMN apparatus consumed (pinned verbatim, GMN_citations.md §"§4 index
machinery"; all quantities on ONE node's window polygon N in its own frame,
which the §B2-DEF D.12 literature dictionary aligns with GMN's polygon —
GMN's theorem of the product ↔ D.7(iii), residual operator ↔ R).** For a
side S of finite slope −h/e (lowest terms) with horizontal length E = eℓ,
height H = hℓ, residual degree d(S) = ℓ:

  (IND)   ind(S) = ½(EH − E − H + d) = ½·ℓ·(ehℓ − e − h + 1),

counted as lattice points BELOW OR ON the finite part of N, STRICTLY ABOVE
the horizontal line L through N's last point, STRICTLY BEYOND the vertical
line L′ through the initial point of the finite part ((P1), Remark 4.14 —
the on-or-below convention, resolved 2026-07-22; discriminating witness
x² + 6x + 36 over ℤ₃ on record there). Pick-style split, used per row:
strict-interior count (EH − E − H − d)/2 + 1, on-side non-vertex count
d − 1. Multi-side polygons only ADD (Σ_{i<j} EᵢHⱼ ≥ 0), so per-side lower
bounds are safe. Slope −∞ sides contribute 0 (Def 4.12).

**THE INDEX TABLE (explicit; rows keyed by the §M-SPECIES letter fields of
the node's read side and selection; ind(S) evaluated from (IND) — pure
arithmetic, DERIVED; the EVENT column is the GMN per-order verdict and is
conditional on (X1a-ALIGN) below, per sub-clause).** Every continuing node
of every history falls in exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h; the
selection constraint μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection
onto an ℓ ≥ 2 side — so rows T3/T4 carry only (g, μ) = (1, 1) selections):

| row | species class (letter fields) | witness lattice point on the node's polygon | ind(S) from (IND) | raw verdict | GMN event verdict |
|---|---|---|---|---|---|
| T0 | LEVEL-0 REDUCTION-CLUSTER OPENING — the passage to one irreducible-cluster track, PRECEDING the root read; not a §M-SPECIES letter (rev 2, finding 5: §M-SPECIES ROOT-tag letters ARE side reads and classify into T1–T5 by their (e, h, ℓ, selection) fields like every other read) | — (not a node; (P3)(iii), x² − p exclusion) | — | not counted | not counted |
| T1 | any side with ℓ ≥ 2, any e, h — ALL reads on such sides live here: increments with μ·g ≥ 2, μ ≥ 2 recenterings (D.10 landings), AND the μ·g = 1 engine-continuing selections on ℓ ≥ 2 sides (the e ≥ 2, (g,μ) = (1,1) increments and the e = 1, (g,μ) = (1,1) recenterings — Fable cosmetic 3: the old gloss omitted these; the row's ind(S) formula always covered them) | (s+e, u+(ℓ−1)h): ON S one e-step from its initial point; strictly above L (height ≥ h ≥ 1 over N's last point since ℓ ≥ 2); strictly beyond L′ (s+e > s) | ½ℓ(ehℓ−e−h+1) ≥ ½ℓ·h(ℓ−1) ≥ 1 [e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)] | POSITIVE side bound | GENUINE, GIVEN (ALIGN-inc) for increments / (ALIGN-rec) for recenterings |
| T2 | one-slot ramified tall: ℓ = 1, e ≥ 2, h ≥ 2 (increment, g = 1, μ = 1; key degree ×e) | explicit witness (s+1, u+1) [S runs (s, u+h) → (s+e, u): strictly beyond L′ (s+1 > s), strictly above L (u+1 > u), strictly below S ⟺ (e−1)(h−1) > 1 — true since e, h ≥ 2 and gcd(e,h) = 1 excludes (2,2)]; no on-side point counts (both endpoints excluded — see rulings) | (e−1)(h−1)/2 ≥ 1 | POSITIVE side bound | GENUINE, GIVEN (ALIGN-inc) |
| T3 | one-slot ramified flat: ℓ = 1, e ≥ 2, h = 1 (increment, g = 1, μ = 1) | interior count (e−1)·0/2 = 0; endpoints excluded | 0 | NO side bound | NOT-CERT (rev 2, finding 1: "0" = no positive per-side bound; actual ind_r may be > 0) — and DEGREE-CHARGED: each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived; charged additively, never absorbed) |
| T4 | one-slot unramified: ℓ = 1, e = 1, any h — the (g, μ) = (1, 1) recenterings (D.10; Species lemma: e_read = 1) | only the two endpoints are lattice points on S (gcd(e,h) = 1); both excluded | (1−1)(h−1)/2 = 0 | NO side bound | NOT-CERT (same finding-1 semantics) — the STALL population; weight-climb strict (D.10); in X.1b's burden |
| T5 | terminal read (selection ⊥; the confirming W = 1 read included) | no descend event | (any) | not counted | not counted — consistency: the (P1) witness's terminal read has ind₂ = 0 (Thm 4.18 equality clause) |

**Endpoint and zero-contributing cases, ruled explicitly (the pass-1 EXHAUST
failure class — a (P1) convention slip — fenced by display):**
- The INITIAL vertex of the finite part never counts: excluded by Remark
  4.14's strictly-beyond-L′ clause.
- The LAST point of N never counts: it lies ON L (strictly-above fails).
  Hence on an ℓ = 1 LAST side both endpoints are excluded, and gcd(e,h) = 1
  gives no interior lattice point ON the segment: only the strict-interior
  count (e−1)(h−1)/2 survives — rows T2/T3/T4's arithmetic.
- A non-last ℓ = 1 side's RIGHT endpoint is the next side's initial vertex
  — on-or-below and strictly above L, so it COUNTS, but its index unit is
  charged to the POLYGON (cross terms Σ EᵢHⱼ), not to this side's event;
  the table's per-row verdicts never consume cross terms (safe: they only
  add to lower bounds, never subtract).
- Flank/co-factor sides of the window polygon: contribute ≥ 0; never
  consumed. Slope −∞ (root openings inside a window): 0 by Def 4.12.
- The T1 witness point at ℓ ≥ 2 is ON S, hence needs (P1)'s ON-OR-BELOW
  convention — this is exactly where the strictly-below reading would
  zero out every e = 1 genuine event ((P3): "would NOT count under a
  strictly-below convention"). The convention is PINNED, with the ℤ₃
  discriminating witness recorded at (P1).

**(X1a-ALIGN) — the kernel's named residue (what keeps X.1a a kernel rather
than a closed lemma).** The table's raw verdicts are computed on the MOVES
node's window polygon in its own frame's raw side coordinates (§B2-DEF D.0).
Thm 4.18's accounting evaluates ind_r on GMN's N_r^−(P) in v_r-NORMALIZED
coordinates, once per order r ((P3) caveat (i)), with representative-
dependent ind_t ((P3) caveat (ii); MOVES canonical lifts must be placed in
GMN's "universally fixed family" — one admissible choice suffices). Two
sub-clauses, separately dischargeable:
- (ALIGN-inc): INCREMENT nodes (key degree grows). Each opens a genuinely
  new higher-order type, so successive increments of one branch sit at
  distinct orders; the duty is the normalization crossing — that D.0's
  scale bookkeeping (w = e·w_prev + j·h slot minimum) reproduces Def 2.5's
  v_r-normalization so the raw ind(S) computed above IS the normalized one.
  Expected mechanical via the D.12 dictionary; NOT yet displayed — open.
- (ALIGN-rec): SAME-DEGREE RECENTERINGS (D.10). GMN v2 increments the order
  at every refinement ((P3): "here they increment the order"; later Montes
  papers optimize refinements away), while the MOVES ledger keeps the key
  degree and climbs weight. The duty: place each MOVES recentering run in
  Thm 4.18's order bookkeeping WITHOUT double-counting index across the
  run's successive polygons — the exact "what counts as an event" subtlety
  that produced the (P1) convention hunt AND the pass-1 obstruction (rev
  1's per-node unit-event claim was withdrawn against it). Until
  (ALIGN-rec) is displayed, a T1-row RECENTERING's GMN verdict is only
  raw-certified: its normalized per-order gain could degrade. Rev 2
  (finding 2): by (CD) such a node was never IN d_cert — it sits in d_unc,
  inside X.1b's burden, and (X.1a) (which counts d_cert only) is
  untouched. The rev-1 "conservative d_gen" language is REPLACED by (CD):
  one pinned operational definition, used in every display of this
  section; no clause below quantifies over d_gen^sem.

**Assembly of (X.1a), given the table + the discharged ALIGN sub-clauses.**
Along one branch H, its certified nodes (the d_cert population of (CD))
occupy distinct orders r₁ < r₂ < … (ALIGN places them), each contributing
ind_{rⱼ}(f) ≥ ind_t(f) ≥ f₀⋯f_{r−1}·1 ≥ 1 (all ind terms ≥ 0). Thm 4.18(1)
sums over ALL orders and types of the tree, so ind(f) ≥ d_cert(H) for EACH
branch H — the other branches' contributions only help (F1's multiplicity
discipline costs nothing for a lower bound). (P2) then gives v_p(disc f) ≥
2·ind(f) ≥ 2·d_cert(H) pointwise on stratum(H), which is (X.1a). ∎
(conditional exactly on the sub-clauses certifying the counted nodes; the
raw table itself is DERIVED)

### X.1b STALL — the WEIGHT-CHARGE kernel (OPEN; stated exactly, NO derivation claimed)

**What survives from the accepted engine (derived).** Each recentering
(row T4 AND every T1-row D.10 landing) strictly increases the current
key's weight: §B2-DEF D.10 — the new key's weight is the consumed side's
value, > the old key's weight, and subsequent side values only grow within
the frame (convexity). So a recentering run is a strictly climbing ladder
in the weight lattice. What does
NOT follow (pass-2 obstruction 6, on record): a local height budget is not
globally coercive and can itself be unbounded — the affine consequence is
a TARGET, reduced to ONE named missing lemma:

> **WEIGHT-CHARGE (OPEN KERNEL; restated rev 2, finding 2 — the burden is
> the FULL recentering population, not "T4 only": while (ALIGN-rec) is
> undischarged the uncertified T1 recenterings sit here too, so the kernel
> is stated to cover them all).** Every unit of key-weight climbed by a
> recentering ladder is charged, injectively up to a factor s(n), against
> a unit of v_p(disc f) — via the L5fix-Invariant-2 different budget,
> which is itself bounded by v_p(disc f). That is:
>   #{recentering nodes of H} ≤ s(n)·v_p(disc f),  with explicit s(n).

STATUS: OPEN until derived. Charging-route note (material for the kernel,
not a claim): (P2)'s identity v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ) has
a SECOND term — the leaf differents — and the L5fix different budget lives
there; T3's degree charge above shows the pattern (a monotone consumable,
≤ f(n) uses). The T4 ladder's consumable must be exhibited, not assumed.

**Two-step reduction (DISPLAYED; rewritten rev 2, finding 3 — the T3 term
is ADDITIVE, never absorbed into the multiplicative charge).** Given
WEIGHT-CHARGE and (ALIGN-inc) — X.1b ALONE discharges nothing (finding
11), since bounding the increment population consumes (ALIGN-inc) by name:
  d_total = #increments + #recenterings
          ≤ [v_p(disc f)/2 + ⌊log₂ n⌋] + s(n)·v_p(disc f)
  [(ALIGN-inc) certifies every T1/T2 increment, so #non-T3 increments =
  d_cert-increments ≤ v_p(disc f)/2 by (X.1a); #T3 ≤ ⌊log₂ n⌋ (degree
  charge); WEIGHT-CHARGE covers ALL recenterings]
  ⟹  v_p(disc f) ≥ (d_total(H) − ⌊log₂ n⌋) / (s(n) + 1/2)
— affine with named constants and the displayed additive offset; the
geometric-in-d_total envelope survives with rescaled constants ((3c) with
2d replaced by (d_total − ⌊log₂ n⌋)/(s(n)+1/2)).

**CONSUMERS (rewritten rev 3, pass-2 finding 3).** X.2's envelope
constants (hence SQ.3 and every envelope gate layer) are CONDITIONAL-ON-
[X.1b ∧ (ALIGN-inc)] (rev 2, finding 11: the reduction consumes both).
AND X.3(a) — in BOTH its routes: at least the T4-restricted burden
#T4 ≤ s(n)·v_p(disc f) (route (a1)), the full burden in (a2); no
ALIGN discharge ever bounds T4, so no X.3 route avoids this kernel.
Nothing else: RS.1's convergence is Tonelli's (plan §4), SQ.1's finiteness is
SQ.0's (§6), RS.3's gap is ESCAPE's (§4). WEIGHT-CHARGE canNOT yield a
uniform per-cylinder bound B(n) — v_p(disc) is unbounded across a source
cylinder (pass-3 obstruction 3) — so no consumer may cite it for uniform
leakage.

**STALL-probe (exploration-class; runs with this draft; scope per plan REV
7).** Exhaustive p = 2 boxes: the full cubic box 2²⁴ at N = 8 and the
quartic RS-chain conditioned cylinder 2²⁶ at N = 10 (the state-probe
geometry: RS self-loops ARE T4-row recenterings — precisely the
(ALIGN-rec) danger zone). Measure: the max recentering run length and the
per-f ratio #{recentering nodes} / v_p(disc f). One f violating the sealed
candidate s(3) = 2 (X.5(ii)) kills that constant before the kernel is
drafted around it. SCOPE: the probe refutes SEALED CANDIDATE constants
only — it can neither refute nor establish the existential WEIGHT-CHARGE
statement (decided by derivation alone). If the derivation instead finds a
legal UNBOUNDED recentering chain: this is NOT automatically a termination
hole (unbounded finite chain lengths across inputs are compatible with
a.e. termination; even an infinite chain on a measure-zero input is
compatible with a density theorem) — it DEFEATS the envelope and
uniform-leak designs as built; stop, record, adjudicate against L5fix's
precise quantifiers, run plan §8 R4's experiment.

### X.2 PROGRESS — the quantitative dichotomy (target displayed; kernel OPEN; both mass legs hypothesis-displayed per the REV 15 ruling)

**The target (with its linear constants displayed).** There exist constants
c_d(n) > 0, c_d′(n), c_h(n) > 0, c_h′(n) — n-only, p-free — such that for
every branch history H of the FOURTH-PIECE FAMILY (retyped rev 5, pass-4
finding: the family is DEFINED BY ITS OWN PREDICATE, not by an unordered
union's routing — H belongs iff H is a finite branch or prefix of a
complete τ-halted tree AND H is (τ-ns)-FREE (no node of H lies on a
(τ-ns) track: the membership predicate itself excludes them; the 𝒯^ns
union piece is where those live, but the EXCLUSION here is intrinsic) —
with cap(H) TOTAL on the family so defined per the DOMAIN CONVENTIONS:
genuine max on cap-detectable H, := 0 on hen/no-window H;
max h(∅) := 0)
(hypothesis made LEVEL-RELATIVE rev 3, pass-2
finding 2: cap(H) is (X2-BRIDGE)'s H-dependent cap of H's OWN cells; the
rev-2 hypothesis "threshold(H) > N" reached the envelope only through the
struck uniform-cap shift, so the target now carries the combined quantity
the bridge actually delivers):

  (X.2)  threshold(H) + cap(H) > N  ⟹  d_total(H) ≥ d*(N)  OR  max h(H) ≥ h*(N),
         with d*(N) := c_d(n)·N − c_d′(n),  h*(N) := c_h(n)·N − c_h′(n),

both slopes POSITIVE — linear enough in N to yield the exponential
envelope below. No "positive exponents ⟹ done" step is accepted: mixed
height cones can grow nominal exponent and required precision at different
rates; the uniform bound must be exhibited (plan REV 5, pass-4 concern 6).

**The two displayed sub-statements (statuses rewritten rev 2).**
(X2-AFF) [OPEN — a NAMED display duty, DEMOTED from "derived" (finding
  7)]: the affine threshold bound threshold(H) ≤ 1 + c₀(n)·Σ_{r ∈ H} h_r,
  the sum over ALL reads of H (continuing AND terminal). What the accepted
  perimeter gives is only Thm 2.1's finite threshold PER STRATUM; the
  required uniform comparison of every base-level digit cost and frame
  shift against Σ h_r (through D.0's scales, Π e_i ≤ n along a branch,
  D.11's per-move form "largest constrained height + 1") is precisely the
  missing coercive accounting. Neither c₀(n)'s value NOR its existence is
  derived here; (X2-AFF) is owned by the PROGRESS kernel.
(X2-HYP) The hyperbolic dichotomy (DERIVED given (X2-AFF) ∧ (X2-CAP);
  counting FIXED rev 2, finding 6 — H's reads are its d_total continuing
  nodes PLUS at most one terminal read, and X2-AFF sums over reads, so the
  correct inequality is Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the
  d_total = 0 lone-terminal-read history is carried by the +1; chain
  rebased rev 3 on the level-relative hypothesis, both prices in the ONE
  currency Σ h_r, combined constant c₀⁺ := c₀ + c_cap):
  threshold(H) + cap(H) > N ⟹ Σ h_r > (N−1−c_cap)/c₀⁺ ⟹
  (d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹
  d_total(H) + 1 ≥ √((N−1−c_cap)/c₀⁺)  OR  max h(H) ≥ √((N−1−c_cap)/c₀⁺)
  — square-root, NOT linear. This is exactly the gap: the product bound
  cannot give both legs linear (d* = αN and h* = βN make d_total·max h <
  αβN², compatible with Σ h_r > (N−1)/c₀ at large N). Closing (X.2) from
  (X2-HYP)'s shape — by pricing each move's mass cost rather than counting
  heights — is THE kernel duty PROGRESS; until it closes, only the
  √N-envelope below is even conditionally available.

**The envelope (every tag displayed; opening inclusion FENCED rev 2,
finding 8 — it is NOT free).** The rev-1 display jumped from Undec(N) to
the two mass legs with no event inclusion; X.2 speaks of a branch history
with threshold(H) + cap(H) > N (rev-3 form), and nothing yet shows every
f ∈ Undec(N) supplies one. The owed bridge, named and displayed:

> **(X2-BRIDGE) [OPEN — display duty, owned by PROGRESS; cap duty
> REWRITTEN rev 3, pass-2 finding 2: the rev-2 duty "a UNIFORM cap bound
> cap(H) ≤ c_cap(n)" CONTRADICTED the TB-CAP record ("No cap uniform over
> ALL cells of a verdict value exists or is claimed — heights grow along
> deeper shapes") and is STRUCK — no absolute per-n cap exists in the
> perimeter and none may be demanded].** Define, per history H:
>   cap(H) := max over the TB-CAP caps of H's OWN leaf-detection cells
>   ((τ-hen): N_V = 1, proved; (τ-irr): the per-REALIZED-CELL cap N_V,
>   proved, perimeter-conditional) — an H-DEPENDENT, level-indexed
>   quantity, exactly what TB-CAP supplies. DOMAIN CONVENTIONS (rev 4,
>   pass-3 finding 1 — the max was over a possibly empty family; cap is
>   now TOTAL on every H the displays quantify over): cap(H) is DEFINED
>   as a genuine (nonempty) max exactly on the CAP-DETECTABLE branches —
>   those with ≥ 1 window read reaching a (τ-irr) leaf-detection cell.
>   Elsewhere: cap(H) := 0 for every hen/no-window branch — continuing
>   prefixes (no leaf-detection cell reached yet) and root/(τ-hen)
>   branches — because hen detection is determined at level 1 per
>   TB-CAP(hen) (N_V = 1), so the threshold term alone carries them.
>   (τ-ns) branches are EXCLUDED BY THE PREDICATE (rev 5 propagation,
>   pass-5 finding: an unordered union does not route — the exclusion
>   must sit in the membership predicate itself): every quantifier over
>   'finite branch H' in this bridge block ranges over (τ-ns)-FREE
>   branches only (no node of H on a (τ-ns) track — a per-node cell-data
>   predicate per VP's certificate clauses), so cap(H) is TOTAL on the
>   quantified family. Companion convention in X.0:
>   max h(∅) := 0. Bridge statement (honest
>   level-relative form): for a.e. f ∈ Undec(N), SOME (τ-ns)-FREE branch
>   H of T_can^τ(f) has threshold(H) + cap(H) > N. Decomposition owed
>   (KEPT — pass 2: well-posed):
>   Undec(N) ⊆ {disc f = 0} ∪ (𝒯^ns fibers) ∪ {f : T_can^τ(f) has an
>   infinite branch} ∪ {f : ∃ (τ-ns)-FREE finite branch H,
>   threshold(H) + cap(H) > N},
> the first three of mass 0 ((3b)'s corollary; (ns-null), closed; X.3(a)
> with its tags). Open duty (i) (KEPT — pass 2: well-posed): the
> EXISTENTIAL conversion — level-N certification failure of a finite
> complete tree ⟹ some branch's Thm-2.1 threshold or its OWN cells'
> TB-CAP cap exceeds N — displayed with its quantifier; every quantity
> per-branch; NO uniform cap invoked. Duty (ii) is REPLACED by:

> **(X2-CAP) [NEW OPEN KERNEL, rev 3 — the cap-structure bound, stated
> contradiction-free; quantifier retyped rev 4, pass-3 finding 1].**
> There is c_cap(n) with, for every CAP-DETECTABLE branch H (the
> genuine-max domain; on the convention-0 hen/no-window branches the
> bound holds trivially, so it extends to the whole fourth-piece
> family — (τ-ns) branches never enter it):
>   cap(H) ≤ c_cap(n)·(1 + Σ_{r ∈ H} h_r),
> pricing cap growth against H's OWN height data — the same coercive
> currency as (X2-AFF). Level-relative by construction: cap(H) may grow
> without bound along deeper shapes, exactly as TB-CAP records; only its
> RATE against H's heights is conjectured. NOT derived here; owned by
> PROGRESS. The qualitative X.3 below never consumes (X2-BRIDGE) or
> (X2-CAP).

Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF), with μ the box mass (the rev-2
shift N′ := N − c_cap(n) is STRUCK with the uniform cap): the witnessing
branch has threshold(H) + cap(H) > N, and
  env(N) := μ(Undec(N)) ≤ μ{d_total ≥ d*(N)} + μ{max h ≥ h*(N)},
via (X.2) — rev-3 level-relative hypothesis — applied to that branch.
- DEEP LEG [CONDITIONAL-ON-X.1b + (ALIGN-inc)]: by the X.1b reduction
  (rev-2 form, additive T3 offset), d_total ≥ d* ⟹ v_p(disc f) ≥
  (d* − ⌊log₂ n⌋)/(s(n)+1/2), so Lemma 3.3's (3b) gives
    μ{d_total ≥ d*} ≤ (n−1)·p^{−⌈( (d*−⌊log₂ n⌋)/(s(n)+1/2) − n·v_p(n) ) / (n−1)⌉}.
- TALL LEG [(X2-TAILS), a NAMED HYPOTHESIS owed by [2b]/§H-DOMAINS,
  discharged at [2b]'s acceptance — the M4a-tail edge pass-2 found
  missing]: there are C_T(n), c_T(n) > 0 with
    (X2-TAILS)   μ{ f : some read of some branch has h_r ≥ h* } ≤
                 C_T(n)·p^{−c_T(n)·h*}
  — the M4a cone-geometry tail at fixed template, summed over the finite
  [2a] catalogue. Consumed here as a display; NOT derived in this note.
Given (X.2) with linear d*, h* AND both legs AND (X2-BRIDGE) + (X2-CAP):
env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n) (X.1b), c₀
((X2-AFF)), C_T, c_T ((X2-TAILS)), c_cap ((X2-CAP)).
Given (X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) PLUS the same two
leg tags — [X.1b ∧ (ALIGN-inc)] for the deep leg, (X2-TAILS) for the
tall leg (rev 4, pass-3 finding 3: the rev-3 "given only" line omitted
the leg tags and contradicted the CONDITIONALITY SUMMARY; the √N form
replaces only (X.2)'s LINEARITY, never the mass legs): env(N) ≤
c₃′(n)·p^{−c₄′(n)·√N} — subexponential, enough for X.3's qualitative
form, NOT for SQUEEZE's constants.
CONSUMERS: SQ.3/SQ.4 and every envelope gate layer consume (X.2)'s
exponential form — hence they inherit ALL tags above (CL-2, CL-3),
(X2-BRIDGE) included.

### X.3 The density form (what (TGT) consumes; = CL-4; (NS-ROUTE)-compatible typing)

**The elementary discriminant tail (DISPLAYED — accepted Lemma 3.3, proof
on record: Res(f, f′) over the n−1 roots of f′, the a₀-translation, union
bound + Fubini).** For every n ≥ 2, prime p, D ≥ 0:

  (3b)   μ{ f monic deg n : v_p(disc f) ≥ D } ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}
         → 0 as D → ∞;   corollary μ{disc f = 0} = 0.

**Statement (X.3) — the clause (TGT) cites verbatim ([3t] §T.0):** the
undecided complement { f : T_can^τ(f) has an infinite branch or an
undetected halt } has mass 0; equivalently μ(Undec(N)) → 0 (N → ∞), and for
each type σ the tree-fiber series sums the full density:
  Σ_{T ∈ 𝒯^fin complete realizable, typemult(T) = σ} μ{f : T_can^τ(f) = T}
  = density_σ(p),
with the 𝒯^ns fibers' total contribution dropped as 0 [(ns-null) tag
displayed per (NS-c); (ns-null) is PROVED/CLOSED at plan REV 15 — the
single-state admissible-Z argument, four independent verifications — the
tag remains displayed at every consumption per (NS-c)'s rule]. This is the
ONE cite point for [3] (RS.4's total-mass identity Σ_σ = 1 consumes X.3,
NOT the quantitative envelope — plan pass-5 over-conditioning note), for
(TGT)'s undecided-complement clause ([3t] §T.0), and for E0's a.e.-exit
route — the plan's CL-4 consumer list verbatim. SQ.1 is NOT a consumer
(rev 4, pass-3 finding 4 — the rev-3 "[4] (SQ.1's clause (b))" cite is
STRUCK as exactly the drafting error X.4 fences): SQ.1's clause (b) is
Undec(N) BY DEFINITION — the partition statement consumes no mass-zero
input; its "ns fibers ⊆ Undec(N) at every N" is (NS-ROUTE)(NS-d) typing
on the envelope side, whose mass control enters only at SQ.3 through
X.2's envelope; SQ.1's finiteness is SQ.0's alone (plan §6, REV 4
narrowing). X.4's consumer map below is the authoritative form.

**(NS-ROUTE) typing, checked clause by clause.** X.3's finite-level object
is Undec(N) — the complement of the level-N certified decided cells — never
a level-N residue set of an exact ns condition ((NS-b): such a set is
UNDEFINED); ns-leaf f's sit in Undec(N) at every N ((NS-d)) and exit only
in the N → ∞ limit, through (ns-null); the decided side quantifies over
𝒯^fin BY CONSTRUCTION ((NS-a)). No clause of (X.3) forms an exact-ns
finite-level count.

**Assembly (the proof, with every conditionality tagged).**
(a) INFINITE BRANCHES [tag REWRITTEN rev 3, pass-2 finding 3: the rev-2
  ALIGN-ONLY route is STRUCK — (X1a-ALIGN) transports only the certified
  T1/T2 accounting and supplies NO bound on the T4 population (permanently
  NOT-CERT, zero certified side contribution, assigned by this note to
  WEIGHT-CHARGE); citing GMN Cor 4.19's step bound for T4 recenterings
  would need a zero-gain-steps correspondence that is neither an ALIGN
  duty nor derived anywhere. NO route avoids X.1b: the corrected tag is
  [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)], the T4-population
  dependence displayed in both disjuncts].
  Off {disc f = 0} (mass 0, (3b)'s corollary), EITHER route gives every
  branch finite pointwise, by the four-population decomposition
  {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}:
  (a1) (X1a-ALIGN) ∧ X.1b(T4) — both ALIGN sub-clauses certify every
  T1/T2 node (increments AND recenterings), so #T1/T2 = d_cert ≤
  v_p(disc f)/2 by (X.1a) (the D.12-transported GMN Cor 4.19 accounting
  bounds exactly these certified events); #T3 ≤ ⌊log₂ n⌋ (degree charge,
  derived); #T4 ≤ s(n)·v_p(disc f) by WEIGHT-CHARGE RESTRICTED to the T4
  population — the one piece no ALIGN discharge ever covers; OR
  (a2) (ALIGN-inc) ∧ WEIGHT-CHARGE(full) — #increments ≤ v_p(disc f)/2 +
  ⌊log₂ n⌋ ((ALIGN-inc) certifies T1/T2 increments via (X.1a); T3
  degree-charged) and #recenterings ≤ s(n)·v_p(disc f) (full recentering
  burden: T4 AND the uncertified T1 recenterings). TREE-FINITE BRIDGE [added rev 2, finding 12]: T_can(f) is
  FINITELY BRANCHING — each node's child menu is finite (finitely many
  sides of a finite window polygon; each side's residual polynomial has
  ≤ ℓ ≤ n irreducible factors; §M-SPECIES' finite letter menus) — so
  König's lemma upgrades "every branch finite" to "T_can(f) finite".
  Hence a.e. f has a FINITE tree. [The plan's X.3 line "3.2 + 3.3 +
  Thm 2.1 restated in MOVES vocabulary" maps to route (a1) — but rev 3
  records that even (a1) consumes X.1b for its T4 leg; (a2) is the
  in-house fallback.]
(b) DETECTION AT A FINITE LEVEL [derived from accepted sources]. Every f
  whose tree is complete with all leaves (τ-irr)/(τ-hen) — the 𝒯^fin case
  — exits Undec(N) at its finite threshold thr(T): Thm 2.1 (each stratum a
  finite union of level-N₀ cylinders) joined over the tree's finitely many
  branches with TB-CAP's per-clause caps ([3t] §T.2: (τ-hen) N_V = 1
  PROVED; (τ-irr) per-realized-cell cap PROVED, perimeter-conditional).
(c) THE NS RESIDUAL [(ns-null) tag, closed]. 𝒯^ns is COUNTABLE ((NS-c)'s
  symbolic indexing) and each fiber has mass 0 GIVEN (ns-null) — total
  contribution 0.
(d) MONOTONE ASSEMBLY. Decided sets grow with N (N-stability, Thm 2.1), so
  Undec(N) ↓ ⋂_N Undec(N) = {some branch never τ-halts} ∪ (𝒯^ns fibers):
  by (b), every 𝒯^fin-decided f exits at its threshold, and an f whose
  complete tree is undetected at EVERY level has an ns leaf (TB-CAP's
  clause trichotomy — detection fails at all N only on the (τ-ns) class).
  By (a) + (c) the intersection has mass 0; monotone convergence gives
  μ(Undec(N)) → 0, decided mass = 1, and (3e)-style regrouping (Tonelli,
  positive terms) yields the per-σ series identity. ∎
CONDITIONALITY SUMMARY (the CL-4 record line, rev 3): X.3 =
[((X1a-ALIGN) ∧ X.1b(T4)) ∨ ((ALIGN-inc) ∧ X.1b(full))] — X.1b's T4 leg
in EVERY route — + (ns-null, closed, tag displayed) + accepted
perimeter (3.2/3.3/Thm 2.1, TB-CAP, König, VP-SOUND — the (HEN-LIFT)/
(OM-SAT) soundness citations §T-ASSEMBLY explicitly RETAINS as
obligations; finding 13: the typemult-to-true-type identification in the
per-σ series inherits THEM, not a bare "VP"). QUANTITATIVE COROLLARY
(consumed by SQ.3 only, never needed by (TGT)): μ(Undec(N)) ≤ env(N) with
X.2's full tag set — exponential GIVEN (X.2)+X.1b+(ALIGN-inc)+(X2-TAILS)+
(X2-BRIDGE)+(X2-CAP), √N-form GIVEN (X2-HYP)+(X2-AFF)+(X2-CAP)+X.1b+
(ALIGN-inc)+(X2-TAILS)+(X2-BRIDGE).

### X.4 Honest perimeter (derived vs fenced, one line each)

DERIVED here, unconditional: the raw index table (pure (IND) arithmetic +
the (P1)-pinned convention + the endpoint rulings + the explicit T2
witness (s+1, u+1)); the T3 degree charge (≤ ⌊log₂ n⌋ per branch); the
two-step X.1b reduction DISPLAY (rev-2 form, additive T3 offset);
(X2-HYP)'s shape GIVEN (X2-AFF) (the d_total+1 counting); the König
tree-finite bridge; X.3(b), X.3(d)'s assembly logic; (3b)/(3c) restated.
OPEN KERNELS owned here: (X1a-ALIGN) — sub-clauses (ALIGN-inc)/(ALIGN-rec);
WEIGHT-CHARGE + its s(n) (burden: the FULL recentering population; the
T4-restricted sub-burden is what X.3(a1) consumes — rev 3); X.2
PROGRESS — the linear coercivity, now explicitly OWNING (X2-AFF) (demoted
rev 2, finding 7: neither c₀(n) nor its existence is derived),
(X2-BRIDGE) (the Undec-to-branch inclusion, finding 8; rev 3: honest
level-relative form, uniform cap struck per TB-CAP), and (X2-CAP) (NEW
rev 3: cap(H) ≤ c_cap(n)·(1 + Σ h_r), the contradiction-free
cap-structure kernel replacing the struck uniform-cap duty).
NAMED HYPOTHESES owed elsewhere: (X2-TAILS) — [2b]/§H-DOMAINS' M4a tails,
discharged at [2b]'s acceptance; (ns-null) — closed at [3t], tag
displayed; VP-SOUND — (HEN-LIFT)/(OM-SAT), §T-ASSEMBLY's retained
citation obligations, inherited by X.3's series identity (finding 13).
CONSUMER MAP: X.1a → CL-15; X.1b → CL-2 (via X.2's constants, jointly
with (ALIGN-inc)) AND CL-4 (rev 3: X.3(a)'s T4 leg, both routes — the
rev-2 "ONLY" struck with the ALIGN-only route); X.2 → CL-3 (SQ.3/SQ.4, envelope gate
layers); X.3 → CL-4 ((TGT)'s density form, RS.4's total mass, E0's
a.e.-exit route). NOTHING here feeds RS.1, SQ.1, or RS.3 (the REV 4
narrowing) — any such citation is a drafting error.

### X.5 Sealed gate X-n3 (REBUILT rev 2, finding 16: quantities defined, numbers sealed; not yet run)

Boxes: exhaustive n = 3, the level-8 box at p = 2 (2²⁴) and the level-5
box at p = 3 (3¹⁵). Predictions SEALED before the census; a layer-(i)
violation is adjudicated against the (X1a-ALIGN) dictionary, never patched.
(i) THE PREFIX-CUMULATIVE INDEX SWEEP — the censused quantity DEFINED
  (finding 16: v_p(disc f) is ONE global valuation, so no per-node
  "increment" of it exists; the before/after object is a PREFIX
  inequality). Each continuing node ν carries its TABLE VALUE from (IND)
  in ν's own frame: T1 ↦ ½ℓ(ehℓ−e−h+1), T2 ↦ (e−1)(h−1)/2, T3/T4 ↦ 0.
  SEALED: for EVERY f in either box and EVERY prefix (ν₀ … ν_j) of every
  branch of T_can(f),
      v_p(disc f) ≥ 2·CUM(j),   CUM(j) := Σ_{i ≤ j} ind(S_{ν_i}),
  0 violations tolerated (this is the raw-table transport of (X.1a),
  independent of the (CD) discharge state — exactly what tests the ALIGN
  dictionary). T3/T4 nodes add 0 to CUM and predict NO required growth
  (observed disc jumps at them refute nothing).
(ii) SEALED NUMBERS (candidates refutable, Case-K — the census
  establishes nothing; each with its one-line derivation):
  - s(3) := 2 [CANDIDATE; shape: a T4 recentering climbs weight by ≥ 1
    (e_read = 1 integral ladder, D.10 strict climb), and L5fix-Invariant-2
    prices terminal weight against the different ≤ v_p(disc f) at ratio
    ≤ 2 — heuristic, NOT the kernel]. Test: max_f #{recentering nodes}/
    v_p(disc f) ≤ 2, both boxes (disc-zero f excluded; a recentering
    forces v_p(disc f) ≥ 1).
  - c₀(3) := 4 [CANDIDATE for (X2-AFF); D.11 per-move cost = "largest
    constrained height + 1" ≤ 3·h_r + 1 ≤ 4·h_r (frame scale ≤ n = 3,
    h_r ≥ 1)]. Sealed √N-fallback thresholds via (X2-HYP):
    d*(N) + 1 = h*(N) := ⌈√((N−1)/4)⌉. [Rev-3 note: (X2-HYP) now runs at
    c₀⁺ = c₀ + c_cap with (X2-CAP)'s c_cap(3) UNSEALED (no candidate
    claimed); the sealed number is retained as the c_cap = 0 face —
    an OBSERVATION target only, per layer (iii)'s standing toothlessness,
    never a refutation gate.]
  - c_d(3) = c_h(3) := 1/2, c_d′(3) = c_h′(3) := 1 [CANDIDATE PROGRESS
    target slopes — optimistic by design; (X2-HYP)'s hyperbola cannot
    derive them; refutation kills the candidates, not the kernel].
  - C_T(3) := 53 [DERIVED count: one union-bound term per M-n3 catalogue
    letter], c_T(3) := 1 [CANDIDATE: one more vanishing digit per extra
    height unit — the M4a cone heuristic, [2b]-owed]. Per-letter teeth:
    for every catalogue letter L of minimal admissible height h₀(L),
      μ{f : some branch node walks L with h_r ≥ h} ≤ p^{−(h − h₀(L))}.
  - (3b) LEGS [DERIVED — refutation would break Lemma 3.3's restatement]:
    μ{v₂(disc f) ≥ D} ≤ 2·2^{−⌈D/2⌉} = 1, 0.5, 0.25, 0.125 at
    D = 2, 4, 6, 8;  μ{v₃(disc f) ≥ D} ≤ 2·3^{−⌈(D−3)/2⌉} = 2/3, 2/9,
    2/27 at D = 5, 7, 9.
(iii) THE DECAY CURVE (falsifiability stated honestly). Measured
  μ(Undec(N)), N = 4…8, both primes, against the ASSEMBLED envelope at
  the sealed candidates (d* = h* = N/2 − 1):
    env*(N) = 2·p^{−⌈((N/2 − 2)/2.5 − 3·v_p(3))/2⌉} + 53·p^{−(N/2 − 1)}.
  Computed NOW: env*(N) > 1 at every N ≤ 8, both primes (deep-leg slope
  c_d/((s+1/2)(n−1)) = 1/10 per level [rev 8: the spurious factor 2 in the displayed constant struck — Fable cosmetic 2; the value 1/10 was already correct]; tall-leg constant 53) — the
  assembled comparison has NO teeth at census range and is displayed for
  shape only, NOT sold as falsifiable there. The falsifiable content at
  N ≤ 8 is layer (i), layer (ii)'s ratio + per-letter + (3b) tests, and:
  measured env(N) MONOTONE nonincreasing in N (derived, Thm 2.1
  N-stability). Exponential-target vs √N-fallback shape is an OBSERVATION
  target, not a refutation.
Relation to the plan's gate EXHAUST-n3 (§5): layer (i) = the plan's items
(i)+(i′); layer (iii) = item (iv); the plan's STALL census (item (ii)) =
layer (ii)'s ratio test = the STALL-probe; its (3b)-constant check (item
(iii), D = 2…8) = layer (ii)'s derived legs — one run, all layers, sealed
jointly.

STATUS: rev 4, 2026-07-27 — the three pass-3 criticals repaired IN PLACE
(records below; verdicts lean/notes/XEXH_PASS1_2026-07-27.md,
XEXH_PASS2_2026-07-27.md, XEXH_PASS3_2026-07-27.md): cap(H)/max h made
TOTAL via the DOMAIN CONVENTIONS with X.2/(X2-CAP) retyped to the
four-way pieces; the √N envelope line carries its full leg tags; the
X.3 cite map rebased to CL-4 (SQ.1 cite struck). Kernels OPEN: (X1a-ALIGN) —
(ALIGN-inc)/(ALIGN-rec); WEIGHT-CHARGE (FULL recentering burden; T4
sub-burden = X.3(a1)'s consumption) + s(n); PROGRESS — owning (X2-AFF),
(X2-BRIDGE) (level-relative form) and (X2-CAP) (NEW rev 3). Hypotheses
displayed: (X2-TAILS) [2b]-owed; VP-SOUND inherited by X.3. Gate X-n3
numbers as sealed at rev 2 (X.5(ii), with the rev-3 c_cap = 0-face note);
STALL-probe specced, not yet run. STATUS [rev 8]: ACCEPTED at the Codex bar (passes 8+9 on rev 7); the Fable dual pass CLEAN on the mathematics (its record below); the census layers of gate X-n3 not yet run.


THE BLUEPRINT UNDER FINAL CONFIRMATION (REV 4):
# MOVES §X-EXHAUST — Lean formalization blueprint (MovesX corpus)
# REV 4 (post-Fable-audit: the 4 rev-3 residue findings repaired; surgical)

*Rev 4, 2026-07-28. Repairs the 4 residue findings of the fresh-Fable audit
`lean/notes/MOVESX_AUDIT_FABLE_2026-07-28.md` (REJECT 2 crit / 2 gap; all 13 rev-3 repairs
verified GENUINE, all arithmetic and derivation chains independently re-derived clean).
ONLY the four flagged objects changed: X2BridgeP's witness, vdisc's signature, the
ℤ_[p]→ℚ_[p] hom name, fTail/Event's Fin arity. Cumulative findings→repairs table in §6.
Ground truth unchanged: DUAL-ACCEPTED §X-EXHAUST rev 8 (`MOVES_2026-07-24.md`
~10947–11555). Protocol-L. Next: parallel dual confirmation (Codex final + fresh Fable).*

**ORCHESTRATOR RULINGS APPLIED (verbatim scope):**
- **RULING 1 (findings 6/4/5/2, structural):** kernels are PROPS OVER THE CONCRETE
  CONTEXT. One shared corpus parameter — `XFamily n` bundling, for every prime p, the
  concrete monic box `MonicBox n p` (a DEFINED type over `ℤ_[p]`, with `vdisc`/`discZero`
  DEFINED via `Polynomial.discr`), the tree context `XCtx n p`, and the GMN interface.
  Every kernel (X2-*, WEIGHT-CHARGE, ALIGN) is a `Prop` parameterized by `(X : XFamily n)`
  and n-only constants: asserting the kernel = asserting the note's condition about THE
  objects; no kernel carries its own F/branch/frac data, so degenerate self-inhabitation
  is impossible by construction. The tall event is a DEFINED set (`TallEvent`), not a free
  field; `frac Set.univ = 1` is a context field; (X2-CAP)'s quantifier sits inside the
  ns-free fourth-piece family.
- **RULING 2 (finding 9):** the note's (3b) and X.3 displays are UNCONDITIONAL (given p
  prime, n ≥ 2) — so XF.7/XF.8/XF.10/XG.3 carry NO `ValExt` argument. The valuation-
  extension content lives only INSIDE the tail-derivation internals (XF.4/XF.6), discharged
  by D8's construction (XF.3) within XF.7's proof. If the construction genuinely cannot be
  completed, that is a STUCK report to the orchestrator, never a silent hypothesis rider.
  (XF.9 is DELETED — its role is absorbed; finding 8 thereby closed.)

Discipline: NO new axioms; open kernels are named Props consumed by name; accepted/owed
interface fields are each ONE note-cited input (never an in-section conclusion — findings
11/12); `sorry`-free ≠ non-vacuous; statement-fence applies.

---

## 0. What §X-EXHAUST is, and what is formalizable NOW

Four layers: **X.1a** the index table (T0–T5 by letter fields) → GMN index → v_p(disc),
pointwise, conditional exactly on (X1a-ALIGN); **X.1b** WEIGHT-CHARGE (OPEN; reduction
DISPLAY derived); **X.2** the dichotomy (OPEN; (X2-HYP) derived given (X2-AFF)∧(X2-CAP));
**X.3** the density form from X.1a + the elementary tail (3b), every tag displayed.

DERIVED in-corpus (rev 3 expands this list per findings 7/11/12): the full A/B layers
(unchanged; arithmetic independently confirmed); the X.1a chain and reduction; (X2-HYP);
the tail (3b) UNCONDITIONAL (Ruling 2); the envelope theorems (exponential AND √N
fallback) as ∃-statements GIVEN the tag set (finding 7); X.3(a) pointwise tree-finiteness,
X.3(b) finite-level detection, the (d)-trichotomy intersection inclusion, König, and the
per-σ series — all UNITS now, not fields (findings 10/11/12).
HYPOTHESIS layer (kernel Props over `XFamily n`, one unit each): (ALIGN-inc)/(ALIGN-rec),
WEIGHT-CHARGE (T4/full), (X2-AFF), (X2-CAP), (X2-BRIDGE), (X2-TAILS), (X2-PROGRESS),
(ns-null) tag, VP-SOUND — plus the accepted/owed CONTEXT FIELDS of `XCtx` (each one
note-cited local input: Thm 2.1 per-branch detection, TB-CAP caps, the Undec definition,
(NS-c) indexing, box-content laws), audited one-by-one in §4.

---

## 1. Design decisions

**D1 (unchanged) — nodes/histories.** `XNode n` with letter fields + coherence
(`t2inc`/`t3inc`/`t4rec`); `HistWF` (termLast, degProd) = ACCEPTED-source facts, planned
MovesSp discharge. **D2 (unchanged)** doubled index `ind2`. **D3 (unchanged)** `p1Region`
Finset, (P1) pin, EQUALITY tie. **D4 (unchanged)** `AlignState`/`dCert`/`DescX`.

**D5 (upgraded — the carrier is now CONCRETE).** `MonicBox n p :=
{f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n}`; `discZero := {f | f.1.discr = 0}`;
`vdisc f := (f.1.discr).valuation` (pinned `PadicInt.valuation : ℤ_[p] → ℕ`, already
ℕ-valued — Fable finding 2; junk 0 on discZero via `valuation_zero`; every statement using it
carries `f ∉ discZero`). Tail (3b) at finite level over `ZMod (p^D)` via
`PadicInt.toZModPow`; INTEGER exponent `tailExp : ℤ` (spot checks re-confirmed by the
auditor: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9)).

**D6 (retyped) — GMN interface over the concrete carrier.** `GMNIndex n p`: only `ind`
and `inStratum` remain fields; `vdisc`/`discZero` are DEFINED (D5), so (P2) is a field
about concrete valuations. Published (GMN); real instance owner MovesD/HC-2.

**D7 (rebuilt per Ruling 1 + findings 11/12) — ONE concrete context.** `XCtx n p` = the
per-f rooted-forest tree presentation (Branch f, hist, root/parent/children/reach), the
detection vocabulary (`DetectedAt`, `threshold`, `capDetectable`/`detCap`, `nsTrack`),
the (NS-c) fiber family, and the box content `frac` with `frac_univ = 1` (finding 5).
The rev-2 fields `detectInter`, `stratumLink`, `infBranch`, `tallFrac`, `link`, `hσ`,
`densityσ` are DELETED: `InfTree`, `TallEvent`, `DeepEvent`, `densityOf` are DEFINED sets/
quantities, and the X.3(b)/(d) content is DERIVED by units XG.2b–d (findings 4/11/12).
Remaining fields are each ONE note-cited input, listed and quoted in §4.

**D8 (unchanged route, Ruling-2 placement) — ValExt.** Constructed by XF.3
(`SplittingField` + `spectralNorm`); consumed EXPLICITLY only by the internals XF.4/XF.6;
discharged inside XF.7's proof. No public statement mentions it.

**D9 (NEW — p-freeness by parameter order, finding 3).** All kernel constants live in
`XConsts n` — a structure indexed by n ALONE, defined before any p enters scope. Kernel
Props take `(X : XFamily n) (K : XConsts n)` and quantify `∀ p [Fact p.Prime]` INSIDE.
A constant cannot depend on p because p is not in scope where the constant is bound.

---

## 2. Proposed Defs skeleton (`lean/LeanUrat/MovesX/Defs.lean`) — REV 3

```lean
import LeanUrat.Moves.Defs
-- import LeanUrat.MovesSp.Defs   -- Defs-sync round
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace LeanUrat.MovesX

/-! §A Nodes, rows, region, doubled index (UNCHANGED from rev 2; arithmetic confirmed) -/

structure XNode (n : ℕ) where
  e ell h s0 u0 : ℕ
  sel : Option (ℕ × ℕ)
  isIncrement : Bool
  epos : 1 ≤ e ; hpos : 1 ≤ h ; ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false

abbrev XHistory (n : ℕ) := List (XNode n)
def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

inductive Row | T1 | T2 | T3 | T4 | T5 deriving DecidableEq, Repr
def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3) else .T4

def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)
def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) := p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

structure AlignState where (inc rec : Bool)
def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing && match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.rec)
    | .T2 => st.inc
    | _   => false
def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length
def dUnc (st : AlignState) (H : XHistory n) : ℕ := dTotal H - dCert st H

inductive Pop | incT12 | recT1 | t3 | t4 deriving DecidableEq
def popOf? (ν : XNode n) : Option Pop :=
  if ¬ ν.continuing then none else some (match rowOf ν, ν.isIncrement with
    | .T1, true => .incT12 | .T2, _ => .incT12 | .T1, false => .recT1
    | .T3, _ => .t3 | .T4, _ => .t4 | .T5, _ => .t4)
def countPop (H : XHistory n) (c : Pop) : ℕ := (H.filter (popOf? · = some c)).length
def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0
def sumH (H : XHistory n) : ℕ := (H.map (·.h)).sum

structure HistWF (n : ℕ) (H : XHistory n) : Prop where
  termLast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true
  degProd  : ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod ≤ n

/-! §B The CONCRETE carrier (D5; Ruling 1) -/

def MonicBox (n p : ℕ) [Fact p.Prime] : Type :=
  { f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n }
def discZero (n p : ℕ) [Fact p.Prime] : Set (MonicBox n p) := { f | f.1.discr = 0 }
noncomputable def vdisc {n p : ℕ} [Fact p.Prime] (f : MonicBox n p) : ℕ :=
  (f.1.discr).valuation      -- ℕ-valued in pinned mathlib (PadicIntegers.lean:321);
                             -- junk value 0 on discZero (valuation_zero); guarded at every use

def polyOfCoeffs (R : Type) [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
def tailCount (p n D : ℕ) : ℕ :=
  Nat.card { a : Fin n → ZMod (p ^ D) // (polyOfCoeffs _ n a).discr = 0 }
def tailExp (p n D : ℕ) : ℤ := ⌈((D : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)⌉

/-- The a₀-free monic family tail and the level-D disc event (rev 4, Fable findings 3/4:
    hom name = pinned `PadicInt.Coe.ringHom` (PadicIntegers.lean:130); the Fin (n−1+1)/Fin n
    unification via an explicit OUTER `Fin.cast` on the index, legal from `hn : 1 ≤ n` —
    threaded from every consumer's `h2 : 2 ≤ n`. Derivative kills a₀: any slot-0 value
    gives the same fTail. -/
def fTail (n p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (aTail : Fin (n - 1) → ℤ_[p]) :
    Polynomial ℚ_[p] :=
  ((polyOfCoeffs ℤ_[p] n
      ((Fin.cons 0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map
    PadicInt.Coe.ringHom).derivative
def Event (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (a0 : ℤ_[p]) : Prop :=
  (p : ℤ_[p]) ^ D ∣ (polyOfCoeffs ℤ_[p] n
      ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).discr

structure ValExt (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) where
  L : Type ; [field : Field L] ; [alg : Algebra ℚ_[p] L]
  w : AbsoluteValue L ℝ
  ext : ∀ x : ℚ_[p], w (algebraMap ℚ_[p] L x) = ‖x‖
  splits : (g.map (algebraMap ℚ_[p] L)).Splits (RingHom.id L)
```

```lean
/-! §C The GMN interface (D6) and the ONE concrete context (D7; Ruling 1) -/

/-- Published GMN consumption surface over the CONCRETE carrier: (P2) + Thm 4.18(1).
    Real instance: OM engine; owner MovesD/HC-2 (wave 4/phase 3). -/
structure GMNIndex (n p : ℕ) [Fact p.Prime] where
  ind : MonicBox n p → ℕ
  inStratum : MonicBox n p → XHistory n → Prop
  p2 : ∀ f, f ∉ discZero n p → 2 * ind f ≤ vdisc f

/-- THE context: per-f canonical tree presentation + detection vocabulary + ns fibers +
    box content. Each field = ONE note-cited accepted/owed LOCAL input (§4 quotes each);
    the X.3(a)/(b)/(d) CONCLUSIONS are units XG.2b–d, never fields (findings 11/12). -/
structure XCtx (n p : ℕ) [Fact p.Prime] where
  Branch : MonicBox n p → Type
  hist : ∀ {f}, Branch f → XHistory n
  wf : ∀ {f} (b : Branch f), HistWF n (hist b)
  root : ∀ f, Branch f
  hist_root : ∀ f, hist (root f) = ([] : XHistory n)
  parent : ∀ {f}, Branch f → Option (Branch f)
  parent_hist : ∀ {f} (b b' : Branch f), parent b = some b' → ∃ ν, hist b = hist b' ++ [ν]
  parent_root : ∀ f, parent (root f) = none
  reach : ∀ {f} (b : Branch f), Relation.ReflTransGen (fun c d => parent c = some d) b (root f)
  children : ∀ {f}, Branch f → Finset (Branch f)          -- FINITE menus (§M-SPECIES)
  children_iff : ∀ {f} (b c : Branch f), c ∈ children b ↔ parent c = some b
  complete : ∀ {f}, Branch f → Prop        -- full branch of a complete τ-halted tree
  nsTrack : XNode n → Prop ; nsDec : DecidablePred nsTrack
  capDetectable : ∀ {f}, Branch f → Prop ; capDec : ∀ f, DecidablePred (@capDetectable f)
  detCap : ∀ {f}, Branch f → ℕ             -- TB-CAP cap of the branch's OWN cells
  threshold : ∀ {f}, Branch f → ℕ          -- Thm 2.1's per-stratum N₀
  DetectedAt : ∀ {f}, Branch f → ℕ → Prop  -- "this leaf branch is cap-detected at level N"
  detectBranch :                            -- Thm 2.1 + TB-CAP per-clause caps (X.3(b) INPUT)
    ∀ {f} (b : Branch f), IsLeafB b → (∀ ν ∈ hist b, ¬ nsTrack ν) →
      ∀ N, threshold b + capHB b ≤ N → DetectedAt b N
  Undec : ℕ → Set (MonicBox n p)
  undec_spec :                              -- X.0's DEFINITION of Undec, pinned
    ∀ f N, f ∉ Undec N ↔ (Finite (Branch f) ∧ ∀ b : Branch f, IsLeafB b → DetectedAt b N)
  undec_antitone : Antitone Undec           -- Thm 2.1 N-stability
  nsIdx : Type ; nsCountable : Countable nsIdx            -- (NS-c) symbolic indexing
  nsFiber : nsIdx → Set (MonicBox n p)
  nsCover :                                 -- ns-leaf f's covered by the fiber family
    ∀ f, (∃ b : Branch f, IsLeafB b ∧ ∃ ν ∈ hist b, nsTrack ν) → ∃ i, f ∈ nsFiber i
  frac : Set (MonicBox n p) → ℚ
  frac_univ : frac Set.univ = 1             -- NORMALIZED (finding 5)
  frac_nonneg : ∀ s, 0 ≤ frac s
  frac_mono : ∀ s t, s ⊆ t → frac s ≤ frac t
  frac_union_le : ∀ s t, frac (s ∪ t) ≤ frac s + frac t
  frac_iUnion_null : ∀ (s : ℕ → Set (MonicBox n p)), (∀ i, frac (s i) = 0) → frac (⋃ i, s i) = 0
  frac_inter_tendsto :                      -- monotone convergence for the box content
    Filter.Tendsto (fun N => frac (Undec N)) Filter.atTop (nhds (frac (⋂ N, Undec N)))
  vdisc_le_tail :                           -- the level-D cylinder fact (definitional at sync)
    ∀ D, frac { f | D ≤ vdisc f ∨ f ∈ discZero n p } ≤ (tailCount p n D : ℚ) / p ^ (n * D)

-- Defs-level abbreviations on XCtx (C : XCtx n p), {f} implicit:
--   IsLeafB b := C.children b = ∅                          -- "finite branch" = leaf-terminated
--   capHB b := if C.capDetectable b then C.detCap b else 0 -- cap conventions (TOTAL)
--   NsFreeB b := ∀ ν ∈ C.hist b, ¬ C.nsTrack ν             -- (τ-ns)-FREE, decidable
--   FourthPieceB b := (IsLeafB b ∨ ∃ b', C.complete b' ∧ isPrefixB b b') ∧ NsFreeB b
--       -- finding 1 REPAIRED: the 'finite branch' disjunct restored verbatim
--   isPrefixB b b' := Relation.ReflTransGen (fun c d => C.parent c = some d) b' b
--   InfTree : Set (MonicBox n p) := { f | ¬ Finite (C.Branch f) }        -- DEFINED (not a field)
--   TallEvent (hstar : ℕ) : Set (MonicBox n p) :=                        -- DEFINED (finding 4)
--       { f | ∃ b : C.Branch f, ∃ ν ∈ C.hist b, hstar ≤ ν.h }
--   DeepEvent (d : ℕ) : Set (MonicBox n p) := { f | ∃ b : C.Branch f, d ≤ dTotal (C.hist b) }

/-- The corpus's ONE shared parameter (Ruling 1): the concrete objects for every prime,
    with the tree-to-stratum tie. Real instance owner: MovesD/MovesT (wave-4 sync);
    ONE inhabitation obligation for the whole corpus, tracked in the campaign ledger. -/
structure XFamily (n : ℕ) where
  ctx : ∀ (p : ℕ) [Fact p.Prime], XCtx n p
  gmn : ∀ (p : ℕ) [Fact p.Prime], GMNIndex n p
  gmnLink :                                  -- §D4-R: f lies in the stratum of each of
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (ctx p).Branch f),  -- its own histories
      (gmn p).inStratum f ((ctx p).hist b)

/-- n-ONLY constants (D9, finding 3): defined BEFORE any p is in scope, so p-freeness
    is enforced by binder order, not convention. -/
structure XConsts (n : ℕ) where
  s : ℕ                                      -- WEIGHT-CHARGE's s(n)
  c0 ccap : ℚ ; c0nonneg : 0 ≤ c0 ; ccapnonneg : 0 ≤ ccap    -- (X2-AFF)/(X2-CAP)
  cd cd' ch ch' : ℚ ; cdpos : 0 < cd ; chpos : 0 < ch        -- (X.2) target slopes
  CT cT : ℝ ; CTpos : 0 < CT ; cTpos : 0 < cT                -- (X2-TAILS)
```

```lean
/-! §D The kernels as Props over the shared context (Ruling 1; findings 2/3/4/6).
    Each `def …P : Prop` quotes its display in its docstring; asserting it = asserting
    the note's condition about THE objects. Variables: (X : XFamily n) (K : XConsts n);
    ∀ p INSIDE each Prop (D9). Abbreviations from the XCtx comment block in scope. -/

def X1aAlignP (n : ℕ) (X : XFamily n) (st : AlignState) : Prop :=      -- (X1a-ALIGN)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → dCert st H ≤ (X.gmn p).ind f

def WeightChargeT4P (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=  -- X.1b, T4 burden
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → countPop H .t4 ≤ K.s * vdisc f

def WeightChargeFullP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop := -- X.1b, FULL burden
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ K.s * vdisc f

def X2AffP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=            -- (X2-AFF)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB b → ((X.ctx p).threshold b : ℚ) ≤ 1 + K.c0 * sumH ((X.ctx p).hist b)

def X2CapP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=            -- (X2-CAP)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB b → (X.ctx p).capDetectable b →                        -- finding 2: inside
      ((X.ctx p).detCap b : ℚ) ≤ K.ccap * (1 + sumH ((X.ctx p).hist b)) --   the ns-free family

def X2ProgressP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=       -- (X.2) target
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f) (N : ℕ),
    FourthPieceB b → N < (X.ctx p).threshold b + capHB b →
      K.cd * N - K.cd' ≤ dTotal ((X.ctx p).hist b) ∨
      K.ch * N - K.ch' ≤ maxH ((X.ctx p).hist b)

def X2TailsP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=          -- (X2-TAILS)
  ∀ (p : ℕ) [Fact p.Prime] (hstar : ℕ),                                  -- finding 4: THE event
    ((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℝ) ≤ K.CT * (p : ℝ) ^ (-(K.cT * hstar))

def X2BridgeP (n : ℕ) (X : XFamily n) : Prop :=                          -- (X2-BRIDGE), both clauses
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    ((X.ctx p).Undec N ⊆ discZero n p ∪ (⋃ i, (X.ctx p).nsFiber i) ∪ InfTree (X.ctx p) ∪
      { f | ∃ b : (X.ctx p).Branch f,
          IsLeafB b ∧ NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b }) ∧
    (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧
      ¬ ∃ b : (X.ctx p).Branch f,
          IsLeafB b ∧ NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b } = 0
  -- rev 4 (Fable finding 1): the note's "(τ-ns)-FREE FINITE BRANCH" witness — leaf-
  -- terminated (IsLeafB) in BOTH clauses. The witness then satisfies FourthPieceB via
  -- its FIRST disjunct (IsLeafB b) ∧ NsFreeB b, which is what X2ProgressP/XD.4 consume.

def NsNullP (n : ℕ) (X : XFamily n) : Prop :=                            -- (ns-null) TAG
  ∀ (p : ℕ) [Fact p.Prime] (i : (X.ctx p).nsIdx), (X.ctx p).frac ((X.ctx p).nsFiber i) = 0

/-- X.3(a)'s route disjunction, verbatim tags. -/
def X3aRouteP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  (X1aAlignP n X ⟨true, true⟩  ∧ WeightChargeT4P n X K) ∨
  (X1aAlignP n X ⟨true, false⟩ ∧ WeightChargeFullP n X K)

/-! §E Series objects (finding 12: densityOf DEFINED; finding 13: additivity defined) -/

/-- Per-(p) series presentation: the countable family of complete realizable finite
    trees with their fibers and letter-computed types. Fields = (NS-a)/§D4-R inputs;
    the density IDENTITY is the unit XG.4, never a field. Owner MovesD/MovesT. -/
structure SeriesData (n p : ℕ) [Fact p.Prime] (C : XCtx n p) where
  FinTree : Type ; treeCountable : Countable FinTree
  fiber : FinTree → Set (MonicBox n p)
  typemult : FinTree → SplitType n              -- the letter-computed type
  splitType : MonicBox n p → SplitType n        -- the TRUE splitting type of f
  fiber_disjoint : ∀ T T', T ≠ T' → Disjoint (fiber T) (fiber T')
  fiber_decided : ∀ T, Disjoint (fiber T) (⋂ N, C.Undec N)   -- fibers are decided sets
  decided_covered : ∀ f, f ∉ (⋂ N, C.Undec N) → f ∉ discZero n p → ∃ T, f ∈ fiber T

def densityOf (S : SeriesData n p C) (σ : SplitType n) : ℚ :=   -- DEFINED (finding 12)
  C.frac { f | S.splitType f = σ }

/-- VP-SOUND — (HEN-LIFT)/(OM-SAT): the typemult-to-true-type identification (note
    finding 13), the ONE place it is consumed. -/
def VPSoundP (S : SeriesData n p C) : Prop :=
  ∀ T (f : MonicBox n p), f ∈ S.fiber T → S.splitType f = S.typemult T

/-- The (3e)/Tonelli positive-term regrouping (finding 13 — now fully specified):
    countable additivity of the content on the disjoint fiber family. Owed (MovesD/T). -/
def CountableFiberAdditive (S : SeriesData n p C) : Prop :=
  ∀ (I : Set S.FinTree) (E : Set (MonicBox n p)),
    (∀ f ∈ E, ∃ T ∈ I, f ∈ S.fiber T) → (∀ T ∈ I, S.fiber T ⊆ E) →
    HasSum (fun T : I => C.frac (S.fiber T)) (C.frac E)

end LeanUrat.MovesX
```

(E-gate entry: this skeleton compiling, with the comment-block abbreviations
(`IsLeafB`, `capHB`, `NsFreeB`, `FourthPieceB`, `isPrefixB`, `InfTree`, `TallEvent`,
`DeepEvent`) made literal `def`s over `(C : XCtx n p)`, and `SplitType n` bound to the
campaign's target type at the Defs sync.)

---

## 3. The units (id · statement · moves_ref · deps · sketch · difficulty · hypothesis_fields)

Files `lean/LeanUrat/MovesX/<id>.lean`. Layers A/B are UNCHANGED from rev 2 (no rev-2
finding touched them; the two audited inequalities were independently confirmed) — full
statements restated for self-containedness, sketches abbreviated.

### Layer A — the index table (10 units, all statements frozen at rev 2)

**XA.1 rowTotal** — `theorem rowTotal (ν : XNode n) : (rowOf ν = .T5 ↔ ν.sel = none) ∧ (rowOf ν = .T1 ↔ ν.sel ≠ none ∧ 2 ≤ ν.ell) ∧ (rowOf ν = .T2 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h) ∧ (rowOf ν = .T3 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1) ∧ (rowOf ν = .T4 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ ν.e = 1)`. moves_ref: "Every continuing node … exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)". deps: Defs. EASY.
**XA.2 selForce** — `theorem selForce (ν) (g μ) (hs : ν.sel = some (g, μ)) (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell ∧ rowOf ν = .T1`. moves_ref: "μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side". deps: XA.1. EASY.
**XA.3 t1Witness** — `theorem t1Witness (ν) (h1 : rowOf ν = .T1) : (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card`. moves_ref: T1 witness "(s+e, u+(ℓ−1)h): ON S …" — the (P1) ON-OR-BELOW pin (§4 trap). deps: XA.1. EASY.
**XA.4 t1Arith** — `theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) : e + h ≤ e * h * ell + 1 ∧ h * (ell - 1) ≤ e * h * ell + 1 - e - h ∧ 1 ≤ ell * (e * h * ell + 1 - e - h)`. moves_ref: T1 column bracket "[e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]". deps: none. EASY.
**XA.5 t2Witness** — `theorem t2Witness (ν) (h2 : rowOf ν = .T2) : (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e - 1) * (ν.h - 1) ∧ 2 ∣ (ν.e - 1) * (ν.h - 1)`. moves_ref: T2 witness "(s+1, u+1) … gcd(e,h) = 1 excludes (2,2)". deps: XA.1. EASY-MEDIUM→MEDIUM band.
**XA.6 lat1** — `theorem lat1 (s0 u0 e h : ℕ) (he) (hh) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1)`. moves_ref: "strict-interior count (EH−E−H−d)/2 + 1, on-side non-vertex count d − 1" at ℓ = 1. sketch: center-reflection involution + no on-segment points (coprime). HARD.
**XA.7a latSlice** — `theorem latSlice (s0 u0 e h ell) (he) (hh) (hl : 1 ≤ ell) : (p1Region s0 u0 e h ell).card = ∑ k ∈ Finset.range ell, ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card + e * ((ell - 1 - k) * h))`. moves_ref: (IND)'s region as column blocks (slice above rectangle; stride vertices absorbed). HARD.
**XA.7b latGen** — `theorem latGen (s0 u0 e h ell) (he) (hh) (hl) (hcop) : 2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 - e - h)` + `example` anchors (ℓ = 1 ↦ XA.6; e = h = ℓ = 1 ↦ 0). moves_ref: "(IND) ind(S) = ½·ℓ·(ehℓ − e − h + 1)". deps: XA.6, XA.7a. MEDIUM.
**XA.8 t34Zero** — `theorem t34Zero (ν) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) : ν.region.card = 0 ∧ ind2 ν = 0`. moves_ref: T3/T4 zero rulings; docstring carries finding-1 semantics ("0" = no positive per-side bound — NEVER "actual ind_r = 0"). deps: XA.1, XA.6. EASY.
**XA.9 ind2Region** — `theorem ind2Region (ν) (hc : ν.continuing) : ind2 ν = 2 * ν.region.card ∧ ((rowOf ν = .T1 ∨ rowOf ν = .T2) → 1 ≤ ind2 ν)`. moves_ref: the table's ind(S) column, EQUALITY (doubled per D2). deps: XA.3–XA.8. MEDIUM.

### Layer B — (CD), populations, degree charge (4 units, frozen at rev 2)

**XB.1 dCertZero** — `theorem dCertZero (H : XHistory n) : dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H`. moves_ref: "At today's discharge state … d_cert ≡ 0". deps: Defs. EASY.
**XB.2 dCertMono** — `theorem dCertMono (H) : dCert ⟨true, false⟩ H = countPop H .incT12 ∧ dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1`. moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1 recenterings". deps: Defs. MEDIUM.
**XB.3 fourPop** — `theorem fourPop (H) : dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4`. moves_ref: "{T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}" (coherence fields make it typecheck). deps: XA.1. MEDIUM.
**XB.4 t3Charge** — `theorem t3Charge (H) (W : HistWF n H) (hn : 1 ≤ n) : countPop H .t3 ≤ Nat.log 2 n`. moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived…)"; exponential step proved in-unit, only Πe ≤ n rides (`HistWF.degProd`, MovesSp-discharged). deps: XA.1. MEDIUM.

### Layer C — the X.1a chain and reduction (retyped over `XFamily`; displays unchanged)

**XC.1 x1aChain** — with `DescX (X : XFamily n) (p) (st) (d) : Set (MonicBox n p) := {f | ∃ H, (X.gmn p).inStratum f H ∧ d ≤ dCert st H}` (Defs):
```lean
theorem x1aChain (X : XFamily n) (st : AlignState) (AL : X1aAlignP n X st)
    (p : ℕ) [Fact p.Prime] :
    (∀ (f : MonicBox n p) H, (X.gmn p).inStratum f H → f ∈ DescX X p st (dCert st H)) ∧
    (∀ (f : MonicBox n p) d, f ∈ DescX X p st d → f ∉ discZero n p → 2 * d ≤ vdisc f)
```
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) }"; first inclusion definitional, second via transport + (P2). deps: Defs. EASY-MEDIUM→MEDIUM band. hyp_fields: X1aAlignP (kernel), GMNIndex.p2 (published).
**XC.2 x1aTrivial** — the same two-inclusion statement at st = ⟨false, false⟩ WITHOUT the `AL` hypothesis. moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true". deps: XB.1. EASY. hyp: none (the honest unconditional instance).
**XC.3 x1bReduction** —
```lean
theorem x1bReduction (X : XFamily n) (K : XConsts n)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n
```
moves_ref: the two-step reduction display, cleared form (auditor-confirmed: "2I ≤ v, R ≤ sv, T3 ≤ ⌊log₂n⌋ give 2d_total ≤ (2s+1)v + 2⌊log₂n⌋"). deps: XB.2–4, XC.1. MEDIUM. hyp_fields: X1aAlignP(inc) ∧ WeightChargeFullP + HistWF.
**XC.4 x1bReductionT4** — same signature at st = ⟨true, true⟩ with `WeightChargeT4P`, conclusion `countPop H .t4 ≤ K.s * vdisc f ∧ 2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n`. moves_ref: X.3(a1)'s three bounds. deps: XB.2–4, XC.1. MEDIUM. hyp_fields: X1aAlignP(both) ∧ WeightChargeT4P + HistWF.

### Layer D — (τ-ns)-FREE, caps, (X2-HYP) (retyped over `XCtx`; displays unchanged)

**XD.1 nsFreeDec** — `instance (C : XCtx n p) (f) : DecidablePred (NsFreeB C (f := f))` + `theorem capTotal (C) (f) (b : C.Branch f) : (¬ C.capDetectable b → capHB C b = 0) ∧ (C.capDetectable b → capHB C b = C.detCap b)` + `theorem maxHNil : maxH ([] : XHistory n) = 0 ∧ sumH ([] : XHistory n) = 0`. moves_ref: DOMAIN CONVENTIONS (predicate exclusion; cap 0-convention; max h(∅) = 0). deps: Defs. EASY.
**XD.2 x2hypCount** — `theorem x2hypCount (H : XHistory n) (W : HistWF n H) : sumH H ≤ (dTotal H + 1) * maxH H` (unconditional; empty case both sides 0). moves_ref: "Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read history is carried by the +1". deps: Defs. MEDIUM. hyp: HistWF.
**XD.3 x2hypDichotomy** — `theorem x2hypDichotomy (M : ℚ) (d m : ℕ) (h : M < (d + 1) * m) : M < ((d : ℚ) + 1)^2 ∨ M < (m : ℚ)^2`. moves_ref: the √ dichotomy, squared form. deps: none. EASY.
**XD.4 x2hypAssembled** — (X2-HYP), over the context:
```lean
theorem x2hypAssembled (X : XFamily n) (K : XConsts n)
    (AF : X2AffP n X K) (CP : X2CapP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f)
    (hb : FourthPieceB b) (N : ℕ) (hN : N < (X.ctx p).threshold b + capHB b) :
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1)^2 ∨
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * (maxH ((X.ctx p).hist b) : ℚ)^2
```
moves_ref: "(X2-HYP) … DERIVED given (X2-AFF) ∧ (X2-CAP) … both prices in the ONE currency Σ h_r, combined constant c₀⁺ := c₀ + c_cap". deps: XD.1–XD.3. MEDIUM. hyp_fields: X2AffP, X2CapP by name.

### Layer E — kernel-Prop units + the DERIVED envelopes (findings 6/7 repaired)

**XE.1a–h** — one unit per kernel Prop: **XE.1a** `X1aAlignP` · **XE.1b** `WeightChargeT4P` · **XE.1c** `WeightChargeFullP` · **XE.1d** `X2AffP` · **XE.1e** `X2CapP` · **XE.1f** `X2BridgeP` · **XE.1g** `X2TailsP` · **XE.1h** `X2ProgressP`. Each unit: the `def` elaborates against Defs; docstring = its display verbatim + owner/status line (a/b/c math-side OPEN; d/e/h owned by PROGRESS; f owned by PROGRESS; g [2b]-owed, discharged at [2b]'s acceptance). NON-VACUITY BY CONSTRUCTION (Ruling 1): each is a Prop about the shared `X : XFamily n` — it carries no data of its own to degenerate; the ONE inhabitation obligation (the real `XFamily` instance, owner MovesD/MovesT) is ledger-tracked. deps: Defs. EASY ×8. hyp: they ARE the hypotheses.

**XE.2 envelopeExp** — the note's exponential envelope, as the DERIVED ∃-theorem (finding 7):
```lean
theorem envelopeExp (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (PR : X2ProgressP n X K) (BR : X2BridgeP n X) (AF : X2AffP n X K) (CP : X2CapP n X K)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (TL : X2TailsP n X K) (NS : NsNullP n X) (R : X3aRouteP n X K) :
    ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N))
```
moves_ref: "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF) … Given (X.2) with linear d*, h* AND both legs …: env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n), c₀, C_T, c_T, c_cap". deps: XC.3, XE.1*, XF.7, XG.2b–d (for the bridge's first-three-pieces mass, via X.3's tags). sketch: BR splits Undec(N) into the three null-tagged pieces (discZero via XF.7/vdisc_le_tail; ns via NS; InfTree via XG.2d ⊆ discZero) + the witness-branch piece. WITNESS FEED (rev 4, traced): BR's witness b carries `IsLeafB b ∧ NsFreeB b`, hence `FourthPieceB b` by the FIRST disjunct of FourthPieceB — exactly PR's (and XD.4's, in XE.3) hypothesis; PR on b gives deep-or-tall at d* = cd·N − cd', h* = ch·N − ch'; DEEP LEG: DeepEvent d* ⊆ {vdisc ≥ (2(d*−log)/(2s+1))} pointwise (XC.3 + gmnLink) → vdisc_le_tail + XF.7 give the (3b) bound with the note's displayed exponent; TALL LEG: TL. Constants assembled n-only (c₄ from cd, s, n − 1; the p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} absorption into c₃ — p-free). HARD. hyp_fields: the FULL tag set, verbatim the note's "CONSUMERS … inherit ALL tags above" line.
**XE.3 envelopeSqrt** — the √N fallback, same signature MINUS `PR` (X2ProgressP), conclusion `… ≤ c3' * (p : ℝ) ^ (-(c4' * Real.sqrt N))`.
moves_ref: "Given (X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) PLUS the same two leg tags …: env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N} — subexponential, enough for X.3's qualitative form, NOT for SQUEEZE's constants". deps: XD.4 in place of PR; otherwise as XE.2. HARD. hyp_fields: (X2-HYP)'s inputs + both leg tags — the rev-4 leg-tag line reproduced.

### Layer F — the ELEMENTARY DISCRIMINANT TAIL, UNCONDITIONAL (Ruling 2; findings 8/9/13)

Display: `(3b) μ{v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉} → 0; corollary
μ{disc f = 0} = 0`. `fTail`/`Event` now Defs (finding 13). XF.9 DELETED (Ruling 2).

**XF.1 discCylinder** — `theorem discCylinder (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) : ((p : ℤ_[p]) ^ D ∣ f.discr ↔ (polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))).discr = 0)`.
moves_ref: the (3b) event is level-D cylinder data. deps: Defs. sketch: `polyOfCoeffs … = f.map (toZModPow D)` for monic deg-n; monic-case `discr_map` helper (Mathlib gap flagged); `PadicInt.ker_toZModPow`. MEDIUM.
**XF.2 discResBridge** — `theorem discResBridge (p) [Fact p.Prime] (f : Polynomial ℤ_[p]) (hm : f.Monic) (h1 : 0 < f.natDegree) : ‖f.discr‖ = ‖f.resultant f.derivative‖`.
moves_ref: "Res(f, f′)" ↔ disc for monic f. deps: Defs. sketch: Mathlib `resultant_deriv`, lc = 1, ‖±x‖. MEDIUM band.
**XF.3 valExtOf** — `noncomputable def valExtOf (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) (hg : g ≠ 0) : ValExt p g`.
moves_ref: none (proof apparatus; §4 flag: never strengthens (3b) — and per Ruling 2 it appears in NO public statement). deps: Defs. sketch: `g.SplittingField` finite over complete ℚ_[p]; `spectralNorm` multiplicative there (Mathlib `SpectralNorm.lean` + Krasner layer); package as `AbsoluteValue`. HARD; STUCK ⟹ report (Ruling 2), no rider.
**XF.4 resRootSum** — `theorem resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) (V : ValExt p ((f.map PadicInt.Coe.ringHom).derivative)) : ‖f.resultant f.derivative‖ = ‖(n : ℚ_[p])‖ ^ n * ((((f.map PadicInt.Coe.ringHom).derivative.map (algebraMap ℚ_[p] V.L)).roots).map (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.Coe.ringHom)))).prod`.
moves_ref: "Res(f, f′) over the n−1 roots of f′" + the n·v_p(n) offset. deps: XF.3-independent (V explicit — INTERNAL unit). sketch: resultant map-commutation helper; root-product over V.L (`resultant_eq_prod_roots_sub` + eval-product lemmas); lc(f′) = n. HARD.
**XF.5 pigeonMax** — `theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) : ∃ v ∈ m, K ≤ (m.card : ℚ) * v`.
moves_ref: "some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)". deps: none. EASY. FLAG: no sign hypothesis (terms may be negative).
**XF.6 ballCover** — `theorem ballCover (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (aTail : Fin (n - 1) → ℤ_[p]) (V : ValExt p (fTail n p (by omega) aTail)) : ∃ idx : ℤ_[p] → Fin (n - 1), ∀ a0 b0, Event p n D (by omega) aTail a0 → Event p n D (by omega) aTail b0 → idx a0 = idx b0 → (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0)` (pairwise-congruence form; `Event`/`fTail` = Defs).
moves_ref: "the a₀-translation, union bound + Fubini". deps: XF.2, XF.4, XF.5 (INTERNAL unit, V explicit). sketch: f′ a₀-free; event point → root θᵢ with V.w(a₀ + c(θᵢ)) ≤ p^{−tailExp}; same-index points ultrametrically congruent; `.toNat` trivializes tailExp ≤ 0. MEDIUM-HARD.
**XF.7 tailCountBound** — (3b-LEAN), UNCONDITIONAL (Ruling 2 — no V argument):
```lean
theorem tailCountBound (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤ (n - 1 : ℚ) * (p : ℚ) ^ ((n * D : ℕ) : ℤ)
```
moves_ref: "(3b) μ{f monic deg n : v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}" (auditor-confirmed arithmetic: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9)). deps: XF.1, XF.6, XF.3. sketch: fiber over aTail ∈ (ZMod p^D)^{n−1} (XF.1); INSIDE the proof, `valExtOf (fTail n p (by omega) aTail) (fTail ≠ 0: lead coeff n ≠ 0 in char 0)` discharges XF.6's V; ≤ (n−1)·p^{D−tailExp.toNat} residues per fiber; trivial-face check at tailExp ≤ 0. MEDIUM-HARD (carries XF.3's stuck-risk — by ruling, a STUCK report, not a rider).
**XF.8 tailZero** — UNCONDITIONAL: `theorem tailZero (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) : Filter.Tendsto (fun D => (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D)) Filter.atTop (nhds 0)`.
moves_ref: "→ 0 as D → ∞". deps: XF.7. sketch: tailExp → ∞ linearly; geometric squeeze. MEDIUM.
**XF.10 discZeroNull** — UNCONDITIONAL over the context (Ruling 2):
```lean
theorem discZeroNull (n p : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (C : XCtx n p) :
    C.frac (discZero n p) = 0
```
moves_ref: "corollary μ{disc f = 0} = 0". deps: XF.8. sketch: discZero ⊆ {D ≤ vdisc ∨ discZero} for every D, so `C.vdisc_le_tail` + XF.8 + `frac_nonneg` squeeze. EASY-MEDIUM→MEDIUM band. hyp_fields: XCtx's `vdisc_le_tail` (definitional cylinder fact, §4).

### Layer G — X.3 DERIVED end-to-end (findings 10/11/12 repaired; 7 units)

**XG.1 branchLenBound** — cleared display over the family:
```lean
theorem branchLenBound (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n
```
moves_ref: X.3(a)'s four-population bound, both routes (auditor-confirmed arithmetic). deps: XC.3, XC.4. EASY (glue). hyp_fields: X3aRouteP + HistWF.

**XG.2 koenigFinite** — the note's König, VERBATIM premise (finding 10 — no uniform depth bound):
```lean
theorem koenigFinite (C : XCtx n p) (f : MonicBox n p)
    (hbranch : ¬ ∃ g : ℕ → C.Branch f, g 0 = C.root f ∧ ∀ k, C.parent (g (k + 1)) = some (g k)) :
    Finite (C.Branch f)
```
moves_ref: "T_can(f) is FINITELY BRANCHING — each node's child menu is finite … — so König's lemma upgrades 'every branch finite' to 'T_can(f) finite'" (finite branching is `children : Finset` in the interface; "every branch finite" = no infinite root-descending path). deps: Defs. sketch: contrapositive is König: if Branch f infinite, the finitely-branching rooted forest (children_iff, reach) has a node at every level with infinitely many descendants; choose successively (Mathlib route: `nonempty_sections_of_finite_inverse_system` on the level-k sets of infinite-descendant nodes, or a direct classical induction). HARD. hyp: none beyond the context.

**XG.2b detectJoin** — X.3(b), the finite-level detection, DERIVED (finding 11):
```lean
theorem detectJoin (C : XCtx n p) (f : MonicBox n p) (hfin : Finite (C.Branch f))
    (hleaves : ∀ b : C.Branch f, IsLeafB b → ∀ ν ∈ C.hist b, ¬ C.nsTrack ν) :
    ∃ N, f ∉ C.Undec N
```
moves_ref: "(b) DETECTION AT A FINITE LEVEL [derived from accepted sources]. Every f whose tree is complete with all leaves (τ-irr)/(τ-hen) … exits Undec(N) at its finite threshold thr(T): Thm 2.1 … joined over the tree's finitely many branches with TB-CAP's per-clause caps". deps: Defs. sketch: N := max over the finitely many leaf branches of (threshold b + capHB b) (Finite ⟹ the max exists); `C.detectBranch` detects each ns-free leaf at N; `C.undec_spec` (the Undec DEFINITION) closes. MEDIUM. hyp_fields: XCtx's detectBranch + undec_spec (accepted LOCAL inputs, §4).

**XG.2c interTrichotomy** — X.3(d)'s first half, DERIVED (finding 11):
```lean
theorem interTrichotomy (C : XCtx n p) :
    (⋂ N, C.Undec N) ⊆ InfTree C ∪ (⋃ i, C.nsFiber i)
```
moves_ref: "(d) … an f whose complete tree is undetected at EVERY level has an ns leaf (TB-CAP's clause trichotomy — detection fails at all N only on the (τ-ns) class)". deps: XG.2b. sketch: f ∉ InfTree ⟹ Finite (Branch f); if every leaf ns-free, XG.2b exits f from some Undec N — contradiction; so some leaf carries an ns node; `C.nsCover` places f in a fiber. MEDIUM. hyp_fields: nsCover ((NS-c) input).

**XG.2d treeFinite** — X.3(a) pointwise, DERIVED (replaces the deleted `stratumLink`/`infBranch` fields):
```lean
theorem treeFinite (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : MonicBox n p) (hd : f ∉ discZero n p) :
    Finite ((X.ctx p).Branch f)
```
moves_ref: "Off {disc f = 0} …, EITHER route gives every branch finite pointwise, by the four-population decomposition … Hence a.e. f has a FINITE tree". deps: XG.1, XG.2. sketch: an infinite path g (¬Finite via XG.2's contrapositive) gives hist (g k) of length k (parent_hist induction), each a stratum of f (`X.gmnLink`) with HistWF (`wf`); dTotal ≥ k − 1 (termLast) contradicts XG.1's bound at large k. MEDIUM-HARD→HARD band. hyp_fields: X3aRouteP; gmnLink/wf (context inputs).

**XG.3 x3Density** — the density limit, DERIVED (finding 11: no detectInter, no MassLink):
```lean
theorem x3Density (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (X.ctx p).frac ((X.ctx p).Undec N)) Filter.atTop (nhds 0)
```
moves_ref: "(X.3) … μ(Undec(N)) → 0 (N → ∞)" + CONDITIONALITY SUMMARY "X.3 = [routes] + (ns-null, closed, tag displayed) + accepted perimeter". deps: XG.2c, XG.2d, XF.10, XD.1. sketch: ⋂Undec ⊆ InfTree ∪ ⋃ns (XG.2c); InfTree ⊆ discZero (XG.2d contrapositive); frac(discZero) = 0 (XF.10); frac(⋃ns) = 0 (NS + nsCountable + frac_iUnion_null); frac_mono/union_le ⟹ frac(⋂) = 0; frac_inter_tendsto + undec_antitone close the limit. MEDIUM-HARD→HARD band. hyp_fields: X3aRouteP, NsNullP (tag) — NOTHING else beyond XCtx's audited inputs.

**XG.4 x3Series** — the per-σ series identity, DERIVED (finding 12: `hσ` deleted; `densityOf` DEFINED):
```lean
theorem x3Series (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X)
    (p : ℕ) [Fact p.Prime] (S : SeriesData n p (X.ctx p))
    (VP : VPSoundP S) (ADD : CountableFiberAdditive S) (σ : SplitType n) :
    HasSum (fun T : { T // S.typemult T = σ } => (X.ctx p).frac (S.fiber T)) (densityOf S σ)
```
moves_ref: "for each type σ the tree-fiber series sums the full density … [(ns-null) tag displayed]" + "(3e)-style regrouping (Tonelli, positive terms) yields the per-σ series identity"; VP-SOUND consumed exactly at the typemult identification (note finding 13). deps: XG.3, XF.10. sketch: E_σ := {f | S.splitType f = σ} ∖ (⋂Undec ∪ discZero); `decided_covered` + `fiber_disjoint` + VP.typeFaithful show E_σ is exactly the union of the σ-typemult fibers minus null sets; ADD gives HasSum to frac E_σ; frac(⋂Undec) = 0 (XG.3's chain) and frac(discZero) = 0 (XF.10) + union_le/mono give frac E_σ = densityOf S σ. HARD. hyp_fields: VPSoundP, CountableFiberAdditive (Tonelli, owed), SeriesData's three coverage fields (§4) + the XG.3 riders.

---

## 4. Audit table (trust surface; each interface field = ONE note-cited LOCAL input)

| object | note display it must match | class |
|---|---|---|
| `p1Region`'s `≤` | (P1)/Remark 4.14 on-or-below pin | DEF — sharpest trap |
| `rowOf` + `XNode` coherence | table rows; T2/T3 increments, T4 recenterings | DEF (MovesSp-discharged) |
| `ind2` + XA.9 equality | (IND) doubled; finding-1 semantics in docstrings | DEF+THM |
| `certified`/`dCert`/`DescX` | (CD); Desc_d keyed by d_cert | DEF |
| `HistWF` | §D4-R terminal-last; §B2-DEF "Π e_i ≤ n along a branch" | IF accepted (MovesSp sync) |
| `MonicBox`/`discZero`/`vdisc` | the monic box; v_p(disc f) — now CONCRETE (D5) | DEF (Mathlib) |
| `GMNIndex` (ind, inStratum, p2) | (P2) + Thm 4.18(1), D.12 dictionary | IF published (MovesD/HC-2) |
| `XFamily.gmnLink` | §D4-R: f lies in the stratum of each of its own histories | IF definitional (sync) |
| `XCtx` tree fields (root/parent/children/reach) | §D4-R T_can rooted presentation; §M-SPECIES finite menus | IF (MovesD; PrefFamily precedent) |
| `XCtx.detectBranch` | X.3(b)'s INPUTS: "Thm 2.1 (each stratum a finite union of level-N₀ cylinders)" + "TB-CAP's per-clause caps ((τ-hen) N_V = 1 PROVED; (τ-irr) per-realized-cell cap PROVED)" — per ONE leaf branch | IF accepted (MovesT sync) |
| `XCtx.undec_spec` | X.0's DEFINITION of Undec(N) verbatim ("does not certify a complete τ-halted tree with every leaf cap-detected") | IF definitional (sync) |
| `XCtx.undec_antitone`, `frac_inter_tendsto` | Thm 2.1 N-stability; monotone convergence of the box content | IF accepted/owed |
| `XCtx.nsIdx/nsCountable/nsFiber/nsCover` | "(NS-c)'s symbolic indexing"; ns-leaf f's covered | IF (owed, [3t]) |
| `XCtx.frac_*` laws + `frac_univ = 1` | the box probability content (finding 5 repaired) | IF (MovesD/T) |
| `XCtx.vdisc_le_tail` | the level-D cylinder fact ({v_p ≥ D} is level-D data) — definitional | IF definitional (sync) |
| kernel Props `*P` over `XFamily` | their displays verbatim; Ruling-1 non-vacuity; D9 p-freeness by binder order; NONNEG normalizations on c0/ccap WLOG-safe (flagged); rev 4: X2BridgeP's witness leaf-qualified (IsLeafB) in both clauses | HYP (open kernels) |
| `TallEvent`/`DeepEvent`/`InfTree`/`FourthPieceB` | the displayed events/sets (finding 4/1 repaired: defined, 'finite branch' disjunct restored) | DEF |
| `tailCount`/`tailExp`/`fTail`/`Event` | (3b) finite-level, INTEGER exponent (auditor-confirmed); rev 4: `Coe.ringHom` + outer `Fin.cast` from `hn : 1 ≤ n` | DEF |
| `ValExt`/`valExtOf` | proof apparatus only — appears in NO public statement (Ruling 2) | DEF+construction |
| `SeriesData` fields | (NS-a) 𝒯^fin quantification; canonical-tree fiber partition; decided coverage | IF (MovesD/T sync) |
| `VPSoundP` | VP-SOUND = (HEN-LIFT)/(OM-SAT) at the typemult identification (note finding 13) | HYP tag |
| `CountableFiberAdditive` | "(3e)-style regrouping (Tonelli, positive terms)" | IF owed (MovesD/T) |

INHABITATION: ONE obligation — the real `XFamily n` instance (+ per-p `SeriesData`),
owner MovesD/MovesT at wave-4 sync (HC-2 for `GMNIndex`); ledger-tracked. Kernels are
Props about it (Ruling 1), so no kernel has independent degenerate models.

## 5. Census and counts

**48 units.** EASY 19 (XA.1–4, XA.8; XB.1; XC.2; XD.1, XD.3; XE.1a–h; XF.5; XG.1) ·
MEDIUM 17 (XA.5, XA.7b, XA.9; XB.2–4; XC.1, XC.3, XC.4; XD.2, XD.4; XF.1, XF.2, XF.8,
XF.10; XG.2b, XG.2c) · HARD 12 (XA.6, XA.7a — lattice; XE.2, XE.3 — envelope assembly;
XF.3, XF.4, XF.6, XF.7 — tail analytics; XG.2, XG.2d, XG.3, XG.4 — X.3 chain).
Escalation-risk set = the 12 HARD ids; XF.3-class failures are STUCK reports (Ruling 2),
never hypothesis riders. X.5 gate layers = runtime, out of corpus. NOT formalized (OPEN
upstream): the X.1b/X.2 kernel derivations, STALL-probe, (X2-TAILS)'s derivation —
matching X.4's perimeter; the envelopes (exponential + √N) are now IN-corpus theorems
XE.2/XE.3 given the tag set (finding 7).

## 6. Findings→repairs (cumulative)

REV-2 round (25 findings of MOVESX_AUDIT_CODEX_2026-07-28.md): all repaired at rev 2 —
1 iffs · 2 split XA.7a/b · 3 equality · 4 coherence fields · 5 degree charge derived ·
6/7 two-inclusion chain · 8 unconditional count · 9 termLast · 10 prefix clause ·
11 FourthPiece domain · 12 ℝ constants · 13 ℚ slopes · 14 bridge fields · 15/16 kernel
units split · 17 c4pos · 18 toZModPow · 19 D8 route · 20 integer exponent · 21 split
XF.8/XF.10 · 22 cleared display · 23 rooted forest · 24 MassLink deleted · 25 series
theorem. (Rev-3 findings below supersede where they touch the same objects.)

REV-3 round (13 findings of MOVESX_AUDIT_CODEX_REV2_2026-07-28.md):

| # | class | object | repair (rev 3) |
|---|---|---|---|
| 1 | CRIT | FourthPiece | FIXED: `IsLeafB b ∨ ∃ b', complete b' ∧ isPrefixB b b'` — the 'finite branch' disjunct restored verbatim |
| 2 | CRIT | X2Cap | FIXED: `X2CapP` quantifies `FourthPieceB b → capDetectable b → …` — inside the ns-free family |
| 3 | CRIT | p-free constants | REDESIGNED (D9): all constants in `XConsts n`, bound before p; kernels `∀ p` INSIDE — p-freeness by binder order |
| 4 | CRIT | X2Tails event | REDESIGNED (Ruling 1): `TallEvent` a DEFINED set over the concrete tree context; `tallFrac` field deleted |
| 5 | CRIT | zero content | FIXED: `frac_univ : frac Set.univ = 1` field added |
| 6 | CRIT | kernel vacuity | REDESIGNED (Ruling 1): kernels are Props over the ONE shared `XFamily n`; no kernel carries its own data; single ledger-tracked inhabitation obligation |
| 7 | CRIT | XE.2 | FIXED: `envelopeExp` = ∃-theorem deriving the exponential envelope from the full tag set; NEW `XE.3 envelopeSqrt` = the p^{−c√N} fallback display |
| 8 | GAP | XF.9 | CLOSED BY DELETION (Ruling 2): XF.7/XF.8 are unconditional; no 'same as' statement remains |
| 9 | CRIT | ValExt riders | FIXED (Ruling 2): XF.7, XF.8, XF.10, XG.3 carry NO ValExt; discharge inside XF.7's proof via valExtOf; stuck ⟹ report |
| 10 | CRIT | König | FIXED: `koenigFinite` premise = no infinite root-descending path (+ finite menus in the interface) — the note's form, no uniform depth bound |
| 11 | CRIT | detectInter | REDESIGNED: field deleted; X.3(b)/(d) DERIVED by units XG.2b (detection join), XG.2c (trichotomy), XG.2d (pointwise tree-finiteness) from the LOCAL inputs detectBranch/undec_spec/nsCover |
| 12 | CRIT | hσ | REDESIGNED: deleted; `densityOf` DEFINED as frac of the true-type event; XG.4 derives the identity from decided coverage + fiber partition + VPSoundP + Tonelli |
| 13 | GAP | Defs deps | FIXED: `fTail`, `Event`, `CountableFiberAdditive` fully specified in the Defs skeleton |

REV-4 round (4 findings of MOVESX_AUDIT_FABLE_2026-07-28.md; all 13 rev-3 repairs
verified genuine there):

| # | class | object | repair (rev 4) |
|---|---|---|---|
| F1 | CRIT | X2BridgeP | FIXED: `IsLeafB b ∧ NsFreeB b` witness in BOTH clauses (the note's "(τ-ns)-FREE finite branch"); witness feed traced in XE.2's sketch — IsLeafB ∧ NsFreeB ⟹ FourthPieceB (first disjunct) ⟹ X2ProgressP/XD.4 apply |
| F2 | CRIT | vdisc | FIXED: `.toNat` dropped — pinned `PadicInt.valuation : ℤ_[p] → ℕ` (PadicIntegers.lean:321); junk-0 convention preserved via `valuation_zero` |
| F3 | GAP | PadicInt.coe | FIXED: renamed to pinned `PadicInt.Coe.ringHom` (PadicIntegers.lean:130) at fTail + XF.4 (grep-verified) |
| F4 | GAP | fTail/Event arity | FIXED: explicit OUTER `Fin.cast (by omega : n = n − 1 + 1)` on the index, from a new `hn : 1 ≤ n` argument threaded from every consumer's `h2 : 2 ≤ n` (option chosen and noted; no Fin (n−1+1) restatement ripple) |

codex
I’m checking the 48 statements against the displays, including the finite-branch conventions, public tail signatures, and both arithmetic spot checks. I’ll report only genuine statement-level offenses, not proof difficulty.
codex
1. No offending unit specs found. All 48 units match their cited displays with the required hypotheses and edge conventions.

Arithmetic checks:

- (3b) bound at \((n,p,D)=(2,2,0)\): \(4\).
- (3b) bound at \((2,2,4)\): \(1/4\).
- Branch bound: \(2d_{\mathrm{total}}\le(2s+1)v_{\mathrm{disc}}+2\lfloor\log_2 n\rfloor\).

Counts: **0 CRITICAL / 0 GAP**

ACCEPT
tokens used
44,056
1. No offending unit specs found. All 48 units match their cited displays with the required hypotheses and edge conventions.

Arithmetic checks:

- (3b) bound at \((n,p,D)=(2,2,0)\): \(4\).
- (3b) bound at \((2,2,4)\): \(1/4\).
- Branch bound: \(2d_{\mathrm{total}}\le(2s+1)v_{\mathrm{disc}}+2\lfloor\log_2 n\rfloor\).

Counts: **0 CRITICAL / 0 GAP**

ACCEPT
