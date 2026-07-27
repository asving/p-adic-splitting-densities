Date: 2026-07-27
Prompt = charge (lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md, below its '---' line) + frozen note §X-EXHAUST (lean/notes/MOVES_2026-07-24.md lines 10947-11556) + blueprint under audit (lean/notes/MOVESX_LEAN_BLUEPRINT_2026-07-28.md, full 465 lines).

OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa3c7-652a-7c71-be01-b46600a882ad
--------
user
---

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

THE FROZEN NOTE (ground truth — final rev, repairs in place):

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


THE BLUEPRINT UNDER AUDIT:

# MOVES §X-EXHAUST — Lean formalization blueprint (MovesX corpus, 2026-07-28)

*Blueprint deliverable for the campaign (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md §2 format).
Source of truth: the DUAL-ACCEPTED §X-EXHAUST rev 8 (`lean/notes/MOVES_2026-07-24.md`
lines ~10947–11555; acceptance record at "§X-EXHAUST: DUAL-ACCEPTED (2026-07-27)").
Consumes MovesSp per the campaign DAG; MovesSp is being blueprinted in parallel, so all
species names below are PLANNED names cited generically (`MovesSp.Letter`, …) — exact-name
sync at the Defs round. Written Protocol-L: verbatim names, statements re-bound at use.*

Discipline: NO new axioms except the already-allowed GMN index theorem (rides here as an
INTERFACE, §D6, so this corpus itself declares nothing). The campaign kernels of this note
— (X1a-ALIGN)=(ALIGN-inc)/(ALIGN-rec), WEIGHT-CHARGE, PROGRESS=(X2-AFF)/(X2-BRIDGE)/(X2-CAP),
(X2-TAILS), VP-SOUND, (ns-null) — are HYPOTHESIS STRUCTURES, never axioms, never silently
strengthened or dropped. `sorry`-free ≠ non-vacuous; statement-fence applies.

---

## 0. What §X-EXHAUST is, and what is formalizable NOW

The note is the exhaustion tie-in in four layers: **X.1a** a per-species INDEX TABLE
(rows T0–T5 keyed by the §M-SPECIES letter fields e, h, ℓ, selection) turning certified
classifier depth into GMN index, hence into v_p(disc f) — pointwise, measure-free,
conditional exactly on (X1a-ALIGN); **X.1b** the WEIGHT-CHARGE budget for uncertified
nodes (OPEN kernel; only its two-step REDUCTION display is derived); **X.2** the
quantitative dichotomy (kernel OPEN; only (X2-HYP)'s √N shape is derived given
(X2-AFF)∧(X2-CAP)); **X.3** the density form (TGT) consumes, assembled from X.1a + the
ELEMENTARY DISCRIMINANT TAIL (3b) with every conditionality tagged.

Formalizable-now split (the MovesC pattern):
- **DERIVED layer (provable outright):** the row classification + selection constraint;
  the (P1)-pin lattice counts and per-row increments; the T3 degree charge; the (CD)
  definition and its d_cert ≡ 0 consequence; the four-population partition; the X.1b
  reduction ARITHMETIC; (X2-HYP)'s counting + product dichotomy; the (τ-ns)-FREE
  predicate and cap TOTALITY conventions; the elementary tail (3b) (the one genuinely
  new mathematical content — §1 D5 for the Mathlib design); X.3's assembly LOGIC.
- **HYPOTHESIS layer (statements only, faithful):** the ALIGN sub-clauses, WEIGHT-CHARGE
  (full + T4-restricted), (X2-AFF), (X2-CAP), (X2-BRIDGE), (X2-TAILS), the X.2 linear
  target, VP-SOUND, (ns-null) tag, and the tree/measure interfaces owed by MovesD/MovesT
  (which MovesX may not import — campaign DAG: MovesX consumes MovesSp ONLY).

---

## 1. Design decisions

**D1 — Nodes = planned MovesSp letters + retained height pair.** §M-SPECIES strikes
heights from the letter; the X table needs (e, h, ℓ, selection). So
`XNode := { letter : MovesSp.Letter n, h : ℕ, hpos : 1 ≤ h, hcop : Nat.Coprime e h, … }`
(fields via planned MovesSp projections `MovesSp.Letter.eRead/ell/selection`; the raw
side left endpoint s₀′ and height base u ride as ℕ fields for the region model). A
history is `H : List (XNode n)`; `Continuing ν := ν.selection ≠ ⊥`. NO tree object is
built here — T_can, strata, Undec ride in interface structures (D7), keeping the campaign
DAG honest (MovesD/MovesT come later).

**D2 — DOUBLED index, division-free.** All table values carry a factor ½; we store
`ind2 : ℕ` (twice the index): T1 ↦ ℓ·(e·h·ℓ − e − h + 1), T2 ↦ (e−1)·(h−1), T3/T4 ↦ 0.
The chain (X.1a) becomes `v_p(disc f) ≥ Σ ind2` — literally the note's
`v_p(disc f) ≥ 2·CUM(j)` (X.5(i)). No ℚ anywhere in the table layer.

**D3 — The (P1) region as a Finset.** `p1Region (s u e h ℓ)` := the lattice points
on-or-below the side segment, strictly above the horizontal line L through the last
point, strictly beyond the vertical line L′ through the initial point (Remark 4.14
conventions, PINNED — the on-or-below clause is load-bearing: T1's witness sits ON S).
Defined as a `Finset (ℕ × ℕ)` by decidable inequalities on a bounding box. Per-row
lemmas are `Finset.card` facts; the (IND) identity is `2 · card = ℓ(ehℓ−e−h+1)` (§3 LAT
units). Witness-membership lemmas are `decide`-shaped memberships plus arithmetic.

**D4 — (CD) as a discharge-state-indexed count.** `AlignState := {inc : Bool, rec : Bool}`
(the two separately-dischargeable sub-clauses). `dCert st H` counts continuing T1/T2
nodes whose sub-clause flag per st is set ((ALIGN-inc) for increments+T2, (ALIGN-rec)
additionally for T1 recenterings). `dCert ⟨false,false⟩ H = 0` is a THEOREM (today's
honest state); `dUnc := dTotal − dCert`. No `d_gen^sem` is ever defined (note's fence).

**D5 — Mathlib discriminant decision (THE design decision).** Mathlib HAS
`Polynomial.resultant` (Sylvester det, `RingTheory/Polynomial/Resultant/Basic.lean`,
~186-lemma API incl. `resultant_eq_prod_roots_sub`, `resultant_eq_zero_iff`) and
`Polynomial.discr` (sign-adjusted `sylvesterDeriv` det) with `resultant_deriv`:
`Res(f, f′) = (−1)^{n(n−1)/2}·lc(f)·discr f`. DECISION: the corpus discriminant is
**`Polynomial.discr` over ℤ_p (`PadicInt`), compared to `resultant f f.derivative`
via `resultant_deriv`** (monic ⟹ lc = 1 ⟹ equal valuations; sign is a unit). The
tail (3b) is stated at FINITE LEVEL, division-free: counting `a : Fin n → ZMod (p^D)`
with `discr (polyOf a) = 0` in `ZMod (p^D)` — legal because discr is a ℤ-polynomial in
the coefficients, so the event `v_p(disc f) ≥ D` is a level-D cylinder (the map-
commutation unit XF.1). The analytic core (roots of f′) lives over a splitting field L
of f′ with an absolute value extending |·|_p — packaged as ONE interface `ValExt`
(PROV/IF: Mathlib's `spectralNorm` + `Krasner.lean` machinery is the discharge route;
if the fleet finds it heavy the interface rides, flagged). NO p-adic Haar measure is
used anywhere: all masses are `Nat.card` box fractions (MovesC M4 pattern).

**D6 — The GMN index apparatus as an interface.** (P1)/(P2)/Thm 4.18(1)/Cor 4.19 are
published (GMN_citations.md); the ALLOWED-axiom route exists, but MovesX stays
axiom-clean by bundling exactly what X.1a consumes into `IndexApparatus` (§2): `ind`,
`vdisc`, the (P2) inequality `vdisc f ≥ 2·ind f`, and the per-order sum lower bound.
Declaring the actual GMN axiom (+ faithfulness entry + guardian audit) is HC-2's/a
later designer's call; the chain theorem here is conditional on the structure either way.

**D7 — Owed-elsewhere objects as interface structures.** Strata/T_can/Undec(N)/TB-CAP
caps/(τ-ns) tracks are MovesD/MovesT property. MovesX types against them through
`XTreeInterface` (finitely-branching menus, branch membership, per-node cell-data
`nsTrack` predicate with a Decidable instance, detection cells + caps) and
`XMassInterface` (level-N box fractions in ℚ, antitone Undec via N-stability, the
detection and ns-null fields). Every field is quoted against its note display in §4.

---

## 2. Proposed Defs skeleton (`lean/LeanUrat/MovesX/Defs.lean`)

```lean
import LeanUrat.Moves.Defs            -- Stage vocabulary (accepted)
-- import LeanUrat.MovesSp.Defs       -- at Defs-sync round: MovesSp.Letter etc.
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace LeanUrat.MovesX

/-! §A  Nodes and rows (X.0 + THE INDEX TABLE) -/

/-- A branch node: a planned `MovesSp.Letter` with the height pair the catalogue
    forgets restored, plus the raw frame coordinates the (P1) region needs.
    PLACEHOLDER FIELDS until the MovesSp Defs sync; keyed fields are final. -/
structure XNode (n : ℕ) where
  e   : ℕ           -- side stride e_read (lowest-terms slope denominator)
  h   : ℕ           -- slope height h_r (RETAINED here; not a letter field)
  ell : ℕ           -- normalized side length ℓ = w′/e
  sel : Option (ℕ × ℕ)   -- selection (g, μ) or ⊥  [MovesSp.Letter.selection]
  isIncrement : Bool     -- D.8 increment (true) vs D.10 recentering (false)
  s0  : ℕ           -- raw left endpoint of the side (region model)
  u0  : ℕ           -- raw height of the side's LAST point (region model)
  epos : 1 ≤ e
  hpos : 1 ≤ h
  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell

abbrev XHistory (n : ℕ) := List (XNode n)

def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

/-- The T1–T5 row classification (T0 is NOT a node — level-0 openings excluded
    upstream by the history type itself; (P3)(iii)). -/
inductive Row | T1 | T2 | T3 | T4 | T5 deriving DecidableEq, Repr

def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3)
  else .T4

/-! §B  The (P1) region and the doubled index table (D2/D3) -/

/-- Remark 4.14's counted set for the side from (s0, u0 + h·ell) to
    (s0 + e·ell, u0): on-or-below S, strictly above L (y > u0), strictly
    beyond L′ (x > s0).  On-or-below S ⟺ h·(x − s0) + e·(y − u0) ≤ e·h·ell. -/
def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)

def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) :=
  p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

/-- The DOUBLED table value (D2): T1 ↦ ℓ(ehℓ−e−h+1), T2 ↦ (e−1)(h−1), else 0. -/
def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

/-! §C  (CD) certified depth and the four populations (X.0 + X.3(a)) -/

/-- The two separately-dischargeable (X1a-ALIGN) sub-clauses. -/
structure AlignState where
  inc : Bool    -- (ALIGN-inc) discharged?
  rec : Bool    -- (ALIGN-rec) discharged?

def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing &&
    match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.rec)
    | .T2 => st.inc          -- T2 is increment-only (g = μ = 1, key ×e)
    | _   => false           -- T3/T4: permanently NOT-CERT; T5 not counted

def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length
def dUnc (st : AlignState) (H : XHistory n) : ℕ := dTotal H - dCert st H

/-- The four-population partition of continuing nodes (X.3(a)). -/
inductive Pop | incT12 | recT1 | t3 | t4 deriving DecidableEq
def popOf? (ν : XNode n) : Option Pop := … -- none on T5/non-continuing

def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0   -- max h(∅) = 0
```

```lean
/-! §D  (τ-ns)-FREE and the cap conventions (X.2 DOMAIN CONVENTIONS, rev 4/5) -/

/-- The tree-side data MovesX types against but does not build (D7).
    Every field is a note display; see §4 audit table. -/
structure XTreeInterface (n : ℕ) where
  Branch    : Type                          -- finite branches/prefixes of T_can^τ
  hist      : Branch → XHistory n           -- its read history
  nsTrack   : XNode n → Prop                -- per-node cell-data predicate (VP clauses)
  nsDec     : DecidablePred nsTrack
  capDetectable : Branch → Prop             -- ≥1 window read reaching a (τ-irr) cell
  capDec    : DecidablePred capDetectable
  detCap    : Branch → ℕ                    -- TB-CAP cap of H's OWN cells (τ-irr side)
  complete  : Branch → Prop                 -- finite branch of a complete τ-halted tree

variable {n : ℕ} (I : XTreeInterface n)

/-- (τ-ns)-FREE: no node of H lies on a (τ-ns) track — the membership
    predicate ITSELF excludes them (rev 5: unions do not route). -/
def NsFree (b : I.Branch) : Prop := ∀ ν ∈ I.hist b, ¬ I.nsTrack ν
instance : DecidablePred (NsFree I) := …   -- List.decidableBAll via nsDec

/-- The FOURTH-PIECE FAMILY predicate (X.2 rev 5). -/
def FourthPiece (b : I.Branch) : Prop := I.complete b ∧ NsFree I b

/-- cap(H), TOTAL by the DOMAIN CONVENTIONS: genuine cap on cap-detectable
    branches, 0 on hen/no-window branches. -/
def capH (b : I.Branch) : ℕ := if I.capDetectable b then I.detCap b else 0

/-! §E  The named kernel/hypothesis structures (statements ONLY; §X.4 perimeter) -/

structure IndexApparatus (n : ℕ) (p : ℕ) where      -- D6 (GMN (P2) + Thm 4.18(1))
  Poly    : Type                                     -- monic separable deg-n f over ℤ_p
  vdisc   : Poly → ℕ                                 -- v_p(disc f) (disc ≠ 0 side)
  ind     : Poly → ℕ
  p2      : ∀ f, 2 * ind f ≤ vdisc f                 -- (P2), reducible case included
  inStratum : Poly → XHistory n → Prop               -- f ∈ stratum(H)

structure X1aAlign (n p : ℕ) (A : IndexApparatus n p) (st : AlignState) : Prop … :=
  -- the ONE transported consequence X.1a consumes (assembly paragraph):
  (transport : ∀ f H, A.inStratum f H → dCert st H ≤ A.ind f)

structure WeightChargeT4 (n p : ℕ) (A : IndexApparatus n p) where   -- X.3(a1) burden
  s : ℕ                                              -- s(n), explicit
  bound : ∀ f H, A.inStratum f H → countPop H .t4 ≤ s * A.vdisc f

structure WeightChargeFull (n p : ℕ) (A : IndexApparatus n p) where -- X.1b kernel
  s : ℕ
  bound : ∀ f H, A.inStratum f H →
    countPop H .recT1 + countPop H .t4 ≤ s * A.vdisc f

structure X2Aff (n : ℕ) (I : XTreeInterface n) where       -- (X2-AFF), OPEN
  c0 : ℕ ; c0pos : 1 ≤ c0
  bound : ∀ b, threshold I b ≤ 1 + c0 * sumH I b            -- Σ over ALL reads

structure X2Cap (n : ℕ) (I : XTreeInterface n) where        -- (X2-CAP), OPEN
  ccap : ℕ
  bound : ∀ b, FourthPiece I b → capH I b ≤ ccap * (1 + sumH I b)

structure X2Bridge (n : ℕ) (I : XTreeInterface n) (M : XMassInterface n) : Prop …
  -- Undec(N) ⊆ {disc=0} ∪ (𝒯^ns fibers) ∪ {infinite branch} ∪
  --            {∃ (τ-ns)-FREE finite branch, threshold + cap > N}   (level-relative)

structure X2Tails (n p : ℕ) (M : XMassInterface n) where    -- [2b]-owed, hypothesis
  CT cT : ℕ ; cTpos : 1 ≤ cT
  bound : ∀ N hstar, M.tallFrac N hstar * (p : ℚ)^(cT * hstar) ≤ CT * 1

structure X2Progress (n : ℕ) (I : XTreeInterface n) where   -- the X.2 linear target
  cd cd' ch ch' : ℕ ; cdpos : 1 ≤ cd ; chpos : 1 ≤ ch
  dichotomy : ∀ b N, FourthPiece I b → N < threshold I b + capH I b →
    cd * N ≤ dTotal (I.hist b) + cd' ∨ ch * N ≤ maxH (I.hist b) + ch'

/-! §F  The discriminant model (D5) + the mass interface -/

def polyOfCoeffs (R) [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  X^n + ∑ i, C (a i) * X^(i : ℕ)                     -- the monic box polynomial

-- level-D tail event, division-free (D5):
def tailCount (p n D : ℕ) : ℕ :=
  Nat.card {a : Fin n → ZMod (p^D) // Polynomial.discr (polyOfCoeffs _ n a) = 0}

structure XMassInterface (n : ℕ) where                -- D7, MovesT/MovesD-owed
  undecFrac : ℕ → ℚ                                   -- μ(Undec(N)), box fraction
  undecAntitone : Antitone undecFrac                  -- Thm 2.1 N-stability
  nonneg : ∀ N, 0 ≤ undecFrac N
  deepFrac  : ℕ → ℕ → ℚ                               -- μ{d_total ≥ d}, per level
  tallFrac  : ℕ → ℕ → ℚ                               -- μ{max h ≥ h*}, per level
  nsNull : Prop                                        -- (ns-null) TAG (closed at [3t];
                                                       --  displayed per (NS-c) rule)
  detection : Prop                                     -- X.3(b): 𝒯^fin f exits at thr(T)
  vpSound : Prop                                       -- VP-SOUND (HEN-LIFT)/(OM-SAT)

end LeanUrat.MovesX
```

(`threshold I b`, `sumH I b` := Σ_{reads of b} h_r, `countPop` are Defs-level
abbreviations over `XTreeInterface`/`XHistory`; elaboration round makes the `…`
Prop-structures literal. The skeleton COMPILING with placeholder `Prop` fields is
the E-gate entry criterion.)

---

## 3. The units (id · statement · moves_ref · deps · sketch · difficulty · hypothesis_fields)

Files: `lean/LeanUrat/MovesX/<id>.lean`, each importing `MovesX.Defs` + deps.

### Layer A — the index table (X.1a's DERIVED core)

**XA.1 rowTotal** — `theorem rowTotal (ν : XNode n) : ν.continuing → (rowOf ν = .T1 ↔ 2 ≤ ν.ell) ∧ (rowOf ν = .T5 ↔ False) ∧ …` (the exactly-one-row trichotomy, stated as the three defining iffs).
moves_ref: "Every continuing node of every history falls in exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)". deps: Defs. sketch: `rowOf` is an if-chain; `unfold` + `omega`/`decide`. EASY. hyp_fields: none.

**XA.2 selForce** — `theorem selForce (ν : XNode n) (g μ) (hs : ν.sel = some (g,μ)) (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell` (hence rowOf = T1).
moves_ref: "the selection constraint μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side". deps: Defs. sketch: from `selBound`: μ·g ≤ ℓ with the other factor ≥ 1; `nlinarith`/`omega`. EASY. hyp: none.

**XA.3 t1Witness** — `theorem t1Witness (ν) (h1 : rowOf ν = .T1) : (ν.s0 + ν.e, ν.u0 + (ν.ell − 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card`.
moves_ref: T1 row, witness "(s+e, u+(ℓ−1)h): ON S one e-step from its initial point; strictly above L …; strictly beyond L′". deps: Defs. sketch: membership = three inequalities: x > s0 (e ≥ 1); y − u0 = (ℓ−1)h ≥ h ≥ 1 > 0 (ℓ ≥ 2); on S: h·e + e·(ℓ−1)h = ehℓ ✓ (ON-OR-BELOW pin — equality case included by design, D3). `Finset.card_pos` via nonempty. EASY. hyp: none. WATCH: this witness is exactly the (P1) on-or-below convention; a strictly-below region def would break HERE — the audit must check `p1Region`'s `≤`.

**XA.4 t1Arith** — `theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) : h * (ell − 1) ≤ e * h * ell + 1 − e − h ∧ 1 ≤ ell * (e * h * ell + 1 − e − h)` plus the ℕ-subtraction guard `e + h ≤ e * h * ell + 1`.
moves_ref: T1 ind column "½ℓ(ehℓ−e−h+1) ≥ ½ℓ·h(ℓ−1) ≥ 1 [e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]". deps: none. sketch: `nlinarith` on the bracket identity; the guard makes T1's `ind2` truncation-free. EASY. hyp: none.

**XA.5 t2Witness** — `theorem t2Witness (ν) (h2 : rowOf ν = .T2) : (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e − 1) * (ν.h − 1) ∧ 2 ∣ (ν.e − 1) * (ν.h − 1)`.
moves_ref: T2 "explicit witness (s+1, u+1) … strictly below S ⟺ (e−1)(h−1) > 1 — true since e, h ≥ 2 and gcd(e,h) = 1 excludes (2,2)"; value "(e−1)(h−1)/2 ≥ 1". deps: Defs. sketch: membership: h·1 + e·1 ≤ eh ⟺ (e−1)(h−1) ≥ 1; ≥ 2 and evenness: e,h ≥ 2 coprime ⟹ not both even ⟹ (e−1)(h−1) even; (2,2) killed by coprimality. `omega` + `Nat.Coprime` parity case split. EASY-MEDIUM. hyp: none.

**XA.6 lat1** (the coprime lattice count) — `theorem lat1 (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h 1).card = (e − 1) * (h − 1)`.
moves_ref: "(P1), Remark 4.14 … Pick-style split: strict-interior count (EH − E − H − d)/2 + 1, on-side non-vertex count d − 1" at ℓ = 1 (interior only; both endpoints excluded, no on-segment points by gcd). deps: Defs. sketch: the classical coprime-triangle count: pair (x,y) ↔ (e−x, h−y) is an involution on the open rectangle (1..e−1)×(1..h−1) swapping below-S and above-S; coprimality ⟹ no lattice point ON the open segment; so 2·#below = (e−1)(h−1). Finset bijection (`Finset.card_nbij`), no Mathlib Pick exists. HARD. hyp: none.

**XA.7 latGen** (the (IND) identity) — `theorem latGen (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 − e − h)`. The region's card is (IND)'s full count — strict-interior (EH−E−H−d)/2 + 1 PLUS the d−1 on-side non-vertex points (each ON S, hence IN the on-or-below region). Sanity anchors carried as `example`s: ℓ = 1 reduces to XA.6 ((e−1)(h−1), since ℓ(ehℓ+1−e−h) = eh+1−e−h); e = h = ℓ = 1 gives 0.
moves_ref: "(IND) ind(S) = ½(EH − E − H + d) = ½·ℓ·(ehℓ − e − h + 1)". deps: XA.6. sketch: slice the length-eℓ side into ℓ coprime segments (XA.6 each), add the ℓ−1 interior stride vertices ON S and the sub-rectangles between slices; assemble by `Finset` disjoint-union arithmetic. HARD (the corpus's hardest derived unit; split further at elaboration if > 40 lines: XA.7a slicing partition, XA.7b arithmetic). hyp: none.

**XA.8 t34Zero** — `theorem t34Zero (ν) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) : ν.region.card = 0 ∧ ind2 ν = 0`.
moves_ref: T3 "interior count (e−1)·0/2 = 0; endpoints excluded"; T4 "only the two endpoints are lattice points on S (gcd(e,h) = 1); both excluded". deps: XA.6 (or direct). sketch: ℓ = 1 and (h = 1 or e = 1) ⟹ (e−1)(h−1) = 0 ⟹ card = 0 by XA.6; `ind2` matches by `rfl`-cases. EASY given XA.6. hyp: none. NOTE (finding-1 semantics, carried in the docstring verbatim): "0" = NO positive per-side bound certified — NEVER "actual ind_r = 0".

**XA.9 ind2Region** — `theorem ind2Region (ν) (hc : ν.continuing) : ind2 ν ≤ 2 * ν.region.card ∧ (rowOf ν = .T1 ∨ rowOf ν = .T2 → 1 ≤ ind2 ν)`.
moves_ref: the table's ind(S) column as REGION counts (rows T1/T2 positive, T3/T4 zero). deps: XA.3–XA.8. sketch: per-row case split; T1 via XA.7 (drop the +(ℓ−1) slack) + XA.4; T2 via XA.6 + XA.5; T3/T4 via XA.8. MEDIUM. hyp: none.

### Layer B — (CD), populations, degree charge

**XB.1 dCertZero** — `theorem dCertZero (H : XHistory n) : dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H`.
moves_ref: "At today's discharge state (neither sub-clause displayed) d_cert ≡ 0"; d_unc = d_total − d_cert. deps: Defs. sketch: `certified ⟨false,false⟩ ν = false` by cases; filter-length monotone. EASY. hyp: none (this THEOREM is the honesty display: (X.1a) at zero discharge is trivially true).

**XB.2 dCertMono** — `theorem dCertMono (H) : dCert ⟨true, false⟩ H = countPop H .incT12 ∧ dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1`.
moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1 recenterings". deps: Defs. sketch: filter/count case analysis on `rowOf`+`isIncrement`. EASY. hyp: none.

**XB.3 fourPop** — `theorem fourPop (H) : dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4`.
moves_ref: "the four-population decomposition {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}". deps: Defs. sketch: `popOf?` is total on continuing nodes (XA.1 trichotomy + T2-is-increment from selection (1,1) + `isIncrement` coherence field); List count partition. EASY-MEDIUM. hyp: none. AUDIT FLAG: T2 nodes must land in `incT12` — the Defs must pin `rowOf ν = .T2 → ν.isIncrement` as an XNode coherence field (T2 is increment-only per the table; carried as `t2inc` field, MovesSp-owed at sync).

**XB.4 t3Charge** — `theorem t3Charge (H) (hdeg : degCharge H n) : countPop H .t3 ≤ Nat.log 2 n` where `degCharge H n : Prop := 2 ^ (countPop H .t3) ≤ n` is a Defs abbreviation delivered by the species side (each T3 multiplies key degree by e ≥ 2, degree ≤ n).
moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived; charged additively, never absorbed)". deps: Defs. sketch: `Nat.log` bridge: 2^k ≤ n → k ≤ Nat.log 2 n (`Nat.pow_le_iff_le_log`, n ≥ 1). EASY. hyp_fields: `degCharge` — the ∏e ≤ n ladder is MovesSp/MovesD-owed (planned cite `MovesSp.degProd_le`); until sync it is this unit's named hypothesis.

### Layer C — the X.1a chain and the X.1b reduction (conditional theorems)

**XC.1 x1aChain** — `theorem x1aChain (A : IndexApparatus n p) (st : AlignState) (AL : X1aAlign n p A st) : ∀ f H, A.inStratum f H → 2 * dCert st H ≤ A.vdisc f`.
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) } … conditional exactly on the sub-clauses certifying the counted nodes". deps: Defs. sketch: `AL.transport` gives dCert ≤ ind f; `A.p2` gives 2·ind ≤ vdisc; chain. EASY (glue by design: the whole GMN/ALIGN weight sits in the two structures). hyp_fields: `X1aAlign` (the (X1a-ALIGN) kernel — its `transport` field IS the note's assembly paragraph conclusion "ind(f) ≥ d_cert(H) for EACH branch"; the per-order/distinct-orders mechanism stays INSIDE the hypothesis, never re-derived here), `IndexApparatus` ((P2) + Thm 4.18(1), published — D6).

**XC.2 x1aTrivial** — `theorem x1aTrivial (A) : ∀ f H, A.inStratum f H → 2 * dCert ⟨false,false⟩ H ≤ A.vdisc f`.
moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true". deps: XB.1. sketch: rewrite by dCertZero; `Nat.zero_le`. EASY. hyp: none — the corpus's honest UNCONDITIONAL instance of (X.1a), the d_cert ≡ 0 display.

**XC.3 x1bReduction** — `theorem x1bReduction (A) (AL : X1aAlign n p A ⟨true,false⟩) (WC : WeightChargeFull n p A) (f H) (hf : A.inStratum f H) (hdeg : degCharge H n) : 2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n`.
moves_ref: "d_total ≤ [v_p(disc f)/2 + ⌊log₂ n⌋] + s(n)·v_p(disc f) ⟹ v_p(disc f) ≥ (d_total(H) − ⌊log₂ n⌋)/(s(n) + 1/2)" (the rev-2 two-step reduction, additive T3 offset). deps: XB.2, XB.3, XB.4, XC.1. sketch: fourPop splits dTotal; incT12 ≤ vdisc/2 via XC.1 at st=⟨true,false⟩ (doubled form avoids the /2); recT1 + t4 ≤ s·vdisc via WC; t3 ≤ log via XB.4; `omega`. MEDIUM. hyp_fields: X1aAlign(inc) AND WeightChargeFull — the note's finding 11 verbatim: "X.1b ALONE discharges nothing"; the division-free form `2·dTotal ≤ (2s+1)·v + 2·log` IS the display `v ≥ (dTotal − log)/(s + ½)` cleared of denominators (audit: check the algebra is the same inequality).

**XC.4 x1bReductionT4** — same statement with `WeightChargeT4` and conclusion restricted to the (a1)-route population count: `countPop H .t4 ≤ WC.s * A.vdisc f ∧ (st := ⟨true,true⟩ …) 2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n`.
moves_ref: X.3(a1) "#T1/T2 = d_cert ≤ v_p(disc f)/2 by (X.1a) …; #T3 ≤ ⌊log₂ n⌋ …; #T4 ≤ s(n)·v_p(disc f) by WEIGHT-CHARGE RESTRICTED to the T4 population". deps: XB.2–4, XC.1. sketch: as XC.3 with st = ⟨true,true⟩ covering recT1 inside dCert. MEDIUM. hyp_fields: X1aAlign(both) ∧ WeightChargeT4 — route (a1)'s exact tag.

### Layer D — the (τ-ns)-FREE predicate, cap conventions, (X2-HYP)

**XD.1 nsFreeDec** — `instance (I : XTreeInterface n) : DecidablePred (NsFree I)` + `theorem capTotal (I) (b) : (¬ I.capDetectable b → capH I b = 0) ∧ (I.capDetectable b → capH I b = I.detCap b)` + `theorem maxHNil : maxH ([] : XHistory n) = 0`.
moves_ref: "the membership predicate itself excludes them"; "cap(H) := 0 for every hen/no-window branch"; "max h(∅) := 0 … no empty max is ever taken". deps: Defs. sketch: `List.decidableBAll`; `if` splits; `rfl`. EASY. hyp: interface fields only.

**XD.2 x2hypCount** — `theorem x2hypCount (I) (b) : sumH I b ≤ (dTotal (I.hist b) + 1) * maxH (I.hist b) ∨ I.hist b = []` — with `sumH` counting ALL reads (continuing + ≤ 1 terminal).
moves_ref: "H's reads are its d_total continuing nodes PLUS at most one terminal read … Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read history is carried by the +1". deps: Defs. sketch: each h_r ≤ maxH; #reads ≤ dTotal + 1 needs the history WELL-FORMEDNESS field (at most one terminal, terminal last — an `XHistory` invariant `wf : atMostOneTerminal` added to Defs; audit flag). List induction + `Nat.sum_le_card_nsmul`-style. MEDIUM. hyp: the `wf` invariant (MovesSp/MovesD-owed: branches read terminals last).

**XD.3 x2hypDichotomy** — `theorem x2hypDichotomy (M d m : ℕ) (h : M < (d + 1) * m) : M < (d + 1)^2 ∨ M < m^2`.
moves_ref: "(d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹ d_total + 1 ≥ √(…) OR max h ≥ √(…) — square-root, NOT linear". deps: none. sketch: contrapositive: (d+1)² ≤ M ∧ m² ≤ M ⟹ ((d+1)·m)² ≤ M² ⟹ (d+1)·m ≤ M; `nlinarith`. EASY. (√-free integer form; audit: the note's √ display is the same statement squared.)

**XD.4 x2hypAssembled** — `theorem x2hypAssembled (I) (AF : X2Aff n I) (CP : X2Cap n I) (b) (hb : FourthPiece I b) (N) (hN : N < threshold I b + capH I b) : (N − 1 − CP.ccap) < (AF.c0 + CP.ccap) * (dTotal (I.hist b) + 1)^2 ∨ (N − 1 − CP.ccap) < (AF.c0 + CP.ccap) * maxH (I.hist b)^2` (ℕ-truncated subtraction; c₀⁺ := c0 + ccap kept multiplied through, division-free).
moves_ref: "(X2-HYP) The hyperbolic dichotomy (DERIVED given (X2-AFF) ∧ (X2-CAP) …): threshold(H) + cap(H) > N ⟹ Σ h_r > (N−1−c_cap)/c₀⁺ ⟹ (d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹ …". deps: XD.1–XD.3. sketch: AF.bound + CP.bound price both terms in Σ h_r; combine, then XD.2, then XD.3. MEDIUM. hyp_fields: X2Aff, X2Cap (both OPEN kernels, owned by PROGRESS — consumed by name, exactly the note's tag).

### Layer E — kernel statements only (the E-gate compiles them; NO proofs ever asked)

**XE.1 kernelDefs** — the Defs §E structures themselves elaborate (`X1aAlign`, `WeightChargeT4/Full`, `X2Aff`, `X2Cap`, `X2Bridge`, `X2Tails`, `X2Progress`) + one NONVACUITY smoke instance each over a toy 1-node interface (fields inhabited with trivial data — vacuity guard, MovesC discipline).
moves_ref: X.4's OPEN-KERNEL list verbatim (one docstring per structure quoting its display). deps: Defs. EASY (elaboration). hyp: these ARE the hypotheses.

**XE.2 envelopeStatement** — `def EnvBound (M : XMassInterface n) (p : ℕ) (K : EnvKernels) : Prop := ∀ N, M.undecFrac N * (p : ℚ)^(K.c4 * N) ≤ K.c3` (division-free ℚ form of env(N) ≤ c₃·p^{−c₄N}). STATEMENT-ONLY def + the tag-trace docstring (c₃, c₄ traced to s(n), c₀, C_T, c_T, c_cap).
moves_ref: "env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n) (X.1b), c₀ ((X2-AFF)), C_T, c_T ((X2-TAILS)), c_cap ((X2-CAP))". deps: Defs. EASY (statement). hyp: EnvKernels bundles ALL X.2 tags — the CONDITIONALITY SUMMARY as a structure; no unit proves it (SQ-side consumption is MovesU's).

### Layer F — the ELEMENTARY DISCRIMINANT TAIL (3b), designed against Mathlib (D5)

Target display (rev 8): `(3b) μ{ f monic deg n : v_p(disc f) ≥ D } ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉} → 0`, corollary `μ{disc f = 0} = 0`. Lean form (finite-level, division-free): with `D' := ⌈(D − n·(padicValNat p n))/(n−1)⌉` (ℕ-ceiling; the bound is trivial when D ≤ n·v_p(n)):
> `(3b-LEAN)  tailCount p n D * p^(D') ≤ (n−1) * p^(n*D)`  — fraction form `tailCount/p^{nD} ≤ (n−1)·p^{−D'}`.

**XF.1 discCylinder** — `theorem discCylinder (p n D) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) : (∀ i, (f.coeff i).appr D = coeffs-of-a) → ((p:ℤ_[p])^D ∣ Polynomial.discr f ↔ Polynomial.discr (polyOfCoeffs (ZMod (p^D)) n a) = 0)`.
moves_ref: Lemma 3.3's proof-shape premise — the event {v_p(disc f) ≥ D} is coefficient-cylinder data (implicit in "union bound + Fubini" over the box). deps: Defs. sketch: `discr` is a det of coefficient matrix entries; ring-hom map `ℤ_[p] → ZMod (p^D)` commutes with det (`RingHom.map_det`) and with `derivative`/`sylvester` entries; needs a `discr_map` helper (natDegree preserved by monic: leading coeff 1 ≠ 0 in both). MEDIUM. hyp: none. Mathlib gap flagged: no `Polynomial.discr_map` lemma exists yet — the unit proves it for the monic case (natDegree-stable maps).

**XF.2 discResBridge** — `theorem discResBridge (f : Polynomial ℤ_[p]) (hm : f.Monic) (h1 : 1 ≤ f.natDegree) : ‖Polynomial.discr f‖ = ‖f.resultant f.derivative‖` (valuation form: equal v_p).
moves_ref: "(P2); reducible case via Def 4.11 + disc(PQ) = …" — here only the disc↔Res(f,f′) normalization for monic f. deps: Defs. sketch: Mathlib `Polynomial.resultant_deriv`: Res(f,f′) = (−1)^{n(n−1)/2}·lc·discr; lc = 1 (monic); ‖±x‖ = ‖x‖. EASY-MEDIUM (arg wrangling: `natDegree`-defaults of `resultant`). hyp: none.

**XF.3 valExt** — the interface + its discharge attempt: `structure ValExt (p) (g : Polynomial ℚ_[p]) where L : Type; [field : Field L]; [alg : Algebra ℚ_[p] L]; w : AbsoluteValue L ℝ; ext : ∀ x : ℚ_[p], w (algebraMap _ L x) = ‖x‖; splits : Polynomial.Splits (algebraMap ℚ_[p] L) g` — and `def valExtOf (g) : ValExt p g` via SplittingField + spectral norm.
moves_ref: Lemma 3.3 "Res(f, f′) over the n−1 roots of f′" — the roots need a valued home; no note display beyond the accepted proof-on-record. deps: Defs. sketch (discharge route): `g.SplittingField` is finite over ℚ_[p] (complete, nonarch); `spectralNorm ℚ_[p] L` is a power-multiplicative norm extending ‖·‖ and multiplicative on finite extensions of a complete rank-1 valued field (Mathlib `Analysis/Normed/Unbundled/SpectralNorm.lean` + `SpectralMulAlgNorm`); package as `AbsoluteValue`. HARD (Mathlib-archaeology unit; if the mult-instance is missing for ℚ_[p], the interface RIDES and the unit delivers only the structure + a flagged `sorry`-free statement holder). hyp: itself when undischarged.

**XF.4 resRootSum** — `theorem resRootSum (V : ValExt p (fPoly a).derivative) (a : Fin n → ℤ_[p]) (h2 : 2 ≤ n) : ‖resultant (fPoly a) (fPoly a).derivative‖ = ‖(n : ℚ_[p])‖^n * ∏ θ ∈ ((fPoly a).derivative.roots-in-L), V.w (aeval θ (fPoly a))` (multiset product over roots with multiplicity, n−1 of them).
moves_ref: "Res(f, f′) over the n−1 roots of f′" with the n·v_p(n) offset — X.3's (3b) exponent "(D − n·v_p(n))/(n−1)". deps: XF.3. sketch: map Res to L (`resultant_map`? exists for `natDegree`-stable maps — check; else prove); over L use Res(f,g) = (−1)^{deg f·deg g}·lc(g)^{deg f}·∏_{g(θ)=0} f(θ) — Mathlib has `resultant_eq_prod_roots_sub` + eval-product helpers (`map_sub_sprod_roots_eq_prod_map_eval`); lc(f′) = n, deg f = n gives ‖n‖^n. HARD. hyp: ValExt.

**XF.5 pigeonMax** — `theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) : ∃ v ∈ m, K ≤ (m.card : ℚ) * v` — max ≥ average, division-free, applied to the VALUATIONS vᵢ := −log_p(V.w(f(θᵢ))) of the n−1 root terms (ℚ-valued: w takes rational p-powers on algebraic elements): Σ vᵢ ≥ D − n·v_p(n) gives some (n−1)·vᵢ ≥ D − n·v_p(n).
moves_ref: the max-term step inside Lemma 3.3 ("some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)"). deps: none (pure `Finset.exists_le_of_sum_le` arithmetic). EASY. hyp: none. AUDIT FLAG: terms may be NEGATIVE (non-integral roots make w(f(θ)) > 1); max ≥ average needs no sign hypothesis — the statement must NOT assume vᵢ ≥ 0.

**XF.6 ballCover** (pairwise-congruence form — centers live in L, so no ℚ_[p]-center is ever claimed; the covering is consumed only through this congruence) — `theorem ballCover (p n D) (h2 : 2 ≤ n) (aTail : Fin (n−1) → ℤ_[p]) (V : ValExt p (fTail aTail).derivative) : ∃ idx : ℤ_[p] → Fin (n−1), ∀ a0 b0 : ℤ_[p], Event D a0 → Event D b0 → idx a0 = idx b0 → (p : ℤ_[p])^(D' ) ∣ (a0 − b0)` — where `Event D a0` := `(p:ℤ_[p])^D ∣ discr (fPoly (Fin.cons a0 aTail))`, `idx` assigns each event point a root index of f′, and D' is the XF.5 threshold.
moves_ref: "the a₀-translation, union bound + Fubini" (Lemma 3.3's proof on record): f(θ) = a₀ + c(θ) with c a₀-independent. deps: XF.2, XF.4, XF.5. sketch: f′ is a₀-independent (derivative kills the constant term — THE a₀-translation), so its root multiset in V.L is one fixed object; for an event point, XF.2+XF.4+XF.5 give a root θᵢ with w(a₀ + c(θᵢ)) ≤ p^{−D'} — set idx a0 := that i; two event points at the same i are p^{−D'}-close to the same −c(θᵢ), hence to each other (ultrametric), and w extends ‖·‖_p on ℚ_[p] (V.ext), giving the ℤ_[p]-divisibility. MEDIUM-HARD. hyp: ValExt.

**XF.7 tailCount** — `theorem tailCountBound (p n D) (hp : p.Prime) (h2 : 2 ≤ n) : tailCount p n D * p^(D') ≤ (n−1) * p^(n*D)` (D' as in (3b-LEAN); the degenerate D ≤ n·v_p(n) and n = 1 faces stated as trivial clauses).
moves_ref: "(3b) μ{…} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}" — THE display. deps: XF.1, XF.6. sketch: fiber the count over aTail ∈ (ZMod p^D)^{n−1} (lift each fiber to ℤ_p, XF.1); within a fiber, XF.6's pairwise congruence puts all event-a₀'s into ≤ n−1 classes mod p^{D'}, each of ≤ p^{D−D'} residues mod p^D; sum: ≤ (n−1)·p^{D−D'}·p^{(n−1)D}. `Nat.card` fiber arithmetic = the MovesC M4 pattern. MEDIUM-HARD. hyp: ValExt (via XF.6).

**XF.8 tailZero** — `theorem tailZero (p n) (hp) (h2 : 2 ≤ n) : Filter.Tendsto (fun D => (tailCount p n D : ℚ) / p^(n*D)) Filter.atTop (nhds 0)` + corollary `discZeroNull`: the disc-vanishing locus has fraction ≤ every (3b) bound (the μ{disc f = 0} = 0 reading at finite level).
moves_ref: "→ 0 as D → ∞; corollary μ{disc f = 0} = 0". deps: XF.7. sketch: D' → ∞ linearly in D; geometric decay; `Tendsto` squeeze over ℚ→ℝ. MEDIUM. hyp: ValExt (inherited).

### Layer G — X.3's qualitative assembly (the conditional theorem, tags displayed)

The route tag is a Defs-level disjunction type, so no route is ever silently preferred:
```lean
/-- X.3(a)'s hypothesis alternatives — the CONDITIONALITY SUMMARY verbatim:
    [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]. -/
inductive X3aRoute (n p : ℕ) (A : IndexApparatus n p)
  | a1 (al : X1aAlign n p A ⟨true, true⟩)  (wc : WeightChargeT4 n p A)
  | a2 (al : X1aAlign n p A ⟨true, false⟩) (wc : WeightChargeFull n p A)
```

**XG.1 branchLenBound** — `theorem branchLenBound (A) (R : X3aRoute n p A) (f H) (hf : A.inStratum f H) (hdeg : degCharge H n) : dTotal H ≤ (2 * R.s + 1) * A.vdisc f + Nat.log 2 n` (with `R.s` the route's s(n); statement identical on both routes — the PROOF differs per route).
moves_ref: X.3(a) "EITHER route gives every branch finite pointwise, by the four-population decomposition {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}: (a1) … OR (a2) …". deps: XB.3, XB.4, XC.3, XC.4. sketch: case on R; (a1): dCert⟨true,true⟩ covers incT12 + recT1 ≤ vdisc/2 (doubled), t4 ≤ s·vdisc, t3 ≤ log; (a2): XC.3 verbatim. `omega` assembly. MEDIUM. hyp_fields: X3aRoute (BOTH disjuncts carry X.1b's T4 leg — the note: "NO route avoids X.1b").

**XG.2 koenigFinite** — `theorem koenigFinite (I : XTreeInterface n) (hfb : FinBranching I) (hlen : ∀ b : I.Branch, dTotal (I.hist b) ≤ B) : TreeFinite I B` — with `FinBranching`/`TreeFinite` Defs-level interface predicates (finite child menus; finitely many branches, all of bounded length).
moves_ref: "TREE-FINITE BRIDGE [rev 2, finding 12]: T_can(f) is FINITELY BRANCHING — … §M-SPECIES' finite letter menus — so König's lemma upgrades 'every branch finite' to 'T_can(f) finite'". deps: Defs. sketch: bounded-depth + finitely-branching ⟹ finite by induction on B (the bounded form avoids full König: XG.1 gives a UNIFORM per-f bound, so no infinite-path compactness is needed — König cited by the note, but the formal route is the bounded one; audit: this is a WEAKER premise-use, not a statement change). deps on MovesSp finite-menu cite (planned `MovesSp.menuFinite`). MEDIUM. hyp: interface + finite menus.

**XG.3 x3Density** — the capstone statement:
```lean
theorem x3Density (n p) (A : IndexApparatus n p) (I : XTreeInterface n)
    (M : XMassInterface n)
    (R : X3aRoute n p A)                  -- X.3(a)'s displayed tag
    (hns : M.nsNull)                      -- (ns-null): CLOSED at [3t]; tag DISPLAYED
    (hdet : M.detection)                  -- X.3(b): Thm 2.1 + TB-CAP (MovesT-owed)
    (hvp : M.vpSound)                     -- VP-SOUND: (HEN-LIFT)/(OM-SAT), inherited
    (hlink : MassLink A I M)              -- the (a)+(c) ⟹ intersection-null glue field
    : Filter.Tendsto M.undecFrac Filter.atTop (nhds 0)
```
moves_ref: "Statement (X.3) … the undecided complement has mass 0; equivalently μ(Undec(N)) → 0 (N → ∞)" + the CONDITIONALITY SUMMARY line (rev 3). deps: XG.1, XG.2, XD.1. sketch: `M.undecAntitone` + `M.nonneg` give convergence to the inf; `MassLink` (the interface field carrying "the intersection has mass 0" from (a)+(c) pointwise finiteness + (3b)'s corollary + countable-ns — the MEASURE-side glue MovesX cannot build without MovesD fibers, stated as: inf undecFrac = 0 given the pointwise pieces) closes it. MEDIUM (the analysis is elementary once MassLink is typed; the WEIGHT sits in the hypothesis fields — by design, this is [5]'s qualitative clause, not a proof of the kernels). hyp_fields: X3aRoute, nsNull, detection, vpSound, MassLink — one-to-one with the note's tag list; the audit MUST check nothing extra and nothing missing.

**XG.4 x3Series** — statement-only: `def X3SeriesIdentity (M) (σ …) : Prop := HasSum (fun T : M.FinTree σ => M.fiberFrac T) (M.densityσ σ)` — the per-σ tree-fiber series display, typed over interface fields (`FinTree`, `fiberFrac`, `densityσ` — MovesD/MovesT-owed; the 𝒯^ns fibers' 0 dropped with the (ns-null) tag in the docstring).
moves_ref: "for each type σ the tree-fiber series sums the full density: Σ … = density_σ(p), with the 𝒯^ns fibers' total contribution dropped as 0 [(ns-null) tag displayed per (NS-c)]". deps: Defs. EASY (statement; the (3e)/Tonelli regrouping PROOF is RS-side, MovesS/MovesU territory — the note's ONE-cite-point discipline: X.3 is where [3]/(TGT)/E0 cite, and the X.4 consumer map "NOTHING here feeds RS.1, SQ.1, or RS.3" is reproduced in the file docstring). hyp: interface.

---

## 4. Audit table (trust surface for the Codex semantic gate)

| object | note display it must match | class |
|---|---|---|
| `p1Region`'s `≤` (on-or-below) | (P1)/Remark 4.14 pin + "T1 witness … ON S" + endpoint rulings | DEF — the corpus's sharpest trap; strictly-below would zero every e = 1 event |
| `rowOf` | table rows T1–T5 keyed (ℓ ≥ 2; ℓ = 1 by e, h; sel = ⊥) | DEF |
| `ind2` | (IND) doubled; T3/T4 ↦ 0 with finding-1 semantics in docstring | DEF |
| `certified`/`dCert` | (CD) verbatim incl. T2-inc-only; `dCertZero` = "d_cert ≡ 0 today" | DEF+THM |
| `X1aAlign.transport` | X.1a assembly paragraph's conclusion (ind ≥ d_cert) | HYP (kernel) |
| `WeightChargeT4/Full` | the boxed WEIGHT-CHARGE display, T4 vs full burden (rev 3) | HYP (kernel) |
| `X2Aff/X2Cap/X2Bridge/X2Tails/X2Progress` | (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/(X2-TAILS)/(X.2) displays | HYP (kernels) |
| `NsFree`/`FourthPiece`/`capH`/`maxH ∅ = 0` | X.2 DOMAIN CONVENTIONS (rev 4/5) | DEF |
| `tailCount` + (3b-LEAN) | Lemma 3.3's (3b), finite-level division-free transcription | DEF+THM — audit the ⌈·⌉ arithmetic and the n·v_p(n) offset |
| `ValExt` | (no note display — Lemma 3.3's proof apparatus) | IF (flag: NOT a note object; must never strengthen (3b)'s statement) |
| `IndexApparatus` | (P2) + Thm 4.18(1) via D.12 dictionary (GMN pins) | IF (published; axiom candidate at HC-2) |
| `XTreeInterface`/`XMassInterface`/`MassLink` | §D4-R/§T-ASSEMBLY objects X.3 types against | IF (MovesD/MovesT-owed; re-audited at wave 4 sync) |
| `X3aRoute` | "[(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]" | DEF (tag structure) |

## 5. Census and counts

**35 units.** EASY 16 (XA.1–4, XA.8, XB.1, XB.2, XB.4, XC.1, XC.2, XD.1, XD.3, XE.1, XE.2, XF.5, XG.4 — of which XE.1/XE.2/XG.4 are statement-only by design), MEDIUM 13 (XA.5, XA.9, XB.3, XC.3, XC.4, XD.2, XD.4, XF.1, XF.2, XF.8, XG.1, XG.2, XG.3), HARD 6 (XA.6, XA.7 — the two lattice-count units; XF.3, XF.4 — the ValExt/Mathlib-archaeology units; XF.6, XF.7 — the covering/Fubini pair, scored medium-hard). [Re-scored at E-gate; the escalation-risk set is exactly the six HARD ids; XA.7 pre-authorized to split (XA.7a/b).]
Sealed-gate X.5 layers (census runs) are NOT Lean units — runtime artifacts, out of corpus.
NOT formalized (statements exist upstream or nowhere): X.1b's kernel derivation (OPEN),
X.2's kernel (OPEN), the STALL-probe, (X2-TAILS)'s derivation ([2b]-owed), the envelope's
SQ-side consumption (MovesU). This matches X.4's DERIVED-vs-OPEN perimeter line by line.

codex
I’m auditing the statements against the displays themselves, including the finite-level tail arithmetic and every interface/hypothesis bundle. I’ll report only offending units, then exact counts and the required verdict.
codex
1. **GAP — XA.1 `rowTotal`.**  
   Offending spec:  
   > `theorem rowTotal ... : ... ∧ …`  
   > “the exactly-one-row trichotomy, stated as the three defining iffs”  
   The statement contains an ellipsis, so the claimed exhaustive and exclusive T1–T4 classification cannot be audited. In particular, the required ℓ = 1 edge cases are not stated.

2. **GAP — XA.7 `latGen`.**  
   Offending spec:  
   > “split further at elaboration if > 40 lines: XA.7a slicing partition, XA.7b arithmetic”  
   This is already a hidden multi-lemma unit: a lattice partition theorem and a separate arithmetic assembly. It violates the one-display/short-unit requirement as currently specified.

3. **CRITICAL — XA.9 `ind2Region`.**  
   Offending spec:  
   > `ind2 ν ≤ 2 * ν.region.card`  
   The note’s `(IND)` display gives equality, not merely a lower bound:
   `2·ind(S) = ℓ(ehℓ−e−h+1)`, and `latGen` identifies the same expression with `2·region.card`. The proposed statement is strictly weaker than the displayed table identity.

4. **GAP — XB.3 `fourPop`.**  
   Offending spec:  
   > `dTotal H = countPop H .incT12 + ...`  
   > “the Defs must pin `rowOf ν = .T2 → ν.isIncrement` as an XNode coherence field”  
   That field is absent from `XNode`. As written, degenerate T2 “recenterings” inhabit the type even though the note makes T2 increment-only. The partition cannot be justified from the proposed Defs.

5. **CRITICAL — XB.4 `t3Charge`.**  
   Offending spec:  
   > `(hdeg : degCharge H n)`  
   The note classifies `#T3 ≤ ⌊log₂ n⌋` as derived from the key-degree multiplication and degree bound. The blueprint weakens it to a theorem conditional on a new proposition defined to be essentially the needed exponential bound. This drops the derived species/degree argument into an unproved hypothesis.

6. **CRITICAL — XC.1 `x1aChain`.**  
   Offending spec:  
   > `2 * dCert st H ≤ A.vdisc f`  
   The quoted `(X.1a)` display is the two-inclusion chain
   `stratum(H) ⊆ Desc_{d_cert(H)} ⊆ {v_p(disc f) ≥ 2d_cert(H)}`.  
   The first inclusion and the `Desc` object are completely absent.

7. **CRITICAL — XC.2 `x1aTrivial`.**  
   Offending spec:  
   > `2 * dCert ⟨false,false⟩ H ≤ A.vdisc f`  
   Calling this the unconditional instance of `(X.1a)` still omits `stratum(H) ⊆ Desc₀`. The zero-discharge convention trivializes the numerical leg, not permission to delete half of the displayed chain.

8. **CRITICAL — XD.2 `x2hypCount`.**  
   Offending spec:  
   > `sumH I b ≤ ... ∨ I.hist b = []`  
   The note states the inequality unconditionally, including the empty history, where both sides are zero. Adding the disjunction makes the Lean statement weaker and loses precisely the `max h(∅)=0` edge case that the note repaired.

9. **GAP — XD.2 `x2hypCount`.**  
   Offending spec:  
   > “needs the history WELL-FORMEDNESS field ... added to Defs”  
   No such field occurs in `XHistory` or `XTreeInterface`. Arbitrary lists may contain multiple terminal reads, so `length ≤ dTotal+1` is unavailable.

10. **GAP — `FourthPiece`.**  
    Offending spec:  
    > `def FourthPiece ... := I.complete b ∧ NsFree I b`  
    The note quantifies over a “finite branch or prefix of a complete τ-halted tree.” The proposed `complete` field is described inconsistently as both branch completeness and membership in a complete tree, and no explicit prefix alternative or prefix relation is present.

11. **CRITICAL — `X2Aff`.**  
    Offending spec:  
    > `bound : ∀ b, threshold I b ≤ 1 + c0 * sumH I b`  
    `(X2-AFF)` belongs to X.2’s intrinsically `(τ-ns)`-free fourth-piece family. Quantifying over every abstract branch silently strengthens the open kernel, including ns branches and branches outside the target family.

12. **CRITICAL — `X2Tails`.**  
    Offending spec:  
    > `CT cT : ℕ ; cTpos : 1 ≤ cT`  
    > `bound : ∀ N hstar, M.tallFrac N hstar * p^(cT*hstar) ≤ CT`  
    The note allows arbitrary real positive `c_T(n)`; requiring an integer rate at least one is stronger and is not obtained by denominator clearing. Moreover, the note’s event is global—“some read of some branch”—whereas the unexplained level-dependent `tallFrac N hstar` can represent a strictly smaller event.

13. **CRITICAL — `X2Progress`.**  
    Offending spec:  
    > `cd cd' ch ch' : ℕ ; cdpos : 1 ≤ cd ; chpos : 1 ≤ ch`  
    The note requires arbitrary positive linear slopes and explicitly seals the candidate `c_d(3)=c_h(3)=1/2`. Natural coefficients at least one exclude that displayed edge case. Correct denominator clearing would also multiply the `dTotal`/`maxH` sides.

14. **GAP — `X2Bridge`.**  
    Offending spec:  
    > `structure X2Bridge ... : Prop …`  
    Only a comment paraphrases the decomposition. Neither the a.e. existential branch statement nor the four-piece inclusion and its quantifiers are supplied as fields. Its faithfulness and use cannot be audited.

15. **CRITICAL — XE.1 `kernelDefs`.**  
    Offending spec:  
    > “one NONVACUITY smoke instance each over a toy 1-node interface (fields inhabited with trivial data)”  
    Trivial toy instances do not prevent the actual hypothesis structures from being empty or degenerate. `IndexApparatus.Poly` and `XTreeInterface.Branch` need not be inhabited; `inStratum` may always be false; and `nsNull`, `detection`, and `vpSound` are unconstrained bare `Prop` fields. Thus the major conditional statements remain vacuously satisfiable.

16. **GAP — XE.1 `kernelDefs`.**  
    Offending spec:  
    > “the Defs §E structures themselves elaborate (`X1aAlign`, `WeightChargeT4/Full`, `X2Aff`, `X2Cap`, `X2Bridge`, `X2Tails`, `X2Progress`) + one ... instance each”  
    This combines at least seven distinct displayed kernels and multiple instance constructions into one unit, contrary to the required one-display decomposition.

17. **CRITICAL — XE.2 `envelopeStatement`.**  
    Offending spec:  
    > `EnvBound ... := ∀ N, ... p^(K.c4 * N) ≤ K.c3`  
    No displayed condition requires `c4 > 0`. With `c4 = 0`, this is merely a uniform bound and carries no decay, making the claimed exponential envelope degenerately satisfiable. The note explicitly requires positive decay.

18. **GAP — XF.1 `discCylinder`.**  
    Offending spec:  
    > `(∀ i, (f.coeff i).appr D = coeffs-of-a) → ...`  
    `coeffs-of-a` is not a term, the reduction map is not typed, and the coefficient range needed to identify `f` with `polyOfCoeffs` is not stated. This is not yet an auditable Lean statement.

19. **GAP — XF.3 `valExt`.**  
    Offending spec:  
    > `def valExtOf ...`  
    > “if ... missing ... the interface RIDES and the unit delivers only the structure + a ... statement holder”  
    These are materially different dependency designs: either every derivative receives a constructed extension, or later units require a quantified `ValExt` hypothesis. The blueprint leaves the choice unresolved and combines interface definition with a substantial construction theorem.

20. **CRITICAL — XF.7 `tailCountBound`.**  
    Offending spec:  
    > `D' := ⌈(D − n·padicValNat p n)/(n−1)⌉` as an “ℕ-ceiling,” with the numerator truncated when nonpositive  
    The note uses integer subtraction in the exponent. Natural truncation changes the bound for `D < n·v_p(n)` and makes it strictly stronger. For example, at `n=2, p=2, D=0`, the note’s right side is `4`, while the proposed truncated form gives `1`. The audit explicitly requires the `D=0` edge case to match exactly.

21. **GAP — XF.8 `tailZero`.**  
    Offending spec:  
    > “+ corollary `discZeroNull`: the disc-vanishing locus has fraction ≤ every (3b) bound”  
    No formal statement for `discZeroNull` is supplied, and a finite-level fraction limit is bundled with a separate null-locus/projective-limit claim. This needs explicit measure/interface semantics and separate units.

22. **CRITICAL — XG.1 `branchLenBound`.**  
    Offending spec:  
    > `dTotal H ≤ (2 * R.s + 1) * A.vdisc f + Nat.log 2 n`  
    The note’s cleared affine display is
    `2·dTotal ≤ (2s+1)·vdisc + 2·log₂ n`.  
    The proposed bound doubles the discriminant coefficient after division and is strictly weaker. It is not “statement identical on both routes” to the note’s arithmetic.

23. **GAP — XG.2 `koenigFinite`.**  
    Offending spec:  
    > `∀ b : I.Branch, dTotal (I.hist b) ≤ B → TreeFinite I B`  
    `XTreeInterface` contains no prefix closure, child relation, root, or assertion that all finite prefixes are represented by `Branch`. `FinBranching` and `TreeFinite` are also left unspecified. A bounded collection of selected finite branches does not imply finiteness of the underlying tree.

24. **CRITICAL — XG.3 `x3Density`.**  
    Offending spec:  
    > `(hlink : MassLink A I M)`  
    > “`MassLink` ... carrying ‘the intersection has mass 0’ ... closes it”  
    This smuggles the central conclusion of X.3(d) into an extra hypothesis not listed among the note’s open kernels or published hypotheses. Together with bare propositions `M.nsNull`, `M.detection`, and `M.vpSound`, it permits a degenerate interface to satisfy the theorem without expressing disc-zero nullity, countable ns fibers, detection, or the tree-to-measure link.

25. **CRITICAL — XG.4 `x3Series`.**  
    Offending spec:  
    > `def X3SeriesIdentity (M) (σ …) : Prop := HasSum ...`  
    > “statement-only”  
    X.3 asserts the series identity as part of its proved conditional conclusion. The blueprint merely defines a proposition and supplies no theorem establishing it. Its type also carries neither the displayed `(ns-null)` tag nor inherited VP-SOUND `(HEN-LIFT)/(OM-SAT)` hypotheses; a docstring is not a hypothesis field.

Counts: **14 CRITICAL / 11 GAP**

**REJECT (14 crit / 11 gap)**
tokens used
41,757
1. **GAP — XA.1 `rowTotal`.**  
   Offending spec:  
   > `theorem rowTotal ... : ... ∧ …`  
   > “the exactly-one-row trichotomy, stated as the three defining iffs”  
   The statement contains an ellipsis, so the claimed exhaustive and exclusive T1–T4 classification cannot be audited. In particular, the required ℓ = 1 edge cases are not stated.

2. **GAP — XA.7 `latGen`.**  
   Offending spec:  
   > “split further at elaboration if > 40 lines: XA.7a slicing partition, XA.7b arithmetic”  
   This is already a hidden multi-lemma unit: a lattice partition theorem and a separate arithmetic assembly. It violates the one-display/short-unit requirement as currently specified.

3. **CRITICAL — XA.9 `ind2Region`.**  
   Offending spec:  
   > `ind2 ν ≤ 2 * ν.region.card`  
   The note’s `(IND)` display gives equality, not merely a lower bound:
   `2·ind(S) = ℓ(ehℓ−e−h+1)`, and `latGen` identifies the same expression with `2·region.card`. The proposed statement is strictly weaker than the displayed table identity.

4. **GAP — XB.3 `fourPop`.**  
   Offending spec:  
   > `dTotal H = countPop H .incT12 + ...`  
   > “the Defs must pin `rowOf ν = .T2 → ν.isIncrement` as an XNode coherence field”  
   That field is absent from `XNode`. As written, degenerate T2 “recenterings” inhabit the type even though the note makes T2 increment-only. The partition cannot be justified from the proposed Defs.

5. **CRITICAL — XB.4 `t3Charge`.**  
   Offending spec:  
   > `(hdeg : degCharge H n)`  
   The note classifies `#T3 ≤ ⌊log₂ n⌋` as derived from the key-degree multiplication and degree bound. The blueprint weakens it to a theorem conditional on a new proposition defined to be essentially the needed exponential bound. This drops the derived species/degree argument into an unproved hypothesis.

6. **CRITICAL — XC.1 `x1aChain`.**  
   Offending spec:  
   > `2 * dCert st H ≤ A.vdisc f`  
   The quoted `(X.1a)` display is the two-inclusion chain
   `stratum(H) ⊆ Desc_{d_cert(H)} ⊆ {v_p(disc f) ≥ 2d_cert(H)}`.  
   The first inclusion and the `Desc` object are completely absent.

7. **CRITICAL — XC.2 `x1aTrivial`.**  
   Offending spec:  
   > `2 * dCert ⟨false,false⟩ H ≤ A.vdisc f`  
   Calling this the unconditional instance of `(X.1a)` still omits `stratum(H) ⊆ Desc₀`. The zero-discharge convention trivializes the numerical leg, not permission to delete half of the displayed chain.

8. **CRITICAL — XD.2 `x2hypCount`.**  
   Offending spec:  
   > `sumH I b ≤ ... ∨ I.hist b = []`  
   The note states the inequality unconditionally, including the empty history, where both sides are zero. Adding the disjunction makes the Lean statement weaker and loses precisely the `max h(∅)=0` edge case that the note repaired.

9. **GAP — XD.2 `x2hypCount`.**  
   Offending spec:  
   > “needs the history WELL-FORMEDNESS field ... added to Defs”  
   No such field occurs in `XHistory` or `XTreeInterface`. Arbitrary lists may contain multiple terminal reads, so `length ≤ dTotal+1` is unavailable.

10. **GAP — `FourthPiece`.**  
    Offending spec:  
    > `def FourthPiece ... := I.complete b ∧ NsFree I b`  
    The note quantifies over a “finite branch or prefix of a complete τ-halted tree.” The proposed `complete` field is described inconsistently as both branch completeness and membership in a complete tree, and no explicit prefix alternative or prefix relation is present.

11. **CRITICAL — `X2Aff`.**  
    Offending spec:  
    > `bound : ∀ b, threshold I b ≤ 1 + c0 * sumH I b`  
    `(X2-AFF)` belongs to X.2’s intrinsically `(τ-ns)`-free fourth-piece family. Quantifying over every abstract branch silently strengthens the open kernel, including ns branches and branches outside the target family.

12. **CRITICAL — `X2Tails`.**  
    Offending spec:  
    > `CT cT : ℕ ; cTpos : 1 ≤ cT`  
    > `bound : ∀ N hstar, M.tallFrac N hstar * p^(cT*hstar) ≤ CT`  
    The note allows arbitrary real positive `c_T(n)`; requiring an integer rate at least one is stronger and is not obtained by denominator clearing. Moreover, the note’s event is global—“some read of some branch”—whereas the unexplained level-dependent `tallFrac N hstar` can represent a strictly smaller event.

13. **CRITICAL — `X2Progress`.**  
    Offending spec:  
    > `cd cd' ch ch' : ℕ ; cdpos : 1 ≤ cd ; chpos : 1 ≤ ch`  
    The note requires arbitrary positive linear slopes and explicitly seals the candidate `c_d(3)=c_h(3)=1/2`. Natural coefficients at least one exclude that displayed edge case. Correct denominator clearing would also multiply the `dTotal`/`maxH` sides.

14. **GAP — `X2Bridge`.**  
    Offending spec:  
    > `structure X2Bridge ... : Prop …`  
    Only a comment paraphrases the decomposition. Neither the a.e. existential branch statement nor the four-piece inclusion and its quantifiers are supplied as fields. Its faithfulness and use cannot be audited.

15. **CRITICAL — XE.1 `kernelDefs`.**  
    Offending spec:  
    > “one NONVACUITY smoke instance each over a toy 1-node interface (fields inhabited with trivial data)”  
    Trivial toy instances do not prevent the actual hypothesis structures from being empty or degenerate. `IndexApparatus.Poly` and `XTreeInterface.Branch` need not be inhabited; `inStratum` may always be false; and `nsNull`, `detection`, and `vpSound` are unconstrained bare `Prop` fields. Thus the major conditional statements remain vacuously satisfiable.

16. **GAP — XE.1 `kernelDefs`.**  
    Offending spec:  
    > “the Defs §E structures themselves elaborate (`X1aAlign`, `WeightChargeT4/Full`, `X2Aff`, `X2Cap`, `X2Bridge`, `X2Tails`, `X2Progress`) + one ... instance each”  
    This combines at least seven distinct displayed kernels and multiple instance constructions into one unit, contrary to the required one-display decomposition.

17. **CRITICAL — XE.2 `envelopeStatement`.**  
    Offending spec:  
    > `EnvBound ... := ∀ N, ... p^(K.c4 * N) ≤ K.c3`  
    No displayed condition requires `c4 > 0`. With `c4 = 0`, this is merely a uniform bound and carries no decay, making the claimed exponential envelope degenerately satisfiable. The note explicitly requires positive decay.

18. **GAP — XF.1 `discCylinder`.**  
    Offending spec:  
    > `(∀ i, (f.coeff i).appr D = coeffs-of-a) → ...`  
    `coeffs-of-a` is not a term, the reduction map is not typed, and the coefficient range needed to identify `f` with `polyOfCoeffs` is not stated. This is not yet an auditable Lean statement.

19. **GAP — XF.3 `valExt`.**  
    Offending spec:  
    > `def valExtOf ...`  
    > “if ... missing ... the interface RIDES and the unit delivers only the structure + a ... statement holder”  
    These are materially different dependency designs: either every derivative receives a constructed extension, or later units require a quantified `ValExt` hypothesis. The blueprint leaves the choice unresolved and combines interface definition with a substantial construction theorem.

20. **CRITICAL — XF.7 `tailCountBound`.**  
    Offending spec:  
    > `D' := ⌈(D − n·padicValNat p n)/(n−1)⌉` as an “ℕ-ceiling,” with the numerator truncated when nonpositive  
    The note uses integer subtraction in the exponent. Natural truncation changes the bound for `D < n·v_p(n)` and makes it strictly stronger. For example, at `n=2, p=2, D=0`, the note’s right side is `4`, while the proposed truncated form gives `1`. The audit explicitly requires the `D=0` edge case to match exactly.

21. **GAP — XF.8 `tailZero`.**  
    Offending spec:  
    > “+ corollary `discZeroNull`: the disc-vanishing locus has fraction ≤ every (3b) bound”  
    No formal statement for `discZeroNull` is supplied, and a finite-level fraction limit is bundled with a separate null-locus/projective-limit claim. This needs explicit measure/interface semantics and separate units.

22. **CRITICAL — XG.1 `branchLenBound`.**  
    Offending spec:  
    > `dTotal H ≤ (2 * R.s + 1) * A.vdisc f + Nat.log 2 n`  
    The note’s cleared affine display is
    `2·dTotal ≤ (2s+1)·vdisc + 2·log₂ n`.  
    The proposed bound doubles the discriminant coefficient after division and is strictly weaker. It is not “statement identical on both routes” to the note’s arithmetic.

23. **GAP — XG.2 `koenigFinite`.**  
    Offending spec:  
    > `∀ b : I.Branch, dTotal (I.hist b) ≤ B → TreeFinite I B`  
    `XTreeInterface` contains no prefix closure, child relation, root, or assertion that all finite prefixes are represented by `Branch`. `FinBranching` and `TreeFinite` are also left unspecified. A bounded collection of selected finite branches does not imply finiteness of the underlying tree.

24. **CRITICAL — XG.3 `x3Density`.**  
    Offending spec:  
    > `(hlink : MassLink A I M)`  
    > “`MassLink` ... carrying ‘the intersection has mass 0’ ... closes it”  
    This smuggles the central conclusion of X.3(d) into an extra hypothesis not listed among the note’s open kernels or published hypotheses. Together with bare propositions `M.nsNull`, `M.detection`, and `M.vpSound`, it permits a degenerate interface to satisfy the theorem without expressing disc-zero nullity, countable ns fibers, detection, or the tree-to-measure link.

25. **CRITICAL — XG.4 `x3Series`.**  
    Offending spec:  
    > `def X3SeriesIdentity (M) (σ …) : Prop := HasSum ...`  
    > “statement-only”  
    X.3 asserts the series identity as part of its proved conditional conclusion. The blueprint merely defines a proposition and supplies no theorem establishing it. Its type also carries neither the displayed `(ns-null)` tag nor inherited VP-SOUND `(HEN-LIFT)/(OM-SAT)` hypotheses; a docstring is not a hypothesis field.

Counts: **14 CRITICAL / 11 GAP**

**REJECT (14 crit / 11 gap)**
