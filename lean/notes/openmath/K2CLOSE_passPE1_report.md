# K2CLOSE-PE1 — first hostile content pass on the assembled K2-CLOSE program

Verifier: fresh-context Fable (K2CLOSE-PE1), 2026-08-08 campaign (wallclock
2026-08-04).  Object: `K2CLOSE_2026-08-08.md` at 4ed354a (note of record,
final text 00a3658) + `K2CLOSE_LEGS23_2026-08-08.md` (11e1743/7bb28a6) +
`verification/openmath/k2close_enum.py` / `k2close_shape_table.md`
(13a2179/8579216) + `k2close_verdicts.py` / `k2close_verdict_table.md`
(816c75e).  Context consumed at its honest grades: SURVK2_PROOF at a8914944
(all commits verified to exist), LEDGERLAMBDA (attempt, 0 passes),
the committed engines.  Charge: quote-and-classify (CRITICAL / GAP / NOTE);
fix NOTHING.  Verifier's own probe: `verification/openmath/k2close_pe1_ext.py`
(NEW, this pass; fresh implementations, nothing imported from the two
runners except read-only committed artifacts) — ALL PROBES GREEN.

**Verdict, first: GAPS-ONLY — 0 critical, 4 gaps, 6 notes.**  The
mathematical spine is sound: K2-L11's φ-functional proof re-derived exact
and independently machine-confirmed (including the budget-free
quantification); K2-L9/K2-L10 re-derived (with one statement-scope gap in
the component note, already sharpened in the note of record); both runners
re-run and byte-reproduced (mod timing + one disclosed non-idempotency
artifact); the budget caps adjudicated (B4 the only declared cap, honestly
so); three verdicts re-derived by hand AND by an independent full-Bell
enumeration (GS-40's 53-state exhaustion decorrelated-confirmed); K2-THM-B's
proof and covers check out; PV-4's miss is honestly disclosed and the
degeneracy finding verified straight from the pinned instrument artifact.
The four gaps are: two residual-box description overclaims ((ii)'s
"no opposite-sign failure mode remains anywhere"; the unnamed non-dump-variant
glued strata), the LEGS23 K2-L9 statement over-breadth, and one stale
"(b) budget-killable" ledger line that K2-L10's reversal never reached.

## S1. Charge 1 — K2-L11 (ID-CLOSURE): re-derived EXACT; the quantification is budget-free

**The functional proof, re-derived from scratch.**  Coordinates
(x₀, x₁, ψ₀, ψ₁, ρ₁..ρ_r).  Cell monomial μ = e_{x_dt} + Σ_{k∈K} e_{ψk} +
e_{ρf} (K2-L4, junk-free, any glued group at g₀ = 2).  For w = Σ c_μ μ ∈ H:
each μ carries exactly one ρ-coordinate, so the ρ_f-coordinate of w is
s_f := Σ_{μ∈f} c_μ; w ρ-free ⟹ s_f = 0 ∀f.  Then deg(w) = Σ_μ c_μ =
Σ_f s_f = 0, and φ(w) = Σ_f φ|_f · s_f = 0 USING φ(μ) = M − dt = −ν̂_f
constant per fiber — which is exactly K2-L6, correctly cited; the lemma's
validity for arbitrary (beyond-budget) glued groups therefore rests on
K2-L4 + K2-L6, both any-budget lemmas of the SURVK2 spine.  Kernel: v ∈ Z⁴
with v_{x0}+v_{x1} = 0 and 2v_{ψ0}+v_{ψ1}−v_{x1} = 0 is exactly
(α, −α, β, −α−2β) = α·I₁ + β·I₃ with α = v_{x0}, β = v_{ψ0} — integral in
both directions, so the containment is saturated.  [Probe A: brute-force
box ±6 over Z⁴, kernel == ⟨I₁,I₃⟩ elementwise; I₂ = I₁ − I₃ = (1,−1,−1,1);
box (b)'s x₀ψ̄₀ = x₁ψ̄₁³ = I₁ + I₃ = (1,−1,1,−3) — all PASS.]

**The quantification question (the charge's sharp point).**  The proof
uses ONLY: (i) x-degree 1 per cell, (ii) one ρ-coordinate per cell,
(iii) φ fiber-constant (K2-L6).  None of these is budget-bounded — the
lemma covers beyond-B4 glued groups, so (K2-RES-B)(iii)'s "the identity
ALGEBRA is closed even where the shape list is not" is LEGITIMATE.  The
machine shadow is corroboration only, and NARROWER than one sentence
claims — see NOTE N1.  I hunted an identity outside the span two ways:
(a) the cross-fiber-cycle construction (force ρ₂−ρ₁ ≡ two different digit
vectors, difference = ψ₀−ψ₁ ∉ ⟨I₁,I₃⟩) — BLOCKED exactly by the
fiber-constancy of φ (the two pinnings would need ν̂₁−ν̂₂ = −1 and −2
simultaneously); (b) the annex direction: ⟨I₁,I₃⟩ ∩ {ψ₁ = 0} =
⟨(−2,2,1,0)⟩ = "x₀² = x₁²ψ₀", but at A = {0} all masses are even, so
ν̂-constancy forces every within-fiber pair to the SAME (dt,K) — every
annex fiber is single-monomial (confirmed: all ten AS shapes), within-fiber
differences vanish, and no annex H can reach the candidate.  The verdicts
docstring's "K2-L11's mass-balance kills all annex pure-digit identities"
is thereby verified, with the mechanism made explicit.  No identity
outside ⟨I₁,I₃⟩ found; the claim quantifies over ALL glued groups of the
residue model, not just in-budget shapes.  K2-L11: CONFIRMED (attempt
grade; model faithfulness = F-3, correctly fenced).

**K2-L12 (patterns are subgroups).**  Forward direction: H_P ⊆ ker φ for
any assignment φ, and closure = coincidence at φ — exact.  Realization:
integer functional avoiding finitely many proper subspaces exists; the
span_Q \ H cross-ratios force torsion, correctly flagged and KEPT
(conservative for every universal quantification — the direction that
matters for corner safety and THM-B).  One consequence verified benign:
for shapes whose only protecting states are torsion-flagged (GS-29, GS-36,
GS-43 witnesses print /tors), CONDITIONAL-grade protection may be
unrealizable in some characteristics — no consumer cites CONDITIONAL
positively (passengers never anchor; THM-B consumes only corner-safety,
which is universal-mode and torsion-inclusive).  CONFIRMED.

## S2. Charge 2 — K2-L9 / K2-L10 re-derived; one statement-scope gap; one stale downstream site

**K2-L9, steps (1)–(5) re-derived.**  (1) Both A = {0} events cost 2 units,
two events cost 4 > 3 = 2g₀−1: one event per active window — exact.
(2) (units,p) singletons; the n = 3 exchange class {C₁,C₁}↔{C₀} needs C₁ —
exact (probe E re-ran the committed `legal_drains_g2` read-only: SPOT-1/2
reproduce; under A = {0} only {C₀} survives in the (u2,p0) class).
(3) parked-parity seed disjointness: sound FOR A FIXED FIBER (arrival base
common, consumption even, t-flip flips parity ⟹ different slot).  (4) C₀
placement rigidity: at fixed (budget, p_w) the A = {0} drain is DETERMINED
({C₀,promo} = 4 > 3); re-derived, including the honest contrast that
{C₁,promo} = 3 fits, which is why (e) lives.  (5) single-book conclusion —
sound AS A SINGLE-BOOK STATEMENT.  **The gap (G3): LEGS23 states the lemma
group-wide** — "every bottom-line group is a single residue class carrying
a SINGLE sign", "Hence every bottom-line group…the involution has no
moves" and claims-table rows K2-L9(3)/(5) PROVED unqualified — while the
proof of (5) opens "A single-book group fixes…" and step (3)'s "No bottom
group mixes seeds" fails for glued A = {0} groups: the unit's OWN annex
exhibits in-budget counter-configurations (AS-02 mixes seeds dt = 0/1
across fibers via the d = 1 dump offset; AS-01/AS-03 mix signs across
fibers of unequal mass; AS-01 is an opposite-sign glue pair = a live
involution move).  The note of record catches and re-scopes this at S2
("K2-L9's single-sign conclusion is a single-book statement") and grades
the annex separately — the assembled program is honest, no consumer uses
the broad form (PC-6 says "Beyond K2-L9's single-book reach").  But the
component note's statement stands over-broad in situ.  GAP.

**K2-L10 re-derived.**  (a) {C₁,C₁,C₁} single-window: 3 → 2 → 1 stall,
third C₁ needs opening ≥ 4 > 3 (probe E SPOT-3: no single-window K with
three 1s, max two, at any n ≤ 3 — reproduced); single-window β_min groups
land in the K2-L3 inventory, co-located combos = the THM-A forms (consumed
at attempt grade).  (b) the (e) chain: w₁ = [C₁,promo] (3 units, f = 0) →
w₂ opens 1, inactive; vs w₁ = [promo] (f = 1) → w₂ opens 2, [C₁], f = 1;
identical totals {C₁}, p = 1, parked 1, promo profile (1,0) both ⟹ one
group, net −2 = K2-CAND — arithmetic exact.  The HONEST-CAP paragraphs
(neither box closes by budget; (e) is a line-quanta question; per-window
budgets shift across a fiber) are the load-bearing honesty and are
correctly restated in the skeleton (S2, PC-8, (K2-RES-B)(ii)/(iii)).

**Propagation of the reversal (the charge's "no site still claims (b)/(e)
budget-dead").**  SYNTHESIS_PASS9 S4's per-box table is hedged ("plausibly
BUDGET-dead…may forbid") — acceptable as the historical prediction LEGS23
names and corrects.  **But (G4): `BRIDGE_ADJUDICATIONS_2026-07-30.md`
line 10147** — the pass-9 ranked-findings ledger entry — still flatly
records "the per-box kill table ((K2-RES)(a)/(e)/W2-BOX-1 pin-immune;
**(b) budget-killable**)", and its item (3) sells K2-CLOSE as
"window-budget kills of boxes (b)/(e)".  K2-L10 proved only the
SINGLE-WINDOW sectors budget-dead and (e) budget-LEGAL; the standing
ledger (a consumer-facing authority) carries no correction bracket.  GAP
(one-bracket fix for the composer).

## S3. Charge 3 — the machine legs: re-runs REPRODUCE; caps adjudicated; three verdicts hand-re-derived

**Re-runs (sandboxed copy, repo untouched).**  `k2close_enum.py --xcheck`:
SELFTEST inventory exact; 43 main + 10 annex shapes regenerate; GLUE-COVER
38/38 ALL MATCHED; GLUE-CENSUS 29/38/{SDG2BF:14, SDG2BZ:14, SDW4G2F:1};
GLUE-DUP the single SDW4G2F fiber; CTRL-MUT 190/190; results json identical
to committed except `elapsed` and ONE artifact — the SEAL law fires on any
re-run (NOTE N4: regeneration emits the pre-verdict PENDING table, the
committed file holds the verdict section; the shape table produced after
the full run is byte-identical to the committed one).  `k2close_verdicts.py`:
verdict table identical mod the timing suffix; results json identical mod
`elapsed`; tallies 35+9 CONDITIONAL / 8+1 NOVEL / 0 PROTECTED; laws GREEN;
PV-4 the sole MISS.  All three md5 pins verified against the on-disk
artifacts before consumption.

**Budget caps B1–B8, derived vs declared.**  B1 = K2-L2, derived.  B2
(arrivals ≤ 2 units): reduced dumps/d-cells ≤ P₀ − 1 raw + the Y unit
⟹ ≤ P₀ = 2e₀ ⟹ ≤ 2 units — derived, and GENEROUS (a_s0 up to 2 where
s₁ ≤ e₀−1 forces ≤ 1): over-enumeration only inflates the table, safe for
every universal verdict.  B3 (root carry ≤ 1): σ₁ ≤ 2(e₀−1) < P₀ —
derived.  B4 (ONE dumping interior correction) — the ONLY declared cap,
and rightly so: it is the same open boundary as box (b)'s multi-window
stratum; deriving it would be closing (iii).  Honestly disclosed in the
docstring, the table's beyond-budget section, S0, and F-4.  B5 (r ≤ 3):
follows from B4 + B2 (a_d ∈ {0,1,2}), with sub-unit slot separation
resting on the PE1 raw-j₀ double-enumerator cite — derived.  B6 (p ≤ 2
from 2p ≤ 5), B7 (t ∈ {0,1} at g₀ = 2, W-D2(iv)), B8 (K2-L8) — derived.
No declared cap that should be derived.  One model-scope observation
feeding G2: the family loop shares (c_init, order, a_s0, p, r0, T) across
fibers and varies only a_d — i.e. "glued" is formalized as PURE
DUMP-VARIANTS with a common promotion/arrival profile, which is the
(K2-RES)(a) mechanism and matches all 38 realized groups (GLUE-EDGE), but
is narrower than "(R1) fails".

**Hand re-derivations (charge's three, plus).**  GS-08 (CONDITIONAL,
the realized anchor): monomials x₀ψ₀ρ₁(−), x₀ψ₁²ρ₁(+), x₀ψ₁ρ₂(−), T = −1;
generic (−1,+1,−1) unprotected; full merge −1 protected; under I₃ the
in-fiber pair cancels FORCEDLY and every state is (0,−1)-protected — corner
column YnYn re-derived.  GS-11 (NOVEL imbalance): T = −2; any state's nets
sum to T, protected states sum to 0/±1 — impossible; the invariant
shortcut is airtight.  GS-40 (NOVEL by exhaustion): the display case
checked — {a,c} in a zero-block forces c − a = −I₁ ∈ H (same fiber, ρ
cancels), and b − d = x₀ψ₁² − x₁ψ₁³ ≡ I₁, so the candidate X = {b},
Y = {d} blocks merge and annihilate; the three I₁- and three I₃-pair
linkages chain every cell.  Also GS-02 (glue-pair dichotomy, kill in every
corner), GS-04 under I₁, AS-03 (full merge −2 = PROT2K at odd char,
generic (−1,−1) unprotected), AS-10 (T = 3 ∉ {0,±1,±2^k}).

**The verifier's independent probe (`k2close_pe1_ext.py`, ALL GREEN).**
Fresh lattice code + FULL Bell-partition enumeration (not the runners'
BFS): GS-40 has EXACTLY 53 closed partitions, none protected, and every
state's ρ-free lattice part decomposes in ⟨I₁,I₃⟩ (coefficient box ±2) —
a decorrelated confirmation of both the 53-state exhaustion and the
ID-CLOSURE shadow on the hardest shape.  GS-11/AS-10 exhaustively
unprotected WITHOUT the invariant shortcut.  GS-08 corners re-computed
independently: c11/c01 universally protected, c10/c00 not — matches YnYn.
GS-02 kill state present in all four corners.  T-invariant audit of the
whole committed table re-parsed: NOVEL ⟺ (main: |T| ≥ 2 or GS-40; annex:
|T| ≥ 2 and not 2^k) across all 53 rows.

## S4. Charge 4 — K2-THM-B sound; the residual box has two description gaps

**Scope conjunction.**  Statement, S7 claims table, and header agree:
TRACK ∧ (H1)–(H3) ∧ g₀ = 2 ∧ c_{m−1} ≥ k ∧ (R0) ∧ (R2) ∧ (R1⁺/R3⁺ = the
B4-table pin) ∧ (R4⁺).  The annex shapes are correctly excluded by (R2).

**(R4⁺) covers.**  (R4) ⟹ (R4⁺): {S} covers all four; {P1,T1} = c00,c01
∪ c01,c10,c11 — all four.  New minimal covers verified against the
machine corner column: {P1, X} for X ∈ {GS-04,06,15,24} (YYnn = c11,c10;
P1 = c00,c01); {P2, Y} for Y ∈ {GS-05,08,16,25} (YnYn = c11,c01;
P2 = c00,c10); {P1,P2,Z} needs exactly a c11-cover, Z ∈ {T1, GS-38,
GS-41, any safe-corner shape containing c11}.  Strictness: the nine
realized anchor rows cover only {c01,c11}.  Exact.

**The proof.**  A residue assignment φ fixes I₁/I₃ truth (tower-level,
row-coherent — THM-A's point), hence a corner.  Single-book leg = THM-A's
form evaluations (re-checked: S always, P1 ⟺ ¬I₁, P2 ⟺ ¬I₃, T1 ⟺ I₁∨I₃).
Glued leg re-derived in full: the in-vivo pattern P at φ has H_P ⊆ ker φ,
is closed, is base-closed at the corner (base identities ∈ ker φ), never
contains a φ-falsified identity, and is REACHED by the BFS (merge toward
P keeps intermediates ≤ P with H ⊆ ⟨base ∪ H_P⟩ ∌ the excluded identity —
so the subtree pruning is sound and the corner space contains every
realizable corner-consistent pattern; torsion states are kept, which is
the conservative side for a universal verdict).  Corner-safety therefore
transfers: G's class vector at φ is a visited protected state.  CONFIRMED
at attempt grade, correctly fenced by F-3 (model faithfulness) and F-5.

**Pattern-class derivations (PC-1..PC-8).**  All re-derived sound, with
one bracket slip (NOTE N2: PC-3 lists "GS-09–14", which sweeps up the
NOVEL GS-11 already assigned to PC-4; should be GS-09/10/12/13/14).
PC-4 (even-dup genre): SD-L7 impossibility from T = ±2 exact; the merge
states die iff char = 2 — right, and PROPERLY same-sign.  PC-6: the 2^k
anchor argument and the order-2 torsion loss of SD-L7 on the partial
(−1,−1) state — exact, fenced by F-2 (PROT2K ≠ SD-L7; survival-graded).
PC-8 (K2-CAND): never a witness (no SD-L7 state at any char), dead at
char 2 cannot block an existential box, threatens only as a sole
population, β_min occurrence gated on the line-quanta question — exact
and honest.

**(K2-RES-B) — honest? complete?**  Nothing PROVED consumes the box:
K2-THM-B is insulated by its (R1⁺/R3⁺) hypothesis; K2-L11/L12 are
budget-free; the instance leg is machine fact.  Items (i) and (iv) exact
((i) even flags the additive (−1,+1,−1)-sums escape).  Two gaps in the
box's DESCRIPTION of what remains:

* **(G1) The unification flourish overclaims.**  "(ii) … The involution
  program is COMPLETE at g₀ = 2: no opposite-sign failure mode remains
  anywhere; what is left is multiplicity arithmetic."  Two over-broad
  axes.  (a) Beyond the enumerated perimeter, (iii) itself keeps the
  SHAPE list open: an un-enumerated glued or out-of-list single-book
  group can still die by an opposite-sign coincidence (box (b)'s own
  displayed kill IS one — a −2 class under I₁+I₃ against an unprotected
  partner); K2-L11 closes the identity ALGEBRA there, not the kill
  CLASSIFICATION.  (b) Even inside the perimeter, survival (SD-L6) of
  NOVEL or corner-uncovered systems at PARTIAL states can fail by
  mixed-sign ADDITIVE cancellation (e.g. GS-20's generic −3r₁ − r₂ + 2r₃
  = 0 on a torus hypersurface, any large char) — acknowledged at (i) for
  corner-uncovered systems but contradicted by (ii)'s "never a sign
  cancellation"; and GS-40's full merge is a char-free mixed-sign death
  (T = 0), covered by "char | forced net count" only as char | 0.  The
  TRUE content — every SD-L7-calculus-internal, coincidence-driven
  opposite-sign mechanism within the B4 table is classified, and every
  in-perimeter unconditional single-group death at the anchor/merge
  states is char | count — needs exactly that scoping.  GAP.
* **(G2) The un-named glued strata.**  (iii) describes beyond-B4 as
  "≥ 2 dumping interior corrections, W ≥ 3 windows".  But the enumerated
  concept of "glued" is dump-variant families sharing (order, arrival,
  promotion profile); an (R1)-failing bottom group whose fibers tie
  lines across DIFFERENT promotion profiles (quanta arithmetic
  E_m·Δw₀ = −Δ(promo quanta)) or across different interior skeletons is
  within W ≤ 2 yet outside both the table and (iii)'s wording.  None is
  realized (GLUE-EDGE 38/38 — all realized glued groups ARE pure dump
  variants), K2-L11 still bounds their digit identities, and K2-THM-B is
  insulated by hypothesis; but the box's "boxed exactly at S5" /
  "What remains open is ONE genre … plus the corner-uncovered systems"
  under-enumerates the open (R1)-failure space.  GAP.

## S5. Charge 5 — the PV-4 miss: honestly disclosed; the finding verified from the artifacts

The sealed PV-4 text (verdicts docstring) predicted realized GS-02 vectors
(−1,+1) with the glue identity FAILING in vivo on all 28.  The data
falsified the prediction and the unit says so in the right register: MISS
reported separately from law violations (FINAL judges laws only), sealed
text byte-untouched, the GLUE-DEGEN law ADDED to pin the finding, and the
note promotes it to "the unit's substantive finding" with the right three
consequences.  Verifier's independent leg (probe D, straight from the
md5-pinned `survk2_instrument_results.json`, no k2close code imported):
exactly 38 glued bottom groups (≥ 2 distinct interior books) on exactly
29 rows of exactly {SDG2BF, SDG2BZ, SDW4G2F}; EVERY one carries a single
in-vivo residue class (the per-cell `res` strings coincide within each
group); nets: 28 × [0] (dead), 8 × [+1], 2 × [−1] — the 28 + 10 split
exact.  The residue-degenerate observation is accurate; "probes ONLY the
full-merge corner … NO evidence about generic glue ratios" is the honest
reading; the residue-generic falsifier target is well-posed.  One prose
slip in the disclosure chain is NOTE N3 (the "carried by co-located S
groups" parenthetical: 8 of the 28 dead GS-02s sit on the nine anchor
rows, carried by GS-08 full-merge anchors, not by S groups; S6's
consequence (b) states it correctly).  Leg 1b's PV "seal" mechanism is
NOTE N5 (session-internal, not commit-boundary; wording honest).

## S6. Charge 6 — fresh-eyes assembly checks

Commits 13a2179 / 8579216 / 816c75e / 11e1743 / 7bb28a6 / a8914944 /
3b9bc84 / 4ed354a all exist and carry the described contents.  All S0–S7
section pointers of the skeleton resolve; the S4↔S6 GLUE-DEGEN pointer
(fixed at 4ed354a) is correct.  Grade caps consistent across the three
K2-CLOSE documents and SURVK2 (everything ATTEMPT under the W arc 0/2;
F-5 correct that no hostile pass had run — this pass is the first).
LEDGERLAMBDA: consumed as "bookkeeping frame only", and grep confirms the
single S0 mention — no lemma of it enters any proof step; its own arc
(0 passes) is not individually named, but the W-arc cap it carries is the
same cap the note already declares, so the cap sentence remains true
(NOTE N6).  Tallies, NOVEL set, corner-safety lists, the realized census
(20/29 class-closed; the nine {c01,c11} rows), and the claims table all
match the machine artifacts.  The consequence paragraph claims exactly
THM-A ∪ corner-covered systems — no grade inflation; fences F-1..F-5
accurate (F-1's insistence that the nine rows' in-vivo protection is
instance fact, not theorem, is exactly right).

## S7. FINDINGS (quote-and-classify)

**CRITICAL: none.**

**GAP G1** — K2CLOSE_2026-08-08.md, (K2-RES-B)(ii): "The involution
program is COMPLETE at g₀ = 2: no opposite-sign failure mode remains
anywhere; what is left is multiplicity arithmetic."  Over-broad on (a) the
un-enumerated strata ((iii) keeps the shape list open; identity algebra
closed ≠ kill classification closed — box (b)'s own displayed kill is an
opposite-sign mode) and (b) additive mixed-sign deaths at partial states
of NOVEL/corner-uncovered systems (flagged at (i), contradicted by
(ii)'s "never a sign cancellation"; GS-40's full merge is a char-free
mixed-sign death).  Needs scoping to: coincidence-driven opposite-sign
modes within the B4-enumerated perimeter, additive arithmetic and
beyond-perimeter shapes excluded by name.

**GAP G2** — same box, (iii): the open (R1)-failure space is wider than
"≥ 2 dumping interior corrections, W ≥ 3 windows": multi-fiber bottom
groups gluing by line-quanta ties across unequal promotion profiles or
unequal interior skeletons sit inside W ≤ 2 but outside the enumerated
dump-variant family model (shared (c_init, order, a_s0, p, r0, T), a_d
varying).  Unrealized (GLUE-EDGE 38/38) and THM-B-external by hypothesis,
but the box should name the stratum (or the scope pin should define
"glued" as dump-variant families and say the rest is open).

**GAP G3** — K2CLOSE_LEGS23_2026-08-08.md, Lemma K2-L9 + claims table:
"every bottom-line group is a single residue class carrying a SINGLE
sign … the sign-reversing involution of (SURV-K2) has NO moves on
A = {0}" — statement broader than its proof (step (5) proves the
single-book case; step (3)'s "No bottom group mixes seeds" fails for
glued A = {0} groups — AS-01/02/03 are in-budget counter-configurations,
AS-01 an opposite-sign glue pair).  Already sharpened in the note of
record (S2) and consumed only in single-book scope; the component note
needs the qualifier in situ.

**GAP G4** — BRIDGE_ADJUDICATIONS_2026-07-30.md:10147 (pass-9 ledger
entry): "the per-box kill table ((K2-RES)(a)/(e)/W2-BOX-1 pin-immune;
(b) budget-killable)" and item (3)'s "window-budget kills of boxes
(b)/(e)" — stale after K2-L10 (only single-window sectors budget-die;
(e) is budget-LEGAL); the standing ledger needs a correction bracket.

**NOTE N1** — K2CLOSE note S1/verdict-1: "(Machine shadow: 0 violations
over every state of every shape.)" — the exists/universal explorations
early-return, so ID-CLOSURE was checked on every VISITED state (S6 and
the verdict table say it correctly); the |T| ≥ 2 shapes' free spaces are
never explored at all.  Coverage claim should read "every visited state".
**NOTE N2** — S4 PC-3's "[GS-09–14, …]" sweeps up GS-11 (NOVEL, T = −2,
already in PC-4); should read GS-09/10/12/13/14.
**NOTE N3** — S6 + verdict table + verdicts docstring: "the 28 GS-02
groups net 0 … (their rows carried by co-located S groups)" — 20/28 are
on S-rows; 8/28 sit on the nine anchor rows carried by GS-08 anchors.
**NOTE N4** — `k2close_enum.py --xcheck` is non-idempotent: any re-run
after commit 2 fires SEAL spuriously (regenerates the PENDING table
against the verdicted file); everything else byte-reproduces.
**NOTE N5** — leg 1b's PV-1..5 "seal" is a pre-first-run hand derivation
inside one commit (816c75e), not leg 1a's two-commit boundary seal; the
docstring's wording ("BEFORE first run") is honest, the shakedown annex
repair disclosed.
**NOTE N6** — LEDGERLAMBDA consumed frame-only without naming its own
0-pass arc; harmless (single mention, no lemma consumed, same W-arc cap).

## Verdict block

Spine claims K2-L11, K2-L12, K2-THM-B, K2-L9 (single-book scope),
K2-L10, the verdict column, and the instance leg: CONFIRMED at their
declared (attempt/machine) grades.  The four gaps are description/scope
repairs — none breaks a proved chain, none is consumed downstream in its
over-broad form.  Machine legs reproduce; the verifier's independent
probe (fresh algorithms) is green including the GS-40 53-state
exhaustion and the artifact-level GLUE-DEGEN census.  Arc counter
consequence: GAPS-ONLY ≠ CLEAN — the K2-CLOSE arc stands at 0/1 CLEAN
after this pass.

K2CLOSE-PE1 FINDINGS: 0 critical, 4 gaps
VERDICT: GAPS-ONLY
