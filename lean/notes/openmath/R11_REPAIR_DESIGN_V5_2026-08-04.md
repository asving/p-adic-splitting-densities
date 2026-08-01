# R11 REPAIR DESIGN — V5 (2026-08-04): the consolidated rewrite

**Status: DESIGN ONLY — the round-5 candidate, a FRESH, SELF-CONTAINED
consolidation.** It replaces `R11_REPAIR_DESIGN_2026-08-03.md` (four in-place
revision layers, marked SUPERSEDED there); nothing from that file is needed to
read this one. No edit to ROOT (`docs/ROOT_ASSEMBLY_2026-08-02.md`, REVISION 9,
a2ad88a) and no edit to the D-11 leaf
(`lean/notes/openmath/D11_massid_phaseB_attempt_rev3.md`, 8a0786c) is made here.
This design goes to a Codex plan-review (round 5) BEFORE execution; §7 lists the
execution units.

**Provenance and warrant.** Four Codex plan-reviews (fresh contexts:
`R11D_review_2026-08-04.md`, `R11D2_review_2026-08-04.md`,
`R11D3_review_2026-08-04.md`, `R11D4_review_2026-08-04.md`) each returned
DESIGN-REVISE. Round 4 accepted the honest-pricing strategy — every contested
proposition is PRICED as a displayed [M] member or stated as a NAMED proof
obligation with a retirement route, never defended by evidence arguments — but
found the four patch layers internally unsynchronized (its findings 1–8
CRITICAL, 9 ADVISORY). This V5 carries forward EVERY accepted decision of
rounds 1–4 IN THE BODY (no patch notes) and fixes the round-4 criticals at
their homes. §8 is the completeness self-check: every finding of all four
rounds → its disposition in this file.

## 0.1 What happened (self-contained)

The ROOT composition assembles the uniformity theorem (splitting-type densities
of Haar-random monic degree-n p-adic polynomials are values R_τ(p) of single
rational functions, at every prime including wild) as a linear walk of 19+
steps over verified/proved-unverified leaves, with all open mathematics priced
in named hypothesis rows ("[M] rows"; ten rows at the r11 baseline). Its
Phase-C acceptance (2026-08-03) was SUSPENDED the same day: the owed hostile
pass on leaf D-11 (`D11_owedpass_2026-08-03.md`, Codex, fresh context) returned
CRITICAL findings, and the impact audit (ledger
`BRIDGE_ADJUDICATIONS_2026-07-30.md`, 44ce0a7) showed two MANDATORY ROOT steps
consume the refuted layers AS PROVED:

- **Step 17** consumes D-11 **Theorem M1** (mass identification: the abstract
  solve family 𝔅_n's entries ARE Haar masses of continuation events) — refuted
  at its announced conditioning scope (C1), at the family-(v) per-entry mass
  claim (C2), at its §5/§7 billing (C3), and at its multi-step disjointness
  clause M1(b) (C4).
- **Step 18b** consumes D-11 **Theorem M2** (the solved values ARE the real
  conditional densities) — FALSE at its displayed universal scope (C6:
  arbitrary allocation data satisfy (S1)/(S2) yet destroy the mass reading; the
  proof mis-cites M1(a) at family-(iv) verdict rows). GAP G5 (Lemma M2.0's
  address induction omits within-block loop history) sits in the same consumed
  chain.

Also owed from the same campaign: **O11-G2** — the CUT-WD premise of Step 18's
consumed walk has no ROOT display and no [M] home; and the O-11 leaf-side
n ≥ 2 Lean-guard note. Both dispositioned at §5.

## 0.2 The decision per layer (summary)

| finding | decision | mechanism |
|---|---|---|
| D11-C1 (M1 conditioning scope) | TRUE-SCOPE REPAIR | per-clause reference-measure display; no formula changes (§2.1) |
| D11-C2 (family-(v) L6a factor) | TRUE-SCOPE REPAIR | the relaxed-box event □(P) + Lemma (BOX-VOL), 2-line proof over L6a's own displays (§2.2) |
| D11-C3 (billing contradiction) | display repair | §5/§7 re-billed to match (a″) exactly (§2.3) |
| D11-C4 (M1(b) disjointness) | TRUE-SCOPE REPAIR | (b-PF) prefix-free lemma (argued in-design) + **(b-EX)** grammar-exhaustiveness OPEN LEMMA (r4 proof obligation; induction sketch displayed, §2.4) + the **(LOOP-∞)** null/disjointness display for the infinite loop-0 word |
| D11-G5 (M2.0 addresses) | TRUE-SCOPE REPAIR | loop-extended addresses; two-letter transport induction (loop letters ← L2/L3 PROVED, hand-off letters ← (S1-m)); r4 obligations **(O-1)–(O-5)** enumerated with routes + the GLOBAL obligation **(O-GLOB)** at its corrected v5 form (§3.4) |
| D11-C6 (M2 false at scope) | TRUE-SCOPE REPAIR + [M] PRICE | Theorem M2 restated AT the hypothesis (RE); at the CONSUMED member, (RE)+row-form = **(PACK-iv)**, a NEW (H5) row-law member — the PRIMARY route; the definitional discharge WITHDRAWN (§3.3/§3.5) |
| D11-C7 (M3(b) silent clause 4) | leaf statement hygiene | conditionality moved in-statement; ROOT already insulated at (H5) (§2.7) |
| D11-G8 (M3(a) "EVERY polynomial") | TRUE-SCOPE REPAIR + [M] PRICE | conclusion at separable lifts (Theorem E's scope) + ns-null mass-sufficiency note; the pin → predicate → corpus chain PRICED as **(NSF-INT)** and the as-built keying conformance as **(NSF-KEY)** — the two members of the NEW row **(H9) = (NSF)**; quotes (q-1)–(q-6) kept as CONTEXT; the channel-coverage audit **(CH-COV)** replaces the former universal non-consumption claim; contingency (NS-ALL) keyed to it (§2.5) |
| D11-G9 (falsifier criterion) | display repair | criterion rescoped to (a″)'s families (§2.6) |
| O11-G2 (CUT-WD) | [M] PRICE | NEW row **(H8) = (K-CUT)**, with the O-11 charge-(vi) adjudication as named retirement route (§5.1) |
| O11-C1 residue (n ≥ 2 guard) | leaf/Lean note | O-11 r4 restates the target row at n ≥ 2; BK.series_tie carries the guard at formalization (§5.2) |

Plus the composition-side obligations this design itself creates: **(ROW-Σ)**
(the member-row normalization theorem-obligation, §4.2 — the ONE authoritative
display) and **(CH-COV)** (the M3-consumer closure audit, §2.5).

## 0.3 Status (the official tier list; the reviewer tier language of round 3)

- **MET on file:** N3, N6.
- **MET AT PRICE:** N5, N7 — one NEW [M] member, (PACK-iv) (§3.5); N8 — the
  NEW row (H8) for Step 18's K1 CUT-WD leg (§5.1).
- **BLOCKED-PENDING** (the operational line; round-4 finding 6: N1's line
  now carries (ROW-Σ); N2's carries (CH-COV). Display rule, exact (round-5
  finding 8): the FULL line is displayed only here; every other status
  display (§4.1's need table) carries the line's per-need clause VERBATIM —
  "BLOCKED-PENDING (⟨that need's parenthetical from this line⟩)" — and
  nothing else):

> **BLOCKED-PENDING: N1 ((b-EX) + (ROW-Σ) proofs), N4 ((O-1)–(O-5) + (O-GLOB)
> global proof), N2 ((NSF-KEY) execution — known false at HEAD until the gated
> definition change lands — plus the (CH-COV) closure audit).**

The composition is NOT restored, and the acceptance standing does not move,
until the r4 proof obligations ((b-EX), (O-1)–(O-5), (O-GLOB), (ROW-Σ))
discharge under the D-11 r4 hostile pass, the (CH-COV) audit closes clean (or
its finding is priced), (NSF-KEY) executes under Unit C's gates, AND the
Unit-D end-to-end bar passes. **[M] accounting (exact):** ROOT's row count
ten → **TWELVE** ((H8) + the two-member row (H9)); (H5)'s displayed row-law
roster three → FOUR (PACK-i/ii/iii/iv) — a member, not a row (round-4 finding
9 confirmed this arithmetic).

Failure mode, recorded in advance: if (b-EX)'s write-out fails at any family,
or any (O-i)/(O-GLOB)/(ROW-Σ) resists its displayed route, or (CH-COV) finds
an out-of-channel consumer (then (NS-ALL) fires and is priced per §6), or
(NSF-KEY)'s sign-off is refused, the corresponding need stays BLOCKED-PENDING
and this design returns for re-adjudication before any ROOT edit.

---

## 1. Objects and vocabulary used below (minimal, for the fresh reviewer)

D-11 works over the O-12 semantic model (VERIFIED leaf:
`O12_phaseB_verifybrief_rev4.md`): q₀ = p^δ, K₀/ℚ_p unramified, O its integers,
Haar on monic degree-e polynomials via coefficient tuples O^e; E := e(e+1)/2;
C_e := {v(a_i) ≥ 1 ∀i} the block-e state law; R_e := {v(a_i) ≥ i ∀i} the
descent event. One step of the descent process 𝒟_e stratifies C_e into loop
strata ((loop-0), (loop-c) for c ∈ F_{q₀}^×), pattern strata (patt-π), and
polygon strata (poly-κρ⃗), up to the null set Z_e; κ₀ := P(loop-0|C_e) =
q₀^{−E}, κ₁ := P(⋃_c loop-c|C_e) = (q₀−1)q₀^{−E}. The abstract solve family
𝔅_n (O-12 §2.3) has per-block entry tables E(e) in seven families:
(i) kernels, (ii) divisor-pattern masses m(π), (iii) polygon-family masses
m(κ,ρ⃗), (iv) verdict rows, (v) scalar atoms {q^{−b}} ∪ {(q^d−q^{d−1})^{−1}} ∪
{(q−1)/(q^{n+1}−1)} ∪ {q^{E_m}/(q^{E_m}−1)}, (vi) β-legs, (vii) solved entries
β_e(σ) = u^{−1}t_σ. Four BOOKINGS (O1)/(O2)/(O2′)/(O3) fix which strata are
booked as loop vs exit; the RE-ENTRANT bookings are (O1)/(O2′)/(O3). D-11's
Theorem M1 identifies entry values with stratum masses; Theorem M2 identifies
solved values with true conditional densities given seams (S1) (hand-off
faithfulness, ← ROOT Step 14) and (S2) (composition-datum correctness, ← ROOT
Step 18); Theorem M3 ties row labels to true types. ROOT consumes: M1/M1′/M3
at Step 17, M2 at Step 18b, the actual-pack correspondence + row-laws as
hypothesis (H5) = (PACK) with clauses PACK-i (rsh_interp), PACK-ii (r_bdd),
PACK-iii (wsh_ok) — and, after this design, PACK-iv (§3.5).

Booked kernel values and termination margins (O-12 Corollary D, consumed
throughout): kernel^{(O1)} = κ₀ + κ₁ = q₀^{1−E} (both loop strata booked
loop); kernel^{(O2)} = kernel^{(O2′)} = κ₀ (loop-0 alone; the recenterings are
exit-side); kernel^{(O3)} = κ₁/(1−κ₀) (the resummed E_rec =
{(loop-0)^{L−1}·(loop-c, c≠0) : L ≥ 1}); margins Φ^{(Ok)} := 1 − kernel^{(Ok)}:
Φ^{(O1)} = 1 − q₀^{1−E} ≥ 3/4, Φ^{(O2)} = Φ^{(O2′)} = 1 − q₀^{−E} ≥ 7/8,
Φ^{(O3)} = 1 − (q₀−1)/(q₀^E−1) ≥ 6/7. Under (O3) every exit row is multiplied
by the family-(v) scaling q₀^E/(q₀^E−1) = 1/(1−κ₀) (the loop-0 resummation
Σ_{L≥0} κ₀^L); under (O2′) the aggregated verdict row carries the re-feed leg
κ₁·x (coefficient pinned = κ₁); under (O2) — and ONLY under (O2) — the table
carries the free allocation datum α_e.

---

## 2. LAYER M1 (consumed at ROOT Step 17): true-scope repairs

### 2.1 C1 — the conditioning scope (statement repair, no formula changes)

**Defect (verifier, verbatim gist).** M1's preamble announces "with all masses
CONDITIONAL on the state law C_e", but (a′) reads vol(C_e) = q₀^{−e},
vol(R_e) = q₀^{−E} — AMBIENT Haar masses (P(C_e|C_e) = 1, P(R_e|C_e) =
q₀^{−(E−e)}); the singleton-residual readings are conditional on a CELL. "M1
does not have one coherent meaning of 'mass'."

**Verification that the defect is preamble-only.** Every clause-(a) bullet is
coherently conditional-on-C_e as displayed: (O1) q₀^{−(E−e)}·q₀·q₀^{−e} =
q₀^{1−E}; (O2) q₀^{−(E−e)}·q₀^{−e} = q₀^{−E}; (O3) κ₁/(1−κ₀); the pattern
bullet carries q₀^{−(E−e)} = P(R_e|C_e); the polygon bullet carries the
displayed conditional normalization q₀^{+e}. The verifier found no arithmetic
error anywhere (M1′'s arithmetic "survives checking"). The repair localizes to
the preamble + (a′).

**REPAIRED PREAMBLE (verbatim; replaces "Then, with all masses CONDITIONAL on
the state law C_e:").**

> Then, with the reference measure NAMED PER CLAUSE — clause (a): masses
> CONDITIONAL on the block state law C_e (each bullet displays its conditional
> derivation); clause (a′): per occurrence as displayed there (AMBIENT Haar on
> O^e for the valuation-box readings, with the conditional forms used inside
> (a) displayed as ratios; the PER-CELL conditional law for the
> singleton-residual readings; NO mass reading for the (O3) scalings — they
> exceed 1); clauses (b)/(d): statements about the one-step strata of the
> C_e-conditional process; clause (c): the per-visit margin sub-clauses
> CONDITIONAL on the block state law C_e (the loop/exit masses and the (r1)
> margins are C_e-conditional probabilities), and the per-block a.s.-exit
> sub-clause a statement about the C_μ-conditional law of each block μ [the
> two sub-clauses' reference measures named per round-1 advisory 7]:

**Proof obligations.** No new mathematics. ONE r4 duty (round-1 advisory 7):
sweep every downstream occurrence of the unqualified word "mass" in the leaf
(§§3–7) and pin each to its clause-(a)/(a′) reference measure or reword.
Survives verbatim: all (a) bullets, (b)'s one-step content, (c), (d), M1′.

### 2.2 C2 — the family-(v) L6a cell factor (the relaxed-box event)

**Defect.** (a′) claimed each q^{−b} occurrence "IS the Haar mass of the
displayed valuation box it names there — e.g. … the L6a cell factors
q₀^{−N(P)}", but the cell mass is (1−q₀^{−1})^k·q₀^{−N(P)} and NO
valuation-box event was defined: the same factor-as-mass inference the
revision had withdrawn for general factors.

**Why a true-scope repair exists (checked against the VERIFIED O-12 brief).**
L6a's verified display (O12_phaseB_verifybrief_rev4.md, "L6a (cell
identification and volume)") gives the cell as a PER-COORDINATE valuation
event:

> { g : v(a_{e−i}) ≥ ⌈h_i⌉ for EVERY column i ∈ {0,…,e−1}, with equality
>   v(a_{e−x_j}) = h_{x_j} at the k vertex columns }, volume
>   (1−q₀^{−1})^k·q₀^{−N(P)}, N(P) := Σ_{i} ⌈h_i⌉,

and its proof displays P(v ≥ t) = q₀^{−t}, P(v = t) = (1−q₀^{−1})q₀^{−t} per
independent coordinate. So the box is already displayed as the ≥-part of L6a's
own event description; only its NAME and one two-line lemma are missing.

**NEW DEFINITION + LEMMA (verbatim, into the r4 text at (a′)).**

> **Definition (relaxed box).** For an L6a polygon cell — by L6a's verified
> display, {g : v(a_{e−i}) ≥ ⌈h_i⌉ for every column i, with equality at the k
> vertex columns} — its RELAXED BOX is □(P) := {g : v(a_{e−i}) ≥ ⌈h_i⌉ for
> every column i} (the k equalities relaxed to the inequalities L6a already
> displays; cell ⊆ □(P)).
>
> **Lemma (BOX-VOL).** vol(□(P)) = q₀^{−N(P)} with N(P) = Σ_i ⌈h_i⌉ (L6a's own
> exponent), and P(cell | □(P)) = (1 − q₀^{−1})^k; hence L6a's cell mass
> factorizes as P(cell) = P(cell | □(P)) · vol(□(P)) with BOTH factors
> masses/conditional masses of displayed events.
> *Proof.* The coefficient coordinates are independent Haar with
> P(v ≥ t) = q₀^{−t} and P(v = t | v ≥ t) = 1 − q₀^{−1} — the two
> per-coordinate computations displayed inside L6a's verified proof; □(P)
> imposes one ≥-condition per column; the cell additionally one equality per
> vertex column; multiply over the independent coordinates. ∎

**REPAIRED (a′) FIRST SUBLIST (verbatim; replaces the q^{−b} bullet).**

> * q^{−b} (0 ≤ b ≤ E_n): each occurrence IS the AMBIENT Haar mass of a
>   displayed valuation box — vol(C_e) = q₀^{−e} (box {v(a_i) ≥ 1 ∀i}),
>   vol(R_e) = q₀^{−E} (box {v(a_i) ≥ i ∀i}) [L1]; the conditional form used
>   inside (a) is the displayed ratio P(R_e | C_e) = q₀^{−(E−e)}; and each L6a
>   cell factor q₀^{−N(P)} IS vol(□(P)), the ambient mass of the cell's
>   relaxed box, with cofactor (1 − q₀^{−1})^k = P(cell | □(P)) [Definition +
>   Lemma (BOX-VOL) above].

**r4 duties (round-1 advisory 6):** verify k counts DISTINCT imposed
equalities and that every referenced N(P) occurrence has the claimed
provenance. **Fallback** (only if the plan-review rejects (BOX-VOL)'s L6a
reading): narrow the sublist to the C_e/R_e occurrences and withdraw the
per-factor claim at L6a cell factors entirely (mass reading only through the
full cell mass at (a)'s polygon bullet). §4 shows NO downstream need consumes
the per-factor reading, so the fallback costs nothing on the mandatory path.

### 2.3 C3 — the §5/§7 billing contradiction (display repair)

**Defect.** (a′) correctly admits the (O3) scalings q^{E_m}/(q^{E_m}−1) are
"NOT masses (they exceed 1)", yet §5 clause 1 bills "PROVED … family (v) per
entry per (a′)" and §7 bills the unit charge "covered exactly at (a)/(a′)/M1′".

**REPAIRED BILLING (verbatim replacement lines).** §5 clause 1's family-(v)
fragment becomes:

> family (v): the q^{−b} occurrences (ambient box masses, incl. the
> relaxed-box reading of the L6a factor) and the (q^d−q^{d−1})^{−1}
> occurrences (per-cell singleton-residual conditional masses) per entry per
> (a′); the (O3) scalings are NOT masses — their entire mass content is (a)'s
> (O3) bullet (scaling × exit mass = mass of the displayed resummed event),
> and they are billed ONLY so;

and §7's coverage sentence becomes:

> The unit charge's "kernel/entry VALUES are masses" is covered exactly at (a)
> (families (i)–(iii), per entry, conditional on C_e), at (a′)'s box and
> singleton-residual readings, and at M1′'s concrete recorded row; it is NOT
> covered per entry at the (O3) scalings (only their products with exit masses
> are event masses), and families (iv)-arbitrary-α/(vi)/(vii) + the (S3)
> weight are excluded ((a″)).

### 2.4 C4 — M1(b)'s multi-step disjointness (prefix-free restriction + the grammar obligation)

**Defect.** "Multi-step events built from disjoint strata by the step maps are
disjoint at the first differing step" is FALSE: with w a proper prefix of w′,
E_{w′} ⊆ E_w (the verifier's loop-0 / loop-0-then-exit counterexample).

**REPAIRED CLAUSE (verbatim; replaces the refuted sentence inside (b)).**

> **(b-PF) [prefix-free multi-step disjointness].** For a finite word
> w = (s_1, …, s_k) over the one-step strata let E_w := {step j lies in s_j,
> j = 1..k} (composed through the step maps). If W is PREFIX-FREE — no member
> is a proper prefix of another — then {E_w : w ∈ W} is pairwise disjoint: two
> distinct members first differ at a position j that both words reach; on the
> common prefix the composed step-j state is the same point, and the one-step
> strata are pairwise disjoint at it by (b)'s one-step clause. [Without
> prefix-freeness the claim is FALSE — E_{w′} ⊆ E_w whenever w is a proper
> prefix of w′; the rev-3 sentence is WITHDRAWN at that generality.]
>
> **(b-EX) [grammar exhaustiveness — an OPEN LEMMA and a D-11 r4 PROOF
> OBLIGATION; the seven-family enumeration does not by itself demonstrate the
> exhaustiveness claim (round-1 finding 2) — it must be PROVED by a grammar
> induction].** Every within-block multi-step continuation event booked by a
> row of the DISPLAYED 𝔅_n row families (i)–(vii) (O-12 §2.3: E(e) IS the
> union of those seven displayed families), under any of the three displayed
> booking adjustments (§2.3(iv)/§2.4: the (O2) α-fold, the (O2′) re-feed leg,
> the (O3) scaling), is indexed by a set of STOPPING WORDS over the one-step
> strata — words whose proper prefixes are all-(loop-0) and whose final letter
> is not (loop-0). Any set of stopping words is prefix-free (a proper prefix
> of a stopping word is all-(loop-0), and no stopping word is all-(loop-0)),
> so (b-PF) applies to every such family. [Concrete packs' combined/adjusted
> rows remain clause-4 content — the existing scope sentence stands unchanged;
> (b-EX) quantifies over the DISPLAYED grammar only.]

**Proof route for (b-EX) — the grammar induction the r4 must write out,
sketched case-by-case (the case enumeration is exhaustive over the displayed
grammar BY CONSTRUCTION of E(e): O-12 §2.3 DEFINES E(e) as the union of
families (i)–(vii), and §2.4 displays exactly three booking adjustments):**
* family (i), kernels: (O1)/(O2)/(O2′) book one-step unions of loop strata —
  no multi-step content; (O3) books E_rec = {(loop-0)^{L−1}·(loop-c, c ≠ 0) :
  L ≥ 1} — stopping words. [In family (i) the only (g4) closure running along
  the TIME axis is the (O3) resummation, displayed as
  Σ_{w≥0} q^{−Ew}·(q−1)q^{−E}.]
* family (ii), divisor-pattern masses: one-step strata (patt-π). No word
  structure.
* family (iii), polygon-family masses: one-step strata (poly-κρ⃗); their (g4)
  closures (exponents c_j ≥ 1) run along the DEPTH axis w of L6b's cone —
  countably many CELLS of the SAME step (O-12 §2.2 lists the polygon strata
  among the one-step strata of C_e \ R_e), never a second step of 𝒟_e.
* family (iv), verdict rows: each books its exit stratum F — one-step at block
  e (the children cross into blocks μ < e: hand-off content consumed at M2's
  layer through (S1)/(S2), not an M1(b) multi-step event); the (O2)
  α-adjustment books the one-step recentering mass; the (O2′) re-feed leg
  books the one-step recentering strata; the (O3) adjustment scales each exit
  row to {(loop-0)^L ∘ F : L ≥ 0} — stopping words.
* family (v), scalar atoms: book no events except through their occurrences
  inside (a)/(a′) and the (O3) exit scalings — the latter exactly family
  (iv)'s (O3) case.
* families (vi)/(vii), β-legs and solved entries: book NO block-e continuation
  events ((a″) excludes them from every mass claim; their density reading is
  Theorem M2's conditional conclusion).
The r4 write-out = this case check stated against the displayed definitions,
one paragraph per family. Honesty clause: if any case fails to close from
displayed text at the r4 pass, (b-EX) stays an OPEN lemma at the failing
family, every consumer citing it inherits that conditionality, and §4's N1
re-opens — the outcome is priced in advance, not assumed away.

**(LOOP-∞) [the infinite loop-0 word — handled SEPARATELY: it is not a finite
word and is outside (b-PF) as stated (round-1 finding 2)].** Set
{loop-0 forever} := ⋂_{L≥1} {first L steps = (loop-0)} — measurable (a
countable intersection of composed preimages of displayed strata under the
step maps). (i) NULL: its C_e-conditional mass is ≤ P(first L steps = (loop-0)
| C_e) = κ₀^L = q₀^{−EL} → 0 (the Markov property, L2+L3, as in M1(c)'s
per-block clause — here at the single stratum (loop-0)). (ii) DISJOINT from
every finite stopping-word event E_w: the word w's final letter, at position
|w|, is NOT (loop-0), while on {loop-0 forever} step |w| lies in (loop-0);
both events constrain step |w| through the same composed step maps, and the
one-step strata at the composed state are pairwise disjoint by (b)'s one-step
clause — so E_w ∩ {loop-0 forever} = ∅. Hence (c)'s complement reread
decomposes the loop region EXACTLY as ⨆_{stopping words w} E_w ⊔
{loop-0 forever}, the last term null — the countable-additivity computations
of (a)'s (O3) bullet are unaffected.

**WHERE prefix-freeness is discharged for the consumed row-walks [never as a
no-hypothesis grammar fact]: at (b-PF) (argued above) + (b-EX) (r4 proof
obligation, route displayed) + (LOOP-∞) (displayed argument).** Consumers
re-pointed in r4: (a)'s (O3) bullet ("pairwise disjoint (they differ at the
first non-(loop-0) step)" → "pairwise disjoint by (b-PF), the family being
stopping words per (b-EX)"), the (O3) exit-scaling line, (c)'s complement
reread (→ (LOOP-∞)), and M2's renewal-equation exhaustiveness note (which
cites M1(b)/(d)).

**Proof obligations.** (b-PF): the two-sentence argument displayed above.
(b-EX): the r4 grammar-induction write-out per the displayed route — an OPEN
LEMMA until it lands AND passes the r4 hostile pass. (LOOP-∞): the two-part
display above, transcribed. Everything else in (b) survives verbatim.

### 2.5 G8 — M3(a)'s "EVERY polynomial" (separable-scope restatement) + the (H9) = (NSF) row

**Defect.** The consumed premise (O5triple Theorem E) covers "every monic
SEPARABLE lift"; M3(a) concluded "the true type of EVERY polynomial of the
event's cylinders" — separability of every lift is not displayed (ns-null
justifies only a.e.).

**REPAIR (verbatim; the conclusion sentence of M3(a)).**

> So the verdict σ labeling a decided continuation/termination event is the
> true splitting type of EVERY MONIC SEPARABLE polynomial of the event's
> cylinders — lift uniformity per box at Theorem E's own scope.
> Mass-sufficiency note: the nonseparable locus is Haar-null (T-6 (ns-null),
> VERIFIED-DUAL), so every mass/counting consumption of these labels (Step
> 18's K1/K4 interfaces) is unaffected; pointwise all-lifts separability at a
> counted box is NOT claimed here — where a counting consumer needs it, it is
> supplied by that consumer's own decided-ns-free certificate apparatus
> (O-1thr §1.4's fiber clauses; D-15's vocabulary), not by this clause.

**The displayed definitions (CONTEXT, not proof — verbatim quotes; what the
interface displays, kept so the priced members are checkable against their
sources).** Sources opened at the round-3 evidence pass: O-1thr
`O1thr_phaseB_verifybrief_rev4.md` §1.4 + §6 Theorem 3/Remark 4 + §8 (S-1);
M04 `M04-series-tie_fable.md` §§2–3, 5.5; M02 `M02-count-tie_fable.md`
headline + §2; Lean HEAD: `MovesU/Defs.lean` (ClassifierSpec),
`MovesU/DefsLedger.lean` (TreeSeam.count_tie),
`MovesU/BridgeD3_treeCarrier.lean` (bridgeTree),
`MovesU/BridgeD7_canonical.lean` ((†7) bridgeCanonical), `MovesT/Defs.lean`
(VTree/fiberAt/Realizes/NsFree), `MovesT/E11_treeN.lean` (hdet).

* **(q-1) [the bundled predicate — O-1thr §1.4]:** "**decided ns-free** :=
  every maximal chain is a (τ-irr) leaf and the Hensel payload covers the
  simple part — no ns-marks"; and the ns-halt is a MARKED halt: "(τ-ns) —
  write **NsHalts(o, f)** := o is a REALIZED non-saturated state whose window
  has no principal face on f — the ns-halt, MARKED". (Classification trees
  carry "leaf verdicts, and ns-marks" in the vocabulary; "decided ns-free" is
  the displayed decided predicate.)
* **(q-2) [the counted corpus — O-1thr Theorem 3(c)]:** "D_σ(N) := #{x
  level-N : fiber(T, x) for some decided ns-free T with type(T) = σ and
  thr(T) ≤ N}" — the corpus is decided-ns-free-quantified IN ITS DISPLAYED
  DEFINITION, and the whole package is scoped there: "Throughout: T decided
  ns-free, t := thr(T), fibers per §1.4" (Theorem 3's opening line).
* **(q-3) [the K1/K4 corpus quantifier — the TREE-N/TREE-EXP source scope,
  quoted on file at M02]:** "The note's TREE-N (MOVES 7559–7574, quoted in
  the T blueprint) is stated for trees 'complete finite realizable with all
  leaves (τ-irr)/(τ-hen)' — the ns leaves are excluded; the machine-checked
  discharge candidate `treeN` (E11_treeN.lean) carries `hdet : ∀ H ∈
  Tr.chains, ¬ Tr.nsLeaf H`" — verified at HEAD (lines 48/118; and `treeN`'s
  body passes `hdet` into `treeExp`, line 68). M04's K1 quantifies over "each
  complete finite realizable canonical tree" (= this source scope) and its K4
  reads "`bridgeMass` T (the normalized level-L fiber count, L = max(thr T,1))
  equals μ(fiber T) — level-exact cylinder reading; plus (ns-null) excluding
  infinite trees".
* **(q-4) [the interface pin — the ClassifierSpec docstring,
  `MovesU/Defs.lean`]:** "`canonical`: T_can^τ's verdict-type map … **`some σ`
  = complete finite realizable tree, all leaves (τ-irr)/(τ-hen), certified at
  level N (thr ≤ N)**"; and the counts are DEFINED from it: "decided_σ(N) —
  DEFINED from the canonical map (never a free field)"
  (`ClassifierSpec.decided … := Nat.card {f // X.canonical N f = some σ}`;
  `undec N := Nat.card {f // X.canonical N f = none}`).
* **(q-5) [what the partition identity actually is — M04 Theorem 2, proof
  step (a)]:** "At each level N the verdict map f ↦ canonical N f partitions
  the p^{nN}-element box into the σ-fibers and the none-fiber:
  Σ_σ decided_σ(N) + undec(N) = p^{nN} (SplittingType n is a Fintype — unit
  U0b; pure counting)" — TRUE FOR ANY Option-valued map; it routes NOTHING.
  The routing content lives in (q-4), not in the identity.
* **(q-6) [the intended drainage — O-1thr Remark 4]:** "The ns-free
  hypothesis is NOT removable: an exact-square family (n = 2: classes of
  (X − b)², v_p(b) = 1 held to level N) fibers an ns-marked tree whose counts
  scale by p, not p² — the countermodel is PARI-verified in the source
  campaign. Undecided/ns loci drain into the undecided envelope instead;
  their treatment is the drainage node, not this package."

**THE [M] ROW (H9) = (NSF) — the ns-routing interface, priced.** The
conditional statement — *at any instantiation satisfying (q-4)'s pin, every
K1/K4-labeled box lies in the decided-ns-free counted corpus and D-15's
exact-classification package applies with no a.e. weakening* — is the TARGET
of this row; the round-3 attempt to PROVE it by chaining (q-1)–(q-6) was
refuted (the chain imports exactly the two unquoted implications priced as
(NSF-INT) below) and stands WITHDRAWN.

> **(H9) = (NSF) — the ns-routing interface row** [two members; enters Step
> 18's K1/K4 chain and Step 17's M3 leg (via Steps 11/12), hence clause (R);
> clause (UB) inherits through the transported chain; NOT (0)/(SQ). Owner:
> the O-1thr/M04/M02 classifier-interface arc.]
>
> **(NSF-INT) — the interface implication chain (pin → predicate → corpus).**
> At every consumed site of Step 18's K1/K4 chain: (i) irr/hen-terminal
> completeness excludes ns-marks — a complete finite realizable tree with all
> leaves (τ-irr)/(τ-hen) carries no ns-marks; in particular the Hensel
> payload carries no ns-marks — so every box labeled under (q-4)'s pin fibers
> a tree that is decided ns-free in (q-1)'s sense; and (ii) M04's
> "complete-finite-realizable" scope coincides with the guarded TREE-N corpus
> ((q-3)'s all-leaves-(τ-irr)/(τ-hen), `hdet`-guarded trees) at every
> consumed site. The quotes (q-1)–(q-6) are CONTEXT for this member, not
> proof: none of them displays (i)'s no-ns-marks implication (ns-marks are an
> INDEPENDENT part of (q-1)'s "decided ns-free", and no quote says ns-marks
> occur only on ns-leaves) nor (ii)'s scope equivalence ((q-3) reports both
> scopes without equating them) [round-3 finding 1, accepted verbatim].
> NAMED RETIREMENT ROUTE — the ONLY one: the r4 leaf proof of the implication
> chain — (i) proved from the ns-mark/leaf-vocabulary definitions of O-1thr
> §1.4 (ns-marks attach only at (τ-ns) halts, which are excluded by
> all-leaves-(τ-irr)/(τ-hen) completeness) and (ii) proved site-by-site at
> the consumed K1/K4 sites — with retirement semantics EXACTLY the artifact
> list (NSF-INT-RET) below (round-5 finding 5). [The former SECOND route — "the Lean interface
> materialization discharges (NSF-INT) too" — is WITHDRAWN per round-4
> finding 4: retyping consumers to a guarded interface may BYPASS the
> implications; it does not PROVE this member as stated. Riders unchanged in
> kind: (E-N) — whether thr(T) ≤ N in D_σ(N) is redundant is OPEN at O-1thr
> rev 4; the target consumes the RESTRICTED count. The numerical
> decided_σ(N) = D_σ(N) tie is the count_tie/finiteness_stack row's content,
> at its own home.]
>
> **(NSF-KEY) — as-built keying conformance [ONE proposition; round-4
> finding 3: the former "equivalently" chain conflated the proposition with
> its realization mechanism and with its validation obligations — struck].**
> At the wired instance: for every n, p, level N, box f, and σ — if the wired
> classifier labels f (`bridgeCanonical … N f = some σ`) then f fibers a
> carried tree of the σ-carrier satisfying `MovesT.NsFree` (no ns-marked
> chain) at threshold ≤ N. KNOWN FALSE AT HEAD: the M02 exact-square poison
> V₀ (record below) is a carried, ns-marked, self-realized tree through which
> `bridgeCanonical` labels exact squares "totally split" — this member is an
> obligation certain to fire, not a contingency. [The `NsFree` conjunct on
> `bridgeTree` is the sanctioned realization MECHANISM — after it, the
> proposition holds by construction of (†7), since no ns-marked tree is
> carried and hence no fibering witness exists; the three re-typed theorems
> are downstream VALIDATION GATES. Neither is the proposition itself.]
> NAMED RETIREMENT ROUTE: Unit C (§7), with retirement semantics EXACTLY the
> artifact list (NSF-KEY-RET) below.
>
> **One-home argument (why one row, two members).** Both members are the
> ns-routing face of the SAME classifier interface: (NSF-INT) is the
> interface/paper side (the pin routes ns-content out of the counted corpus),
> (NSF-KEY) the as-built/Lean side (the wiring satisfies the pin). Same seam
> (K1/N2 label routing at Step 18), same owners, same consumption chain.
> Splitting them would scatter one interface's conformance across two homes
> against the VC7-2 one-home precedent. **The members RETIRE SEPARATELY**
> [round-4 finding 4: the former "the materialization discharges BOTH at
> once" claim is WITHDRAWN]: (NSF-INT) by its leaf proof, (NSF-KEY) by its
> gated execution; neither retirement discharges the other.

**(NSF-KEY-RET) — retirement semantics, exact (round-4 finding 3).**
(NSF-KEY) is RETIRED when and only when ALL SIX artifacts exist on file:

* **R-0 (sign-off precondition).** Asvin's recorded sign-off on the
  definition change (the statement fence of the parent CLAUDE.md), naming
  exactly the R-1 diff. No execution before it; refusal ⇒ Unit C
  NON-TERMINAL and the §0.3 failure mode (design returns; no ROOT edit).
* **R-1 (the NsFree conjunct diff).** `MovesU/BridgeD3_treeCarrier.lean`,
  `bridgeTree` gains the third conjunct — the carrier becomes, verbatim:
  `def bridgeTree (n p : ℕ) [Fact p.Prime] (σ : SplittingType n) : Type :=`
  `  {V : MovesT.VTree p (ZMod p) //`
  `    V.typemult = σ.1 ∧ RealizedSelf n p V ∧ MovesT.NsFree V}`
  (`MovesT.NsFree V := ∀ H ∈ V.chains, ¬ V.nsLeaf H` — the existing HEAD
  predicate, conjoined; plus the mechanical ripple through the carrier's
  projections and consumers, M02's own effects list: "canonical_pin,
  vtree_eq_of_fiberAt, Lemmas A/B are untouched (they never used the ns
  clause)"). **Ripple scope, CLOSED (round-5 finding 5):** the ripple is
  exactly the declarations referencing `bridgeTree` (its projections and
  direct consumers), enumerated at execution time by `lean_references`/grep
  and RECORDED as a list inside the R-5 confirmation; R-5's "diff is exactly
  R-1" check is adjudicated against that recorded enumeration — no
  open-ended "and consumers" residue.
* **R-2 (the three statements, verbatim as they will read).** The field/def
  TEXTS are byte-identical to HEAD — the re-typing is THROUGH the carrier
  (at the wired instance `F.Tree σ := bridgeTree n p σ`, now guarded):
  (1) `count_tie` (TreeSeam field, `MovesU/DefsLedger.lean`):
  `count_tie : ∀ (σ : SplittingType n) (N : ℕ) (T : F.Tree σ), F.thr σ T ≤ N →`
  `  F.mass σ T * (p : ℝ≥0∞) ^ (n * N)`
  `    = (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //`
  `        treeOf σ N f = T} : ℝ≥0∞)`
  — the quantifier ∀ T : F.Tree σ now ranges over ns-free carried trees only.
  (2) `canonical_stable` (ClassifierSpec field, `MovesU/Defs.lean`), with
  `canonical := bridgeCanonical` over the guarded carrier:
  `canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),`
  `  canonical N (boxProj p n h f) = some σ → canonical N' f = some σ`
  (3) `VPSound` (`MovesU/Defs.lean`), at the same instance:
  `def VPSound {n p : ℕ} (X : ClassifierSpec n p) : Prop :=`
  `  ∀ N (f : Box p n N) σ, X.canonical N f = some σ → X.trueType N f = some σ`
* **R-3 (the validations, one per statement — made precise; the former
  blanket "three theorems RE-PROVED" overpromised for VPSound).**
  (1) the wired instance's `count_tie` discharge COMPILED sorry-free over the
  guarded carrier (the TreePin discharge candidate re-run); (2) BridgeD8's
  `canonical_stable` proof re-run green over the new `bridgeCanonical`;
  (3) `VPSound` REMAINS the open kernel it always was (hypothesis-class,
  consumed as the ledger field `cl10_vpsound`) — the retirement artifact for
  it is the RECORD that the M02 V₀ refutation is DEAD at the guarded carrier
  (V₀ ∉ bridgeTree since ¬ MovesT.NsFree V₀) plus its consuming ledger
  wiring re-compiled; no proof of VPSound is promised or required.
* **R-4 (build gate).** Full `lake build` green + `lake env lean
  LeanUrat/AxChk_baseline.lean` footprint identical (a regression is
  stop-the-line).
* **R-5 (Codex diff confirmation).** Fresh-context Codex confirms the applied
  diff is exactly R-1 (+ its mechanical ripple) and the statement fence is
  respected — per the standing definition-change authority.

Retirement EFFECT, stated once: (NSF-KEY) holds by construction of (†7) over
the guarded carrier; N2's BLOCKED-PENDING clause drops "(NSF-KEY) execution";
(NSF-INT) is NOT retired by any of this (round-4 finding 4); E9 records the
executed status. M02's one flagged step — the intended `ReadsOf` semantics,
no compiled countermodel while `canPolicy` is designer-sorried — is inherited
here verbatim.

**(NSF-INT-RET) — retirement semantics, exact (round-5 finding 5; the
NSF-KEY-RET genre applied to the other member).** (NSF-INT) is RETIRED when
and only when ALL THREE artifacts exist on file:

* **I-1 (the leaf-proof artifact, named).** The implication-chain write-out
  inside the Unit-A L7 deliverable — the D-11 r4 leaf artifact, in a section
  titled "(NSF-INT) leaf proof" — proving (i) from the O-1thr §1.4
  ns-mark/leaf-vocabulary definitions and (ii) site-by-site over I-2's list.
* **I-2 (the closed consumed-site list).** The K1/K4 sites at which (ii)'s
  scope equivalence must hold are EXACTLY: the (†18) K1 row's invoked
  statements (M04 §5.5 (K1) + Lemma 3.3) and K4 row's (M04 §5.5 (K4) +
  D-15 = O-1thr Theorem 3(b)/(c)), PLUS any further M3(a)/corpus-consuming
  site surfaced by the (CH-COV) closure walk (L11) — L11's closure-complete
  trace is what CLOSES this list; I-1 must display the list it proved
  against and its identity with L11's.
* **I-3 (the validation gate).** The r4 hostile pass's ACCEPT of I-1 AS A
  PROOF (the same Unit-A gate that adjudicates (b-EX)/(O-i)/(ROW-Σ)),
  recorded with the pass artifact.

No other route retires (NSF-INT) (round-4 finding 4 unchanged); until all
three are on file it stands PRICED. Effect: (H9) loses its interface-side
price; (NSF-KEY)'s standing is untouched.

**The as-built keying FAILS the pin at HEAD — the on-file record behind
(NSF-KEY)'s "KNOWN FALSE AT HEAD".** The M02 attempt (on file 2026-07-31,
`M02-count-tie_fable.md`), re-verified against Lean HEAD:

* **the carrier:** "The carrier `bridgeTree n p σ = {V // V.typemult = σ.1 ∧
  RealizedSelf n p V}` (BridgeD3) carries **no ns-free clause**, so count_tie
  quantifies over trees with ns-marked leaves." At HEAD: `MovesT.VTree`
  carries the `nsLeaf` field; `VTree.fiberAt` clause (ii) displays the
  ns-leaf disjunct (`NsHalts T (some H) x ∧ ¬ IrrHalts H ∧ Tr.nsLeaf H ∧
  Tr.leafV H = some (nsVerdictOf H)`); `Realizes` is bare fibering (`∃ x,
  Tr.fiberAt T χ x`); `MovesT.NsFree` exists as a SEPARATE predicate (`∀ H ∈
  Tr.chains, ¬ Tr.nsLeaf H`) conjoined NOWHERE in `bridgeTree`; and
  `TreeSeam.count_tie` (`DefsLedger.lean`) quantifies `∀ (T : F.Tree σ),
  F.thr σ T ≤ N → …` with NO ns-free guard.
* **the classifier:** (†7) `bridgeCanonical N f` returns `some h.choose` on
  `∃ σ T, thr ≤ N ∧ fiberAt … f` over THAT carrier — so a finite ns-halted
  box fibering an ns-marked carried tree is LABELED, not routed to `none`.
* **the poison, exhibited (M02 §2):** the exact-square family's V₀ (chains =
  prefix-closure of {[ν₀]}, nsLeaf marked, leafV = nsVerdictOf, typemult
  {(1,1),(1,1)}, self-realized) "∈ bridgeTree n p σ₀ … and — this is the
  poison — **the classifier decides exact squares, with verdict 'totally
  split'**"; c_{V₀}(N) = p^{N−2} against (SCALE)'s forced p²-per-level growth
  — count_tie as typed REFUTED; and "The same ns family refutes, at the
  intended instance, `canonical_stable` … (iii) It also makes `VPSound`
  unsatisfiable."
* **the sanctioned repair, PROPOSED NOT EXECUTED (M02 "Minimal repair"):**
  conjoin `MovesT.NsFree V` into `bridgeTree`; then "exact squares (and every
  window-degenerate locus) fiber NO carried tree, so `bridgeCanonical`
  returns `none` there — they drain into the undecided envelope env(N)" —
  exactly (q-6)'s intended drainage — "flagged for sign-off per the
  axiom/statement policy". At HEAD the conjunct is NOT in
  `BridgeD3_treeCarrier.lean`. [After Unit C's repair the pin holds BY
  CONSTRUCTION of (†7) — no ns-marked tree is carried, so no fibering witness
  exists at window-degenerate loci. Until (NSF-KEY) retires, (H9)'s target
  statement covers the intended/pinned instantiation, NOT the HEAD wiring.]

**The two consumption channels (what M3 does and does not supply at K1 —
displayed so the a.e./exact distinction cannot blur again):**
* **(ch-1) K1's EXACT combinatorics** — the cylinder classification, the
  finite-level counts, Lemma 3.3's weight-preserving regrouping — consumes
  D-15 + the K1 kernels AT decided ns-free trees and is
  LABEL-SEMANTICS-BLIND: both sides are keyed by the trees' RECORDED verdict
  multisets; no statement on this channel reads the true type of any
  polynomial. M3 is not consumed here, so its separable-lift scope cannot
  injure the exact content.
* **(ch-2) the SEMANTIC tie** (recorded labels = true types) — where M3(a)
  enters (via Steps 11/12 → Step 17): consumed MASS-MEDIATED. Each counted
  box's true-σ locus is the box minus its nonseparable locus (M3(a) at
  separable scope, applicable AT THE (H9) PRICE — (NSF-INT) for the pin →
  corpus chain, (NSF-KEY) for the as-built keying), of full box mass by T-6
  (ns-null) — exactly what the Step-19 squeeze and Step 18b's density reading
  consume. No mandatory consumer reads a true type at an individual
  nonseparable lift.

**(CH-COV) — the channel-coverage closure audit [NEW at V5; round-4 finding
8: the former justification "the checks found none on the Step-17/18/18b/19
path" was a UNIVERSAL NON-CONSUMPTION CLAIM with no closure-complete trace —
the same defect class whose Σ = 1 instance was cured by (ROW-Σ). The claim is
DROPPED; the executed checks survive as EVIDENCE only.]** The obligation: a
DEPENDENCY-CLOSURE audit establishing that every mandatory consumption of
M3(a)'s conclusion on the Step-17/18/18b/19 path factors through (ch-1) or
(ch-2) — walked to closure (each consuming step's displayed proof line, its
invoked leaf statements, and THEIR hypotheses), not sampled. Executed at Unit
A (artifact L11), adjudicated by the r4 hostile pass as a CLOSURE-COMPLETE
trace. Outcome pricing, in advance: if the audit finds a consumer needing
all-lifts separability FROM M3 at boxes not definitionally ns-free — a
consumer OUTSIDE both channels — then contingency **(NS-ALL)** FIRES and is
priced as an explicit open lemma per §6, and this design returns for
re-adjudication. Until the audit is on file and clean, N2 carries "(CH-COV)
closure audit" in its BLOCKED-PENDING clause (§0.3's canonical line).

### 2.6 G9 — the falsifier-criterion display

§6's "every entry defined with value in [0, 1] (necessary for M1(a))" and the
"single failure — an entry outside [0, 1] … would have refuted M1(a)"
sentence are rescoped (display only): the [0,1] criterion is necessary for
M1(a) exactly at families (i)/(ii)/(iii) (the (a″) scope); the (O3) scaling
entries are checked against their displayed > 1 form; an out-of-[0,1] value
at a family-(i)–(iii) entry would have refuted M1(a). No scanned quantity
changes (the scan already keys entries by family).

### 2.7 C7 — M3(b)'s silent clause-4 consumption (leaf hygiene; ROOT already insulated)

The impact audit graded C7 INSULATED: ROOT's Step 17 REVISION-4 note + the
§3.2 D-11 [V] row already price the actual-pack correspondence as (H5), so
ROOT assumes what the leaf sentence hid. The LEAF sentence is still false as
written. **REPAIR (in-statement conditionality, verbatim):** M3(b)'s first
sentence becomes

> Under the clause-4 correspondence (OPEN — §5 clause 4 = OL-O12-2's data
> half; ROOT prices it as (H5)/(PACK)), M1/M2's identities attach to the
> ACTUAL tables' values; unconditionally, M1/M2 identify entries of a
> stipulated 𝔅_n member and the displayed (R-read) with masses of SEMANTIC
> strata (root valuations, reductions of rescales, Newton polygons, residual
> shapes) — and this clause ties those semantic strata to the classifier
> vocabulary:

with the rest of M3(b) (the GD/CU dictionary and its displayed
conditionality) byte-stable.

---

## 3. LAYER M2 (consumed at ROOT Step 18b): the (RE) true-scope repair, PRICED at the consumed member by the NEW (H5) member (PACK-iv)

### 3.1 The finding, restated precisely

M2 as displayed: "Assume (S1) and (S2) for the member. Then … the abstract
solved values ARE the real conditional densities" — quantified over ALL 𝔅_n
members. The verifier's counterexample: 𝔅_n admits members with ARBITRARY
allocation data α_e (rows can leave [0,1]) while (S1)/(S2) still hold; and
the proof's step "With M1(a) (each P(F) is the abstract mass entry at q₀)"
mis-cites M1(a), which the r3 rescoped to families (i)–(iii) — family-(iv)
verdict rows are excluded. The impact audit gestured at a "semantic
verdict-row allocation premise" as the missing hypothesis.

### 3.2 The decisive grammar facts (checked against the VERIFIED O-12 brief)

From `O12_phaseB_verifybrief_rev4.md` §2.3(iv) (verbatim, verified text):

> The verdict row of F at verdict σ is row_σ(F) := m(F) · Σ_{comp_F(σ⃗)=σ}
> ∏_i β_{μ_i}(σ_i)(q^{D_i}), a finite sum of products with coefficients 0 or
> 1 — no other scalars enter. … Booking adjustments (§2.4): under (O2) the
> table carries one further datum, the *allocation datum* α_e … and the
> aggregated verdict row becomes t_σ + α_e(σ)·q^{−E} …; under (O3) every exit
> row is multiplied by the scaling q^E/(q^E−1) of family (v).

and §1:

> the machine-checked degree-2 table = (O2) at n = 2; the sealed degree-3
> tables = (O3); the general-n engine = (O1).

Consequences: **(g-i)** in 𝔅_n's own grammar, family-(iv) verdict rows are
the CANONICAL 0/1-coefficient semantic assembly BY DEFINITION; **(g-ii)** the
arbitrary allocation datum α_e exists ONLY at the (O2) booking; **(g-iii)**
the (O2′) adjustment is the pinned re-feed leg κ₁·x (coefficient = κ₁
exactly, per the §2.4 display M2 already quotes), and the (O3) adjustment is
the deterministic family-(v) scaling — neither introduces free scalars;
**(g-iv)** the intended density-carrying instances are (O1) (general n) and
(O3) (sealed n = 3), never (O2) — D-11's M1′ already pins this, and M1′
moreover shows NO α-constraint could rescue M2 at (O2): the (O2) booking's
solved values differ from the true densities even with the semantic
α₂ = (0, q−1), because the booked event is not verdict-constant. So the
audit's gestured "semantic-allocation premise", read as a constraint on α,
would be BOTH too weak (fails at (O2) anyway) and unnecessary (no α exists at
re-entrant bookings). The sound repair is a BOOKING-PROFILE hypothesis.

### 3.3 REPAIRED THEOREM M2 (verbatim)

> **Theorem M2 (r4).** Let the member satisfy:
> **(RE) [re-entrant booking profile — a CONJUNCTION; the former
> "equivalently" is STRUCK (round-2 advisory 4): the displays establish only
> (O2) ⟹ carries-α, so no clause here is derived from another; (RE) states
> everything the proof uses, the same conjunctive genre as (PACK-iv)].**
> EVERY block e ∈ {2, …, n} of the member is booked (O1), (O2′), or (O3) —
> never (O2); AND the member carries NO allocation datum at any block; AND
> its family-(iv) verdict rows at every block are the canonical
> 0/1-coefficient assembly row_σ(F) = m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i
> β_{μ_i}(σ_i)(q^{D_i}), aggregated t_σ = Σ_F row_σ(F), with the only booking
> adjustments the (O2′) re-feed leg κ₁·x (coefficient pinned = κ₁) and the
> (O3) exit-row scaling q^{E}/(q^{E}−1). [Arbitrary-α members are EXCLUDED —
> they are exactly M1(a″)/M1′'s exclusion, and for them only O-12's pole/zero
> theorem speaks; the (O2) member is a gate object, not a density carrier
> (M1′).]
> Assume further (S1) and (S2) for the member. Then for every prime power
> q₀ = p^δ and every block e: β_e(σ)(q₀) = P(splitting type = σ | the block-e
> state law at q₀) for all σ; and the top-layer assembly (root read +
> entrance weights) identifies the solved final densities with the true
> unconditional splitting-type densities of Haar-random monic degree-n f over
> O. [MONIC scope; the PROJECTIVE reading additionally conditional on (S3).
> The identified top object is the DISPLAYED root read (R-read); that a
> concrete pack's rows equal the member's is clause-4 content ((H5)), NOT
> claimed here.]

**REPAIRED PROOF STEP (verbatim; replaces "With M1(a) (each P(F) is the
abstract mass entry at q₀), the semantic one-step identity is therefore").**

> By (RE) and the verified grammar display (O-12 §2.3(iv), quoted in §0), the
> member's exit/verdict rows at block e are the canonical assembly: each exit
> stratum F contributes m(F) times the 0/1 comp_F-selected products of
> β-legs, with no other scalars. By M1(a) (families (ii)/(iii) — in scope
> after the r3 rescope), each m(F)(q₀) = P(F | C_e). By (S1)+(S2),
> P(type σ | F) = Σ_{comp_F(σ⃗)=σ} ∏_i β*_{μ_i}(σ_i at q₀^{D_i}), and by the
> induction hypothesis (every lower block is also re-entrant-booked under
> (RE)) each β*_{μ_i}(· at q₀^{D_i}) = β_{μ_i}(·)(q₀^{D_i}). Hence the
> member's abstract exit row equals the true exit row: s_member(q₀) =
> s_true(q₀), and the semantic one-step identity is the member's balance
> equation:

with the three displayed booking legs ((O1)/(O2′)/(O3)) and the
uniqueness-pivot close byte-stable. The r3 note that exhaustiveness consumes
M1(b)/(d) is re-pointed to (b)/(b-PF)/(b-EX)/(LOOP-∞) per §2.4 — (b-EX) is an
r4 proof obligation, and M2's exhaustiveness note inherits its conditionality
until it lands.

**At the CONSUMED instance: the definitional discharge is WITHDRAWN (round-1
finding 1) — (RE)+row-form at the consumed member is (PACK-iv), a NEW [M]
member of (H5); §3.5 is the PRIMARY route.** The withdrawal reasons, recorded
so the withdrawal is durable:
* the O-12 §1 sentence names the project's concrete tables' INTENDED
  bookings, but O-12's own scope declaration (§1, verbatim) makes the
  identification of the COMPLETE sealed degree-3 tables with an (O3) member
  "an interface assumption declared outside this proof (recorded as the
  labeled open item OL-O12-2)", and the general-n identification likewise
  ("declared outside this proof, NOT proved here and NOT part of the
  claim"). So the quoted sentence cannot pin the PER-BLOCK BOOKING PROFILE
  of the member ROOT actually consumes: that member is reached only through
  (H5), and its booking profile is exactly (H5)-class content — hypothesis,
  not verified text;
* absence-of-α does not prove the profile: the §2.3(iv)/§2.4 displays
  establish that the allocation datum exists only under (O2) — i.e.
  (O2) ⟹ carries α — NOT the converse; and (RE) needs more than "no α":
  every block booked (O1)/(O2′)/(O3) AND the family-(iv) rows equal to the
  canonical 0/1-coefficient assembly with only the displayed adjustments — a
  per-block booking + row-form profile that no quoted display pins for the
  consumed member;
* M1′'s "instance pin" is a sentence of D-11's own repaired chain — an
  assertion inside the artifact under repair, not independent evidence of
  pack-to-member conformance.
The grammar facts (g-i)–(g-iv) remain correct AND load-bearing — but in two
demoted roles only: as the derivation "(RE)-member ⟹ canonical verdict rows"
INSIDE Theorem M2 (r4), and as (PACK-iv)'s RETIREMENT ROUTE (below) — never
as a discharge at the consumed instance. The concrete pack's conformance to
the member remains (H5)'s correspondence clause, unchanged. ROOT r11 displays
the PRICE at Step 18b (§7, edit E3) and adds (PACK-iv) to the (H5) row as a
NEW hypothesis member (edit E4 — worded as an ADDITION to the row-law roster,
never a clarification).

**(PACK-iv)'s RETIREMENT ROUTE — what would discharge it later.** (PACK-iv)
retires when the booking profile and row forms of a consumed member become
VERIFIED DATA rather than hypothesis:
* (route-a), n = 3: the OL-O12-2 transcription-and-correspondence pass (D-11
  §5 clause 4's data half), EXTENDED BY ONE NAMED DUTY — per sealed row,
  verify the block's booking against the (O3) forms and the row against
  §2.3(iv)'s canonical assembly + the displayed (O3) scaling. (Finite data
  comparison; naming the duty prevents the pass from silently skipping the
  booking-profile half.)
* (route-b), general n: the O-14d instance population constructing the member
  IN the (O1) booking — the profile then holds BY CONSTRUCTION and is
  checkable at population time.
On either route's verified completion at a consumed instance, (g-i)–(g-iv)
convert "verified re-entrant profile, no α" into the canonical row-form
clause BY the displayed §2.3(iv) definition, and (PACK-iv) retires into the
executed correspondence at that instance.

**Proof obligations for M2 r4:** (RE)-grammar cite displayed (quote §2.3(iv)
into the leaf's §0 consumed-inputs list); the repaired proof step above;
everything else in M2's proof survives verbatim (the (O2′)/(O3) legs, the
Theorem 1(3) fold, the pivot, the root layer).

### 3.4 G5 — Lemma M2.0's address induction (loop-extended addresses)

**Defect.** Addresses recorded only (hand-off stratum, child slot) pairs, but
a child is born after L ≥ 0 within-block loop steps then exit through F; the
induction step "{node a reached} = {node a′ reached} ∩ {x_{a′} ∈ F}" is false
when loops precede the hand-off (reaching the child is a countable union over
loop words).

**REPAIR (structure, to be written out in r4 at the displayed level of the
current step 3).** (i) Addresses become a = ((w_1, F_1, i_1), …,
(w_k, F_k, i_k)) with w_j a finite WORD over block-level j's loop strata
(executed before the j-th hand-off) — still countable. (ii) The ≪-transport
induction runs over ONE LETTER at a time, with two letter kinds: LOOP letters
— the pushforward of the normalized restriction of Haar-C_e to a loop stratum
s under the loop step map IS Haar-C_e: verbatim L2+L3 ("conditioned on the
stratum, ĥ is AGAIN the state law"), PROVED, no seam; HAND-OFF letters —
(S1-m), as now. The kernel-null-set step is unchanged in form at both letter
kinds. (iii) Step 2's reduction sentence gains "after executing its finite
loop word" at the node-birth reading.

**The r4 OBLIGATION LIST for the rewritten Lemma M2.0 (round-1 finding 5 —
the facts the loop-extension must PROVE, not assert; §4's N4 rests on exactly
these):**
* **(O-1) [the child-reached identity — the disjoint/countable-union
  display].** For a node a′ and a child slot (F, i): {child (F, i) of a′
  reached} = ⨆_w ({a′ reached} ∩ {the within-block trajectory at a′ executes
  the finite loop word w, then lands in F}) — a COUNTABLE union, PAIRWISE
  DISJOINT over the words w over block-μ(a′)'s loop alphabet ({loop-0} ∪
  {loop-c}_{c≠0}). Route: the words w·F are stopping words in the
  generalized sense (proper prefixes all-loop, final letter the exit stratum
  F); pairwise disjointness at the first differing position is (b-PF) —
  (b)'s one-step clause covers the full mixed loop alphabet; countability:
  finite words over a finite-per-length alphabet; exhaustion of {child
  reached} minus the (O-2) null set: under (DET) the trajectory is a
  deterministic map sequence, so reaching the child MEANS some finite loop
  history precedes the hand-off. This identity REPLACES the rev-3 false
  one-letter induction equation.
* **(O-2) [the infinite pre-hand-off loop path].** At every node a′ with
  P(a′ reached) > 0: P(the within-block trajectory at a′ never exits | a′
  reached) = 0. Route: the eternal-loop set N_μ ⊆ C_μ is Haar-null (M1(c)'s
  per-block clause, over ALL loop strata); the reached-conditioned law of
  x_{a′} is ≪ Haar-C_μ (the transport induction); null pulls back to null.
* **(O-3) [measurability of the iterated restrictions and maps].** Every
  loop letter's step map (g ↦ ĥ = h(c̃ + y) on its stratum) is measurable;
  finite compositions along a word are measurable; every event in
  (O-1)/(O-2) is a composed preimage of displayed strata — the L2/L3/L6
  measurability layer of §1, applied finitely often per word; the r4 writes
  the composition sentence once, at the loop-extended addresses.
* **(O-4) [preservation of normalized conditional laws after arbitrary loop
  words].** Under the CANONICAL block law, conditioned on executing the loop
  word w, the post-w state law IS Haar-C_{μ(a′)} exactly (|w|-fold L2+L3,
  each letter's normalized stratum restriction pushing forward TO the state
  law); under a reached-conditioned law that is merely ≪ Haar-C_{μ(a′)},
  absolute continuity is preserved letter-by-letter (the kernel-null-set
  step with (S1-m) replaced by the PROVED L2+L3 statement). This is the loop
  case of the two-letter transport and the exact reason the billing does not
  widen.
* **(O-5) [where per-block a.s. exit is consumed — the corrected
  exit-partition display (round-2 finding 3: the earlier union omitted the
  TERMINATING exits, strata with NO child slot)].** At every node a′ (block
  μ := μ(a′)), up to the (O-2) null set, the within-block trajectory
  executes a finite loop word w and then lands in exactly ONE exit stratum F
  of block μ — F ranging over ALL displayed exit strata of the block: the
  HAND-OFF strata (children born in blocks μ_i < μ; child slots (F, i)) AND
  the TERMINATING exits (verdict/leaf rows with no child slot). The
  countable disjoint decomposition consumed by the accounting is

      {a′ reached} = ⨆_w ⨆_{F ∈ Exits(μ)} ({a′ reached} ∩ {w then F})
                     ⊔ ({a′ reached} ∩ {the trajectory never exits}),

  the last member NULL by (O-2). Disjointness: across (w, F) the words w·F
  are stopping words in (O-1)'s generalized sense — (b-PF) at the first
  differing position, (b)'s one-step clause across distinct F at equal w;
  countability as in (O-1). The induction step consumes EXACTLY this
  corrected form, in three displayed uses: (i) the child-reached identity
  (O-1) is the sub-union at the HAND-OFF pairs — for each hand-off F, the
  event ⨆_w ({a′ reached} ∩ {w then F}) IS {child (F, i) of a′ reached} for
  EVERY slot i of F (the factor-children of one exit are simultaneous, not
  alternatives — ONE event per F, shared by its slots); (ii) the
  TERMINATING-exit members are consumed as the per-node terminal/leaf masses
  — they spawn no child and no further induction step; (iii) the null member
  is discarded — this is where M1(c)'s per-block bound, transported by ≪, is
  spent. The r4 displays this consumption line, in exactly this three-part
  form, at the induction step.
* **(O-GLOB) [the GLOBAL multi-block a.s.-termination obligation — RESTATED
  AT V5; round-4 finding 5 refuted the prior route on two points: (α) strict
  descent bounds branch DEPTH but not node count — a branching bound was
  missing; (β) the "no duplication: one event per parent exit" convention is
  WRONG for the null-set union — sibling slots share their parent exit event
  but carry DISTINCT future nontermination events at distinct addresses,
  which cannot be replaced by one event per parent exit. Both fixed in the
  route below; the withdrawn convention is recorded here so it cannot
  return.]** STATEMENT: for Haar-a.e. input, every realized node of the
  block tree is exited after finitely many within-block steps, the realized
  block tree has finitely many nodes, and the full multi-block trajectory
  terminates. ROUTE (the r4 write-out = this four-part induction, displayed):
  * **(G-a) [the address set is countable — with the branching input made
    explicit].** Addresses a = ((w_1, F_1, i_1), …, (w_k, F_k, i_k)); depth
    k < n by STRICT BLOCK DESCENT (children born in blocks μ_i < μ, block
    sizes in {1, …, n}); per node the alphabet is countable — finitely many
    loop letters per position and finite words w; countably many exit strata
    F (patterns finite, polygon cells countable); FINITELY MANY SLOTS i per
    F (the slot list of each hand-off stratum is finite BY THE DISPLAYED
    GRAMMAR: every family-(iv) row is "a finite sum of products" ∏_i over
    F's slots — O-12 §2.3(iv)). Countable unions of countable sets along
    depth < n: the address set 𝒜 is countable. [Descent alone bounds depth,
    never node count — the finite-slot display is the branching bound the
    prior route omitted.]
  * **(G-b) [root-to-leaf transport — induction on address length,
    conditional on reached].** For every a ∈ 𝒜 with P(R_a) > 0 (R_a := {a
    reached}): the R_a-conditioned law of the node state x_a is ≪
    Haar-C_{μ(a)}. Base: the root nodes — the top-layer read spawns finitely
    many top blocks with entrance laws delivered at the root seam ((S1-m),
    Lemma M2.0's existing step 2). Step a′ → a = a′·(w, F, i):
    R_a = R_{a′} ∩ {w then F at a′} ((O-1)) — the SAME conditioning event
    for EVERY slot i of F — and the child-state law is the hand-off letter
    applied after the |w| loop letters ((O-4): ≪ preserved
    letter-by-letter). [Sibling slots CONDITION ON ONE SHARED EVENT; nothing
    is multiplied and no independence is claimed.]
  * **(G-c) [the null union runs PER ADDRESS].** N_a := R_a ∩ {the
    within-block trajectory at a never exits} — the node-a nontermination
    event. P(N_a) = 0 for every a ∈ 𝒜: trivially when P(R_a) = 0 (N_a ⊆
    R_a); else by (G-b) + (O-2) (the eternal-loop set is Haar-null per
    M1(c); null pulls back through ≪). The global exceptional set is
    𝒩 := ⋃_{a ∈ 𝒜} N_a — countable by (G-a), each member null, hence NULL.
    [Corrected per round-4 finding 5: the union index is the ADDRESS SET —
    sibling slots contribute DISTINCT N_a's, every one included; "one event
    per parent exit" applies to the (O-5) MASS decomposition of R_{a′}
    (where sibling slots genuinely share one event per (w, F)), NEVER to
    this union. The two aggregations have different index sets, and the
    write-out displays both where each is taken.]
  * **(G-d) [off 𝒩 the realized tree is finite — strong induction on block
    size, pointwise].** Fix g ∉ 𝒩. At any node a that g realizes: g ∉ N_a,
    so the within-block trajectory at a exits after finitely many steps
    through exactly one realized exit F ((O-5), read pointwise). If F is a
    terminating exit, a is a leaf of g's realized tree. If F is a hand-off,
    it spawns the finitely many slot-children of F ((G-a)'s finite-slot
    display), each of block size < μ(a); by strong induction on block size,
    each child's realized subtree is finite; hence a's realized subtree is
    finite. Applied at the finitely many root nodes: g's realized tree is
    finite and the full trajectory terminates (finitely many nodes, each
    exited after finitely many steps). ∎-shape.

  (O-GLOB) consumes: (O-1)–(O-5), M1(c), the displayed finite-slot grammar
  (O-12 §2.3(iv)), countable additivity, AND the root-finiteness premise —
  the top-layer read spawns FINITELY many top blocks with entrance laws
  delivered at the root seam ((S1-m), Lemma M2.0's existing step 2) —
  consumed at (G-b)'s base and at (G-d)'s final application (round-5
  finding 6: previously used but uninventoried) — NOTHING of M2.

**Billing.** (O-4)'s loop legs consume only the PROVED L2/L3; (O-1)/(O-3) are
structural; (O-2)/(O-5) consume M1(c) + the ≪-induction; (O-GLOB) as
displayed above. "Billing unchanged" ((S1-m)+(DET)) is the DESIGN-LEVEL CLAIM
the r4 proof must bear out, not an established fact. The honest-widening
paragraph ((S1-m+) under a stochastic hand-off reading) survives verbatim in
the leaf. Until the (O-1)–(O-5) AND (O-GLOB) write-outs land AND pass the r4
hostile pass, Lemma M2.0 stands REPAIR-DESIGNED, not repaired (§4 N4:
BLOCKED-PENDING).

### 3.5 (PACK-iv) — the PRIMARY route's [M] member

The priced form is the following NEW (H5) clause, stated per the
PACK-i/ii/iii genre AT the 𝔅_n member. E4 presents it as a NEW HYPOTHESIS
MEMBER — an enlargement of (H5)'s displayed row-law roster, exactly the
mechanism by which PACK-i/ii/iii entered at ROOT REVISION 7 — NEVER as a
clarification of existing content:

> **(PACK-iv) sem_alloc — semantic verdict-row form at the intended member.**
> At every block e of the intended 𝔅_n instantiation, the booking is
> re-entrant ((O1)/(O2′)/(O3)) and the family-(iv) source/verdict rows are
> the canonical semantic assembly: every verdict-row entry equals
> Σ_{F exit} m(F)·Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q^{D_i}) — plus, at
> (O2′), the displayed κ₁ re-feed leg and, at (O3), the displayed family-(v)
> exit scaling, and nothing else — with m(F) the member's family-(ii)/(iii)
> mass entry and the β's its family-(vi) legs; the member carries no
> allocation adjustment beyond these. [The premise D-11 r4's Theorem M2
> names as (RE); (S1)/(S2) do NOT imply it (owed-pass C6). CONSUMED AT: Step
> 18b (direct — Theorem M2's (RE) instantiation) AND every application of
> (ROW-Σ) at the consumed member (the untraced-cover channel) — the
> authoritative attribution display is §4.2, and every other display syncs
> to it (round-4 finding 1; no conditional language: (ROW-Σ) HAS fired).
> Step 18's K2/K3 glue consumes PACK-i/ii/iii, and Step 17's M1 excludes
> family (iv) in-statement ((a″)).]

**One-home argument (why (H5) enlargement, not a new row):** (H5) is BY
CONSTRUCTION "the actual-pack correspondence PLUS the pack row-laws … stated
AT THE 𝔅_n ROWS" (REVISION-7 enlargement, finding VC7-2); (PACK-iv) is a
row-law at the 𝔅_n rows, same owners (D-11/O-12 with the O-14d pack
construction), same consumption chain (Steps 17 → 18/18b), same
borderline-[M]/[T]-kept-[M] disposition (a finite per-n row-form comparison,
RESUM-n3's transcription its executed n = 3 instance). A separate row would
split the 𝔅_n row-law content across two homes against the VC7-2 precedent.

**[M] accounting (exact).** (PACK-iv) adds a MEMBER to (H5), not a row;
(H5)'s displayed row-law roster grows THREE → FOUR (PACK-i/ii/iii/iv, plus
the correspondence clause it always carried). The §3.1 ROW count after r11 is
**TWELVE**: (H8) (§5.1) AND (H9) = (NSF) (§2.5) are the two new rows — ten →
twelve (round-4 finding 9: this arithmetic is confirmed internally
consistent). Named retirement routes displayed on each: (PACK-iv) at §3.3's
(route-a)/(route-b); (H8) at O-11 §8 charge (vi); (NSF-INT) at §2.5 (the r4
leaf proof — its ONLY route); (NSF-KEY) at §2.5 (NSF-KEY-RET)/Unit C.

---

## 4. THE NEED CHECK (decisive): what Steps 17/18b actually need, met need-by-need

### 4.1 The consumed lines and the need table

**The consumed lines, quoted from ROOT REVISION 9.** Step 17 Delivers: "the
pack-side mass laws + true row labels that Step 18's K1/K2 consume; D-9k's
escape input at the pack; the (r1) uniqueness pivot Step 18b re-uses." Step
18 consumes (K2 leg): "K2 ← O-12 at 𝔅_n + D-11 PACK SIDE (= Step 17's
tranche, never M2) + the (PACK) correspondence-plus-row-laws … PACK-i/ii at
THIS K2 evaluation glue …; (PACK-iii) at K3". Step 18b Statement: "(D-11 M2)
for every type τ: α(n, τ; p) — the Haar density of clause (0) — equals the
σ-graded tree series of T_can; equivalently, the solved values are the real
conditional densities"; its proof line names "(S1) … ← Step 14 …; (S2) = the
O-11 composition datum ← Step 18. (r1) is the uniqueness pivot (Step 17)";
Delivers: "the α = series identification; with Step 18, the α(n,τ;p) = R_τ(p)
evaluation clause of (R)." Step 19 consumes: "Step 18 delivers series = R_τ
(O-11); Step 18b delivers α = series (D-11 M2); TOGETHER they deliver
α = R_τ — neither alone does"; plus "the pole-free specialization at every
prime power (Steps 4 + 5 + 17 …)".

| # | need | met by | verdict |
|---|---|---|---|
| N1 | Step 18 K1/K2 ← "pack-side mass laws": per-row stratum masses at the 𝔅_n member + row disjointness (incl. the (O3) resummed rows) | repaired M1(a) families (i)–(iii) (conditional-on-C_e, formulas unchanged) + M1(d) (one-step strata Σ = 1 — its honest scope) + (b) with (b-PF) argued + **(b-EX) an r4 PROOF OBLIGATION** (route §2.4) + (LOOP-∞) + **(ROW-Σ) an r4 THEOREM-OBLIGATION** (statement, route, consumers: §4.2 — the belt-and-braces cover for the non-exhaustive (†18) trace); the K2 glue laws at the CONCRETE pack stay (PACK-i/ii); K3's stays (PACK-iii) | **BLOCKED-PENDING ((b-EX) + (ROW-Σ) proofs)** |
| N2 | Step 18 K1 ← "true row labels" (M3 leg, via Steps 11/12) | repaired M3(a) at separable-lift scope + the [M] row **(H9) = (NSF)** (§2.5): (NSF-INT) prices the pin → predicate → corpus implication chain (quotes (q-1)–(q-6) = context) and (NSF-KEY) prices as-built keying conformance — KNOWN FALSE AT HEAD (M02 §2's exact-square poison); retirement: (NSF-INT) by r4 leaf proof ONLY; (NSF-KEY) by Unit C per (NSF-KEY-RET); channels (ch-1)/(ch-2) + the **(CH-COV) closure audit** (§2.5); label attachment to ACTUAL tables rides (H5) | **BLOCKED-PENDING ((NSF-KEY) execution — known false at HEAD until the gated definition change lands — plus the (CH-COV) closure audit)** |
| N3 | Step 18b ← "the (r1) uniqueness pivot" | Corollary D margins/pivot — untouched by every finding | **MET** |
| N4 | Step 17's termination delivery ("a.s. termination from the (r1) margins"; D-9k's escape input) | M1(c) per-visit margins at (O1)/(O3) + per-block a.s. exit, unconditional (pass-confirmed, byte-stable); multi-block a.s. termination = Lemma M2.0 REPAIR-DESIGNED per §3.4 with the LOCAL obligations **(O-1)–(O-5)** enumerated and routed PLUS the GLOBAL obligation **(O-GLOB)** at its v5 route ((G-a)–(G-d): countable addresses with the finite-slot branching bound; root-to-leaf ≪ transport; per-ADDRESS null union; pointwise strong induction on block size); billing (S1-m)+(DET) = the design-level claim the r4 must bear out; Step-17 display line rescoped to this split (edit E1) | **BLOCKED-PENDING ((O-1)–(O-5) + (O-GLOB) global proof)** |
| N5 | Step 18b → Step 19: α = series at the consumed instance | repaired M2 (r4) at its (RE) scope — a THEOREM about (RE) members; at the CONSUMED member, (RE)+row-form = **(PACK-iv)**, the NEW (H5) member (§3.5, PRIMARY); (S1) ← Step 14, (S2) ← Step 18, pivot ← Step 17; concrete-pack attachment = (H5)'s correspondence clause | **MET AT PRICE ((PACK-iv), NEW [M] member)** |
| N6 | Step 19 ← Step 17's pole-free leg | the (r1)/(r2) margins reread — untouched | **MET** |
| N7 | Step 19's Σ_τ R_τ = 1 | rides α = R_τ at every p (N5) + Step 1 — hence INHERITS N5's (PACK-iv) price; conditionality otherwise unchanged (Step 1 + interpolation, ROOT REVISION-3 finding B3) | **MET AT PRICE (inherited from N5)** |
| N8 | Step 18 K1's Lemma-3.3 shallow-cut regrouping ← CUT-WD | **(H8) = (K-CUT)**, the NEW [M] row (§5.1: exactly-one shallow decomposition, exhaustive-exclusive read ownership, weight-preserving μ(fiber T) = W(Ŝ)·∏_i weight(D_i) — M04 Lemma 3.3's hypothesis); named retirement route = O-11 §8 charge (vi) | **MET AT PRICE ((H8), NEW [M] row)** |

### 4.2 (ROW-Σ) — the ONE authoritative display (statement, route, consumers, graph)

[Round-4 finding 1: the prior layers displayed (ROW-Σ) inconsistently —
"required obligation" at N1, "if it fires" at E4, absent from Step 18's graph
and from the canonical BLOCKED line. THIS SUBSECTION is now the single home;
every other mention (N1, E1, E4, L10, the status lines) POINTS here and
restates nothing. (ROW-Σ) HAS FIRED: it is an obligation Unit A must prove,
and N1 is BLOCKED-PENDING on it. No conditional language anywhere.]

> **(ROW-Σ) [r4 THEOREM-OBLIGATION — proved at Unit A (L10), Step 17's
> layer].** For every 𝔅_n member satisfying (PACK-iv), every prime power
> q₀ ≥ 2, and every block e (with E := e(e+1)/2 the block's own exponent):
> **(a) [solved-entry normalization]** Σ_σ β_e(σ)(q₀) = 1;
> **(b) [per-booking verdict-row totals — three DIFFERENT values]** for
> e ∈ {2, …, n}, the aggregated family-(iv) verdict-row total
> S_e := Σ_σ row_σ(q₀) equals the block's booked termination margin
> (Corollary D's Φ):
> at (O1): S_e = 1 − κ₀ − κ₁ = 1 − q₀^{1−E} = Φ^{(O1)};
> at (O2′): S_e = 1 − κ₀ = 1 − q₀^{−E} = Φ^{(O2′)};
> at (O3): S_e = (1 − κ₀ − κ₁)/(1 − κ₀) = 1 − (q₀−1)/(q₀^E − 1) = Φ^{(O3)}.
> In particular NO booking's displayed row total is 1; the object normalized
> to 1 is the SOLVED vector (a). [Honesty over elegance (round-4 finding 2):
> the prior single-total display ("the row total is 1 − κ₀ − κ₁") is true
> ONLY at (O1); the uniform restatement is S_e = Φ^{(booking)}.]

**Proof route (the r4 write-out; induction on e, uniform in q₀ — so the
induction hypothesis applies at the child pools q₀^{D_i}).**

Base e = 1: β_1 = 1 (the displayed base of O-12's engine: a single verdict,
trivial solve).

Step, at block e of a (PACK-iv) member. Write t_σ := Σ_F m(F)·
Σ_{comp_F(σ⃗)=σ} ∏_i β_{μ_i}(σ_i)(q₀^{D_i}) — the canonical UNADJUSTED
assembly over the block's pattern/polygon exit strata F. [In every re-entrant
booking t ranges over exactly these strata: the recentering strata are NEVER
inside t — loop-side at (O1) and (O3) (inside E_rec), the separately
displayed re-feed leg at (O2′). This is where round-4 finding 2 bit: the
prior route treated the DISPLAYED row as t_σ in all three bookings.]

1. **[telescoping]** Σ_σ t_σ = Σ_F m(F) · ∏_i [Σ_{σ_i} β_{μ_i}(σ_i)(q₀^{D_i})]
   — summing the comp_F fibers over σ recovers the full tuple sum (the 0/1
   comp-sum telescopes over the finite verdict set), which factors as the
   product of the per-slot sums (finite slot list, O-12 §2.3(iv)); each slot
   sum = 1 by the induction hypothesis (μ_i < e, at pool q₀^{D_i}). So
   T := Σ_σ t_σ = Σ_F m(F).
2. **[mass input]** By M1(a)(ii)/(iii) (repaired, §2.1), m(F)(q₀) =
   P(F | C_e); by M1(d) (the one-step strata sum to 1) minus the two loop
   masses: **T = 1 − κ₀ − κ₁**.
3. **[the three booking cases, separated]**
   * **(O1) [plain].** Displayed row: row_σ = t_σ. Balance:
     x_σ = (κ₀+κ₁)·x_σ + t_σ ⟹ (1−κ₀−κ₁)·x_σ = t_σ.
     Row total: **S_e = T = 1 − κ₀ − κ₁ = Φ^{(O1)}**.
   * **(O2′) [the κ₁·x re-feed — the affine fixed point, solved for the
     totals].** Displayed row: row_σ = t_σ + κ₁·x_σ (the re-feed leg books
     the recentering strata; the coefficient is pinned = κ₁). Balance:
     x_σ = κ₀·x_σ + row_σ. Sum both displays over σ (X := Σ_σ x_σ):
     the balance gives X = κ₀·X + S_e, i.e. S_e = (1−κ₀)·X; the row display
     gives S_e = T + κ₁·X. Equate: (1−κ₀)·X = T + κ₁·X ⟹ (1−κ₀−κ₁)·X = T =
     1−κ₀−κ₁ ⟹ X = 1, and **S_e = T + κ₁ = 1 − κ₀ = Φ^{(O2′)}**. (The
     fixed-point solve is legitimate: 1−κ₀−κ₁ = 1−q₀^{1−E} ≠ 0 at every
     q₀ ≥ 2 — Corollary D's pivot; per-σ this is exactly O-12 Theorem
     2(vii)'s display β_e(σ) = u^{−1}·t_σ, u = 1−q^{1−E}, "NOT a division of
     a row containing β_e".)
   * **(O3) [the exit-row scaling — how the factor enters].** Displayed row:
     row_σ = q₀^E/(q₀^E−1) · t_σ = t_σ/(1−κ₀) (the family-(v) scaling IS the
     loop-0 resummation Σ_{L≥0} κ₀^L; each exit row books
     {(loop-0)^L ∘ F : L ≥ 0}); the booked kernel is the resummed
     E_rec with value κ₁/(1−κ₀). Balance: x_σ = (κ₁/(1−κ₀))·x_σ +
     t_σ/(1−κ₀); multiply by (1−κ₀): (1−κ₀)·x_σ = κ₁·x_σ + t_σ ⟹
     (1−κ₀−κ₁)·x_σ = t_σ. Row total: **S_e = T/(1−κ₀) = (1−κ₀−κ₁)/(1−κ₀) =
     1 − (q₀−1)/(q₀^E−1) = Φ^{(O3)}**.
4. **[close]** In all three cases the balance reduces to the SAME solve
   (1−κ₀−κ₁)·x_σ = t_σ (O-12 Theorem 1(3), verbatim: "their balance
   equations are all algebraically (1 − κ₀ − κ₁)x = s"), so
   Σ_σ β_e(σ)(q₀) = T/(1−κ₀−κ₁) = 1 — clause (a); and the three S_e values
   are clause (b). Cross-check, displayed: in each booking
   S_e = (1 − booked kernel)·X = Φ·1 = Φ — the row total IS the termination
   margin, per booking. ∎-shape (the r4 transcribes this with the leaf's
   notation).

**What (ROW-Σ) consumes:** (PACK-iv) — the quantifier's scope (the member's
booking + row-form profile); M1(a)(ii)/(iii) + M1(d) (repaired, §2); the
displayed grammar (finite slot lists, 0/1 comp-selection — O-12 §2.3(iv));
O-12 Theorem 1(3)/2(vii) + Corollary D (pivot ≠ 0). NOTHING from Steps
18/18b — M2-free, hence NON-CIRCULAR wherever it is applied at Steps 17/18.

**Consumers (the authoritative attribution).**
* Step 17 DELIVERS (ROW-Σ) in its tranche (E1 records it as a PROVED lemma —
  Unit B executes only after the r4 pass accepts the write-out).
* Step 18: its TRACED consumption lines consume neither (PACK-iv) nor any
  member-row total — the (†18) trace below. The trace is NON-EXHAUSTIVE, and
  (ROW-Σ) is exactly the PROVED COVER for it: any member-row-normalization
  input inside Step 17/18's tranche that the trace missed is covered by
  (ROW-Σ), and THROUGH it consumes (PACK-iv). This cover set is NOT claimed
  empty (that claim was round-3 finding 3's defect; it is dropped).
* Step 18b consumes (PACK-iv) DIRECTLY (Theorem M2's (RE) instantiation).

**The dependency graph (one display; round-4 finding 1).**

    Step 17 ≺ Step 18 ≺ Step 18b        (order intact)
    (ROW-Σ): proved at 17's layer; hypotheses {(PACK-iv), M1(a)(ii)/(iii),
             M1(d), O-12 solve/Corollary D}; no M2 content.
    (PACK-iv) (hypothesis-class, (H5) member — no step-dependencies):
             enters at 18b (direct, traced) AND at every (ROW-Σ)
             application site (untraced cover, possibly within 17/18).
    No 18b content flows into 17/18. ACYCLIC.

### 4.3 (†18) The Σ = 1 trace — a TRACE, NON-EXHAUSTIVE (supporting context only)

[Round-3 finding 3, accepted: the K1 row omits Step 17/D-11 M1/M3 inputs; the
Theorem-4 row leaves Lemmas 3.1/3.2, Bekić, `blockSolve`, `Rsh`, `rsh_interp`
hypotheses untraced; several cells are excerpts with ellipses — the table
cannot support a universal non-consumption conclusion and NO SUCH CONCLUSION
IS DRAWN FROM IT. The load-bearing cover is (ROW-Σ), §4.2.] Background: the
round-1 N1 row claimed Step 17 delivers "member-row Σ = 1 through the
canonical grammar + family-(vi) aggregates" — WITHDRAWN; M1(d)'s theorem is
Σ = 1 over the ONE-STEP STRATA only, and member verdict rows are family (iv),
excluded from M1(a) by (a″) (verbatim: "NOT claimed by (a)/(a′): family-(iv)
verdict rows under ARBITRARY allocation data α_e … families (vi)/(vii) — the
β-legs and solved entries carry no per-entry mass identity").

| consumer | ROOT REVISION 9's displayed consumption/proof line (verbatim) | the invoked leaf statement — operative clause (verbatim) | row-total content found |
|---|---|---|---|
| **K1** (Step 18) | "K1 ← O-10 (guarded) + (I-τ)→GD [the (I-τ)/K-LOC interface = §3.1 (H7) …] + CU leaf labels [which carry the terminal-seam (H6) content and (FRESH) — the A-5 route leg]" | M04 §5.5 (K1): "each complete finite realizable canonical tree's fiber mass factors as the grammar weight of its derivation, with outcome weights the MEASURED one-step conditional masses (`M.rowVal`, J, ι/W) at the composed pools, and the type-σ corpus decomposes along shallow shapes as in Lemma 3.3 with W(Ŝ)(p) the measured shallow-shape mass"; Lemma 3.3's hypothesis: "a WEIGHT-PRESERVING BIJECTION … under which μ(fiber T) = W(Ŝ)·∏_i weight(D_i)", proof "Regroup along the bijection; … factor (Tonelli in [0,∞])"; the cut hypothesis = (H8) (§5.1) | **NONE.** A product/regrouping law: every sum is over derivations or shapes in [0,∞] (Tonelli); no sum over σ; no total set to 1 |
| **K2** (Step 18) | "K2 ← O-12 at 𝔅_n + D-11 PACK SIDE (= Step 17's tranche, never M2) + the **(PACK)** correspondence-plus-row-laws … (PACK-i)/(PACK-ii) at THIS K2 evaluation glue (the Rsh → Rval conversion and the [0,1] bound behind ENNReal.ofReal)" | M04 §5.5 (K2): "at every consumed pool q₀ = p^δ …, the active one-step matrix A(q₀) satisfies A(q₀)^k·𝟙 → 0". Its displayed discharge, O-11 rev 3 §3.3: "**O-12 Theorem 1 + Corollary D** …: every block kernel substochastic with positive termination margin at every prime power q₀ ≥ 2 (margins ≥ 3/4, 7/8, 6/7 …), hence ρ(A) < 1 and det(I−A) ≠ 0; plus D-6 …". O-12 Theorem 4's note: "At 𝔅_n the hypothesis holds … (Corollary D margins; **the row 'sum' is the scalar kernel value**)" | **the only row-sum object is the KERNEL row sum** — the scalar loop mass, bounded AWAY from 1 (SUB-stochasticity — the opposite of a Σ = 1 law); (PACK-ii) r_bdd is a PER-ENTRY [0,1] bound; no Σ_σ anywhere |
| **K3** (Step 18; for completeness) | "K3 = [1v]-FULL value correctness ASSEMBLED from T-7s + O-9's census + O-8b (arbitrary-DVR), with **(PACK-iii) wsh_ok** the membership input to K3's evaluation ring-hom evalAt (with D-6)" | M04 §5.5 (K3): "the numeric grammar weights equal the evaluations at the pools of the symbolic ℚ(q) entries K_e, b^{term}, J, W_Ŝ …"; O-12 (r2): "every g ∈ E(e) is defined at q₀" | **NONE.** Value-correctness + definedness; no totals |
| **K4** (Step 18) | "K4 ← Dfloor/D-15/CU mass semantics" | M04 §5.5 (K4): "`bridgeMass` T (the normalized level-L fiber count, L = max(thr T,1)) equals μ(fiber T) — level-exact cylinder reading; plus (ns-null) excluding infinite trees". D-15 = O-1thr Theorem 3(b)/(c): "#Φ_N(T) = mass(T)·p^{nN}"; "D_σ(N) = Σ_{T : type(T) = σ, thr(T) ≤ N} mass(T)·p^{nN}, a finite sum" | **NONE.** Per-tree count laws + a PER-σ count; nothing is summed over σ, nothing totals 1. [M04 Theorem 2 does sum over σ — but its identity is the bare box partition ((q-5), a tautology of any Option-valued map, a BOX-side count, not a member-row sum), and Theorem 2 is consumed NEITHER by the Theorem-4 walk NOR by ROOT Step 18's displayed statement (the per-τ tie only)] |
| **the Theorem-4 walk itself** (Step 18's proof line: "the M04 Theorem-4 walk (least fixed point, Bekić triangularization, Neumann under spectral escape; proved self-contained)") | "Consumes: Steps 1, 5, 6, 10–12, 14, 15, 16, 17 — all EARLIER. NOT consumed: D-11 M2 (Step 18b)" | M04 Theorem 4's proof, in full: "K4 turns the LHS into Σ_{T type σ} μ(fiber T). K1 + Lemma 3.3 turn it into the shallow convolution of the numeric B's. Lemma 3.1 + Bekić + Lemma 3.2 with K2, by induction on the block size e …, give B_{e,·}(σ′)(q₀) = (I − A(q₀))^{−1} c(σ′) …; K3 identifies this … with the evaluation at q₀ of `blockSolve` …; det(I − A) ≠ 0 comes from Lemma 3.2(ii) …. Assembling over shapes gives the evaluation at p of `Rsh`(vmap σ); by `rsh_interp` … that is Rval(vmap σ)(p) ∈ [0,1] (`r_bdd`), so `ENNReal.ofReal` is faithful." Lemma 3.2's hypothesis: "Suppose all smaller-block values entering block e's split outcomes at q₀ are finite" | **NONE.** The linear solve needs ρ(A) < 1 (K2) and FINITENESS from smaller blocks — never a row total; M04's own bookkeeping note: "the [0,∞] bookkeeping: no convergence hypothesis is consumed anywhere before K2 enters" |
| **Step 18b** (M2 r4) | "Proof: the D-11 M2 argument … with its two seams now supplied by EARLIER steps: **(S1)** … ← Step 14 …; **(S2)** = the O-11 composition datum ← Step 18. (r1) is the uniqueness pivot (Step 17)." | The §3.3 repaired proof step's inputs, each displayed: (RE)/(PACK-iv) row form; M1(a) families (ii)/(iii) ("each m(F)(q₀) = P(F | C_e)"); (S1)+(S2); the block induction; O-12 Theorem 1(3): "the three re-entrant bookings O1, O2′, O3 have the SAME solve: their balance equations are all algebraically (1 − κ₀ − κ₁)x = s, and 1 − κ₀ − κ₁ = 1 − q^{1−E} ≠ 0 in ℚ(q)" (and O-12 Theorem 2 (vii): "β_e(σ) = u^{−1}·t_σ with u = 1 − q^{1−E} … **NOT a division of a row containing β_e**"); (r1) = Corollary D nonvanishing; the exhaustiveness note ← M1(b)/**(d)** + (b-PF)/(b-EX)/(LOOP-∞) (§2.4) | **exactly ONE Σ = 1, and it is NOT a member-row total:** D-11 M1(d), verbatim — "(d) [Σ = 1]. For every block state, the **one-step strata** masses sum to 1: (b)'s partition + countable additivity + L6e(ii) (Z_e null)" — a PROVED theorem at its honest scope, consumed at the renewal-equation exhaustiveness note. The balance equation is a row IDENTITY (s_member = s_true), the pivot a nonvanishing; no line sums t_σ or β-legs over σ |
| **Step 19's squeeze** (context row) | "Step 18 delivers series = R_τ (O-11); Step 18b delivers α = series (D-11 M2); TOGETHER they deliver α = R_τ"; Σ_τ R_τ = 1 "CONCLUDED at Step 19" from Step 1 + interpolation (ROOT REVISION-3 finding B3) | — | **NONE table-side**: the total is a CONCLUSION from Step 1 + interpolation, not a consumed table-side normalization |

**What the trace supports.** Within the lines it traces, the only Σ = 1 found
is M1(d)'s ONE-STEP-STRATA theorem (delivered, proved, consumed at 18b's
exhaustiveness note) and the only other row-sum object is Corollary D's
SUB-stochastic kernel value. Because the trace is NOT closure-complete, the
design claims NO universal non-consumption — the cover is (ROW-Σ), §4.2.

**STATUS.** The tier list and the canonical BLOCKED-PENDING line are §0.3's.
The FULL line is displayed nowhere but §0.3; §4.1's need-table cells are its
per-need clauses, verbatim (§0.3's display rule, round-5 finding 8) — sync
is clause-by-clause against §0.3, so the displays cannot desynchronize.

---

## 5. The two O-11 items

### 5.1 O11-G2 — CUT-WD: NEW [M] row (H8)

**What CUT-WD is.** An open kernel of tree node T-6 consumed inside Step 18's
K1 (the M04 Lemma 3.3 regrouping): the shallow-cut decomposition /
exhaustive-exclusive read-ownership statement. O-11 r3 displays its serving
map (← O-1thr Theorem 1 = D-14 read locality + CU-3 coherent nonempty locus)
as a correspondence CLAIM, not a demonstrated implication (its own pass-2 G-1
display); the owed pass verified the gap ("overlapping ownership, an unowned
read, or two different shallow decompositions" are unexcluded). ROOT displays
it nowhere (`rg CUT-WD` = 0 hits). Under the ledger's own classification rule
(the VC5/VC6/F-1 genre), an open proposition consumed on clause (R)'s
mandatory path cannot ride an unexecuted adjudication promise: it needs an
[M] home.

**NEW ROW (verbatim, §3.1 + (ROOT-C)).**

> **(H8) = (K-CUT) — the shallow-cut decomposition kernel** [NEW row at r11,
> from the O-11 owed-pass G-2]: for every n ≥ 2, every prime p, and every
> splitting type σ of degree n, every complete type-σ canonical tree T admits
> EXACTLY ONE decomposition into a shallow shape Ŝ plus per-branch block
> derivations (D_1, …, D_r) — exhaustive-exclusive read ownership at the
> first-split cut — and the decomposition is weight-preserving,
> μ(fiber T) = W(Ŝ)·∏_i weight(D_i), as M04 Lemma 3.3's hypothesis consumes
> it at Step 18's K1. Status: an OPEN KERNEL of T-6 (the T-6 row's own
> naming); the O-11 r3 record's serving map (← D-14 + CU-3) is a
> correspondence CLAIM, not a demonstrated implication (O-11 pass-2 G-1;
> owed-pass G-2). Owner: T-6/O-1thr/CU-3 arc. NAMED RETIREMENT ROUTE: O-11
> §8 charge (vi) — the adjudication of the serving map against T-6's
> §T-ASSEMBLY; if that adjudication demonstrates the implication from
> on-file content, this row RETIRES into the consuming leaves' [V] debts.
> Enters Step 18 (K1's Lemma-3.3 regrouping), hence clause (R); clause (UB)
> inherits through the transported chain. NOT (0)/(SQ).

**One-home adjudication (why not (H6)/(H7)).** Not (H6): CUT-WD's seam is the
first-split cut inside K1, not the terminal seam, and (H6)'s membership is
pinned by the leaf-#9 interlock. Not an (H7) member: the K1 seam CLASS
matches, but the owners differ (T-6/O-1thr/CU-3 vs (H7)'s O-10/GD-family),
(H7)'s membership is pinned as the F-1-adjudicated PAIR, and CUT-WD carries
its OWN named retirement route (charge (vi)) — content that can retire
independently keeps its own home. This mirrors the F-1 sibling-row reasoning
exactly.

**Conforming ROOT edits** (executed at r11, listed at §7 E5): (ROOT-C)
hypothesis list + clause (R)/(UB) attribution lines gain (H8) AND (H9); Step
18's K1-a display names them; the [M] row count syncs (ten → TWELVE); §3.4's
correspondence table gains the pointer at its Lemma-3.3 rows.

### 5.2 O11-C1 residue — the n ≥ 2 Lean guard (leaf-side note; no ROOT edit)

ROOT is insulated (its §1 opens "Fix n ≥ 2"; the impact audit's disposition
(c)). Leaf-side dispositions to execute with the next O-11 touch (r4):
(i) the advertised target row in O-11's §"Mathematics" gains the explicit
"for every n ≥ 2" quantifier (matching Theorem O11's proved scope); (ii) the
normative Lean row `BK.series_tie` gains the `2 ≤ n` guard at formalization —
recorded now in the §3.3 "Item-27/28 Lean statement repairs" row's territory
(PARKED engineering) so the census carries it; no (ROOT-C) content changes.

---

## 6. Contingencies (labeled)

**Standing note.** **(NSF-KEY) is NOT in this roster** — it is an [M] member
of (H9) (§2.5), KNOWN FALSE at HEAD, with its retirement semantics at
(NSF-KEY-RET) and its execution at §7 Unit C; contingencies are things that
MIGHT fire. **(ROW-Σ) is NOT in this roster** — it is an r4
THEOREM-OBLIGATION (§4.2; Unit A L10); it HAS fired.

1. **(BOX-VOL) L6a-shape dependence** — RESOLVED IN THIS DESIGN: L6a's
   verified display was checked and quoted (§2.2); the r4 executor's duties
   are the verbatim cite PLUS verifying that k counts the DISTINCT imposed
   equalities and that every referenced N(P) occurrence has the claimed
   provenance. Fallback (narrowing) specified at §2.2, costs nothing on the
   mandatory path.
2. **(NS-ALL)** — fires exactly if the (CH-COV) closure audit (§2.5; Unit A
   L11) finds a mandatory consumer needing all-lifts separability FROM M3(a)
   at boxes not definitionally ns-free — a consumer OUTSIDE both displayed
   channels. THEN it is priced as an explicit open lemma (home:
   (H6)-adjacent, terminal/label seam — adjudicate at that time) and this
   design returns for re-adjudication. [Round-4 finding 8: the former
   justification for keeping this contingent — "no such consumer was found"
   — was an unsupported universal non-consumption claim and is DROPPED; the
   executed round-2 checks survive as EVIDENCE only. The honest status is:
   non-firing is NOT established until (CH-COV) closes clean; N2 carries the
   audit in its BLOCKED-PENDING clause (§0.3).]
3. **(PACK-iv) fallback — tombstone:** (PACK-iv) has been the PRIMARY route
   since round 2 (round-1 finding 1); its named RETIREMENT ROUTE
   ((route-a)/(route-b)) is displayed at §3.3. Kept in this roster so the
   promotion stays visible.
4. **(ROW-Σ) — tombstone:** promoted OUT of this roster (round-3 finding 3:
   the (†18) trace is non-exhaustive, so "fires only if a consumer is found"
   rested on an unsupportable universal claim). Now the §4.2
   theorem-obligation, executed at Unit A L10.

---

## 7. Execution plan (after the Codex plan-review ACCEPTS this design)

**Unit A — D-11 r4** (leaf repair; COPY rev 3, edits at finding sites only,
every pass-confirmed passage byte-stable; open with a §0-pre dispositions
table mapping pass-3 findings 1–9 → the §§2–3 repairs):
* L1 preamble (§2.1) + the downstream unqualified-"mass" sweep;
* L2 (a′) first sublist + (BOX)/(BOX-VOL) (§2.2) + the k/N(P) provenance
  verification duty;
* L3 §5/§7 billing (§2.3);
* L4 (b-PF) + the (b-EX) OPEN-LEMMA statement + its grammar-induction
  write-out per §2.4's displayed route (one paragraph per family; honesty
  clause if a case fails) + the (LOOP-∞) display + consumer re-points;
* L5 Theorem M2 (RE) restatement at its conjunctive form + proof-step
  replacement + the §2.3(iv) grammar quote into §0 (§3.3) + the
  consumed-instance sentence REPLACED by the (PACK-iv) cross-reference: the
  leaf displays that (RE)-at-the-consumed-member is clause-4/(H5)-class
  content, priced at ROOT as (PACK-iv) — the leaf does NOT discharge it;
* L6 Lemma M2.0 loop-extended addresses + the (O-1)–(O-5) write-outs, with
  (O-5) at its corrected exit-partition form (terminating exits + the null
  path — §3.4), PLUS the (O-GLOB) write-out per its §3.4 v5 route — the
  four parts (G-a)–(G-d) each displayed: the finite-slot branching bound,
  the root-to-leaf ≪ transport, the PER-ADDRESS null union (with the
  two-index-sets display distinguishing it from (O-5)'s per-(w, F) mass
  decomposition), and the pointwise strong induction on block size;
* L7 M3(a) separable scope + the (H9) = (NSF) display per §2.5 (the target
  statement; (NSF-INT) with the two priced gaps and its SINGLE retirement
  route; (NSF-KEY) at its one-proposition v5 form with the M02 divergence
  record and (NSF-KEY-RET); quotes as context, NO proof claim) — plus the
  (NSF-INT) leaf-proof write-out per (NSF-INT-RET) (artifact I-1, against
  the I-2 site list), separately adjudicated as a proof (gate I-3);
* L8 M3(b) in-statement conditionality (§2.7);
* L9 §6 falsifier-criterion display (§2.6);
* L10 the (ROW-Σ) write-out at Step 17's layer, per §4.2's displayed
  statement and per-booking route — clause (a) AND the per-booking clause
  (b); the write-out must display the three booking cases separately
  (round-4 finding 2);
* L11 the (CH-COV) closure-audit artifact (§2.5): the dependency-closure
  table of every M3(a) consumer on the Step-17/18/18b/19 path, walked to
  closure; outcome = clean, or (NS-ALL) fires per §6.

**GATE (Unit A):** the r4 hostile pass (fresh context, Codex; the D-11
registry bar unchanged) — its charge EXPLICITLY includes adjudicating the
(b-EX), (O-1)–(O-5), (O-GLOB), and (ROW-Σ) write-outs as PROOFS (not
displays) and the (CH-COV) artifact as a CLOSURE-COMPLETE trace.

**Unit B — ROOT r11** (display edits; §§1/7–15 discipline as at prior
revisions; CONDITIONAL — see Order):
* E1 Step 17 statement line → the r4-scoped form: "every
  family-(i)/(ii)/(iii) solve entry … IS the Haar mass of its continuation
  event CONDITIONAL on the block state law C_e; family-(v) atoms at their
  per-occurrence (a′) readings (ambient boxes / per-cell singletons; the
  (O3) scalings NOT masses); families (iv)/(vi)/(vii) excluded in-statement
  ((a″)); Σ = 1 at the displayed ONE-STEP STRATA (M1(d)); member-row
  normalization at (PACK-iv) members = **(ROW-Σ), a PROVED lemma** (solved
  totals Σ_σ β_e(σ) = 1; per-booking verdict-row totals = the Corollary-D
  margins Φ^{(O1)}/Φ^{(O2′)}/Φ^{(O3)} — §4.2's display); multi-step
  disjointness at prefix-free families ((b-PF)), grammar exhaustiveness =
  **(b-EX), a PROVED lemma** [the "or a displayed open lemma" branch is
  STRUCK — under the Order clause Unit B executes ONLY IF the r4 pass has
  ACCEPTED these write-outs as proofs, so an executed E1 records nothing
  weaker]; the infinite loop-0 word per (LOOP-∞); per-block a.s. exit
  unconditional, multi-block at Lemma M2.0's (S1-m)+(DET) + (O-GLOB) (Step
  18b's layer)";
* E2 Step 17 status line gains the pass-3 CRITICAL record + r4 pointer;
* E3 Step 18b proof line → "the D-11 r4 M2 argument at its (RE) scope — the
  consumed member's (RE)+row-form profile priced as **(PACK-iv)** ((H5), NEW
  member; the former definitional-discharge display is WITHDRAWN) — with
  (S1) ← Step 14, (S2) ← Step 18, (r1) pivot ← Step 17; the concrete pack's
  conformance = (H5)'s correspondence clause";
* E4 (H5) row + (ROOT-C)(H5): ADD the NEW member (PACK-iv) verbatim per §3.5
  — presented as an ADDITION to the row-law roster (three → four), never a
  clarification; consumption attribution written UNCONDITIONALLY per §4.2:
  Step 18b (direct) AND every (ROW-Σ) application site (untraced cover)
  [round-4 finding 1: the former "if (ROW-Σ) ever fires, re-sync" rider is
  DELETED — it fired; E4 writes the widened set at execution];
* E5 the (H8) row + the (H9) = (NSF) row (both members verbatim per §2.5,
  (NSF-KEY) at its one-proposition form with (NSF-KEY-RET) referenced) + all
  conforming displays (§5.1); the row count sync is ten → TWELVE ((H8) +
  (H9)); (PACK-iv) adds a member, not a row (§3.5 accounting);
* E6 §3.4 rows 6(iii)–(ix)+7 and 13: "(M1: entries ARE masses)" pointers
  re-scoped to the r4 form;
* E7 §3.2 D-11 [V] row synced to r4 (pass 3 CRITICAL; r4 on file; fresh pass
  owed);
* E8 ACCEPTANCE STANDING: every display (header, §3.2, §6, footer, §15)
  reads **SUSPENDED** — never "clean", never "accepted" — with the counter
  at 0 of 2 toward the end-to-end bar (two consecutive clean model-diverse
  passes on identical text, fresh verifiers). A clean D-11 r4 leaf pass
  removes the LEAF defect and is recorded at E2/E7 as exactly that;
  composition acceptance moves ONLY at the bar — the two events are never
  conflated in any display. Every status display carries §0.3's canonical
  BLOCKED-PENDING line verbatim (round-4 finding 6);
* E9 Step 18's K1-a/K4 lines + Step 17's M3 leg gain the **(H9) = (NSF)**
  display — the target statement AT ITS INTERFACE-PIN SCOPE with BOTH
  members and the two-channel consumption attribution + (CH-COV) status
  (§2.5); (NSF-KEY)'s executed status is recorded as of the edit — written
  ONCE, after Unit C is TERMINAL (see Order); E9 must NEVER display the
  (H9) target as covering the HEAD wiring while (NSF-KEY) is unretired.

**Unit C — (NSF-KEY) execution** (Lean wiring + leaf-row conformance; the
C-cone changes the carrier and the `count_tie` scope across the
`canonical_stable`/`VPSound` cone, so it carries its own gates):
* (C-0) obtain SIGN-OFF per (NSF-KEY-RET) R-0 (statement-fence gated);
* (C-1) execute the R-1 diff (the `MovesT.NsFree` conjunct on `bridgeTree` +
  the mechanical ripple — BridgeD6/D7/D8 pins, the
  `canonical_stable`/`VPSound` consumers);
* (C-2) validations per R-2/R-3: the `count_tie` discharge compiled
  sorry-free at the guarded instance; BridgeD8's `canonical_stable` re-run
  green; the V₀-refutation-dead record for `VPSound` + its ledger wiring
  re-compiled (VPSound itself REMAINS the open kernel — no proof promised);
* (C-3) gates per R-4/R-5: full `lake build` green + AxChk footprint
  identical; the Codex diff-confirmation (fresh context: the applied diff is
  exactly R-1 + mechanical ripple; statement fence respected);
* (C-4) record the executed status for E9.

**Unit C terminal semantics [round-4 finding 7 — made unambiguous].** Unit C
is TERMINAL when and only when it is EXECUTED with (C-0)–(C-4) all green
(= all six (NSF-KEY-RET) artifacts on file). There is NO other terminal
state. If sign-off is REFUSED or any gate fails: Unit C is NON-TERMINAL, the
execution plan HALTS — Unit B does NOT run, NO ROOT edit occurs (E9
included) — and this design returns for re-adjudication (§0.3's failure
mode). ["Refused-and-re-adjudicated" is NOT a terminal state of THIS plan:
re-adjudication produces a successor design; nothing downstream of C runs
under this one.]

**Unit D — the end-to-end bar:** two consecutive clean model-diverse
verification passes on IDENTICAL text, fresh verifiers (the E8 bar). Unit D
STARTS only after Units A, B, AND C have all closed (r4 pass accepted; ROOT
edits E1–E9 written, E9 after Unit C terminal; Unit C's gates green). **ANY
text change after a pass — including an E9 status re-sync — restarts the
counter at 0.** Suspension stands until Unit D passes.

**Order [STRICT LINEAR — round-4 finding 7: the former "Unit C may run in
parallel with Unit A" permission is WITHDRAWN (it contradicted the displayed
linear order); C's ripple work may be PREPARED any time, but its sign-off
request and execution follow the r4 pass, so that any pass-triggered
re-adjudication folds into one sign-off package]:**

    Codex plan-review of THIS design (round 5) — must ACCEPT
      → Unit A (L1–L11)
      → the D-11 r4 hostile pass — must ACCEPT the (b-EX)/(O-1)–(O-5)/
        (O-GLOB)/(ROW-Σ) write-outs AS PROOFS and (CH-COV) as
        closure-complete
      → Unit C (C-0 … C-4) — must reach TERMINAL (= executed, gates green)
      → Unit B (E1–E9; E9 written once, after C terminal)
      → Unit D (the end-to-end bar).

If the plan-review or the r4 pass rejects, or Unit C fails: NO ROOT edit
occurs; the design returns here for re-adjudication first. PROJECT_STATE.md +
ledger sync at each unit close.

---

## 8. Completeness self-check: every round-1..4 finding → where this V5 disposes it

Rounds: R1 = `R11D_review_2026-08-04.md` (9 findings), R2 =
`R11D2_review_2026-08-04.md` (9), R3 = `R11D3_review_2026-08-04.md` (7),
R4 = `R11D4_review_2026-08-04.md` (9). "Superseded-by" chains are walked to
their FINAL disposition in this file; nothing rests on a withdrawn
intermediate.

| finding | class | gist | V5 disposition | where |
|---|---|---|---|---|
| R1-1 | CRIT | (RE) not definitionally discharged; (PACK-iv) warranted; "no-α ⟺ profile" unestablished | definitional discharge WITHDRAWN with three recorded reasons; (PACK-iv) the PRIMARY route; (RE) a pure conjunction (no derived clause) | §3.3, §3.5 |
| R1-2 | CRIT | (b-SW) asserted, not proved; {loop-0 forever} outside (b-PF) | (b-SW) replaced by OPEN LEMMA (b-EX) with per-family induction route + honesty clause; (LOOP-∞) displayed (null + disjoint) | §2.4 |
| R1-3 | CRIT | M3(a) narrowing may lose N2 content; certificate implication unchecked | separable-scope repair + the two channels; the checked-implication attempts of rounds 2–3 ultimately WITHDRAWN and priced as (H9) ((NSF-INT)/(NSF-KEY)); residual coverage claim now the (CH-COV) audit | §2.5 |
| R1-4 | CRIT | N1 silently uses member-row Σ = 1; source unnamed; 18b circularity risk | delivery claim WITHDRAWN; (†18) trace (non-exhaustive, so no universal claim); (ROW-Σ) the proved M2-free cover; 17≺18≺18b graph displayed once | §4.2, §4.3 |
| R1-5 | CRIT | M2.0 repair not discharged; five obligation classes omitted | (O-1)–(O-5) enumerated verbatim with routes; billing demoted to design-level claim | §3.4 |
| R1-6 | ADV | BOX-VOL genuine; verify k-distinctness + N(P) provenance | duties on L2 | §2.2, §7 |
| R1-7 | ADV | clause-(c) scope + "obligations: none" too strong | per-sub-clause reference measures named; the downstream "mass" sweep on L1 | §2.1, §7 |
| R1-8 | ADV | (H8) correctly treated | carried unchanged | §5.1 |
| R1-9 | CRIT | Unit B unconditional; E8 conflates leaf-clean with accepted | Unit B gated on r4 ACCEPT; E8 = SUSPENDED everywhere, counter 0-of-2, events never conflated | §7 E8, Order |
| R2-1 | CRIT | (K1-NSF) still unwarranted ((w3)/(w4) fail) | (w3)/(w4) withdrawn; the round-3 quote-chain proof ALSO withdrawn (R3-1); final home = (H9)/(NSF-INT) priced, quotes = context | §2.5 |
| R2-2 | CRIT | "Σ = 1 consumed nowhere" not established | universal claim DROPPED; trace relabeled non-exhaustive; (ROW-Σ) required cover | §4.2, §4.3 |
| R2-3 | CRIT | (O-5) omits terminating exits | (O-5) restated over ALL exit strata + null path; three-part consumption display | §3.4 |
| R2-4 | ADV | M2 (RE) retains contradictory "equivalently" | struck; (RE) a conjunction | §3.3 |
| R2-5 | ADV | (b-EX) honestly open, real skeleton; (vi)/(vii) claims pending | carried; validation = the r4 write-out + hostile pass | §2.4, §7 |
| R2-6 | CRIT | need verdicts misassigned; (H8) outside N-table | tier verdicts per §0.3; N8 in the table | §4.1 |
| R2-7 | ADV | [M] arithmetic consistent | twelve-row accounting displayed | §3.5 |
| R2-8 | ADV | dependency graph acyclic | maintained; ONE authoritative graph display | §4.2 |
| R2-9 | ADV | E1's dead "open lemma" branch | struck; E1 records only PROVED lemmas | §7 E1 |
| R3-1 | CRIT | (K1-NSF′) does not prove pin → predicate → corpus (two unquoted gaps) | proof claim WITHDRAWN; gaps priced as (NSF-INT) (i)/(ii); retirement = r4 leaf proof ONLY | §2.5 |
| R3-2 | CRIT | (NSF-KEY) needs its own [M] home | re-homed as (H9)'s second member; one-home argument displayed | §2.5 |
| R3-3 | CRIT | (†18) not exhaustive; universal conclusion unsupported | relabeled TRACE, NON-EXHAUSTIVE; (ROW-Σ) promoted to required obligation | §4.2, §4.3 |
| R3-4 | CRIT | (O-5) local only; global route missing; shared hand-off aggregation undisplayed | (O-GLOB) stated + v5 route (G-a)–(G-d) — including the corrections R4-5 forced | §3.4 |
| R3-5 | CRIT | N2 "MET AT THE INTERFACE PIN" dishonest at HEAD | N2 = BLOCKED-PENDING ((NSF-KEY) + (CH-COV)); pin language survives only as the conditional target's description | §4.1, §0.3 |
| R3-6 | CRIT | Unit C not order-independent; counter restart unstated; no C gates | strict linear order; C's own gates (C-0)–(C-4); D counter restarts on ANY text change — plus R4-7's terminal-state fix | §7 |
| R3-7 | ADV | "BLOCKED strictly EMPTY" obscures status | tier vocabulary official; BLOCKED-PENDING canonical line, stated ONCE (§0.3) | §0.3 |
| R4-1 | CRIT | (ROW-Σ) integration contradictory ((PACK-iv) attribution, 17-18-18b graph, E4 conditional) | ONE authoritative display (§4.2: statement/route/consumers/graph); (PACK-iv) consumption set widened UNCONDITIONALLY (18b direct + every (ROW-Σ) site); E4 rider deleted; N1 line carries (ROW-Σ) | §4.2, §3.5, §7 E4 |
| R4-2 | CRIT | (ROW-Σ) telescoping ignores the (O2′) re-feed and (O3) scaling | the route redone with the three booking cases SEPARATED: (O1) S = 1−κ₀−κ₁; (O2′) affine fixed point solved, S = 1−κ₀; (O3) scaling displayed, S = (1−κ₀−κ₁)/(1−κ₀); statement made per-booking (clause (b)), solved totals uniform (clause (a)) | §4.2 |
| R4-3 | CRIT | (NSF-KEY) not one proposition ("equivalently" chain) | restated as ONE implication in as-built vocabulary; mechanism (conjunct) and validations (gates) explicitly de-conflated; retirement semantics = the exact six-artifact list (NSF-KEY-RET) with verbatim statements/diff/gates/sign-off | §2.5 |
| R4-4 | CRIT | joint (NSF-INT)+(NSF-KEY) retirement unsupported | "materialization discharges BOTH" WITHDRAWN; members retire SEPARATELY ((NSF-INT): leaf proof only; (NSF-KEY): (NSF-KEY-RET)); one-home argument survives without the joint-retirement claim | §2.5 |
| R4-5 | CRIT | (O-GLOB) defective: no branching bound; "one event per parent exit" wrong for the null union | (G-a) finite-slot branching bound displayed (from O-12 §2.3(iv)'s finite products); (G-c) null union runs PER ADDRESS (sibling slots' distinct N_a all included); the per-(w,F) convention confined to (O-5)'s mass decomposition; the two index sets explicitly distinguished; (G-b)/(G-d) give the actual root-to-leaf induction (conditional-on-reached transport; pointwise strong induction on block size) | §3.4 |
| R4-6 | CRIT | BLOCKED-PENDING line omits (ROW-Σ) at N1 | canonical line updated (N1: (b-EX) + (ROW-Σ)); stated ONCE at §0.3, every display syncs to it verbatim | §0.3, §7 E8 |
| R4-7 | CRIT | Unit C terminal state inconsistent (refusal branch; parallelism contradiction) | TERMINAL = executed-with-gates-green ONLY; refusal ⇒ HALT, no Unit B, no ROOT edit, re-adjudication; parallelism permission withdrawn; strict linear order displayed | §7 |
| R4-8 | CRIT | (NS-ALL) rests on an unpriced universal non-consumption claim | claim DROPPED (checks = evidence only); (CH-COV) closure audit created (Unit A L11, gate-adjudicated); (NS-ALL) firing priced in advance; N2's line carries the audit | §2.5, §6, §0.3 |
| R4-9 | ADV | [M] arithmetic consistent (ten → twelve) | carried; accounting displayed with the confirmation noted | §3.5, §0.3 |

**Self-check closure.** Every R1/R2/R3 disposition above is either carried
verbatim in this file's body or explicitly superseded by a LATER round's
accepted disposition (chains: R1-3 → R2-1 → R3-1 → §2.5; R2-2 → R3-3 →
R4-1/2 → §4.2; R3-4 → R4-5 → §3.4; R3-6 → R4-7 → §7) — walked in the table.
No finding of any round is silently dropped; no withdrawn claim is
load-bearing anywhere in §§0–7.

---

## 9. ROUND-5 DISPOSITION (orchestrator, 2026-08-04; ledger bb1370f)

R5 = `R11D5_review_2026-08-04.md` (3 criticals, 5 advisories; verdict
DESIGN-REVISE). Disposition, by orchestrator call:

* **R5-5 (CRIT, (H9) retirement asymmetry): FIXED IN TEXT** —
  (NSF-INT-RET) added (§2.5: artifact I-1 named, site list I-2 closed by
  L11, gate I-3 = the r4 pass); L7 carries the write-out as a listed
  deliverable; R-1's "mechanical ripple" given a CLOSED, recorded scope
  adjudicated at R-5.
* **R5-8 (ADV, verbatim-display rule): FIXED IN TEXT** — §0.3's display
  rule restated to match reality (FULL line only at §0.3; §4.1 cells = the
  per-need clauses, verbatim); §4.3's "restated nowhere else" claim
  corrected accordingly.
* **R5-6 (ADV, uninventoried root-finiteness premise): FIXED IN TEXT** —
  (O-GLOB)'s consumption line now inventories the root-finiteness premise
  ((S1-m)/Lemma M2.0 step 2), consumed at (G-b) base and (G-d) close.
* **R5-2 (CRIT, (ROW-Σ) consumption-graph edge set) and R5-3 (CRIT,
  (O-GLOB) finite-time Z_μ encounters): FOLDED AS NAMED DUTIES INTO UNIT
  A'S CHARGE**, adjudicated by the r4 hostile pass — R5-2: the L10
  write-out (with L11's closure walk) must enumerate the ACTUAL (ROW-Σ)
  application sites/consuming proof lines, replacing "possibly within
  17/18"; R5-3: the L6 (O-GLOB) write-out must add the per-address/per-time
  null union covering finite-history entries into Z_μ (via (G-b)'s ≪
  transport against M1(d)'s Z_μ nullity), so (G-d)'s pointwise exit claim
  follows off the enlarged 𝒩. Neither is claimed disposed by this design's
  text; both sit inside obligations already gated at the r4 pass.
* **R5-1/4/7 (ADV): confirmations** — no text change.

**Standing: the design is EXECUTION-READY at architecture level**
(orchestrator call, ledger bb1370f): the remaining criticals live inside
Unit A's proof obligations, not in the architecture, and the r4 hostile
pass is their adjudicator. The Order clause is unchanged — no ROOT edit
before the r4 pass accepts.

