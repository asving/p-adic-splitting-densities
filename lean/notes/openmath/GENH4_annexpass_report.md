# GENH4 ANNEX-PASS — HOSTILE VERIFIER REPORT (scoped: ANNEX PE5 + ANNEX R)

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 GAP + 4 MINOR (+ 2 remarks),
scoped to the two annexes.** The GAP sits in ANNEX R's R2 (the F4
repair): its N-even band-pinned per-stratum witness leg is FALSE, with
a MACHINE-REFUTED instance at (q,N,k) = (2,10,2) — the u = 10
refine-path lifts that R2's refine-deeper display labels
2SIDED′ → {(1,2),(1,2)} read PARI σ = {(2,2)} on 6/6, and at (2,8,2)
the "Lift 2" read R2 invokes is structurally unrealizable, making the
whole band-pinned stratum σ-CONSTANT — no within-stratum differing
pair exists there at all. Clause (c)'s KEY-LEVEL conclusion (no single
lift-sound label for the leaf key) SURVIVES — machine-confirmed by
band-zero contrast members of the same keys (6/6 {(1,2),(1,2)}) —
and (c) is unconsumed by W-12.D, so no consumer breaks: GAP, not
CRITICAL. The heavy consumed surface — ANNEX-LEMMA GENH4-7'(b), the
F-SPLTAIL σ-supply over the free band — was re-derived from scratch
and survived every attack, including two fresh cells (first k = 3
ever; first odd-q k ≥ 2). Both annex machine legs re-ran isolated
GREEN (PE5 leg bit-identical; R leg elapsed-only diff); all md5 pins
and byte-freezes verified.

Scope and provenance: target = the TWO ANNEXES of
`GENH4_PROOF_2026-08-08.md` — ANNEX PE5 (baf05ed/e945734/cceca77:
ANNEX-LEMMA GENH4-7 + A2 + A3 + `genh4annex_supp.py`) and ANNEX R
(6272cd4/b10a5a7: ANNEX-LEMMA GENH4-7' + R2 per-stratum displays + R3
L/O_L frame + R4 units + R5 law-keys + `genh4annexr_supp.py`). The
frozen accepted body's 2/2 is NOT at stake and nothing here touches
it. Fresh context, zero prior stake, quote-and-classify, fix nothing.
Body sections read for context: GENH4-3 (S4), S2.1/S2.3, S6.1/S6.3,
S7, S8; `CODEX_GENH4RAT_2026-08-09.md` read for what ANNEX R repaired.

## S1. Findings

### GAP-1 — ANNEX R, R2's N-even band-pinned leg + the refine-deeper leg: FALSE per-stratum witness claims, machine-refuted; clause (c)'s per-stratum re-establishment fails on band-pinned strata (unconsumed; key-level conclusion survives)

**Quoted (R2, N-even dμ < w bullet):** "band-pinned with m ≤ 2w:
u = N residual read at depth dμ < w (S₁-slot 0): char ≠ 2 decided
≠ {(2,2)} as above; char 2: '1sq' → one refine step. NO
residual-class comparison is needed in this sub-case — the char-2
even-N gap of the old display is bypassed by the RAM(N+1) leg."

**Quoted (the refine-deeper leg):** "LEMMA GENH4-4 maps the refine
locus ONTO the floored fresh node {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁},
whose digits are free lift digits; realize the fresh leaf
dv(A₁′) = dμ₁+1 =: w′, dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ …: a fresh
2SIDED′(w′, w′+1) for every such lift, σ = {(1,2),(1,2)} … Clause (c)
is thereby re-established at the key level in every stratum."

**Failure scenario 1 (machine-refuted, the refine-path).** Cell
(q,N,k) = (2,10,2), UND key (2w = 14 ≥ N), band-pinned stratum
m = 11 (b₁@9 ≠ 0), w = 7, dμ = 5 < w — squarely inside the quoted
bullet. The u = 10 lift (b₀@10, in budget) reads '1sq' at depth 5
and refines; the quoted display then promises a fresh
2SIDED′(6,7) → σ = {(1,2),(1,2)} "for every such lift". FALSE: the
fresh leaf dv(A₀′) = 2dμ+3 = 13 is UNREALIZABLE — the height-11 band
letter's ȳ-component d₁ ≠ 0 survives the refine (λ = ŝ²π¹⁰ + ŝπ⁵A₁
contributes the height-10 kill plus terms at heights ≥ 12 only; no
correction reaches height 11), so dv(A₀′) = 11 is FORCED, 11 odd
≤ 2w → RAM(11) → σ = {(2,2)}. The transport error: GENH4-4's
onto-the-fresh-node statement holds over the FULL refine slice
(all in-window digits free), but here the member is FIXED and only
LIFT digits vary — "whose digits are free lift digits" is false for
the A₁′ string (in-window, key-pinned: dv(A₁′) = w in equal
characteristic since s₁ = √S₀ ∈ F_q gives carry C = 0 and the 2w_re
term dies; = dμ+1 in mixed characteristic by the +2w_re revival —
forced either way, never free) and false for A₀′ below m. PARI
adjudication (fresh leg FR4): the 6 refine-path u = 10 lifts across
3 pins read σ = {(2,2)} on 6/6 — the verifier's RAM(11) derivation
CONFIRMED, the annex's 2SIDED′ display REFUTED. All 12 lifts of the
stratum read {(2,2)} (the stratum is σ-constant), both u = 10 and
u = 11 shapes.

**Failure scenario 2 (structural, N ≤ 4k).** Cell (2,8,2), band-pinned
m = 9, w = 6 (N = 8 even, dμ = 4 < w: in the bullet's scope). The
quoted "u = N residual read" DOES NOT EXIST: the height-8 letter's
two components both sit below the GENH4-1F entry budgets
(b₀@8 < v(β₀) ≥ 4k+1 = 9; b₁@6 < v(β₁) ≥ 3k+1 = 7) — a "lift" with
b₀@8 ≠ 0 leaves the entry family (its B₀ leading digit cancels:
v(B₀) = 9 ≠ 4k = 8, breaking the entry pin; smoke members built in
violation came back OUTSIDE the F dictionary entirely —
{(2,1),(2,1)}, disc 0 — disclosed in the fresh leg's docstring). So
every in-family lift has u = 9 = m → RAM(9) → σ = {(2,2)}
CONSTANT, in BOTH characteristics (12/12 machine) — neither the
char-≠2 leg nor the char-2 leg of the quoted sentence produces a
within-stratum differing pair, because no second read exists.

**Classification: GAP** (justification gap in the unconsumed
sharpness clause's re-proof). What survives: clause (c)'s conclusion
AT THE KEY LEVEL — the leaf key aggregates band strata (deep0 is
inside the key mass), and band-zero members of the SAME keys carry
u > 2w lifts with σ = {(1,2),(1,2)} (machine: 6/6 at both cells), so
"no single label is lift-sound FOR THE KEY" holds, which is exactly
what cap-uniqueness consumes; the reader's UND exit stays
conservative-sound; W-12.D consumes (b) only. What does not survive:
R2's sentence "re-established at the key level in EVERY STRATUM" read
as within-stratum witness existence, the refine-deeper leg's fresh
2SIDED′ construction (false in equal characteristic everywhere it is
invoked on a fixed member, false in both characteristics where the
band caps u′ ≤ m < 2dμ+3), and the N-even band-pinned sub-case's
claimed differing pair (no pair exists there). Owed: a dated
correction to R2 scoping the N-even band-pinned sub-case to
key-level (cross-stratum) witnesses — which is all (c) ever needed.

### MINOR-1 — GENH4-7'(a)'s realizability parenthetical (and R2's u-geography) false at N ≤ 4k hidden states

**Quoted (GENH4-7'(a)):** "u_lift = N realizable (the a₀ lift digit
at position N)". **Quoted (R2):** "u_lift sweeps {N, N+1, …} at a
band-zero state".

**Failure scenario:** at (2,8,2) hidden states (nonempty: every UND
leaf there), position N = 8 sits BELOW the entry budget
v(β₀) ≥ 4k+1 = 9 and the height-8 b₁-component below v(β₁) ≥ 7: the
height-N letter is structurally zero, u = N unrealizable; the sweep
starts at max(N, 4k+1). Harmless for the consumed clause (b) —
SPLTAIL forces N ≥ 4k+3 > 4k+1, where position N is in budget and
every committed and fresh cell confirms realizability — and for every
committed row; it bites only inside (c)'s geography, where it is
mechanism 2 of GAP-1. The floor half of (a) (u_lift ≥ N, every band
completion, every lift) is exact everywhere (re-derived, and
enumerated 24,576/0 by the annex leg's C4 + 96 + 96 fresh members).

### MINOR-2 — R2's 2w = N char-odd line-partition argument: quantifier slip at s = 0 and the 0-line case

**Quoted:** "if for EVERY square s and every d₀ the value s/4 − c·d₀
were a square, the set (squares ∪ {0}) of size (q²+1)/2 would be a
union of full affine lines in direction c, each of size q —
impossible since q ∤ (q²+1)/2."

**Failure scenario:** the faithful negation of the existence claim
quantifies only over REALIZABLE s = S₁² with S₁ ∈ F_{q²}^× — the
NONZERO squares; s = 0 is not realizable (pin letter ≠ 0), so the
displayed hypothesis is stronger than the negation, and without the
s = 0 instance the coset c·F_q through 0 is not covered: "union of
FULL affine lines" needs the extra half-step. It closes two ways: at
the actual instance c = 1 (genre F has no twist, S3) the 0-coset is
F_q ⊆ squares of F_{q²} automatically (every F_q element is a square
in F_{q²}, q odd); or count Sq∖{0} = (q²−1)/2, also ∤ q. Conclusion
(inert-continuation members EXIST at 2w = N, char odd) HOLDS; display
slip only.

### MINOR-3 — R2's N-odd dμ₁ = w branch: "separable in both characteristics" / "any nonzero digit gives a decided '11'/'2'" false at the single char-odd degenerate digit

**Quoted:** "if dμ₁ = w (N+1 = 2w) the S₁-slot is the pin letter ≠ 0,
the residual is separable in both characteristics, and any nonzero
digit gives a decided '11'/'2' ≠ {(2,2)}."

**Failure scenario:** char odd, the digit d₀ with S₀ = S₁²/4 (when
S₁²/4 lies on the S₀-line — possible) gives disc = 0: '1sq', neither
separable nor decided. In char 2 the claim is exact (disc = S₁² ≠ 0).
Existence of a decided second lift survives at every odd q ≥ 3
(≥ 2 admissible digits, ≤ 1 degenerate), so the differing pair —
which is all the branch needs — exists; the universal is the defect.
The branch's instance claim at Codex's (2,9,5) cell is char 2 and was
machine-confirmed this pass (FR5: 9/9, RAM(9) {(2,2)} vs decided
{(1,2),(1,2)}/{(1,4)}).

### MINOR-4 — GENH4-7' supersession header: "everything else unchanged" undersells its own scope

**Quoted:** "(GENH4-7 with the leaf's true floor … replaces GENH4-7's
hypothesis sentence and clause (a)'s parenthetical, everything else
unchanged)."

**Failure scenario:** 7'(a) also ADDS a new claim absent from 7(a)
(the band cap "u_lift ≤ m := the lowest nonzero band height"), and
clause (c)'s proof is wholly replaced (old two-lift witnesses
withdrawn, re-proof delegated to R2) — a reader trusting "everything
else unchanged" mis-inventories what moved. The replacement itself is
stated correctly in R1.0/R2; cosmetic display defect of the header.
