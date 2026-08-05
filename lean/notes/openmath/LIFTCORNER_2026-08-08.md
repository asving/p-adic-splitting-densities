# LIFT-CORNER — NR-1 ((ITER-LAW-LIFT) at g₀ = 1 ∧ δ₁ = 1): the lift-ORBIT transport instrument + the shift-descent compose

**Unit:** LIFT-CORNER (NR-1 of ILNRES S1; spec ILNRES S5.1, price M; route =
the W-2 shift-descent covariance + window-calculus tail bookkeeping).
Wallclock 2026-08-04, campaign date 2026-08-08. Genre: sealed-preregistration
numerics (two-commit seal) + a conditional COMPOSE (S4; written only on a
0-violation verdict, per the probe-first discipline). **Grade cap (read
first): everything this unit proves is at attempt grade 0/2 AND capped by its
W-2 consumption (GRTW2_PROOF, itself attempt 0/2, no acceptance arc run).**

**Machine leg:** `verification/openmath/liftcorner_checks.py` (this header +
the runner commit BEFORE any full run; verdict appended in commit 2 from the
artifacts `liftcorner_checks_output.txt` / `liftcorner_checks_results.json`).
[r1] A SECOND, post-hoc machine leg was added at repair round r1 and is NOT
part of the sealed prediction battery: `liftcorner_tailstab_children.py` +
its committed output `liftcorner_tailstab_children_table.txt` — the
examples-first child-type table the repaired S4.1 induction is derived from
(disclosed as written AFTER the refutation, hence evidence for a repair, not
a prediction). The sealed runner is byte-untouched (md5 unchanged, S3).

**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against LIFTCORNER-PE1 (hostile pass, fresh context, report
`LIFTCORNER_passPE1_report.md`, commit 30e570c: **1 CRITICAL + 3 gaps**;
ledger entry BRIDGE_ADJUDICATIONS_2026-07-30.md "PE1 VERDICTS"). PE1's
machine leg was bit-identical (exit 0, 25,409/0, fires 1,576, all roster
counts independently re-derived, two-commit seal verified), so nothing in
S1–S3 or in the corner measurement moved; the critical finding is confined
to one line of the S4.1 PROOF. Dispositions, each edit carrying a dated
`[r1, F#]` bracket: **F1** (CRITICAL) — the S4.1 strict-descent clause
"every child has m′ ≤ m−1" is FALSE at the top-mid q-digit child (k = e₀−1,
which sits at m′ = m; PE1's counter-instance reproduced numerically in
S4.1). REPAIRED, statement byte-unchanged, by replacing the single
induction on m with the LEXICOGRAPHIC (m, deg a) induction: the child census
is now displayed in full (seven genres), the one m-preserving genre is proved
to drop deg a strictly, the deg a = 0 stratum is proved to have NO
m-preserving child at all, and BOTH consumers (the induction; the
termination/dev-linearity finiteness) are re-closed on the lex order with an
explicit depth bound. The case list is DERIVED FROM the examples-first
table (standing directive, Asvin 2026-08-05), which is committed with this
round: 29 towers over p ∈ {2,3,5}, d₀ ∈ {1,2,3}, e₀ ∈ {2,…,6} (the e₀ = 2
boundary included), all four lift genres, PE1's counter-instance verbatim —
0 children dropping neither coordinate, and the (LEDGER) conclusion itself
re-verified on the honestly recomputed double development. **F2** — the
wave-18 S1 split b₀ = ĉ′π^{h₀} + t₀ is now defined in-note at first use
(S4 setting), with its source cited inline. **F3** — COR 2's identification
with "W2-OPEN-1 RESTRICTED to the base junction" is WITHDRAWN as underived;
COR 2 is rescoped to exactly what S4 proves (the harness monic-lift orbit),
with a box naming the two things still owed for the W2-OPEN-1 tie.
**F4** — S2 disclosure (c) now says exactly what the runner asserts (full
ψ₁-byte carryover + a one-element K₂ smoke check) and where the
modulus-independence verification actually lives (`mk_field_ext` at g = 1).
Acceptance counter unchanged at 0/2 — a repair round is not a pass; round r2
(a fresh hostile pass on THIS text) is the next acceptance attempt.]**

**Sources of record:** ILNRES_2026-08-08.md S1 [NR-1] + S5.1 (the spec);
ITERLAWLIFT_CORNER_2026-08-08.md (wave 18: the LAWFUL slice measured
104,404/0; the S7 sketch + its one open step (TAIL-STAB)); ITERLAWN_PROOF
S0.1 (the standard-lift class pin + the verbatim residual propagation rider);
GRTW2_PROOF §3.4 (χ-chain/shift-descent), §5 (clause 3 ψ-transport, W2-OPEN-1).

**FENCES.** No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies,
sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY
(in-memory ledger override only, engine_ext precedent); no Lean change; no
orders-≥3 machine claim (the battery is 2-read); no gr(w₂) claim; nothing
here closes NR-1's ledger entry until this note's own acceptance arc runs.

## S1. The corner orbit and the transport frame (derived; sealed pre-run)

At g₀ = 1: ψ₀ = y + c₀ (c₀ ≠ 0), K₁ = K₀, z₁ = −c₀ a SCALAR. The full monic
lift orbit at the corner (deg = e₀d₀, w₁ = e₀h₀, nonzero order-1 residual):
Φ′ = Φ₀^{e₀} + Σ_{k<e₀} b_kΦ₀^k, deg b_k < d₀, with w₀(b₀) = h₀,
c′ := res(b₀/π^{h₀}) ≠ 0, and w₀(b_k) ≥ amin(k) := ⌈(e₀−k)h₀/e₀⌉ (k ≥ 1;
strict-above automatic, gcd(e₀,h₀) = 1). Stratification by the residue c′:

* c′ = c₀ — the LAWFUL class of ψ₀ (wave-18's slice: measured exact, 0/104,404);
* c′ ≠ c₀ — the lawful class of the ξ-CONJUGATE ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy)
  = y + c₀/ξ at ξ := c₀/c′; letters z₁ = ξ·z₁′, z₁′ := −c′. This is exactly
  W-2 clause 3's ψ-transport, DEGENERATE at the corner: K₁ = K₀ carries no
  letter, so the tower transport is the bare scalar substitution z₁ ↦ z₁′
  (the clause-3 re-coordination step is vacuous). The ε-degeneration the
  charge names: ε₁-corrections are z₁-powers of a scalar, so the whole
  value layer transports by one character — the χ-law.

**CANDIDATE (the transport law, preregistered).** On the tower built on ANY
orbit member Φ′ (ledger transported: ψ₀ ↦ y + c′, all deeper data
byte-identical, canonical Φ₂ rebuilt on the transported letter), the accepted
2-read display holds WITH THE LETTER THE LIFT CARRIES:

    c′(γ,γ′) = z̄^{δ₂} · (z₁′)^{D₁},   D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀,
    equivalently  c_base(γ,γ′) = c′(γ,γ′) · ξ^{D₁}   (the χ-ratio law),

with all integer data (splits, D₁, δ₂, windows) lift-independent. The ξ = 1
slice is wave-18's measured law; the ξ ≠ 1 direction is NEW — no instance
evidence exists anywhere in the corpus before this battery.

## S2. Sealed prediction sheet (`liftcorner_checks.py`, seed 20260911)

Roster: the wave-18 rows CA–CF verbatim (all g₀ = 1, E₂ ∈ {4,6,8,6,10,3}),
× rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; windows W1×W1 + mixed W1×W3. Twists
exist iff |K₀| > 2 (deterministic applicability: d₀ = 2 rows on all rings;
d₀ = 1 rows on p = 3 rings only; 16 twistable (ring,row) instances). Per
instance: c′-draws (≤ 2, deterministic enumeration) × variants {pure twist,
twist + dense tails/mids} = 48 twisted towers; plus the ξ = 1 dense controls
(rows CB/CF × 4 rings) and the 24 base (standard) towers for the χ-cache.

| family | content | prediction |
|---|---|---|
| Q1 GATE | every generated tower passes the lawfulness gate FOR ITS OWN ψ₀′ (residual = y + c′) | 0 failures |
| Q2 AV | ANCHOR-VAL with the transported ε₁′ (z₁′-powers), letters W1+W3 | 0 |
| Q3 TLAW | **THE CANDIDATE: measured cocycle = transported display (z₁′)** | 0 |
| Q4 PV | L7 PAIR-VAL both forms + single-slot shape, transported letters | 0 |
| Q5 INT | exponent integrality | 0 |
| Q6 LOC | δ₁ = 0 sub-violations (lift-form-free legs; bug detector) | 0 |
| Q7 CHI | cross-tower χ-ratio: c_base == c′·ξ^{D₁}, measured vs MEASURED | 0 |
| Q8 COV | per twisted block: ≥ 1 δ₁ = 1 pair AND ≥ 1 pair with ξ^{D₁} ≠ 1 | met |
| Q9 WRONGLET | control: per-pair (c′ ≠ wrong-letter form) ⟺ (ξ^{D₁} ≠ 1), exact set equivalence; total fires > 0 | 0 / fires |
| Q10 XI1 | the ξ = 1 dense slice reproduces the UNCHANGED display (wave-18 tie) | 0 |
| TRS | closed-form transcription vs C.iter_law (transported automatically) | 0 |
| CERT | base towers: G.T1_T2(nf=4) + G.T5 internal (PARI leg NOT re-run: wave-18 T11 on the same base roster is on file — disclosed reuse) | 0 |
| ENG-GATE | engine_ext.agreement_gate(full=False) re-run in-unit (standing rule) | 0 new |

**Disclosures (pre-seal):** (a) a `--shakedown` crash-freedom run (1 ring,
2 rows, 1 twist, no json) runs before commit 1; (b) exact arithmetic,
deterministic full windows, no sampling beyond the seeded pert residues;
(c) the ledger override (ψ₀ ↦ y + c′) is IN-MEMORY on a fresh Tower object —
sound because at g₀ = 1 the degree-1 extension arithmetic of K₁ is
modulus-independent (mk_field_ext at g = 1: products never touch the reducer),
so ψ₁ and every deeper byte carries over verbatim; **[r1, F4 — corrected
wording]** the runner asserts, before any comparison, (i) full ψ₁-BYTE
carryover (`[tuple(c) for c in T.psi1] == psi1_base`) and (ii) a
single-element byte check on the K₂ table (`C.K2["one"] == C0.K2["one"]`) —
(ii) is a SMOKE CHECK on one element, NOT an assertion that the K₂ arithmetic
representation is shared, as the r0 text's parenthesis "(ψ₁ bytes equal, K₂
arithmetic representation shared)" implied. The modulus-independence itself is
verified by READING `mk_field_ext`: at g = 1 its reduction loop
`range(len(out)-1, g-1, -1)` is empty, so products never touch the reducer —
that is where the override's soundness lives (PE1 F4 re-derived it there
independently), not in the runner's asserts;
(d) SP bug-detector counters recorded.

## S3. VERDICT (commit 2; from the artifacts; seal dafc0b5, runner
byte-untouched, md5 ccb4351c92573f5f962cae4ae952d8dd)

**ALL GREEN, FIRST RUN, exit 0** — 25,409 checks, **0 violations in every
family**, elapsed 4.4 s (`liftcorner_checks_output.txt`,
`liftcorner_checks_results.json`; these govern on any transcription
discrepancy):

* Q1 GATE 56/56 orbit towers pass the lawfulness gate for their OWN ψ₀′
  (48 twisted + 8 ξ = 1 dense controls — exactly the deterministic
  applicability counts of the sheet); Q2 AV 656/0;
* **Q3 TLAW 4,176/0 — THE CANDIDATE: the display holds with the letter the
  lift carries (z₁′ = −c′) on every ξ-twisted tower**, both pair blocks;
* **Q7 CHI 4,176/0 — the χ-ratio law c_base = c′·ξ^{D₁} EXACT, measured
  against measured** (no closed form in the comparison): the W-2 covariance
  carries the corner;
* Q4 PV / Q5 INT / TRS 4,176/0 each; Q6 LOC 0 (no δ₁ = 0 anomaly);
* Q8 COV met — min 6 δ₁ = 1 pairs and min 6 teeth pairs (ξ^{D₁} ≠ 1) per
  twisted block; Q9 WRONGLET: per-pair set equivalence EXACT on 3,816
  samples, total fires 1,576 > 0 (the wrong-letter form fails exactly where
  ξ^{D₁} ≠ 1 — the transport is sharp, not slack);
* Q10 XI1: the ξ = 1 dense slice reproduces the unchanged display (wave-18
  tie re-confirmed); CERT internal 0; ENG-GATE 0 new (full=False disclosed);
  SP bug-detector 0.

STATUS EFFECT of S3 alone (before S4): the ξ ≠ 1 orbit direction — where NO
corpus evidence existed — is now MEASURED-TRANSPORT-EXACT: the displays
change under the lift orbit by EXACTLY the χ-law, W-2 clause 3's prediction
degenerate at the corner. The S4 compose is earned per the seal condition.

## S4. THE COMPOSE (earned by S3; the shift-descent route)

Setting: the S1 corner (g₀ = 1, e₀ ≥ 2; at e₀ = 1 no Case II exists —
COR-3's degeneration, theorem-backed, outside this unit). Φ′ an orbit member
with residue c′; Φ″ := Φ₀^{e₀} + lift(c′)·π^{h₀} the STANDARD lift of
ψ₀^{(ξ)} = y + c′. Base facts as [IL S1]/[ILN] S0.2 (division algorithm by
monic keys, w₀ a valuation, res additive + kills strict π-excess), plus:

**[r1, F2 — notation, defined here at first use.]** The b₀-SPLIT, used by the
S4.1 branch table and by S4.2 and imported from wave-18 S1
(ITERLAWLIFT_CORNER_2026-08-08.md S1, a source of record above; it was used
in the r0 text without an in-note binding):

    b₀ = ĉ′·π^{h₀} + t₀,   deg ĉ′ < d₀, res(ĉ′) = c′ ≠ 0 (so w₀(ĉ′) = 0),
                            deg t₀ < d₀, w₀(t₀) ≥ h₀ + 1.

Existence and uniqueness given a choice of the lift ĉ′ of c′: w₀(b₀) = h₀ (S1)
lets one divide b₀ by π^{h₀}, take ĉ′ := any degree-<d₀ lift of the residue
c′ = res(b₀/π^{h₀}), and set t₀ := b₀ − ĉ′π^{h₀}, whose residue at level h₀
vanishes — i.e. w₀(t₀) ≥ h₀+1. "ĉ′π^{h₀}" is the b₀-MAIN part, "t₀" the
b₀-TAIL; the STANDARD lift Φ″ is the orbit member with ĉ′ = lift(c′) and
t₀ = 0 and all mids b_k = 0 (k ≥ 1).

**CONTENT (sub-lemma).** For monic Φ, the digits of dev(F, Φ) satisfy
w₀-content ≥ w₀-content(F). *Proof:* induction through the division step —
each subtraction removes lc(F)·x^i·Φ with lc(F) a coefficient of the current
remainder; w₀ is a valuation. ∎

### S4.1 LEMMA (TAIL-STAB) — the wave-18 open step, closed (proof REPAIRED at r1; statement byte-unchanged)

For X = a·Φ₀^m·Φ′^j (a ∈ O[x], deg a < d₀) put the LEDGER weight
ω(X) := e₁(e₀·w₀(a) + m·h₀) + j·γ₂, γ₂ = e₁e₀h₀ + h₁. Then in the double
development X = Σ_j A_jΦ′^j, A_j = Σ_i a_{ji}Φ₀^i (dev by Φ′ then Φ₀):

    (LEDGER)  every nonzero digit obeys e₁(e₀·w₀(a_{ji}) + i·h₀) + jγ₂ ≥ ω(X).

Hence w₂(X) ≥ ω(X), and for any read weight Γ < ω(X) every level-2 read of X
at Γ contributes 0 at every grid slot (on-line: strict-excess summands die in
res; off-line: C_j = 0; digit collisions: w₀ ultrametric, min bounds survive).

*Proof (r1).* Induction on the pair (m, deg a) in the LEXICOGRAPHIC order on
ℕ × ({−∞} ∪ {0,…,d₀−1}) — m first, then deg a, with deg 0 := −∞ (a zero
coefficient contributes no digit and generates no child). Lex products of
well-orders are well-founded, which is all the induction uses; the statement
is proved for every (a, m, j) with deg a < d₀, uniformly in j.

**Base m < e₀** (any deg a): deg(aΦ₀^m) ≤ (d₀−1) + (e₀−1)d₀ < e₀d₀ = deg Φ′,
so by dev uniqueness the double dev is the single digit a at (i, j) = (m, j):
(LEDGER) with equality.

**Step m ≥ e₀:** one pass of the orbit identity Φ₀^{e₀} = Φ′ − b₀ −
Σ_{k≥1}b_kΦ₀^k gives X = aΦ₀^{m−e₀}Φ′^{j+1} − ab₀Φ₀^{m−e₀}Φ′^j −
Σ_{k≥1} ab_kΦ₀^{m−e₀+k}Φ′^j, with b₀ = ĉ′π^{h₀} + t₀ split as above. Each
level-0 coefficient is a product a·b with b ∈ {1, ĉ′π^{h₀}, t₀, b_1, …,
b_{e₀−1}}, so deg(a·b) ≤ deg a + d₀ − 1 < 2d₀ and its Φ₀-redigit
a·b = r + qΦ₀ has deg r, deg q < d₀ with w₀(r), w₀(q) ≥ w₀(a·b) ≥
w₀(a) + w₀(b) by CONTENT. Every child is again of the lemma's shape.

**(A) THE CHILD CENSUS — seven genres** (this case list matches the genre
list of the r1 examples-first table under the explicit 9 ↦ 7 label mapping
displayed in the machine-leg bracket below; the two coordinates are read off
per row, then justified):

| # | child genre | a′ | (m′, j′) | m-descent | lex (m, deg a) descent | ω-gain ≥ |
|---|---|---|---|---|---|---|
| 1 | key | a | (m−e₀, j+1) | m′ ≤ m−2 | 1st coord | γ₂ − e₁e₀h₀ = h₁ > 0 |
| 2 | b₀-main r-digit | −r(aĉ′π^{h₀}) | (m−e₀, j) | m′ ≤ m−2 | 1st | **0** (the only 0-gain genre) |
| 3 | b₀-main q-digit | −q(aĉ′π^{h₀}) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁h₀ |
| 4 | b₀-tail r-digit | −r(a t₀) | (m−e₀, j) | m′ ≤ m−2 | 1st | e₁e₀ |
| 5 | b₀-tail q-digit | −q(a t₀) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁e₀ + e₁h₀ |
| 6 | mid r-digit, 1 ≤ k ≤ e₀−1 | −r(a b_k) | (m−e₀+k, j) | m′ ≤ m−1 | 1st | e₁ |
| 7a | mid q-digit, 1 ≤ k ≤ e₀−2 | −q(a b_k) | (m−e₀+k+1, j) | m′ ≤ m−1 | 1st | e₁(h₀+1) |
| 7b | **mid q-digit at k = e₀−1 (the TOP mid)** | −q(a b_{e₀−1}) | **(m, j)** | **NONE: m′ = m** | **2nd: deg a′ ≤ deg a − 1** | e₁(h₀+1) |

*The m′ column.* Read off the pass identity (a q-digit sits one Φ₀-power
above its r-digit). Rows 1–5 use e₀ ≥ 2 (the S4 setting; e₀ = 1 is COR-3's
degeneration, out of scope): m−e₀ ≤ m−2 and m−e₀+1 ≤ m−1. Row 6:
k ≤ e₀−1 ⟹ m−e₀+k ≤ m−1. Row 7a: k ≤ e₀−2 ⟹ m−e₀+k+1 ≤ m−1. Row 7b:
k = e₀−1 gives m′ = m exactly — the one m-preserving genre.

*Row 7b drops the second coordinate.* Its q-digit is nonzero only if
deg(a b_{e₀−1}) ≥ d₀, and then, using only deg b_k < d₀ (S1),

    deg a′ = deg q = deg(a b_{e₀−1}) − d₀ ≤ deg a + (d₀−1) − d₀ = deg a − 1.

So every one of the seven genres has (m′, deg a′) <_lex (m, deg a) and the IH
applies to every child.

*The ω-gains.* For a branch with factor b at Φ₀-exponent M = m−e₀+k and
w₀(b) ≥ β: gain(r-digit) = e₁[e₀(w₀(a′)−w₀(a)) + (M−m)h₀] ≥ e₁[e₀β −
(e₀−k)h₀] by CONTENT, and gain(q-digit) = gain(r-digit) + e₁h₀. Row 1:
b = 1, but j′ = j+1 adds γ₂ and the Φ₀-drop costs e₁e₀h₀, net h₁ > 0. Rows
2–3: β = h₀, k = 0. Rows 4–5: β = h₀+1. Rows 6–7: β = amin(k) with
e₀·amin(k) ≥ (e₀−k)h₀ + 1, forced by gcd(e₀, h₀) = 1 (e₀ | kh₀ ⟺ e₀ | k,
impossible for 1 ≤ k < e₀). Every gain is ≥ 0 and the ONLY zero is row 2.

**[r1 MACHINE LEG for (A)/(B) — the examples-first table.]**
`verification/openmath/liftcorner_tailstab_children.py`, output committed as
`liftcorner_tailstab_children_table.txt` (exit 0, ALL GREEN; independent of
the sealed battery, which is byte-untouched). 29 towers spanning p ∈ {2,3,5},
d₀ ∈ {1,2,3}, e₀ ∈ {2,3,4,5,6} (the e₀ = 2 boundary and e₀ ≥ 3 both), all
four lift genres (pure = Φ″, dense = tail + mids, mids-only, tail-only), plus
PE1's counter-instance verbatim as row CTR; 752 (a, m, j) probes; **2,668
child rows**. Its §3 genre summary reports NINE normalized labels, which map
onto the seven rows above exactly: `key` = 1, `b0-main-r/q` = 2/3,
`b0-tail-r/q` = 4/5, `mid[k<e0-1]-r` and `mid[TOP=e0-1]-r` both = 6 (same
bound m′ ≤ m−1), `mid[k<e0-1]-q` = 7a, `mid[TOP=e0-1]-q` = 7b. Observed lex
deltas per label: `m-DROP` for all eight non-7b labels, `degA-DROP` for all
220 instances of 7b; **0 children dropping NEITHER coordinate**. Observed
ω-gains per label agree with the table's bounds, with `b0-main-r` the unique
label whose gain set is exactly {0}. The 220 m′ = m children are ALL of
genre 7b, all with deg a′ < deg a, all at deg a ≥ 1, all at d₀ ≥ 2 (the (B)
predictions), min gain +2. Assertions A1 (lex descent on every child),
A2 (every m′ = m child is 7b with deg a′ ≤ deg a − 1), A3 (none at
deg a = 0), A4 (none at d₀ = 1), A5 (gain ≥ 0, zero only at row 2), and
A6 — (LEDGER) itself re-verified on the HONESTLY RECOMPUTED double
development (dev by Φ′, then each Φ′-digit by Φ₀) over 752 probes / 4,438
nonzero digits, minimum slack 0 (the equality thread realized) — all PASS.
The table is evidence for the case split, not a substitute for (A)–(C): it
is a finite battery, and the proof above is what carries the ∀.

**(B) The deg a = 0 stratum (the second coordinate's base) and the d₀ = 1
corner.** At deg a = 0 row 7b is EMPTY: deg(a b_{e₀−1}) ≤ 0 + (d₀−1) < d₀,
so its q-digit vanishes and the top-mid branch contributes only its r-child.
Hence at deg a = 0 EVERY child drops m, and the lex induction needs no
separate base for the second coordinate — it bottoms out on the m < e₀ base
alone. Two consequences worth recording: (i) at most deg a ≤ d₀−1
consecutive m-preserving steps can occur from any node, so the recursion is
equally a single induction on m with an inner chain of length < d₀; (ii) at
d₀ = 1 NO branch ever produces a q-digit (deg(a·b) ≤ 0 < 1 = d₀), so the r0
single-m induction was in fact valid exactly on the flat corner d₀ = 1 —
which is why no d₀ = 1 row could have exposed the defect, and why the
counter-instance below is at d₀ = 2.

**(C) The two consumers, re-closed on the lex order.** (i) *The induction.*
The IH is invoked only on the children of one pass; each is strictly lex-below
its parent by (A), so the appeal is legitimate. With the gains of (A) every
child satisfies (LEDGER) at its own ω(child) ≥ ω(X); dev-linearity (the
double dev of X is the digit-wise sum of the children's — polynomial devs
carry no carries) plus the ultrametric close then gives (LEDGER) for X.
(ii) *Termination/finiteness* (the job the false clause was doing). The
recursion tree is finitely branching — ≤ 2e₀+1 children per node (row 1,
rows 2–5, and ≤ e₀−1 realizations each of rows 6 and 7) — and by (A) has no
infinite path, hence is FINITE, so the dev-linearity sum is finite. Explicit
depth bound: ρ(m, deg a) := m·d₀ + max(deg a, 0) strictly drops along every
child edge (an m-drop of ≥ 1 costs ≥ d₀ and can restore at most d₀−1 in the
second coordinate; an m-preserving step drops the second coordinate by ≥ 1),
so every root-to-leaf path has length ≤ m·d₀ + d₀ − 1. The r0 bound
⌈m/e₀⌉ survives in its correct scope: it bounds the ω-EQUALITY thread, whose
only genre is row 2 (gain 0), which drops m by exactly e₀ per step. ∎

[This IS the shift-descent bookkeeping: one key up costs h₁, exactly the
χ-chain's descent step (GRTW2 §3.4 rem. 1); the window-calculus ledger ω is
the tail-weight bookkeeping ILNRES S5.1 priced. Machine mirror: Q3/Q4 — the
tail never reaches the read.]

**[r1, F1 — CRITICAL (PE1): what changed, and what did not.]** The r0 proof
asserted "Every child is again of the lemma's shape with m′ ≤ m−1 (strict
descent; termination)" and closed "The ONLY 0-gain branch is b₀-main's
r-digit, which also strictly drops m: the ω(X)-thread terminates in
≤ ⌈m/e₀⌉ passes." The first clause is FALSE at row 7b (m′ = m), so the
strong induction on m alone had no IH at that child and the finiteness claim
rode the same clause; PE1 graded this CRITICAL and the ledger dropped
(TAIL-STAB) to PROVED-MODULO-F1. The LEMMA STATEMENT is byte-unchanged. NEW
at r1: the lex order, the seven-genre census with its per-genre descent
column, the (B) deg a = 0 / d₀ = 1 analysis, and the (C)(ii) finiteness with
an explicit depth bound. UNCHANGED in content and re-verified by PE1
independently: the base case, the one-pass identity, all ω-gains (now
displayed per digit, hence sharper on rows 3, 5, 7 than r0's per-branch
lower bounds), the gain-0 census (row 2 only), CONTENT, dev-linearity, the
(LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill close, and the ⌈m/e₀⌉
equality-thread bound in its correct scope.

**[r1, F1 — the counter-instance's own descent chain, numerically.]** PE1's
instance: O = ℤ₂, d₀ = 2, e₀ = 2, h₀ = 1, Φ₀ = x²+x+1, b₀ = 2 (so ĉ′ = 1,
t₀ = 0, c′ = 1), b₁ = 2x (w₀ = 1 = amin(1)); Φ′ = Φ₀² + b₁Φ₀ + b₀ =
x⁴+4x³+5x²+4x+3. Take e₁ = h₁ = 1, so γ₂ = e₁e₀h₀+h₁ = 3 and
ω(aΦ₀^mΦ′^j) = 2w₀(a) + m + 3j. Root X = xΦ₀^2, i.e. (m, deg a) = (2, 1),
ω(X) = 2. One pass, its four nonzero branches (mid digits from
2x² = 2Φ₀ − 2x − 2, i.e. r = −2x−2, q = 2, negated by the identity's sign):

    key        → a′ = x      (m′,j′) = (0,1)  ω = 3  gain +1 = h₁        [m-DROP]
    b₀-main r  → a′ = −2x              (0,0)  ω = 2  gain  0            [m-DROP]
    mid[1] r   → a′ = 2x+2             (1,0)  ω = 3  gain +1 = e₁       [m-DROP]
    mid[1] q   → a′ = −2               (2,0)  ω = 4  gain +2 = e₁(h₀+1)
                                     [m′ = m = 2, deg a′ = 0 < 1 = deg a: row 7b]

The r0 induction stops dead at the fourth child. Under the lex order that
child, (m, deg a) = (2, 0), is expanded once more:

    key        → a′ = −2              (0,1)  ω = 5  gain +1             [m-DROP]
    b₀-main r  → a′ = 4               (0,0)  ω = 4  gain  0            [m-DROP]
    mid[1] r   → a′ = 4x              (1,0)  ω = 5  gain +1            [m-DROP]

— and NO mid q-child, exactly as (B) predicts at deg a = 0 (a·b₁ = −4x has
degree 1 < 2 = d₀). All six leaves sit at m ≤ 1 < e₀ = 2, i.e. on the base
case: the tree is 8 nodes, depth 2, well inside the (C)(ii) bound
m·d₀ + d₀ − 1 = 5. (This whole chain is machine-printed in §6 of the r1
table, digit for digit.) Independent tie (not via the recursion): the honest double
development of the root is

    xΦ₀² = (x−2)·Φ′ + (6x+2)·Φ₀ + (−2x+4),

digits at (j,i) = (1,0), (0,1), (0,0) with weights 3, 3, 2 against
ω(X) = 2 — (LEDGER) holds, slacks 1, 1, 0, and the equality thread is the
(0,0) digit, precisely row 2's gain-0 thread.

### S4.2 LEMMA (READ-EQ) — the Φ′-tower reads = the Φ″-tower reads

Every 2-read battery object (anchors φ_γ = π^{u₁}Φ₀^{s₁}K^{s₂}; pair
products φ_γφ_{γ′}; K = the tower's own key) has IDENTICAL level-2 reads
(weight, grid, every slot coefficient) on the Φ′- and Φ″-towers. *Proof.*
The towers share every read datum (reads, ψ₁, K₂, and the LETTER z₁′ = −c′
in ε₁) — only key bytes differ. (a) Anchors and δ₁ = 0 products are
π^uΦ₀^sK^S with s < e₀ < deg: single K-slot coefficient π^uΦ₀^s — identical
bytes, the key power never opened (any δ₂-carry is grid bookkeeping, no
reduction at the top level of a 2-read). (b) δ₁ = 1 products (g₀ = 1 ⟹
s₁+s₁′ ≤ 2e₀−2: EXACTLY one overflow): P = π^UΦ₀^{e₀+S₁″}K^{S₂},
ω(P) = Γ := γ+γ′ (the split identity γ = e₁(e₀u₁+s₁h₀) + s₂γ₂). One pass on
each tower; compare children. Key child π^UΦ₀^{S₁″}K^{S₂+1}: identical
bytes, ledger Γ+h₁ — strictly above on BOTH towers (reads 0 both; it is the
E₁ digit). b₀-main children: −π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} vs
−π^{U+h₀}lift(c′)Φ₀^{S₁″}K^{S₂}: single digits; their difference has
w₀(ĉ′−lift(c′)) ≥ 1 (both lift c′), ledger ≥ Γ + e₁e₀. Φ′-only children
(t₀, mids): ledger ≥ Γ+1, and by TAIL-STAB every digit they generate stays
> Γ. So the on-Γ-line digit content coincides; all deviations are strict
π-excess at their slots; res kills them and the ultrametric keeps w₂ = Γ and
the on-line status equal on both sides. Reads agree slot-by-slot. ∎

### S4.3 THEOREM (the corner discharge) and the two corollaries

**THEOREM.** For EVERY orbit member Φ′ (any residue c′ ≠ 0), the 2-read
ITER-LAW display holds on the Φ′-tower with the letter the lift carries:
c(γ,γ′) = z̄^{δ₂}·(z₁′)^{D₁}, z₁′ = −c′, all γ,γ′ ∈ W₂. *Proof.* READ-EQ
transports every anchor value, pair value and cocycle to the Φ″-tower; Φ″ is
a STANDARD-LIFT instance of the accepted class with ψ₀ ↦ ψ₀^{(ξ)} (same
(e,h,g) data, ψ₀^{(ξ)}(0) = c′ ≠ 0), where the ACCEPTED ITER-LAW gives the
display with its letter z₁′. ∎ [Machine: Q3 4,176/0.]

**COR 1 ((ITER-LAW-LIFT), the corner).** ξ = 1 slice (c′ = c₀): the display
holds UNCHANGED for every LAWFUL monic lift — the 2-read (ITER-LAW-LIFT) is
proved at g₀ = 1 ∧ δ₁ = 1, exactly where it was open (ITERLAW S7: only
PAIR-VAL Case II consumes Φ₁'s form; all other strata lift-form-free).
[Machine: Q10 + wave-18's 104,404/0.]

**COR 2 (the χ-covariance; RESCOPED at r1).** Across the HARNESS monic-lift
orbit of S1 the 2-read display transports by the letter alone: for every
orbit member Φ′ with residue c′ and ξ := c₀/c′,

    c_base(γ,γ′) = c′(γ,γ′)·ξ^{D₁}   for all γ, γ′ ∈ W₂.

*Proof.* The THEOREM applied on the Φ′-tower and on the base tower, plus
z₁ = ξ·z₁′ (S1) and the lift-independence of D₁ (S1/S2). ∎ This is the
corner-degenerate FORM that W-2 clause 3's value-layer transport predicts,
and (with Q9's sharpness) evidence that it is the true covariance there.
Nothing beyond the displayed identity on the harness orbit is claimed.
[Machine: Q7 4,176/0 measured-vs-measured; Q9 sharpness 1,576 fires exact.]

**[r1, F3 — WITHDRAWN identification + what is still owed for the W2-OPEN-1
tie.]** The r0 text said this corollary "is W-2 clause 3's value-layer
statement (W2-OPEN-1) RESTRICTED to the base junction at the corner — now
PROVED at this note's grade there, upgraded from instance-confirmed". That
identification is WITHDRAWN as underived (PE1 F3): no equivalence between
COR 2 and any slice of W2-OPEN-1 is derived anywhere in this note.
W2-OPEN-1 as recorded (GRTW2 §5.3) quantifies over the committed
value/cocycle battery — K5/K6/K7, K12 = π-shift/ρ-monodromy, K1–K4/K13
riding — WITH THE TRANSPORTED CLASSIFIER LIFTS substituted for the harness
lifts. Two things are therefore owed before even the base-junction slice of
that statement may be claimed, and NEITHER is in this note: **(a) an
orbit-membership display** — that the transported CLASSIFIER key at the base
junction is an S1 orbit member (monic, degree e₀d₀, w₁ = e₀h₀, nonzero
order-1 residual y + c′), which needs the GMN key-polynomial normalization
plus W2-C3(ii), not merely the harness parametrization this note uses;
**(b) the battery legs outside the display/anchor families** — K12 above
all — under the restriction. Until both are displayed, COR 2 is a statement
about the harness monic-lift orbit only. The unit's W-2 grade cap (grade
box) is unaffected: it was and remains driven by S1's and this corollary's
consumption of clause 3's FRAMING.

**PROP (propagation to every level — the S0.1 rider leg).** (ITER-LAW-n)
for every lawful monic Φ₁ at the corner, all n: the [ILN] chain consumes
Φ₁'s explicit bytes only through (i) monicity/degree/w₁Φ₁ = e₀g₀h₀ (shared
by every orbit member) and (ii) the level-1 base package (= [IL], replaced
here by COR 1; at n = 1 clause (ii) is ITERLAW S7's own display). Riding
S0.1's verbatim propagation, the discharge lifts to every rung AT [ILN]'s
OWN conditionality (T-class/(RM-m)/DCX ledger unchanged). VERIFY-TARGET for
the arc: the clause-(ii) census at rungs ≥ 2 (no rung leg opens Φ₁'s bytes
outside the level-1 package) is cited from the [ILN]/ILNRES consumption
tables, not re-proved here.

**Grade box + W-2 consumption census (the cap).** This note: ATTEMPT 0/2 —
r1 is a REPAIR round, not a pass; one hostile pass has run (PE1: 1 CRITICAL
+ 3 gaps, all four repaired here) and the arc is OWED on THIS text. Charge
(r1-updated; the r0 charge list named neither the step that broke nor the
r1 argument — PE1 F1's closing observation, accepted): **(1) the S4.1
seven-genre child census's COMPLETENESS** — that the pass identity, after
the b₀-split and the r/q redigit, produces no branch outside rows 1–7 — and
the row-7b degree drop; **(2) the lex-order finiteness argument** ((C)(ii):
finite branching + the ρ depth bound); **(3)** the CONTENT sub-lemma's
base-fact status; **(4)** the READ-EQ on-line-content/ultrametric close;
**(5)** PROP's census cite; **(6)** COR 2's rescoped statement (the F3 box's
(a)/(b) are owed for any W2-OPEN-1 tie, and are NOT part of this note's
claim). W-2
consumption: COR 2 and the S1 orbit frame consume GRTW2 clause 3 (the
ψ-transport definition + its corner degeneration) — GRTW2 is itself 0/2, so
**the unit's grade is CAPPED at that consumption, as charged**. Honest
decoupling fact the arc may use: the COR 1 chain (TAIL-STAB + READ-EQ +
accepted ITER-LAW) is W-2-free — if W-2's arc lags, the ξ = 1 discharge
stands on this note's own arc alone.

## S5. Consequence display (what [ILN]'s rider becomes; at the capped grade, pending arcs)

ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or accepted text is
edited now): ITERLAWN S0.1's rider "(ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; nothing is claimed for any non-canonical lawful lift at any
level" becomes, on the Φ₁ axis: "(ITER-LAW-LIFT) DISCHARGED at attempt grade
(capped by the W-2 0/2 consumption; ξ = 1 core W-2-free): ITER-LAW-n holds
for EVERY lawful monic Φ₁, every n, at [ILN]'s own conditionality, and
covariantly for the full Φ₁-orbit by the χ-law". NR-1 then leaves the
ILNRES residual list; the T-class(n) conditionality of record shrinks to
NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said plainly:
non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a separate
corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s displayed
statement (wave-18 S0), stays open as its own priced item.

**STATUS LINE (r1-honest; supersedes the r0 sentence "The wave-18 sketch's
one open step (TAIL-STAB) is CLOSED by S4.1 (its ω is this ledger; the
monomial form is subsumed); wave-18's price sheet is settled in full").**
As of repair round r1: (TAIL-STAB) is PROVED by S4.1 AS REPAIRED — the r0
proof's strict-descent clause (m′ ≤ m−1 at every child) was REFUTED by PE1
at the top-mid q-child (m′ = m), the lemma STATEMENT is byte-unchanged, and
the argument now rides the lexicographic (m, deg a) descent over a
seven-genre child census derived from the committed examples-first table
(`liftcorner_tailstab_children.py` / `..._table.txt`). Its ω is this ledger
and wave-18's monomial form is subsumed, as r0 said. Grade: **attempt 0/2**
— PE1 was a hostile pass but returned 1 CRITICAL, so no acceptance credit
accrued; the r1 argument itself has NEVER been hostile-read, and the grade
box's charge (1)–(2) names exactly which of its steps are unaudited. So:
wave-18's price sheet is settled MODULO this note's own arc, not "in full".
The three r1 gap repairs, for the record: ĉ′/t₀ now defined in-note (F2);
COR 2's W2-OPEN-1 identification WITHDRAWN and rescoped, with (a)/(b) owed
(F3); S2 disclosure (c) corrected to what the runner actually asserts (F4).
Everything downstream of (TAIL-STAB) — READ-EQ, the THEOREM, COR 1, PROP —
stands exactly as PE1 verified it GIVEN (TAIL-STAB), and the corner
measurement (S3, the covariance carrying the corner) is machine fact,
untouched by F1 in either direction.

— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
repair round r1 applied 2026-08-08 campaign (wallclock 2026-08-05).
