# (ITER-LAW-LIFT) CORNER PROBE — general lawful lifts at g₀ = 1 ∧ δ₁ = 1: the degeneration-shaped attempt (PROBE-FIRST; two-commit seal)

Unit chartered by SYNTHESIS PASS 8 queue #5 (docs/SYNTHESIS_PASS8_2026-08-08.md
S4-5, per S3(iii)'s narrow ACCEPT of the D-REAL degeneration trick at this
corner): "(ITER-LAW-LIFT) corner attempt at g₀ = 1 ∧ δ₁ = 1 via degeneration
(math, S/M). Probe-first: measure general-lawful-lift vs standard-lift cocycle
deltas at the trivial-extension corner (z₁ scalar); attempt only on an exact
measured law." Genre: sealed-preregistration numerics + (conditional on a
0-violation verdict) a PROOF SKETCH — **not a claimed proof**. Wallclock
2026-08-03, campaign date 2026-08-08.

FENCES: no edit to the accepted ITERLAW_2026-08-08.md (acceptance brackets
byte-frozen), to DITER_RESTATE_2026-08-08.md, or to the sealed falsifiers
`iterlaw_check.py` / `iterlaw_cor4_mixed.py`; no Lean statement changes; no
orders-≥ 3 claim; no gr(w₂)-wrapper claim; NOTHING here upgrades the residual —
a green verdict makes the corner MEASURED-LAWFUL-EXACT (instance evidence where
before there was NONE outside the standard-lift class), and the sketch prices a
wave-19 compose; the residual closes only when that compose is accepted.

## S0. The residual under attack, and the acceptance citation of record

The target is the first of the accepted ITER-LAW's three residuals. Acceptance
citation, PASTED from the ledger's defined-term block
(`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, "ITER-LAW ACCEPTED —
2026-08-03"):

> Scope as accepted: the harness
> tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence
> restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1;
> gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3 untouched.

The residual's own display (ITERLAW_2026-08-08.md S7, first bullet): only
PAIR-VAL Case II consumes Φ₁'s explicit form (the standard lift's exact
two-term shape at g₀ = 1); for a general lawful monic lift the g₀ = 1 ∧ δ₁ = 1
stratum needs a development-reduction induction — the honest OPEN displayed
lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁. All
52 + all JUNCFORGE instance towers are standard-lift, so before this probe NO
instance evidence exists outside the proved class.

## S1. The lawful-lift class at the corner (derived; the probe's parameter space)

Pinned class (TR3-S2 S0, the standing lawful-monic-lift definition): Φ₁ monic,
deg Φ₁ = e₀g₀d₀, w₁(Φ₁) = e₀g₀h₀, order-1 residual condition R_{λ₀}(Φ₁) ∼ ψ₀.
Specialize to g₀ = 1 (so ψ₀ = y + c₀ monic degree 1, c₀ = ψ₀(0) ≠ 0, K₁ = K₀,
z₁ = −c₀ a scalar). Write the Φ₀-development Φ₁ = Φ₀^{e₀} + Σ_{k=0}^{e₀−1}
b_k Φ₀^k, deg b_k < d₀. Then (derivation, three steps, each elementary):

1. The top digit (k = e₀, b = 1) contributes e₀·0 + e₀h₀ = e₀h₀ to
   w₁ = min_k(e₀w₀(b_k) + kh₀), so w₁(Φ₁) = e₀h₀ ⟺ every lower digit satisfies
   e₀w₀(b_k) + kh₀ ≥ e₀h₀.
2. On-line digits (equality) need e₀ | (e₀−k)h₀, and gcd(e₀,h₀) = 1 forces
   e₀ | k: only k = 0 and k = e₀ can sit on the line. So for 1 ≤ k ≤ e₀−1 the
   constraint is w₀(b_k) ≥ ⌈(e₀−k)h₀/e₀⌉ =: amin(k), automatically STRICT
   (the bound is non-integral), i.e. every mid digit is strictly above the line.
3. The level-1 residual polynomial at β = e₀h₀ (eq-12 data s = 0, u = h₀; grid
   abscissas 0, e₀) is R = y + res(b₀/π^{h₀}). Both R and ψ₀ are monic degree
   1, so the class condition R ∼ ψ₀ DEGENERATES TO EQUALITY at this corner:
   w₀(b₀) = h₀ exactly and res(b₀/π^{h₀}) = c₀. (If w₀(b₀) > h₀ then R = y,
   not ∼ ψ₀ since c₀ ≠ 0.)

So the FULL lawful-lift freedom at g₀ = 1 is: (i) the b₀ tail — b₀ = ĉ′π^{h₀}
+ (anything of w₀ ≥ h₀+1), ĉ′ any lift of c₀; (ii) the mid digits — any b_k
with w₀(b_k) ≥ amin(k), 1 ≤ k ≤ e₀−1. The standard lift is b₀ = ĉπ^{h₀},
b_k = 0. The probe's variant generator (runner V1–V5) spans exactly (i)+(ii),
including every digit simultaneously at the MINIMAL lawful valuation (V3) —
the closest-to-the-line, maximal-recursion extreme.

## S2. The candidate and the degeneration rationale (sealed pre-run)

**CANDIDATE.** The accepted display holds UNCHANGED for every lawful lift at
the corner: for γ, γ′ in the anchor window of the tower built on ANY lawful Φ₁,

    c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′)+ℓ₀γ₂δ₂)/e₀}.

**WHY lift-independence is predicted (the S3(iii) degeneration argument, said
exactly).** At g₀ = 1 the level-1 extension is trivial and z₁ enters as a
scalar: z₁ = −ψ₀(0) = −c₀ ∈ K₀. The Case-II reduction step for a general
lawful lift reads Φ₀^{e₀} = Φ₁ − b₀ − Σ_{k≥1} b_k Φ₀^k, and S1 shows
lawfulness PINS the one on-line datum: the correction's on-line part is
−ĉ′π^{h₀} with res(ĉ′) = c₀, so the residue the weight-γ″ read extracts is
−c₀ = z₁ — **the residue −ψ₀(0) = z₁ is lift-covariant and cancels**: it is
the SAME constant the standard-lift Case II produced, for every lawful lift.
Every other piece of the lift freedom (the b₀ tail, all mid digits) sits
STRICTLY above the line (S1 steps 2–3), and strictly-above digits read 0 in
the exact-ordinate weight read; the denominators val(φ_{γ+γ′}) and the
Case-I/anchor legs are single-digit developments consuming only monicity +
degree (ITERLAW S7: L1–L6, EXP, Case I, S5, S6 are lift-form-free). Hence the
cocycle comparison general-vs-standard is a ratio of identical scalars: 1.

**THE ONE HONEST OPEN STEP (what the probe CANNOT decide; the sketch's gap).**
When the correction tail multiplies Φ₀^{S₁″+k} with S₁″+k ≥ e₀, the reduction
RE-ENTERS itself (the "development-reduction induction" of the residual's
display): the recursion generates new digits, and the argument needs the
invariant "every digit generated by re-reducing a strictly-above-the-line term
stays strictly above the line" (each pass exchanges Φ₀^{e₀} for Φ₁-slot weight
γ₂ − e₀e₁h₀ = h₁ > 0 up, or multiplies by correction data of w₁-weight ≥
line + 1). Variants V3 (all digits minimal) and V5 (top-adjacent digit) are
designed to maximize exactly this recursion; row CE (e₀ = 5) gives it four
mid digits to spread over.

## S3. Probe design (roster, windows, controls — the seal)

Runner: `verification/openmath/iterlawlift_corner.py`, committed WITH this
header BEFORE any run (two-commit seal; the run verdict lands at commit 2 in
S6 below). Full roster/variant/prediction display in the runner docstring —
of record there; summary: 6 fresh rows (all g₀ = 1; tuples fresh vs the
grb A–J, strata K–N, iterlaw P–X, COR-4 Y/Z rosters; E₂ ∈ {3,4,6,6,8,10} —
two rows ≥ 8 per the charter), × 4 rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}, × 12
lift variants (V0 standard + 11 general-lawful draws spanning S1's freedom),
own seed 20260903; windows W1 and W1+7E₂ with the MIXED pair block in the
first battery (the COR-4 lesson); families P1–P8 + CERT preregistered in the
docstring verbatim (LAWCERT gate / ANCHOR-VAL / **LAW = the candidate** /
PAIR-VAL+shape / integrality / δ₁=0 localization / coverage / four mutation
controls M1–M4, each with a deterministic applicability argument). PREDICTED:
every family 0 violations, coverage met, controls fire 4/4 rings each.

## S4. Verdict

**ALL GREEN, FIRST RUN, exit 0** — full block at S6 (commit 2; the sealed
runner byte-untouched, md5 `2ec3a152181d30933c6758e1ff133285` == seal 7537b40).
The candidate measured EXACT: the accepted display holds unchanged on all
104,404 samples across 288 lawful-lift variant towers, 0 violations in every
family; the 0-violation condition for the S7 proof sketch is MET.

## S5. What this unit does NOT do

No proof claim at any grade (the sketch, if earned, is a priced route, not an
attempt). No status change to (ITER-LAW-LIFT) — the residual stays OPEN; every
citation of the accepted ITER-LAW continues to carry all three residuals
verbatim from the ledger block quoted in S0. No edits to accepted records, no
Lean work, no consumer re-pointing. The e₀ = 1 leg is not probed (no Case II
exists there — COR-3's degeneration, already theorem-backed); the E₂ = 1 leg
is outside the statement of record per the S0-erratum scope.

## S6. VERDICT (post-run; commit 2; seal commit 7537b40, runner byte-untouched)

**ALL GREEN, FIRST RUN, exit 0** — 104,404 total samples, **0 violations in
every family**, seed 20260903:

* P1 LAWCERT 288/288 variant towers pass the lawfulness gate (0 rejects — the
  generator hit the lawful class exactly, incl. every all-digits-minimal V3);
* P2 AV 3,552/0 (ANCHOR-VAL, lift-free leg confirmed on every variant);
* **P3 LAW 25,056/0 — THE CANDIDATE: the accepted display holds UNCHANGED on
  every lawful lift at the corner**, both pair blocks (W1×W1 and the mixed
  W1×W3) on all 288 variants;
* P4 PV 25,056/0 (both L7 forms + the single-slot y^{δ₂} shape clause survive
  general lifts — the correction tail never reaches the read);
* P5 INT 25,056/0; TRS transcription control 25,056/0; P6 LOC 0 (no δ₁=0
  anomaly anywhere); P7 coverage MET — 288/288 blocks with δ₁=1 pairs (min 6,
  max 80; E₂ = 8 and E₂ = 10 rows on roster);
* P8 controls 4/4 rings EACH: M1 unlawful-residue swap fires 12/12/12/12 (every
  δ₁=1 pair of the CB block, as predicted); M2 below-line gate flag 1/1/1/1;
  M3 fibration-term drop fires 9/9/9/9 (every δ₂=1 pair); M4 outer-carry drop
  fires 16/16/16/16 (exactly the 4×4 s₂=1×s₂=1 pairs of the CC window —
  the predicted deterministic counts on the nose);
* CERT 324/0 on the base towers (T1/T2/T5 + T11 PARI factorpadic fired on the
  ℤ_p instances); harness bug-detector counters 0.

Of record: `iterlawlift_corner_output.txt`, `iterlawlift_corner_results.json`
(these govern on any transcription discrepancy). Lift-parameter coverage: the
b₀ tail (V1, incl. ĉ→ĉ+πr), single mid digits at minimal lawful valuation
(V2), ALL digits minimal simultaneously (V3), deep random tails (V4),
top-adjacent k = e₀−1 (V5) — over d₀ ∈ {1,2}, e₀ ∈ {2,3,4,5}, all four rings.
STATUS EFFECT (honest): (ITER-LAW-LIFT) remains OPEN; the corner is now
MEASURED-LAWFUL-EXACT (first instance evidence outside the standard-lift
class: 264 general-lawful-lift towers, 0 violations), and the S7 sketch is
earned per the seal's own condition.

## S7. PROOF SKETCH (earned by the 0-violation verdict — NOT a claimed proof)

The degeneration argument written out; ONE honest open step, named and priced.

**Perimeter already proved (accepted, lift-form-free).** ITERLAW S7 first
bullet: L1–L6, Lemma EXP, PAIR-VAL Case I, the S5 assembly and S6 corollaries
consume only "Φ₁ monic of degree e₀g₀d₀". So (ITER-LAW-LIFT) reduces to:
PAIR-VAL Case II (g₀ = 1, δ₁ = 1) for a general lawful Φ₁.

**Step 1 (the generalized two-term decomposition).** By S1, a lawful lift is
Φ₁ = Φ₀^{e₀} + b₀ + Σ_{k=1}^{e₀−1} b_k Φ₀^k with b₀ = ĉ′π^{h₀} + t₀
(res(ĉ′) = c₀, w₀(t₀) ≥ h₀+1) and every mid digit strictly above the line.
Substituting Φ₀^{e₀} = Φ₁ − b₀ − Σ b_kΦ₀^k into P = π^U Φ₀^{e₀+S₁″} Φ₁^{S₂}:

    P = π^UΦ₀^{S₁″}Φ₁^{S₂+1} − ĉ′π^{U+h₀}Φ₀^{S₁″}Φ₁^{S₂}
        − t₀π^UΦ₀^{S₁″}Φ₁^{S₂} − Σ_{k≥1} b_k π^U Φ₀^{S₁″+k}Φ₁^{S₂}.

Term 2 is the standard-lift on-line digit UP TO the lift of the residue: its
γ″-read residue is −res(ĉ′) = −c₀ = z₁ — lift-covariant, the SAME constant as
the accepted Case II. Terms 1, 3, 4 have nominal weight > γ″ (term 1: +h₁;
term 3: ≥ +e₀e₁; term 4: ≥ +1, by the strict mid-digit bound of S1).

**Step 2 (THE ONE OPEN STEP — displayed lemma (TAIL-STAB)).** For a monomial
X = π^aρΦ₀^mΦ₁^j (ρ a unit-residue digit, m possibly ≥ e₀) define the nominal
weight ω(X) := e₁(e₀a + m h₀) + jγ₂. **(TAIL-STAB):** if ω(X) > γ″ then every
digit of the Φ₁-development of X reads 0 at the weight-γ″ read. Route: double
induction — m strictly descends under one reduction pass (Φ₀^{e₀} ↦ Φ₁ − b₀ −
Σb_kΦ₀^k sends m ↦ m−e₀, m−e₀, m−e₀+k), while ω is non-decreasing along every
branch (the Φ₁ branch gains γ₂ − e₀e₁h₀ = h₁ > 0; the b₀-tail branch gains
≥ e₀e₁; the mid-digit branches gain ≥ 1; the b₀-main branch preserves ω
exactly but strictly drops m). At terminal m < e₀ the term is a literal digit;
ω > γ″ there means strictly above the line, and dev-linearity + "res at the
exact ordinate kills higher-valuation summands" transfers this through sums
(cancellation only raises valuations — min-weight bounds survive). Term 2's
descendant is the unique ω = γ″ thread and terminates at the on-line digit of
residue z₁ in ONE pass (m = S₁″ < e₀). This is exactly the
"development-reduction induction" the accepted note's scope box priced.

**Honesty box.** (TAIL-STAB) is UNPROVED — it is the entire distance between
this sketch and a proof note. Everything else above is either accepted content
(the lift-free perimeter) or the one-line lawfulness pin of S1. The sketch
consumes NO print, NO extraction — pure harness-calculus bookkeeping, the
TR3-S2 Lemma-EXP genre.

**Price for the wave-19 compose.** S/M: one displayed lemma (TAIL-STAB, double
induction, elementary), one substitution display (Step 1), then Case II′ =
verbatim Case II with ĉ′ for ĉ; falsifier ALREADY EXISTS (this sealed runner
re-runnable at fresh seeds/rows for the note's own battery), measured cover
104,404/0 on file. Acceptance bar as usual (hostile passes, model-diverse).

— (ITER-LAW-LIFT) corner probe unit, campaign date 2026-08-08 (wallclock
2026-08-03). SEAL COMMIT 7537b40 (pre-run); verdict + sketch at commit 2.
