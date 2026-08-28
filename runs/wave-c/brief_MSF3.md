# UNIT MSF3 — lift tails: MSF at j ≥ 3 first; then SR; then WASH-n (n ≥ 5) via the grade-shift pairing handle

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

The chapter-H one-grade-lifting core is documented in
docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md (post-MLFIX/MLF2/FML1 state;
codex-verified ACCEPT). Landed there: U(n|F) unconditional through n = 4 over any DVR,
target-free via Lemma BP′; the μ ≥ 2 frame condition proved SHARP by a constructed μ = 1
counterexample at q = 3; MSF proved at grades j ≤ 2 (Lemma MSF-LOW, §6.2d); the cofactor
block eliminated exactly (REM); the CRT constant pinned (RES). Numeric certificates
C1–C15 in verification/ all pass. The HONEST OPENS (§6.6 area, ~line 659):

- **MSF (mixed-secant flag rigidity) at j ≥ 3**: `V_j(D_{x,y}) = V_j(T_x)` for the
  relevant j — proved only for j ≤ 2; first possible failure j = 3 (matches SCHED-LOW).
- **SR (secant realization)**: the actual differences κ = x − y occurring with the right
  spread — SEC + MSF gives only `image(ω_n) ⊆ V_n(T_x)`; SR supplies the reverse
  inclusion. Neither MSF nor SR follows from TDC or the current MSMITH interface (tangent
  maps at presentations, not mixed secants).
- **WASH-n for n ≥ 5** (deep MLIFT-1): the identified HANDLE is the grade-shift pairing
  conjecture — locate its exact statement in the doc and treat it as the entry point.

## Your charge

1. READ the doc in full: Lemma MSF-LOW's proof mechanism (§6.2d), Lemma WASH (§5.6/§ around
   line 452) and its sharp failure fence, Lemma BP′, the SCHED-LOW scheduling analysis,
   and the FML1 verdict (runs/wave-b/ — grep FML1/VLIFT).
2. ATTACK MSF j ≥ 3 first. Examples-first: extend the existing battery
   (runs/wave-b/h116b4_battery.py and the C1–C15 certificate scripts in verification/)
   to compute mixed-secant flags at j = 3, 4 across q ∈ {2, 3, 5} and the doc's frame
   genres — including the μ = 1 and q = 3 regimes that earlier scans were structurally
   blind to (the FML1 meta-finding). Read the mechanism off the table; derive the case
   split; prove or refute. A CONSTRUCTED counterexample at j = 3 is a fully valuable
   outcome (it reshapes the induction) — derive the simultaneous-defeat equations from
   MSF's statement and solve or prove infeasible, rather than blind sweeps.
3. Then SR (same examples-first discipline), then the grade-shift pairing conjecture for
   WASH-n ≥ 5 — state it precisely, certify numerically at n = 5, 6, and prove what you
   can; partial reductions (e.g. pairing ⟹ WASH-5) are valuable and should be proved as
   conditionals.
4. Every new general claim gets a numeric certificate (new C16+ scripts in verification/,
   python3+sympy). State parameters swept and case counts.

## Deliverables

- Dated `[MSF3 2026-08-28]` section APPENDED to
  docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md, doc-rigor proofs, OPEN rows updated
  only by appended status markers (`[MSF3: PROVED/PARTIAL/REFUTED/BLOCKED]`).
- `runs/wave-c/verdict_MSF3.md`: per-item status (MSF-j≥3 / SR / pairing / WASH-n), each
  claim PROVED / REFUTED-BY (with the counterexample) / PARTIAL (exact remaining gap) /
  BLOCKED-BECAUSE; certificate run summary.

## Rules

No git commits. Rigor is paramount; battery patterns are conjectures until proved.
Honest partials beat papered gaps. Published cites only, precise theorem numbers.
