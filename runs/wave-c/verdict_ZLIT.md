# VERDICT — UNIT ZLIT2: literature classification of the resultant-depth law

**Date:** 2026-08-26 · **Agent:** fresh finisher (ZLIT2) · **Status:** IN PROGRESS

## The result to classify

For two independent uniform random monic polynomials f (deg n₁), g (deg n₂) over a
complete DVR with residue cardinality q, with m = min(n₁,n₂), s = 1/q:

- Generating function: Σ_v P[v(Res(f,g)) = v] t^v = ∏_{j=1}^m (1−s^j t^{j−1})/(1−s^j t^j)
- Mean: E[v(Res)] = Σ_{j=1}^m 1/(q^j − 1)

(Battery-verified integer-exactly; derivation via Weierstrass/localization recursion.)

Classification target: (a) known / (b) new proof of known / (c) claimed new.

## Search budget

At most 8 WebSearch calls; findings appended immediately after each.

## Findings table

| # | Query angle | Query | Finding |
|---|-------------|-------|---------|

## Classification

(pending)

## CLOSED PENDING (orchestrator, 2026-08-31 09:35)

Both lookup agents (ZLIT, ZLIT2) hung in the web-search phase with no findings written —
the search tooling appears unreliable in this session. CLASSIFICATION STANDS AT:
**(c?) pending lookup** — novelty neither claimed nor ruled out. The Lean proof of the
min=1 law and the battery-verified general Z_m form are unaffected (they are corpus
theorems + a verified conjecture-shape regardless of novelty). ACTION FOR THE OWNER /
a future session with working search: run the four search angles in this file's charge;
the t = 0 specialization (coprimality probability 1 − 1/q over O, cf. the classical
F_q[x] coprimality 1 − 1/q) and the Evans elementary-divisor genre are the fastest
checks. Queued as a REVIEW_QUEUE-adjacent note, not a Tier-1 row (no cite depends on it).
