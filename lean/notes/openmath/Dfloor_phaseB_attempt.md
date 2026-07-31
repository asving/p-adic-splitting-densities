# Dfloor — the assembly floor (D-1 + D-2 + D-4) — Phase-B attempt record (Fable, 2026-07-31)

Unit: the three "assembly floor" nodes of `docs/MATH_COMPLETION_TREE_2026-08-01.md`
§D1.2, attacked as ONE unit per the DELTA-1 attack order (slots 6–7):

* **D-1 (MEAS-BRIDGE)** — the complete Haar/counting bridge (V6 finding 1:
  the tree silently assumed it; now written as one quantified proposition).
* **D-2 (SUM-ONE)** — exactly-one-type partition + ns-null + Σ_σ α = 1 +
  the rational-function identity principle ⟹ Σ_σ R_σ = 1 in ℚ(t).
* **D-4 (BASE-CASES)** — n = 1 in full, degree-0/empty-product conventions,
  terminal-leaf conventions (V6 finding 4).

Deliverable (the verification target; SELF-CONTAINED):
`lean/notes/openmath/Dfloor_phaseB_verifybrief.md`. This file is the working
record only.

## 1. What is proved (headline)

All three nodes are DISCHARGED at assembly grade — full proofs, no new
mechanism needed (as the tree predicted), with these strengthenings over the
tree's stated clauses:

* D-1(iv) is proved EXACT for the root (U-GEN)'s strict decided convention
  (⋃_N D_σ(N) = L_σ on the nose), not merely up-to-null; the up-to-null form
  is exactly what survives for M05's LAX convention, and BOTH conventions are
  proved with explicit deltas (the "up to a Haar-null set" in the tree's
  clause (iv) is thereby explained: it is the lax convention's residue).
* The bracket (U-GEN)(i) and qualitative + quantitative semantic drainage
  (U-GEN)(ii) fall out as corollaries (BRACKET, SEM-DRAIN, SEM-DRAIN-RATE),
  unconditional at every prime including wild — the semantic side only; the
  OM-classifier side stays with O-1..O-5/O-4 as before.
* D-1(v) (the density limit) needs NO drainage hypothesis: continuity from
  below alone identifies lim decided_σ(N)/p^{nN} = α(n,σ;p).
* D-2 clauses (iii)–(iv) are stated hypothesis-explicitly (Theorem TRANSFER:
  any infinite prime set P where α = R_σ(p) pointwise forces Σ_σ R_σ = 1 in
  ℚ(t)); instances: n = 1 and n = 2 UNCONDITIONAL (BASE-1; the VERIFIED-LEAN
  n = 2 capstone), general n conditional exactly on the T-U ledger with
  P = (REG-p) primes (infinite by K-13).
* D-4 delivers the full uniformity root at n = 1 unconditionally (BASE-1),
  the degree-0 floor (BASE-0), type additivity over coprime families
  including the empty family (Lemma ADD), and the convolution algebra with
  its unit ⊛_∅ = δ_∅ as proved conventions (C0)–(C1). (C2)'s (τ-irr)/(τ-hen)
  clauses at degree > 1 are FIXED AS CONVENTIONS with their semantic
  correctness explicitly fenced to O-5 — only the degree-≤1 instances are
  proved (Lemma LIN).

## 2. Imports consumed (exact statements in brief §2)

I-1 = M05 Lemma D (local constancy at 2v+1; V2-upheld, wild-valid) — the ONE
substantive input to D-1(iv)/(i). I-2 = K-11's e·f = deg (over LIT-2,
V3-audited). I-3 = M05 Lemmas B+C tail bound + null locus (V2-upheld; null
clause ALSO re-proved self-containedly in the brief's Appendix A — the
qualitative package stands on I-1 + I-2 alone). I-4 = K-13 (REG-p cofinite;
instance remarks only). I-5 = n = 2 Lean capstone values + sealed n = 3 R_σ
(instances and falsifier only). No LIT-3/LIT-4/LIT-5, no O-1..O-5 content,
no T-1..T-9 content is consumed anywhere.

## 3. Falsifier (run FIRST, before the brief was finalized)

`verification/openmath/dfloor_checks.py` — pure Python, exact arithmetic;
ground truth = ONLY the classical square-class classification of quadratics
over ℚ_p. Results: `verification/openmath/results/dfloor_results.json`,
**ALL PASS, 0 failures** (2026-07-31, this machine).

* T-A exhaustive n = 2 census at p ∈ {2,3,5} (N ≤ 7/4/3): partition,
  per-class nesting (clause (iii)), the BRACKET against the known R_σ(p),
  the SEM-DRAIN-RATE envelope, monotone undec.
* T-B: every undecided class certified by an explicit witness pair of lifts
  with distinct verdicts (or an exact nonseparable lift) — the exact decided
  criterion (brief Prop N2) is not trusted, it is checked both ways.
* T-C: Krasner cross-check — every class with a center lift satisfying
  2v+1 ≤ N is decided with that verdict (I-1's n = 2 instance, exhaustive).
* T-D: independent closed-form counts at p odd + the exact geometric-series
  limit p/(2(p+1)) — an end-to-end analytic instance of D-1(v).
* T-E: Lemma D perturbation test, 3000 f × 8 perturbations per prime at
  modulus 2v+1: 0 violations. (Probe at 2v: also 0 found by random sampling
  at n = 2 — reported only; the proved constant stays 2v+1.)
* T-F: Σ_σ R_σ = 1 exact at q = 2..200 for the n = 2 table and the sealed
  n = 3 table.
* Observed and recorded: strict undec(N) = p^{−N} EXACTLY at n = 2 for all
  tested (p, N) — at p odd this is provable from Prop N2.

## 4. Honest fences (what this unit does NOT close)

* Nothing about the OM classifier's own counts: the O-4 OL1-ii agreement
  seam, O-1/O-2/O-3/O-5, rates (OL2) — all untouched, as scoped.
* The α = R_σ(p) tie at general n: T-U + the §2.3 kernel ledger; D-2's
  general-n instance is conditional exactly on that (stated on-node).
* (C2) terminal conventions at block degree > 1: O-5's (τ-irr)/(τ-hen)
  clauses — conventions pinned here, correctness there.
* D-3 (unramified bases): only the free n = 1 remark is recorded.
* The Lean `decided`/`hExhaustP` faithfulness tie to the strict/lax
  conventions: K-12's recorded audit duty (tree §D1.5(g)), flagged again.

## 5. Status + verification protocol

Per the standing discipline: **PROVED-UNVERIFIED** (this attempt has had no
fresh-context adversarial pass). Suggested verification charge is in the
brief's §9 — hand the verifier `Dfloor_phaseB_verifybrief.md` ALONE (it is
self-contained). Highest-value pokes: Prop H1's compactness/π–λ
bookkeeping; the strict-vs-lax deltas in MEAS-BRIDGE; SEM-DRAIN-RATE's
integer arithmetic; whether (C2)'s fences leak into any proof; Prop N2
re-derivation.

## 6. Files

* `lean/notes/openmath/Dfloor_phaseB_verifybrief.md` — the self-contained
  brief (verification target): D-1 = Thm MEAS-BRIDGE + Cors BRACKET /
  SEM-DRAIN / SEM-DRAIN-RATE; D-2 = Thms TYPE/PART/FIN + SUM-ONE + ID +
  TRANSFER; D-4 = Thms BASE-0/BASE-1 + Lemmas ADD/LIN + conventions
  (C0)–(C2); Prop N2; Appendix A (self-contained ns-null).
* `verification/openmath/dfloor_checks.py` — falsifier suite (ALL PASS).
* `verification/openmath/results/dfloor_results.json` — sealed run output.
* This record.
