# O4T — the O-4 drainage transfer (DELTA-2 path step) — Phase-B attempt (Fable, 2026-07-31)

Charge (dispatch "O4T"; tree O-4 entry + SYNTH4 framing + DELTA-2 consumer walk
`O-4 OL1-ii ← CU-2 + CU-4 + GMN Cor 4.19`): transfer the VERIFIED semantic drainage
core (M05 Lemmas A–D + Theorem E, upheld at V2 items 5–8; Dfloor's SEM-DRAIN
corollaries, V22 SOUND) to the OM/GD tree classifier through the OL1-ii agreement
seam — prove the transfer or the sharpest honest partial with the exact seam named;
falsifier = numeric comparison of undecided_OM vs undecided_sem extending the
N1-exhaust artifacts.

The self-contained brief is `O4T_phaseB_verifybrief.md` (hand THAT to the hostile
pass). This attempt records what was achieved, the design decisions, the falsifier
record, and the honest status.

## 1. What was achieved

* **The transfer skeleton, unconditional** (brief §2): TR-0 (a.e.-finite decision
  level ⇒ env → 0; sufficiency only — V2 finding 1's a.e./pointwise correction
  honored), FLOOR (soundness ⇒ `undec^sem(N) ≤ undec^c(N)`: the semantic classifier
  is the floor, tying into Dfloor's MEAS-BRIDGE picture), TR-Q (a nondecreasing
  majorant `N(f) ≤ Γ(v_p(disc f))` converts M05's verified Lemma-C tail into an
  explicit envelope for the classifier).
* **THE NEW THEOREM (N3, brief §3): the O-4 transfer is UNCONDITIONALLY DISCHARGED at
  n ≤ 3 for the canonical mathematical classifier.** The canonical order-≤1
  lazy-scan run (policy pinned in brief §3.2 — level-synchronous digit scan, hull
  certificates (C1)/(C2), left-edge shortcut, residual reads, refinement recursion)
  terminates on every separable monic f at every prime including wild, its verdict is
  the true type of EVERY lift of the level-L(f) class, and

      L(f) ≤ v_p(disc f) + 1     (sharp: attained in every numeric config).

  Hence pointwise OL1 (not just a.e.) with the LINEAR majorant Γ(v) = v+1, drainage
  with the explicit envelope `env(N) ≤ (n−1)·p^{−max(0,⌈(N−w)/(n−1)⌉)}` (w = n·v_p(n)),
  and the two-sided transfer display

      undec^sem(N) ≤ undec^can(N) ≤ undec^K(2N−1)

  (the canonical classifier beats the Krasner/discriminant decider by a factor-2
  level shift — the transfer "shift" is in the classifier's favor). Key structural
  point: at n ≤ 3 the canonical OM tree cannot leave order ≤ 1 (a repeated residual
  on an e ≥ 2 side needs side length e·d ≥ 4 > n), so the whole run sits inside the
  V26-VERIFIED GD23 perimeter (order-≤1 algebra + DEVID); the proof consumes only
  displayed classical facts (Newton polygon, Galois-stable slope factorization,
  Hensel) — no CU-*, no GD-≥2, no BNS.
* **The seam at general n, named exactly** (brief §4): TR-OM conditional on (AGR) =
  OL1-ii, decomposed per the DELTA-2 arrow with per-input statuses quoted: GMN Cor
  4.19 [literature, pinned; the "≤ ind(f) steps" caveat = V2 item 4, at GD-7]; CU-2
  [open over GD-1..6; V26 verified order ≤ 1, REJECTED beyond]; CU-4/F4-C [open;
  CU-1's proof REJECTED at V27, including the (N*-MAJ) prefix-monotonicity break];
  the finite-stable-certificate obligation [V2 finding 3] — which is exactly what N3
  PROVES at n ≤ 3, so the n ≤ 3 residue is pure engine conformance (GD-4/GD-6/CU-4),
  no new mathematics.
* **Rescope (churn classification, standing authority):** the charge's displayed
  inequality `undecided_OM(N) ≤ undecided_sem(N + shift)` is unprovable AS WRITTEN in
  that direction (FLOOR: sem ≤ OM always); the faithful transfer display is
  N3-BRACKET `undec^can(N) ≤ undec^K(2N−1)` (Krasner superset, multiplicative shift,
  classifier's favor) + TR-Q at general n. Recorded in brief §4; nothing else in the
  charge is affected.

## 2. Falsifier record (falsifier-first: run BEFORE the brief was written)

`verification/openmath/O4T_transfer_check.py` — NEW harness extending the N1-exhaust
artifacts (imports N1's validated exact n=2 semantic law + the exact `padic_types`
oracles): implements the pinned canonical walk WITH ITS READ LEDGER (the first
executable `undec_OM`-side instrument; N1's flag F1 noted that no such extraction
existed). Preregistered predictions P1–P6 in the module docstring, written before the
production run. Exhaustive exact-integer scans, 2,534,851 classes:

    configs: n=2 (p=2,C=10) (p=3,C=6) (p=5,C=4); n=3 (p=2,C=5) (p=3,C=4)  [wild incl.]

    P1 SOUND  (walker verdict = exact oracle type)            0 mismatches
    P2 FLOOR  (never decided while semantically undecided)    0 violations
    P3 CEIL   (L ≤ v_p(disc)+1 per separable rep)             0 violations, max slack 0
    P4 KRA    (L ≤ max(1, 2v+1))                              0 violations
    P5 ENV    (N3-ENV envelope + monotone undec)              0 violations
    P6 LEAN2  (n=2: under the K-12 hExhaustP envelope shape)  0 violations
    OVERALL: ALL PASS   (sealed: results/O4T_transfer_results.json;
                         log: logs/O4T_transfer_20260731_155929.log; ~80 s rerun)

Findings beyond the pass/fail: (i) max(L − v − 1) = 0 in EVERY config — the ceiling
is exactly sharp, the same δ+1 precision shape as BNS Thm 3.13 (consistency only; BNS
stays literature-candidate, unconsumed). (ii) At n = 2 the canonical classifier is
EXACTLY semantically optimal: undec^can(N) = undec^sem(N) (exact law) at every probed
level for p ∈ {2,3,5} — 1.97M classes; recorded as an observation, not a theorem.
(iii) At n = 3 undec^can tracks the certified semantic lower bracket to within the
depth artifact at N ~ C.

## 3. Design decisions

* **An executable read-ledger surrogate, not the Lean engine.** The as-built
  classifier has no extraction (N1 F1); the unit therefore proves and tests the
  CANONICAL MATHEMATICAL run (M05 §5's N(f) object) with a pinned read policy, and
  prices the engine-conformance seam separately (brief §4). This is the same
  fidelity split the tree already uses (mathematical law vs decision lag).
* **The lazy (level-synchronous) scan is load-bearing.** An eager scan (resolve every
  v(g_i) exactly) has NO disc-bounded ceiling: x² − a with a ≡ 1 mod 8 at p = 2 has
  v(disc) = 2 but v(A) = v(1−a) unbounded — the eager reader loses OL2's linear
  shape entirely. The left-edge shortcut certificate ((C2) + Lemma CERT(ii)) is what
  restores L ≤ v+1; this is the mathematical content the "finite run ⇒ finite stable
  certificate" gap (V2 finding 3) was hiding.
* **n ≤ 3 as the honest perimeter.** It is exactly where (a) the run provably stays
  at order ≤ 1 = the V26-verified GD23 layer, (b) exhaustive falsification is cheap,
  (c) the transfer question is fully decidable numerically (n=2 exact semantic law;
  n=3 certified bracket). n = 2 was closed in Lean (K-12); n = 3 drainage-with-rate
  for the canonical classifier is NEW.

## 4. Honest status

**PROVED-UNVERIFIED (rev 1):** TR-0/FLOOR/TR-Q + Theorem N3 + corollaries, no
hostile pass yet. TR-OM remains CONDITIONAL-OPEN on (AGR) with the seam decomposition
displayed — this unit does NOT close O-4 at general n; it closes the mathematical
half at n ≤ 3 and supplies the general-n skeleton + the sharp target shape
Γ(v) = v+1. Verification protocol: hand `O4T_phaseB_verifybrief.md` ALONE to a fresh
hostile verifier; priority charges = brief §7 items 1–3 (the shortcut certificate,
the case-(b) ceiling corner, the refinement count) and 8 (no silent (AGR)
consumption).

## 5. Files

* `lean/notes/openmath/O4T_phaseB_verifybrief.md` — the self-contained brief (rev 1).
* `lean/notes/openmath/O4T_phaseB_attempt.md` — this record.
* `verification/openmath/O4T_transfer_check.py` — the falsifier harness (rerun:
  `python3 O4T_transfer_check.py`; `--quick` for the 1 s smoke grid; exits nonzero on
  any violation).
* `verification/openmath/results/O4T_transfer_results.json` — sealed results.
* `verification/openmath/logs/O4T_transfer_20260731_155929.log` — production log
  (155913 = the prior --quick smoke run).

## 6. Handoff notes (for the orchestrator)

1. **Tree edits suggested (not executed here):** O-4's status line can record: at
   n ≤ 3 the OL1-ii MATHEMATICAL half is PROVED-UNVERIFIED with the sharp linear
   majorant v+1 (this unit); the general-n residue is unchanged (CU-2 + CU-4 + Cor
   4.19). The charge-direction rescope (brief §4) should be folded into the O-4
   entry's falsifier wording.
2. **The n = 2 exact-optimality observation** (undec^can = undec^sem, 1.97M classes)
   is a candidate cheap theorem (quadratic case analysis vs the N1 closed-form law)
   and would upgrade K-12's faithfulness-audit story; not attempted here.
3. **OL2 at general n:** N3's ceiling argument is per-cluster-step and did not use
   n ≤ 3 in the (CEIL) chains — only in "the walk never needs order ≥ 2" and the
   e = 1 recursion. A general-n version over the GD-≥2 layer (once V26's criticals
   are repaired) is the natural next dedicated unit; target shape Γ(v) = v + O_n(1).
4. **Depth-3/order-2 falsifier synergy:** the CU-1 depth-3 harness (o1thr_depth3)
   probes the same seam from the engine side; extending THIS harness to n = 4
   (order-2 states appear) requires implementing genuine order-2 reads — do not
   attempt without the GD-≥2 repair, or the surrogate loses its verified-perimeter
   warrant.
