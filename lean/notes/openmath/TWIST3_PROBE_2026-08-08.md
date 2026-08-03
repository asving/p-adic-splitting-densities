# TWIST-3 PROBE — the order-3 e₁ ≥ 2 stratum measured: the ǫ-recurrence REVIVES with exactly the sealed character — (TWIST-3) C^F3_j = z₂^{θ₂s_j}·c^G3_{s_j}, θ₂ = ℓ₁g₁γ₂, EXACT (0/1,656); IDENT-3-persists refuted 710/710; KEY0/ORD-INV lift confirmed; TR3-S4 CHARTERED

**Unit:** synthesis-7 queue #5 (charter = `docs/SYNTHESIS_PASS7_2026-08-08.md`
F2b + queue item 5: preregistered order-3 e₁ ≥ 2 measurement of the sealed
candidate; TR3-S4 charters ONLY on an exact law).  **Harness:**
`verification/openmath/strata3e2_probe.py` (preregistration sealed pre-run
at commit 76513f8, run committed separately — the two-commit protocol;
candidate laws + full derivation + design table in the header BEFORE the
run; seed 20260818; exact arithmetic; rerun JSON-identical; design script
`strata3e2_design.py`, tower constants only, disclosed).  **Parents:**
`STRATA3_2026-08-08.md` (the harness inherited verbatim; the (TWIST-3)
candidate sealed UNTESTED at its commit d8ef8d8 §S3), `TR3S2_2026-08-08.md`
(the order-2 twist law θ = ℓ₀g₀γ₁; ORD-INV/KEY0 matched-key discipline),
`STRATA_PROBE_2026-08-08.md` (the FAMILY-A derivation shape),
grb_order2_check.py (N-1 machinery, CERT legs).  **Author:** Fable TWIST-3
probe unit, campaign window 2026-08-08.

## S0. Defined terms (the F6 template; all scoped verdicts reference these)

* **(P3E2)** := the probed stratum/perimeter: order-3 towers with e₀ = 1,
  e₁ ∈ {2,3}, e₂ = 1 (E₃ = e₁ — the e₁ ramification isolated), mixed
  g_j ≤ 3 (all three g_j = 1 corners covered), d₀ ≤ 2, p ∈ {2,3}, over the
  four base rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]} — the sealed 6-row × 4-ring
  roster (24 towers, deg Φ₃ ≤ 12, 22/24 twist-visible by design).
* **(TWIST-3-MEASURED)** := the statement: at every on-line slot j (abscissa
  s_j) of the level-3 read of every nonzero probed f on (P3E2),
  C^F3_j = z₂^{θ₂·s_j} · c^G3_{s_j} with θ₂ = ℓ₁g₁γ₂ — confirmed at exact
  instances ONLY (a conjecture-level statement with derivation displayed
  pre-run), conditional on the displayed hypotheses of §S2 (reading-C ǫ₂,
  (H-v3), shared-input scope, normalized-ℓ convention).

## S1. Verdict table (all preregistered rows; samples in parentheses)

| row | claim | status going in | observed | verdict |
|---|---|---|---|---|
| C1 | **(TWIST-3)** C^F3_j = z₂^{θ₂s_j}·c^G3_{s_j} | **THE PROBED LAW** (sealed at STRATA3 d8ef8d8; derivation re-derived in this header) | 0/1,656 samples (2,274 on-line-slot comparisons) | **GREEN** |
| P0 | GMN-3 integrity (t₂ ∈ ℤ now GENUINE at ℓ₁ ≠ 0, component shape, c ≠ 0 on-line) | sealed (GMN printed proofs, under (H-v3)) | 0/6,356 | GREEN |
| P1 | support agreement FGMN vs GMN at level 3 | conj component | 0/4,363 | GREEN |
| P2 | level-3 Lemma A-GEN z-shift with NONTRIVIAL ǫ₂ | conj component | 0/2,274 | GREEN |
| P3 | digit-level order-2 identity (TR3-S1; e₁ absent from θ = ℓ₀g₀h₀ = 0) | sealed theorem | 0/2,274 | GREEN |
| P4′ | key class law: gmn3(Φ₃)_k = z₂^{−θ₂k}·ψ₂_k (KEY0 lift) — PRIMARY clause | derived from C1+V4 | 0/24 | GREEN |
| P4′ | divergence-criterion display — SECONDARY clause | sealed formula | **10/24 mismatch** | **RED — classified §S2** |
| P5′ | matched-LABEL ord transport (GMN side keyed by the θ₂-twisted monic key kG; FGMN side by ψ₂ — ORD-INV lift) | derived from C1 | 0/1,656 | GREEN |
| V1–V3 | VAL-3 mult · R₃ total mult · W-MULT-3 δ ≡ 0 (level-3 carry empty at e₂ = 1) | bug detectors | 0/720 | GREEN |
| V4 | key lift R₃(Φ₃) = ψ₂ EXACT — first genuine test of build_Phi3's ǫ₂-correction | bug detector | 0/24 | GREEN |
| V5 | two-form/support/j₀ shape | bug detector | 0/1,656 | GREEN |
| M0 | design-table tripwire (θ₂, ord z₂, visibility) | bug detector | 24/24 match | GREEN |
| CERT2 | order-2 tower re-certification at e₁ ≥ 2 (T1/T2/T5/T11+PARI) | sealed | 0/420 | GREEN |
| CERT3 | PARI order-3 external leg: Φ₃ irred/ℚ_p, unique prime, **(e,f) = (e₁, d₀g₀g₁g₂) — RAMIFIED keys, first in the genre** | sealed | 0/12 | GREEN |
| M1 | reading-P ǫ₂ refuted at every P-visible slot (both readings nontrivial here) | discrimination meter | **1,277/1,277** | MATCH |
| M2/M3 | m₀ > 0 / t₂ ≠ 0 exercised | teeth meters | 206 / 2,139 | MATCH |
| M4 | twist-visible towers | design table: 22/24 | 22/24 | MATCH |
| M5/M6 | visible slots > 0 / **naive IDENT-3 refuted at EVERY visible slot** | CANDIDATE-2 adjudicator | 710 / **710/710** | MATCH |
| M7 | marched increment ratio(j+1)/ratio(j) = z₂^{θ₂e₂} | derived | 0 bad / 504 pairs | MATCH |
| M8 | naive shared-ψ₂ ord pairing failures | REPORT ONLY | 142 | reported |
| P5-hist | ord histogram | teeth | 0:1507 1:84 2:64 3:1 | MATCH |

23,733 samples, 14.9 s, exit 1 (sole red = the P4′ SECONDARY clause,
classified below; every law row green).  Zero harness amendments; the
committed output/JSON is the first full run as sealed; rerun JSON-identical.

## S2. The measured law, and the honest box

**THE MEASURED LAW = (TWIST-3-MEASURED).**  The ǫ-recurrence REVIVES at
order 3 on (P3E2), and it revives with EXACTLY the sealed character: the
level-3 FGMN/GMN discrepancy is the pure z₂-character z₂^{θ₂s_j},
θ₂ = ℓ₁g₁γ₂ — the precise level shift of TR3-S2's accepted order-2 law
θ = ℓ₀g₀γ₁.  Mechanism (sealed pre-run, now instance-confirmed): ǫ₂ is
genuinely nontrivial (ℓ₁ ≠ 0) and its eq-(12)-split-dependent part cancels
against the forced-vs-actual abscissa shift m₀ and GMN's t₂ exponent,
leaving only the slot character (harness header §CANDIDATE 1, steps
(i)–(iv)).  The degenerate/identity alternative (IDENT-3-persists, the
no-revival continuation of the parent's all-e_j = 1 law) is REFUTED at
every one of the 710 twist-visible slots (M6), on towers whose order-3 OM
data carry the genre's first PARI-certified RAMIFIED keys (CERT3,
(e,f) = (e₁, d₀g₀g₁g₂), 12/12).  The marched-ǫ residue table (the sealed
RED-catcher) is identically 1 — recorded per tower in the JSON.

**KEY0/ORD-INV one level up (the TR3S2 pattern reproduced exactly).**  The
GMN-lawful level-3 key class is the θ₂-TWISTED ψ₂ class (P4′ primary,
24/24): key classes diverge on exactly the 22 twist-visible towers,
coincide on the 2 blind ones.
**[SUPERSEDED 2026-08-03, the ROOT r34 fold (TR3-S4 pass-3 observation,
`TR3S4_pass3_report.md` §6 item 1): the orientation LABEL in the
preceding sentence — and its echo at the S3 charter's KEY0-lift
display-lemma line — is the pre-correction reading; TR3-S4 REVISION 1
corrected it. The GMN-LAWFUL level-3 key class is the UNTWISTED ψ₂
class: R_λ₃(Φ₃) = z̄₂^{−θ₂g₂}·ψ₂ (a scalar times ψ₂, from lawfulness +
the verified pin t₂(g₂) = −θ₂g₂); the θ₂-TWISTED T_{c⁻¹}ψ₂ class
belongs to the FGMN-NORMALIZED lift. This probe's Φ₃ — like the sealed
harness's — IS the FGMN-normalized lift, so every measured number in
this note stands unchanged: the P4′/P5′/M8 divergence data compare the
same two objects throughout; only the "GMN-lawful" ATTRIBUTION label
was wrong. Additive bracket; the sealed harness and the committed
run record are byte-untouched per the seal discipline.]**
Ord transport is exact under MATCHED LABELS
(P5′, 0/1,656) and the naive shared-ψ₂ pairing fails 142 times (M8, report
row) — consumers must key each side by its OWN key read, as TR3S2's
ORD-INV prescribes at order 2.

**Reading-P killed at level 2 in the twist-live regime (M1).**  The parent
discriminated reading P at ℓ₁ = 0-adjacent visibility only; here BOTH
readings are nontrivial and reading P fails at all 1,277 P-visible slots
(conditional discrimination given C1, with CERT3 external teeth).

**The single RED — the P4′ SECONDARY clause (harness-display slip, not
mathematics).**  Sealed: "divergence from ψ₂ occurs exactly on towers where
some ψ₂_k ≠ 0 (k < g₂) has z₂^{θ₂k} ≠ 1".  Measured: mismatch on 10/24
towers (observed divergent, predicted not).  ROOT CAUSE (post-hoc script
`strata3e2_p4_posthoc.py` + output, NOT sealed): the sealed formula
compared the wrong objects twice — the harness's observed comparison is
LITERAL polynomial inequality (includes the non-monic leading coefficient
z₂^{−θ₂g₂}), while the sealed formula ranged over k < g₂ bottom-weighted;
the mismatch towers are exactly those whose only visible slot is the
leading one (g₂ = 1 rows R2D/R2F; R2B at p = 3).  The corrected literal
formula (any k ≤ g₂ with ψ₂_k ≠ 0, z₂^{θ₂k} ≠ 1) matches observed 24/24;
the CLASS-divergence formula (monic representatives: any k < g₂ with
ψ₂_k ≠ 0, z₂^{θ₂(g₂−k)} ≠ 1) gives 22/24 = exactly the twist-visible set.
Classification: transcription slip in a self-consistency DISPLAY clause;
the underlying coefficient law (the mathematics) passed 24/24.  Per the
D-ITER precedent the red run stands as committed (exit 1, zero amendments);
the corrected formulas live only in the labeled post-hoc script.

**Instances, not proofs.**  (TWIST-3-MEASURED) is instance-level; numerics
are falsifiers, never proofs.  Theorem-backed inner legs: TR3-S1 (P3) and
N-1/CERT2 machinery certification.

**Displayed hypotheses.**  (H-v3): the GMN-3 ordinate consumes
u_i = w₂(A_i) + i·w₂(Φ₂), i.e. v₃ = w₂ (shared-input scope: both sides
consume the same w₂; the queue-#3 discharge unit owns its reduction to
print attribution).  Reading C for ǫ at both levels (N-1 pins + parent M1
+ this unit's M1).  Normalized-ℓ convention (project standing hypothesis).
The level-3 FGMN transcription is validated internally (V1–V5) and
externally (CERT3), not against the raw print (corrupted at Def 3.15).

**NOT touched:** order-3 strata with e₀ ≥ 2 (stacked E₃ = e₀e₁ — the inner
digit identity P3 becomes TR3-S2's twisted law there and the discrepancy is
predicted NOT to remain a pure z₂-character: the z₁-twist rides INSIDE the
R₂ evaluation — mechanism displayed, probe-first, NO candidate sealed
here); e₂ ≥ 2 (live level-3 carry, V3 empty by stratum here); orders ≥ 4;
the D-ITER composite algebra at order 3 (rank e₁ > 1 on (P3E2) — not
probed); TR-3-ORD-X's FGMN-internal Cor-5.15 leg.

## S3. TR3-S4 CHARTER (earned: the law returned exact per the F2b protocol)

**TR3-S4 (compose): TR-3′-GEN at order 3 on the e₀ = 1, e₁ ≥ 2, e₂ = 1
stratum — the finite-algebra proof note in TR3-S1/S2/S3 format.**
Statement to prove: under {σ₀, σ₁, σ₂} (matched distinguished data) and
the normalized-ℓ convention, the level-3 discrepancy is IDENTICALLY the
character z₂^{θ₂s_j}, θ₂ = ℓ₁g₁γ₂ — equivalently σ₂(R^F₃(f)) equals the
θ₂-twisted R_λ₃(f) — for every nonzero f at every (P3E2)-shaped state
(general g_j, d₀, residue characteristic; e₀ = 1, e₁ ≥ 2, e₂ = 1).  Proof
route (= the sealed header derivation, to be written as mathematics):
  (i) ǫ₁-triviality at e₀ = 1 + TR3-S1 (accepted) on each on-line digit;
  (ii) the level-3 Lemma A-GEN (row P2's identity, nontrivial ǫ₂): same
      proof shape as TR3-S2's Lemma A-GEN one level up;
  (iii) the Bezout/ǫ₂ cancellation: ℓ₁γ_j = s + e₁(ℓ₁u′ − ℓ₁′s) kills the
      split-dependent part of ǫ₂(γ_j)·z₂^{m₀−t₂}, leaving θ₂s_j;
  (iv) the GMN t₂-absorption at general ℓ₁ (Def 2.19 verbatim);
plus two display lemmas with measured cover: KEY0-lift (the GMN-lawful key
class = the θ₂-twisted ψ₂ class; divergence exactly on twist-visible
states) and ORD-INV-lift (matched-label ord transport).  Consumers: the
(2′) R_λ leg of GD3-FULL/OL-B extends to these states WITH the character
threaded (not on-the-nose — the twist must ride the transport, as TR3-S2's
consumers do at order 2).  Falsifiers on file: this unit's 23,733 samples
(law rows 0 violations).  Conditionality: (H-v3) (attribution-only, as in
TR3-S3).  Price: M (all pieces on record; the TR3-S2 → TR3-S3 pattern
composes).  Per the pass-7 F2c standing rule, the acceptance arc must
include a verifier-owned from-note implementation on off-roster instances.

**The stratum after that (NOT chartered, probe-first):** order 3 with
e₀ ≥ 2 (stacked) or e₂ ≥ 2 (live level-3 carry) — see the NOT-touched
display: no sealed candidate; the mechanism note there predicts a
non-scalar inner-twisted evaluation, so the next probe must MEASURE the
shape, not confirm one.

## S4. Run record

`python3 strata3e2_probe.py` → exit 1 (sole red = the P4′ secondary
display clause, classified §S2; ALL law/bug-detector/CERT rows green, all
meters MATCH), 23,733 samples, 14.9 s, seed 20260818.  Preregistration
sealed at 76513f8 BEFORE the run (two-commit protocol); zero harness
amendments; rerun JSON-identical.  PARI legs: CERT2 T11 (order-2 keys at
e₁ ≥ 2) + CERT3 (order-3 RAMIFIED keys: factorpadic + idealprimedec,
(e,f) = (e₁, d₀g₀g₁g₂) exact on all 12 ℤ_p instances).  Post-hoc
classification: `strata3e2_p4_posthoc.py` (+ output, 24/24 corrected
formula match; labeled post-hoc, no sealed status).  Outputs:
`strata3e2_probe_output.txt`, `strata3e2_probe_results.json` (per-tower
marched-ǫ residue tables included).
