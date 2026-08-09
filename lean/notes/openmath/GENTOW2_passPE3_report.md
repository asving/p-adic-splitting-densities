# GENTOW2 passPE3 — HOSTILE VERIFIER REPORT (fresh context), 2026-08-09

**VERDICT: PENDING (skeleton commit; findings + fresh route below as
sections land).**

Target: lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md at HEAD
(r2 = c7c4416 + d56e439 + 100d1ea; folded at 5ea9a60). PE1 (61daa69)
and PE2 (aff457c) reports read first; their routes not re-walked.
Charge: quote-and-classify, fix nothing; CLEAN bar = nothing
GAP-or-worse; a CLEAN pass starts the counter 0/2 → 1/2.

## OWNED SURFACES (attack order)

1. The [r2] canonical LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}:
   re-derived from the PDF itself (Def 3.12 + §3.2/§3.3 + Prop 1.15);
   provenance rows 17–19 re-verified against rendered pages 7/15/16
   (+ p.17 z_i pins); both identification use-sites checked.
2. The [r2] h-step repair: division argument re-derived; strictness
   legs (e₃ ≥ 2 value-group; e₃ = 1 y-degree contradiction) checked
   against Cor 4.4/4.7, Lemma 3.17, eq (14) at the rendered pages;
   N1 grade-7 worked trace re-computed incl. the 17/2 arithmetic.
3. The LP1 letter-live probe instrument: seal chain, dual-route
   decorrelation, tautology audit.
4. Cross-round [r1]+[r2] coherence.
5. Free hunt + FRESH ROUTE (letter-live, DIFFERENT p, z₂ ≠ 1 —
   the first detectably-nonzero FGMN-letter contact).

## MACHINE-LEG INTEGRITY (verified before the fresh route)

* Pins at HEAD, all EXACT: PDF md5 da846c82f1fcb619cefb3feb8164191e
  (518,522 bytes); gentow2_checks.py 2603eb7c...; run2 output
  832aa838...; gentow2_pe1_fresh.py a70dd986... / output e66e8ea5...;
  gentow2_pe2_fresh.py f2d6f1fa... = its seal blob at 090f501;
  gentow2_r2_letter_probe.py d0c0ebeb... = its seal blob at d56e439
  (byte-identical at HEAD; output added only at 100d1ea — first run
  under seal confirmed by the commit sequence).
* r2 commit sweep: c7c4416 touches ONLY the note; d56e439 adds ONLY
  the probe; 100d1ea adds ONLY the note S10 + probe output — zero
  modifications to sealed files across the r2 range.
* Isolated re-runs (fresh /tmp copies, this pass): sealed battery →
  BIT-IDENTICAL (41 checks/0 violations, teeth T1+T2′, exit 0); r2
  letter probe → BIT-IDENTICAL (21/0, exit 0); PE1 fresh runner →
  BIT-IDENTICAL (20/0); PE2 fresh runner → BIT-IDENTICAL (22/0).
* Probe import audit: gentow2_checks has a __main__ guard, so the
  probe's `import gentow2_checks as G` pulls only the helper
  functions and EMPTY counters — the probe's 21 checks are its own,
  not battery re-counts.

(Findings, fresh route, and grade line follow in the next commits.)
