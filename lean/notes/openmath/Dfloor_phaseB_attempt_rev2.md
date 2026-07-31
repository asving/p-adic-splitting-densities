# Dfloor — the assembly floor (D-1 + D-2 + D-4) — Phase-B attempt REV 2 (Fable, 2026-07-31)

Repair of the V17 hostile verification (`V17_dfloor.jsonl`, verdict UNSOUND)
of the rev-1 attempt (`Dfloor_phaseB_attempt.md`) / brief
(`Dfloor_phaseB_verifybrief.md`). V17's own summary: "The semantic results
for n ≥ 1 are largely correct, including the exact strict measure bridge,
SUM-ONE, TRANSFER, and the elementary part of BASE-1. But the package
contains a false n = 0 Haar assertion and an unsupported jump from degree-one
semantics to the claimed algorithmic solve/uniformity statements." Both
defects (and every smaller finding) are repaired in the rev-2 brief
`Dfloor_phaseB_verifybrief_rev2.md` — produced by COPYING rev 1 and applying
ONLY the edits listed below, so every V17-confirmed passage is byte-stable.

## 0. V17 findings → dispositions (no silent drops)

| # | V17 finding (gist, quoted) | class | disposition |
|---|---|---|---|
| 1 | Prop H1 "singletons are μ-null" is "FALSE as stated": at n = 0, G = ℤ_p⁰ = {()} has singleton mass 1, and the proof's p^{−nN} = 1 ↛ 0; "directly contradicts BASE-0(b)" (Dirac mass); "internally inconsistent" | CRITICAL | **FIXED (brief §1.2)**: the singleton clause is now the DISPLAYED hypothesis-carrying statement (2′) "IF n ≥ 1, singletons are μ-null", with an explicit non-removability note (at n = 0, μ = δ_{()}, singleton mass 1 — reconciled with BASE-0(b)); the proof step is labeled "n ≥ 1 only" and shows exactly where n ≥ 1 enters; Appendix A's one consumption of the clause is re-pointed at (2′) with its n = 1 instance named |
| 2 | BASE-1(e)'s "one type and one state, so the finite solve … degenerates to (1)C = (1)… (U-GEN) and (U-DENS) hold" is "UNPROVED / OUT OF SCOPE": no definition/theorem that the external classifier/solve has one state, matrix (1), or faithful output; "'One type' does not imply 'one algorithmic state'"; (a)–(d) and R = 1 sound | CRITICAL (scope) | **FIXED (brief §6.1)**: (e) rescoped to the proved SEMANTIC clauses only (α = R(p) at every prime, exact bracket, trivial drainage, Σ R = 1 — (U-GEN)(i)–(ii)'s measure content read with the semantic counts (5) + (U-DENS)'s density identity); the algorithmic residue is NAMED in a new displayed fence (f): one-state classifier, the producing 1×1 solve (1)·C = (1) of (U-GEN)(iii), and count-faithfulness to (5) are CLASSIFIER-SIDE — re-pointed at the tree's classifier nodes O-1/O-2/O-3/O-5, O-4's OL1-ii agreement seam, and T-8's block solve; the full (U-GEN)+(U-DENS) at n = 1 is explicitly NOT claimed. Header of BASE-1, §0 summary, the base-change remark, §6.2 consumers, and §8 ledger aligned |
| 3 | "C_N(x) is the ball of radius p^{−N}" — "With the usual convention, it is the CLOSED ball d ≤ p^{−N}, not the open ball" (minor; does not damage the clopen/base argument) | minor | **FIXED (brief §1.1)**: "CLOSED ball of radius p^{−N} (the set d(·, x) ≤ p^{−N})", with the clopen-either-way note |
| 4 | ADD "invokes 'uniqueness (TYPE)' before establishing that gh is separable… presentation-level circularity, not a false conclusion" (the UFD argument inside TYPE's proof removes the obstacle) | presentation | **FIXED (brief §6.2)**: proof reordered exactly per the finding — SEPARABILITY OF gh FIRST (direct: gh's roots = g's ∪ h's, distinct within each separable factor, distinct across by gcd(g,h) = 1 through minimal polynomials; the rev-1 char-0 irreducible-separability detour is deleted as no longer needed), THEN TYPE applies to the now-known-separable gh, with the multiset-union step attributed to UFD monic-normalization uniqueness (separability-free, as displayed inside TYPE's proof) |
| 5 | T-F's n = 3 interpolation conclusion "cannot be checked from the package because the rational functions/degrees are not included" (I-5(b) "Unverifiable here, but not used in the main theorems"); a finite check proves an identity only once the point count exceeds the cleared numerator degree | auditability | **FIXED (brief §7 T-F)**: the five sealed n = 3 R_σ are now DISPLAYED (numerators + denominators P4 = q⁴+q³+q²+q+1, P5 = (q+1)P4), with the cleared numerator A := 6·P5·(Σ R_σ − 1) written as six displayed terms each of degree ≤ 5, so 6 valid points suffice (Lemma ID) and 199 were checked; during this repair A(q) = 0 was re-verified at q = 2..11 by exact integer arithmetic (10 > 5 points — an independent in-session certificate). The n = 2 cleared-degree remark added for the same shape |
| 6 | I-4 "Honest but dependent on the undefined external REG-p predicate" (no repair demanded; the general-n instance is honestly conditional) | note | **CLARIFIED (brief §5 instances)**: one sentence added — (REG-p) is an EXTERNAL predicate (nodes T-U/D-6/O-12), consumed only as the name of the hypothesis set P |

Everything else V17 confirmed — the Haar algebra/compactness/π–λ
bookkeeping, the cylinder mass law, MEAS-BRIDGE(iv)'s EXACT strict equality
and lax bracket with Lemma EX's role (EX valid for n ≥ 1 = exactly
MEAS-BRIDGE's scope, per V17), TRANSFER and its definedness bookkeeping,
SUM-ONE, BASE-1(a)–(d) with the level-0 decision, the import-by-import scope
audit (I-1/I-2/I-3/I-5(a) honest; C2 fences honest) — is BYTE-STABLE in
rev 2 (verified by diff: the rev-1 → rev-2 delta is exactly the six
dispositions above plus the rev-2 preamble and §9 checks (viii)–(xi)).

## 1. What is now claimed (corrected headline)

* **D-1 (MEAS-BRIDGE)** — unchanged: clauses (i)–(v) proved for both decided
  conventions, (iv) EXACT in the strict convention; BRACKET / SEM-DRAIN /
  SEM-DRAIN-RATE unconditional at every prime including wild. Semantic side
  only, as before.
* **D-2 (SUM-ONE)** — unchanged: TYPE/PART/FIN + SUM-ONE + ID + TRANSFER;
  n = 1, n = 2 instances unconditional; general n conditional exactly on the
  T-U ledger.
* **D-4 (BASE-CASES)** — CORRECTED SCOPE: BASE-1(a)–(e) prove the uniformity
  root's SEMANTIC clauses at n = 1 (one type; α = 1 = R(p); exact bracket;
  trivial drainage; Σ R = 1). The ALGORITHMIC half (one-state classifier,
  the 1×1 solve, count faithfulness) is a named fence — BASE-1(f) — pointed
  at O-1/O-2/O-3/O-5 + O-4 OL1-ii + T-8, NOT proved by this unit. BASE-0,
  ADD (proof reordered), LIN, (C0)–(C2) as before. Prop H1's singleton
  clause now carries its displayed n ≥ 1 hypothesis (2′); the n = 0 floor is
  BASE-0(b)'s Dirac mass, no longer contradicted.

## 2. Falsifier status

`verification/openmath/dfloor_checks.py` is UNCHANGED (its assertions tested
only repaired-scope claims; nothing it checks was touched by the repairs —
T-F's runtime content was always the 199 exact point checks, whose
interpolation WARRANT is what §7 now displays). Sealed results remain
`verification/openmath/results/dfloor_results.json`, ALL PASS, 0 failures.
New in-session check (this repair): the displayed cleared numerator A(q)
vanishes at q = 2..11 by exact integer arithmetic, certifying the displayed
n = 3 table's checksum independently of the sealed file.

## 3. Status + verification protocol

**PROVED-UNVERIFIED (rev 2)** — the repairs have had no fresh-context
adversarial pass yet. Hand a fresh verifier `Dfloor_phaseB_verifybrief_rev2.md`
ALONE (self-contained). Highest-value pokes: the rev-2 checks §9
(viii)–(xi) — the (2′) hypothesis discipline at every singleton consumption,
BASE-1(e)/(f)'s semantic/algorithmic seam (does any proved clause smuggle a
classifier fact?), ADD's reordered proof, and the displayed T-F degree
bound; plus V17's original checklist for regression.

## 4. Files

* `lean/notes/openmath/Dfloor_phaseB_verifybrief_rev2.md` — the repaired
  self-contained brief (verification target; rev-1 confirmed passages
  byte-stable).
* `lean/notes/openmath/Dfloor_phaseB_attempt_rev2.md` — this record.
* Rev-1 pair (`Dfloor_phaseB_attempt.md`, `Dfloor_phaseB_verifybrief.md`) +
  `V17_dfloor.jsonl` — kept as the audit trail; superseded for consumption.
* `verification/openmath/dfloor_checks.py` + `results/dfloor_results.json` —
  unchanged, still valid.
