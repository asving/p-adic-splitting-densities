# HE7 passPE2 — hostile verification report (fresh context, zero prior stake)

**VERDICT: PENDING (skeleton; machine-integrity leg complete, math audit and
fresh route in progress).**

Target: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` at HEAD (r2 complete at
83ced80 + machine leg 1811605; arc seal 1956151 → verdict 4c42f9d → r1
aafb481/d58680e/2970615 → PE1 5c98481/7b66364 → r2). Prior report
`HE7_passPE1_report.md` read; prime surface per the r2 fold: §S5.8 (LEMMAS
HE7-12/HE7-13 — the never-attacked new math), the r2 wirings at HE7.A(3) /
LEMMA HE7-8 / §S8 row 5, the F-2/F-3/F-4 display repairs, and the §S11 [r2]
disclosures. Protocol: quote-and-classify, fix nothing.

## MACHINE LEG (integrity) — COMPLETE, GREEN

* **Pins.** All seven files byte-identical at worktree = HEAD = r2 83ced80 =
  machine-leg 1811605: `he7_checks.py` 688adbe88447…, `he7_checks_output.txt`
  b2d095a2556a…, `he7_checks_results.json` f5bedab2ecda…, `he7r1_supp.py`
  24ece42e4538…, `he7r2_supp.py` 71bb6202f72c…, `he7r2_supp_output.txt`
  1e787536254c…, `he7r2_supp_results.json` f45b5ab1e3b5… — §S11's displayed
  pins all match.
* **Isolated re-run** (`/tmp/he7_pe2_sandbox`, committed artifacts untouched):
  `he7r2_supp.py` GREEN, exit 0, 3.7 s, checks {B1 42, B2 210, B3 42, B4 42,
  B5 13}, 0 violations; results-JSON leaf-diff vs committed artifact =
  {secs: 3.7 vs 3.8} only; output ex-timing IDENTICAL.
* **42-vs-41 recount, independently recomputed** from the frozen
  `he7_checks_results.json` refine histograms: 9+1+5+0+0+5+0+0+3+8+6+2+3 =
  **42**, all with exactly one refine step (no key '2' or higher anywhere), on
  member counts matching Q1's table row-for-row (209/243/161/125/124/150/105/
  115/105/79/57/57/57). The r2 disclosure (artifact was always 42; Q1's
  pre-r2 "41" a prose slip) is CONFIRMED.
* **Display-alignment check (attack item 3).** The sealed runner's refine
  object `fr.lift2(lam2, s2)` = c·nrm(m₀)·Φ′^{s₀} with nrm(k) = x^k mod Φ′ =
  π^{⌊k/2⌋}x^{k mod 2} — degree ≤ 1 + 2s₀ ≤ 3 < D″ = 4, slot value exactly
  λ₂, residue s₂: this IS the note's [r2] displayed object (a (LIFT₂)
  polynomial w with deg w < D″), not the pre-r2 "ŝ₂·n₂(λ₂)" (which, as a
  literal power product x^{m₀}Φ′^{s₀}, has x-degree m₀+2s₀ = 5 ≥ D″ at
  λ₂ = 11 and is NOT a HE7-12-eligible perturbation). Alignment holds.
* **Instrument audit of `he7r2_supp.py`.** B2's bound is literally the
  note's (S5.8.1) with ν = λ₂ (`(lam2 - fr.T2) + e1 - fr.l*(DP-1)*e0`); the
  five strata's hardcoded offsets re-derived and verified against the
  geometry (δ=∞; κ=(u+2)/2 > λ; κ=(2u−1)/4 in the F-2 middle band, ε₁ = 1/2;
  x−1 with ε₀ = 1, ε₁ = u; δ=λ wrong residue). B3's HE7-9(b) identity is
  computed AT the refined key from an independently recomputed hull — the
  F-1 gap is exercised, not assumed. B5 keys (ring, s, u), which is
  injective across the 13 rows (checked). One vacuity niche found — see
  finding/remark section.

## FINDINGS

(TO BE FILLED — math audit of §S5.8 and fresh route in progress.)

## FRESH ROUTE

(TO BE FILLED — running.)

## GRADE

(TO BE FILLED.)
