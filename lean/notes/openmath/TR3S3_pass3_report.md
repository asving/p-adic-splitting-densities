# TR3-S3 hostile pass 3 (Fable, fresh context, model-diverse clean-#2 candidate) — 2026-08-08

**Target:** `lean/notes/openmath/TR3S3_2026-08-08.md` at REVISION 1 (+
`verification/openmath/tr3s3_check.py`, `tr3s3_check_run2_output.txt`).
**Context consumed:** TR3S1/TR3S2 (accepted parents), STRATA3 (the measured
law), GRB_ORDER2 REV 14 (S1.1/S1.2/S3.4/S4/R2.3). **Independence:** no pass
report or reaudit file was read; the FULL chain was re-derived from the
displayed pins; both recorded harness runs were re-executed live in a sandbox;
a verifier-owned implementation of BOTH operators was written from the note's
formulas alone (zero shared code, different tower) and run green. The
stipulated corruption of /tmp/litunit/fgmn.txt at Def 3.15 was honored:
extraction agreement was nowhere treated as verification; numerics were
treated as falsifiers only.

**VERDICT: GAPS-ONLY — 0 critical / 2 justification gaps (both display/record
level; the theorem's algebraic chain, its conditionality discipline, and the
falsifier record are sound). Both gaps: assume the conclusion, verify
downstream — downstream verified in full.**

---

## Findings

### GAP 1 — (PIN-GEN-i)'s coverage omits Def 3.18 at i = 3 (same provenance class)

Quote (S1, the pin): "The identification of the corrected Def 3.15 AT LEVEL 2
(ǫ₂) and of Def 3.16 AT LEVEL 3 with the printed FGMN operators rests on (a)
the print's level-GENERIC displays and (b) computational discrimination only".
Quote (S1, the Def 3.18 pin): "**FGMN Def 3.18**: R^F_i(g) = R_{i,α}(g)/y^{j₀},
j₀ = ⌊s(g)/e_i^F⌋; at e₃^F = e₂ = 1, j₀ = s(g) = the initial abscissa of the
λ₃-component." — this pin carries NEITHER a non-textual-leg note NOR a
transcription-scope display, violating the note's own header discipline
("Every formula pin carries a non-textual leg or an explicit
transcription-scope display") at exactly one pin. The i = 3 instantiation of
Def 3.18 (the side-read y^{j₀}-normalization) rests on the same
generic-index-only provenance as Def 3.16-at-i=3 — TR3-S1's inherited leg
(fgmn.txt:1354) pinned the display at its i = 2 consumption, not at i = 3 —
so by the REVISION-1 standard that created (PIN-GEN-i) (pass-1 gap 2), Def
3.18-at-i=3 belongs inside the named pin (the owed `pdftotext -layout` leg
would cover the same pages). Classification: JUSTIFICATION GAP, display-level.
Downstream (assuming the displayed 3.18 shape): the j₀-law is exercised green
by E2B (0/816), K (0/24), the j0pos meter (173), the probe's V5, and my
independent implementation; the attribution caveat is the already-displayed
open-pin genre. Nothing else rests on it.

### GAP 2 — falsifier row O's violation branch is unreachable; S8.2 assigns it falsifying power it lacks

Quote (S8.2): "A red on E2A/E2B falsifies S5; … K the S6.2 label tie; O the
S6.2 transport." In `check_sample`, row O runs only after E2B has passed
(`if not ok: … return`), and E2B's pass requires `side == glist` elementwise;
`fp_ord(K2, glist, T3.psi2) == fp_ord(K2, side, T3.psi2)` is then an identity
of equal lists (fp_ord is non-mutating) — the `o1 != o2` branch cannot fire on
any reachable sample. So "O … falsifies the S6.2 transport" misattributes
discriminating power: the row's only live content is the preregistered
ord-histogram teeth ("must contain some ord >= 1" — fired, 0:744 1:38 2:34),
and the preregistered "PREDICTED: 0 mismatches" carries no exposure.
Classification: JUSTIFICATION GAP, record-level (same genre as pass-1's gap 3:
the record's claim about what the harness tests vs what it can test).
Downstream: the S6.2 transport is iso-invariance of ψ-adic order — algebra
needing no numeric leg; I verified it directly (step-2 chain below). No
consumer is misled about the mathematics, only about the harness's coverage
map.

---

## Verified perimeter (every step walked; the charge items in order)

* **Lemma KER.** Re-derived: at e_i^F = 1, eq-(12) forces (s,u) = (0,β);
  normalized Bézout forces (ℓ,ℓ′) = (0,1); corrected-Def-3.15 exponent
  ℓ′s − ℓu = 0 at every β, so ǫ₁ ≡ ǫ₂ ≡ 1 (and s(γ) = 0 at level 3 gives
  stride-1 slots from 0). One line per level, correct; code pins
  (`bezout`/`eq12`) agree; RI tests all clauses at REVISION 1 (0/21,741).
* **Lemma A3.** (i) Chain truncation: a MacLane chain's conditions are
  per-augmentation-step, so the depth-3 chain's prefix is a depth-2 chain —
  (H-CHAIN)₃ ⟹ (H-CHAIN)₂ for the substate, as displayed. (ii) Read-data
  inheritance: the substate's ν₀-read data (lawful monic Φ₁, R_{λ₀}(Φ₁) ∼ ψ₀)
  are verbatim the state's S0 inputs; e₀ = 1 holds, so accepted TR3-S1 applies
  in full, with the SAME σ₀/σ₁ (same K₀/K₁, same truncated residue tower —
  the (SQ₂) compatibility is genuine). (iii) Totality: TR3-S1's statement is
  total in nonzero f ∈ O[x] with no degree bound (its S3 scope note), so the
  digit A (deg A < deg Φ₂, possibly ≥ deg Φ₁) qualifies; the degree bound is
  consumed only at S5(ii)'s evaluation-nonvanishing, correctly. (iv)
  j₀ = ⌊s₀/e₁⌋ = s₀ at e₁ = 1, and s₀(A) = s₂(A) is the same
  initial-abscissa datum (TR3-S1 S5(i)'s accepted identification, at the
  substate). (v) Inner-operator identification: Def 3.16-at-i=3's inner
  R_{2,γ_j} is Def 3.16 at i = 2 with slot weights β_m = β − mγ₂, stride 1,
  start 0 — exactly the operator of TR3-S1's theorem at the substate's
  stratum instance, read at its own weight γ_j = w₂(A) at on-line slots.
  m₀ = (s₂(A) − s(β))/e₁ = s₂(A) at s(β) = 0. All verified.
* **Lemma Z2 (the genuinely new obligation).** The two-level dichotomy
  re-derived: β < w₂(A) gives w₁(a_m) > β_m for every nonzero Φ₁-digit
  (γ₂-min), then w₀(b) > δ for every Φ₀-digit at every level-1 slot (h₀-min),
  and red of an all-positive-valuation polynomial is 0 — including δ < 0 and
  zero digits (TR3-S1 (A3)'s corner verbatim). Domain direction checked:
  β < w₂(A) is INSIDE P_β(µ₂) (a ≥-set), so Def 3.16 is applied in its
  printed domain. The E2A face (noff = 902 honestly computed off-line slots)
  and the constructed Z2 row (0/768) confirm at instance level; verified in
  the harness code that the probe's `Tower3.R3w` hard-codes off-line slots to
  zero (`if on else K2["zero"]`) while `fresh_R3` computes them — the note's
  claim about what is newly tested is accurate.
* **t₂-absorption.** GMN's t_{r−1}(i) at r = 3 is (s₂(A_i) − ℓ₂^{GMN}u_i)/e₂^{GMN}
  with GMN level-2 = project read-ν₁ data (the note's gloss is explicit and
  the index bookkeeping coherent); at e₁ = 1, ℓ₁ = 0 (KER) it collapses to
  s₂(A_i), integrality trivial. Def-2.19-verbatim; RIII 0/1,141.
* **σ₂ via Cor 5.6(2) at index 2 < r (the no-(KP_i) claim).** Correct: at
  r = 3 the chain (H-CHAIN)₃ supplies φ₃ = Φ₂ as a CHAIN member, so
  ψ₂^F = R₂^F(Φ₂) is chain-internal — (KP_i) is consumed only at the state
  key Φ₃ (S6.2 step 1, extended chain), exactly mirroring TR3-S1's index
  discipline (internal at 1 < 2, extended at Φ₂). The S2(iii) monicity
  upgrade recomputed: top digit 1 on-line (u + g₁h₁ = g₁γ₂ = w₂(Φ₂)),
  R₁(1) = 1, s₁(1) = 0, t₁ = 0, c^G2_{g₁} = 1; lawful degree forces
  s₂(Φ₂) = 0; monic associate of monic ψ₁ = ψ₁. σ₂ = quotient of σ₁[y] by
  (ψ₂^F) ↦ (ψ₁); (SQ₂) standard. The S6.2 Φ₃-tie recomputed the same way
  (c^G3_{g₂} = 1, s₀(Φ₃) = 0, σ₂(ψ₃^F) = ψ₂); step-2 transport is
  iso-invariance with matched labels, and the key-class coincidence at
  discrepancy ≡ 1 is PROVED by step 1's scalar-1 computation (P4 24/24 its
  instance face); step-3 Cor 5.15/[T] displayed as NOT discharged.
* **S5 assembly.** Support equivalence (on-line iff w₂(A_j) = γ_j, both
  polygons the same points under (H-v3)), the five-step per-slot chain
  ([KER][(SQ₂)][A3][t₂ = s₂][Def 2.20]), evaluation-nonvanishing (window
  ≤ g₁ − 1 from deg A < deg Φ₂ — the ONLY degree-bound consumption — and
  {1,…,z̄₂^{g₁−1}} a K₁-basis), y^s division against Def 3.18's j₀ = s: all
  re-derived, correct. Trichotomy of slots exhaustive; γ_j < 0 covered.
* **(H-v3) discipline.** The S1 derivation sketch's arithmetic checked
  (H₂ = min(w₁(a_i) + iγ₂) = w₂ at e₁ = 1, v₃ = e₂^{GMN}H₂ = w₂); honestly
  kept a hypothesis (the H_{r−1} generic display not re-extracted); the
  fallback claim (a false (H-v3) strips only the GMN label, the displayed
  identity surviving project-facing) is correct — every S5 step consumes only
  the w₂-form of u_i, and v₃ enters the r = 3 recursion only through u_i
  (ordinates + component), as S9.1 says. EVERY consumer display carries the
  conditionality: summary rows 6–8, S6.1 heading + blockquote + GD3-FULL/OL-B
  clause, S6.2 conclusion + consumer clause ((H-v3) + (KP_i) + [T]), S6.3.
  TR-4's order-3 consumption at S6.1 is licensed (leaf S4 discharges it
  r-generically via Cors 4.4/4.5/4.11). No unconditional leak found.
* **(PIN-GEN-i) display.** Present, named, correctly scoped to ATTRIBUTION
  (not the finite identity), with the owed `pdftotext -layout` leg displayed
  as OWED, not attempted; S7 + S9.6 name it. Coverage defect = GAP 1 above.
* **Fences.** e_j ≥ 2 untouched (KER/A3/t₂ all die there, mechanisms named;
  (TWIST-3) with θ₂ = ℓ₁g₁γ₂ quoted correctly from the probe and left
  sealed); orders ≥ 4 fenced (induction not written; correctly noted that
  stating it = the open general-σ_j clause); D-ITER untouched (E₃ = 1,
  rank-1 carry). No hidden consumption found anywhere in S2–S6.

## Script/output reconciliation (all exact)

* **Counts.** Run 1: RI 0/14,797, TOTAL 23,869 (sum of the 12 family counts
  = 23,869 exactly). Run 2: RI 0/21,741, TOTAL 30,813 (JSON counts sum =
  30,813 exactly). Delta = 6,944 on both = the nonzero level-1 digit reads:
  the count system {run-1 RI = 2N₂ + D + 2,893; run-2 RI = 2N₂ + 2D + 2,893;
  base 2,893 = R2w_at calls from RII (1,141) + Z2 (768) + fresh_R3 calls
  (984)} solves EXACTLY at D = 6,944, N₂ = 2,480 (integral, consistent) —
  the "+6,944 = the nonzero level-1 digit reads" claim is arithmetically
  forced, not just asserted.
* **Deviation perimeter.** `diff` of the two recorded outputs touches ONLY
  the four ring-timing lines, the RI line, and the TOTAL line (which carries
  the elapsed) — precisely as preregistered in the ADDENDUM ("ANY other
  deviation = STOP") and as S8.3 states.
* **Provenance commits.** b4a142b = note + script ONLY (no outputs) —
  the seal; 482150b = run-1 log + JSON (RI 14,797, sum 23,869) + note
  results block; 8b003c4 = REVISION 1. `git diff b4a142b..482150b` on the
  script is EMPTY (the sealed script is the run-1 script); the
  482150b→HEAD script diff is EXACTLY the ADDENDUM header + the single
  R2w_at leg (level-1 eq-(12) split + l0 check), consuming no randomness.
* **Live reproduction (this pass).** Both script versions re-executed in a
  sandbox copy (repo artifacts untouched): the HEAD version reproduces
  `tr3s3_check_run2_output.txt` byte-identically mod timings, JSON identical,
  exit 0; the 482150b version reproduces `tr3s3_check_output.txt` mod
  timings, exit 0. PARI legs live in both reruns.
* **Perimeter honesty.** Verified in source: `gmn3` hard-codes
  u_i = w₂(A_i) + i·w₂(Φ₂) and normalized ℓ (t₂ = (s₂ − l1·u)/e1), exactly as
  the header's cannot-falsify declarations state; ROSTER3 is 6 all-e_j = 1
  rows × 4 rings with the g₀ = 1 (3E), g₁ = 1 (3D), g₂ = 1 (3F) corners;
  cert3_pari does factorpadic + idealprimedec with (e,f) = (E₃, d₀g₀g₁g₂);
  W-row noise is strictly-above-line (w₃ ≥ base+2 > γ), so its greenness is
  a genuine end-to-end Z2+linearity face; rows E2A/E2B/RI–RIV/Z2/XV/W/K are
  live falsifiers (only O is not — GAP 2).

## Verifier-owned independent leg (falsifier, not proof)

Implemented both operators from the note's displayed formulas alone
(/tmp/tr3s3_verify/independent_note_check.py): own tower over ℤ₂ with
h-vector (1,2,1) (in no ROSTER3 row), d₀ = 1, own keys Φ₀ = x+1,
Φ₁ = Φ₀² + 2Φ₀ + 4, Φ₂ = Φ₁² + 16Φ₁ + 128Φ₀ (γ₂ = 4, w₂(Φ₂) = 8, γ₃ = 9),
own F₄/F₁₆ models, own dev/eq12/Bézout, ǫ computed from the corrected formula
(not set to 1). Sanity gates: R_λ₂(Φ₂) = ψ₁ exactly by my own gmn2 (the
S2(iii) instance). Result: 93 samples (random, Φ₂^a·h, Φ₁^a·h, π^k, Φ₂, Φ₂²),
189 abscissa checks, composed identity + support + two-form ALL GREEN with
m0pos = 5, j0pos = 17, noff = 72 (all teeth fired). Hand-walked instance
displaying the absorption: f = Φ₁ (single digit A₀ = Φ₁, γ = 4): FGMN gets
C^F3_0 = z₂ from the y¹-slot of the inner read; GMN gets c^G3_0 = z₂^{t₂}·1
= z₂ from t₂ = s₂(Φ₁) = 1 against a constant-anchored inner value — equal,
by exactly the S5(ii) mechanism.

## Non-classifiable observations (no action required)

1. The preregistration seal evidences ORDER in the repo record; no repository
   can evidence non-execution before sealing. The note's REVISION-1 phrasing
   ("carried by the repository record") is accurate about what is carried.
2. S6.3's "beyond {order ≤ 2} ∪ {order 3, all e_j = 1}": order-1 states are
   outside the leaf's setting (order ≥ 2), so "order ≤ 2" = order 2; harmless.
3. The script comment "sub-line noise" describes strictly-above-the-polygon
   noise; the code's direction is the invisible one and correct.
4. The truncation argument's prefix-stability of Def 3.1 rests on the
   MacLane-chain conditions being per-augmentation-step — true of the
   standard definitions and displayed as the mechanism, but the definition
   itself is another generic-display consumption of the corrupted-extraction
   class (covered by the leaf's standing (H-CHAIN) consumption, where it
   belongs — no new display owed by this unit).

## Bottom line

The finite algebra is correct at every step; the two genuinely new
obligations (Lemma Z2, σ₂) are proved; the conditionality discipline
((H-v3), (KP_i), [T], (H-ℓ), the attribution pin) is executed at every
consumer site; the falsifier record is genuine, arithmetically reconciled,
and live-reproduced; a verifier-owned implementation confirms the law on a
tower outside the tested roster. Two display/record-level justification gaps
(GAP 1: pin coverage of Def 3.18-at-i=3; GAP 2: row O's dead violation
branch vs its claimed falsifying face). No critical finding.

TR3S3-P3 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY
