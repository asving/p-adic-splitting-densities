# ADM-REAL′ pass 4 — hostile verification report (Fable, fresh context, 2026-08-03)

**Target:** `lean/notes/openmath/ADMREAL_2026-08-08.md` (REVISION 2) +
`verification/openmath/admreal_check.py` +
`verification/logs/admreal_rev1_20260803T014602Z.log`.
**Role:** model-diverse clean-#2 candidate. No `*_pass*_report.md` /
`*_reaudit*_report.md` was read; every source claim re-verified against the
primary artifacts (GMN TeX source, O-9 rev-5 brief, blueprint, ADM-U7, the
Lean carrier files, git history). FIX NOTHING discipline observed.
Numerics treated as falsifiers only. `/tmp/litunit/fgmn.txt` (known corrupted
at Def 3.15) was not used and is not on any of the note's dependency paths.

**VERDICT: CLEAN — 0 critical, 0 gaps.** Every charged item survives
hostile re-derivation. Details per charge below; non-counted observations at
the end.

---

## 1. W-LAD via GMN Lemma 2.14 (any-type scope) + Prop 2.15(1) — CONFIRMED

Source leg: `/tmp/gmn_src/gmn.tex`, sha256
`8253d4d62cf3d180567d5e41429fdb0e4875abdc5d58db595dc66a24fb16bd18` — matches
the note's §2 pin exactly, and `\section{Newton polygons of higher order}`
sits at TeX 869 as claimed.

* **Numbering map independently recounted.** amsart preamble: ONE shared
  counter numbered [section] across theorem/lemma/remark/definition/notation/
  corollary/proposition (TeX 3–11). Section 2 spans TeX 869–1717 and contains
  exactly 27 counter-sharing environments, zero `notation`/`remark` among
  them. My own count: #2 lemma `typedegree` = Lemma 2.2; #5 the v_r
  definition (TeX 985, inside the §"p-adic valuation of r-th order") =
  Def 2.5; #7 `propertiesv` (TeX 1028) = Prop 2.7; #8 `pseudo` (TeX 1101) =
  Prop 2.8; #11 `phir` = Thm 2.11; #12 the representative definition
  (TeX 1288) = Def 2.12; #14 `omji` (TeX 1309) = Lemma 2.14; #15 `vrphii`
  (TeX 1316) = Prop 2.15; #17 `shape` = Lemma 2.17; #19–21 = Defs 2.19–2.21;
  #26 product theorem = Thm 2.26. EVERY pinned label lands where the note
  says. (Thm "polygon in order r" at TeX 1724 falls in section 3 — outside,
  consistently.)
* **Lemma 2.14 verbatim** (TeX 1309): *"For all $1\le i<j\le r$, we have
  $\om_j(\phi_i)=0$."* Printed proof (TeX 1312–1314): slope-−∞ side ⟹
  S_i(φ_i) a point ⟹ ω_{i+1}(φ_i) = 0; then Lemma `typedegree`. NO degree
  comparison, NO optimality/strictness hypothesis anywhere in the chain.
* **Standing scope verbatim** (TeX 975): *"We fix a type $\ty$ of order
  $r-1$ for the rest of section \ref{secNPr}."* The §2.1 type definition
  (TeX 873–885) demands of N_i(φ_{i+1}) only *"one-sided, with positive
  length and slope $\la_i$"* — stationary levels e_if_i = 1 are admitted.
  `grep -i optimal` over the whole TeX: zero hits — the note's "the word
  'optimal' does not occur" is exact. The H3 blueprint's lone "optimal"
  (line 503) is indeed the Cor 3.8/Def 3.9 f-complete wording.
* **Lemma 2.2 re-read** (TeX 935): (1) the ω-chain
  ω_1(P) ≥ e_1f_1ω_2(P) ≥ ⋯, per-level display (chain) with factors
  e_if_i ≥ 1 — hypothesis-free beyond P ≠ 0; (2) deg P < m_r ⟹ ω_r(P) = 0.
  Both exactly as the note consumes them. The deduction 0 = ω_{i+1}(φ_i)
  forces ω_j(φ_i) = 0 for all j > i uses only ω ≥ 0 and factors ≥ 1 —
  stationary levels ride through, as claimed.
* **Indexing translation checked:** our order-r type + representative
  φ_{r+1} = GMN's fixed type at paper-r := r+1; Lemma 2.14 then covers
  ω_j(φ_i) = 0 for all j ∈ (i, r+1] ⊇ the climb's needed j ∈ (i, r]. (P1) =
  Prop 2.7(1) verbatim ("$v_r(P)\ge e_{r-1}v_{r-1}(P)$ and equality holds if
  and only if $\om_{r-1}(P)=0$"); Prop 2.8 is the pseudo-valuation P−Q
  proposition — the pass-1 attribution alternative stays refuted at source.
  (P3) = Prop 2.7(4) ("$v_r(\phi_{r-1})=e_{r-1}v_{r-1}(\phi_{r-1})+h_{r-1}$")
  + Thm 2.11's `vrphir` display ($v_r(\phi_r)=e_{r-1}f_{r-1}v_r(\phi_{r-1})$
  = the W-CAP step e_rf_r·w_r = V̂). W-LAD's climb re-derived by hand:
  w(φ_i) = (e_{i+1}⋯e_r)·v_{i+1}(φ_i) = E_i(e_iV_i + h_i). φ₀ = x case: at
  f₀ ≥ 2, deg x = 1 < m_1 = f₀ ≤ m_j (tower non-decreasing, e_jf_j ≥ 1
  suffices), Lemma 2.2(2) closes it. SOUND at full GMN-§2.1 scope.
* **(P-VRPHII) term-for-term tie re-derived:** A_{i+1} = e_{i+1}e_if_iA_i +
  h_{i+1} unrolls to A_i = Σ_{j≤i}(e_{j+1}⋯e_i)(e_jf_j⋯e_{i−1}f_{i−1})h_j
  (verified against the recursion coefficient-by-coefficient); multiplying by
  E_i turns (e_{j+1}⋯e_i) into (e_{j+1}⋯e_r) — exactly Prop 2.15(1) verbatim
  at paper-r = r+1 ("for all $1\le i<r$", covering all our i ≤ r). The pin is
  corroborative only; W-LAD's own proof stands without it.
* Secondary (degree) route: valid at exactly the live levels
  (m_j ≥ m_{i+1} = e_if_im_i ≥ 2m_i > m_i for j > i live i), and the ledger
  reads w(φ_i) only at live i (stationary ⟹ j_i = 0). Both halves as
  displayed.

## 2. CLASS-LAT: divide-by-e_r + truncated-type identification — CONFIRMED

Re-proved from scratch. (F1) e_r | E_i for i < r: definitional. (F2)
w_r = e_rV_r + h_r ≡ h_r invertible mod e_r by gcd(h_r, e_r) = 1. (F3)
w_i = E_i(e_iV_i + h_i) = e_r·E′_i(e_iV_i + h_i) with E′_i = e_{i+1}⋯e_{r−1},
and the truncated data's V_i (i ≤ r−1) are unchanged because the (P3)
recursion is bottom-up — so the w′_i are exactly the truncated lattice's
weights. Split j_r = a + e_rb bijective onto [0, e_rf_r). Reduction mod e_r
kills the bracket; invertibility pins a = a_c uniquely; c − a_cw_r ≡ 0 mod
e_r makes the division legal, and x·e_r ↦ x is the isomorphism
e_rℤ/eℤ ≅ ℤ/e′ℤ (e = e′e_r). For each of the f_r values of b the inductive
hypothesis gives exactly f₁⋯f_{r−1} solutions; total f₁⋯f_r; the weight-0
j₀ digit multiplies by f₀. Totals audit: e classes × f₁⋯f_r = Πe_if_i ✓.
Stationary-top degeneration (e_r = f_r = 1: a = b = 0, mod-1 trivial,
e′ = e) and interleaved-stationary transparency ((F3) needs no liveness)
both check. Hand instance at r = 3, all e_i > 1 (charge (2)): stages
(2,1,1),(3,1,1),(2,1,1), f₀ = 1 — full weights {6,14,43}-generated,
12 indices hit the 12 classes mod 12 exactly once; truncated weights
{3,7} = {w₁/e₃, w₂/e₃} hit ℤ/6 exactly once; identification exact.
Consequences 1–2 follow from LED(iii) (O-9 rev5 line 512, PROVED stock).
The note's status label is right: O-9 line 255–266 priced general-order
(CLASS-d) via (GR-B); CLASS-LAT strengthens, contradicts no display.

## 3. STEP (merged-list argument), NON-END, LOC — CONFIRMED

* O-9's datum definition (rev5 lines 184–201) has k₀ < ⋯ < k_s and slopes
  strictly increasing < 0, and itself carries d(S) = (k_S − k_{S−1})/e_S —
  so δ_S ≥ 1 and STEP(a)'s divisibility (gcd argument re-checked) are
  faithful. (READ) β_k = L_k − kV̂ at on-line slots: verbatim (line 216–218).
* Merged list: face slot-sets live in [k_{S−1}, k_S], overlap pairwise only
  at shared vertices (face S's slots ≤ k_S, face S+1's ≥ k_S), and both
  faces read L = U_S there (δ_Sh_S telescope re-checked); hence every
  consecutive pair of the k-ordered merged list lies within ONE face's
  progression and obeys that face's exact step −(e_SV̂ + h_S). The
  "consecutive faces sharing non-vertex lattice points" attack has no
  purchase: slots are per-face segments, not extended lines. Descent
  e_SV̂ + h_S ≥ V̂ + 1 (e_S, h_S ≥ 1, V̂ ≥ 0); the walk into k_s ends with a
  face-s step (exists, δ_s ≥ 1); single-vertex data vacuous — all as
  displayed.
* NON-END chain: β_k ≥ β_{k_s} + V̂ + 1 ≥ V̂ + 1 > V̂ − w(φ₁) ≥ W_max ≥
  classmax; FULL conversion by CLASS-LAT + LED(iii) (all class weights <
  β_k ⟹ count = class size = d). r = 0 reading (V̂ = 0, W_max = 0, count =
  f₀ = d) and the margin claims (≥ 1 + w(φ₁) ≥ 2 at r ≥ 1, ≥ 1 at r = 0)
  check. W-CAP's telescope re-derived: (REC) w_{i+1} = e_if_iw_i +
  E_{i+1}h_{i+1} (E_{i+1}e_{i+1} = E_i), top e_rf_rw_r = V_{r+1} = V̂ (Thm
  2.11), Σ(e_if_i−1)w_i = V̂ − w₁ − Σ_{i≥2}E_ih_i; top-index legality and
  the stationary-level zero-contribution both check.
* Realized reads: β_{k_s} = w(a_{k_s}) ≥ 0 by TRI (O-9 §4, PROVED; weights
  ≥ 0, e·v_π ≥ 0) — the only realization input, honestly displayed, with the
  abstract β_{k_s} < 0 caveat and the R2(d)/(e) legs supporting (not
  proving) it.
* LOC: both equivalences re-derived from NON-END + CLASS-LAT + LED(iii);
  the "no abstract countermodel off the right end" claim is correctly scoped
  to β_{k_s} ≥ 0 data.
* Assembly: clause 1 = NON-END at realized data; clause 2 cites ADM-U7 §4's
  trichotomy + instances A/B/C (machine-reconfirmed via R5, reran green).
  The quantifier block matches HDISCHARGE_H3 §1.3(c) verbatim (blueprint
  lines 157–163 checked) and consumption honesty ("only: a datum over a
  type, and β_{k_s} ≥ 0") is accurate.

## 4. B-PIN displayed-open discipline + consumption corollary scope — CONFIRMED

* (B-PIN) quotes O-9's CEN-J display faithfully (rev5 lines 434–437: "L′ :=
  L − [k_s ∈ K_D] (the chain's right-end read is ρ-pinned — (FRESH)(c) —
  hence charged to the parent … monic top k_s = ℓ ∉ K_D … nothing is
  subtracted)"). (FRESH)(c) is OPEN in O-9 (rev5 line 95) — consistent with
  §8's pricing. The ε = 1-exclusion reading is NOT asserted; it is carried
  as displayed open audit item (ii) inside (C-JCT) with the circularity
  reason stated (presupposes fan-out exhaustiveness) — the downgrade is
  applied consistently at §1, §8, §9 ("NOT CLAIMED"). Support items are
  labeled "Support on file (NOT proof)". The theorem itself consumes no
  (B-PIN); only the corollary does — checked line by line.
* Consumption corollary: conditional on (B-PIN) alone; claims exactly the
  FULL-at-the-L′-slots conjunct of (ADM′) := FULL at L′-slots +
  value-attainment at vertices (matches ADM-U7 §7 item 2's definition);
  L′-slots are on-line ∈ K_D minus k_s, hence ⊆ NON-END's coverage; the
  value-attainment conjunct is displayed OPEN in §1, §8, AND §9. O-9's §5.1
  image law ("onto F_{r+1} ⟺ FULL attainment", rev5 §5.1) is what makes
  FULL the consumed predicate at digit slots — cited, not re-proved. No
  over-claim found.

## 5. F-ADM-3 scoping + the E_i>1-restricted inheritance sentence — CONFIRMED

* Definition site verified: `CensusCore.lean:155–156` — `wphi i = if i.1 = 0
  then 0 else D.e i * D.Vrec i.1 + D.h i` (birth value, no E_i rescale);
  `wt j = Σ_i digit_i · wphi i` with `ledgerE` the INTRA-stage radix
  (digit = a + e_i·b), not a rescale.
* O-9's convention verified top-normalized: rev5 line 482 "wt(𝐣) := w(B_𝐣)
  = Σ j_i·w(φ_i)"; TRI's proof rescale quote "e_r·wt_r(𝐣′) = w(B_{𝐣′})"
  verbatim at line 498. The scope-pin argument (TRI on a single monomial
  forces wt(𝐣) = w(B_𝐣)) is airtight given TRI's PROVED status.
* Consumer audit independently re-grepped at HEAD: `CensusData.wt/wphi`
  consumers = exactly the note's six files. (A seventh grep hit,
  `HC2/HK22_twoNodeGate.lean`, is a local hypothesis named `hwphi` —
  NOT a CensusData consumer; audit table stands.) Zero E_i-rescale sites
  (pattern grep clean). Derived-hypothesis rows verified:
  `ValueSide/DensityTie.lean:390` and `ValueSide/SeriesTie.lean:1243` take
  `ADMFull CD` as priced hypothesis fields. Compiled instances found: D0
  (r=0, AdmCarrier:174), Dm (r=1, AdmCarrier:191, Census:905) — the
  "r ≤ 1/degenerate" precision holds.
* The REVISION 2 rescope is mathematically exact: wphi_i ≥ h_i ≥ 1, so the
  conventions diverge at stage i iff E_i > 1, and an r ≥ 2 type with all
  e_j = 1 (j ≥ 2) has every E_i = 1 — divergence ⟺ some relevant E_i > 1.
* F-ADM-2 reconciliation: blueprint entry (H3 lines 125–147) re-read — the
  88-count, smallest type (2,1,2,1) all f = 1, multiset {0,1,5,6}, and the
  collision mechanism w(φ₂) = 4f₁+1 ≡ w(φ₁) mod 4 all reproduce under the
  coded weights (hand-recomputed: coded {0,1,5,6} class-3-empty vs top
  {0,2,5,7} uniform). The blueprint itself scopes F-ADM-2 to "the coded
  Vrec/wphi weight recursion", so the note's relocation contradicts nothing.
  No reading makes the coded convention the one O-9's census consumes
  (charge (3)): O-9's census reads wt through TRI/LED = w(B_𝐣) values.

## 6. Falsifier reconciliation — ALL LEGS RECONCILED

* **Rerun this pass:** `python3 admreal_check.py` → exit 0, output
  byte-identical (mod blank lines) to the committed
  `admreal_rev1_20260803T014602Z.log` (fixed seed 20260803; R5 subprocess
  reran `adm_u7_check.py` green).
* **Grid arithmetic recomputed by hand:** r ≤ 3 grid = 36 + 648 + 11,664 =
  12,348 (18 stage choices re-derived: e=1:8, e=2:4, e=3:6). r=4 spot grid =
  2·4·14·4·14·3 = 18,816. R6 total 31,164 ✓. Stationary count = (8 + 256 +
  6,176) + 18,816 = 25,256 ✓ (18³−14³ = 3,088 per f₀ at r=3).
* **R6(c) premise control recomputed EXACTLY:** failing pairs (m_i ≥ m_j) ⟺
  stages i..j−1 all stationary. Spot patterns contribute 2+1+3 = 6 per
  combo → 6,272·6 = 37,632; r=2 grid 144; r=3 grid 2,592+2,592+576 = 5,760.
  Total 43,536 — matches the log EXACTLY. Live-pair failures = 0 is forced
  (a failing pair's stage i is stationary), so that leg is a transcription
  check, not a discriminator — consistent with its stated role.
* R2: 243 neg-pool failures under b ≤ cm (log ✓; the surviving
  `/tmp/admreal_run1.log`, mtime 00:16 — pre-045b435 (00:26) — shows 90
  under the old strict-<, corroborating the note's "vs 90"); R2(d)'s
  pre-run bound β_{k_s} ≤ −2 re-derived (failure b ≤ cm ≤ V̂−1 and STEP ⟹
  β_{k_s} ≤ −2). Datum generator re-read: vertex-β recursion, face-set
  coverage counter, slopes distinct + sorted, slots[:-1] = non-end — all
  faithful to the contracts.
* R3′ == 88 exact ✓; R3″ 11,664/0 ✓; R3(b)-STATE in the live exit contract
  (preds dict re-read) ✓; R4 re-read logic vs the 198-row jsonl (row count
  confirmed; tallies 113/85/0/0 match GADM2's sealed disposition); the
  n_att-from-harness limitation is displayed (§7 numerics honesty +
  §9 charge (6)).
* **Two-commit seal verified in git:** e05e660 (2026-08-03 01:45:54, note +
  script only) contains the FULL revised contracts but a verdict
  PLACEHOLDER ("*REVISION 1 verdict:* recorded in the follow-up commit
  appended below" — zero occurrences of the PASS text); log timestamped
  01:46:02Z; 90e1ecb (01:47:33) adds the verdict + log. Chronology sound.
  The original legs' prose-only attestation is displayed as accepted
  downgrade — honest.
* REVISION 2 diff (0c93371 → b2e173a): exactly 3 hunks — the §5 rescope,
  the §7 seal naming, the appended REVISION 2 block — "no other line
  changed" verifies.

## 7. Findings

**CRITICAL: none. GAPS: none.**

Non-counted observations (below defect threshold, recorded for
completeness):

1. §0's CLASS-LAT summary attributes the induction's inputs to "gcd(h_i,
   e_i) = 1 and the pinned (P1)/(P3) weight ladder" without naming
   (P-OMJI); the ladder's stationary-level legs need the new pin. The
   operative displays (§1 theorem inputs, §3, §5 "inputs = W-LAD + gcd",
   §9) all carry the exact dependency, so this is summary compression, not
   a missing justification.
2. The note cites the type definition at "TeX 872–885"; the definition
   sentence begins at 873 (872 opens the display). Verbatim content
   unaffected.
3. R6(c)'s live-pair-0 prediction is tautological given the failure
   characterization (any failing pair starts at a stationary stage); it
   checks the transcription, which is its stated purpose.

## 8. Verdict

CLEAN. The (ADM-REAL′) chain — W-LAD at full GMN-§2.1 scope via the
source-verified (P-OMJI)/(P-VRPHII), W-CAP, CLASS-LAT at every order, STEP,
NON-END, LOC, the assembled theorem with the k_s carve-out — survives a
full hostile pass with the boundary hypothesis (B-PIN), the value-attainment
conjunct, (FRESH)(a′)(c), (GR-B)-for-CEN-J's-own-proof, and the TAMS
numbering all correctly displayed as open/pending, and F-ADM-3 correctly
scoped as a prospective carrier variance with the re-key duty sign-off
gated. This is the second model-diverse clean pass on REVISION 2.

ADMREAL-P4 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
