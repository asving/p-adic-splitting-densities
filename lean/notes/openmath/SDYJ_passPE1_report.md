# SDYJ pass PE1 — hostile content verification (fresh context)

Object: `lean/notes/openmath/SDYJ_PROOF_2026-08-08.md` at a44cb70 (confirmed
`git log -1 --format=%h -- <file>` = a44cb70; seal commit 1 = d9540e0).
Charge: SDY-L1 re-derivation (forced dump chain, single-cell exactness,
all-g-1 entry points, (H3) coverage); SDY-L2 ledger vs L-NORM/S2.2; companion
anatomy exhaustiveness; every-d₀ extension (hidden d₀=1 dependence); the
consequence display + grade caps; machine re-run + 2 hand companions; F-E
cross-note adjudication + the d₀≥2 wall disclosure.  I verify; I fix nothing.

Findings appended incrementally below.  Classification: CRITICAL (breaks the
chain) / GAP (justification gap; assume and continue) / NOTE.

---
## 1. Charge 1 — SDY-L1 re-derived from the accepted [RMG] displays: SOUND

The full chain re-derived from source, independently of the note's text:

* **Inventory basis.** [RMG] S2.2 (lines 493–517) defines C_k^{(i)} :=
  realize_i(ε_i((g_i−k)γ_{i+1})^{−1}ψ_{i,k}, (g_i−k)γ_{i+1}), correction
  children per reduced cell d with "a_{d,l} ≤ P_l − 1 for l < i, a_{d,l} = 0
  for l ≥ i"; [RMG] line 917 certifies "B-READ on C_k^{(i)} (all cells
  on-line on-grid, L-CELL/S2.1)" at target β_k = (g_i−k)γ_{i+1}.  At all-g-1,
  k < g_i forces k = 0, so the digit is C₀^{(i)} on-line at γ_{i+1} — the
  note's basis is exactly the accepted certification.
* **The forcing.** S3.1's t-chain (t_l := (a_{l−1} − s_l(λ_l))/e_{l−1} ∈ ℤ
  on-grid) + the reduced window a_{l−1} ∈ [0, e_{l−1}g_{l−1} − 1] +
  s_l ∈ [0, e_{l−1}) give −1 < t_l < g_{l−1}, so t_l ∈ [0, g_{l−1}); at
  g_{l−1} = 1, t_l = 0 and a_{l−1} = s_l(λ_l) exactly.  Verified at every
  level incl. l = 1 (g₀ = 1 = exactly where the remark says it enters).
  The note asserts the interval without the two-line window arithmetic —
  ingredients are all in-sentence (reduced is quoted); see n-1.
* **Single cell.** Forced dump vector = a function of γ_{i+1} alone ⟹ every
  cell of C₀^{(i)} has the same exponent vector; L-CELL(i) ("finite sum of
  DISTINCT reduced cells", distinctness keyed by exponent vectors) ⟹
  exactly one cell.  EXACT — no multi-cell digit is possible at any level
  at all-g-1.  (Machine: 30/30 interior digits single-celled.)  The
  L-CELL(i) step is consumed at S0 but not cited in the proof body — n-2.
* **λ₀ = w₀(c_d).** L-GRID: λ_l = line_l(truncation); at l = 0,
  line₀(b) = E₀·w₀(b) = w₀(b).  ✓
* **Integrality.** S3.1: λ_{l−1} ∈ ℤ automatic on-grid (γ_l ≡ h_{l−1},
  ℓ_{l−1}h_{l−1} ≡ 1 mod e_{l−1}).  Engine-free: v_l − s_lγ_l ≡
  v_l(1 − ℓh) ≡ 0 mod e_{l−1}.  ✓
* **(INV) induction re-done by hand.** Base (i ≥ 1): v_i = γ_{i+1} =
  e_i·e_{i−1}γ_i + h_i ≥ e_{i−1}γ_i + 1 (e_i, h_i ≥ 1).  Step 2 ≤ l ≤ i:
  v_{l−1} ≥ (v_l − (e_{l−1}−1)γ_l)/e_{l−1} ≥ (γ_l+1)/e_{l−1} =
  w_{l−1}Φ_{l−1} + (h_{l−1}+1)/e_{l−1} > e_{l−2}γ_{l−1}, and v_{l−1} ∈ ℤ
  strictly above an integer ⟹ (INV_{l−1}).  Terminal: v₀ ≥ (γ₁+1)/e₀ > 0,
  v₀ ∈ ℤ ⟹ v₀ ≥ 1.  Integrality is genuinely load-bearing (YJX2:
  rational bound 2/3 < 1, hand-checked).  i = 0: C₀^{(0)} =
  lift(ψ₀,0)·π^{h₀}, w₀(lift) = 0 per S2.2, w₀ = h₀ ≥ 1 exactly.  ✓
* **(H2)/(H3)/g₀ = 1 coverage.** (H2) g_{m−1} = 1 + (H3) g_{1..m−2} = 1 +
  g₀ = 1 = all g_l = 1, 0 ≤ l ≤ m−1 (WMULTDCX S1 defs verified; SD-L1's
  standing remark verbatim).  Every consumption in the chain needs only
  these: k = 0 at level i needs g_i = 1 (top digit i = m−1 needs (H2));
  the forcing at level l−1 needs g_{l−1} = 1; w_lΦ_l = e_{l−1}γ_l needs
  g_{l−1} = 1.  All covered; m = 2 corner ((H3) range empty) checks.
* **Where all-g-1 enters, complete list:** the t-forcing at every level,
  P_l = e_l (window), k_c ≡ 0 (digit choice), w_lΦ_l = e_{l−1}γ_l (base +
  step of (INV)).  The g₀ ≥ 2 failure remark (t₁-freedom) is correct and
  correctly fenced (F-A).
* **Consumption footprint clean of the W cap:** SDY-L1 rests ONLY on
  [RMG] (ACCEPTED) + [ILN]† S0.1 definitions.  Verified against S8 row.

## 2. Charge 2 — SDY-L2 ledger vs L-NORM/S2.2: SOUND, no leaking child type

Edge inventory audited against [RMG] S2.2 + WMULTDCX W-D0/W-D1:
promotion (b unchanged — S2.2 verbatim), Φ_m-exit (cofactor keeps b),
correction L/π-junk/Φ₀Y children (L-NORM(a)/(b)/(c): ≥ w exact / ≥ w+1 /
≥ w), i = 0 corrections (split of b·C₀^{(0)}, digit w₀ = h₀), stage-2
seeding (split of b·c_D, w₀(c_D) = u₀ — W-D2(iii) verified stated for
EVERY d-cell at (H3) ∧ g₀ = 1, any d₀, in WMULTDCX lines 174–176).
Root = π^{u₁+u₁′} exactly (W-D1 an identity, verified).  Every two-exit
path has exactly one seeding (W-D0 two-stage structure).  Junk counter
(W-D0) = π-junk + Φ₀Y edges, so X(C) = junk − Y₂ − ΣY_c as the runner
reads it.  Chaining gives w₀ ≥ ŵ + Σ w₀(c_{d_c}) + X(C); junk-free ⟹
all-L ⟹ equality (L exact, seeding exact at u₀).  "Promotions never
touch b" is S2.2 verbatim — the valuation ledger indeed has no promotion
term, so the box's feared offset cannot exist in this ledger.  No child
type found whose w₀ contribution is miscounted.

## 3. Charge 3 — companion anatomy (Reduction 2): EXHAUSTIVE

CE(C) = ∅ ⟹ no L-NORM split anywhere in stage 1 (splits occur only at
corrections + the one seeding) ⟹ b₀ = π^{u₁+u₁′} verbatim ⟹ seeding
Y-child ≡ 0 at ANY d₀ (SD-L4(i)/E-L6, deg b̂₀ = 0 — E-L6 verified stated
for any d₀).  Seed unique: W-D2(iii) forces every d-cell principal at
(H3) ∧ g₀ = 1 + L-CELL(i) distinctness ⟹ ONE d-cell (S-L1's display,
verified already any-d₀ in SURV_PROOF lines 242–246).  Post-seeding
forks: none (promotion/exit unique per firing, E1-priority — S-L4(iii)
uniqueness half, stated at (H3) ∧ g₀ = 1, d₀-free).  So L-ride ⟹ the
unique correction/junk/Y₂-free path = the cascade (S-L4(iii)) ⟹ C = Ĉ;
X-ride ⟹ the X-mate, ≤ 1, w₀ ≥ ŵ + 1 (L-NORM(b)), junk ≥ 1.  Exhaustive.
(★) consumed at its full pin set ((H2) ∧ (H3) ∧ g₀ = 1 ∧ (STK) ∧ clause —
all present in SDY-L3's header); its any-d₀ status re-verified from the
derivation (SD-L2 any g₀/d₀ + pool telescope + W-D2(iii) any d₀).
SD-L1 equality analysis (defc = 0 ⟹ e_i = 1 ∧ Y_c = 1 ∧ full dump)
re-checked by the mixed-radix telescope.  Φ₀Y-fed dichotomy (Y₂ = 1 or
all-defc-0-all-Y_c = 1) ⟹ junk ≥ 1: correct.

## 4. Charge 4 — the every-d₀ extension: NO hidden d₀ = 1 dependence found

Step-by-step d₀ audit: SDY-L1 arithmetic never mentions d₀; SDY-L2 rides
W-D2(iii) (any d₀, verified) + L-NORM (any d₀); Reduction 2 rides
E-L6/SD-L4(i) (any d₀ by the degree argument), unique d-cell (any d₀),
S-L4(iii)-uniq (any d₀); (★) any d₀; S-L0/S-L4(i)(ii)/S-THM(c) d₀-free
(S-L4(i) is the line DEFINITION, [RMG] S2.1).  SD-L4(ii)/(iii)'s SD-r1
principal-seed pin is satisfied at (H3) ∧ g₀ = 1 for any d₀ (unique
principal d-cell), extending the predecessor's d₀ = 1-only consumption
legitimately.  The two displayed proof deltas vs SD-THM-A are exactly
right (CE = ∅ forcing was the only d₀ = 1 step; X-mate same-exponent
display correctly dropped).  The honest residue is (H1): at d₀ ≥ 2 the
T-scope sufficient condition wants all interior e_i ≥ 2, and every
realized companion lives on flat-e₁ d₀ = 2 towers OUTSIDE it — F-C
disclosés this exactly (per-row T-TERM certificates).  d₀ ≥ 3 is
machine-dark (F-D) — engine wall verified in source: grb_order2_check
Tower.__init__ hardcodes phibar quadratic on the d₀ ≥ 2 branch (lines
479–490), so a d₀ = 3 request silently builds deg Φ₀ = 2.  The proof's
d₀-uniformity + the coverage-gap framing are both accurate.

## 5. Charge 5 — consequence display and grade caps: EXACT (one gloss, n-3)

* Predecessor pinned class confirmed (SURVDISJ_PROOF S8): LAW-DCX on
  TRACK ∧ (H1)–(H3) ∧ g₀ = 1 ∧ d₀ = 1 ∧ (STK) ∧ (RW), every m ≥ 2.  The
  drop is exactly d₀ = 1, legitimate: ≥ k leg = SDY-THM(v) (all pins
  carried), < k leg = E-THM (EMPTY_PROOF header verified: "(H1)–(H3),
  g₀ FREE and d₀ free inside T-scope" — cited correctly incl. the
  T-scope qualifier via (H1)).
* "OPEN = exactly (SURV-K2)" follows the predecessor's box convention
  (its S8: "open set exactly = the two boxes" with pins listed
  separately); the claims-table row displays the full pin set and is
  exact.  The one over-strong gloss is n-3 below.
* Grade caps verified against the pass-report verdict lines:
  WMULTDCX PE1 NOT-CLEAN / PE2 GAPS-ONLY / PE3 GAPS-ONLY = 0/2 CLEAN ✓
  (binding cap, correctly named); SURVDISJ PE1 GAPS-ONLY / PE2 CLEAN =
  1/2 ✓; SURV PE1 GAPS-ONLY = 0 CLEAN ✓; EMPTY PE1 NOT-CLEAN / PE2
  CLEAN = 1/2 ✓; RMENGINE ACCEPTED ✓.  The W arc's residual gaps
  (attainment-pin display scope) do not touch W-D1/W-D2(iii)/W-D7 as
  consumed here — this note displays exactly the (H3) ∧ g₀ = 1 ∧ (STK)
  ∧ clause scoping those gaps demanded.  Every S6 acceptance-leg item
  cross-checked present.

## 6. Charge 6 — machine leg: REPLICATED EXACTLY; F-E and the wall ADJUDICATED

* Object at a44cb70 ✓; seal d9540e0 ✓.  Post-seal diff (d9540e0 →
  a44cb70) confined to wall_probe(): constructor name Tower2 → G.Tower
  + log strings + disclosure comment.  All sealed family checks
  byte-unchanged; the repair is exactly as disclosed at S7.3.
* All 8 md5 pins match the note; runner/output/results md5s match S7.3.
* Fresh read-only re-run (outdir /tmp): ALL ELEVEN FAMILIES 0
  VIOLATIONS; output identical modulo timing; results json identical
  modulo elapsed (companions/counters/findings/rows/violations all
  MATCH).  Counters reproduce the note's S7.3 numbers exactly (980,646
  sweep chains; 3,892 sharp; 26,416 integrality-load; 56 live rows;
  139 super cells; 30 digits, 9 sharp; 41 committed rows re-traced;
  8 companions matched; 11 total).
* Family fidelity audited against S7.1: DIG/SWEEP/SUPER/COMP/NEP/REP
  test exactly the displayed clauses (SUPER uses engine-side digits via
  dmap — decorrelated from the vchain leg; GAM re-derives γ's with the
  general e·g form — a genuine non-textual pin).  One fidelity defect:
  G-1 below (CASC's "line = β̂" sub-clause).
* HAND RE-DERIVATIONS (2 companions + spot checks).  Committed
  YJ3FLT[91,95]: γ₁ = 1, γ₂ = 3; digit i = 1: s₁ = 1 (forced), v₀ =
  (3−1)/2 = 1; ledger ŵ + v₀ + 0 = 17 + 1 = 18 = w₀ ✓; line = 68 +
  4·1 = 72 ✓; defc = 1·2 − 1 − 1 = 0 = Y₂ ✓ (e₁ = 1, Y_c = 1, full
  dump ✓).  Twin [95,95]: defc = 1 = Y₂ = 1, corr rode L (dj0 = 0),
  w₀ = 18 ✓ line 74 ✓.  Fresh YJX1[235,239]: γ₁ = 3, γ₂ = 9; s₁ =
  3⁻¹·9 mod 2 = 1, v₀ = (9−3)/2 = 3; w₀ = 42 + 3 + 0 = 45 ✓; line =
  168 + 4·3 = 180 ✓; defc = 2 − 1 − 1 = 0 = Y₂ ✓.  ALL 15 displayed
  S7.2 v₀ predictions re-derived by hand (YJ2F 2; YJ3F 2,4; YJ3FLT
  1,3; YJ3FLTB 2,6; YJ3DPF 2,3; YJ4FLT 1,3,5; YJT1F 2,4; YJX1 3,8;
  YJX2 1,3; YJX3 1,5; YJX4 1,2,4; YJX6 1; razor corners: YJX2 naive
  2/3 < 1, YJX3 naive = 1, forced s₁ = 1 resp. 2) — every one exact.
* F-E ADJUDICATION: the construct note's bracket (line 386) "[Y₂ = 1:
  the correction rides its X-child, defc = 1]" is CONTRADICTED by its
  own committed artifacts on three independent legs: (1) junk = 1 on
  all Y₂ = 1 companions while the seeding Y-edge already accounts 1
  and an X-child ride would add 1 more; (2) gain = 1 = digit v₀ with
  no π-junk +1 (an X-ride forces gain ≥ v₀ + 1); (3) this battery's
  direct dj0/nX census (nX = 0 on all 11).  The SDYJ note's F-E
  finding is CORRECT as displayed (the Y₂ = 0 bracket is confirmed;
  only the Y₂ = 1 bracket was wrong).
* Wall disclosure ADJUDICATED CORRECT (see charge 4).  The run-1
  (sealed) artifacts were not committed; the "run 1's other ten
  families: 0 violations, same counters" claim rests on the disclosure
  plus determinism (my identical re-run supports it) — n-6.

## 7. Findings

**CRITICAL: none.**

**G-1 (GAP — machine-bracket display).**  S7.1 seals "SDYJ-CASC
cascade cell: ŵ = u₁+u₁′+u₀, residue ≠ 0, line = β̂ (S-L1 shadow…)",
and S3's bracket repeats "line = β̂ on every cascade cell".  As
implemented (sdyj_checks.py lines 315–321) β̂ is DEFINED as the cascade
cell's own line (bhat := crec['line']); the S-L1 formula β̂ = λ̂ +
Σ c_l·q_l is never independently computed by this unit.  The family
genuinely checks ŵ, residue ≠ 0, uniqueness; the "line = β̂" sub-clause
is tautological as implemented.  No proof step is damaged (S-L1 is
consumed†, not re-proved; the companion line-affinity check is real),
but the sealed family display overstates what the runner verifies.

**n-1 (NOTE).**  SDY-L1(a) asserts t_l ∈ [0, g_{l−1}) without the
two-line window arithmetic (a_{l−1} ≤ P_{l−1} − 1 ∧ s_l < e_{l−1} ∧
t_l ∈ ℤ ⟹ interval); ingredients are all quoted in-sentence.

**n-2 (NOTE).**  The single-cell conclusion needs L-CELL(i)
distinctness; it is consumed at S0 but uncited in SDY-L1's proof body
and absent from SDY-L1's claims-table consumption row.

**n-3 (NOTE — display precision).**  S6: "The g₀ = 1 leg is
class-complete: no g₀ = 1 residual remains anywhere."  Under the
corpus box-convention this means "no g₀ = 1 BOX remains" and is right;
read literally it erases the standing pins ((STK), the (H2) discharge
rider, (H1)/T-scope, (RW) for clause (v)) that the same section names
four bullets later and the claims table carries.  Suggest "no g₀ = 1
box remains" or "beyond the standing pins".

**n-4 (NOTE — internal inconsistency).**  F-D cites "grb_order2_check
Tower2 __init__" — the constructor is `Tower`; "Tower2" is the exact
wrong name whose repair S7.3 itself discloses.

**n-5 (NOTE).**  S7.2 preamble "…are exactly the i = 1 values below
plus 0 or 1 units of junk overshoot": all 8 committed gains realize
overshoot 0; no +1 case exists in the record (permissive, not false).

**n-6 (NOTE).**  The sealed run 1's artifacts are uncommitted; its
described outcome (ten families 0 violations, same counters) is a
disclosure backed by determinism, not by a committed artifact.

## Verdict block

SDY-L1: re-derived SOUND from accepted [RMG] + [ILN] definitions alone
(the single-cell exactness holds; all-g-1 entry points and (H2)/(H3)
coverage complete).  SDY-L2: re-derived SOUND from L-NORM(a)(b)(c) +
S2.2 + W-D1/W-D2(iii); no ledger leak.  SDY-L3/(SD-YJ′): anatomy
exhaustive, pins complete — PROVED as displayed at the capped attempt
grade, and genuinely stronger than charged.  SDY-THM: the two proof
deltas vs SD-THM-A are exactly the displayed ones; every-d₀ legitimate
with the (H1)/F-C and d₀ ≥ 3/F-D honesty fences accurate.  Consequence
display exact up to one gloss (n-3); grade caps all verified against
the pass-report record.  Machine leg: re-run identical; 2 companions +
all 15 sealed v₀ predictions hand-re-derived exact; F-E cross-note
contradiction CONFIRMED in the construct note's own artifacts; wall
disclosure confirmed in engine source.  One gap: the SDYJ-CASC family
display (G-1).  No critical error found.

SDYJ-PE1 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
