# GRTW2 passPE6 report — hostile pass 6 on `GRTW2_PROOF_2026-08-08.md` (post-r4; THE would-be accepting attempt)

**Verifier:** Fable hostile pass PE6, fresh context, wallclock 2026-08-07.
**Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` at HEAD — byte-identical
to r4 commit 94534df (`git diff 94534df..HEAD -- <note>` empty; working tree clean
on `verification/` and the note). **Bar:** identical to every prior pass; the
1/2 counter did not soften it. **Inputs read:** all five committed reports
(PE1 083adff / PE2 79e796b / PE3 9bd938f / PE4 e92cb22 / PE5 ba2c47c), the full
note at HEAD (1,331 lines), the GMN print `docs/references/HigherNewton.tex`
at tex 1160–1291 (construct r = 2 and r ≥ 3, Thm `phir` + c₁, the representative
Definition, the fixed-representative sentence), the sealed runner + probe leg +
`iterlawn_pe_reimpl.py` at the cited lines, the committed artifacts. I fixed
nothing.

## VERDICT

**0 CRITICAL ERRORS. 0 JUSTIFICATION GAPS. 0 minor defects. CLEAN — the counter
advances 1/2 → 2/2: this is the arc's second consecutive clean pass, so the
note is ACCEPTED under the arc rule** (the acceptance fold is the
orchestrator's action, not this pass's). The whole note is statement-level TRUE
at HEAD: every box (W2-BOX-1, W2-OPEN-1, W2-OPEN-2 with (OPEN-2a) and the [r3]
converse flag + [r4] o-e precision), the grade cap, the claims table, the
consumer carry-list, and the §4.3 fence are internally consistent and
faithful to their sources; my own census recomputation from the committed JSON
reproduces every figure the fences carry (§D). The machine leg reproduces
byte-for-byte (exit 0, 6,403/0, 17 GREEN, results JSON byte-identical
including elapsed_s; §C). TWO components were re-derived by routes different
from all five prior reports (§A, §B): (1) the m = 1 (ξ, w) closed form, the
W2-C2(a) slot law, Thm-`phir`, the §3.4 display, and the rk. 3 byte law by
**from-definitions two-recipe construction with an independent engine on 560
FRESH OFF-ROSTER junctions (g₁ up to 4, residue fields up to F₂₅ — both beyond
the roster) plus a Sylvester-resultant leg** — 5,568 checks, 0 failures, both
teeth caught; (2) **(HR-REC) by a functional-equation/uniqueness route** in
which W2-L0 and W2-L2 never enter — the recursion is forced by read-additivity
plus the single-slot normalization (derivation displayed in §B, machine-keyed
at the same 566 junctions). Arc accounting is consistent and true at every
surface; PE5's Lean fresh leg was re-extracted from the committed report and
recompiled this pass — exit 0, zero sorry, only the two disclosed deprecation
warnings (§E). Three nil-weight observations; no repair owed.

---

## §A. Fresh component 1 (route unused by PE1–PE5): FROM-DEFINITIONS TWO-RECIPE CONSTRUCTION + SYLVESTER RESULTANT, on fresh off-roster instances

Route decorrelation: PE1 re-derived the closed form algebraically by hand;
PE2 evaluated the displayed formula against the committed ledger (m = 1 slice
+ two hand m = 2 cases); PE3 walked the full committed roster with its own
field arithmetic and formula evaluator; PE4 exhaustively mapped the m = 1
selection geography (residual-level only — no polynomial construction); PE5
proved the integer-exponent system in the Lean kernel. **No prior pass ever
CONSTRUCTED the two competing polynomials from their raw definitions** — the
only existing constructions live in the sealed code (reimpl + GmnLeg), which
every prior instance figure ultimately rode. This pass built both recipes
independently (own field tower, own exact ℤ[x] arithmetic, own Φ-adic dev,
own reads; the print side transcribed directly from tex 1166–1283 — the r = 2
construct display, the r ≥ 3 child prescription y^{(ℓu_j−𝔰_j)/e}c_j(y) mod ψ,
Thm-`phir`'s c₁ and φ(y) = c(ψ − y^f); the harness side from the note's
§1.1 S0.1/S0.2 restatement, semantics cross-checked against the sealed reimpl
by READING, no imports), then compared them at m = 1 junctions (d₀ = 1,
GMN r = 3). Artifact: `/tmp/w2_pe6_fresh.py`, source embedded in Appendix I.

Per junction, EIGHT checks, all from first principles:

* **A (REALIZE R3):** R₁v(C_k, β_k) = ε₁(β_k)⁻¹ψ₁,k for every harness slot.
* **B (THM W2-C2(a)):** ρ_j = R₁v(P_j)/R₁v(C_j) = c·z₁^{A₁e₁j} exactly.
* **C (Thm-`phir` on my own transcription):** my order-2 print residual
  (rescoeff c_i = z₁^{t(i)}R₁(a_i)(z₁), t(i) = (s₁(a_i) − ℓ₀u_i)/e₀ — the
  (s − ℓu)/e arrangement, transcribed from the construct proof / tex 1431
  genre) of my constructed φ₃ equals c·ψ₁ — validating the transcription
  against the print's own theorem before it judges the harness lift.
* **D (THE §3.4 DISPLAY):** R₂(Φ₂^har)(y) = w·ψ₁(ξ·y) with the DISPLAYED
  pair (ξ, w) = (z₁^{−e₁A₁}, 1) — the print residual of the harness lift
  computed from raw definitions, coefficient by coefficient.
* **E (the resultant leg):** the conjugate built a THIRD way — C(y) :=
  Res_t(ψ₁(t), y − ξ⁻¹t) as my own Sylvester determinant over K₁[y]
  (cofactor expansion, polynomial entries) — equals ξ^{−g₁}ψ₁(ξy)
  coefficientwise, and w·ξ^{g₁}·C(y) equals the constructed residual of D.
  (Run at the 263 extension-residue-field junctions, g₀ = 2.)
* **F (rk. 3 byte law):** exact ℤ[x] coefficient-list equality of Φ₂^har vs
  φ₃^cls ⟺ c·z₁^{A₁e₁j} = 1 on supp(ψ₁) ∩ [0, g₁).
* **G (HR-REC):** R₂v(P) = Σ_j ε₁(V_j)·R₁v(P_j)·z₂^j — LHS through my own
  dev + eq12 grid + exact-weight packed read in K₂ = K₁[z₂]/(ψ₁); RHS
  semantic (§B keys what this tests).
* **H (orbit):** the formula pair satisfies the orbit equations against the
  constructed residual (scan-independent).

**Instance set.** Calibration: 6 junctions — the roster's five d₀ = 1 m = 1
junctions (T2A, T2B, T2C, T3B r = 3, T3F r = 3) plus PE3's counter-instance
chamber (F₄, ψ₁ = y³ + ζ, e₀ = 1). My recorded data reproduce the committed
ledger exactly: T2A ξ = z₁² byte-RED, T2C ξ = −1 byte-RED, T2B/T3B/T3F ξ = 1
byte-GREEN, and the counter-instance junction byte-EQUAL with formula pair
(1, 1) — the first reproduction of that chamber's byte side by actual
polynomial construction (PE3/PE4 probed it at the residual level only).
Fresh sweep: **560 off-roster junctions**, deterministic enumeration —
p ∈ {2, 3, 5}; g₀ ∈ {1, 2} (residue fields F₂ … F₂₅ — the roster stops at
F₉); (e₀, h₀) ∈ {(1,1), (2,1), (3,1), (3,2), (4,3)}; (e₁, h₁) ∈ {(1,1),
(2,1), (3,1), (3,2)}; **g₁ ∈ {2, 3, 4}** — the sealed Tower builder
implements only g ≤ 2 (reimpl line 311), so the g₁ ∈ {3, 4} block (including
every sparse-support high-degree ψ₁) is terrain NO roster evidence ever
touched.

**Result: 566 junctions, 5,568 individual checks (A/B 1,106 each; C/D/F/G/H
566 each; E/E2 263 each), 0 failures. Exit 0.** Teeth: (T1) dropping the
ε⁻¹-correction from the harness slots (on the T2A shape, where
ε₁(γ₂) = z₁² ≠ 1) breaks check D — CAUGHT; (T2) forcing the print child
twist T_j = 0 (same shape, T₀ = 4 with z₁⁴ = z₁ ≠ 1) breaks check C —
CAUGHT. Byproduct worth recording: among the 560 fresh junctions, 195 carry
formula ξ ≠ 1 but only 153 are byte-RED — **42 fresh support-invisible-twist
instances at m = 1** (ξ ≠ 1 with ξ^j ≡ 1 on supp ψ₁), abundantly confirming
off-roster the support-triviality-weaker-than-ξ = 1 distinction that W2-C1
and §3.4 rk. 2 fence (the roster exhibits the genre only at I4B r = 4).

Verdict on the closed form: **CONFIRMED on a route independent of every
prior leg and of the sealed code** — the displayed m = 1 pair, the slot law,
the byte law, and the conjugation display all hold from raw definitions on
terrain the roster cannot see.

## §B. Fresh component 2 (route unused by PE1–PE5): (HR-REC) by the functional-equation/uniqueness route

PE1's §A.4 derived (HR-REC) by unfolding the S0.2 read recursion node-by-node
with W2-L0 and the child prescription. This pass derives it so that **neither
W2-L0's grid tie nor W2-L2's Bézout bridge enters** — the recursion is forced
by additivity and the single-slot normalization alone:

Fix level Q, weight λ = V, and the eq12 grid s + je_{Q−1}. Let M_λ be the
O-module of f whose Φ_{Q−1}-dev digits A_i sit at grid abscissas with
w_{Q−1}(A_{s+je}) ≥ V_j, V_j := (λ − (s+je)γ_Q)/e_{Q−1}. Consider the two
functionals M_λ → K_Q: Ψ₁ := the S0.2 level-Q read at λ, and Ψ₂(f) :=
Σ_j ε_{Q−1}(V_j)·R_{Q−1}v(A_{s+je})·z_Q^j.

1. **(Additivity.)** Both are additive on M_λ: the dev is additive, and each
   level read at a fixed weight is additive on the weight-≥ module — by
   induction from level 0, where res(·/π^β) is additive on {v ≥ β}, with
   strictly-above digits reading 0.
2. **(Single-slot law.)** On a single-slot element A·Φ_{Q−1}^{s+je}
   (deg A < deg Φ_{Q−1}), Ψ₁ gives ε_{Q−1}(V_j)·R_{Q−1}v(A)·z_Q^j — this IS
   the packed-read definition (S0.2's C_j), not a computation; Ψ₂ gives the
   same by construction.
3. **(Spanning.)** The dev decomposition writes every f ∈ M_λ as a finite
   sum of single-slot elements.

Hence Ψ₁ = Ψ₂ on all of M_λ. The print output P = construct(r, V, φ) =
Σ_j P_j·φ_{r−1}^{s+je_{r−1}} lies in M_λ with dev digits EXACTLY the
children: (i) deg P_j < m_{r−1} = deg Φ_{Q−1} (the construct's own degree
property, tex (ef)) makes the defining sum its own base-Φ expansion, by
uniqueness of the dev; (ii) the slots are on-line at exactly V_j — the
construct property v_{r−1}(P_j) = V_j through the v = w dictionary (the
probe's sealed P-index pin). Applying Ψ₁ = Ψ₂ to P is verbatim (HR-REC). ∎

The ε-and-twist collapse ε(V_j)·z^{T_j} = z^{A·k_j} is the SUBSEQUENT
sentence of §3.1 (that one is W2-L2, machine-keyed CK-MM) — the display
(HR-REC) itself needs none of it, and the note's presentation (recursion
first, collapse second) is faithful to this structure. Machine key: §A's
G-check exercises exactly the three legs — dev = placement (uniqueness),
slot weights = V_j (on-line), grid/packing alignment — plus the identity, at
566 junctions including all 560 fresh, 0 failures. **CONFIRMED by a route on
which the recursion is a uniqueness theorem, not a computation.**

## §C. Machine leg (re-run this pass)

* **Seals:** `grt_w2_checks.py` sha256 `71f8fc90…ba52` byte-identical at
  working tree, seal commit 5463f2a, and HEAD ✓; `grt_weld_probe.py`
  `107c92b6…4ea9` byte-identical to seal commit 55f7416 and HEAD ✓; both
  committed artifacts hash-identical to HEAD before the run ✓
  (results JSON e6e845ed…, output ace257b6…).
* **Re-run (in a /tmp copy of the three sealed modules): exit 0. 6,403
  samples, 0 violations, 17 families GREEN, boundary junctions = 1, teeth
  MT-TW CAUGHT.** Produced results JSON **byte-identical to the committed
  artifact including elapsed_s (3.2)** — `diff` empty; stdout differs only
  in one intermediate timing figure (1.0 → 0.9 s at the T3D row) and the
  JSON-path line (expected from /tmp). Per-family counts match §6.1 exactly
  (CK-MM 4,396 · CK-HR1/VD1 156 · CK-REC 55 · CK-SLOT 44/16 · CK-XI 22 ·
  CK-BYTE 28 · TW-RATIO/ADM/STRICT 44 each · TW-F3/F3b 684 each · TW-PARI
  12 · TW-QO 7 · CK-T3E 2 · MT-TW 2). `git status verification/` clean
  before and after.

## §D. Statement-level truth of the whole note at HEAD

* **Census recomputation (committed JSON, own parser, own is-one test, own
  SKIP/walk classification):** 44 junction-levels = 16 r = 2 + 28 r ≥ 3 ✓;
  22 walked + 6 SKIP, all 6 SKIPs byte-RED ✓; walked split 12 RED/10 GREEN
  (→ 18/10) ✓; recorded ξ ≠ 1 ⟺ byte-RED at 22/22 walked, 0 exceptions ✓;
  every below-r₀ junction byte-GREEN ✓; first-twist census T2A/C/D/G = 3,
  T3A/C/D/E = 3, T3B/F = 4, I4B = 5, I4C = 3, T2B/E/F + I4A none ✓;
  above-twist = exactly {T3A/T3C/T3D/T3E r = 4; I4C r = 4, 5} ⟹ 38/6 ✓;
  instance-warranted = exactly {I4A r = 5, I4B r = 5} ⟹ 36 + 2 ✓; I4B
  ledger [(3, (1,1)), (4, (1,1)), (5, (−1,−1))], r = 4 byte-equal, r = 5
  byte-RED, the run's sole CK-XI boundary ✓. Every figure carried by the
  grade cap, §5.2, §6.1, §6.2, §6.3(d) matches.
* **The §3.5 boundary witness, recomputed from the committed I4B spec**
  (reads (3,2,1),(2,1,1),(1,1,2),(2,1,1), ψ₀ = y+1, ψ₂ = 1+y²): ℓ₀ = 2,
  γ₂ = 13, A₁ = 4, A₂ = 13, χ₂ = z₁⁴ = 1, ξ₃ = z₂^{−13} = −1, invisible on
  supp {0, 2}; ξ₄: e₂ = 1 ⟹ ℓ₂ = 0 ⟹ A₃ = 0, χ₃ = χ₂ = 1 ⟹ ξ₄ = 1 —
  every bracket figure exact ✓.
* **LEMMA W2-ID1** re-derived (recorded (1, w) + the unconditional display ⟹
  w = 1 at j = 0 via ψ₁(0) ≠ 0 ⟹ ξ_f^j = 1 on supp incl. the monic top ⟹
  c·z₁^{A₁e₁j} = ξ_f^{g₁−j} = 1 on supp ∩ [0, g₁) = rk. 3's byte law) —
  sound; its premise (the m = 1 display) now carries §A's from-definitions
  confirmation. The [r3] "Consequently" one-directional ✓; the
  counter-instance block faithful and TRUE (my §A calibration constructs the
  chamber; c = 1, byte-equal, all of F₄* in the stabilizer) ✓.
* **Identification-token disposition (my own grep at HEAD): 31 tokens on 30
  lines** — scoped [r3]/[r4] sites (119, 727, 789, 807/809, 979, 981, 1006,
  1036) each one-directional or roster-scoped ✓; struck spans preserved as
  record (720, 802–803, 1004) ✓; historical/arc records quoting the cured
  species (36, 1040, 1137/1139, 1217/1221, 1285–1306) ✓; different senses
  (600 letter identification; 931/1097 overflow identification) ✓; the
  instance-exactness claims machine-true two-sidedly (22/22, §D bullet 1) ✓.
  **No residual two-sided assertion at HEAD.** (See o-1 on PE5's count
  figure.)
* **Boxes and fences:** W2-OPEN-1 statement matches what TW-F3 runs (684
  groups, 0; control 0) and stays OPEN ✓; W2-OPEN-2's premise carries the
  P3-corrected Φ_{q−1} pairing (dictionary-exact per §1.2), the [r3]
  converse flag, the [r4] o-e precision (the recorded chamber's top junction
  IS its r₀ — 2 reads — verified), and (OPEN-2a) stated one-directionally
  with honest Status ✓; W2-BOX-1 matches CK-SLOT/CK-XI (exactly 1 boundary)
  ✓; the §4.3 fence stands with the r2-reverted sign — my own read of the
  print's construct proof (t(j) = (s_{r−2}(P_j) − ℓ_{r−2}u_j)/e_{r−2}, the
  (s − ℓu)/e arrangement) and of tex 1201's child exponent
  (ℓ_{r−2}u_j − 𝔰_j)/e_{r−2} confirms the two-referent split of §2.3
  [r2, P2] and the r0 sign t ↦ t − k·u_i ✓.
* **Source-line citations re-verified at the seals:** `orbit_scan` def at
  runner line 135, `return out` at 163, 164 blank ✓ (o-c figure exact);
  "only g in {1,2} implemented" at reimpl line 311 ✓; `Ext.elems` product
  comprehension at reimpl 220–222, (0,1) = ζ before (1,0) = 1 for F₄ ✓
  (see o-2); TW-PARI "PREDICT: 24/24" at runner docstring line 77 vs the
  executed 12 ✓ (the [r1, F4] disclosure accurate).
* **Grade cap / claims table / consumer face:** internally consistent; every
  PROVED row is proved at the stated scope (clause 2 m = 1 now confirmed on
  a from-definitions route; m ≥ 2 correctly split (C-coll)/recursion/
  boundary); every OPEN row is genuinely open; the four-route adjudication
  stands as displayed (verified at source by PE1/PE2 with a fifth-route
  hunt; not re-opened — no new consumption since) ✓.

## §E. The arc system — CONSISTENT AND TRUE; the counter

* **Chain vs git (clock-ordered, hashes and verdicts exact):** composed
  5463f2a (08-04 15:59) → PE1 083adff (08-06 19:16; 0C+2G+5m ✓) → r1
  8d5e3fa (19:45) → PE2 79e796b (08-07 08:20; 0C+2G+1m ✓) → r2 ffa1e57
  (08:35) → PE3 9bd938f (09:18; 0C+1G ✓) → r3 79d1d9c (09:31) → PE4
  e92cb22 (14:03; 0C+1G+1m ✓) → r4 94534df (14:20) → PE5 ba2c47c (15:03;
  CLEAN, counter 0/2 → 1/2 ✓). Note byte-frozen since 94534df ✓; runner +
  artifacts byte-frozen through the whole arc ✓.
* **The note's [r4] S-STATUS ("counter 0/2, FOUR passes run, PE5 next") is a
  dated as-of-r4 record** — correct under the freeze convention (a clean
  pass edits nothing; the counter lives in the committed reports; the
  2-clean rule requires PE6 to grade the SAME text PE5 graded, which this
  pass did). The live counter per PE5's committed report: 1/2 with PE6 the
  would-be accepting attempt — this pass ✓.
* **PE5's fresh leg re-verified:** Appendix I of the committed PE5 report
  extracted verbatim and recompiled against the repo's pinned toolchain —
  `lake env lean` **exit 0, zero sorry**, exactly the two disclosed
  `Int.ediv_add_emod` deprecation warnings. The arc's first clean pass
  stands on a reproducible leg.
* **Verdict of this pass: CLEAN. Counter 1/2 → 2/2 — two consecutive clean
  passes on the same frozen text: the note is ACCEPTED at its displayed
  grades and conditionality** (clause 2 m = 1 unconditional / m ≥ 2 on
  (C-coll) with (HR-REC) exact and W2-BOX-1; clause 1 on the byte-shared
  perimeter with the W2-C1a chamber qualifier; clause 3 proved-to-first-
  recorded-twist riding W2-ID1/(OPEN-2a) one-directionally, MEASURED above
  riding W2-OPEN-2; value layer = W2-OPEN-1, open; §4.3 review-owed).
  Orchestrator items at the fold, unchanged from the r1/r2 records: the WM
  (M4) annotation + "its only commit" staleness (now WM line 111), the JB
  §0M row-15 annotation.

**Ungraded observations (nil weight, no repair owed):**

* **(o-1)** PE5 §A.2's headline figure "27 hits" for the `identification`
  grep does not reproduce: at the identical frozen text the count is 31
  tokens on 30 lines. PE5's own disposition list COVERS all 30 lines (its
  enumerated sites plus the 1285–1306 range), and my independent
  disposition (§D) confirms completeness — the figure reads as a count of
  grouped sites, not tokens. A slip inside a committed report, invisible to
  the note and to every consumer; verdict-irrelevant then and now.
* **(o-2)** The counter-instance block cites "`Ext.elems` =
  `itertools.product(base.elems(), repeat=g)`, iterlawn_pe_reimpl.py line
  220": the `def` header sits at 220, the product expression at 221.
  Content-true as cited by PE3/PE4/PE5; sub-token imprecision.
* **(o-3)** §A's fresh sweep shows the invisible-twist genre is ABUNDANT at
  m = 1 off-roster (42 of 560 junctions: ξ ≠ 1, byte-GREEN, ξ support-
  trivial) — strong independent corroboration of §3.4 rk. 2 / W2-C1's
  support-triviality fence and of why the converse selection question
  (PE3's counter-instance) had to stay unclaimed. Recorded for any future
  round that considers pinning a selection rule.

## Repair queue implied

**None.** CLEAN; counter 2/2; acceptance per the arc rule, fold owed to the
orchestrator.

---

## Appendix I — the fresh-leg source (`/tmp/w2_pe6_fresh.py`, run exit 0 this pass)

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GRTW2 PE6 fresh leg — route unused by PE1-PE5: FROM-DEFINITIONS TWO-RECIPE
CONSTRUCTION at m=1 junctions (d0=1), on FRESH OFF-ROSTER instances
(g1 up to 4; the roster builder caps g<=2), with a SYLVESTER-RESULTANT leg
for the conjugate polynomial.

Independent of the sealed runner/reimpl/probe: no imports from them; own
field tower, own integer-polynomial arithmetic, own dev, own reads, own
print transcription straight from HigherNewton.tex 1166-1283 (construct r=2
and r=3, Thm phir c1), own rescoeff/t(i) order-2 residual (tex 1431/1447).

Per instance (p, (e0,h0,g0,psi0), (e1,h1,g1,psi1)):
  HARNESS: Phi1 (std lift), Phi2 = Phi1^{e1g1} + sum realize1(eps1^{-1}psi1k)
  PRINT:   phi3 = Phi1^{e1g1} + sum construct(2,Vj,phij)*Phi1^{j e1}  [tex]
  CHECKS:
   A  REALIZE-R3: R1v(C_k, beta_k) == eps1(beta_k)^{-1} psi1_k
   B  W2-C2(a) slot law: rho_j = R1v(P_j)/R1v(C_j) == c * z1^{A1 e1 j}
   C  Thm-phir on own transcription: R2print(phi3) == c * psi1
   D  THE DISPLAY: R2print(Phi2^har)(y) == w * psi1(xi*y), (xi,w)=(z1^{-e1A1},1)
   E  RESULTANT: Sylvester Res_t(psi1(t), y - xi^{-1} t) == xi^{-g1} psi1(xi y)
      and display RHS == w * xi^{g1} * that resultant
   F  BYTE LAW (rk.3): bytes(Phi2)==bytes(phi3) <=> c*z1^{A1 e1 j}==1 on supp
   G  HR-REC at the junction: R2v(P) == sum_j eps1(V_j) R1v(P_j) z2^j
   H  ORBIT: the formula pair satisfies the orbit equations (scan all units)
  TEETH: (T1) drop the eps^{-1} correction in Phi2 -> D must fail somewhere
         (T2) force T_j = 0 in the print child -> C must fail somewhere
  CALIBRATION: roster m=1 junctions T2A/T2B/T2C/T3B/T3F + PE3's
  counter-instance; recorded pairs and byte verdicts vs the committed ledger.
"""
import sys, json, itertools
from math import gcd

# ---------------- fields: F_p and one extension step ----------------
class Fp:
    def __init__(s, p): s.p = p
    def zero(s): return 0
    def one(s): return 1
    def add(s,a,b): return (a+b)%s.p
    def sub(s,a,b): return (a-b)%s.p
    def mul(s,a,b): return (a*b)%s.p
    def neg(s,a): return (-a)%s.p
    def inv(s,a):
        assert a%s.p, "inv 0"
        return pow(a, s.p-2, s.p)
    def is_zero(s,a): return a%s.p==0
    def eq(s,a,b): return (a-b)%s.p==0
    def elems(s): return list(range(s.p))
    def lift(s,a): return a%s.p     # canonical lift to {0..p-1}

class Ext:
    """K = base[t]/mod, mod monic (list of base elems, len g+1, mod[-1]=1).
    Elements: tuples of base elems, length g."""
    def __init__(s, base, mod):
        s.B, s.mod = base, mod
        s.g = len(mod)-1
        assert base.eq(mod[-1], base.one())
    def zero(s): return tuple(s.B.zero() for _ in range(s.g))
    def one(s):  return tuple(s.B.one() if i==0 else s.B.zero() for i in range(s.g))
    def from_base(s,a): return tuple(a if i==0 else s.B.zero() for i in range(s.g))
    def gen(s):  return tuple(s.B.one() if i==1 else s.B.zero() for i in range(s.g))
    def add(s,a,b): return tuple(s.B.add(x,y) for x,y in zip(a,b))
    def sub(s,a,b): return tuple(s.B.sub(x,y) for x,y in zip(a,b))
    def neg(s,a): return tuple(s.B.neg(x) for x in a)
    def is_zero(s,a): return all(s.B.is_zero(x) for x in a)
    def eq(s,a,b): return s.is_zero(s.sub(a,b))
    def reduce_list(s, L):
        L = list(L)
        while len(L) > s.g:
            c = L.pop()
            if s.B.is_zero(c): continue
            d = len(L) - s.g   # x^{len(L)} = x^{d} * x^{g}; x^g = -sum mod[i] x^i
            for i in range(s.g):
                L[d+i] = s.B.sub(L[d+i], s.B.mul(c, s.mod[i]))
        while len(L) < s.g: L.append(s.B.zero())
        return tuple(L[:s.g])
    def mul(s,a,b):
        L = [s.B.zero()]*(2*s.g-1)
        for i,x in enumerate(a):
            if s.B.is_zero(x): continue
            for j,y in enumerate(b):
                if s.B.is_zero(y): continue
                L[i+j] = s.B.add(L[i+j], s.B.mul(x,y))
        return s.reduce_list(L)
    def inv(s,a):
        # extended Euclid in base[t] on (mod, a)
        assert not s.is_zero(a)
        B = s.B
        def pdeg(f):
            d=-1
            for i,c in enumerate(f):
                if not B.is_zero(c): d=i
            return d
        def pscale(f,c): return [B.mul(x,c) for x in f]
        def psub(f,g):
            n=max(len(f),len(g)); f=f+[B.zero()]*(n-len(f)); g=g+[B.zero()]*(n-len(g))
            return [B.sub(x,y) for x,y in zip(f,g)]
        def pmulx(f,k): return [B.zero()]*k + f
        r0, r1 = list(s.mod), list(a)
        s0, s1 = [B.zero()], [B.one()]
        while True:
            d1 = pdeg(r1)
            assert d1 >= 0
            if d1 == 0:
                c = B.inv(r1[0])
                return s.reduce_list(pscale(s1, c))
            d0 = pdeg(r0)
            if d0 < d1:
                r0, r1, s0, s1 = r1, r0, s1, s0; continue
            c = B.mul(r0[pdeg(r0)], B.inv(r1[d1]))
            k = pdeg(r0) - d1
            r0 = psub(r0, pmulx(pscale(r1, c), k))
            s0 = psub(s0, pmulx(pscale(s1, c), k))
    def elems(s):
        return [tuple(t) for t in itertools.product(s.B.elems(), repeat=s.g)]
    def lift(s,a): raise NotImplementedError

def fpow(F, z, k):
    if k < 0: return fpow(F, F.inv(z), -k)
    r = F.one()
    b = z; kk = k
    while kk:
        if kk & 1: r = F.mul(r, b)
        b = F.mul(b, b); kk >>= 1
    return r

# poly-over-field helpers (lists of field elems, index = degree)
def fp_trim(F, f):
    while f and F.is_zero(f[-1]): f.pop()
    return f
def fp_eval(F, f, x):
    r = F.zero()
    for c in reversed(f): r = F.add(F.mul(r,x), c)
    return r
def fp_mul(F, f, g):
    if not f or not g: return []
    L = [F.zero()]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if F.is_zero(a): continue
        for j,b in enumerate(g):
            if F.is_zero(b): continue
            L[i+j] = F.add(L[i+j], F.mul(a,b))
    return L
def fp_is_irred(F, f):
    # monic deg<=4 over small field: no root (deg 2,3); deg 4 also no monic quad factor
    d = len(f)-1
    assert F.eq(f[-1], F.one())
    if d == 1: return True
    for x in F.elems():
        if F.is_zero(fp_eval(F, f, x)): return False
    if d <= 3: return True
    if d == 4:
        for a in F.elems():
            for b in F.elems():
                # divide f by t^2 + a t + b, check remainder zero
                q = list(f)
                for i in range(d, 1, -1):
                    c = q[i]
                    if F.is_zero(c):
                        continue
                    q[i] = F.zero()
                    q[i-1] = F.sub(q[i-1], F.mul(c,a))
                    q[i-2] = F.sub(q[i-2], F.mul(c,b))
                if F.is_zero(q[0]) and F.is_zero(q[1]): return False
        return True
    raise NotImplementedError

# ---------------- integer polynomial layer (O = Z, pi = p, exact) ----------
def zp_trim(f):
    while f and f[-1]==0: f.pop()
    return f
def zp_add(f,g):
    n=max(len(f),len(g)); f=f+[0]*(n-len(f)); g=g+[0]*(n-len(g))
    return zp_trim([a+b for a,b in zip(f,g)])
def zp_mul(f,g):
    if not f or not g: return []
    L=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a==0: continue
        for j,b in enumerate(g):
            if b==0: continue
            L[i+j]+=a*b
    return zp_trim(L)
def zp_pow(f,k):
    r=[1]
    for _ in range(k): r=zp_mul(r,f)
    return r
def zp_dev(f, Phi):
    """base-Phi digits (Phi monic over Z): [A_0, A_1, ...], deg A_i < deg Phi."""
    f=list(f); out=[]
    dP=len(Phi)-1
    while f:
        if len(f)-1 < dP:
            out.append(zp_trim(list(f))); f=[]
            break
        # divmod by monic Phi
        q=[0]*(len(f)-dP)
        r=list(f)
        for i in range(len(f)-1, dP-1, -1):
            c=r[i]
            if c:
                q[i-dP]=c
                for k2 in range(dP+1):
                    r[i-dP+k2]-=c*Phi[k2]
        out.append(zp_trim(r[:dP]))
        f=zp_trim(q)
    return out
def vp(n, p):
    assert n!=0
    v=0
    while n%p==0: n//=p; v+=1
    return v

# ---------------- one m=1 junction: everything from definitions ------------
class Junction:
    def __init__(s, p, e0,h0,g0, psi0, e1,h1,g1, psi1):
        s.p=p; s.e0,s.h0,s.g0=e0,h0,g0; s.e1,s.h1,s.g1=e1,h1,g1
        s.F0=Fp(p)
        s.psi0=psi0  # list over F0, monic deg g0, psi0[0]!=0
        if g0==1:
            s.K1=s.F0; s.z1=s.F0.neg(psi0[0])
            s.K1_from0=lambda a:a
        else:
            s.K1=Ext(s.F0, psi0); s.z1=s.K1.gen()
            s.K1_from0=lambda a:s.K1.from_base(a)
        s.psi1=psi1  # list over K1, monic deg g1, psi1[0]!=0
        s.K2=Ext(s.K1, psi1); s.z2=s.K2.gen()
        s.l0,s.lp0 = s.bez(e0,h0); s.l1,s.lp1 = s.bez(e1,h1)
        s.gam1=h0; s.wPhi1=e0*g0*h0; s.gam2=e1*s.wPhi1+h1
        s.A1=s.l0*g0*s.gam1
        s.Phi1=s.build_Phi1()
    @staticmethod
    def bez(e,h):
        if e==1: return 0,1
        l=next(x for x in range(e) if (x*h)%e==1)
        return l,(1-l*h)//e
    # canonical lift K1 -> Z[x]-coefficient... for d0=1 digits are ints
    def liftF0(s,a): return a % s.p
    def K1coords(s,a):
        return [a] if s.g0==1 else list(a)
    def eq12(s, beta, e,h,l):
        sx=(l*beta)%e; u=(beta-sx*h)//e
        assert u*e+sx*h==beta
        return sx,u
    def eps1(s, beta):
        sx,u=s.eq12(beta, s.e0,s.h0,s.l0)
        return fpow(s.K1, s.z1, s.lp0*sx - s.l0*u)
    def build_Phi1(s):
        out=[0]*(s.e0*s.g0)+[1]
        for k in range(s.g0):
            ck = s.psi0[k]
            if s.F0.is_zero(ck): continue
            term=[0]*(s.e0*k); term=term+[ (s.p**((s.g0-k)*s.h0)) * s.liftF0(ck) ]
            out=zp_add(out, term)
        return out
    def realize1(s, tau, beta):
        sx,u=s.eq12(beta, s.e0,s.h0,s.l0)
        out=[]
        for nu,c in enumerate(s.K1coords(tau)):
            if s.F0.is_zero(c): continue
            expo=u-nu*s.h0
            assert expo>=0, "negative pi exponent in realize1"
            mono=[0]*(sx+nu*s.e0)+[(s.p**expo)*s.liftF0(c)]
            out=zp_add(out,mono)
        return out
    def w1(s, A):
        assert A
        return min(s.e0*vp(c,s.p)+i*s.h0 for i,c in enumerate(A) if c)
    def R1v(s, A, beta):
        """level-1 read at weight beta (requires w1(A)>=beta)."""
        sx,u=s.eq12(beta, s.e0,s.h0,s.l0)
        r=s.K1.zero() if s.g0>1 else 0
        for a in range(sx, len(A), s.e0):
            c=A[a]
            if c==0: continue
            sw=(beta-a*s.gam1)//s.e0
            assert (beta-a*s.gam1)%s.e0==0
            v=vp(c,s.p)
            assert v>=sw, "digit below line"
            if v>sw: continue
            digit=(c//(s.p**sw))%s.p
            j=(a-sx)//s.e0
            term=fpow(s.K1, s.z1, j)
            term=s.K1.mul(s.K1_from0(digit), term)
            r=s.K1.add(r,term) if s.g0>1 else s.F0.add(r,term)
        return r
    def build_Phi2(s, garble_eps=False):
        out=zp_pow(s.Phi1, s.e1*s.g1)
        s.har_slots={}
        for k in range(s.g1):
            ck=s.psi1[k] if s.g1>0 else None
            if s.K1.is_zero(ck) if s.g0>1 else s.F0.is_zero(ck): continue
            bk=(s.g1-k)*s.gam2
            e=s.eps1(bk)
            tau = ck if garble_eps else s.K1.mul(s.K1.inv(e), ck)
            Ck=s.realize1(tau, bk)
            s.har_slots[k]=Ck
            out=zp_add(out, zp_mul(Ck, zp_pow(s.Phi1, s.e1*k)))
        return out
    # ---- print side (tex transcription) ----
    def print_construct_r3(s, force_Tj_zero=False):
        K1=s.K1
        c1=fpow(K1, s.z1, -s.l0*s.g0*s.h0)      # tex 1270 via v2(phi2)=e0 g0 h0
        c=fpow(K1, c1, s.e1*s.g1)
        V=s.e1*s.g1*s.gam2
        sx=(s.l1*V)%s.e1                        # W2-L0 initial abscissa of T
        u=(V-sx*s.h1)//s.e1
        assert sx==0, "top junction s=0 expected"
        s.print_slots={}
        P=[]
        for j in range(s.g1):
            cj_res = s.psi1[j]
            if (K1.is_zero(cj_res) if s.g0>1 else s.F0.is_zero(cj_res)): continue
            cj=K1.mul(c, cj_res)
            uj=u-j*s.h1
            Vj=uj-(sx+j*s.e1)*s.wPhi1
            sj=(s.l0*Vj)%s.e0
            upj=(Vj-sj*s.h0)//s.e0
            assert (s.l0*uj-sj)%s.e0==0, "T_j not integral"
            Tj=0 if force_Tj_zero else (s.l0*uj-sj)//s.e0
            phij=K1.mul(fpow(K1, s.z1, Tj), cj)   # the child residual element
            # construct(2, Vj, phij): place the K0-coordinates of phij
            Pj=[]
            for nu,cc in enumerate(s.K1coords(phij)):
                if s.F0.is_zero(cc): continue
                expo=upj-nu*s.h0
                assert expo>=0, "negative exponent in construct2"
                mono=[0]*(sj+nu*s.e0)+[(s.p**expo)*s.liftF0(cc)]
                Pj=zp_add(Pj,mono)
            s.print_slots[j]=(Pj, Vj)
            P=zp_add(P, zp_mul(Pj, zp_pow(s.Phi1, sx+j*s.e1)))
        s.c1, s.c, s.V = c1, c, V
        phi3=zp_add(zp_pow(s.Phi1, s.e1*s.g1), P)
        return phi3, P
    # ---- print order-2 residual (rescoeff + t(i), tex 1373/1431/1447) ----
    def R1_print(s, a):
        """order-1 residual of a in O[x] on its own lambda_1-side: attained
        initial abscissa s1(a), coefficients red(a_i/pi^{u_nu})."""
        beta=s.w1(a)
        att=[i for i,c in enumerate(a) if c and s.e0*vp(c,s.p)+i*s.h0==beta]
        s1=min(att)
        out=[]
        i=s1; nu=0
        while i < len(a):
            c=a[i] if i<len(a) else 0
            w=(beta-i*s.h0)
            if c and s.e0*vp(c,s.p)==w:
                assert w%s.e0==0
                out.append(s.K1_from0((c//(s.p**(w//s.e0)))%s.p))
            else:
                out.append(s.K1.zero() if s.g0>1 else 0)
            i+=s.e0; nu+=1
        while out and (s.K1.is_zero(out[-1]) if s.g0>1 else s.F0.is_zero(out[-1])):
            out.pop()
        return s1, out
    def R2_print(s, X):
        """order-2 residual of X on the junction-slope side (lambda = h1/e1),
        via dev by phi2=Phi1, ordinates u_i = w1(a_i) + i*v2(phi2),
        rescoeff c_i = z1^{t(i)} R1(a_i)(z1), t(i)=(s1(a_i)-l0*u_i)/e0."""
        dv=zp_dev(X, s.Phi1)
        v2phi2=s.wPhi1
        pts={}
        for i,A in enumerate(dv):
            if not A: continue
            pts[i]=s.w1(A)+i*v2phi2
        m=min(s.e1*u+i*s.h1 for i,u in pts.items())
        onside=sorted(i for i,u in pts.items() if s.e1*u+i*s.h1==m)
        s2=onside[0]
        out=[]
        i=s2
        while i<=onside[-1]:
            if i in pts and s.e1*pts[i]+i*s.h1==m:
                A=dv[i]; ui=pts[i]
                s1a,R1a=s.R1_print(A)
                assert (s1a-s.l0*ui)%s.e0==0, "t(i) not integral"
                ti=(s1a-s.l0*ui)//s.e0
                val=fp_eval(s.K1, R1a, s.z1)
                ci=s.K1.mul(fpow(s.K1,s.z1,ti), val)
            else:
                ci=s.K1.zero() if s.g0>1 else 0
            out.append(ci)
            i+=s.e1
        while out and (s.K1.is_zero(out[-1]) if s.g0>1 else s.F0.is_zero(out[-1])):
            out.pop()
        return s2, out
    # ---- level-2 read (for HR-REC) ----
    def w2(s, f):
        dv=zp_dev(f, s.Phi1)
        return min(s.e1*s.w1(A)+j*s.gam2 for j,A in enumerate(dv) if A)
    def R2v(s, f, lam):
        dv=zp_dev(f, s.Phi1)
        sx,u=s.eq12(lam, s.e1,s.h1,s.l1)
        r=s.K2.zero()
        for a in range(sx, len(dv), s.e1):
            A=dv[a]
            if not A: continue
            sw=(lam-a*s.gam2)//s.e1
            assert (lam-a*s.gam2)%s.e1==0
            wA=s.w1(A)
            assert wA>=sw, "digit below line (R2v)"
            if wA>sw: continue
            cj=s.K1.mul(s.eps1(sw), s.R1v(A,sw)) if s.g0>1 else \
               s.F0.mul(s.eps1(sw), s.R1v(A,sw))
            j=(a-sx)//s.e1
            term=s.K2.mul(s.K2.from_base(cj), fpow(s.K2, s.z2, j))
            r=s.K2.add(r,term)
        return r
    # ---- Sylvester resultant conjugate ----
    def conj_by_resultant(s, xi):
        """C(y) = Res_t(psi1(t), y - xi^{-1} t) as poly in y over K1,
        via Sylvester determinant with symbolic y (poly-in-y entries)."""
        K1=s.K1
        g=s.g1
        xinv=K1.inv(xi)
        def kconst(c): return [c]
        Y=[K1.zero(), K1.one()]
        Z=[]
        psirow=[kconst(s.psi1[g-i]) if i<=g else Z for i in range(g+1)]
        M=[psirow]
        for r in range(g):
            row=[Z]*(g+1)
            row[r]=kconst(K1.neg(xinv))
            row[r+1]=Y
            M.append(row)
        def padd(f,gp):
            n=max(len(f),len(gp)); f=f+[K1.zero()]*(n-len(f)); gp=gp+[K1.zero()]*(n-len(gp))
            out=[K1.add(a,b) for a,b in zip(f,gp)]
            while out and K1.is_zero(out[-1]): out.pop()
            return out
        def pmul(f,gp):
            if not f or not gp: return []
            L=[K1.zero()]*(len(f)+len(gp)-1)
            for i,a in enumerate(f):
                if K1.is_zero(a): continue
                for j,b in enumerate(gp):
                    if K1.is_zero(b): continue
                    L[i+j]=K1.add(L[i+j],K1.mul(a,b))
            while L and K1.is_zero(L[-1]): L.pop()
            return L
        def pneg(f): return [K1.neg(a) for a in f]
        def det(Mx):
            n=len(Mx)
            if n==1: return Mx[0][0]
            out=[]
            for c in range(n):
                e=Mx[0][c]
                if not e: continue
                sub=[[Mx[r][cc] for cc in range(n) if cc!=c] for r in range(1,n)]
                term=pmul(e, det(sub))
                out=padd(out, term if c%2==0 else pneg(term))
            return out
        return det(M)

    def K1_is_one(s, a):
        return s.K1.eq(a, s.K1.one()) if s.g0>1 else s.F0.eq(a,1)
    def K1eq(s,a,b):
        return s.K1.eq(a,b) if s.g0>1 else s.F0.eq(a,b)
    def K1mul(s,a,b):
        return s.K1.mul(a,b) if s.g0>1 else s.F0.mul(a,b)
    def K1inv(s,a):
        return s.K1.inv(a) if s.g0>1 else s.F0.inv(a)
    def K1zero(s,a):
        return s.K1.is_zero(a) if s.g0>1 else s.F0.is_zero(a)

def run_junction(J, checks, teeth=False):
    fails=[]
    K1=J.K1; F0=J.F0
    Phi2=J.build_Phi2()
    phi3, P = J.print_construct_r3()
    xi=fpow(K1, J.z1, -J.e1*J.A1)
    w=K1.one() if J.g0>1 else 1
    # A: REALIZE R3
    for k,Ck in J.har_slots.items():
        bk=(J.g1-k)*J.gam2
        want=J.K1mul(J.K1inv(J.eps1(bk)), J.psi1[k])
        got=J.R1v(Ck, bk)
        checks['A']+=1
        if not J.K1eq(got,want): fails.append(('A',k))
    # B: slot ratio law
    for j,(Pj,Vj) in J.print_slots.items():
        rp=J.R1v(Pj, Vj)
        rh=J.R1v(J.har_slots[j], (J.g1-j)*J.gam2)
        rho=J.K1mul(rp, J.K1inv(rh))
        want=J.K1mul(J.c, fpow(K1, J.z1, J.A1*J.e1*j))
        checks['B']+=1
        if not J.K1eq(rho,want): fails.append(('B',j))
    # C: Thm-phir on own transcription
    s2,R=J.R2_print(phi3)
    want=[J.K1mul(J.c, cj) for cj in J.psi1]
    got=list(R)
    while len(got)<len(want): got.append(K1.zero() if J.g0>1 else 0)
    checks['C']+=1
    okC=(s2==0 and len(got)==len(want) and all(J.K1eq(a,b) for a,b in zip(got,want)))
    if not okC: fails.append(('C',s2))
    # D: THE DISPLAY on the harness lift
    s2h,Rh=J.R2_print(Phi2)
    disp=[J.K1mul(w, J.K1mul(fpow(K1,xi,j), J.psi1[j])) for j in range(J.g1+1)]
    goth=list(Rh)
    while len(goth)<len(disp): goth.append(K1.zero() if J.g0>1 else 0)
    checks['D']+=1
    okD=(s2h==0 and all(J.K1eq(a,b) for a,b in zip(goth,disp)))
    if not okD: fails.append(('D',s2h))
    # E: resultant conjugate (K1 an Ext; run when g0>1)
    if J.g0>1:
        C=J.conj_by_resultant(xi)
        conj=[J.K1mul(fpow(K1,xi,j-J.g1), J.psi1[j]) for j in range(J.g1+1)]
        got=list(C)
        while len(got)<len(conj): got.append(K1.zero())
        checks['E']+=1
        if not all(J.K1eq(a,b) for a,b in zip(got,conj)): fails.append(('E',))
        rhs=[J.K1mul(w, J.K1mul(fpow(K1,xi,J.g1), c)) for c in got]
        gothp=list(goth)
        while len(gothp)<len(rhs): gothp.append(K1.zero())
        checks['E2']+=1
        if not all(J.K1eq(a,b) for a,b in zip(gothp,rhs)): fails.append(('E2',))
    # F: byte law
    byte_eq = (zp_trim(list(Phi2))==zp_trim(list(phi3)))
    law = all(J.K1_is_one(J.K1mul(J.c, fpow(K1,J.z1,J.A1*J.e1*j)))
              for j in range(J.g1) if not J.K1zero(J.psi1[j]))
    checks['F']+=1
    if byte_eq != law: fails.append(('F',byte_eq,law))
    # G: HR-REC
    if P:
        lhs=J.R2v(P, J.V)
        rhs=J.K2.zero()
        for j,(Pj,Vj) in J.print_slots.items():
            cj=J.K1mul(J.eps1(Vj), J.R1v(Pj,Vj))
            rhs=J.K2.add(rhs, J.K2.mul(J.K2.from_base(cj), fpow(J.K2,J.z2,j)))
        checks['G']+=1
        if not J.K2.eq(lhs,rhs): fails.append(('G',))
    # H: orbit — formula pair satisfies the orbit equations
    def satisfies(xih, wh):
        pred=[J.K1mul(wh, J.K1mul(fpow(K1,xih,j), J.psi1[j])) for j in range(J.g1+1)]
        return all(J.K1eq(a,b) for a,b in zip(goth+[K1.zero() if J.g0>1 else 0]*(len(pred)-len(goth)), pred))
    checks['H']+=1
    if not satisfies(xi,w): fails.append(('H',))
    return fails, byte_eq, xi, w

def main():
    total=0; nfail=0; results=[]
    checks=dict(A=0,B=0,C=0,D=0,E=0,E2=0,F=0,G=0,H=0)
    # ---------- calibration: roster m=1 junctions ----------
    cal=[]
    F2=Fp(2); F3=Fp(3)
    K1_T2A=Ext(F2,[1,1,1])
    cal.append(('T2A', Junction(2, 2,1,2,[1,1,1], 2,1,1,[K1_T2A.gen(),K1_T2A.one()]),
                False, 'z^2'))  # ledger xi=1+z=z^2, byte RED
    cal.append(('T2B', Junction(3, 3,1,1,[1,1], 2,1,1,[2,1]), True, '1'))
    cal.append(('T2C', Junction(3, 2,1,1,[1,1], 3,2,1,[2,1]), False, '2'))
    cal.append(('T3B_r3', Junction(3, 3,1,1,[1,1], 2,1,1,[1,1]), True, '1'))
    K1_T3F=Ext(F3,[1,0,1])
    cal.append(('T3F_r3', Junction(3, 1,2,2,[1,0,1], 3,1,1,[K1_T3F.gen(),K1_T3F.one()]), True, '1'))
    K1_CI=Ext(F2,[1,1,1])
    ci_psi1=[K1_CI.gen(), K1_CI.zero(), K1_CI.zero(), K1_CI.one()]
    cal.append(('PE3-CI', Junction(2, 1,1,2,[1,1,1], 2,1,3,ci_psi1), True, '1'))
    print("== CALIBRATION (roster + PE3 counter-instance) ==")
    for name,J,exp_byte,exp_xi in cal:
        fails, byte_eq, xi, w = run_junction(J, checks)
        total+=1
        K1=J.K1
        if exp_xi=='1': xok=J.K1_is_one(xi)
        elif exp_xi=='2': xok=J.K1eq(xi,2)
        elif exp_xi=='z^2': xok=J.K1eq(xi, K1.mul(K1.gen(),K1.gen()))
        print(f"  {name:8s} byte_eq={byte_eq} (exp {exp_byte})  xi_ok={xok}  fails={fails}")
        if fails or byte_eq!=exp_byte or not xok: nfail+=1
    # ---------- fresh off-roster sweep ----------
    print("== FRESH OFF-ROSTER SWEEP (g1 up to 4) ==")
    def irred_polys(F, g, limit):
        out=[]
        for tail in itertools.product(F.elems(), repeat=g):
            if F.is_zero(tail[0]): continue
            f=list(tail)+[F.one()]
            if fp_is_irred(F,f): out.append(f)
            if len(out)>=limit: break
        return out
    count=0
    byte_green=0; byte_red=0; xi_nontriv=0
    for p in (2,3,5):
        F=Fp(p)
        for g0 in (1,2):
            if g0==1:
                psi0s=[[a,1] for a in range(1,p)][:2]
            else:
                psi0s=[f for f in irred_polys(F,2,2)]
            for psi0 in psi0s:
                if g0==1:
                    K1=F
                else:
                    K1=Ext(F,psi0)
                for e0,h0 in ((1,1),(2,1),(3,1),(3,2),(4,3)):
                    if gcd(e0,h0)!=1: continue
                    for e1,h1 in ((1,1),(2,1),(3,1),(3,2)):
                        if gcd(e1,h1)!=1: continue
                        for g1 in (2,3,4):
                            if p**(g0*1)>9 and g1>3: continue
                            psi1s=irred_polys(K1,g1,1)
                            for psi1 in psi1s:
                                J=Junction(p, e0,h0,g0, psi0, e1,h1,g1, psi1)
                                fails, byte_eq, xi, w = run_junction(J, checks)
                                total+=1; count+=1
                                if fails:
                                    nfail+=1
                                    print(f"  FAIL p={p} e0h0g0=({e0},{h0},{g0}) psi0={psi0} "
                                          f"e1h1g1=({e1},{h1},{g1}) psi1={psi1}: {fails}")
                                if byte_eq: byte_green+=1
                                else: byte_red+=1
                                if not J.K1_is_one(xi): xi_nontriv+=1
    print(f"  fresh junctions: {count}  byte GREEN/RED: {byte_green}/{byte_red}  "
          f"xi nontrivial: {xi_nontriv}")
    # ---------- teeth ----------
    print("== TEETH ==")
    KT=Ext(Fp(2),[1,1,1])
    JT=Junction(2, 2,1,2,[1,1,1], 2,1,1,[KT.gen(),KT.one()])
    Phi2g=JT.build_Phi2(garble_eps=True)
    JT.print_construct_r3()
    s2g,Rg=JT.R2_print(Phi2g)
    xi=fpow(JT.K1, JT.z1, -JT.e1*JT.A1)
    disp=[JT.K1mul(fpow(JT.K1,xi,j), JT.psi1[j]) for j in range(JT.g1+1)]
    gotg=list(Rg)
    while len(gotg)<len(disp): gotg.append(JT.K1.zero())
    t1_caught = not (s2g==0 and all(JT.K1eq(a,b) for a,b in zip(gotg,disp)))
    print(f"  T1 (eps dropped): display violated = {t1_caught}")
    JT2=Junction(2, 2,1,2,[1,1,1], 2,1,1,[KT.gen(),KT.one()])
    JT2.build_Phi2()
    phi3g,_=JT2.print_construct_r3(force_Tj_zero=True)
    s2t,Rt=JT2.R2_print(phi3g)
    wantC=[JT2.K1mul(JT2.c,cj) for cj in JT2.psi1]
    gotC=list(Rt)
    while len(gotC)<len(wantC): gotC.append(JT2.K1.zero())
    t2_caught = not (s2t==0 and all(JT2.K1eq(a,b) for a,b in zip(gotC,wantC)))
    print(f"  T2 (T_j forced 0): phir residual violated = {t2_caught}")
    if not (t1_caught and t2_caught): nfail+=1
    print("== SUMMARY ==")
    print(f"  junctions total: {total}   check counts: {checks}")
    print(f"  FAILURES: {nfail}")
    return 0 if nfail==0 else 1

if __name__=='__main__':
    sys.exit(main())
```

(Run record this pass: the source above was extracted from this appendix
back to `/tmp/w2_pe6_fresh.py` and run VERBATIM as the final leg — exit 0;
calibration 6/6 with ledger-exact ξ and byte verdicts; fresh 560 junctions,
byte 407 GREEN / 153 RED, ξ ≠ 1 on 195; check counts A/B 1,106 each,
C/D/F/G/H 566 each, E/E2 263 each — 5,568 checks, 0 failures; teeth T1/T2
both caught. Two earlier runs of comment-level variants of the same source
produced figure-identical output.)

— PE6, GRTW2 acceptance arc, 2026-08-07.
