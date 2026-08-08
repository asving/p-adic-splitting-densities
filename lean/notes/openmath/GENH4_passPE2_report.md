# GENH4 passPE2 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE2 (full complete-theorem bar;
quote-and-classify; fixes nothing). **Target:** `lean/notes/openmath/
GENH4_PROOF_2026-08-08.md` at HEAD (b49e111; note body frozen at r1 dff23f8).
**Arc so far:** skeleton ea5978d → seal 121d9ab → run-1 RED 3eb1667 → run-2
GREEN 4b5c085 → PE1 0C+0G+1m 263a36f → r1 dff23f8 → **PE2 = this**.
**Charges (the PE1-declared UNMINED surfaces):** (1) LEMMA GENH4-1F, the
genre-F fibration itself (PE1 checked only its budgets); (2) LEMMA GENH4-3 +
GENH4-CAP, the ragged-window ledger, never re-derived by anyone; (3) the
e₁-cover claim's interaction with HE6/HE7 — do their post-GENH4 corrected
statements (the widened HE6.B box; the (LIFT) threshold) retro-affect any
GENH4 surface? (4) the eleven R_τ's engine tie at a FRESH prime (q = 11, 13);
(5) supplier-arc currency. Plus the machine leg and a fresh route of my own
choosing (deliberately NOT PE1's tuple scans).

## VERDICT: NOT CLEAN — 1 CRITICAL + 2 GAPS + 2 MINOR (+3 remarks).

The CRITICAL is a **false census factor in the displayed statement of the
note's headline count law** (THEOREM GENH4.A = Q22-L1) at genre-F
boundary-band pins. It is refuted three independent ways: by four committed
artifact rows at q = 2, 3, 5, 7 in BOTH characteristics; by mass conservation
(the displayed census makes the leaf strata **overcount** the entry locus, by
a factor up to q); and by the note's own S6.3 UND display and its own
preregistered P-3 value, which both use the correct factor. **No machine
number and no density conclusion moves** — the runner implements the correct
comp-weighted census (`ex0 = q**comp(dv0) - 1`) and the battery re-runs
bit-identically GREEN. The repair is a one-clause statement fix plus two
sentence fixes (GAP 1), i.e. the note as written misstates a theorem it
proves and measures correctly.

### FINDINGS

* **CRITICAL 1 (S1, THEOREM GENH4.A — the census factor at genre-F
  boundary-band pins; false as displayed, with counter-instances).** S1 reads
  > "C_ℓ = the residual census over F_{q^{f₁}} (f₁ = 1 for E, 2 for F):
  > (Q−1)(Q−2)/2 for SPLITEQ, Q(Q−1)/2 for INERT, **Q−1 for RAM and per
  > 2SIDED pin**, 1 for tails"

  and S6.1 repeats it: "genre F identically with **comp-weighted exponents and
  F_{q²} censuses**" — i.e. only the *exponents* are declared comp-weighted.
  At genre F, S2.3's own slot geometry says the v₁-slot at height m has
  F_q-dimension comp(m) = 2 for m ≤ N−1 and **comp(m) = 1 for
  N ≤ m ≤ N+k−1** (only the a₁-component is in window). A pin AT such a slot
  therefore has census q^{comp(m)} − 1 = **q − 1**, not Q − 1 = q² − 1: the
  in-window data at that slot is a SINGLE F_q-digit (β₁'s digit at height
  N − k), so the number of ways to pin the value there is q − 1; the residual
  letter res(β₁)ȳ + res(β₀) ∈ F_{q²} is not even determined, its res(β₀)
  component being out of window — which is precisely why S1's own GENH4.B
  calls this the "readable-value/unreadable-residual band". The displayed law is false at every
  RAM(N) and 2SIDED(w, N−w) key. Counter-instances, from the **committed**
  artifacts (my own independent recount, `/tmp/pe2/fresh_f3.py`, reproduces
  the left column key-for-key; the right column is what the S1 display gives,
  applying (Q−1) only where S1 states it):

  | row (source) | key | committed | S1-displayed census |
  |---|---|---|---|
  | consF Zp q=7 N=5 k=1 (`genh4_checks_results.json`, = P-3's own prediction) | RAM(5) | **2,117,682** | 16,941,456 |
  | consF Zp q=5 N=5 k=1 (`qscout22_results.json` @ dd67cda) | RAM(5) | **125,000** | 750,000 |
  | consF Fqt q=3 N=5 k=1 (equal char) | RAM(5) | **1,458** | 5,832 |
  | consF Zp q=2 N=7 k=1 | RAM(7) | **128** | 384 |
  | consF Zp q=2 N=7 k=1 | 2SIDED(3,4) | **384** | 1,152 |
  | consF Zp q=2 N=8 k=1 | 2SIDED(3,5) | **1,536** | 4,608 |

  Arithmetically airtight at the q = 7 row: 2,117,682 = ((q²−q)/2)·(q−1)·q⁵ =
  21·6·16,807, whereas 2,117,682/(21·48) = 2100.08… is not a power of 7, so
  **no choice of the exponent X reconciles the displayed census with the
  note's own preregistered P-3 value**. Independent kill by mass
  conservation: with the displayed census the leaf strata sum to MORE than the
  entry locus in **40 of the 50** (q, N, k) cases scanned (q ∈ {2,3,5,7,11} ×
  k ∈ {1,2} × N ∈ [4k+1, 4k+5]; the 10 passes are exactly the (N, k) where no
  RAM(N)/2SIDED(·, N) key is realizable, e.g. N = 4k+2) — e.g. q = 3, N = 5,
  k = 1 gives 2,187 vs q⁶ = 729, a factor-3 overcount; with the comp-weighted
  census, **0 failures in 216 cases** (q ∈ {2,3,4,5,7,8,9,11,13} ×
  k ∈ {1,2,3} × N ∈ [4k+1, 4k+8]). The note's own
  S6.3 UND display uses the correct factor at the same slot ("(q−1)·q²·
  q^{Σcomp(s)…}·q^{k−1}"), so S1's census clause contradicts S1's own
  GENH4.B display. **Scope of damage:** the runner's `law_F` is correct
  (`ex0 = q ** comp(dv0) - 1`; likewise `q ** comp(dv1) - 1` for the w-pin),
  every committed count is correct, the battery is GREEN, and the boundary
  families drain into W-12.D's (A2) tail so the eleven R_τ are unaffected.
  What is wrong is the displayed statement of Q22-L1, the note's title claim.
  **The one charitable alternative reading, priced.** GENH4.A's stability
  clause reads "lift-stable below the caps (dv < 2N for E; v₁ ≤ N **with the
  v₁ = N residual band excluded**, for F)". If "excluded" is read as excluding
  the whole v₁ = N stratum from the LAW's scope (rather than, as it plainly
  says, from lift-stability of the residual), then GENH4.A is not false — it
  simply does not cover the keys RAM(N) and 2SIDED(w, N−w), i.e. it does not
  cover **86% of the (Zp,7,5,k1) row's mass**, the note's own headline fresh
  q = 7 prediction, nor 512 of the 16,384 members of the committed
  (Zp,2,7,k1) row. On that reading the finding is a GAP (an uncovered stratum
  that the note nonetheless counts, predicts and measures) rather than a
  CRITICAL. I grade it CRITICAL because the census clause is stated
  unconditionally over "every prehistory chain … stage history … and leaf ℓ
  with parameters", and because the same sentence's SPLITEQ/INERT censuses are
  correct at every slot — so the reader has no signal that RAM/2SIDED are
  scoped differently. Either way one repair is owed, and it is the same
  repair: say q^{comp(m)} − 1.

* **GAP 1 (S2.3 LEMMA GENH4-CAP(F) + S4 — the dv0 = N exit rule is false as
  stated).** GENH4-CAP(F) ends "readable value, unreadable residual (**the
  reader's dv0 = N → UND exit**)", and S4 lists "(F's u = N residual band →
  UND)" among the conservative exits, both unconditionally. Both are false:
  at **odd** N the key dv0 = N is a DECIDED RAM(N) (S7's RAM bullet needs
  only the one-side shape and the value, which CAP itself certifies stable —
  no residual), and at dv0 = N > 2w it is a DECIDED 2SIDED(w, N−w) (again
  shape-only). The committed artifacts contain both as decided keys —
  RAM(5) = 2,117,682 is **86% of the whole (Zp,7,5,k1) row**, and
  2SIDED(3,4) = 384 sits in the (Zp,2,7,k1) row. UND is the exit only at
  **even** dv0 = N (the integer-slope case that actually consumes the
  residual), which is exactly what S1's GENH4.B display says
  ("present at even N only") and what the runner implements (the `dv0 == N →
  UND` branch is inside the even branch). So the lemma's displayed exit rule
  contradicts the note's own drainage theorem, its runner and its artifacts.
  Same locus as CRITICAL 1; a separate sentence.

* **GAP 2 (S11 — W-12.D is fired at a pin whose hypotheses are, by W-12's own
  later adjudication, insufficient; no fired-clause check exists).** GENH4.D(ii)
  fires "THEOREM W-12.D" pinned "@ w12 seal f669cb0/r2 99f1813", and r1
  (13:59) re-asserted "body unchanged at r2 99f1813, counter 0/2; PE3
  launched … re-running". Since then W-12 ran PE3 (c9c5c0e, 0C+1G+1m) → r3
  (b17238a/b8dfe62) → **PE4 (26689da, 1 CRITICAL + 2 GAPS + 2 minor)** → r4
  (d2d91b7/5728258) → PE5 (c3e2f8e, 0C+1G+3m) → r5 (be4a1dc/ee17210). W-12
  PE4's GAP 1 is directly load-bearing here: as pinned, (A0)+(A1) "never
  assert core-family members are σ-DECIDED nor that the forced σ = σ_F, and
  Step 4's lower bound needs both", with an explicit degenerate instance
  (one family = all window-N monic quadratics labelled `split`) satisfying
  (A0)(A1)(A2) while R_split = 1 ≠ μ_split — i.e. **the r2-pinned W-12.D is
  false as a reduction**, and the version that is true carries an added
  σ-labelling clause introduced only at r4. Two mitigations, both real: (a)
  W-12's own r4 FIRING CHECK has an explicit **n = 4 row** ruling the clause
  "**SUPPLIED**" by THEOREM GENH4.C ("the dictionary IS the σ_F assignment,
  and the quantifier is over every lift of every leaf member") — I read that
  row and agree; (b) GENH4's S7 already closes with "(A0)-strong at the
  stage". So no conclusion moves. What is missing is inside GENH4: its cited
  supplier theorem is the defective revision, the sufficient revision is
  post-pin and uncited, and the note has no fired-clause check for W-12 —
  even though r1 performed exactly that check for HEX3 and PE1's Remark 1
  recommended it as standing practice.

* **MINOR 1 (S12 GH-DENS / S9.2 — the ν₃ ≡ β₃ tie is listed but not
  executed).** S12 lists under GH-DENS "ν₂/ν₃ ties (engine, md5-pinned)", and
  S9.2 asserts "ν₃ (TRP, HMENU3 @ pins): q³·T_τ of HM3.D S5.5 = the engine's
  β₃ term for term". In the runner, ν₂ and ν₂^{(2)} are genuinely tied
  (`dcheck('nu2-vs-beta2', …)`, `dcheck('nu22-vs-betascaled', …)`), but ν₃ is
  **defined** as the engine's value — `nu3 = ENG.beta(3)` with no `dcheck` —
  so within this battery no ν₃ tie is performed and the engine's β₃ is an
  INPUT to the ν₄ assembly (via the D31 child re-entry and the level-0 `3·1`
  shape), which sits slightly athwart GENH4-BOX-6's "the β₄ tie … are
  corroboration legs" scoping. Nothing moves: the identity is machine-checked
  at the supplier (HMENU3 HM3-RTAU, and HM3.D S5.5 states it), and Σβ₃ = 1
  symbolically (my check). Display/battery-claim accuracy only.

* **MINOR 2 (S10-BOX-1 + S11 — the r1 "refreshed to NOW" stack is falsified
  at HEAD in two cells).** (i) "HEX3 at r2 a707430 …, counter 1/2, **PE4 = the
  accepting attempt**": HEX3 PE4 landed NOT CLEAN (34a946b, 0C+0G+1m), the
  counter **reset to 0/2**, and HEX3 r3 landed (b6a1d69) — the acceptance did
  not happen. (ii) "W-12 body unchanged at r2 99f1813" is stale by three
  repair rounds (see GAP 2). Unchanged: GENIND still unopened ✓, HMENU3 still
  ACCEPTED 2/2 (with a post-acceptance ANNEX A, 19c0285, correcting HM3.C's
  (A0) quantifier to the disc ≠ 0 form — which W-12's n = 3 firing row rules
  harmless and which GENH4 does not cite), W-11 ACCEPTED 2/2 ✓. The **minimum
  grade over the stack is unchanged at 0/2**, so P(4)'s conditionality display
  is unaffected — the same disposition r1 recorded, for different reasons.

* **REMARK 1 (unstated admissibility).** No closed form in the note carries
  its domain. The genre-F entry requires v(B₀) = 4k exactly with that digit
  in window, i.e. **N ≥ 4k+1**; genre E requires v(B₀) = 2h exactly, i.e.
  **N ≥ 2h+1**. Below those the displayed totals fail: at (N,k) = (4,1) the
  true slot count is 3 but 4N−10k−4 = 2; at (5,2) it is 2 but the form gives
  −4. Every roster row satisfies the bound, two of them at equality
  ((Zp,7,5,k1) and (Zp,2,11,h5)), so nothing is wrong — the inequality is
  just never written down, and "entry parameter (h resp. k) **admissible**
  over the chain" (S1) is the only gesture at it and is undefined.

* **REMARK 2 (S6.2 bracket wording).** "genre E: q^{δ} … ; as a per-advance
  bracket this is **exactly** GENIND-5's b_stage(μ) = (q−1)q^{2μ−1}" equates
  two different quantities: Σ_{H₂ ⊆ D} L^{|H₂|} = q^{|D|} is the full
  sub-history bracket, while (q−1)q^{δ−1} is the sub-stratum whose LAST
  refine sits at ladder position δ. Both are correct and the displayed
  telescoping identity 1 + Σ_j (q−1)q^{j−1} = q^δ is the bridge; the sentence
  reads as an equality of the two.

* **REMARK 3 (the retro-effect check's by-product, and why CRITICAL 1 is not
  a coincidence).** HE6's corrected (LIFT) — LEMMA HE6-1L = HE7-L1 — says
  exactly that at a height k the reachable residue set is
  {Σ_{t ∈ T(k)} c_t η^t}, ALL of K^× only when T(k) is full. GENH4 never
  consumes it (charge 3 below), and its threshold never bites at GENH4's
  heights. But CRITICAL 1 is the same *shape* of defect arising from a
  different cause (window truncation of the a₀ component at height N rather
  than the i₀ + e₁t threshold): a pin whose reachable residues form a proper
  F_q-subspace of K, priced as if they were all of K^×. The reconciliation's
  "the count laws never consumed (LIFT)" is TRUE for GENH4 — and the
  analogous correction is nonetheless owed inside GENH4's own count law.

---

## Charge 3 (FIRST, as charged) — THE RETRO-EFFECT CHECK: NO retro-effect; verified three ways

HE6/HE7 landed AFTER GENH4 (HE6 seal a77c376 20:18, HE7 1956151 21:21, HE6 r1
+ reconciliation 4f5ebaa/850e77e 21:54/22:14; GENH4 r1 dff23f8 13:59) and
consume GENH4's stage frame. Charge: do their corrected statements — the
widened HE6.B box, and the (LIFT) threshold — reach back?

**(a) Consumption direction: GENH4 cites no HE face.** S11's pin list is
{GENIND, QSCOUT22, W-12, W-11, HEX3/HMENU3, GRTJC/JC-LOAD/W-8, J-D0, DULEMMA,
WELDMASTER/[W12-H], om_density_engine, classical}. No HE3/HE6/HE7 pin, no
(LIFT) citation (grep: zero hits for HE6/HE7/LIFT in the note). So the
reconciliation's claim "the count laws never consumed (LIFT)" is TRUE **for
GENH4 specifically** — verified, not assumed.

**(b) GENH4's own slot lemma IS the D′ = 2 instance of the corrected slot
lemma, and the corrected threshold never bites.** HE6-0″ [r1] gives
dv(A(ξ)) = min_i(e₁v(a_i) + ih) for A = Σ_{i<D′} a_i x^i. At GENH4's genre E,
(e₁, f₁, h, D′) = (2, 1, h, 2) and A = ax + b, so HE6-0″ reads
min(2v(b), 2v(a) + h) — **GENH4-2(E) verbatim**; at genre F,
(e₁, f₁, h, D′) = (1, 2, k, 2), it reads min(v(b), v(a) + k) = **GENH4-2(F)
verbatim**. HE6-1L's attainability: T(k) = {t < f₁ : k ≥ (i₀(k) + e₁t)h}.
* Genre E (f₁ = 1): the reachable set is all of K^× = F_q^× whenever
  T ≠ ∅, and T ≠ ∅ ⟺ k ≥ i₀(k)h, i.e. only ODD dv-heights carry a condition,
  dv ≥ h. GENH4's odd A₁ slots start at 2h+1 and odd A₀ slots at 4h+1 — both
  ≫ h. No bite; and f₁ = 1 means the "proper subspace" failure mode is
  structurally absent at E.
* Genre F (e₁ = 1, i₀ ≡ 0, f₁ = 2): T(m) = {0,1} ⟺ m ≥ k. GENH4's F slots
  start at 2k+1 (A₁) and 4k+1 (A₀) — both > k. No bite.
So the (LIFT) correction leaves every GENH4 surface intact, and in fact
CORROBORATES GENH4-2 (the corrected general lemma specialises to it exactly).

**(c) The widened HE6.B box is vacuous at n = 4 — bound re-derived
independently.** A boxed node needs a repeated irreducible residual factor
(multiplicity m ≥ 2) with ℓ·d_r ≥ 2, hence a side of length
L_λ = ℓ·deg R_λ ≥ ℓ·m·d_r = m·(ℓd_r) ≥ 4, hence μ ≥ 4 and, since a composite
stage has D′ = e₁f₁ ≥ 2, n ≥ D′μ ≥ 8. GENH4's stages have μ = 2 with a
residual of degree 2 in T, so (i) a repeated irreducible factor of degree
≥ 2 would need residual degree ≥ 4 — impossible, and (ii) GENH4's only
repeated residual is the '1sq' case (T − s)², i.e. ℓ = 1 (integer slope dμ)
and d_r = 1 (K-rational linear), so ℓ·d_r = 1: **precisely the configuration
the widened box excludes**. HE6R1's "both branches first bite at n = 8" is
confirmed at n = 4 from GENH4's side.

**(d) The one thing the check did surface** is REMARK 3 / CRITICAL 1 above:
the same failure *shape* is independently present in GENH4's genre-F census
display, for a window-truncation reason rather than a threshold reason.

## Charge 1 — LEMMA GENH4-1F (the fibration itself): VERIFIED, exact, both characteristics

Re-derived from scratch (own sympy expansion, no runner import):

* **The four triangular relations are the expansion of φ² + A₁φ + A₀, term
  for term** — I expanded with φ = x² + p₁x + p₀, A₁ = α₁x + α₀,
  A₀ = β₁x + β₀ and matched all four coefficients plus the leading 1:
  B₃ = 2p₁+α₁ ✓, B₂ = p₁²+2p₀+α₁p₁+α₀ ✓, B₁ = 2p₁p₀+α₁p₀+α₀p₁+β₁ ✓,
  B₀ = p₀²+α₀p₀+β₀ ✓. Triangularity (α₁ ← B₃, then α₀ ← B₂, then β₁, β₀) is
  immediate from the displayed shape, so bijectivity holds coordinate by
  coordinate over any O — the lemma's "digit bijection" is exact, not
  approximate.
* **The budget cancellations are universal identities.** With the entry pins
  p₁ = ĉ₁π^k, p₀ = ĉ₀π^{2k}, B₃ = 2ĉ₁π^k + t₃, B₂ = (ĉ₁²+2ĉ₀)π^{2k} + t₂,
  B₁ = 2ĉ₁ĉ₀π^{3k} + t₁, B₀ = ĉ₀²π^{4k} + t₀ (v(t_j) ≥ (4−j)k+1 = the
  residual pinning of ψ² = y⁴+2c₁y³+(c₁²+2c₀)y²+2c₁c₀y+c₀²), inversion gives
  symbolically α₁ = t₃; α₀ = t₂ − c₁π^k t₃; β₁ = t₁ − c₁π^k t₂ +
  (c₁²−c₀)π^{2k} t₃; β₀ = t₀ − c₀π^{2k} t₂ + c₀c₁π^{3k} t₃. Every term of
  α₀ has v ≥ 2k+1, of β₁ v ≥ 3k+1, of β₀ v ≥ 4k+1 — **exactly the stated
  floors**, and the 2's occur only inside the pin VALUES, never in the
  cancellations, so the derivation is characteristic-uniform (the note's
  "the cancellations are universal identities" checked, not asserted).
* **Node:** v₁(A₁) = min(v(α₁)+k, v(α₀)) ≥ 2k+1 ✓;
  v₁(A₀) ≥ min(3k+1+k, 4k+1) = 4k+1 ✓ (= W-11's C(2S+1, S+1) at S = 2k).
* **Slot count:** (N−k−1)+(N−2k−1)+(N−3k−1)+(N−4k−1) = 4N−10k−4 = the
  W-12.A entry exponent — verified as an integer identity on the whole
  admissible grid, and shown to FAIL below N = 4k+1 (REMARK 1).
* **Constructively:** the battery's GH-FEVEN row is built THROUGH this map
  and read back by the pinned reader (8/8), and my own ledger recount (below)
  reproduces every committed genre-F key from the budget space alone.

## Charge 2 — LEMMA GENH4-3 + GENH4-CAP (the ragged-window ledger): re-derived; ledger CLOSES (and pins CRITICAL 1)

Nobody had re-derived the coherence argument. I rebuilt the strata from the
S2.3/S4 prose alone (own code, `/tmp/pe2/fresh_f3.py`; no runner import) and
tested **mass conservation** — the ledger's real content: at every node,
Σ(leaves) + Σ(refine children) must equal q^{#free slots}, since the strata
are supposed to tile the floored node exactly, with the never-consulted band
priced once as a free factor.

* **Slot strings re-derived.** E: A₁ odd dv = 2v(α₁)+h over
  v(α₁) ∈ [(h+1)/2, N−1] → [2h+1, 2N−2+h]; A₁ even dv = 2v(α₀) →
  [2h+2, 2N−2]; A₀ odd → [4h+1, 2N−2+h]; A₀ even → [4h+2, 2N−2]. Every
  integer of [2h+1, 2N−2] is covered exactly once (parities alternate, so no
  slot is double-listed — this is the content of "the e₁-fold cover, the full
  integer dv-ladder"), and the band {2N ≤ dv ≤ 2N−2+h} holds exactly
  (h−1)/2 odd slots per string, empty at h = 1 ✓. Totals: 4N−5h−3 ✓ = the
  W-12 S2.5 entry exponent. F: A₁ m ∈ [2k+1, N+k−1], A₀ m ∈ [4k+1, N+k−1],
  comp = 2 below N and 1 on [N, N+k−1]; comp-totals 2N−3k−2 and 2N−7k−2,
  summing to 4N−10k−4 ✓.
* **CLOSURE, genre E: 0 failures in 288 cases** (q ∈ {2,3,4,5,7,8,9,11,13} ×
  h ∈ {1,3,5,7} × N ∈ [2h+1, 2h+8], each recursing over all histories). The trichotomy
  (i)/(ii)/(iii) plus the two conservative exits partition every node, with
  the cap 2N as the readability boundary and the band free — GENH4-3's and
  GENH4-CAP(E)'s content, independently confirmed.
* **CLOSURE, genre F with the comp-weighted census: 0 failures in 216 cases**
  (q ∈ {2,3,4,5,7,8,9,11,13} × k ∈ {1,2,3} × N ∈ [4k+1, 4k+8]).
* **CLOSURE, genre F with the S1-DISPLAYED census: 40 of 50 fail** (overcount
  up to ×q). This is the independent, artifact-free kill of CRITICAL 1.
* **Key-for-key artifact reproduction.** My strata reproduce EVERY committed
  genre-F key exactly on consF (Zp,2,7,k1) [9 keys incl. two histories],
  (Zp,2,8,k1), (Zp,3,6,k1), (Zp,5,5,k1), (Fqt,3,5,k1) and the GENH4-battery
  row (Zp,7,5,k1) — under the comp-weighted census; the S1-displayed census
  disagrees on 5 of the 6.
* **The two exit rules re-derived, and where the note's prose diverges.** For
  E, SPLTAIL is decided iff every lift has u ≥ 2N > 2w, i.e. **w < N**, and
  UND is A₀-readable-zero with **w ≥ N**; the UND exponent is then
  (h−1)/2 + #{A₁ slots at dv ≥ N} = (h−1)/2 + ⌊(N+h)/2⌋ + ⌊N/2⌋ =
  N + h − 1 for both parities of N (h odd) — S6.3's "the two floors' parity
  bookkeeping cancels", re-derived. For F, the load-bearing subtlety is that
  a lift CAN attain u = N through the out-of-window β₀ digit at height N, so
  SPLTAIL needs 2w < N and UND takes 2w ≥ N — which is exactly the note's
  "2s ≥ N" and is WRONG if one (as I first did) assumes u ≥ N+1. That
  detail is right in the note and right in the runner. What is wrong is the
  dv0 = N exit rule (GAP 1).
* **Deep-entry spot check by hand (P-3's never-measured row, unchecked by
  PE1):** consE (Zp,2,11,h5): entry (q−1)q^{4N−5h−3} = 2^{16} = 65,536;
  A₀ slots = {21,23,25} (even string [22,20] empty), A₁ slots = 13; ladder
  {2h+1,…,N−1} = {11,…,10} EMPTY so no refine; RAM(21) = (q−1)q^{2+13} =
  32,768 and UND = q^{2+13} = 32,768 — exactly two keys, summing to the
  entry volume. Matches the sealed P-3 and the committed row.

## Charge 4 — the eleven R_τ at FRESH primes q = 11 and q = 13: VERIFIED

Forms typed by hand from S9.4 (`/tmp/pe2/fresh_f2.py`), then pinned against
the note's own q = 2, 3 anchors (22 independent data points in the note):
**0 mismatches** — the transcription is clean, so what follows tests the
forms, not my typing.

* **Σ_τ R_τ = 1** symbolically in ℚ(q); and exactly at q = 11 and q = 13
  (never evaluated in the note or the battery, whose anchors stop at
  q = 2, 3, 5).
* **E[#roots] = Σ_τ #{(1,1) parts}·R_τ = q/(q+1)** symbolically, and exactly
  11/12 at q = 11, 13/14 at q = 13. (Independent sanity anchor: for n = 2 the
  Haar computation gives 2·½·p/(p+1) = p/(p+1), so the "degree-stable"
  reading of S9.4b's spot identity is the right one and the underlying
  measure is Haar on monic quartics over O.)
* **Engine tie at the fresh primes:** R_{(4,1)} = β₄({(4,1)})/q³ from the
  md5-pinned `om_density_engine.py` (7240a916…) — symbolically, and exactly
  1933955/2829537228 at q = 11 and 5200313/12371915934 at q = 13.
* **Own level-0 assembly at the fresh primes.** I rebuilt S9.3's eleven
  f̄-shape censuses myself (C(q,4), C(q,2)n₂, C(n₂,2), qn₃, n₄, qC(q−1,2),
  qn₂, C(q,2), q(q−1), q, n₂ with n_d = #monic irreducibles) and convolved
  with the engine's cluster laws β₂, β₃, β₄, β₂-scaled(2): census = q⁴ exactly
  (14,641 at q = 11; 28,561 at q = 13), **all eleven R_τ reproduced exactly**,
  **no extra types**, Σ = 1 — at both fresh primes.
* **Leading-order cross-check (own):** as q → ∞ the five unramified types
  tend to 1/24, 1/4, 1/3, 1/8, 1/4 = the S₄ cycle-type fractions
  (1+6+8+3+6)/24, and every ramified type is O(1/q) with total ramified mass
  ~1/q. The eleven displayed forms have exactly these asymptotics.

## Charge 5 — supplier-arc currency: two cells falsified (MINOR 2), one load-bearing (GAP 2)

All 18 pinned commits exist with subjects matching their claimed roles and
timestamps consistent with the r1 narrative (verified by `git log -1` on each
of af988ee e1280be 7e5026a 6249166 050425d a707430 f60348b fca1a97 99f1813
8c984db 35e6545 31506b3 839b735 16d12e1 2580f12 671a126 e3f3459 64d3ff9
625fa49 4682bcf 4984004 dd67cda 970197d f669cb0 83f47f4 9387eb1 f819f26).
State at HEAD vs the r1 display: HMENU3 ACCEPTED 2/2 ✓ (+ post-acceptance
ANNEX A 19c0285, harmless here); W-11 ACCEPTED 2/2 ✓; GENIND unopened ✓;
**HEX3 counter reset 1/2 → 0/2 by PE4 (34a946b), now at r3 (b6a1d69)** —
r1's "PE4 = the accepting attempt" falsified; **W-12 now at r5 after a PE4
CRITICAL** — see GAP 2. Minimum grade over the stack unchanged at 0/2, so
P(4)'s conditionality display stands as written.

## Machine leg: GREEN, bit-identical

Runner md5 at HEAD = `ee8024b7a500220a6408dab373d7432f` = the repaired runner
at 3eb1667 = S13.2's claim; the seal-time runner at 121d9ab is
`e5e435c3c345a20e8001be1679a692ae` (the one repaired line). Committed
artifacts `9e6ca9b3…` / `cbcff562…` re-verified at HEAD. Full fresh re-run of
the HEAD runner in an isolated copy of `verification/` (committed artifacts
untouched): **exit 0, GREEN, 937.5 s** (vs S13.2's 947.5 s), family totals
GH-PIN 6 / JSONTIE 481 / FRESH 54 / PRE2 5 / REFINE 192,000 / FEVEN 8 /
PD 46,590 / UND 92 / BRACKET 157 / DENS 115 / SIGMA 6,185 = **245,693 checks,
0 violations**, teeth LAT 19 / CEN 14 / ALPH 4 / SIG 2 / DENS 1. Leaf-diff of
the results JSON vs the committed one: **131 leaves, exactly 1 diff, and it is
the elapsed-time leaf — 0 non-timing diffs.** Counts, families, teeth and
verdict all agree with S13.2 and with PE1's independent re-run.

## Fresh route (own, deliberately different from PE1's tuple scans)

PE1's route was exhaustive coefficient-tuple scans plus own walkers on three
rows. Mine is: (F1) symbolic re-derivation of the genre-F fibration and its
budget cancellations over a symbolic ring (charge 1); (F2) the eleven R_τ at
two never-evaluated primes with an own level-0 assembly (charge 4); (F3) a
**ledger-closure** recount — mass conservation over a 504-case (q, N, h/k)
grid, with the note's displayed census as an armed counter-hypothesis on a
further 50
(charge 2; this is what found CRITICAL 1); (F4) a **mechanism-free σ-density
measurement at a fresh prime**: monic quartics with coefficients uniform in
[0, p^{10}), σ-type read as the (e, f) multiset of the primes above p in the
MAXIMAL order of ℚ[x]/(f) via PARI `nfinit([f,[p]])` + `idealprimedec` — no
Newton polygon, no window counting, no density engine anywhere in the loop.
Result: see the table below (150,000 samples per prime, p = 11 and 13).

**(F4) the mechanism-free σ-density measurement at q = 11 and q = 13.**
150,000 monic quartics per prime, coefficients uniform in [0, p^{10}) (Haar on
O⁴ to precision 10; 0/150,000 reducible over ℚ at either prime, so no
selection bias), σ read from `idealprimedec` on the p-maximal order. This is
the FIRST direct measurement of the density display itself (the battery's
GH-SIGMA is per-member key-vs-σ on stage rows, not a density measurement) and
the first at a prime outside {2,3,5,7}.

| τ | R_τ(11) predicted | measured (n/150,000) | z | R_τ(13) predicted | measured | z |
|---|---|---|---|---|---|---|
| (1,1)⁴ | 0.0239554 | 0.0240067 (3601) | +0.13 | 0.0261108 | 0.0258933 (3884) | −0.53 |
| (1,1)²(1,2) | 0.2097577 | 0.2093733 (31406) | −0.37 | 0.2153667 | 0.2165733 (32486) | +1.14 |
| (1,1)²(2,1) | 0.0319003 | 0.0317733 (4766) | −0.28 | 0.0284644 | 0.0290933 (4364) | +1.46 |
| (1,1)(1,3) | 0.3305804 | 0.3311800 (49677) | +0.49 | 0.3313618 | 0.3306400 (49596) | −0.59 |
| (1,1)(3,1) | 0.0069488 | 0.0069200 (1038) | −0.13 | 0.0051040 | 0.0049933 (749) | −0.60 |
| (1,2)² | 0.1031712 | 0.1035267 (15529) | +0.45 | 0.1064229 | 0.1048733 (15731) | −1.95 |
| (1,2)(2,1) | 0.0381660 | 0.0387067 (5806) | +1.09 | 0.0331483 | 0.0329733 (4946) | −0.38 |
| (1,4) | 0.2479493 | 0.2472933 (37094) | −0.59 | 0.2485287 | 0.2491467 (37372) | +0.55 |
| (2,1)² | 0.0031589 | 0.0029533 (443) | −1.42 | 0.0023559 | 0.0023667 (355) | +0.09 |
| (2,2) | 0.0037286 | 0.0036200 (543) | −0.69 | 0.0027162 | 0.0029467 (442) | +1.72 |
| (4,1) | 0.0006835 | 0.0006467 (97) | −0.55 | 0.0004203 | 0.0005000 (75) | +1.51 |

χ² = 5.02 (q = 11) and 13.88 (q = 13) on 10 df — both comfortable fits
(p ≈ 0.89 and 0.18); every |z| ≤ 1.95, including the three deepest-mass
ramified types (2,1)², (2,2), (4,1) whose predicted densities are 10⁻³–10⁻⁴.
**Exactly the eleven displayed types occurred, at both primes, in 300,000
samples** — an independent corroboration of the display's completeness (a
twelfth type would have shown up at any density above ~2×10⁻⁵). This leg
touches none of the note's machinery: no polygon read, no slot string, no
engine, no window.

## Scope not re-checked here (for the record)

THEOREM GENH4.C's five σ-cases and LEMMA GENH4-4's carry bijection were
audited by PE1 (instance-level, exact rings) and are re-run by the battery
(GH-REFINE 192,000 checks, GH-SIGMA 6,185 PARI); I re-read S7 and S5 for
consistency with the corrected boundary reading (RAM(N) and 2SIDED(·, N) are
shape-decided, so S7 covers them — the σ side of GAP 1 is sound) but did not
re-derive them instance by instance. GENH4-6's liveness chains and the P-D
in-vitro cascade were re-read, not re-scanned (PE1 re-derived them).

**Counter: this is pass PE2 → NOT CLEAN (1C + 2G + 2m) → r2 owed, then PE3.
The 2-clean count has not started.**

## Verifier's own artifacts (session-local; all numbers above are reproduced inline)

* `/tmp/pe2/fresh_f2.py` — the eleven R_τ typed by hand, anchor pin, fresh
  primes, engine tie, own level-0 assembly.
* `/tmp/pe2/fresh_f3.py` — the independent ledger-closure recount (own slot
  strings, own strata, both genres) with the S1-displayed census as an armed
  counter-hypothesis, plus the committed-artifact key-for-key comparison.
* `/tmp/pe2/fresh_f4.gp` / `/tmp/pe2/fresh_f4.out` — the PARI
  `nfinit`+`idealprimedec` σ-density measurement at q = 11, 13.
* `/tmp/pe2/run/` — the isolated copy of `verification/` in which the battery
  was re-run (`/tmp/pe2/rerun.log`); the repo's committed artifacts were never
  written to.
