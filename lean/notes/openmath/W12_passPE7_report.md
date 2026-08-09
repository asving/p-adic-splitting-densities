# W12 passPE7 report — hostile verification pass 7 (fresh context) of W12_PROOF_2026-08-08.md — THE ACCEPTANCE ATTEMPT

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD =
r5 (be4a1dc + markup fix ee17210) + the PE6-m1 dated record (**c2afad3**,
2026-08-09). Read first: all six prior reports (PE1 2b47711, PE2
1be15d2, PE3 c9c5c0e, PE4 26689da, PE5 c3e2f8e, PE6 ef258fe), the
dated-record diff, and the consumer notes at HEAD (HMENU3 incl. ANNEX A
@ 19c0285; GENH4 @ 4b0d946 + append-only annex stack; GENHN post-errata
E1–E3; HE7 frozen; GENIND 2/2). This pass fixes nothing; it quotes and
classifies. Charged attack order: (1) the DATED RECORD itself
(charge-mandated); (2) the never-owned trust boundary — the S3.2
witness construction re-derived by hand, the (A0)/(A1)/(A2)
instance-bundle DEFINITIONS audited as definitions; (3) the error
envelope's q-uniformity (where proved / whether needed); (4) the
three-readings equivalence re-derived + machine-checked with an
INDEPENDENT Haar leg; (5) the firing table end-to-end at HEAD; (6)
free hunt. Fresh instrument `/tmp/w12_pe7_fresh.py` (no repo imports),
log `/tmp/w12_pe7_fresh.log`; isolated battery re-run in
`/tmp/w12_pe7_iso/` (log `pe7_run.log`).

**VERDICT: CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAP + 1 MINOR
(+ 3 uncounted remarks). The 2-clean counter COMPLETES: 1/2 → 2/2.
W-12 IS ACCEPTED; THE REDUCTION (THEOREM W-12.D) IS FROZEN (dated
appends only). The chain's conditionality narrows to the
HEX3/GENHN/HE6 arc grades + the displayed frontier boxes.**

The r5+record text held everywhere this pass attacked it. The one
surviving defect is record-accuracy inside the new dated record itself
(MINOR 1 — its GENHN line anchors were already stale at its own commit
and its third bullet's descriptor is wrong as written; the harmlessness
classifications survive on the actual sentences, verified here). The
mathematics held at every never-owned surface: the S3.2 witness pair
re-derived by hand in both characteristics including the t = N parity
corner and the disc valuations; the (A1) bundle definition audited
clause by clause with one uncounted type-annotation remark; the
envelope question resolved (the proof consumes NO decay rate and NO
q-uniformity of the envelope — hypotheses are per-q, the "SAME
expression" clause rides only (A1)'s data-q-independence; corroborated
by a live ε-degraded bundle); the three readings (series / decided-core
limit / Haar μ_τ) re-derived and, for the first time in the arc, tied
to a μ_τ computed INDEPENDENTLY of the note's entire apparatus (LEG A).
Machine leg: seal intact, SEVENTH green run at identical counts.

---

## 1. FINDINGS

### MINOR 1 — the PE6-m1 dated record's GENHN anchors were stale at the record's own commit, and its third bullet misdescribes the L440-hit as "the second occurrence of the same slot-min sentence"

**Quotes (the record, note L1937–1943):** "**GENHN_PROOF L153**
('slot-min EXACTLY, for every root θ and every lift — W-9's …')" and
"**GENHN_PROOF L440** — the second occurrence of the same slot-min
sentence; harmless by the same PE6 classification as L153."

**Facts (verified against git):** the GENHN errata E1–E3
(bc1b996/961d0ff/46bf675, 2026-08-09 09:23–09:26) edited
GENHN_PROOF in place BEFORE PE6's verdict commit (ef258fe, 09:39) and
before the record (c2afad3, 10:03). At the record's own HEAD: the
slot-min sentence sits at **L156** (sole occurrence; L153 carries
unrelated text), and the second grep hit sits at **L548**, which is
NOT the same sentence — it is the dv-display's universality clause
("for every root θ of Φ′ and every lift; the minimum's residue class
mod e₁ …"), a DIFFERENT sentence of the same slot-min/valuation genre.
Even pre-errata (850e77e: hits at L153/L440/L631) the L440 sentence was
that distinct dv-display clause, so "second occurrence of the same …
sentence" was never right; PE6's own report carried the same collapsed
description, and the record transcribed it without re-anchoring at its
HEAD.

**Classification: MINOR** (record accuracy in a dated append; no
conclusion moves). I verified the substance survives on the actual
sentences: L156 and L548 are both valuation/slot-min facts true of
every lift — exactly the genre the sweep's W-11 row excuses ("valuation
facts, not σ-certifications") — and HEX3 L438 is verbatim as the record
quotes it at HEAD. *Repair shape: one dated line re-anchoring the two
GENHN hits (L156, L548 at HEAD) and re-describing hit 3 as the
dv-display's distinct universality clause, same genre.*

### Remarks (uncounted, no repair owed)

* **R-1 ((A1) leaves c_F(q)'s type implicit).** The clause writes
  "dens_F(x) = c_F(q)·q^{−ℓ_F(x)}" with "all data … independent of q";
  Step 1 concludes "∈ ℚ(q)", which needs c_F(q) ∈ ℚ(q). The hostile
  alternative readings are unfirable: exactness (counts ∈ ℤ at every
  prime power) forces a constant c_F into ℤ and every in-corpus
  supplier provides polynomial c_F; the display's own usage (a
  coefficient carried through the geometric-series algebra) is the
  ℚ(q) reading. One-phrase hardening available ("c_F(q) ∈ ℚ(q)"), not
  owed for acceptance.
* **R-2 (the n ≥ 6 firing row's conservative staleness persists at
  HEAD — PE5 R-1/PE6 R-1 lineage).** HE7 is now ACCEPTED 2/2 (frozen @
  ca3754d) and claims [GENHN-HE(μ)] discharged at composition grade
  ("modulo the arc grade", HE7 L288–305); W-12's row still says "NOT
  supplied — … the named open box". Under-claims only; honest.
* **R-3 (the W12-PIN family does not close its import graph).** The
  isolated re-run required two files beyond the five pinned imports:
  `engine_ext.py` (imported at module level by the pinned
  `grt_jc_probe.py`) and `grb_order2_check.py` (imported by
  engine_ext). engine_ext internally pins grb_order2_check
  (dab62713… — verified matching at HEAD); nothing in the w12 chain
  pins engine_ext itself (md5 today d7eba6ac…). Verified inert for the
  w12 legs (w12 consumes only W10.ZpWin/FqtWin/gp_run +
  W11.classify_full/predict, none engine_ext-dependent) and the
  seventh run reproduced §S10 content-identically. Instrument-hygiene
  note for future seals; the note's own W12-PIN claim ("violation if a
  pinned file moved") is accurate as scoped.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) The dated record (c2afad3), verified.** Byte-freeze REAL: first
122,242 bytes of the note at HEAD md5 **ab1f768c…** == the full file at
ee17210 (append-only). Its sentences are enumerated/scoped (record
rule held). HEX3 L438 quote verbatim at HEAD. GENHN anchors → MINOR 1.
I re-ran the sweep's own grep at HEAD over the six-note scope: GENHN
now hits L156/L548/L780 (first two = MINOR 1's sentences, third =
the sweep's own GENH4/GENHN-row phrase); the GENHN errata introduced
NO new in-scope hits; HMENU3's L218 original + L881 (inside ANNEX A,
quoting-and-correcting) are covered by the applied annex; the GENH4
hits are in-proof valuation/configuration phrases inside its
disc ≠ 0-restricted statements (the sweep row's stated rationale);
W-12's own L486/L595/L847 hits are factorization/data-sharing/
construction sentences, not σ-certifications.

**(2) The trust boundary — the witness construction and the bundle
definitions (never owned before as definitions).**

* *LEMMA W12-S3.2 + the [r4] repair, re-derived by hand from zero:*
  member y³ + b₂y² (b₂ ∈ πO/π^N, t = v(b₂), B = π^N at b₂ = 0).
  Lift 1 = y(y² + By + π^{2K+1}), 2K+1 ≥ max(N, 2t+2): congruence to
  the member needs exactly 2K+1 ≥ N ✓; quadratic polygon
  {(0,2K+1),(1,t),(2,0)} has its vertex at 1 iff 2t < 2K+1 ✓; the two
  Hensel roots re-derived at valuations t and 2K+1−t (derivative
  2z + u a unit at both approximate roots INCLUDING char 2, where it
  is u); disc F_A = (B²−4π^{2K+1})·π^{2(2K+1)} with v(B²−4π^{2K+1}) =
  2t in every characteristic (eq-char 2: the 4-term vanishes leaving
  B² ≠ 0; mixed 2: v(4π^{2K+1}) = 2K+3 > 2t; else ≥ 2K+1 ≥ 2t+2) —
  the [r4] display's claim, confirmed. Lift 2 = y³ + By² + π^L,
  L ≥ 3N, L−t odd: vertex-at-2 needs L > 3t — automatic at t ≤ N−1
  and supplied by PARITY at t = N (L = 3N would make L−t = 2N even) —
  the [r4] bracket is exactly the needed step; g(s) = s³ + us² +
  π^{L−3t} has g′(−u) = u² a unit in EVERY characteristic (3u²−2u²;
  char 3: = u²; char 2: = u²) and L−3t ≥ 1 odd ✓; the complementary
  block's roots at (L−3t)/2 ∉ ℤ ⟹ e = 2 irreducible ✓;
  disc F_B = −4B³π^L − 27π^{2L} nonzero in all five cases (eq-2:
  −27π^{2L}, 27 odd; eq-3: −4B³π^L, −4 ≠ 0; p ≥ 5 and mixed: valuation
  comparison 3t+L vs 2L resp. 2+3t+L vs 2L, min attained, ≠ 0). The
  deleted B = 0 branches fail exactly as recorded (eq-2 Lift 1:
  disc = −4π^{2K+1} = 0; eq-3 Lift 2: F′ ≡ 0). Both lifts ≡ the member
  mod π^N incl. the B-terms at t = N ✓. Count q·q^{N−1} ✓. σ_A ≠ σ_B ✓
  ⟹ undecided in the pinned (BOX-7 clause 1) sense ✓.
* *The (A1) definition as a definition:* parameter sets = finite
  unions of shifted products (Step 1's [r1] point-coordinate guard and
  [r2] integrality derivation re-derived: ℓ integer-valued on P_F ⟹
  m_ib_i ∈ ℤ_{>0} by two-point evaluation, ℓ(base) ∈ ℤ — and
  integer-valuedness itself is forced by the exactness clause at every
  prime power); disjointness + exact counts + one label per family are
  precisely what Steps 3–4 consume; the [r4] σ-LABELING clause = BOX-7
  clause 1 with forced σ = σ_F, TOTAL by the [r4] R-1 argument
  (re-verified: generic disc ≢ 0, invertible affine substitution,
  nonzero polynomial on O^n with O infinite). c_F type → R-1 remark.
  (A2)'s r = the complement by definition; its display note ("drainage
  of the REST") re-checked against the n = 2 instance's SPLIT-TAIL
  routing (count (q−1)q^{N−1} per center per w admits no N-free dens).
* *The n = 2 instance data re-computed from W12-L0 aggregates:* RAM
  aggregate per center (q−1)q^{2N−u−2} (history bracket q^{(u−1)/2}),
  ×q centers = dens·q^{2N} with dens = (q−1)q^{−h−1} ✓; 2SIDED
  (q−1)²q^{2N−w₁−w₂−2} ✓; SPLITEQ/INERTDEEP ((q−1)(q−2)/2 resp.
  q(q−1)/2)·q^{2N−2k−2} ✓; all four series + both R-brackets re-summed
  by hand: R_split = q³/(2q²(q+1)) = q/(2(q+1)) ✓, R_inert ✓, Σ = 1 ✓.

**(3) The error envelope's uniformity in q — resolved, no gap.**
W-12.D's hypotheses are quantified per prime power ("suppose, at every
prime power q simultaneously" = the package holds for each q); (A2) is
per-q convergence r(N)/q^{nN} → 0 with NO rate and NO cross-q
uniformity — and the proof consumes none: Step 1 is symbolic algebra,
Step 2 a per-q monotone net, Steps 3–4 per-q limits. The conclusion's
"SAME expression at every prime power" rides exclusively (A1)'s
q-independence of (families, c_F, ℓ_F, P_F, ν_F): the summed expression
is one element of ℚ(q), evaluated per q. Nothing in the note claims or
needs a q-uniform envelope; the displayed rate (W-12.B's c_n(q)q^{−N})
belongs to the CONJECTURE only, cleanly fenced. Machine corroboration:
LEG B1 (the ε-degraded bundle) delivers the same R_τ with an envelope
slower by a factor > 10³ at N = 60.

**(4) The three-readings equivalence, re-derived + machine-tied.**
Reading 1 (the series) = Reading 2 (decided-core window limit): Step
2's monotone partial-sum net over visible sets increasing to P_F
(ν_F affine ⟹ exhaustion; nonneg terms) — re-derived. Reading 2 =
Reading 3 (Haar μ_τ): the Step-4 squeeze re-derived at both bounds
(lower: disjoint cylinder unions, the σ-LABELING clause, disc = 0
null; upper: truncation of a disc ≠ 0 type-τ F into a visible class
forces σ_F = τ via the same clause applied at F, else the rest; both
ends → R_τ by Step 2 + (A2)); wellposedness (Krasner-open τ-partition
of the étale locus, valid in equal characteristic since disc ≠ 0 ⟹
separable; disc = 0 null in both characteristics) — classical as
displayed. Machine: LEG A ties Reading 3 to Reading 1 through
computations of μ_τ that use NONE of the note's apparatus (§4).

**(5) The firing table end-to-end at HEAD.** n = 2: W-11 ACCEPTED 2/2
(fold 35e6545); row's pinned-strength leg unchanged. n = 3: HM3.C
quote byte-faithful at HMENU3 L216–219; ANNEX A APPLIED at 19c0285 as
a dated append (both corrected sites quoted there with the
counter-instance; body frozen), so the row's disc ≠ 0 form is now
supplied ON THE SUPPLIER'S OWN PAGE as well. n = 4: THEOREM GENH4.C
re-read at HEAD — verbatim as the row transcribes it (statement + both
dictionaries); HEAD vs pin 4b0d946 = 966 INSERTIONS, zero deletions
(append-only; body frozen). n = 5: THEOREM GENHN.C re-read at HEAD —
the errata E1–E3 did not touch it (diff grep empty on its statement
lines); the row's dictionary transcription drops the ambient
"(·e_A, ·f_A)"-block qualifier, exact where fired (n = 5 has trivial
ambient; towers need n ≥ 8 per LEMMA GENHN-T). n ≥ 6: "NOT supplied"
remains TRUE-as-under-claim at HEAD (R-2); the box [GENHN-HE(μ ≥ 3)]
is still GENHN's displayed box (L813), and HE7's discharge claim is
composition-grade, arc-conditional — the row hides nothing and
over-claims nothing.

**(6) Free hunt.** LEMMA W12-S2.1's injectivity re-derived (minimal-k
divergence level, 2(k−1) ≥ k at k ≥ 2, coprimality forces Ā_i = 0 by
degree); the separable-pattern all-lift decidedness behind S3.1's
partition re-derived (irreducible reduction ⟹ irreducible unramified
factor for EVERY lift — the disc ≠ 0 restriction is not even needed
there); S2.4's RAM2LIN row re-derived from S2.2 (heights, L = 2,
vertex parity, σ); S3.3's lower bound re-checked incl. the n = 3 and
n−2 = 1 corners; the S2.2 census sweep re-checked against the
(q−1)²-not-(q−1)³ cross-check; the [r3]/[r4]/[r5] arc displays counted
(exactly one CURRENT); no dangling [r5]/record reference found.

## 3. MACHINE LEG

* **Seal + pins:** `verification/openmath/w12_checks.py` md5
  **7dc040d94fbbb1e8d20ac817b665d418** == `git show f669cb0:…`;
  all five W12-PIN imports at their pinned md5s (500aae15…/a9c34244…/
  cae45db2…/03811b69…/d3a5e13d…); committed artifacts at §S10's md5s
  (0557b15f… / 05776c9e…) before AND after this pass (the re-run was
  fully isolated in /tmp — repo bytes never touched).
* **SEVENTH isolated green run** (detached, pidfile): exit 0,
  **3,232,506 checks / 0 violations**, teeth **23 / 23 / 8 / 1273**,
  324.2 s. Output diff vs committed = timing only; JSON
  content-identical after stripping timing keys (programmatic compare
  == True). Two dependency files beyond the pinned five were required
  to run in isolation (R-3): both verified (engine_ext's own pin on
  grb_order2_check matches at HEAD).
* **Tautology audit (spot):** the witness-builder slice (runner
  L1040–1067) re-read — byte-consistent with the [r5] CITE
  VERIFICATION (`B = b2`; `B == 0` branch builds the SEALED pair
  predA = ((1,1),(2,1)), predB = ((3,1),)); σ predictions constructed
  from the note's data and scored against PARI factorpadic +
  nfinit/idealprimedec (independent engine); count legs compare
  reader-measured counts vs note formulas with evidence classes
  disclosed per family ([SAME]/[IND]/[NONE]); the SHAPE leg is
  two-sided (unpredicted-key AND absent-key violations). Negative.

## 4. FRESH ROUTE — disjoint from PE1–PE6's disclosed routes; the Haar side computed independently of the note's entire apparatus for the first time in the arc

`/tmp/w12_pe7_fresh.py` (log `/tmp/w12_pe7_fresh.log`): own finite
fields (F₄, F₉, F₂₅ incl. non-prime), exact Fractions, no repo
imports, NO menu, NO reader, NO polygons. **386 checks, 0 violations;
both teeth fired.** Run-1 disclosed: 13 violations, all three
instrument bugs of my own (truncated series compared with `==` instead
of tail-bounded ties; a split/inert-symmetric tooth that cannot bite;
one hand-fitted envelope bound) — fixed, run-2 GREEN; no note text was
implicated.

* **LEG A — the three-readings tie with an INDEPENDENT μ_τ.**
  (A1, odd residue char incl. q = 9, 25): disc-uniformity route —
  c ↦ b²−4c measure-preserving (4 a unit; bijectivity
  machine-verified at finite windows), so μ_τ = square-class measures:
  s_q = 1/2 counted in own field tables; symbolic assembly
  μ_split = μ_inert = q/(2(q+1)), μ_ram = 1/(q+1) == R_τ EXACTLY.
  (A2, q = 2 mixed — the wild row): exact strata: v(b) = 0 dictionary
  enumerated mod 8 (disc ≡ 1 vs 5 mod 8 by parity of c); v(b) ≥ 1
  reduces to uniform disc/4 (translation-invariance, enumerated);
  2-adic square-class fractions assembled exactly:
  μ = (1/3, 1/3, 1/3) == R_τ(2); brute-force interval cross-check
  over (b,c) mod 2⁹ consistent (undetermined mass 1/32); PLUS an
  independent-engine tooth: the (v(disc), unit-class) ↔ σ dictionary
  verified against PARI nfinit/idealprimedec on 180 exact integer
  quadratics at p = 2, 3, 5 (180/180).
  (A3, EQUAL characteristic 2, q = 2 AND q = 4 — the
  charge-suggested F_q[[t]] exercise, via ARTIN–SCHREIER, no disc):
  for v(b) = β, w = c/b² is uniform on t^{−2β}O and type(w) depends
  only on its 2β+1 pole/constant coefficients — enumerated EXACTLY per
  stratum (AS reduction by Frobenius square roots; RAM iff an odd pole
  survives; else split/inert by Tr_{F_q/F_2}); μ_τ assembled with
  exact geometric tails: |μ_τ − R_τ| ≤ 2^{−11} at q = 2 (frac table
  split = 2^{−β−1}: the exact geometric pattern summing to 1/3) and
  ≤ 2^{−12} at q = 4 vs R_τ(4) = (2/5, 2/5, 1/5). Teeth: corrupting
  the mixed-2 dictionary (5 mod 8 → split) and the q = 4 trace kernel
  (size 1) both break the ties — fired.
* **LEG B — the envelope probe (does the proof need the displayed
  rate?).** B1: the same six n = 2 core families with visibility
  thresholds re-declared ν′ = 10ν + 7 (still affine ⟹ (A1) intact,
  same closed-form R_τ tied within explicit truncation tails):
  D′_τ(N) monotone below R_τ at q = 2, 3, 5 for N up to 120, residual
  r′(N) strictly decreasing → 0 — but SLOWER than the true envelope
  by a factor > 10³ at N = 60: W-12.D's conclusion is delivered
  unchanged. The proof consumes only r → 0; the displayed q^{−N} rate
  belongs to W-12.B alone. B2: demoting SEP-INERT to the rest breaks
  (A2) (r″(N)/q^{2N} → (q−1)/(2q) > 0) and the conclusion fails
  EXACTLY at its consumption sites: Σ_τ R″_τ = 1 − (q−1)/(2q) and
  μ_inert − R″_inert = (q−1)/(2q) exactly (symbolic) — the deficit
  equals the undrained mass, landing entirely on the demoted family's
  τ. (A2) is individually load-bearing, quantitatively.

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 1C+3G+2m (2b47711) → r1 (ba0d1a4) + BOX-3
annex (8e535d2) → PE2 0C+3G+2m (1be15d2) → r2 + BOX-2 annex (99f1813)
→ PE3 0C+1G+1m (c9c5c0e) → r3 σ-pin (b17238a) → PE4 1C+2G+2m
(26689da) → r4 (d2d91b7 + 5728258) → PE5 0C+1G+3m (c3e2f8e) → r5
(be4a1dc + ee17210) → PE6 CLEAN 0C+0G+1m (ef258fe; counter 0/2 → 1/2)
→ PE6-m1 dated record (c2afad3) → **PE7 (this pass): CLEAN —
0 CRITICAL + 0 GAP + 1 MINOR (+3 remarks); the 2-clean counter
COMPLETES 1/2 → 2/2. W-12 IS ACCEPTED — the tenth note through the
bar; THE REDUCTION THEOREM (W-12.D) and the whole note are FROZEN
(dated appends only; the MINOR's repair shape is a one-line dated
re-anchor, not a repair round).** Arc facts: seal intact through a
SEVENTH identical green run; the Haar reading of the capstone's
conclusion now verified by two apparatus-independent routes
(disc square classes; Artin–Schreier strata) in four ring types incl.
equal characteristic 2 at q = 2, 4; the (A2) clause's necessity and
the rate-freeness of the proof both exhibited on live bundles. With
HE7, GENH4, GENIND, W-11, HMENU3 and now W-12 through the bar, the
chain's conditionality = the HEX3/GENHN/HE6 arc grades + the displayed
frontier boxes ([GENHN-HE(μ ≥ 3)], [W12-H] at orders ≥ 2, W12-BOX-4/5,
HEX3-BOX-1).

— passPE7 verifier, fresh context, 2026-08-09.
