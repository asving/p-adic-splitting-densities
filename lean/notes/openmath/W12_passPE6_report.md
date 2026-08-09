# W12 passPE6 report — hostile verification pass 6 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r5
(**be4a1dc** + markup fix **ee17210**). Read first: all five prior reports
(PE1 2b47711, PE2 1be15d2, PE3 c9c5c0e, PE4 26689da, PE5 c3e2f8e), the full
r5 diff (both commits), the delivered annex draft `HMENU3_annex_draft_r5.md`
and its application at HMENU3 (**19c0285**, ANNEX A applied), and the
consumer notes at their pins (GENH4.C @ 4b0d946; GENIND Step 5 + S0 + S16 @
HEAD; HE7's chain claim + GENHN's [GENHN-HE] box). This pass fixes nothing;
it quotes and classifies. Charged attack order: (1) THE r5 TEXT (never
before attacked) — all eleven changed passages walked against the files they
cite; (2) the (A1) σ-LABELING clause AS CONSUMED by GENH4's supply, GENIND
Step 5, and the firing table's per-degree rows; (3) W-12.D's proof core —
Step 4 both bounds and the Step 1–3 telescoping, re-derived from scratch;
(4) the (A0)/(A2) clauses; (5) free hunt (S9 stack, S6 boxes, the
blast-radius sweep re-run from its own search terms, in and out of scope).
Fresh instrument `/tmp/w12_pe6_fresh.py` (own field tables GF(4)/GF(8)/
GF(9)/GF(25), own recursive n = 2 reader, no repo imports), log
`/tmp/w12_pe6_fresh.log`.

**VERDICT: CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAP + 1 MINOR
(+ 3 uncounted remarks). The 2-clean counter STARTS: 0/2 → 1/2.**

The r5 repair is faithful at all eleven changed passages (each walked
against the cited files at HEAD — the eleven: header supersede marker; n = 3
firing-row rewording; Step-4 upper-bound bracket; "No other conditionality"
bracket; the three m3 witness-pair brackets incl. §S10's; the [r5] NOTICE at
ANNEX 2 with the m2 blast-radius sweep; the two re-pointed supersede markers
(ee17210's plain-text form renders correctly); the [r4]-ARC supersede mark;
the [r5] ARC). The (A1) clause matches its three consumers with no daylight
found at the quantifier (§2, charge 2). Step 4 (both bounds, post-r5
warrants) and the Step 1–3 telescoping re-derived clean (§2, charge 3).
(A0)/(A2) hold as displayed (§2, charge 4). The one surviving defect is
record-completeness in the [r5] sweep table itself (MINOR 1). Machine leg:
seal intact, SIXTH green run at identical counts, artifacts
content-identical ex-timing, tautology spot-audit negative. Fresh route
(three legs, all disjoint from PE1–PE5's disclosed routes): the Step-3
telescoping verified SYMBOLICALLY in q at every window N ∈ [2, 30] (116
identities incl. the three per-τ deficit identities); the reduction's n = 2
firing quantities machine-exercised at NON-PRIME q for the first time in
the arc (q = 4, 8, 9, 25; 180 checks, 0 violations, both teeth fired
first); two adversarial bundles at (A1)'s boundary behave exactly as the
clause structure predicts.

---

## 1. FINDINGS

### MINOR 1 — the [r5] m2 BLAST-RADIUS SWEEP's table does not disposition every hit of its own declared search terms within its own declared scope

**Quote (the sweep's method line, note L1760–1763):** "Search terms:
'every lift', 'EVERY lift', 'all lifts', 'any lift', excluding
disc ≠ 0-restricted occurrences" — over "the live σ-certification surfaces
of the W-11/W-12/HEX3/HMENU3/GENH4/GENHN stack."

Re-running exactly that grep over exactly those six notes (this pass)
returns hits the table's five rows do not reach:

* **HEX3_PROOF L438**: "The S3.2-species lower bound **(all lifts genuinely
  ambiguous)** shows U₃^σ ≥ q^N is attained by fully-hidden states" — an
  "all lifts" hit, not disc ≠ 0-restricted, on a σ-quantity surface; the
  sweep's HEX3 row dispositions L80–81 only.
* **GENHN_PROOF L153 and L440**: "slot-min EXACTLY, **for every root θ and
  every lift** — W-9's …" — two "every lift" hits; the GENHN row's stated
  rationale covers only the "a 2SIDED configuration for every lift" phrases
  by name.

**Classification: MINOR** (record completeness; no conclusion moves — same
genre as GENIND PE7's "fails its own stated method" minor). I verified each
missed hit harmless: L438's parenthetical is a category slip (the species
MEMBERS are ambiguous — two disc ≠ 0 lifts with distinct σ per LEMMA
W12-S3.2; a single lift has one σ and cannot be "ambiguous"), not a
certification of disc = 0 lifts, and the sentence's substance (U₃^σ ≥ q^N
via the species) is the annexed bracket's own content; GENHN L153/L440 are
valuation/slot-min facts true of every lift (the same genre the sweep's
W-11 row correctly excuses as "valuation facts, not σ-certifications").
*Repair shape: one line per missed hit, or a "hits not individually
dispositioned are of the W-11-row valuation genre, checked" close.*

### Remarks (uncounted, no repair owed)

* **R-1 (the n ≥ 6 firing row is stale at HEAD, strengthening direction —
  PE5's R-1 one round later).** The row's "NOT supplied — and openly so:
  the clause at μ ≥ 3 leaves IS the named open box [GENHN-HE(μ ≥ 3)]" is
  conservative at HEAD: HE7 (frozen through its annex passes) claims that
  box discharged at composition grade ("[GENHN-HE(μ)] holds at every leaf …
  This is a composition claim at attempt grade 0/2, not an acceptance
  claim", HE7_PROOF L288–305). W-12's row under-claims rather than
  over-claims; honesty preserved.
* **R-2 (PE5's R-2/R-3/R-4 stand, verified still-true at r5).** In
  particular R-4: the (A1) clause still quantifies over classes (F, x) at
  non-visible x, where (A1) defines no class — vacuous, one word
  ("visible") from exact; Step 4 needs visible classes only (re-checked in
  this pass's Step-4 re-derivation).
* **R-3 (S9's supplier-arc parentheticals are date-scoped inline and stale
  as histories).** E.g. "r2 = HEAD 31506b3 **at composition time**; counter
  0/2" for W-11, which is ACCEPTED 2/2 at repo HEAD (fold 35e6545). The
  inline "at composition time" scope keeps these honest under the era-tag
  convention PE3 audited; noting because the strengthenings (W-11 accepted;
  HMENU3 accepted + ANNEX A applied at 19c0285) are now recorded only
  outside this note.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) The r5 text (never attacked before), passage by passage.**

* *Header supersede marker + the two re-pointed markers + [r4]-ARC mark +
  [r5] ARC:* at HEAD there is exactly ONE current arc display ([r5] ARC,
  L1836) and four marked-superseded displays (header L5–11; §S10 [r1]
  L1644; [r3] L1774; [r4] L1793) — inventory walked. ee17210's plain-text
  re-point ("the ~~[r4]~~ [r5, re-pointed at r5] ARC") renders without the
  nested-bold defect. The [r5] ARC's transcriptions checked against the
  PE5 report at c3e2f8e: verdict line (0C+1G+3m), the four findings, the
  arc-facts summary — faithful; "report @ c3e2f8e" is the correct commit.
* *The n = 3 firing row (the PE5-F1 repair):* the HM3.C quote is
  byte-faithful at HMENU3_PROOF L216–219 (re-diffed this pass); the row now
  vouches only for the disc ≠ 0 form; the warrant chain (HM3.C decidedness
  content → S2.3 POST-r4's surviving restricted sentence at the terminal
  frame → W12-L1(c) for the DBL transports, window coherence from HM3.C's
  own §S5.2) delivers exactly BOX-7's pinned form, which is (A1)'s clause
  — re-derived here, and the equal-characteristic-3 counter-instance
  re-verified (F = y³ + b₀, F′ = 3y² ≡ 0, disc = 0, member of TRP-RAM3(1)
  with b₁ = b₂ = 0 in-window, visible at every N ≥ 2). The row's scoped
  record sentence ("nothing in (A1)'s clause, in Step 4, or in COROLLARY
  HM3.D quantifies over disc = 0 lifts") checked at all three named
  surfaces — true.
* *The [r5] NOTICE at ANNEX 2:* ANNEX 2's verbatim text untouched (diff
  walked); the notice's HMENU3 quotes verified (L216–219; the §S5.2
  "(not only disc ≠ 0 ones)" parenthetical at L433–434); the drafted annex
  `HMENU3_annex_draft_r5.md` corrects exactly those two sites and has been
  APPLIED at HMENU3 as a dated append (19c0285) — the cross-note
  obligation from PE5's FINDING 1 is discharged repo-side. The HEX3 row's
  claim checked: HEX3 L80–81 carries "Ore applies to every lift — W-12
  S2.3" warranting U₃^σ ≤ U₃^conv, and the conclusion is indeed unaffected
  (conservative-DECIDED ⟹ separable in-window residuals ⟹ post-r4 S2.3
  gives one σ across disc ≠ 0 lifts ⟹ σ-decided in the pinned sense — the
  inequality needs nothing about disc = 0 lifts). The W-11 row's honest
  note verified by construction: RAM(h) in equal characteristic 2 admits
  A₁ = 0 (constraint v(A₁) ≥ (h+1)/2 is an inequality), and then
  disc = A₁² = 0 with F = x² + A₀ inseparable — a disc = 0 lift inside a
  DECIDED family, excluded exactly by the clause's quantifier. GENH4.C/
  GENHN.C rows: statements re-read at pins, both carry "EVERY lift with
  disc ≠ 0" (GENH4 @ 4b0d946 L171–181 re-shown this pass; GENHN L188–200).
  Sweep completeness: MINOR 1. Outside the sweep's declared scope I also
  ran the grep over the consumers (GENIND, HE7): the only non-restricted
  hits are GENIND L790/L807, runner-diagnostic sentences ("reproduces its
  own zero-filled deep digits on every lift"), not σ-certifications — the
  six-note scope choice hid nothing live.
* *The Step-4 m1 brackets:* both route the bounds through (A1)'s clause
  with (A0) explicitly demoted to redundant-but-retained — matching my
  independent re-derivation (charge 3); the F2 record's STEP-4 RE-CHECK
  and the new brackets now say the same thing at all three sites.
* *The m3 witness-pair brackets (S7 W12-ORACLE, S7 P-7, §S10 P-7):* the
  70/15 split re-derived from the runner loop this pass (`B = b2` with
  `b2 = p·tdig`, so b₂ = 0 iff tdig = 0 — q pairs per row over the five
  oracle rows (2,3),(2,4),(3,2),(3,3),(5,2): 2+2+3+3+5 = 15 of
  8+16+9+27+25 = 85); the `else` branch builds the SEALED pair with
  `predA = ((1,1),(2,1))`, `predB = ((3,1),)` (runner L1043–1065, re-read);
  the brackets' scoping ("true of the witnesses as built on those
  mixed-characteristic ℤ_p rows, silent on the repaired B = π^N pair") is
  exactly right — in mixed characteristic both sealed lifts have disc ≠ 0
  (−4p^{2K+1}, −27p^{2L} ≠ 0). §S10's GREEN-summary line is covered by the
  §S10 P-7 bracket as claimed.

**(2) The (A1) σ-LABELING clause as consumed — no daylight found.**

* *The clause itself* (S1, (A1) [r4] bracket): "EVERY member of every class
  (F, x) is σ-DECIDED in the S1 Conventions' pinned lift-certification
  sense, with forced σ = σ_F". Pinned sense = W12-BOX-7 clause 1 ("Decided
  = certified on window digits for all disc ≠ 0 lifts"), TOTAL by the [r4]
  R-1 record (every window class has a disc ≠ 0 lift — re-checked: the
  generic disc polynomial is nonzero and O is infinite). So the clause =
  "all disc ≠ 0 lifts of every member of every (visible) core class have
  type σ_F" — exactly what Step 4 consumes at both bounds (charge 3).
* *GENH4's supply (n = 4 row vs the FROZEN text @ 4b0d946):* THEOREM
  GENH4.C reads "At every decided stage leaf of either genre (any history,
  any window), EVERY lift with disc ≠ 0 has the σ claimed by the leaf
  dictionary" + the two dictionaries — the firing row's transcription is
  verbatim-faithful including both dictionaries (E: RAM ↦ {(4,1)},
  2SIDED/SPLITEQ/SPLTAIL ↦ {(2,1),(2,1)}, INERT ↦ {(2,2)}; F: {(2,2)} /
  {(1,2),(1,2)} / {(1,4)}). Quantifier identical to the clause's; the
  dictionary IS the σ_F assignment. No daylight.
* *GENIND Step 5 (the 1/2 text, @ HEAD):* Step 5 fires W-12.D by assuming
  "P(n)'s (A0)+(A1)+(A2) are W-12.D's hypotheses at degree n" — and
  GENIND's S0 defines the package BY REFERENCE ("Its per-degree hypothesis
  package {(A0), (A1), (A2)} is what (hMenu-n)+(hExhaust-n) abbreviate
  throughout"), with the supplier re-pinned at r5 (GENIND S16 row 1:
  "W-12.D re-read at r5 and re-matched to Step 5 verbatim"). Consumption
  by reference at the current pin leaves no restatement to drift; the r4
  strengthening is inside what P(n) assumes. Consistent with GENIND PE7's
  CLEAN walk of the same seam from the other side.
* *HE7 via the chain:* HE7's consumption is the composition claim (HE7
  L300–305): "[GENHN-HE(μ)] holds at every leaf … through HE6.B + GENIND.B
  + W-12.D the uniformity theorem's conditional stack reduces to arc
  grades + the named hardening boxes." The object it claims to discharge,
  [GENHN-HE(μ ≥ 3)] (GENHN L664–673), is DEFINED with the clause's own
  quantifier ("the σ-decision — every disc ≠ 0 lift factors as the stage
  dictionary … — is OPEN"), which is exactly what W-12's n ≥ 6 row names
  as the un-supplied clause. Definition and consumption use the same
  quantifier; the only tension is R-1's (conservative) staleness.

**(3) W-12.D's proof core, re-derived from scratch.**

* *Step 1 (rationality):* re-derived — Σ_{x∈P} q^{−ℓ(x)} over a shifted
  product with ℓ = m₀ + Σm_ix_i, m_i > 0 gives
  q^{−ℓ(base)}·Π_i(1−q^{−m_ib_i})^{−1}; m_ib_i ∈ ℤ_{>0} by evaluating ℓ at
  x and x + b_ie_i (the r2 repair's route — the display needs only these
  and ℓ(base) ∈ ℤ, both integer); b_i = 0 point coordinates absorbed
  before the display (r1 guard); intersections of shifted progressions are
  empty or single progressions with modulus lcm (CRT), so
  inclusion–exclusion stays inside the display's reach. Fresh-route LEG C
  re-verified the r2 boundary instance (ℓ = (x+1)/2 on 1 + 2ℤ_{≥0}: sum =
  q^{−1}/(1−q^{−1}) ∈ ℚ(q) with m₁b₁ = 1).
* *Step 2:* visible sets increase to P_F (ν_F real-valued suffices), so
  D_τ(N)/q^{nN} is a monotone partial-sum net of Step 1's positive
  convergent series → R_τ. Machine-checked monotone at every fresh-route
  row.
* *Step 3 (the telescoping):* Σ_τ D_τ(N) + r(N) = q^{nN} needs exactly
  (A1)-disjointness + one label per family + (A2)'s definition of r;
  finitely many τ passes the limit. Verified SYMBOLICALLY in q at n = 2
  for every N ∈ [2, 30] (fresh route LEG A), including the sharper per-τ
  form: R_τ − D_τ(N)/q^{2N} equals the closed-form invisible-core tail
  per τ (three identities per N — the deficit identities, which imply
  Σ_τ deficits = r(N)/q^{2N} exactly, i.e. invisible-core mass ==
  tail + undecided mass at every window: the telescoping's exact
  engine-room identity).
* *Step 4 (the PE4-CRITICAL site, post-r4/r5):* re-derived both bounds.
  Lower: visible τ-classes are disjoint cylinder unions; by the clause all
  their disc ≠ 0 lifts have type τ; disc = 0 is null; so
  μ_τ ≥ D_τ(N)/q^{nN}. Upper: a disc ≠ 0 type-τ F truncates into a unique
  visible class or the rest; in the first case the clause applied to F
  (a disc ≠ 0 lift of its own truncation) forces σ_F = τ; so
  μ_τ ≤ (D_τ(N)+r(N))/q^{nN}. Both bounds → R_τ by Steps 2 + (A2). The r5
  m1 brackets say precisely this; (A0) carries no residual proof weight at
  either bound. Wellposedness of μ_τ (Krasner-open τ-partition of the
  étale locus, disc = 0 null, classes = cylinder unions of mass q^{−nN})
  is classical as displayed.
* *The necessity instance* (PE4's degenerate one-family bundle) —
  spot-re-verified: (A1)-sans-clause + (A2) + tautologous (A0) hold,
  Σ_τ R_τ = 1 still holds, and the failing conclusion clause is exactly
  the μ_τ tie. Fresh-route LEG C adds a SECOND boundary bundle (RAM
  relabeled split — see §4) with the same signature.

**(4) The (A0)/(A2) clauses.** (A0) post-r4 gloss ("the read's type" =
σ_F): implied by the clause + BOX-7 totality, so redundant-but-retained —
consistent at its three surviving display sites (S1 statement, S3.4 close,
FIRING CHECK), each now carrying the demotion bracket. (A2): r(N) ≥ 0 is
automatic from (A1) exactness + disjointness (r counts the complement);
the n = 2 instance's routing of SPLIT-TAIL through (A2) re-checked (its
count (q−1)q^{N−1} per center per w admits no N-free dens — dens would be
(q−1)q^{−N−1}); the display note ("drainage of the REST, not of the
σ-undecided residue alone") is load-bearing and correct — LEG B measured
the complement's two legs separately and their sum equals
q^N + q⌊(N−1)/2⌋(q−1)q^{N−2} on every row.

**(5) Free hunt.** S9 stack walked (R-3 remark); S6 boxes re-read — BOX-7's
clause 1 is the quantifier every r5 passage cites, and the box inventory is
unchanged from PE5's complete walk; the [r5] CITE VERIFICATION's own claims
spot-checked (runner lines, HMENU3 lines, 15-of-85 arithmetic — all
reproduced here independently); no new dangling reference introduced by r5
(grep for "[r5]" — 14 sites, each attached to a PE5 finding or the NOTICE/
ARC).

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  **7dc040d94fbbb1e8d20ac817b665d418** == `git show
  f669cb0:verification/openmath/w12_checks.py | md5sum` — byte-identical at
  HEAD; committed artifacts carry §S10's md5s (05776c9e… / 0557b15f…).
* **Fresh isolated re-run (single run, this pass, detached with pidfile):**
  exit 0, **3,232,506 checks / 0 violations**, teeth **W12-T-SHAPE 23 /
  T-DRAIN 23 / T-CENSUS4 8 / T-SIGMA 1273**, 323.8 s, verdict GREEN — the
  SIXTH green run of the arc, at counts identical to §S10.
* **Artifacts:** fresh JSON content-identical to committed after stripping
  timing keys (programmatic compare == True); output diff vs committed = 1
  line (elapsed 323.8s vs 323.0s). Committed bytes RESTORED, md5s
  re-verified (05776c9e… / 0557b15f…).
* **Tautology audit (spot):** σ-witness predictions come from the note's
  constructions (runner L1043–1065), scored against PARI `factorpadic`
  (L951) — an independent engine; DBL/SHAPE legs compare reader-measured
  counts against note formulas, not formula-vs-formula. Witness-builder
  code byte-consistent with the [r5] CITE VERIFICATION's description.

## 4. FRESH ROUTE — three legs, disjoint from PE1–PE5's disclosed routes (mixed-char ℤ_p; prime-power readers q = 4, 8, 9; exotic mixed-char rings; equal-char p ≥ 5 + n = 2/L0 symbolic limits)

`/tmp/w12_pe6_fresh.py` (log `/tmp/w12_pe6_fresh.log`): own GF(p^m) tables
(q = 4, 8, 9, 25 with named irreducibles), own truncated-series arithmetic,
own RECURSIVE n = 2 conservative reader (level-0 factorization, recentered
branch polygons, refinement at repeated residual roots incl. the char-2
Frobenius square root, tail/undecided exits) — no repo imports.

**LEG A — the Step-3 telescoping at parametric depth (symbolic in q).**
For every window N ∈ [2, 30], as rational-function identities in q (sympy):
the finite-N partition identity Σ_families visible-mass + r(N) = q^{2N}
(with the n = 2 menu's visible ranges h ≤ N−1 odd; w₁+w₂ ≤ N−1;
k ≤ ⌊(N−1)/2⌋), AND the three per-τ deficit identities
R_τ − D_τ(N)/q^{2N} == closed-form invisible-core tails (derived here
independently: d_ram = (q−1)q^{−h₀−1}/(1−q^{−2}) with h₀ the first
invisible odd; d_inert = (q(q−1)/2)q^{−2M−4}/(1−q^{−2}); d_split = the
SPLITEQ tail + the two-regime 2SIDED tail (q−1)²q^{−2}(1−1/q)^{−1}·
(Mq^{−N} + q^{−2M−3}/(1−q^{−2}))). **116 identities, 0 failures.** These
verify, exactly and at every checked depth, that the invisible-core mass
equals the tail+undecided mass — the identity that makes Steps 2+3 close.

**LEG B — the reduction's n = 2 firing quantities at NON-PRIME q (first
in the arc).** Full-space enumeration (up to 531,441 members/row) on ten
rows — (4,2), (4,3), (4,4), (8,2), (8,3), (9,2), (9,3), **(25,2)** (the
first q = 25 row anywhere in the arc), plus prime cross-checks (3,3),
(5,3). Checked per row, in exact rationals: all eight family aggregate
laws (measured == law, both directions — every measured key predicted,
every predicted key realized); the partition total q^{2N}; the complement
law r(N) = q^N + q⌊(N−1)/2⌋(q−1)q^{N−2} with SPLIT-TAIL and UNDECIDED
measured separately; the per-τ decided masses D_τ; and the exact deficit
identity of LEG A on measured data. **Teeth first, both fired:** T1
(corrupt the RAM law exponent) → mismatch caught at every visible RAM key;
T2 (mislabel SPLITEQ's σ as inert) → both the split and inert deficit
identities break at exact rational values. Clean run: **180 checks, 0
violations.** D_τ monotone in N at fixed q on every (q, N)-chain tested.

**LEG C — adversarial bundles at (A1)'s boundary (5 checks, 0 failures).**
(i) Duplicated-family bundle (the true n = 2 menu + a second copy of
SEP-SPLIT): every family individually keeps exact counts and a correct
label, ONLY pairwise-disjointness fails — and Σ_τ R_τ = 1 + (q−1)/(2q) ≠ 1
symbolically: disjointness is individually load-bearing for the Σ-clause.
(ii) The Step-1 integrality boundary (PE2's ℓ = (x+1)/2 on 1 + 2ℤ_{≥0}):
the repaired display yields q^{−1}/(1−q^{−1}) ∈ ℚ(q) via m₁b₁ = 1 exactly
(symbolic + exact-rational partial sums at q = 4). (iii) Relabeled bundle
(σ_RAM := split; counts, disjointness, (A2), and sealed-(A0) all intact):
Σ_τ R'_τ = 1 STILL HOLDS while R'_split − μ_split = 1/(q+1) ≠ 0
symbolically — a second instance, structurally different from PE4's
degenerate one-family bundle, in which every (A1) clause EXCEPT the
σ-LABELING clause holds and exactly the μ_τ tie fails, with the clause
excluding it precisely (RAM members are σ-DECIDED with forced σ = ram ≠
split). The clause's boundary behaves exactly as the [r4] necessity record
claims, from a new direction.

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 1C+3G+2m (2b47711) → r1 (ba0d1a4) + BOX-3 annex
(8e535d2) → PE2 0C+3G+2m (1be15d2) → r2 + BOX-2 annex (99f1813) → PE3
0C+1G+1m (c9c5c0e) → r3 σ-pin (b17238a) → PE4 1C+2G+2m (26689da) → r4
(d2d91b7 + 5728258) → PE5 0C+1G+3m (c3e2f8e) → r5 (be4a1dc + ee17210) →
**PE6 (this pass): CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR (+3 remarks);
the 2-clean counter STARTS: 0/2 → 1/2.** The r5 repair held everywhere it
was attacked: the n = 3 firing row now vouches only for what its supplier
delivers at the pinned quantifier (and the HMENU3-side correction is
drafted AND applied at 19c0285); both Step-4 bounds and the
conditionality close now cite the load-bearing clause; the arc record is
single-voiced; the witness-credit surfaces are scoped to the runner's
actual construction. What survives is one record-completeness MINOR inside
the new sweep table itself. Arc facts: seal intact through a SIXTH
identical green run; the telescoping now holds symbolically at every
window N ≤ 30; the reduction's firing quantities now machine-verified at
non-prime q (incl. q = 25) with the deficit identities exact; and (A1)'s
σ-LABELING clause passed a second, structurally new necessity probe at
its boundary. PE7 next; a second CLEAN accepts the note at 2/2.

— passPE6 verifier, fresh context, 2026-08-09.
