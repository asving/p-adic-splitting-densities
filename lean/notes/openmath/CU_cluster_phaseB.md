# The CU re-label cluster (CU-2, CU-2t, CU-3, CU-4, CU-5, CU-6, CU-7) — consolidated Phase-B unit (Fable "CUC", 2026-07-31; **R2** 2026-07-31, unit CU2t)

*(R2 applies the `CUC_pass1_verify.md` corrections in place: the F1 CRITICAL
(Θ^τ blind to ν) + its F2 root (undefined consistency predicate) repaired in
§§9.2a/9.3; §1 rescoped per F3; the §9.4/§9.5 pricing honesty-corrected per
F4 with ledger/ROOT touches enumerated. Full disposition table for all
eleven findings: §10. Surviving cores — Lemma CU-2t clauses (i), (ii)-main,
(iv), the §6.1 audit — are byte-stable.)*

**Unit type: RE-LABEL CONSOLIDATION.** Per the O3adj adjudication (§3.1) and the
tree's DELTA-2 §D2.3, the K-RUN-C composition has exactly ONE new proof (CU-1,
its own unit — `CU1_phaseB_verifybrief_rev2.md`, V29 pending; NOT part of this
document) and seven units that are re-labels of content already proved or
exactly declared in home packages with their own hostile-verification records.
This document gives, for each of the seven: the precise statement per the
§D2.3 skeleton; the proof BY CITATION to its proved home; the exact
conditionality (CONDITIONAL-ON-PASS with the pending verdict NAMED wherever the
home is mid-verification); and an honest flag wherever the re-label carries a
genuinely unexecuted obligation. It also EXECUTES the two §D2.3 actions owed to
this cluster: the CU-7 attribution correction (§7) and the §D2.7 OB2/D-11
audit (§6). No Lean file is touched; no home brief is edited (home-file
pointer updates are listed in §8 for their owners, per the CU-1 rev-2
discipline).

Sources (all read this session): `docs/MATH_COMPLETION_TREE_2026-08-01.md`
(DELTA 2 §§D2.1–D2.7; node texts O-1/O-2/O-3/O-5, D-11/D-13/D-14/D-15/D-16,
D-10/D-12) · `lean/notes/openmath/O3adj_adjudication.md` (§§1–4) ·
`lean/notes/SYNTHESIS_PASS4_2026-08-01.md` (§§1–2) ·
`O2a_phaseB_verifybrief_rev5.md` (§§2, 4, 5) · `CU1_phaseB_attempt_rev2.md` +
`CU1_phaseB_verifybrief_rev2.md` (the split, via the attempt record) ·
`O1thr_phaseB_verifybrief_rev3.md` (§§0, 1.4, 4, 5, 6) +
`O1thr_phaseB_attempt_rev4.md` (rev-4 state via ledger) ·
`O5triple_phaseB_verifybrief_rev3.md` (§§5–9) · `O14ap_phaseB_attempt_rev3.md`
(§§0–1) · `O12_phaseB_verifybrief_rev4.md` (§1 scope + OL-O12-2 sites) ·
`Dfloor_phaseB_verifybrief_rev2.md` (§§0, 8) · `O3design_phaseB_attempt.md`
(§2.1 (O2)/(O7)/OB2, §2.2 K-OB-A/B, §R2 consumer table, §R3 F4 split/F3′) ·
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (2026-08-01 sections through
WAVE 7 COMPLETE).

**Standing preconditions (tree §2.4, carried verbatim by §D2.3):** f monic
separable ns-free of degree n over O; trees range over ns-free carriers;
pinned representative family F_rep. All statements below are PER-f
(selected-f); box-level lift quantification appears ONLY where D-15 owns it
(D2.1 line 3). N\*(𝐇) = the D4R.4/L12 per-branch level with the TB-CAP
verdict-window join; CEIL-UB retained one-directional.

## 0. The pending-verdict registry (the CONDITIONAL-ON-PASS key)

Every "CONDITIONAL-ON-PASS: P(·)" below points at exactly one row here.

| home | rev of record | verification state (ledger-cited) | the pending verdict |
|---|---|---|---|
| O-2a | rev 5 (commit b337195; brief `O2a_phaseB_verifybrief_rev5.md`) | core THRICE confirmed (V10 → pass-2 → V25 arc); V25 on rev 4: SOUND-WITH-GAPS, 0 criticals, 1 minimality gap → the OL-3-min trim EXECUTED at rev 5 | **P(O-2a r5)** = the owed fresh hostile pass on rev 5 (D2.5 "passes owed") |
| O-1thr (Thm 1 = D-14; Thm 2 = O-1(thr); Thm 3 = D-15) | rev 4 (commit 5613274) | V24 on rev 3: UNSOUND — 1 critical (REAL≡ non-halt circularity) + gaps, adjudicated PACKAGING ("pin STANDS", ledger); sheared core + Thm 1 + (M6c) perimeter SURVIVED; rev-4 repairs landed ((M6c) requantified, non-ns-halt a conclusion) | **P(O-1thr r4)** = the owed fresh pass on rev 4 |
| O5triple | rev 3 (commit 6fe1b2d) | V18 → rev 2; V23: NO criticals, 3–4 gaps → rev-3 repairs, 0-critical | **P(O5t r3)** = the owed fresh pass on rev 3; PLUS the five §2 flags (GMN-COH)/(R-0)/(R-1)/(R-2)/(R-3), OPEN (= GD-1/GD-7/GD-8 duties; NOT covered by the executed LITUNIT, which pinned T-1/T-2/ML-scope/(V1)/(V2)/FGMN) |
| CU-1 | rev 2 (commits 784728a/3108e26 wave) | V27 on rev 1: UNSOUND, core repairable → rev-2 structural repairs (N-free induction; ADEQ interior/terminal split; construction-before-recovery; pins declared) | **P(CU-1 r2)** = V29, RUNNING |
| GD23 (GD-2/GD-3 head) | r2 (same wave) | V26 on r1: UNSOUND, order-≤1 core NO critical → r2 against the LITUNIT-pinned printed statements | **P(GD23 r2)** = V28, RUNNING |

**VERIFIED homes (no pass condition):** Dfloor D-1/D-2/D-4 (leaf #3: V22 clean
+ Fable pass 2, adjudicated at ledger commit dbccbc1) · O-12 (leaf #2, honest
scope) · O-13/D-12 skeleton finiteness (leaf #1; `skeleton_finite` in Lean) ·
the O-14a′ core (Theorems 1–3 TWICE-STABLE across V11/V15; the consumed
instance `RRE(p, ZMod p)` FORMALIZED as `runRealizerExists_zmod`,
`MovesD/R7_runRealizer.lean`, Lean-core). **Perimeter constant:** TB-CAP (T-6)
is dual-accepted PERIMETER-CONDITIONAL on D-12r (the D4R.0-K(c) verdict pin) —
inherited, displayed wherever consumed, unchanged by this cluster.

Open-lemma vocabulary: O-2a's OL-1..OL-6 are the GD families' carrier
instances — OL-1 = GD-1, OL-2/OL-2-min ⊂ GD-2, OL-3/OL-3-min ⊂ GD-3,
OL-4 = GD-4's run-side half, OL-5 = GD-5 (nearly closed by composition),
OL-6 = GD-6(a). "The GD residue" below always means these, by the D2.2 merge.

---

## 1. CU-2 (NP — no-phantom)

**Statement (CU-2 — rescoped at R2 per the §9.1 carrier note; CUC F3).** Let
f satisfy the standing perimeter. For every history emitted by a complete run
of the engine's stage flow on f, the CONTINUING PART 𝐇° is a well-formed
element of the carrier 𝔈 satisfying Cons_f — the run's at-most-one terminal
record (OL-4), when present, is the run-side half of the seam PAIR (𝐇°, ν)
of §9.1, NOT a node of the 𝔈 element (at a saturated prefix appending it
would violate W3's interior clause — the §9.1 finding; its own forcing is
CU-2t, §9) — hence, through the GMN interpretation ι and O-2a Theorem
2(A)–(C): each emitted CONTINUING record (with its dressing) is the GMN
datum of the stage read over its emitted prefix's chain Θ(𝐇°_{≤i}) ((c1)
side data verbatim, (c2) residual multiplicity), the chain places
t^{(i)} ∈ t_i(f) at every level with injective placement, the invariant
matching and saturation clauses of 2(B) hold, and the index charge of 2(C)
bounds dCert(𝐇°) ≤ ind(f). In words: every emitted continuing record is the
GMN datum of its chain — the run emits NO phantom (terminal seam: CU-2t).

**Proof by citation.** This IS O-2a rev 5 **Theorem 2(D)** (brief §5) composed
with 2(A)–(C); the run-length induction is written inside §5's (D)-proof (base
= OL-6(a) + OL-5; step = OL-6(b) + OL-2-min + OL-3-min + OL-1; discipline =
OL-4). Nothing is re-derived here — per O3adj §2 ("no-phantom is not a new
induction at all… its run-length induction is already written inside O-2a
rev 4 §5", carried to rev 5 intact).

**Displayed residue (consumed, not discharged):** exactly OL-1 + OL-2-min +
OL-3-min + OL-4 + OL-5 + OL-6 = the GD-1..GD-6 instances (§0 mapping); OL-6's
standing falsifier is G-EMIT (O-2a rev 4 §4 record). GD-2/GD-3's prover head
is GD23 (P(GD23 r2)).

**Grade: RE-LABEL, complete — nothing new to prove in this unit.**
CONDITIONAL-ON-PASS: **P(O-2a r5)**. Conditional-on-open-lemmas: the GD
residue as displayed (that conditionality is Theorem 2(D)'s own, stated in its
hypothesis list; CU-2 adds none).

**Consumption note (deviation already on record):** the O3adj §3.1 CU-1 line
"Step = IH + OL-6 + …" is superseded by CU-1 rev 2, which DROPPED OL-6 in
favor of the state-level pins (P-ROOT)/(P-KEY)/(FR≡) (CU-1 attempt rev 2 §2,
orchestrator note). Consequence for this cluster: **OL-6's only consumer is
CU-2** (through Theorem 2(D)) — the arrow map in §8 reflects this.

---

## 2. CU-2t (the terminal seam)

**The split this unit lives in (per CU-1 rev 2 — the adjudicated V27 repair).**
GMN children of a continuing node divide as: INTERIOR children (μ ≥ 2) —
CU-1's scope; COMPLETE children (μ = 1, leaves by O-2a Theorem 2(B)'s
biconditional) — routed to O5triple Theorem B / Theorem D(b), counting-forced,
NO no-missing consumed. Terminal machine records (sel = ⊥) are **not GMN
children at all** (Cons_f constrains no terminal field — Lemma R's displayed
non-claim, O-2a §2); their verdict-carrying reading is THIS seam. The split's
no-gap/no-overlap display is CU-1 brief rev 2 §4.

**Statement (CU-2t — one lemma; the old Cons^τ (t-i)/(t-ii) obligations).**
Let 𝐇 = (𝐇°; ν) be emitted by a complete run on f with verdict-carrying
terminal last node ν, and let c = Θ(𝐇°) be the continuing prefix's chain
(Cons_f(𝐇°) by CU-2). Then the terminal record is FORCED by (f, prefix):
(τ-irr case) the last read has μ_{k'} = 1 and the verdict pair equals
(accE_{k'}, accF_{k'}) — the O-2a Theorem 2(B) saturation data — read inside
the TB-CAP (τ-irr) window; (τ-hen case) ν sits on the slope-−∞/Hensel side
with verdict pair (1, f₀) and the (D3)-window read, inside the TB-CAP (τ-hen)
window N_V = 1. Equivalently: the codomain extension (t-ii) (a final entry
(λ_{k'+1}, ⊥) on Θ) is consistent, and (t-i) the terminal fields tie to the
level-(k'+1) GMN read of f, same shape as (c1) — so no free choice of terminal
record exists at a verdict-carrying leaf. [R2 note: "no free choice" is
quantified over RC-consistent records — Definition RC, §9.2a — and every
run-emitted record is RC-consistent via the (T-DEC)/(T-VERD) rows of §9.4.]

**Proof route by citation (declared, NOT executed anywhere yet).** O-2a
Theorem 2(B) saturation (+ Cor 1.20/3.8 for irreducibility and (e, f)) + the
TB-CAP (τ-hen)/(τ-irr) windows — the route recorded at O3design §2.1 (O2)
(the (t-i) lemma "from O-2a (B) + Cor 1.20/3.8", formerly JC-0's clause) and
re-homed by §D2.3 with NO global T_can definition riding on it (the Cons^τ-set
definition died with the O3design replacement; verdict records still need
their forced-terminal reading, which is all this lemma asserts).

**Grade: OPEN (one lemma) — the honest flag.** CU-2t is the ONE unit in this
cluster whose content is a genuinely unexecuted proof obligation, exactly as
§D2.3 prices it ("Status: OPEN (one lemma) over the GD residue"). It is
corollary-grade over cited material (2(B) is proved conditional in O-2a §5;
the windows are T-6's), NOT new mathematics in the reporting sense — but it
must be WRITTEN, and no home package has written it. Recommended owner: the
CU-1 orbit (its brief already names "verdict-carrying terminal seams =
CU-2t's business" twice). Conditions when written: **P(O-2a r5)** + TB-CAP's
D-12r perimeter + the GD residue via 2(B)'s hypothesis (Cons_f + OL-1).

---

## 3. CU-3 (NE — nonempty locus, coherent form)

**Statement (CU-3 = F3′, verbatim the O3design rev-1 form the tree now keys).**
Every COHERENT chain (`HistoryCoherent`, the O-14a′ predicate — the realizer
theorem's actual compiled scope) with N\*(𝐇) ≤ N, bookkept under the (O6)
canonicalizations, has a monic separable witness g in its level-N digit
cylinder with the corresponding history in T_can(g).

**Proof by citation (three factors, per §D2.3).**
* **(a) The realizer.** O-14a′ rev 3 Theorems 1–3 (twice-stable): the
  last-node flank CLOSED from bare coherence (threshold derived at the run
  anchor, transported along the recentering run — Lemmas 3.1/3.2), and
  `RRE(p, ZMod p)` — THE consumed instance — proved for every prime under the
  RG-2-fenced coherence predicate ((CR2) free at F = 𝔽_p: every frame key
  linear). FORMALIZED: `runRealizerExists_zmod`, Lean-core. Scope note: the
  general-F singleton clause (CR2) is REFUTED (F₉ inert-quadratic
  countermodel, twice-stable); the mandatory path consumes ONLY the ZMod p
  instance (O-14a′ rev 3 §1's consumption audit: TreeCan (†15),
  `canPolicyC_pin`, every mandatory consumer at prime ambient field), so the
  refutation costs CU-3 nothing — displayed, not hidden.
* **(b) Cylinder pinning = D-14.** O-1thr Theorem 1 (lawful-site locality):
  whether the machine reads any lawful site (H, ν) on f is determined by f's
  digits below L(H, ν) — quantified over ALL lawful sites, realization NOT
  presupposed (the noncircularity remark, O-1thr §4 Remark 1). Applied over
  the witness's chain with N\*(𝐇) ≥ L bookkeeping (CEIL-UB direction), the
  realizer's witness pins the whole level-N digit cylinder: every g in the
  cylinder realizes the same history. This is exactly the "D-14 cylinder
  pinning" factor of §D2.3.
* **(c) Bookkeeping.** The (O6) canonicalizations (branch-letter keying +
  deep-marker pooling; O3design §1 (O6)) for census-side counting only —
  definitional, no proof content.

**Governance, executed:** the O-3 clause-3 re-key ("every fresh-frame-lawful
assignment chain" → "every coherent chain") was EXECUTED at DELTA-2 §D2.1
line 1; **LC-COH** (lawful ⇒ coherent) stands as a named open note CONSUMED BY
NOTHING — CU-3 neither needs nor claims it.

**Grade: RE-LABEL, complete.** The realizer core is VERIFIED (twice-stable) +
Lean-checked, unconditional. CONDITIONAL-ON-PASS: **P(O-1thr r4)** for the
D-14 factor. Perimeter: the RG-2 fence (forward obligation on record: a
fence-lift re-adjudicates (CR2) → (S6b′-SUPP) FIRST — parked sign-off class).

---

## 4. CU-4 (ACC — acceptance, selected-f)

**Statements (verbatim the rev-1 split, V21-confirmed level quantifiers;
stated for the box's own f only — x_f := f mod p^N).**
* **(F4-S — soundness, every N):** Cert accepts (x_f, 𝐇) ⇒ 𝐇 ∈ Run_N(x_f)
  AND 𝐇 is verdict-carrying in T_can(f).
* **(F4-C — completeness at the decision level):** if 𝐇 ∈ T_can(f) is
  verdict-carrying and N ≥ N\*(𝐇), then Cert accepts (x_f, 𝐇).
Displayed corollary: for N ≥ N\*(𝐇) the two give the biconditional; the all-N
biconditional and every lift quantifier remain WITHDRAWN (V16-5/12).

**The charged supply check — what O-1thr rev 3/4 and Dfloor actually provide.**
* **O-1thr Theorem 3 supplies the fiber-side reading.** NAME COLLISION,
  displayed: O-1thr §1.4's (F1)–(F6) are FIBER clauses (of fiber(T, x)), not
  the O3design faces F1′/F4. §D2.3's "from O-1thr Theorem 3 (F1)/(F4)" means:
  **(F1)** T's chains are ALL AND ONLY the realized pruned runs on f_x, and
  **(F4)** interior chains do not halt — both transported cylinder-exactly by
  Theorem 3(a) — plus the §1.4 record-only acceptance mechanics: IrrHalts ⟺
  μ_last = 1 (key-degree identity), irrVerdict = (accE, accF) a pure record
  function, τ-hen certificates from mod-p data. So at any box fibering a
  decided ns-free T, "Cert accepts" is record-determined and uniform on the
  thr(T)-cylinder. What Theorem 3 does NOT supply: that the run on x_f REACHES
  a decided tree at N ≥ N\* — that is drainage/no-missing content. Scope
  caveat carried: **(E-N)** (can a level-N box fiber a thr > N tree?) is OPEN
  (O-1thr §6 rev-3 scoping) and touches F4-C's decision-level scoping through
  Theorem 3(c) — displayed, inherited, owned by O-1thr.
* **O-2a Theorem 2(B) supplies the semantic verdict tie:** at the last
  continuing node, accE·accF = deg f_{t^{(k')}} ⟺ μ_{k'} = 1, and at μ = 1
  the cluster factor is irreducible with (e, f) = (accE, accF) — so an
  accepted saturated leaf's verdict is the true factor datum of f (through
  CU-2's Cons_f, which makes 2(B) applicable to emitted histories).
* **TB-CAP (τ-irr) window** (T-6, perimeter-conditional on D-12r): the
  certificate fires within its verdict window — the level bookkeeping that
  makes "accepts AT N ≥ N\*" well-posed (N\*'s join clause).
* **Dfloor supplies NO proof content toward CU-4 — it is CU-4's fence-side
  CONSUMER.** Checked against `Dfloor_phaseB_verifybrief_rev2.md`: the
  conventions (C0)–(C2) are FIXED, with (C2)'s (τ-irr)/(τ-hen) clauses at
  block/residue degree > 1 explicitly NOT proved there (owned by O5triple
  Theorem C through the cluster interface); and **BASE-1(f)** is a displayed
  FENCE — the n = 1 algorithmic half (one-state classifier, the 1×1 solve,
  count faithfulness) is expressly deferred "to the classifier nodes". CU-4
  (+ CU-1/CU-2) is the addressee of that fence; discharging BASE-1(f) at
  n = 1 is the composition's first end-to-end consumer test and costs nothing
  beyond the general statements above.

**Assembly display (why this is a re-label plus glue, and where the glue
lives).** F4-S = record-only acceptance (O-1thr §1.4) + CU-2 (the accepted
history is Cons_f) + 2(B) (verdict-carrying). F4-C = CU-1 (the verdict-
carrying 𝐇 is realized on f; working-level form via Corollary CU-1-LVL's one
D-14 application) + CU-2t (the terminal record fires, forced) + the TB-CAP
window (it fires WITHIN the level budget). No step here is new mathematics —
each is a displayed clause of CU-1/CU-2/CU-2t or a cited theorem — but CU-4 is
honestly graded ASSEMBLY, not bare citation: the composition of these five
supplies has not been walked end-to-end in any home package.

**Grade: RE-LABEL-AS-ASSEMBLY, complete at the statement layer; the walk is
routine given its inputs.** CONDITIONAL-ON-PASS: **P(O-1thr r4)** +
**P(O-2a r5)** + **P(CU-1 r2)** (= V29, for the F4-C leg). Perimeter: TB-CAP
(D-12r) + (E-N) displayed OPEN.

---

## 5. CU-5 (the satellites — K-OB-A / K-OB-B / K-OB-E dispositions per the SYNTH4 merge)

* **K-OB-A (finite-site assembly).** Statement (O3design §2.2, verbatim): for
  a row touching finitely many sites, the fibers agree below the max modulus
  max_i L(H_i, ν_i). Proof by citation: O-1thr Theorem 1 applied per site
  (each read determined below its own ceiling, so all reads below the max) +
  O-13/D-12 finiteness of the site roster (VERIFIED — leaf #1;
  `skeleton_finite` in Lean) + CEIL-UB for the N\*-side bookkeeping (the ONE
  direction K-OB-A consumes, per the O3design finding-4 repair).
  Grade: RE-LABEL, corollary-grade (the old JC-13 half). CONDITIONAL-ON-PASS:
  **P(O-1thr r4)**; the roster-finiteness leg is unconditional.
* **K-OB-B (inStratum ⇒ realized).** Under the DES-6 re-key (O3design §2.2:
  inStratum f H := ∃ dressing 𝐇 of H with Cons_f(𝐇)), membership ⇒
  𝐇 ∈ T_can(f) is DEFINITIONAL; realization then follows from CU-1 (clause
  (i): every Cons_f chain is realized on f) with the working-level form from
  Corollary CU-1-LVL — one N\*(𝐇) ≤ N computation. This is §D2.3's "DES-6
  re-key + CU-1 (definitional + one N\* computation)" exactly; the V1-critical
  bridge is priced but no longer an independent obligation.
  Grade: RE-LABEL onto CU-1. CONDITIONAL-ON-PASS: **P(CU-1 r2)** (= V29).
* **K-OB-E (continuing ⇒ repeated residual).** Statement: a continuing OM node
  presupposes a residual factor of multiplicity μ ≥ 2 — GMN Def 3.9
  arithmetic, the semantic counterpart of the carrier law W3. Disposition per
  the SYNTH4 merge: FOLDED INTO GD-4 as that family's one semantic clause
  (SYNTH4 GD-4 row; the rest of GD-4 is engine bookkeeping with
  proof-by-construction routes on record in both home briefs).
  Grade: RE-LABEL into GD-4, near-definitional; discharged when GD-4's unit
  writes its construction route. No pass condition of its own.
* **K-OB-C (Okutsu proximity): STRUCK from the mandatory set** (DELTA-2 §D2.1
  line 4; only remaining consumer O-7 = route R-QNT; O5triple §7 remark 6
  bypasses the Krasner route for D-7a). Standalone GMN-side citation pull only
  if the rates route is elected. Nothing to state here.

---

## 6. CU-6 (OB2 — σ-invariance, level-free) + the §D2.7 audit, EXECUTED

**Statement (OB2, verbatim O3design §2.1).** If f ∼_OM g then σ(f) = σ(g) —
where ∼_OM is the BNS relation ((O7): f and g admit a COMMON OM factorization
in the published sense) and σ(·) is the splitting type (the multiset of (e, f)
pairs over monic irreducible factors).

**Proof by citation (level-free — no induction, no level filtration).** An OM
factorization assigns each irreducible factor a saturated type; the O-2
dictionary's clause (i) — realized in O-2a as Theorem 2(B)'s invariant
matching ((e, f) per factor = (accE, accF), functions of the type's discrete
data) — plus the BNS §2 definitional transcription (Defs 1.7/3.1–3.2, PINNED:
these quantify over factors, not traces — V16 finding 9 confirmed the
evasion of the induction) gives: ∼_OM preserves the per-factor (e, f) data,
and σ is their multiset. So OB2 = O-2a clause (i) + one transcription +
bookkeeping. Grade: RE-LABEL, complete modulo the BNS §2 transcription duty
(a LITERATURE pin, with the documented arXiv-vs-journal numbering hazard).
CONDITIONAL-ON-PASS: **P(O-2a r5)**. Gate: G-OB2 stays a free rider.

### 6.1 The owed §D2.7 audit: does D-11 actually consume OB2?

**The question (DELTA-2 §D2.7, verbatim charge):** O3design's §R2 consumer
table carries the row `| D-11 / mass-id | σ invariance | OB2 (level-free) |`.
If D-11's eventual statement really consumes OB2, CU-6 stays root-mandatory
WITH its BNS §2 pin; if not, OB2 leaves the mandatory path, CU-6 moves to the
deferred tier, and the LAST root-side BNS touch-point disappears.

**Texts read (the audit's evidence base):**
1. **The D-11 node** (tree §D1.2, verbatim): "the eventual general-n pack's
   kernel entries are the Haar volumes of the T-3/T-6 continuation events at
   the intended instance, the events per row pairwise disjoint with positive
   per-state termination margin, and the pack's block system IS 𝔅_n — or an
   organization covered by the O-12 attempt's robustness criterion (Theorem 3
   + the contingent OL-O12-1). … Inputs: O-2, T-7s, O-14d, T-3/T-6." There is
   NO ∼_OM quantifier anywhere in this text. σ enters D-11 only as the ROW
   LABELS of the pack (the verdict typing of continuation events).
2. **O-12's OL-O12-2** (rev-4 brief, verbatim): "The identification of the
   COMPLETE sealed degree-3 tables — entries beyond those quoted in §7 — with
   an (O3) member of 𝔅₃ is an interface assumption declared outside this
   proof (recorded as the labeled open item OL-O12-2) … it is NOT part of the
   claim." A pure table-data identification; no equivalence-class pooling, no
   ∼_OM, no BNS object appears anywhere in the O-12 brief (checked by grep:
   the only Okutsu mention is an expressly EXCLUDED value-correctness remark).
3. **The O3design row itself** carries no warrant sentence; its visible
   ancestry is the pre-split O-2 clause (vi) rationale (tree: "without it
   LIT-5 yields factorization data, never σ(f) = σ(g)") — a rationale about
   CONSUMING LIT-5/BNS Thm 3.13, which is D-16's move (execution transport at
   ∼_OM pairs, route R-QNT), and which D-11 does not make.

**The distinction that decides it.** What D-11's mass identification DOES need
is σ-CONSTANCY ACROSS THE POLYNOMIALS OF ONE CONTINUATION EVENT — the verdict
labeling a row must be the true splitting type of every polynomial in the
event's cylinder. That is lift-uniformity across one box/cylinder, which is
OWNED and SERVED elsewhere in this composition: O5triple Theorem E ("any two
monic separable lifts of x have equal splitting types", via CU-7's interface)
+ D-15's cylinder law (O-1thr Theorem 3). It is NOT σ-invariance across
∼_OM-equivalent polynomials in different cylinders — no D-11 input identifies
masses by pooling OM-equivalent instances.

**ANSWER: NO — on every text on file, D-11 does not consume OB2.** The
O3design table row is unwarranted by any displayed D-11 content; the
σ-constancy D-11 needs is CU-7/D-15 territory (per-box lift uniformity), not
the BNS equivalence.

**Consequence + recommended DELTA-3 line (governance, sign-off owed — NOT
executed by this unit):** "OB2/CU-6 leaves the root-mandatory path → deferred
tier (route R-QNT, D-16's package, alongside OB1); the BNS §2 definitional pin
(Defs 1.7/3.1–3.2) leaves with it — ZERO root-side BNS touch-points remain;
G-OB2 retained as a free-rider gate." Per §D2.7's conservative reading, CU-6
STAYS root-side until the DELTA-3 line is adjudicated; this section puts the
owed answer on record ahead of the D-11-dispatch deadline (path step 8).
Displayed caveat: D-11 is OPEN — if its eventual PROOF (as opposed to every
present statement text) elects to identify kernel entries by pooling
OM-equivalent instances, the audit re-opens as a re-scoping event (O3adj §4 R3
discipline), not a silent assumption.

---

## 7. CU-7 (O5triple interface discharge + the owed re-attribution)

**What is discharged.** O5triple rev 3 §5 displays four consumed interface
clauses, (I-0)–(I-3), pricing its Theorems B–E (= O-5 LEAF/ASSEMBLY +
D-7a/b/c). The composition serves them as follows — each line names content
that EXISTS as a displayed statement in a home package (this is an
attribution/pricing discharge; the mathematics of each supply carries its own
home conditionality):

* **(I-1) preamble + (a) [path data match].** For every monic separable lift
  g of the decided box x: the run's sites all have ceiling ≤ thr(T) ≤ N, so
  O-1thr Theorem 1/D-14 per-site lift transfer gives that g realizes the same
  engine histories as the box's decode; CU-2 applied to THE RUN ON g then
  gives Cons_g — each slot's engine history transports (Θ) to a node path of
  𝒯(g), side data through OL-2a-2 (GD-2), residual reads through OL-2a-3
  (GD-3). Single-polynomial throughout: no ∼_OM pair, no second polynomial's
  run — exactly O3adj Arg-1's displayed-content reading.
* **(I-1)(b) [terminal event match].** CU-2t (the verdict-carrying terminal
  reading, forced) + CU-4 (F4-S/F4-C acceptance) + Lemma STEEP (corner slots —
  already O5triple's own, conditional on its (L5b)/(L5b′) pins).
* **(I-1)(c) [verdict match].** O-2a Theorem 2(B)/(D): (e_ℓ, f_ℓ) =
  (accE, accF) at saturated leaves, on the Cons_g history supplied by (a).
* **(I-2) [transport injectivity].** OL-2a-2/3 faithfulness — the FULL-form
  slot-wise clauses of GD-2/GD-3 (distinct side reads ↦ distinct sides;
  distinct residual reads ↦ ∼-inequivalent ψ's; note V26's slot-twist
  countermodel and CU-1's coherent-convention gate finding are convergent
  evidence that GD-3's statement must carry the normalization clause) + the
  (N4) corner band (O-1thr). Honest display: these faithfulness legs are OPEN
  GD content — CU-7 discharges the interface's ATTRIBUTION, not these lemmas.
* **(I-3)** is engine typing by construction (O5triple's own §5) — nothing
  owed. **(I-0)** is context-only there; its content is D-15's, served per the
  §8 arrow map.

**The attribution correction (the O3adj §3.5-item-4 action, recorded here as
the correction of record).** O5triple rev 3 still carries, at TWO sites, the
superseded pricing:
* §5 "Attribution." line: "(I-1)(a,b) = O-3 K-RUN clauses 'no-phantom' +
  'acceptance' (clause 4) composed with O-2b's trace/tree correspondence
  (K-DICT-OB1) — the O-3 ⊕ O-2b joint cluster of DELTA §D1.3."
* §8 first open bullet: "(I-1)(a,b) — O-3 no-phantom + acceptance ∘ O-2b
  trace correspondence [the O-3 ⊕ O-2b joint cluster; …]".
**Corrected reading (governing, per DELTA-2 §D2.3 which supersedes §D1.3
item 2):** (I-1)(a) = **CU-2 (O-2a Theorem 2(D)) + O-1thr Thm 1/D-14 lift
transfer below thr(T)**; (I-1)(b) = **CU-2t + CU-4 + Lemma STEEP**; (I-1)(c) =
**O-2a Theorem 2(B)/(D)**; (I-2) = **OL-2a-2/3 faithfulness + the (N4) corner
band**. The "∘ O-2b trace correspondence" phrase priced a node whose content
the displayed clauses never use — the displayed (I-1) is single-polynomial
(no ∼_OM pair anywhere in §5's text); K-DICT-OB1 is consumed ONLY by D-16
(route R-QNT, deferred tier). Per the other-unit-file discipline, the O5triple
brief's own two lines are NOT edited here; the edit rides O5triple's next
revision (owed pointer, §8). Until then THIS section is the attribution of
record, as DELTA-2 already governs.

**Grade: RE-LABEL/re-pricing, complete.** CONDITIONAL-ON-PASS: **P(O5t r3)**
(for Theorems B–E themselves + STEEP) and, through the supplies: **P(O-2a
r5)**, **P(O-1thr r4)**, **P(CU-1 r2)** (via CU-4's F4-C leg), plus the five
O5triple flags and the open GD instances as displayed above.

---

## 8. Cluster summary, arrow map, residue, owed pointers

| unit | statement home | proof home (citation) | grade | pending verdicts |
|---|---|---|---|---|
| CU-2 | §1 (= §D2.3) | O-2a rev 5 Thm 2(D) + (A)–(C) | RE-LABEL complete | P(O-2a r5); GD-1..6 residue |
| CU-2t | §2 (= (t-i)/(t-ii) as one lemma) | route: O-2a 2(B) + Cor 1.20/3.8 + TB-CAP windows | **OPEN (one lemma)** — the cluster's one unexecuted obligation | P(O-2a r5) when written; D-12r perimeter |
| CU-3 | §3 (= F3′ coherent) | O-14a′ Thms 1–3 (twice-stable, Lean-core instance) + O-1thr Thm 1 (D-14) + (O6) | RE-LABEL complete | P(O-1thr r4); realizer leg unconditional |
| CU-4 | §4 (= F4-S/F4-C selected-f) | O-1thr Thm 3 (F1)/(F4) + §1.4 record mechanics + O-2a 2(B) + TB-CAP + CU-1/CU-2/CU-2t glue | RE-LABEL-AS-ASSEMBLY (walk routine, unwalked) | P(O-1thr r4), P(O-2a r5), P(CU-1 r2); (E-N) open |
| CU-5 | §5 | K-OB-A: O-1thr Thm 1 + O-13/D-12 + CEIL-UB · K-OB-B: DES-6 + CU-1 · K-OB-E: → GD-4 · K-OB-C: struck | RE-LABEL complete (corollary-grade) | P(O-1thr r4); P(CU-1 r2) |
| CU-6 | §6 (OB2 level-free) | O-2a clause (i) (= Thm 2(B) invariants) + BNS §2 pin | RE-LABEL complete; **audit answered: D-11 does NOT consume OB2** → recommended DELTA-3 eviction, sign-off owed | P(O-2a r5); until DELTA-3: root-side (conservative) |
| CU-7 | §7 | interface pricing to CU-2/CU-2t/CU-4 + O-1thr Thm 1/D-14 + O-2a 2(B)/(D) + GD-2/3 faithfulness | RE-LABEL/re-pricing complete; attribution correction recorded | P(O5t r3) + inherited |

**Arrow-map deltas this unit makes explicit (vs the O3adj §3.1 skeleton):**
(1) OL-6 is consumed by CU-2 ONLY (CU-1 rev 2 dropped it for the
(P-ROOT)/(P-KEY)/(FR≡) pins — already flagged to the orchestrator in the CU-1
rev-2 record). (2) CU-2t's home split is CU-1 rev 2's interior/terminal
split (terminal records are not GMN children), superseding the O3adj wording
"from O-2a Theorem 2(B) saturation + TB-CAP windows" only in WHERE the seam
sits, not in what proves it. (3) If the §6.1 audit's DELTA-3 line is signed
off, the D-11 arrow "σ-invariance ← CU-6" is DELETED and replaced by
"row-label σ-constancy ← CU-7 (O5triple Thm E) + D-15".

**NEW-mathematics report (the charge's explicit question):** NO re-label in
this cluster turned out to need new mathematics beyond what DELTA-2 already
prices. The two non-trivial findings: CU-2t is an unexecuted (corollary-grade)
lemma — consistent with its §D2.3 "OPEN (one lemma)" pricing, now with its
exact statement and proof route displayed (§2); CU-4 is assembly whose
end-to-end walk exists in no home package (§4) — routine given CU-1/CU-2/CU-2t,
flagged so the walk gets an owner rather than being silently presumed.

**Cluster-wide open residue (owners named, nothing hidden):** the GD-1..GD-6
instances (heads: GD23 under V28; the GD campaign) · CU-1's induction (V29) ·
CU-2t's lemma (§2, unowned — recommend CU-1 orbit) · the five O5triple flags
(GD-1/GD-7/GD-8 duties) · TB-CAP's D-12r perimeter · (E-N) (open, scoped,
owner O-1thr) · LC-COH (open, consumed by nothing) · the CU-1 rev-2 pins
(P-ROOT)/(P-KEY)/(FR≡) at orders ≥ 2 (owner: MOVES transcription / GD-6) ·
the four owed passes of §0.

**Owed pointers to other units' files (NOT executed here):** O5triple brief —
replace the two attribution lines per §7 at its next revision · O-2a brief §4
— OL-6's consumer line may add "(sole consumer after CU-1 rev 2)" · the tree —
the §6.1 DELTA-3 line (orchestrator sign-off) · CU-2t — assign an owner at
CU-1's V29 adjudication.

**Files:** this record = `lean/notes/openmath/CU_cluster_phaseB.md` (the
consolidated CU-2..CU-7 unit of record). No other file touched.

---

## 9. CU-2t EXECUTED — the terminal-seam lemma (unit D3CU2t, appended 2026-08-02)

*(Appended by the CU-2t prover unit per the wave-8 dispatch (ledger §"WAVE 8
COMPLETE"; tree DELTA 3). This section SUPERSEDES §2's grade line: CU-2t is
now **PROVED-UNVERIFIED, conditional exactly as displayed in §9.6**; the
statement is §2's, made precise below; the proof is corollary-grade over the
cited homes, exactly as §D2.3 priced it ("OPEN (one lemma) over the GD
residue" — the lemma is now written). Hostile pass owed. The section is
self-contained modulo the NAMED citations; every consumed external statement
is quoted or pinpointed.)*

### 9.0 What is proved, in one paragraph

At a verdict-carrying leaf the terminal record has no degrees of freedom:
its semantic datum (the level-(k'+1) read entry) and its verdict pair are
single-valued functions of (f, prefix chain), and the verdict pair equals
the true (e, f) invariant pair of a genuine irreducible p-adic factor of f.
This discharges the two old terminal-seam obligations as ONE lemma — (t-i)
(the terminal datum ties to the level-(k'+1) GMN read of f, same shape as
(c1)) and (t-ii) (extending Θ's codomain by a final entry (λ_{k'+1}, ⊥) is
consistent) — by the route on record at O3design §2.1 (O2) and §D2.3:
**O-2a Theorem 2(B) saturation + Cor 1.20/3.8 + the TB-CAP windows**. No
global T_can definition rides on it (the Cons^τ-SET died with the O3design
replacement); the clause is defined and discharged PER SEAM OBJECT.

### 9.1 Setting (objects verbatim from O-2a rev 5 §§1–2; recap, no re-definition)

Standing perimeter (§0 of this file): f ∈ O[x] monic separable ns-free of
degree n, disc f ≠ 0, pinned representative family F_rep with the fixed
function Lift. From O-2a rev 5 (`O2a_phaseB_verifybrief_rev5.md`), consumed
at **P(O-2a r5)**:

* the carrier 𝔈 of dressed histories 𝐇 = (ρ₀; ν₁, …, ν_k), ρ₀ = (ψ̂₀, a₀),
  ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i), laws W1–W5; continuing
  (sel ≠ ⊥) vs terminal (sel = ⊥) nodes; 𝐇° the continuing part, k' its
  length; f₀ := deg ψ̂₀, g_i := deg ψ̂_i;
* Θ(𝐇) = (ψ̂₀; (−h_i/e_i, ψ̂_i)_{i ≤ k'}) ∈ 𝔗 (formal; discards a terminal
  last node); Cons_f = (c0)+(c1)+(c2) with the intrinsic positional clause;
* Lemma R (PROVED): Θ injective on all-continuing Cons_f histories, with the
  displayed TERMINAL NON-CLAIM — Cons_f constrains no terminal field, and
  the deferred seam is exactly (t-i)/(t-ii) as displayed in O-2a §2;
* accE_i := e₁⋯e_i, accF_i := f₀g₁⋯g_i (so accE₀ = 1, accF₀ = f₀);
* ι and the chain interpretation: c := Θ(𝐇°) of order k',
  φ_{i+1} := Lift_i(c_{≤i}); level-(k'+1) GMN objects (v_{k'+1},
  N_{k'+1}^−(f), residuals) are read through ι — unconditionally at k' = 0
  ((D4), PROVED), given **OL-1** (= GD-1) at k' ≥ 1;
* Theorem 1 (PROVED, incl. (D3): the order-1 first-read format IS
  (L2)/(L3)'s data, with the (L3+) j₀-convention: j₀ := ord_{φ₁}(f) ≤ 1 for
  separable f, and a j₀ = 1 slope-−∞ side of length 1 carrying the exact
  factor φ₁, irreducible with (e, f) = (1, f₀));
* Theorem 2(B) (conditional proof; hypotheses Cons_f + OL-1): saturation at
  the last continuing node — deg f_{t^{(k')}} = m_{k'+1}·μ_{k'} with
  m_{k'+1} = accE_{k'}·accF_{k'}, hence accE·accF = deg f_{t^{(k')}} ⇔
  μ_{k'} = 1, and at μ_{k'} = 1 the cluster factor f_{t^{(k')}} is
  IRREDUCIBLE with (e, f) = (accE_{k'}, accF_{k'}) [via GMN Def 3.9 +
  Cor 3.8; at k' = 1 this is Cor 1.20, inside the unconditional Theorem 1
  (D1)]. Inside the same proof: ω_{k'+1}(f) = ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) =
  μ_{k'} — the (c2) identification.

Pinned literature consumed directly (quoted in `docs/GMN_citations.md`):
**GMN Lemma 2.17** with §2.1's ω-definition and Def 1.8 ("principal
φ-polygon … including the side of slope −∞"): (2) the length of N_r^−(f) is
ω_r(f); (3) the slope-−∞ side of N_r^−(f) has length ord_{φ_r}(f). **LIT-3
(HEN-LIFT)**: f̄ = ψ·h̄ coprime with ψ irreducible lifts to f = F·G, F̄ = ψ,
uniquely; F monic with irreducible reduction is irreducible with
(e, f) = (1, deg ψ). **T-6 TB-CAP** (dual-accepted; (τ-irr) leg
perimeter-conditional on D-12r): (τ-hen) leaves cap at N_V = 1
unconditionally; (τ-irr) leaf verdict classes are exact finite unions of
shape-computable level-N(η) cylinders. N\*(𝐇) = the D4R.4/L12 per-branch
level with the TB-CAP verdict-window join (§0 of this file, standing).

**Seam vocabulary.** A terminal machine record is **verdict-carrying** if it
announces an invariant pair (E, F) ∈ ℕ² for its branch — the Dfloor
(C0)–(C2) verdict fields. The **seam object** is the pair (𝐇°, ν): 𝐇° ∈ 𝔈
all-continuing with the run's emitted prefix data, ν the branch's terminal
machine record.

**Carrier note (a finding of this unit, displayed — nothing edited).**
Under W3/W5 as printed in O-2a rev 5 (C1), the CONCATENATION (𝐇°; ν) is a
well-formed 𝔈 element only when every interior selection has μ ≥ 2 — so it
is 𝔈-legal in the (τ-hen) case below (k' = 0; Theorem 1 case (ii)'s shape),
but at a saturated prefix (μ_{k'} = 1) appending ν would VIOLATE W3's
interior clause. §2's display "𝐇 = (𝐇°; ν)" is therefore to be read as the
seam PAIR; the dressed history of a (τ-irr)-decided branch is the
all-continuing 𝐇° itself (consistent with OL-4's "a run emits at most one
terminal record, last" — the record exists run-side), and Θ^τ below is
defined on pairs. This sharpens, and is convergent with, CU-1 rev 2's split
("terminal machine records are not GMN children at all").

### 9.2 The decided configurations and the forced terminal datum (definitions)

Fix f (perimeter) and a seam object (𝐇°, ν) with Cons_f(𝐇°); k', c,
φ_{k'+1} as above; j₀ := ord_{φ_{k'+1}}(f) (at k' = 0: j₀ = ord_{φ₁}(f)).
Note j₀ ≤ 1 at EVERY level: φ_{k'+1}² | f forces a repeated root of f,
contradicting disc f ≠ 0 (the (D3) argument verbatim, φ-irreducibility not
used).

* **DEC(τ-irr):** k' ≥ 1 and μ_{k'} = 1 (the last read is saturated).
* **DEC(τ-hen):** k' = 0 and [a₀ = 1 or j₀ = 1] (the track is
  Hensel-decided: simple residue factor, or the slope-−∞ exact-factor side).
  W3 permits a terminal NODE here only at a₀ ≥ 2; at a₀ = 1 the seam object
  is (ρ₀) plus the machine record — the carrier note applies.

**The terminal datum T(f, 𝐇°)** (defined only on DEC configurations):
* read entry λ_{k'+1} ∈ ℚ_{<0} ∪ {−∞}: on DEC(τ-irr), the slope of the
  unique side of N_{k'+1}^−(f) (Lemma 9.1(i) below shows there is exactly
  one, of horizontal length 1; λ = −∞ in the j₀ = 1 sub-case). On
  DEC(τ-hen): −∞ if j₀ = 1 (the unique slope-−∞ side, length 1); at
  a₀ = 1 ∧ j₀ = 0, the slope of the unique (length-1) side of N₁^−(f).
* verdict pair: (accE_{k'}, accF_{k'}) on DEC(τ-irr); (1, f₀) =
  (accE₀, accF₀) on DEC(τ-hen).

This IS the O3design (O2) terminal clause, stated per seam object: the
(t-ii) codomain extension appends a terminal entry to Θ(𝐇°), and (t-i) says
the terminal datum ties to the level-(k'+1) GMN read of f, same shape as
(c1) — side-existence + position with sel = ⊥ in place of a selection.

### 9.2a Definition RC — record-consistency (the (t-i) tie as a displayed predicate; R2, the CUC F2 repair)

The uniqueness tail of (ii) and the injectivity layer of (iii) quantify over
"consistent" records; that predicate is now DEFINED (it was an undefined
word at rev 1 — CUC F2):

**Definition RC.** Let f satisfy the perimeter and (𝐇°, ν) be a DEC seam
object with Cons_f(𝐇°); c = Θ(𝐇°). Say ν is **RC-consistent with
(f, 𝐇°)** — written RC_f(𝐇°, ν) — iff both:

* **(RC-read)** ν's shape/position fields (e, h, ℓ, s, u), with sel = ⊥,
  are the (c1)-shape datum of a side of N_{k'+1}^−(f), read through ι over
  c — the same clause shape as (c1), sel = ⊥ in place of a selection; on
  the −∞ branches (j₀ = 1), the slope-−∞-side convention of §9.2.
* **(RC-verd)** ν's announced verdict pair (E, F) equals the PREFIX
  ACCUMULATOR pair: (accE_{k'}, accF_{k'}) on DEC(τ-irr), (1, f₀) on
  DEC(τ-hen) — a pure record function of 𝐇°'s own discrete fields, the
  (T-VERD) shape (§9.4).

**Non-circularity, displayed.** Neither clause mentions the true factor or
its invariants: (RC-read) is a polygon read of f over the prefix's chain
(exactly the (c1) shape), and (RC-verd) is arithmetic of 𝐇°'s own fields.
That the RC-pinned pair equals the TRUE invariant pair of a genuine
irreducible factor is a THEOREM — clause (ii)-main below — not part of the
definition. This is the non-circular reading CUC F2 asked to be displayed.

**Granularity caveat (displayed, priced nowhere else).** RC constrains the
field vector (e, h, ℓ, s, u, sel, E, F) — call this the record's **datum
granularity**. No document on file displays a field INVENTORY for terminal
machine records (beyond Dfloor's (C0)–(C2) verdict fields), so
"RC-consistent records over the same (f, 𝐇°) coincide" is asserted at
datum granularity only; full-RECORD coincidence additionally needs the
inventory closure (that the RC-constrained fields exhaust a terminal
record's payload) — an engine-bookkeeping question routed WITH the
(T-DEC)/(T-VERD) scope note to the GD-4 owner (§9.4), consumed by no
clause below.

### 9.3 Lemma CU-2t and proof

**Lemma CU-2t ((t-i) + (t-ii) as one lemma).** Let f satisfy the standing
perimeter and let (𝐇°, ν) be a seam object with Cons_f(𝐇°), in a DEC
configuration [GMN objects through ι: unconditional at k' = 0, given OL-1 at
k' ≥ 1]. Then:

**(i) [read forcing — the (t-i) polygon clause].** On DEC(τ-irr):
N_{k'+1}^−(f) has total horizontal length 1, hence consists of EXACTLY ONE
side; at j₀ = 0 that side is finite of length 1 (so its (c1)-shape datum has
e = ℓ = 1, integral slope λ_{k'+1} = −h with h ≥ 1, and initial point (s, u)
in the order-(k'+1) integer frame), and at j₀ = 1 it is the slope-−∞ side of
length 1 (empty finite part). On DEC(τ-hen) with j₀ = 1: the slope-−∞ side
exists, is unique, and has length exactly 1; with a₀ = 1: N₁^−(f) has total
length 1 and exactly one side. In every case, every coordinate of the read
entry is a single-valued function of (f, c), and NO residual selection
exists or is needed (in the length-1 finite cases the residual R_{λ}(f) has
degree d(S) = 1, so even its factor choice is unique of multiplicity 1).

**(ii) [verdict forcing + correctness].** On DEC(τ-irr): the branch's
cluster factor f_{t^{(k')}} is irreducible with
(e, f) = (accE_{k'}, accF_{k'}) [O-2a Theorem 2(B), consumed with its own
hypothesis row Cons_f + OL-1; = Cor 1.20 at k' = 1, Cor 3.8 at k' ≥ 2].
On DEC(τ-hen): f has a unique monic irreducible factor F with F̄ = ψ̂₀ in
the decided reading — F = φ₁ (the exact −∞ factor) at j₀ = 1, F = the
LIT-3 Hensel lift at a₀ = 1 — with (e, f) = (1, f₀) [(D3)/(L3+) PROVED +
LIT-3]. Hence in both cases the verdict pair of T(f, 𝐇°) equals the TRUE
invariant pair of a genuine irreducible p-adic factor of f; moreover it is
a function of the PREFIX'S OWN DISCRETE FIELDS alone ((f₀; e_i, g_i)_{i≤k'}
resp. f₀), so any two verdict-carrying terminal data consistent with the
same (f, 𝐇°) coincide — no free choice.

**(iii) [(t-ii) consistency].** Define Θ^τ(𝐇°, ν) := Θ(𝐇°) ⌢ (λ_{k'+1}, ⊥)
with λ_{k'+1} the read entry of (i). Θ^τ is well-defined on DEC seam objects
(by (i)), truncation-compatible over Θ (strip the last entry), takes no
Lift call at level k'+1 (the chain ENDS: no new representative, OL-1's
cumulative quantifier untouched), and is INJECTIVE on DEC seam objects over
a fixed f: equal images force equal Θ(𝐇°), Lemma R recovers 𝐇°, and
(i)+(ii) reconstruct the terminal datum from (f, c). This closes Lemma R's
terminal seam EXACTLY at verdict-carrying decided leaves; free
(non-verdict) terminal records remain non-recoverable — the non-claim is
unchanged, now displayed as scoped rather than open.

**(iv) [windows].** The verdict pair on DEC(τ-hen) is a function of the
level-1 datum ψ̂₀ alone (proved in (ii)) — consistent with, and joined into
N\*(𝐇) through, TB-CAP's unconditional (τ-hen) cap N_V = 1. On DEC(τ-irr)
the verdict pair is a function of 𝐇° alone (ii); the leaf verdict class as
a box event is an exact finite union of shape-computable level-N(η)
cylinders — consumed VERBATIM from TB-CAP (τ-irr) [T-6,
perimeter-conditional D-12r], used here only as the N\*(𝐇) join bookkeeping
that makes "read inside the verdict window" well-posed. CU-2t re-proves no
cylinder structure.

*Proof.*

(i) DEC(τ-irr): Cons_f(𝐇°)'s clause (c2) at i = k' gives
ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) = μ_{k'} = 1, and by the §2.1 ω-definition
(pinned with Lemma 2.17) this is ω_{k'+1}(f) — the identification O-2a's
Theorem 2(B) proof displays. Lemma 2.17(2) [through ι; φ_{k'+1} a Def-2.12
representative by (D4)/OL-1]: the length of N_{k'+1}^−(f) — which by Def
1.8 INCLUDES the slope-−∞ side — is ω_{k'+1}(f) = 1. A principal polygon of
total length 1 has exactly one side, of horizontal length 1. Lemma 2.17(3):
the −∞ side has length j₀ ∈ {0, 1} (j₀ ≤ 1 by separability, §9.2). If
j₀ = 0 the one side is finite: horizontal length E = e·ℓ = 1 forces
e = ℓ = 1 and λ_{k'+1} = −h ∈ ℤ_{<0}; its initial point (s, u) is the
(c1)-shape positional datum in the order-(k'+1) integer frame. If j₀ = 1
the −∞ side exhausts the length: the finite part is empty. DEC(τ-hen),
j₀ = 1: Lemma 2.17(3) at r = 1 gives the −∞ side with length
ord_{φ₁}(f) = 1; a polygon has at most one −∞ side (Def 1.8), so it is
unique. (Here ω₁(f) = a₀ may exceed 1: the finite sides sprout the track's
OTHER children — this lemma books only the −∞ branch.) DEC(τ-hen), a₀ = 1:
ω₁(f) = ord_{ψ̂₀}(f̄) = a₀ = 1 ((c0)), so N₁^−(f) has total length 1 and
exactly one side as before. In each case the polygon is a GMN function of
(f, c) (of (f, ψ̂₀) at k' = 0), a polygon has at most one side of a given
slope, and the −∞ side is unique — so every coordinate of the read entry is
single-valued in (f, c). Choice-freeness of the residual: where the one
side is finite it has d(S) = ℓ = 1, so R_λ(f) is a degree-1 polynomial over
F_{k'+1} (Def 2.21), with a unique monic irreducible factor, of
multiplicity 1; a terminal record carries sel = ⊥ and consumes none of it.

(ii) DEC(τ-irr): Theorem 2(B) applies to 𝐇° (all-continuing, Cons_f;
saturation guard k' ≥ 1 holds; hypotheses Cons_f + OL-1 displayed):
μ_{k'} = 1 gives deg f_{t^{(k')}} = m_{k'+1} = accE_{k'}·accF_{k'} and
f_{t^{(k')}} irreducible with (e, f) = (accE_{k'}, accF_{k'}) — at k' = 1
this instance is Theorem 1 (D1)'s saturation law (Cor 1.20),
UNCONDITIONAL. The pair (accE_{k'}, accF_{k'}) = (e₁⋯e_{k'}, f₀g₁⋯g_{k'})
is literally a function of the prefix's discrete fields. DEC(τ-hen): at
j₀ = 1, (D3)/(L3+) [PROVED, O-2a §3]: the −∞ side carries the EXACT factor
φ₁, monic with irreducible reduction ψ̂₀, hence irreducible, with
(e, f) = (1, f₀); at a₀ = 1, LIT-3 gives the unique monic factorization
f = F·G with F̄ = ψ̂₀, F irreducible with (e, f) = (1, f₀). (At
a₀ = 1 ∧ j₀ = 1 the two readings name the same factor F = φ₁.) The pair
(1, f₀) is a function of ψ̂₀. Uniqueness across candidate records: a
verdict-carrying terminal datum consistent with (f, 𝐇°) must announce its
branch's invariant pair; the branch's decided factor is the SINGLE
polynomial named above (irreducibility makes f_{t^{(k')}} one factor, not a
product; LIT-3's F is unique), so its invariant pair is single-valued —
combined with (i), the whole datum T(f, 𝐇°) is the unique consistent one.

(iii) Immediate from (i)/(ii) + Lemma R, as displayed in the statement.
The trailing ⊥ entry separates Θ^τ-images from Θ-images of all-continuing
histories, so no new collision is created — consistency of the extension in
O-2a §2's sense.

(iv) The function claims were proved inside (ii); the two TB-CAP legs are
consumed as cited (T-6 dual-accepted; the (τ-irr) leg perimeter-conditional
on D-12r), and N\*(𝐇)'s verdict-window join is the standing definition. ∎

**Corollary CU-2t-deep (displayed, OUT of the two priced cases;
conditional).** At an UNDECIDED prefix (k' ≥ 1, μ_{k'} ≥ 2) with j₀ = 1 at
level k'+1 — the deep exact-key corner, GD-8's seam — if the engine books
the −∞ branch with a verdict-carrying terminal record, the same forcing
shape holds with verdict (accE_{k'}, accF_{k'}): the −∞ side is unique of
length 1 (Lemma 2.17(3) + separability, as in (i)), and the exact factor
φ_{k'+1} is irreducible with (e, f) = (accE_{k'}, accF_{k'}) GIVEN the
representative-invariant fact **(REP-IRR)**: a Def-2.12 representative of a
type over F_rep is irreducible over K with e = e₁⋯e_{k'}, f = f₀⋯f_{k'}
[GMN §2, Prop 2.15's neighborhood — a LITERATURE pull NOT yet pinned in
`docs/GMN_citations.md`; pin owed to the literature unit]. This corollary
is NOT part of Lemma CU-2t's grade; its conditionality adds (REP-IRR) +
GD-8's booking conformance, and its owner remains GD-8/O5triple NODE(ii)/
Thm A(3), per §2's routing.

### 9.4 The emitted-side tie (the §2 statement's "emitted by a complete run")

For 𝐇°+ν produced by a complete run on f, three supply rows connect the
machine to the lemma — displayed, priced, nothing silently absorbed:

* **(T-PREFIX).** Cons_f(𝐇°): this is CU-2 (§1 = O-2a Theorem 2(D)),
  consumed with its full displayed residue OL-1..OL-6 = the GD-1..GD-6
  instances. Nothing new.
* **(T-DEC).** The engine emits a verdict-carrying terminal record on a
  branch ONLY at a decided configuration, bound to its branch: after the
  branch's saturated selection (μ_last = 1 → the τ-irr booking) or at the
  base read's Hensel/−∞ booking (→ τ-hen); the deep exact-key booking, if
  the engine performs one, is the displayed Corollary corner. Engine
  CONTROL-FLOW bookkeeping — the same clause OL-4's intended proof route
  already cites ("the (τ-irr) rule halts a branch at multiplicity 1").
* **(T-VERD).** The emitted verdict pair is the record function of the
  emitted prefix: (accE_{k'}, accF_{k'}) resp. (1, f₀). Engine RECORD
  bookkeeping (the accumulator fields are part of the emitted record
  stream).

Given the rows: emitted verdict-carrying ⇒ DEC configuration with Cons_f
prefix ⇒ (Lemma CU-2t) the terminal datum is the forced T(f, 𝐇°) and the
emitted verdict equals the true invariant pair of the branch's irreducible
factor. **Pricing of (T-DEC)/(T-VERD):** both are GD-4-family instances
(D2.2: "emission/record discipline — engine bookkeeping, not GMN
mathematics", proof-by-construction routes on record); they are NOT in
OL-4's printed clause list (which covers W-laws + (c0) only) — a displayed
SCOPE NOTE owed to the GD-4 owner: GD-4 gains the two terminal rows. NO new
open family is created. The machine-side home of both statements is O-1thr
§1.4's record mechanics ("IrrHalts ⟺ μ_last = 1"; "irrVerdict =
(accE, accF) a pure record function") — cited here as CORROBORATION ONLY,
not consumed, so CU-2t's pass conditionality stays as §2 priced it (no
P(O-1thr r4)).

### 9.5 Conditionality (exact), consumers, non-claims

**Conditional on:** P(O-2a r5) [Theorem 2(B) + (D3)/Theorem 1 + Lemma R +
the OL statements consumed via CU-2] · TB-CAP's D-12r perimeter [(τ-irr)
window leg only; the (τ-hen) leg is unconditional T-6 content] · the GD
residue: via CU-2/(T-PREFIX) = OL-1..OL-6, plus OL-1 directly at k' ≥ 1 in
clauses (i)/(ii), plus the (T-DEC)/(T-VERD) GD-4 rows (§9.4). Zero new open
inputs beyond the GD families already on the mandatory path — exactly the
§D2.3 pricing.

**Consumers served:** CU-4's F4-C leg (§4's assembly display: "CU-2t (the
terminal record fires, forced)" — this section supplies the forced-value
half; the COMPLETENESS half, that the certificate fires within the window
on the box, remains CU-4's walk) · CU-7 (I-1)(b) (§7: terminal event match
= CU-2t + CU-4 + Lemma STEEP) · Lemma R's consumer audit (any future
consumer needing full-𝐇 injectivity now has the verdict-carrying case
supplied by Θ^τ, §9.3(iii)).

**Non-claims (displayed):** (1) no claim that every decided branch GETS a
verdict emitted at any particular level — completeness/acceptance is CU-4
(F4-C) + O-1thr territory; (2) no claim about free (non-verdict) terminal
records — Lemma R's non-claim stands; (3) the deep exact-key corner is the
displayed Corollary, conditional on (REP-IRR) + GD-8, owned elsewhere;
(4) no box-level lift quantification — per §0, D-15 owns all of it; (5) no
Lean file touched; no other unit's file edited.

### 9.6 Falsifier record (falsifier-first duty: discharged by citation)

The lemma's refutable surface — the forced VERDICT VALUES — is already
executed by O-2a's standing falsifiers, cited as run (O-2a rev 5 §6):
**F1** (3432 order-1-decided samples: predicted (e, f) verdicts — Hensel
(1, f₀) and Cor-1.20 saturated (e₁, f₀g₁) — vs PARI prime-decomposition
ground truth, 0 mismatches: exercises DEC(τ-hen) a₀ = 1 and DEC(τ-irr)
k' = 1); **F3** (order-2 saturated families incl. wild residue-extended:
verdicts (4, 1) and (4, 2) = (accE₂, accF₂) confirmed 12/12: DEC(τ-irr)
k' = 2); **F5** (871 forced j₀ = 1 samples, −∞ side booked (1, f₀), 0
mismatches on the 827 decided: DEC(τ-hen) j₀ = 1). The remaining clauses
((i)'s polygon shape, (iii)'s injectivity) are structural
functions-of-(f, c) statements with no independent numeric surface beyond
the polygon reads those same harnesses perform. No new harness is owed; a
verifier wanting a fresh gate should extend F3's family to a k' = 2 seam
with j₀ = 1 at level 3 (the Corollary corner — currently UNexercised, and
honestly out of the lemma's grade).

### 9.7 Charge to the hostile verifier (pass owed)

Check: (1) the W3 carrier note (§9.1) against O-2a rev 5 (C1) verbatim —
the seam-pair reading is THIS unit's, not O-2a's; (2) the Lemma 2.17/Def
1.8 consumption (does the pinned statement really give length = ω INCLUDING
the −∞ side, and −∞-length = ord_{φ}(f)?); (3) the ω = μ identification's
dependence on (c2) + the pinned ω-definition; (4) that (ii) consumes
Theorem 2(B) only at its displayed hypothesis row and adds no hidden
realization semantics; (5) that (T-DEC)/(T-VERD) are engine-bookkeeping
rows (GD-4 grade), not smuggled mathematics; (6) that the Corollary's
(REP-IRR) is genuinely quarantined out of the lemma's grade; (7) the
j₀ ≤ 1 separability argument at every level; (8) that Θ^τ creates no
collision with Θ-images (the trailing-⊥ separation). Falsifier F1/F3/F5
citations are checkable against O-2a rev 5 §6 verbatim.

**Grade after this unit: CU-2t = PROVED-UNVERIFIED, conditional per §9.5.**
§2's "OPEN (one lemma)" and §8's table row and residue line are SUPERSEDED
accordingly (append-only: the § texts above are unedited). Owner question
(§8's owed pointer) resolved: this unit (D3CU2t) wrote it; the CU-1 orbit
inherits maintenance at V29 adjudication as recommended.

**Files (§9 addendum):** this section appended to
`lean/notes/openmath/CU_cluster_phaseB.md`. No other file touched by §9;
the tree's DELTA 3 (same commit) records the path-level status.
