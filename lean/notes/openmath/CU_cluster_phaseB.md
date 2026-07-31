# The CU re-label cluster (CU-2, CU-2t, CU-3, CU-4, CU-5, CU-6, CU-7) — consolidated Phase-B unit (Fable "CUC", 2026-07-31)

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

**Statement (CU-2).** Let f satisfy the standing perimeter. Every history 𝐇
emitted by a complete run of the engine's stage flow on f is a well-formed
element of the carrier 𝔈 satisfying Cons_f — hence, through the GMN
interpretation ι and O-2a Theorem 2(A)–(C): each emitted record (with its
dressing) is the GMN datum of the stage read over its emitted prefix's chain
Θ(𝐇_{≤i}) ((c1) side data verbatim, (c2) residual multiplicity), the chain
places t^{(i)} ∈ t_i(f) at every level with injective placement, the invariant
matching and saturation clauses of 2(B) hold, and the index charge of 2(C)
bounds dCert(𝐇) ≤ ind(f). In words: every emitted record is the GMN datum of
its chain — the run emits NO phantom.

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
record exists at a verdict-carrying leaf.

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
