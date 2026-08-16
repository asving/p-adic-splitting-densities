# OM-7 — `[GENHN-HE(μ=3)]` + `[GENHN-TOW-1]` (HYP.81 / HYP.82), incl. the no-owner finding — unit note, 2026-08-16

**Charge.** Ledger rows HYP.81 (`[GENHN-HE(μ ≥ 3)]`, the deep-leaf σ-decision conjunct,
first live `n = 6`) and HYP.82 (`[GENHN-TOW-1]`, the `n ≥ 8` tower supplier law), plus the
chapter-I composer's ownership finding (orchestrator item **O-1**): the μ = 3 slice of
HYP.81 at its first live degrees `n = 6, 7` is **corpus-unconditional** (THEOREM HE3.A /
COROLLARY HE3.B at μ ≤ 3) but has **no transcription owner in any committed chapter**.
Mandate: outline → per-step certification (exact numerics, both primes, both
characteristics, constructed-counterexample attacks) → prove only certified steps; decide
the ownership disposition (an E-side node per E §14, an H-adjacent witness file per the
H09w/H89w precedent, or a C-side tower node) and land there if the vocabulary reaches.
Fences honored: chapter E's trap E-3 (E carries, never proves, the μ ≥ 3 σ-decision);
the μ ≥ 4 region rides HYP.143 (HE3-BOX-6 branch (ii)) and is OM-10's family, not mine
to discharge; never weaken, never push.

**Statuses used:** PROVED / CERTIFIED-OPEN / REFUTED(+repair) / REDUCES-TO(<row>) /
CITE-CANDIDATE.

**Verdict summary** (details §3; certifications §2; landings + ownership §4):

| item | verdict |
|---|---|
| 81-S1 five-type exhaustiveness at μ = 3 | **PROVED** (Lean `H73w.lean`: `stageType3_complete`, exact enumeration cert) |
| 81-S2 the transport dictionary (HE3.A at μ = 3) | **PROVED-IN-CORPUS, transcription LANDED at the H.73 standard** — dictionary + arithmetic in Lean (`heTransport`/`stageSigma3`), the σ-decision itself carried by executable teeth (om7 battery: embedded n=7 rows, equal-char rows, D′=4 f₁=2 row, h=2 row — all GREEN, 0 violations), exactly H.73's own standard ("the σ decision itself is carried by the executable regression, not by this file") |
| 81-S3 degree conservation at μ = 3 | **PROVED** (Lean: `stageSigma3_degree`) |
| 81-S4 μ ≤ 3 composite-stage-free (strict descent) | **PROVED** (Lean: `no_stageCS_below_four`; GENIND.A(IV) arithmetic) |
| 81-S5 branch-(ii) unreachability at μ ≤ 3 | **PROVED** (Lean: `branch_ii_needs_mu_four`) |
| 81-S6 first-live degrees n = 6, 7 (and μ ≥ 4 ⟹ n ≥ 8 at D′ ≥ 2) | **PROVED** (Lean: `mu3_first_live`, `mu4_lives_at_eight`; the D′ = 1 leg is HE3-4D1's direct case, OUTSIDE `GenreDatum`'s grammar — scope note §4.2) |
| 81-S7 μ = 2 consistency (GENHN.C = the μ = 2 case of HE3.A, no circularity) | **PROVED** (Lean: `stageSigma_eq_transport_mu2` — H.73's dictionary IS the transport at μ = 2) |
| 81-S8 the μ ≥ 4 residue | **CARRY, unchanged** — HYP.143 (HE3-BOX-6 branch (ii)), OM-10's family; narrowed residue restated §3.1 |
| HYP.81 post-unit disposition | **CARRY, μ = 3 slice OWNED** — O-1 discharged: transcription home = `leanfinal/Uniformity/ChapH/H73w.lean` (H-adjacent witness file, H09w/H89w precedent) + this unit's battery as its teeth; chapter I's I.06 docstring gets its owner; E's BLOCKED-HYP.81 stubs at μ = 3 may cite the owner; μ ≥ 4 conjunct carried exactly as before |
| 82-S1 threshold arithmetic (n ≥ 2^{r+1}, sharp) | **PROVED** (Lean `C93.lean`: `tower_first_live` at C.93's signed signature, + sharpness witness; exhaustive cert) |
| 82-S2 census disposition (items (1)–(6)) | **CERTIFIED** (mechanical re-verification vs committed CHAP-C + leanspec names — table §2.6) |
| 82-S3 the n ≥ 8 open remainder | **CARRY, unchanged** — the box family HYP.67–71/78–80/142/143/144-BOX-2 (OM-10); verified: nothing in it leaks below n = 8 |
| HYP.82 post-unit disposition | **CARRY, narrowed** — the census's arithmetic node now PROVED in Lean; the residue is exactly the named box family, no new conjunct |

---

## §1. HIGH-LEVEL OUTLINE (mandated order)

### 1.1 The ledger rows, verbatim (spec/HYPOTHESIS_LEDGER.md)

> HYP.81 `[GENHN-HE(μ ≥ 3)]`
> WHERE: W12 L437; GENIND L3081–3084.
> STATEMENT: Stage leaves of multiplicity μ≥3 have required σ-decision; first live n=6.
> CONSUMED BY: W12/GENIND from n=6.
> CLASS: hypothesis-box
> PROPOSED DISPOSITION: CARRY — independent leaf obligation. SCOPE SPLIT ADDED (v3, delta
> item 9): HE3 proves THEOREM HE3.A and [GENHN-HE(μ)] UNCONDITIONAL for μ≤3 — exactly the
> first-live n=6,7 case — while at μ≥4 (n≥8) COROLLARY HE3.B rides the open HE3-BOX-6
> ramified branch (ii). The conjunct is unchanged; its supplier is conditional above μ=3.
> See HYP.143.

> HYP.82 `[GENHN-TOW-1]`
> WHERE: GENIND L3081–3084.
> STATEMENT: n≥8 tower leg satisfies additional GENHN supplier law.
> CONSUMED BY: GENIND at n≥8, in addition to HYP.81 and [GENIND-H].
> CLASS: hypothesis-box
> PROPOSED DISPOSITION: CARRY.

### 1.2 The source statements

**THEOREM HE3.A** (the stage-σ recursion; `EFF.HE3.16`, statement verbatim at
`HE3_PROOF_2026-08-08.md` 312–331): at any composite-stage genre G, any DECIDED stage
leaf ℓ with stage type τ_stage(ℓ) = {(e_s⁽ⁱ⁾, f_s⁽ⁱ⁾)}_i, any lift f with disc(f) ≠ 0:
f factors over O into exactly k monic irreducibles, in bijection with τ_stage(ℓ), the
i-th of degree D′·e_s⁽ⁱ⁾f_s⁽ⁱ⁾ with

    e = e₁·e_s⁽ⁱ⁾ ,  f = f₁·f_s⁽ⁱ⁾ ,

i.e. **the σ-decision at a multiplicity-μ stage is the σ-decision at DEGREE μ over the
stage ring R, transported by the multiplicative re-basing (e, f) ↦ (e₁e, f₁f).**
Suppliers beyond the pins: HE3-1 (resultant identity), HE3-2 (recentering), HE3-3
(Ψ-inversion), HE3-4 (residue peel + unramified base change, ramified branch (ii) BOXED
= HE3-BOX-6), and HE3.A itself at inner multiplicities μ′ ≤ μ/2 (stage-CS events only).

**COROLLARY HE3.B** (`EFF.HE3.17`): [GENHN-HE(μ)] for every μ ≥ 2; μ ≤ 3 UNCONDITIONAL
("no assumed hypothesis inside this note's mathematics at μ ≤ 3") because μ ≤ 3 is
**composite-stage-free** (GENIND.A(IV): a stage-CS event needs e₁′f₁′ ≥ 2, μ′ ≥ 2,
e₁′f₁′μ′ ≤ μ, hence μ ≥ 4; strict descent μ′ ≤ μ/2) and branch (ii) is unreachable at
μ ≤ 3 (needs a side with ℓ ≥ 2, d ≥ 2, hence length ℓd ≥ 4 > 3). At μ ≥ 4 the single
reservation is HE3-BOX-6 branch (ii) (= HYP.143). The `n ≤ 7` range uses R8-3's LEMMA
HE3-4D1 (the D′ = 1 linear-key case is direct, no base change) so that the conditional
region needs D′ ≥ 2 AND μ ≥ 4, i.e. n = D′μ ≥ 8.

**The box row** (`EFF.GENHN.40`, GENHN's own record): "[GENHN-HE(μ ≥ 3)] (THE box; first
live n = 6)" — open on GENHN's side; HE3's discharge at μ ≤ 3 never landed as a GENHN
append (OPEN-CALL 6). The ledger's v3 scope split adjudicates: μ ≤ 3 unconditional, μ ≥ 4
rides HYP.143.

**The tower law** (HYP.82): CHAP-C trap C-H4 — "[GENHN-TOW-1] ('seven items under six
numerals' [F8]) is load-bearing at n ≥ 8 ONLY, and this chapter transcribes exactly the
items that have proofs": items (1) GENTOW-1 §6, (2) GENTOW-2 §6, (3) GENTOW-3 §8,
(4) GENTOW-4 §8, (5) GENTOW-5 §6 — PROVED; (6)(α) iterated depth-≥3 key composition —
THEOREM GENTOW5-A at depth 3 only (first live n = 16), depth ≥ 4 NOT claimed;
(6)(β) depth-3 node-floor rider — discharged into item (1). NODE C.93 makes the census
formal: threshold arithmetic `n = D_r·μ_r ≥ 2^{r+1}` (depth 2 first lives at n ≥ 8,
depth 3 at 16, depth 4 at 32 — S4 witness exactly minimal), Lean signature
`tower_first_live` signed at A-C.1 (`leanspec/Leanspec/ChapC.lean:3084`, currently an
axiom-signature) + the `C93Census` #check block.

**The ownership finding** (CHAP-I §3.7 row HYP.81 + item O-1, verbatim): "at μ = 3
(first-live n = 6, 7) the corpus proof is UNCONDITIONAL (THEOREM HE3.A) but has **no
transcription owner** — orchestrator item O-1 (honesty I-11(i))"; candidate homes "a
chapter-B appendix (HE3 is B's note) or a chapter-E instance section" (I §8: O-1 "book
the transcription … cheap relative to its Display-A weight"). Chapter E's trap E-3
forbids an E-side PROOF ("a fleet agent reaching for a μ ≥ 3 σ-decision has left the
chapter" — E carries `hσ₃` fields or returns BLOCKED: HYP.81); chapter I NODE I.06
(`GenhnHEAt`, stub) awaits the O-1 resolution by name.

### 1.3 Step decomposition

**HYP.81** (the μ = 3 law and its residue):

* **81-S1** (arith): the μ = 3 stage types are EXACTLY five: {(3,1)}, {(1,3)},
  {(1,1),(2,1)}, {(1,1),(1,2)}, {(1,1),(1,1),(1,1)} — the multisets of pairs with
  Σ e_s f_s = 3.
* **81-S2** (analytic core, corpus THEOREM HE3.A §S3–S6): at a decided μ = 3 leaf,
  σ(f) = {(e₁e_s, f₁f_s)}. Certification adds the four machine legs the corpus record
  itself names as missing: (a) embedded n = 7 rows (HE3-BOX-4b/source-defect-9: "no
  embedded n = 7 row" anywhere in HE3's battery); (b) equal-characteristic μ = 3 rows
  (HE3-BOX-4b: delivered coverage was ℤ_p only); (c) an f₁ ≥ 2 frame at D′ = 4 (all
  prior f₁ ≥ 2 rows sat at D′ = 2); (d) an h ≥ 2 frame (all prior μ = 3 rows sat at
  h = 1). Attacks: the defeat equations (a factor with e < e₁e_s or f < f₁f_s at a
  decided leaf) + dictionary flips as planted mutants.
* **81-S3** (arith): Σᵢ (e₁e_s⁽ⁱ⁾)(f₁f_s⁽ⁱ⁾) = D′·μ — the forcing chain's tightness.
* **81-S4** (arith): no stage-CS event fits inside μ ≤ 3 (GENIND.A(IV) arithmetic).
* **81-S5** (arith): branch (ii) needs ℓ ≥ 2 ∧ d ≥ 2 ⟹ side length ℓd ≥ 4 > 3.
* **81-S6** (arith): composite stage (D′ = e₁f₁ ≥ 2, `GenreDatum.hkey`) ∧ μ = 3 ⟹
  n = D′μ ≥ 6; the n = 7 slice is embedded (6 + 1, GENIND-3 Hensel split); μ ≥ 4 ∧
  D′ ≥ 2 ⟹ n ≥ 8. The D′ = 1 leg (LEMMA HE3-4D1) is outside `GenreDatum`'s grammar
  (H.01: e₁f₁ ≥ 2 "else the event is order-1 α/β") — scope note at the landing.
* **81-S7** (consistency): the transport at μ = 2 reproduces H.73's `stageSigma`
  verbatim (ram ↦ {(2e₁,f₁)}, twoSided ↦ {(e₁,f₁)²}, inert ↦ {(e₁,2f₁)}) — HE3's
  "GENHN.C is re-derived as the μ = 2 case of HE3.A, so no circularity", transcribed.
* **81-S8** (residue): μ ≥ 4 = HYP.143's territory. No work here beyond restating the
  narrowed residue.

**HYP.82** (the tower supplier law):

* **82-S1** (arith): a depth-r tower with live top μ_r ≥ 2 and proper levels lᵢ ≥ 2 has
  n = D_r·μ_r ≥ 2^{r+1}, and the bound is SHARP (all lᵢ = 2, μ_r = 2). Hence depth 2
  first lives at n = 8, depth 3 at 16, depth 4 at 32.
* **82-S2** (mechanical): the census disposition of C-H4/C.93 re-verified item-by-item
  against committed CHAP-C nodes and leanspec signature names.
* **82-S3** (residue): the open remainder is exactly the n ≥ 8 box family
  (HYP.67–71/78–80/142/143/144-BOX-2); verify no member is consulted below n = 8.

---

## §2. CERTIFICATIONS (script `verification/openmath/om7_cert.py`; committed artifact
`om7_cert_output.txt` — **VERDICT GREEN, 97 rows, 0 violations, 6/6 planted teeth fired**)

Design targets: the FOUR machine legs the corpus record itself names as missing at HEAD —
(a) no embedded n = 7 row anywhere in HE3's battery (EFF.HE3 source defect 9 / HE3-BOX-4b's
"no embedded n = 7 row"); (b) delivered μ = 3 coverage ℤ_p ONLY (HE3-BOX-4b); (c) every
f₁ ≥ 2 row at D′ = 2 (pe1 leg B); (d) every μ = 3 row at h = 1.

### 2.1 LEG A — the HYP.81 arithmetic, exhaustively (steps 81-S1/S3/S4/S5/S6)
* A1 five-type exhaustiveness: enumeration over all multisets of positive pairs with
  Σef = 3 returns EXACTLY the five types. ✓
* A2 degree conservation Σ(e₁e_s)(f₁f_s) = 3e₁f₁ on the 36-point (e₁,f₁) grid × 5 types:
  0 bad. ✓
* A3 stage-CS infeasibility at μ ≤ 3: 0 solutions of {e′f′ ≥ 2, μ′ ≥ 2, e′f′μ′ ≤ 3};
  first feasible μ = 4 exactly. ✓ (The constructed-counterexample attack on 81-S4: the
  defeat system is INFEASIBLE — infeasibility is the lemma.)
* A4 branch-(ii) unreachability: 0 solutions of {ℓ ≥ 2, d ≥ 2, ℓd ≤ 3}. ✓
* A5 first-live: min D′·3 over D′ ≥ 2 is 6 (attained); min D′μ over μ ≥ 4, D′ ≥ 2 is 8
  (attained). ✓

### 2.2 LEG B — ℤ_p rows at (2,1,3;1), p ∈ {2,3,5}, PARI oracle + THE EMBEDDED n = 7 ROWS
All five stage types constructed in stage coordinates, re-read by this unit's fresh reader
(reader type must equal intended type — a mismatch is a violation), then PARI
factorpadic-200 + idealprimedec (the pinned w12 GP_FUN convention). 15 sextic rows ✓ 0 bad.
**Embedded rows (the first in the HE3 orbit)**: member × (x − c) for c ∈ {1, 1+p} (the
Hensel-split sibling) — PARI σ = block-dictionary ∪ {(1,1)} on ALL 30 rows ✓; boundary
probe c = p (sibling at positive valuation, OUTSIDE GENIND-3's unit-distance premise):
the polygon still separates, σ = block ∪ {(1,1)} on all 15 probe rows (recorded as probes,
not as certification of the extraction premise). Teeth: T-FLIP-B (flipped dictionary caught
6/6 on the (3,1)/(1,3) rows), T-SIB (block-only prediction caught on every n = 7 row).

### 2.3 LEG C — equal characteristic F_q[[t]], q ∈ {2,3} (HE3-BOX-4b's gap): construction oracle
Genre (q; 2,1,3; 1); q = 3 key x² − t; q = 2 key x² + tx + t (x² − t is INSEPARABLE in
char 2 — disc ≠ 0 is HE3.A's standing hypothesis, so the Artin–Schreier-side separable key
is the honest frame; the corpus's own equal-char rows dodged the same way). All five types,
members = explicit products of factors with ELEMENTARY certificates (Eisenstein slope;
the exact identity block = t^kG(Φ′/t^m) with G irreducible over F_q ⟹ the factor's residue
field contains F_{q^{deg G}}; value-group forcing v(Φ′(ξ)) = 7/6 resp. 5/4 from the exact
relations Φ′(ξ)³ = t³ξ resp. Φ′(ξ)² = t²ξ). Programmatic checks per member: separability
(pseudo-Euclid gcd over F_q[t] — verified to FAIL on a planted square), fresh stage read =
intended type, dictionary = construction σ. 10 rows ✓ 0 bad.

### 2.4 LEG D — ℤ_3 at D′ = 4, f₁ = 2 (key x⁴ + 9, degree-12 members): the first f₁ ≥ 2
frame off D′ = 2, PARI oracle. Residual fields F_9 (genuine F_9 residual coefficients used:
the (1,1)+(1,2) row's quadratic residual is Z² − (1+i), irreducible over F_9 — an F_3
quadratic would SPLIT over F_9). All five types ✓ 0 bad, including σ = {(2,6)} (one
degree-12 factor, e = 2, f = 6) and {(6,2)}. Teeth: T-FLIP-D (2/2 caught); T-READ — the
OFF-NODE attack row Φ′³ + 9x²Φ′ + 3⁵ (entry floors violated) is REJECTED by the reader, and
PARI gives σ = {(2,1),(2,2),(3,2)} — outside the genre's entire σ-menu (odd e = 3 block):
the node floor fences REAL objects, the pe1-A2 finding reproduced at a fresh frame.

### 2.5 LEG E — ℤ_p at h = 3 (key x² − p³), p ∈ {3,5}, PARI oracle
(h = 2 is excluded by `gcd(h, e₁) = 1`; h = 3 is the first non-minimal height ever run at
μ = 3.) All five types at both primes: 10 rows ✓ 0 bad. Teeth: T-FLIP-E (4/4 caught).

### 2.6 LEG F — the HYP.82 threshold arithmetic (step 82-S1)
* F1 exhaustive: r ≤ 6, l_i ∈ {2..5}, μ_r ∈ {2..6} — 27,300 tuples, 0 violations of
  2^{r+1} ≤ D·μ_r. ✓
* F2 sharpness: the all-2 tower with μ_r = 2 attains equality at every depth. ✓ Tooth
  T-TOW: the strengthened bound 2^{r+2} FAILS on the witness (the certified bound is tight,
  not slack). ✓
* F3 depth first-live table {1: 4, 2: 8, 3: 16, 4: 32} — matches C.93's statement. ✓
* F4 the GENTOW5 S4 witness chain u_{k+1} = 4u_k + 1: (5, 21, 85, 341) = (4^{k+2}−1)/3
  recomputed exactly; n = 2⁵ = 32 minimal at depth 4. ✓

### 2.7 The census disposition re-verification (step 82-S2, mechanical, at HEAD)
C-H4's item table re-read against committed CHAP-C: items (1) GENTOW-1 §6, (2) GENTOW-2 §6,
(3) GENTOW-3 §8, (4) GENTOW-4 §8, (5) GENTOW-5 §6 — PROVED-in-blueprint with scope fences
stated on the nodes; (6)(α) THEOREM GENTOW5-A at depth 3 only (first live n = 16), depth ≥ 4
claimed by NO node; (6)(β) discharged into item (1). The `C93Census` #check suite exists in
`leanspec/Leanspec/ChapC.lean` (signed A-C.1) over the named items. **No-leak check**: every
member of the open remainder (HYP.67–71/78–80/142/143/144-BOX-2) is explicitly scoped
`n ≥ 8` in CHAP-I's §3 table (verified row-by-row this unit) — nothing in HYP.82's residue
is consulted below n = 8.

---

## §3. STATUSES AND RESIDUES

### 3.1 HYP.81 `[GENHN-HE(μ ≥ 3)]`

| step | status |
|---|---|
| 81-S1 five-type exhaustiveness | **PROVED** (Lean `stageType3_complete`, multiset induction; cert LEG A1) |
| 81-S2 the μ = 3 transport dictionary | **PROVED-IN-CORPUS (THEOREM HE3.A §S3–S6), transcription LANDED at the H.73 standard** — dictionary/transport/arithmetic in Lean; the σ-decision analytics carried by teeth (HE-SIG 947 + om7_cert 97, four new geographies, all GREEN). NOT re-proved here and NOT claimed machine-checked: the analytic decision content remains a corpus proof (grade per HE3's own record), exactly as H.73's μ = 2 decision does |
| 81-S3 degree conservation | **PROVED** (Lean `stageSigma3_degree`, `heTransport_degree`) |
| 81-S4 μ ≤ 3 composite-stage-free | **PROVED** (Lean `no_stageCS_below_four`/`composite_stage_free_mu3` + `stageCS_strict_descent`; attack A3 infeasible) |
| 81-S5 branch-(ii) unreachability | **PROVED** (Lean `branch_ii_needs_mu_four`; attack A4 infeasible) |
| 81-S6 first-live n = 6, 7 | **PROVED** (Lean `mu3_first_live` sharp at `genreE3`, `mu4_lives_at_eight`; the n = 7 slice = embedded 6+1, now MACHINE-TESTED for the first time — LEG B's 30 embedded rows) |
| 81-S7 μ = 2 consistency (no circularity) | **PROVED** (Lean `stageSigma_eq_heTransport`: H.73's dictionary IS the transport's μ = 2 shadow) |
| 81-S8 the μ ≥ 4 residue | **CARRY** — HYP.143 (HE3-BOX-6 branch (ii)), OM-10's family; PROOF-ONLY there (no machine leg exists at μ ≥ 4, per HE3-BOX-3, unchanged) |

**Row verdict: CARRY, μ = 3 slice OWNED + newly toothed.** The conjunct's residue after
this unit, exactly: (i) the μ ≥ 4 supplier (HYP.143, n ≥ 8); (ii) the analytic μ = 3
decision content remains corpus-side at HE3's own grade — what changed is that it now has
a transcription owner, a consistency theorem tying it to the landed μ = 2 dictionary, and
four decorrelated machine geographies where it previously had recorded coverage gaps.

### 3.2 HYP.82 `[GENHN-TOW-1]`

| step | status |
|---|---|
| 82-S1 threshold arithmetic | **PROVED** (Lean `tower_first_live` at the A-C.1-signed signature VERBATIM + `tower_first_live_sharp`; cert LEG F 27,300/0) |
| 82-S2 census disposition | **CERTIFIED** (mechanical re-verification at HEAD, §2.7) |
| 82-S3 the n ≥ 8 remainder | **CARRY** — the box family, OM-10's charge; verified no-leak below n = 8 |

**Row verdict: CARRY, narrowed** — the census's arithmetic node is now a Lean theorem; the
residue is exactly the named box family; no conjunct added or discharged.

### 3.3 Effect on chapter E's stub gate (the charter question)

The E-side BLOCKED-HYP.81 fields **carry, with the block's μ = 3 half now CITABLE**: E's
trap E-3 stands unchanged (E transports σ along the ladder, never decides μ ≥ 3 σ — a
node reaching for it has left the chapter), and nothing here discharges an `hσ₃` field.
What lifts is the OWNERSHIP hole behind the block: a μ = 3 consumer routed through chapter
I's hypothesis block now finds I.06's slice owned (H73w) instead of "UNASSIGNED (O-1)".
The μ ≥ 4 half of the block carries exactly as before (HYP.143). So: **the block neither
lifts nor becomes a cite — it carries, with its μ = 3 slice's supplier now transcribed.**

### 3.4 CITE-CANDIDATE adjudication (charter option, declined)

HE3.A's published shadow is the GMN/GN15 transport machinery (NS-3's order-r theorems of
the polygon/residual polynomial; NS-9's theorem of the product; e/f multiplicativity along
types — cf. [AGNPRW] Thm 5.2-v1/renumbered, the (e,f) formula). A B.42-standard gate-(b)
cite was CONSIDERED and is NOT drafted: unlike B.42 (where the corpus proof was found
unreachable), the μ = 3 law's corpus proof EXISTS and is adjudicated corpus-unconditional
by the ledger's v3 scope split — a cite would ADD an owner-signature obligation without
removing any conditionality, and the published statements would still need the
stage-ring/stage-coordinate dictionary (exactly HE3.A's content) to reach the box's form.
If the owner later wants the external anchor, NS-3/NS-9 are the rows to draft against;
recorded as an option, not an obligation.

---

## §4. LANDINGS AND THE OWNERSHIP DISPOSITION

**The O-1 ownership disposition (the charter's headline question): the μ = 3 law's
transcription home is an H-adjacent appendix file — `leanfinal/Uniformity/ChapH/H73w.lean`
— registered by CHAP-H AMENDMENT A-H.4, at the H09w/H89w precedent.** Adjudication of the
three candidate homes: an E-side node violates E-3's fence (E never proves/transcribes
μ ≥ 3 σ-decision content — a μ = 3 dictionary node in E is exactly the "fleet agent
reaching for a μ ≥ 3 σ-decision" the trap forbids); a C-side tower node is wrong-scoped
(C owns n ≥ 8 towers; the μ = 3 slice is the n = 6, 7 NON-tower case) and C's fleet is
mid-flight; the H-adjacent home is exactly right: the μ = 3 dictionary is H.73's landed
μ = 2 dictionary one μ up, typed against H.01/H.02/H.73/H.74's vocabulary, which reaches
completely (no new carrier was needed). CHAP-I's I.06 stub can bind its μ = 3 slice to
`stageSigma3`/`stageType3_complete` at resolution time.

Landed, all sorry-free, build green (8,565 jobs), footprints Lean-core or axiom-free:

1. `leanfinal/Uniformity/ChapH/H73w.lean` — `heTransport` (+ degree law), `StageLeaf3` /
   `stageType3` / `stageSigma3` (+ degree conservation), `stageType3_complete` (five-type
   exhaustiveness, multiset induction), `stageSigma_eq_heTransport` (the μ = 2 consistency
   /no-circularity theorem), `no_stageCS_below_four`, `composite_stage_free_mu3`,
   `stageCS_strict_descent`, `branch_ii_needs_mu_four`, `mu3_first_live`,
   `mu4_lives_at_eight`, `genreE3`, + a 12-example dictionary gate tied to the battery's
   PARI-confirmed rows (both gate genres: E3 and the D′ = 4 f₁ = 2 genre). Wired into the
   `ChapH.lean` roll-up.
2. `leanfinal/Uniformity/ChapC/C93.lean` — `tower_first_live` PROVED at the A-C.1-signed
   signature verbatim (`hr` kept though unused: signature fence) + `tower_first_live_sharp`.
   Deliberately NOT self-wired into `ChapC.lean` (to avoid racing the live fleet);
   CONFIRMED WIRED by the fleet's own layer-close-13 regeneration (commit `da716fae`,
   `ChapC.lean:23`) minutes later.
3. `verification/openmath/om7_cert.py` + committed output (GREEN).
4. Blueprint AMENDMENT A-H.4 (CHAP-H, dated append; §§0–17 + A-H.1/2/3 byte-unchanged).
5. CHAP-I addendum (O-1 discharge record; below).
6. Ledger ARC NOTEs on HYP.81 and HYP.82 (dispositions unchanged: CARRY).

**Honesty inventory (what is NOT claimed).** H73w does not machine-check THEOREM HE3.A's
analytic content; the μ = 3 σ-decision at real stage leaves remains a corpus proof at HE3's
own recorded grade, toothed by PARI/construction batteries. The D′ = 1 direct case
(HE3-4D1) is outside `GenreDatum`'s grammar and is NOT transcribed (order-1 layer
property). `GenhnHEAt` (I.06) and `GenhnTow1At` (I.07) remain stubs owned by chapter I.
Nothing at μ ≥ 4 moved. No statement was weakened anywhere; the one kept-though-unused
hypothesis (`hr` in C93) is kept BECAUSE of the signature fence.

---

## §5. LEDGER-EFFECT NOTES

* **HYP.81**: disposition CARRY unchanged; dated ARC NOTE added (μ = 3 slice owned at
  H73w + A-H.4; four new machine geographies closing EFF.HE3 defect 9 and HE3-BOX-4b's
  ℤ_p-only gap; μ ≥ 4 rides HYP.143 as before; E-3/GC-5 unchanged).
* **HYP.82**: disposition CARRY unchanged; dated ARC NOTE added (C.93(i) proved in Lean at
  the signed signature; census re-verified at HEAD; no-leak below n = 8 verified; residue
  = the box family, OM-10).
* **HYP.143**: untouched (OM-10). **HYP.24/36**: untouched. **HYP.148/139** (GENHN-BOX-2 /
  W-1 transport): untouched — this unit confirmed HE3's σ chain does NOT consume the W-9
  weld face (HE3 L1293 wording re-verified at merge level by the EFF compile), so no
  contact.
* **Chapter I bookkeeping**: O-1 DISCHARGED (addendum in CHAP-I); I.06's docstring owner
  reference can move from "UNASSIGNED (O-1)" to H73w at I's next edit pass (I.06's Lean
  stub itself is untouched — chapter I owns it); the §4 field-list row "GENHN-HE (n≥6)"
  stays on the open surface S3 (the conjunct carries; only its μ = 3 supplier gained an
  owner + teeth).
* **Chapter C bookkeeping**: C93.lean wiring into the fleet's `ChapC.lean` roll-up —
  RESOLVED: the fleet's layer-close-13 regeneration picked it up (commit `da716fae`);
  nothing owed.

## Commits

* `6b082ad7` — skeleton (outline, sources, step decomposition).
* `2cac6878` — certification battery GREEN (97 rows, 6/6 teeth).
* `7d5e643b` — Lean landings (H73w + C93), ChapH roll-up wired, build 8,565 green.
* (this commit) — A-H.4, CHAP-I addendum, ledger ARC NOTEs, note §§2–5.
