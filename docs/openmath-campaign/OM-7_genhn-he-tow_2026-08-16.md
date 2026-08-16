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

## §2. CERTIFICATIONS (scripts in `verification/openmath/om7_*`)

PENDING AT SKELETON COMMIT — filled per leg below, each from committed artifacts.

---

## §3. STATUSES AND RESIDUES

PENDING AT SKELETON COMMIT.

---

## §4. LANDINGS AND THE OWNERSHIP DISPOSITION

PENDING AT SKELETON COMMIT.

---

## §5. LEDGER-EFFECT NOTES

PENDING AT SKELETON COMMIT.
