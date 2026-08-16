# CHAPTER I — CAPSTONE AND CONDITIONALITY (the hypothesis ledger made formal)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **I = CAPSTONE AND
CONDITIONALITY** — the `HYP.*` rows of `spec/HYPOTHESIS_LEDGER.md`, the two `CAP:` targets, and
the three `COND:` orphans. **Census correction at HEAD:** the cut table's figure (154 = 149
HYP + 2 CAP + 3 COND) predates the v7 ledger fold; `spec/DAG_NODES.tsv` at HEAD carries
**159 chapter-I nodes = 154 HYP + 2 CAP + 3 COND** (HYP.150–154 harvested). This chapter
dispositions all **154 ledger rows** (v7: 35 CARRY · 18 MATH · 81 NODE · 4 MERGED · 13 CLOSED ·
2 OUT-OF-PATH-BY-POLICY · 1 IN-PROGRESS), both CAP targets, and all three COND orphans.
**Sources transcribed:** `spec/HYPOTHESIS_LEDGER.md` **v7 in full** (the rows ARE the spec —
GC-10 transcription grade, hard); Display A, **FROZEN at v5 (question 8)**; the landed
`leanfinal/Uniformity/Density/Statement.lean` API (`UniformityStatement` `:71`,
`UniformityStatementDecided` `:84`, `DrainageAt` `:118`, `UniformityStatement.ofDecided` `:124`,
`TotalMassOne` `:166`).
**Governing ruling:** `blueprint/CONVENTIONS_2026-08-15.md` **PART V (the owner ruling)** —
two owner gates only: (a) the main Lean statement (`UniformityStatement` and any change to it);
(b) every literature-cite import, signed per cite, owner's own paper never citable. **Every
hypothesis on the capstone path must terminate as a DISCHARGE NODE or a gate-(b) LITERATURE
CITE — no third category.** Part V item 2 replaces Brief I's per-conjunct sign-off plan;
CORE-SET rows about cite/def-faithfulness are gate-(b)-adjacent, the rest are absorbed into the
standing fresh-eyes audit cadence.
**Supplier chapters consumed:** **A** (landed kernel, by declaration name) · **G** (landed,
`ChapG/*`, by declaration name) · **B, C, E, H** (committed blueprint contracts, by node ID —
GC-13 tier (b)) · **D, F** (composing in parallel NOW — GC-13 tier (c) placeholders ONLY,
resolved in §9 LATE-BINDING at their freeze).
**Target repo:** `leanfinal/` (chapter I declares in `Uniformity.Density` directly — GC-6.2
assigns I **no sub-namespace**; new defs are capstone-conditionality carriers about landed
objects).
**Authored:** 2026-08-15, chapter-I composer (Fable arm, parallel-author fleet per CONVENTIONS
Part V). **CODEX CROSS-READ OWED** (§13 is the queue).

---

## 0. How to read this chapter

### 0.1 What this chapter is, and is not

Chapter I proves **no new mathematics**. Its product is the complete, honest accounting from
`UniformityStatement` down: (i) the **ledger disposition table** (§3) — every one of the 154
ledger rows terminated in exactly one of the five charge categories; (ii) the **capstone
hypothesis structure** (§4) — one field per Display-A conjunct at exactly ledger strength,
degree-indexed where the display is; (iii) the **COND resolutions** (§5) — the three orphan
conjuncts tied to rows and landed declarations; (iv) the **assembly theorems** (§6) — the
structure plus chapter products fired through landed `UniformityStatement.ofDecided` and
CHAP-H's `uniformity_of_package` (H.98); (v) the **CORE-SET audit ledger** (§7); (vi) the
**gates** (§8), including the AXCHK census artifact REVISION 2 plans. Sections 9–13 are the
late-binding block for the parallel chapters D/F and the closing contract sections.

### 0.2 The standing environments (chapter-prefixed per GC-6.3)

Chapter I's Lean nodes bind **per node** (GC-6.4). Two environments suffice:

**ENV-I1 — the statement arena** (the capstone targets' own environment; everything
quantifies internally over the complete-DVR bundle, exactly as `Statement.lean` does — no
section variables):

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial
```

**ENV-I2 — the census arena** (gate files; imports the chapter roll-ups named per gate; no
`variable`s, no public declarations).

**File layout (GC-6.1):** one file per Lean node, `leanfinal/Uniformity/ChapI/I<nn>.lean`,
module `Uniformity.ChapI.I<nn>`; roll-up `Uniformity/ChapI.lean`; `Uniformity.lean` gains one
line. Note-nodes (provenance/resolution/audit rows marked `[note]`) have **no Lean file** —
they live in this chapter and in the DAG only.

### 0.3 Names that already exist and must not be redefined

`UniformityStatement`, `UniformityStatementDecided`, `UniformityStatementPadic`,
`UniformityStatement.ofDecided/.toDecided/.toPadic`, `DrainageAt`, `TotalMassOne`,
`totalMassOne_of_drainage` (`Statement.lean`); `genuineDensity`, `decidedDensity`,
`UndecidedVanishes`, `CoveringMenu`, `genuineDensity_eq_of_drainage`,
`sum_genuineDensity_eq_one_of_drainage`, `one_le_sum_genuineDensity` (`GenuineDensity.lean`);
`drainage_one`, `totalMass_one` (`Gates.lean`); `drainage_two`, `totalMass_two`,
`coveringMenu_two`, `undecidedSeq`, `gapSeq_le_undecidedSeq` (`Drainage.lean`); chapter G's
landed layer (`ChapG/*`: `undecidedCount_two_eq`, `undecidedSeq_two_eq`,
`genuineDensity_two_exact`, `uniformityStatement_two`, `coveringMenu_three`,
`totalMass_three_of_drainage`, `one_le_sum_three`, `card_le_undecidedCount_three`,
`gate_two_padic_two_exact`, `gate_two_padic_three_exact`); the landed discharge set
(`Uniformity.Hensel.strongHensel`, `exists_monic_factorization_finset`,
`Uniformity.Density.typeOf_shift`, `typeOf_scaleRoots`, `typeOf_scale`,
`exists_anisotropic`). Committed contract names consumed by node ID: H.93–H.99 (`A1Cell`,
`A1Family`, `InductionPackage`, `package_two`, `package_three_of_rate`,
`drainage_of_package`, `uniformity_of_package`), E.24/E.39/E.40/E.44/E.61/E.62
(`HE7APackage`, `LadderSupply`, `LB1Carrier`, `MP1Carrier`, `LadderObligations`,
`VarthetaRes`, the `𝒲` socket), C.66/C.69/C.89/C.92/C.93/C.94/C.114.

### 0.4 The chapter's mathematical spine, in one page

The capstone chain, with today's status on every link:

```
UniformityStatement                                     -- CAP, gate (a); landed Prop
  ⇐ ofDecided (landed theorem)
      { UniformityStatementDecided                      -- the COUNT LAYER: open (A0/A1 per degree)
      ∧ ∀ n, DrainageAt n }                             -- the DRAINAGE LAYER: open at n ≥ 3
  ⇐ uniformity_of_package (H.98, contract)
      { UniformityStatementDecided
      ∧ ∀ n, InductionPackage n }                       -- menu + rate, per degree
  where InductionPackage 2 is UNCONDITIONAL (H.96 ⇐ chapter G, landed),
        InductionPackage 3 ⇐ hrate₃ (H.97's adopted form; = chapter G's named frontier),
        InductionPackage n (n ≥ 4) ⇐ THE INDUCTIVE STEP — **NO NODE ANYWHERE** (the
          GENIND.B fence, honesty item I-2): its content is Display A's hypothesis block.
```

Display A's hypothesis block is therefore the exact open surface, and this chapter's §4
structure is its Lean-facing transcription: `NS7` (a gate-(b) CITE, C.94), `LB1 ∧ MP1`
(E.39/E.40, open), the `HE7A` package (E.24), `∀ i ≥ 3 ((H-VARTHETA-RES)_i ∧ 𝒲_(≤i))`
(E.61/E.62 + C.89, open at `i ≥ 3`), `A0/A1/A2` (§4 carriers; A2 = landed `DrainageAt`),
`JD0-BOX-2` and `GENHN-BOX-2 (n≥6)` (chapter F carriers, late-binding), `(H-e)-window-pinning`
(H.89 at `e₁ = 2` + the carried general field), `[GENHN-HE(μ≥3)] (n≥6)` and `[GENHN-TOW-1]
(n≥8)` (carriers keyed to C.93), and the `AllOInterfaces` conjunct (a signed structural
disposition on the Lean side — §4.3). What fires **unconditionally today**: the `n = 1` and
`n = 2` slices (landed `drainage_one`/`drainage_two`, `totalMass_one`/`totalMass_two`,
chapter G's `uniformityStatement_two` and `genuineDensity_two_exact`).

---

## 1. HONESTY BLOCK (read before consuming any node)

**I-1 — NOTHING IN THIS CHAPTER PROVES THE CAPSTONE, AND NOBODY MAY SAY OTHERWISE.** Every
Lean theorem in §6 is bookkeeping: projections of the hypothesis structure and applications of
landed/committed assembly lemmas. The honest headline after this chapter lands in full is
exactly: *the uniformity theorem is proved at `n = 1` and `n = 2`, unconditionally; at every
`n ≥ 3` it is stated with its complete named conditionality, machine-checked to be exactly the
§4 structure plus the count layer.* Any progress claim must name the capstone, the instance,
the clause, and its conditionality (repo CLAUDE.md standing rule).

**I-2 — THE GENIND.B FENCE (inherited from CHAP-H §13, binding here).** H.98 is `GENIND.B`
**Step 5 only**: `P(n)` for all `n` ⟹ the capstone. The reduction's inductive step
(`(IH) + [GENIND-H(n)] ⟹ P(n)`) has **no node in any chapter** — its content is the event
grammar, the transports, and the stage clauses, i.e. exactly Display A's hypothesis block. **A
node claiming `GENIND.B`, here or anywhere, must be returned.** Chapter I represents the
inductive step as the OPEN-MATH terminal item T-1 of §3.9, never as a Lean node.

**I-3 — DISPLAY A ONLY.** Display B is HISTORICAL (v5, question 8) and is not cited as an
interface anywhere in this chapter. A conjunct without a dagger is NOT a discharged conjunct
(v5's own warning): the dagger count reached zero because the owner calls were made, and **all
the conjuncts are still there** (ledger, 0d-closure block, verbatim).

**I-4 — `TotalMassOne` IS THE DRAINAGE LEG IN DISGUISE.** Never counted as a separate
obligation (ledger synthesis note; `Statement.lean:163`'s own words). §6 carries it as a
corollary of the `a2` field through landed `totalMassOne_of_drainage`, and the disposition
table gives it no row of its own.

**I-5 — `HYP.137` IS DISCLOSURE-WITHOUT-PROMOTION.** The tail-σ-certification lemma
(`HEX3-BOX-1`) is visible in the ledger's n=3 perimeter clause and is **NOT** a Display-A
conjunct; it stays MATH in the ledger, conditions only the W-12.B corroboration aside, and no
§4 field mentions it. The chapter-G tripwire (`BLOCKED: HYP.137`) stands for any agent who
finds itself needing it.

**I-6 — `A0_n[disc≠0]` vs GC-9, THE RECORDED DIVERGENCE.** The corpus's `(A0)` is stated on
the `disc ≠ 0` locus; `leanfinal`'s `DecidedAt`/`typeOf` carry **no** such restriction (σ read
through `monicFactors`, total on monic polynomials — CHAP-B H-11 / D-4(a), globalized as
GC-9). §4's `A0` carrier states the corpus's conjunct faithfully at the decided-value level
and records that the Lean predicate is the strictly stronger every-lift one; the divergence is
FAITHFULNESS text on I.02, not a silent strengthening.

**I-7 — THE WELD-ZERO ARC LICENSES NOTHING.** `HYP.149` is IN-PROGRESS (clean-pass counter
**1 of 2**; the second, model-diverse pass is LAUNCHED and IN FLIGHT per append #56 — no
landing commit exists at HEAD). `HYP.148` stays CARRY and `HYP.139` stays MATH **at full
strength**; the §4 fields carry both, with the arc note attached. If the unit lands and passes,
the fields are REMOVED by the owner-gate-(a) amendment route (a Display-A conjunct change),
not by a fleet edit.

**I-8 — MERGED ROWS ARE REPRESENTED BY THEIR PARENT, ONCE.** `HYP.34` (=`HYP.24`),
`HYP.92` (under `HYP.36`), `HYP.93` (under `HYP.31`), `HYP.117` (consumer map for `HYP.63`):
one field or one table row each, never two (Brief I trap (vi)).

**I-9 — HOW "OPEN-MATH" SQUARES WITH PART V's "NO THIRD CATEGORY".** Part V demands every
carried hypothesis terminate as a discharge node or a gate-(b) cite. An OPEN-MATH row in §3 is
**not a third terminal category**: it is a discharge node whose proof does not exist yet — the
table names its owner chapter and the exact missing statement, so the terminal fate is fixed
(a future discharge node there, or a future gate-(b) cite if a published source is found —
Part V item 3 makes cite-vs-prove the fleet's choice). What Part V forbids is a hypothesis
with NO named termination; §3 has none.

**I-10 — THE `AllOInterfaces` CONJUNCT IS RECONCILED, NOT CARRIED AS A LEAN FIELD.** In Lean,
all-`O` generality is not an assumption but the statement form itself (every blueprint
signature quantifies over the bundle). §4.3 reconciles the conjunct's 14 names row by row
(GC-8 rider (iii): signed-vacuity rows must reconcile against Display A) — each name
terminates as ∀`O`-by-construction (transcribed), out-of-cone (consumer signed out), or
route-excluded (quarry/measure, Q7 policy). This is a **signed structural disposition**, the
chapter's one deliberate departure from field-per-conjunct, taken because a Lean field
asserting "the informal corpus's uses are characteristic-general" is not a statable Prop.

**I-11 — TWO SUPPLIER GAPS FOUND BY THIS CHAPTER'S TABLE, FLAGGED, NOT PAPERED OVER.**
(i) **`[GENHN-HE(μ≥3)]` at `μ = 3` (first-live `n = 6, 7`) is corpus-UNCONDITIONAL
(THEOREM HE3.A) but has NO transcription owner**: CHAP-B transcribes HE3.A's `e₁ = 1` shadow
only (B's SOURCE fields at `EFF.HE3.16`), CHAP-E explicitly BLOCKS the `μ ≥ 3` σ-decision
(`BLOCKED: HYP.81`), CHAP-C does not carry it. The conjunct's `μ = 3` slice is therefore a
bookable discharge node with no book — recorded as orchestrator item O-1 (§9.3). (ii) The
**`(H-e)-window-pinning` general supplier is only partially transcribed**: H.89 discharges the
consulted-height ledger at `e₁ = 2`; the general case lives in `StageInterface.hwin`
(a per-genre carried field), and `LEMMA GENHN-3`'s cap/consultation clauses (`EFF.GENHN.29`)
are consumed by committed H only at the (c) congruence bound (H.51). Orchestrator item O-2.

---

## 2. NODE INDEX

25 nodes: **10 def** (I.01–I.03, I.05–I.09 incl. two late-binding, I.10 structure, I.21) ·
**4 theorem** (I.15–I.18) · **3 gate** (I.23–I.25) · **8 note** (I.04, I.11–I.14, I.19, I.20,
I.22 — provenance/resolution/audit rows, no Lean files). Plus the §3 table (154 rows), the
§4.3 reconciliation, and the closing sections.

| § | nodes | content |
|---|---|---|
| 3 | (table) | THE LEDGER DISPOSITION TABLE: all 154 rows → {DISCHARGED-BY, DISCHARGE-NODE-HERE, CITE, OPEN-MATH, NOT-ON-CAPSTONE-PATH} |
| 4 | I.01–I.10 | the Display-A carriers and the capstone hypothesis structure `CapstoneHypotheses` |
| 4.3 | I.11 | the `AllOInterfaces` reconciliation (signed, row by row) |
| 5 | I.12–I.14 | the three COND resolutions (`A2_n`, `A1_n`, `(H-e)-window-pinning`) |
| 6 | I.15–I.20 | assembly: projections + `ofDecided`/H.98 firing + `TotalMassOne` + the stage display |
| 7 | I.21–I.22 | the `typeOf` faithfulness bridge statement + the CORE-SET audit ledger |
| 8 | I.23–I.25 | gates: the `n ≤ 2` unconditional re-fire, AXCHK, the cite-footprint gate |
| 9 | — | LATE-BINDING: chapters D and F (placeholders + the orchestrator resolution items) |
| 10 | — | DAG additions (`spec/DAG_BLUEPRINT_I.tsv`) |
| 11 | — | leanspec stub list (`LeanspecI` per GC-6.6) |
| 12 | — | TEETH dispositions (GC-8; I has no batteries — the gates are the teeth) |
| 13 | — | flagged for the codex cross-read |

Numbering note: I.04, I.11–I.14, I.19, I.20, I.22 are `[note]` nodes (no Lean file; DAG rows
only), and I.08/I.09 are late-binding placeholders that type directly into I.10's fields at
the F freeze (no separate files). Lean files: I01–I03, I05–I07, I10, I15–I18, I21, I23–I25
(**15 files**).

---

## 3. §3 — THE LEDGER DISPOSITION TABLE (all 154 rows)

**Vocabulary (the charge's five categories, exactly; two sub-flavours and reason codes for
honesty):**

* **DISCHARGED-BY `<name>`** — the discharge exists. Sub-flavours: **(landed)** = a live Lean
  declaration, verified in the tree; **(contract)** = a committed blueprint node (signed
  contract, Lean landing pending); **(structural)** = discharged by the formalization
  discipline itself (∀`O`/∀`q` statement forms, GC-9 every-lift), stated per row;
  **(late-binding: D/F)** = the discharging node belongs to a chapter composing in parallel —
  GC-13(c) placeholder, resolved in §9.
* **DISCHARGE-NODE-HERE `<I.nn / A-n>`** — chapter I composes it (§§4–8 Lean nodes, §5
  resolutions, §7 audit-ledger items).
* **CITE `<source / node>`** — a gate-(b) literature import (owner signs per cite).
* **OPEN-MATH** — the honest remaining mathematics: named, with **owner chapter** and the
  **exact missing statement**. Per honesty item I-9 this is a discharge node whose proof does
  not yet exist, never a licence to assume.
* **NOT-ON-CAPSTONE-PATH** — justified per row by a reason code:
  {NOT-REACHED (weld-face audit / ORPHAN-1), CLOSED (ledger-closed with reference),
  MERGED/AGGREGATE (represented elsewhere), POLICY (OUT-OF-PATH-BY-POLICY, Q7),
  PROCESS (grade/protocol/hygiene rows with no mathematical conjunct),
  FENCE (scope fences with no capstone leg), NO-CONSUMER (no blueprint node consumes it;
  re-entry condition named)}.

A row's ledger class/disposition (CARRY/MATH/NODE/…) is quoted as provenance; the CATEGORY
column is this chapter's terminal accounting under Part V. Dual-natured rows (a Display-A
conjunct with both a carrier here and open mathematics) are categorized **OPEN-MATH primary**
with the §4 carrier cross-referenced — the carrier is bookkeeping, not the discharge (I-1).

### 3.1 Capstone and low-degree interface (HYP.01–12)

| row | title (ledger) | category | disposition detail |
|---|---|---|---|
| HYP.01 | `typeOf` faithfulness [CORE-SET] | **DISCHARGE-NODE-HERE** I.21 + audit A-1 | the bridge STATEMENT is composed here (I.21 `TypeOfFaithful`, per GC-3: "I … owns the bridge statement"); the review is gate-(b)-adjacent def-faithfulness (Part V item 2), human, scheduled §7. NOT liftable by Q4; NOT discharged by any chapter. |
| HYP.02 | `eq_of_add_mul_eq` | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | "optional injectivity refinements … the n=3 consumer does not obviously need it" (row text); no Display-A conjunct, no blueprint DEPENDS names it. Re-entry: an ordinary fresh node in whichever chapter first needs uniqueness of the exact solve. |
| HYP.03 | n-fold Hensel factorization | **DISCHARGED-BY** (landed) `Uniformity.Hensel.exists_monic_factorization_finset` (`MultiHensel.lean:111`, CN-17) | ledger-stamped DISCHARGED 2026-08-14; Lean-core axioms. **Residual (not covered):** the order-0 leaf-law weld with `typeOf_mul` at every degree — booked at CHAP-B's B.63a/B.67 (contract), not here. |
| HYP.04 | strong Hensel inequality | **DISCHARGED-BY** (landed) `Uniformity.Hensel.strongHensel`/`strongHensel_addVal` (P5) | stronger than the row (no monicity, sharp distance, uniqueness); gate `gate_fires`. |
| HYP.05 | `typeOf` shift invariance | **DISCHARGED-BY** (landed) `Uniformity.Density.typeOf_shift` (P5) | unconditional, general DVR. |
| HYP.06 | `typeOf` scale invariance | **DISCHARGED-BY** (landed) `typeOf_scaleRoots` + `typeOf_scale` (P5) | the level-bookkeeping residual (classes mod `π^N ↦ π^(N−3m)`) is part of HYP.08's frontier, recorded there. |
| HYP.07 | nonintegral-slope `CertRam3` | **DISCHARGED-BY** (contract) B.42 + B.58 instance | the cubic nonintegral-slope branch is the one-side pure-residual leaf read at `(ℓ, m, d) = (3, 1, 1)`: `typeOf = ⟨{(3,1)}⟩` — B.58 is **unconditional at `d = 1`** (no `B-BOX-1`). Ledger class MATH → terminal fate: B's committed contract. |
| HYP.08 | cubic tail recurrence | **OPEN-MATH** — owner: the post-G `n = 3` frontier, typed at H.97 | exact missing statement: `∀ O [bundle], Induction.RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)` (H.97's `hrate` — chapter G honesty H-1's bridge from the `hex3U` arithmetic layer to `undecidedCount O 3 N`). The corpus's `u(N) ≤ q^(−N/2) + q^(−5)·u(N−3)` is its informal shadow. |
| HYP.09 | cubic triple-root drainage | **OPEN-MATH** — same frontier | exact missing statement: `DrainageAt 3`; follows from HYP.08's rate via H.97 + H.98 step 1 (`RateSpecies ⟹ undecidedSeq → 0 ⟹ UndecidedVanishes`). Depends on the landed P5 set (HYP.04–06, discharged) — the remaining gap is the rate, nothing else. |
| HYP.10 | exactly five cubic splitting types | **DISCHARGED-BY** (landed) chapter G: the five-type enumeration + `coveringMenu_three` (`ChapG/G54.lean`) | Lean-core; the ledger's LOW-CONFIDENCE flag is resolved by the landed proof. |
| HYP.11 | exact cubic densities | **OPEN-MATH** — owner: the `n = 3` value layer (post-G) | exact missing statement: per-type `genuineDensity O 3 σ = R_σ(q)` for the five types. Needs: HYP.08's rate (drainage), HYP.29 (exhaust bridge), HYP.28 (menu weights). G landed the sum law (`totalMass_three_of_drainage`) and the arithmetic layer; the per-type values are the residue. |
| HYP.12 | `(e,f)` ordering convention [CORE-SET] | **DISCHARGE-NODE-HERE** audit A-2 | reviewed as one clause of the core-set definitional audit (HYP.98), per the row's own Q4 answer; gate-(b)-adjacent (def-faithfulness). |

### 3.2 Citation and theorem-scope residue (HYP.13–18)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.13 | all-O citation swap | **DISCHARGED-BY** (contract) the chapter dictionary | in Lean there are no citations: NS-2/NS-4/NS-5/NS-6 became proof nodes (CHAP-B H-8's table: B.48+B.58, B.22/B.23, D-1+B.11–B.20, B.63/B.64); NS-7 and FGMN became the gate-(b) cites (C.94; C.66/C.92). *[A-F.10, 2026-08-16: NS-1 moved columns — B.42 is now itself a gate-(b) cite (`[cite:GN15 Thm 2.3]`, this file's 2026-08-16 addendum), after its proof route was machine-refuted; the row stays DISCHARGED-BY (contract) with the citation swap landing as a signed axiom instead of a proof node.]* The one name with no consumer is HYP.18's row. |
| HYP.14 | `NS-6` stopping criterion | **DISCHARGED-BY** (contract) B.65 — **PARTIAL: order 1 only** | B.65's own ⚠ and CHAP-B §11's edge `BP.B.65 → HYP.14` label the discharge partial; the order-`r` biconditional is chapter C's §5 trigger layer (level-jump trigger, `LEMMA HE6R1-1`). |
| HYP.15 | `NS-7` termination (CARRY-as-CITE) | **CITE** [AGNPRW] Thm 5.2 via **C.94** (gate (b)) | Q1's answered branch; §4's `ns7` field (I.01) is the carried hypothesis, discharged by C.94's signed axiom at stub time. HYP.17's numbering check is load-bearing on this cite (audit A-3, pre-signing). |
| HYP.16 | `NS-15` finite-depth bound | **NOT-ON-CAPSTONE-PATH** (CLOSED) | LAPSED per Q1/COR-13 (the cite branch has no explicit constant; the capstone needs finiteness only). Re-opening = re-opening F-2 + inheriting MQ-3. |
| HYP.17 | publisher-number verification [CORE-SET] | **DISCHARGE-NODE-HERE** audit A-3 | bounded lookup, gate-(b)-adjacent (it IS about a cite), scheduled BEFORE C.94/C.66/C.92 sign (§7). |
| HYP.18 | `AX-DEFECT` / Kuhlmann Thm 3.3 | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | no committed blueprint node consumes defectlessness at HEAD (checked across B/C/E/H DEPENDS). Re-entry condition: any future consumer imports it as a gate-(b) cite at the corrected scope (discreteness for defectlessness; separability fence). |

### 3.3 W12 and general induction (HYP.19–40)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.19 | `[W12-H]` | **NOT-ON-CAPSTONE-PATH** (AGGREGATE) | aggregate only, per its own disposition ("omit when children are expanded"); children HYP.20–24 are dispositioned individually. The W12 composite route itself is the priced-not-taken one (v4 audit). |
| HYP.20 | `[H-a]` / JC warrant | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED as a W12 leg) | the composite-stage route actually taken is GENIND's (GENH4.C/GENHN.C); the reachable GRTJC content is exactly the W-9 face = HYP.148's row, dispositioned there. Child DMULT-S is HYP.77 (out). |
| HYP.21 | `[H-b]` / JB row 12 | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-WFA-06) | no capstone-path consumer; dropped from Display A at v4; unreachable in the DAG (checked 7/7). |
| HYP.22 | `[H-c]` / J-D1 value package | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-WFA-07) | the whole package left Display A at v4; children accounted at HYP.74 (survives, re-parented), HYP.76/77 (out), HYP.83–86 (out, ORPHAN-1 cured). |
| HYP.23 | `[H-d]` residual censuses | **OPEN-MATH** at `μ ≥ 3` — owner: **C** (the count layer) | supplied at order 1/`μ = 2` by contracts C.114 (`HT`) + H §§5–7; exact missing statement at `μ ≥ 3`: the level-by-level residual-tower censuses — the HYP.139/142/144 family, each dispositioned below. |
| HYP.24 | `[H-e]` decision + window pinning | **OPEN-MATH** (carrier I.05; COND resolution I.14) | two halves. **Decision half:** order 1 = B.58/B.79–B.82 (contract); order ≥ 2 = C §10 certificates + E's ladder; `μ ≥ 3` = HYP.81. **Pinning half (the COND conjunct):** discharged at `e₁ = 2` by H.89 (contract); general case carried in `StageInterface.hwin` (H.09 field, per-genre); `LEMMA GENHN-3`'s cap clauses (`EFF.GENHN.29`) only partially transcribed — orchestrator item O-2 (honesty I-11(ii)). |
| HYP.25 | `A0` lift well-posedness | **OPEN-MATH** (carrier I.02) — owner: the count layer (H §7 laws + C/E suppliers) | Display-A conjunct `A0_n[disc≠0]`. Lean carrier: the degree-`n` decided-value slice (I.02), entering assembly as `UniformityStatementDecided` exactly as H.95's signature note routes it. GC-9 divergence recorded (honesty I-6). |
| HYP.26 | `A1` exact core menu | **OPEN-MATH** (carrier I.03; COND resolution I.13) — owner: H/C | Display-A conjunct `A1_n`. Formal tie: H.93/H.94 (`A1Cell` with the σ-label, closure under the STRENGTHENED predicate) + H.95's menu clause. Missing: the composite-stage menu construction (CS-1's content) with exact q-independent weights. |
| HYP.27 | `A2` drainage | **OPEN-MATH** at `n ≥ 3` (carrier = landed `DrainageAt`; COND resolution I.12) | `n = 1, 2` DISCHARGED (landed `drainage_one`/`drainage_two`; exact `n = 2` law G.36/G.37 — the ledger's v7 partial-discharge note). `n = 3`: HYP.08/09's frontier. `n ≥ 4`: `drainage_of_package` (H.98) ⇐ `InductionPackage n` ⇐ the inductive step (I-2 fence). |
| HYP.28 | `hMenu3` / `W12-BOX-2` | **OPEN-MATH** — owner: the `n = 3` value layer (post-G; orchestrator books the owner) | G.72 is the type-level shadow, NOT the discharge (G's own H-3); missing: the HMENU3 finite disjoint 53-family menu with exact weights. Consumed by HYP.11. |
| HYP.29 | `hExhaust3` / `W12-BOX-3` | **OPEN-MATH** — owner: chapter G's named frontier (H-1) | missing: THEOREM HEX3.A's Lean form (cubic menu exhausts the separable event up to null); G.71 names it as its explicit hypothesis. HYP.138's reader-reconciliation rides as a regression caveat, not a conjunct. |
| HYP.30 | `W12-BOX-4` / `DRAIN-N4` | **OPEN-MATH** — owner: H §10 (rate calculus) + C (count layer) | missing: the `n ≥ 4` rate — `InductionPackage n`'s rate clause, supplied through CS-1Q (HYP.36). Distinct from GENIND-BOX-4 (HYP.88). |
| HYP.31 | `[GENIND-H]` | **NOT-ON-CAPSTONE-PATH** (AGGREGATE) | aggregate only; children CS-1/2/3/EXACT (HYP.32–35), CS-1Q (HYP.36), GENHN-HE (HYP.81), TOW-1 (HYP.82). HYP.93 merges here. |
| HYP.32 | `CS-1` count-fibration | **OPEN-MATH** — owner: per-genre instances (H: standalone quartic genres; C: composed genres; embedded/mixed = `BLOCKED: HYP.36`-adjacent, obstructed per `EFF.GENIND.197/.199`) | missing: the exact count-fibration + product transport at every composite/mixed stage. GC-5's field table governs who instantiates. |
| HYP.33 | `CS-2` stage bracket | **OPEN-MATH** — owner: C (composed stages; `hbracket` field), numeric at order 1 by H.21 | missing: the MASS-normalized bracket at general genres (the ghost fibre `\|K\|^{c(μ)κ}` mandatory). |
| HYP.34 | `CS-3` | **NOT-ON-CAPSTONE-PATH** (MERGED → HYP.24) | exactly HYP.24 at the GENIND layer (ledger). One row, one accounting (I-8). |
| HYP.35 | `CS-EXACT` | **OPEN-MATH** — owner: C (the exact q-power-sum count laws; C.114 at order 1) | missing: exactness (identity, not bound) at composite stages. Deliberately NOT a `StageInterface` field — the `exactDrain` RE-PLAN protocol (GC-5) governs any node needing it. |
| HYP.36 | `(CS-1Q)` | **OPEN-MATH** — owner: per-genre (H's standalone-quartic instances are contract; C may add composed; embedded/mixed OPEN) | missing: `M_G ≥ e(N−1−H) − Δ_G` + the digit-loss rate for embedded/mixed affine ledgers. A node needing it for those genres returns `BLOCKED: HYP.36` (GC-5). |
| HYP.37 | `GENIND-BOX-2` | **DISCHARGED-BY** (contract) H §3 | the displayed schema expands faithfully = `GenreDatum`/`StageInterface` made formal (H.01/H.09); the presentation debt is paid by the schema layer's existence. |
| HYP.38 | `FGMN-MAIN` Lean declaration | **CITE** FGMN via **C.66** (+ C.92's chain battery; gate (b)) | the row's "declare faithfully and wire consumers" IS C.66's deliverable (exact Lean statement drafted at stub stage, faithfulness entry, Asvin signs). Consumers wired: C.67 → C.69 (the multiplicity tie), footprint-visible per `#print axioms` (gate I.25). |
| HYP.39 | `JD0-BAR` | **NOT-ON-CAPSTONE-PATH** (CLOSED-SIGNED, Q6) | machine grade signed as the bar; MQ-4 (optional codex pass) stays queued, gates nothing. |
| HYP.40 | single-w B″ transport | **DISCHARGED-BY** (contract) C §9 (GENTOW5 at acceptance scope, C.83–C.91) | the surviving work was the S12.1 scope re-verification; C transcribes at exactly acceptance scope, so the scope IS the node statements. Explicitly does NOT discharge HYP.63. |

### 3.4 T2 carrier obligations and grade (HYP.41–45)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.41 | `(LB1)` | **OPEN-MATH** — owner: the σ-ladder (T2/E) | Display-A conjunct. Carrier: E.39 `LB1Carrier` (contract, at exactly `EFF.T2.18` strength); enters §4 through E.24/E.44. No discharge exists in T2's effective text (E §6's adjudication, verbatim). Terminal fate: a future discharge unit or a gate-(b) cite — none is known today. |
| HYP.42 | `(MP1)` | **OPEN-MATH** — owner: the σ-ladder (T2/E) | Display-A conjunct. Carrier: E.40 `MP1Carrier`; the level-two analogue IS discharged (E.42), level one open ("No pin proves the recentered level-one key's orbit/(e,f) item"). |
| HYP.43 | `(SEC-RANK)` | **DISCHARGED-BY** (contract) E.12/E.35 | stipulated carrier data, "fences no read" (`EFF.T2.52`); lives as interface fields/hypotheses, NOT a chapter-I conjunct (E.44's explicit ruling). |
| HYP.44 | `(RISE)` | **DISCHARGED-BY** (contract) E's carrier layer | same treatment: a stipulated hypothesis field at refine steps, not a ledger obligation, not a conjunct. |
| HYP.45 | `(GRADE)` | **NOT-ON-CAPSTONE-PATH** (PROCESS) | a grade cap, not a mathematical conjunct; carried at E.22 for conditionality bookkeeping ("level-two chains consuming an HE3 pin through S1.8C remain capped"). Recorded in §12's teeth text. |

### 3.5 T1/T3/T5 supplier conditions (HYP.46–66)

Chapter D is composing in parallel: every "(late-binding: D)" below is a GC-13(c) placeholder
resolved at §9 when D freezes. The pattern for all of them: an ACCEPTED T-unit's supplier
interface / scope fence is transcribed at exactly EFF strength by a chapter-D node; the
generality content that is genuinely open at depth `i ≥ 3` does NOT hide in D's nodes — it
rides Display A's `∀ i ≥ 3` conjunct (HYP.57/63).

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.46 | canonical-letter scope | **DISCHARGED-BY** (late-binding: D) | T1's narrow carrier claim, level 2 unconditional; arbitrary depth needs `(H-JA-CONJ)_i` (HYP.53). |
| HYP.47 | `C3-ladder-multiplicativity` | **DISCHARGED-BY** (late-binding: D) | sitewise supplier; the level-general name is NOT inferred (row's own fence). |
| HYP.48 | `C3-slot-grade` | **DISCHARGED-BY** (late-binding: D) | sitewise grade identity. |
| HYP.49 | `C3-graded-scalar-covariance` | **DISCHARGED-BY** (late-binding: D) | sitewise read supplier; no all-homogeneous claim. |
| HYP.50 | `C3-zero-read` | **DISCHARGED-BY** (late-binding: D) | sitewise zero read. |
| HYP.51 | `C3-ladder-nonvanishing` | **DISCHARGED-BY** (late-binding: D) at `i = 2` | `i ≥ 3` rides the `∀ i ≥ 3` conjunct family (HYP.57/63) — D must NOT state a level-general form. |
| HYP.52 | `C3-read-codomain` | **DISCHARGED-BY** (late-binding: D) at `i = 2` | `i ≥ 3` rides the unverified level-general package = the `∀ i ≥ 3` conjunct; not inferred by T1. |
| HYP.53 | `(H-JA-CONJ_i)` | **DISCHARGED-BY** (late-binding: D) as a named hypothesis interface | T1 names no discharged supplier; deep-`i` content rides the `∀ i ≥ 3` conjunct. |
| HYP.54 | `(H-JA-RES-CONJ)` | **DISCHARGED-BY** (late-binding: D) | the source designation is UNDESIGNATED (EFF-T1 OPEN-CALL 2; HYP.141's register) — D's node must carry the undesignated-source disclosure, never invent a supplier. |
| HYP.55 | `(H-GENHN-CLEAR)` | **DISCHARGED-BY** (late-binding: D) | the cited designation is REFUTED (grep count 0; EFF-T1 OPEN-CALL 3); same disclosure discipline. `GENHN-LIFT` must not be invented as the clearance theorem. |
| HYP.56 | `(H-HETOW-LOCAL)` | **DISCHARGED-BY** (late-binding: D) as the interface; content supplied by C (HETOW is C's note) | complete local supplier interface — D states, C supplies via GC-13. |
| HYP.57 | `(H-VARTHETA-RES_i)` | **OPEN-MATH** — Display-A `∀ i ≥ 3` conjunct, first half | carrier: E.61 `VarthetaRes i` (contract); enters §4 via E.24's `vartheta` field. The T5-implication adjudication (does S11.2 §S2.1 imply it) is a technical unit, not an owner call — bookable by the orchestrator. |
| HYP.58 | integral K₁ lift range | **DISCHARGED-BY** (late-binding: D) | strict domain `M > D′h` retained in the D statement. |
| HYP.59 | `WELD-M-PKG` boundary | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED; pricing-only) | v4's own check: consumed on the spine as naming only (GENIND L1523); the narrow-interface disposition is correct as written and needs no node — F's out-of-cone census records it. |
| HYP.60 | raw/canonical equality | **DISCHARGED-BY** (late-binding: D) | the `z^ν = 1` (not `ν = 0`) correction carried in D's statements. |
| HYP.61 | dv_i codomain | **DISCHARGED-BY** (late-binding: D) | scope typing (`(e(μ_i)/e(μ_r))ℤ` generally); gates no C1–C7 conclusion. |
| HYP.62 | `T3-JOINT-OPEN` | **NOT-ON-CAPSTONE-PATH** (PROCESS) | realized-regression coverage only; not merged with HYP.135. |
| HYP.63 | `[GENTOW5-W(i)]` / `𝒲_(≤i)` | **OPEN-MATH** — Display-A `∀ i ≥ 3` conjunct, second half | carrier: C.89 `GENTOW5W`/`Wle` (contract: `i = 2` DISCHARGED via C.99/C.100; `i = 1` shape with the tie OPEN; `i ≥ 3` OPEN — "the honest-sorry analogue") + E.62's socket. HYP.117 is its consumer map (merged). |
| HYP.64 | `WFRAME OPEN-1` | **NOT-ON-CAPSTONE-PATH** (FENCE) | "no current capstone leg" (row); keeps the stronger `w_i`-formula claim out. |
| HYP.65 | `WFRAME OPEN-2` | **NOT-ON-CAPSTONE-PATH** (FENCE; the `i = 1` stratum is presently excluded) | the open `u₁ = w₁` tie is RECORDED at C.89(ii) as a separate named open tie; it becomes OPEN-MATH only if the `i = 1` stratum is ever consumed. |
| HYP.66 | `WFRAME OPEN-3` | **NOT-ON-CAPSTONE-PATH** (FENCE) | avatar-vs-intrinsic gap, measured to GAP at LW3 (HYP.145's fence); preserved by C §10's descriptive-status discipline. |

### 3.6 T4 boxes and tightness suspects (HYP.67–80)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.67 | `GENTOW6-BOX-1` | **OPEN-MATH** — owner: C §9's exact-scope boxes; live at `n ≥ 8` ONLY | missing: `μ₂ ≥ 3` attainment classification incl. the `f₁ ≥ 2` compound face (BOX-1 is CLOSED at `f₁ = 1` in the source). Reachability: a tower-leg residue under HYP.82's census (C.93), never consulted below `n = 8`. |
| HYP.68 | `GENTOW6-BOX-2` | **OPEN-MATH** — owner: C (count layer); `n ≥ 8` family | missing: the count LEDGER at partial sides (open already at FULL sides); sits beside HYP.144's BOX-2. |
| HYP.69 | `GENTOW6-BOX-3` | **OPEN-MATH** — owner: C; `n ≥ 8` family | missing: exhaustive regime-3 (entry-driven / non-top-overflow) classification. |
| HYP.70 | `GENTOW6-BOX-4` residue | **OPEN-MATH** — owner: C; `n ≥ 8` family | missing: the theorem-grade all-`f₁ ≥ 2` widening (the battery discharge at four x-ful rows stays distinct, per the row). |
| HYP.71 | `GENTOW3-BOX-1` | **OPEN-MATH** — owner: C; `n ≥ 8` family | missing: genre-general nonvanishing / battery witnesses for entry-driven overflow with self-power below `D′`. HYP.112's fence applies to any candidate (a candidate implies neither `ω_j ≠ 0`, touched `j`, nor attainment). |
| HYP.72 | disc≠0 downstream fence | **DISCHARGED-BY** (structural) GC-9 | the every-lift/`monicFactors` discipline threads the fence by construction: no blueprint σ-consumer imports `disc ≠ 0` silently — where the corpus's σ was root-read, the Lean statement is the strictly stronger total one, flagged per node (B H-11 template). |
| HYP.73 | `WELD-FACE-AUDIT` | **NOT-ON-CAPSTONE-PATH** (CLOSED) | executed 2026-08-13; retained as the closing reference. |
| HYP.74 | `JD0-BOX-2` | **OPEN-MATH** — Display-A conjunct; owner: **F** (late-binding) | carrier: F §4's `GaugeFormPerimeter`/`JD0Box2` (`EFF.JD0.05` [supplied-by: chapter F]). The discharge is a bounded FOLD, not a theorem: per-site strike ledger (each of the seven cone sites' gauge is an explicit z-power unit character verified in-note). Grade bar SIGNED (HYP.39); the general unit-character lemma is NOT needed (row's own fence). |
| HYP.75 | `JB-NOLEG` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-WFA-03) | all four JB rows out; GRTJB-internal frontier only. |
| HYP.76 | `W2-VALUE` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-WFA-04) | GRTW2 reaches the spine only through display bookkeeping (the v4-corrected count: two non-consuming W12 mentions). |
| HYP.77 | `DMULT-S` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-WFA-05) | W-9 rides the citable (DMULT-w) tier (PDF-VERIFIED); the structural clauses stand without (DMULT-s). |
| HYP.78 | `S8.1-MEMBER` | **OPEN-MATH** — owner: C's compound/`μ ≥ 3` family; live at `n ≥ 8` | missing: complete membership classification of above-floor divergence cases; feeds the compound drainage leg only (the value leg is out of cone). |
| HYP.79 | `P-BINOM` | **OPEN-MATH** — rider on HYP.78; `n ≥ 8` | missing: floor attainment + lower-coordinate classification when `p ∣ binom(m,2)`. |
| HYP.80 | `COMPOUND-6.5′` | **OPEN-MATH** — owner: C; `n ≥ 8` compound family | its `[H-c]` parentage is out of cone, but the content overlaps HYP.67's `f₁ ≥ 2, μ₂ ≥ 3` tower face (ledger dedup note), so it is conservatively kept in the `n ≥ 8` open family rather than signed out. |

### 3.7 Completeness additions from the adjudication (HYP.81–98)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.81 | `[GENHN-HE(μ ≥ 3)]` | **OPEN-MATH** — Display-A conjunct (`if n ≥ 6`); carrier I.06 | **scope split (v3), transcribed exactly:** at `μ = 3` (first-live `n = 6, 7`) the corpus proof is UNCONDITIONAL (THEOREM HE3.A) but has **no transcription owner** — orchestrator item O-1 (honesty I-11(i)); at `μ ≥ 4` (`n ≥ 8`) it rides the open HE3-BOX-6 ramified branch (HYP.143). Everyone else returns `BLOCKED: HYP.81` (E trap (iii), GC-5). |
| HYP.82 | `[GENHN-TOW-1]` | **OPEN-MATH** — Display-A conjunct (`if n ≥ 8`); carrier I.07 | census made formal at C.93 (contract): items (1)–(5)+(6)(β) are C theorems; (6)(α) depth 3 = C.90/C.91's scope; depth ≥ 4 claimed by no node. The open remainder = the `n ≥ 8` box family (HYP.67–71/78–80/143/144-BOX-2/142). |
| HYP.83 | `(VD-m)` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-ORPH-01) | ORPHAN-1 cured by independent verification; weld-internal frontier. |
| HYP.84 | `(C-coll)` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-ORPH-02) | ditto. |
| HYP.85 | `(R-coll)` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-ORPH-03) | ditto. |
| HYP.86 | `PERIM-μ` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED, COR-ORPH-04) | ditto; J-D0 names it first among the fences count-layer consumers need not carry. |
| HYP.87 | `GENIND-BOX-3` | **DISCHARGED-BY** (structural) | the all-prime-power/`d ≥ 2` scope worry ("rests on proof q-uniformity") dissolves in Lean: every blueprint signature quantifies over the full bundle (`∀ O`, all `q`), so the landed proofs ARE the q-uniformity. The battery's `d = 1`-prime-`q` limitation survives only as regression-scope disclosure (GC-8 rider (i), per owning chapter). |
| HYP.88 | `GENIND-BOX-4` | **OPEN-MATH** — owner: H §10 / C seam | missing: the simple-slice β-bookkeeping compression proved on EVERY route of the `n ≥ 4` drainage recursion (distinct from HYP.30, per the ledger's dedup note). |
| HYP.89 | `GENIND-BOX-5` | **NOT-ON-CAPSTONE-PATH** (PROCESS) | a grade cap ("clean count not started"); the blueprint program (chapters B–I) IS the clean count of the conditional structure — the row's content is superseded by the artifact set it asked for. |
| HYP.90 | `GENIND-BOX-6` | **NOT-ON-CAPSTONE-PATH** (PROCESS) | oracle-coverage disclosure (mixed-char only); the Lean statements cover equal characteristic by construction (`∀ O` includes `𝔽_q⟦t⟧`), and the oracle's scope stays a regression caveat in the owning chapters' teeth tables. |
| HYP.91 | `GENIND-5` / `OB-a…OB-d` | **DISCHARGE-NODE-HERE** audit A-7 | bounded representation check: the four displayed obstructions and their routing, verified against CHAP-H's committed text + `spec/DAG_BLUEPRINT_H.tsv` (OB-a = H.89's ledger + `hwin`; the §3 table is where the check is recorded). |
| HYP.92 | `ANNEX-LEMMA GENIND-C2Q` | **NOT-ON-CAPSTONE-PATH** (MERGED → HYP.36) | supplier node under CS-1Q. |
| HYP.93 | `GENIND-6` | **NOT-ON-CAPSTONE-PATH** (MERGED → HYP.31) | represented by [GENIND-H] and children. |
| HYP.94 | `UniformityStatement` signature | **NOT-ON-CAPSTONE-PATH** (CLOSED-SIGNED, Q3) | the three signed points verified at `Statement.lean:55–58`; any CHANGE to the statement is owner gate (a). |
| HYP.95 | Haar bridge | **NOT-ON-CAPSTONE-PATH** (CLOSED, Q5 — no Haar) | the capstone asserts a proportion limit; re-introducing Haar re-opens the row and owes measurability. |
| HYP.96 | `AX-CELLREC`/`AX-LEAF` | **NOT-ON-CAPSTONE-PATH** (POLICY, Q7) | quarantined in the quarry's measure route; `leanfinal` is Lean-core-only. Gate I.24/I.25 enforce mechanically. |
| HYP.97 | `RealInstanceAt.faithful` | **NOT-ON-CAPSTONE-PATH** (POLICY, Q7) | conditions the quarry only; still illegitimate to consume at theorem strength there. |
| HYP.98 | `DEFINITION-AUDIT` [CORE-SET] | **DISCHARGE-NODE-HERE** audit A-4 | the one place the human-review surface lives: the types, the uniformity theorem, the two densities, the cites, the changed definitions' faithfulness paragraphs. RECURRING (append #49 directive 2: fresh eyes at chapter milestones), scheduled §7; HYP.12 and HYP.111's definitional half ride inside it. |

### 3.8 T-chain riders, coverage debt, and the all-O block (HYP.99–135)

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.99 | T3/T5 frame staleness | **DISCHARGED-BY** (late-binding: D) | D transcribes from the EFF specs at HEAD (merged, correction-resolved), which is exactly the cross-note HEAD audit the row asked for; the `w_i ∈ K_i^×` gate rides D's statements. |
| HYP.100 | contradictory T5 sentence | **NOT-ON-CAPSTONE-PATH** (PROCESS) | corpus hygiene (stale L299 vs governing L616); the EFF-T5 spec already resolves the governing reading; strike/append stays an MQ-class action. |
| HYP.101 | HE7.A source suite | **DISCHARGED-BY** (contract) E §4 | the five clause families are `RungInterface`'s FIELDS and the five instance records are proved instances (E's §4); naming a carrier is insufficient — the instances supply ACCOUNT/RES-DEG/nonempty/exhaust/continuation each. |
| HYP.102 | `(MID-PEEL)` items 2–5 | **DISCHARGED-BY** (contract) E | per-instance discharge records; the level-2 analogue proved (E.42); item-1 master-proved in source. |
| HYP.103 | T2 S4.2 non-claims | **DISCHARGED-BY** (contract) E's honesty block + census | the twelve exclusions preserved as chapter-E fences (no E node claims a density law; §13's census lists the exclusions). |
| HYP.104 | `C3-lift-coefficient-space` | **DISCHARGED-BY** (late-binding: D) | independent site obligation (`deg k̂_t < deg Φ_i`) carried in D's key-formation statements. |
| HYP.105 | factor patterns need tower correctness | **DISCHARGE-NODE-HERE** I.21 + audit A-1 | the missing trust-boundary theorem is NAMED here: `TypeOfFaithful` (I.21) is the statement connecting residual factor patterns to splitting types; it rides the core-set audit next to HYP.01 (the row's own v5 placement). |
| HYP.106 | nonzero-digit lift contract | **DISCHARGED-BY** (late-binding: D) | zero-branch scope fence in D's statements. |
| HYP.107 | A2 binary carry | **DISCHARGED-BY** (late-binding: D) | the HETOW pin restricted to the stated binary-carry regime in D's A2 node. |
| HYP.108 | A6 provenance | **DISCHARGED-BY** (late-binding: D) | scalar read = HE6 F-1, lift = GENTOW6 S6.1 — provenance carried in D's SOURCE fields. |
| HYP.109 | T-unit grade caveats | **NOT-ON-CAPSTONE-PATH** (PROCESS) | grade bookkeeping; the blueprint consumes EFF statements, not grades. |
| HYP.110 | `W12-BOX-5` | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | `omCount` is the quarry's; the W-2/LIFTCORNER seam is recorded UNCONSUMED at F's out-of-cone census. |
| HYP.111 | `W12-BOX-7` (split at v5) | **DISCHARGE-NODE-HERE** audit A-5 (definitional half) · **NOT-ON-CAPSTONE-PATH** (lifted; deep-tail half) | the "decided" predicate's meaning is core (it is what `decidedDensity` counts) and rides A-4/A-5; the deep-tail TRP reconciliation is lifted by Q4 and cannot move `genuineDensity` at all (P4 narrowing, row text). |
| HYP.112 | T4 μ₂≥3 candidate fence | **DISCHARGED-BY** (late-binding: D) | the consumption ban carried in D's T4 statements; ALSO fences C's `n ≥ 8` boxes (noted at HYP.71). |
| HYP.113 | T4.2(c) exposure premise | **DISCHARGED-BY** (late-binding: D) | full-exposure premise displayed in the statement. |
| HYP.114 | T4.2(d) provenance exclusion | **DISCHARGED-BY** (late-binding: D) | exclusion carried. |
| HYP.115 | T4 fail-closed pins | **DISCHARGED-BY** (late-binding: D) | fail-closed behaviour is the transcription default (missing pin ⇒ no node). |
| HYP.116 | `GENTOW3-BOX-2` | **DISCHARGED-BY** (contract) C's teeth discipline | evidence-scope disclosure (`f₁ = 1, η = 1` only) carried as a GC-8 rider-(i) re-scoping row in C's disposition table. |
| HYP.117 | `(G5-COND)` ride list | **NOT-ON-CAPSTONE-PATH** (MERGED → HYP.63) | the consumer map. |
| HYP.118 | T3 narrowed delivery | **DISCHARGED-BY** (late-binding: D) | two absorptions + one non-instance, GENTOW-6.4 unabsorbed — D's scope text. |
| HYP.119 | HENSEL branch-(ii) residue | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | the landed `MultiHensel`/P5 set supersedes the trigger/count uses; determinacy stays unadjudicated as a corpus item with no blueprint consumer. Re-entry: an ordinary node if a consumer appears. |
| HYP.120 | eight-audit coverage debt | **NOT-ON-CAPSTONE-PATH** (AGGREGATE) | umbrella for HYP.121–134, each dispositioned below. |
| HYP.121 | `GENIND-1` all-O | **DISCHARGED-BY** (contract) H.93/H.94 | the closure lemma is `ℕ`-level (O-free) in chapter H's form; the all-O edge dissolves. |
| HYP.122 | `[RMG]` all-O | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | RMENGINE is an `EXT:` note (no 0a spec, outside the cut); the Lean route re-derives the reduction content fresh in B/C. Re-entry: any RMG import would be a new cut decision. |
| HYP.123 | `[ILN]†` all-O | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED except via HYP.148) | GRTJB/GRTJC consumers are out-of-cone; the one reachable GRT face's generality rides HYP.148's carrier statement (∀`O` by construction). |
| HYP.124 | `GRB` all-O | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | GRB_ORDER2 is `EXT:`; not consumed by the Lean route. |
| HYP.125 | `ITER-LAW` all-O | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | ITERLAWN is `EXT:`; ditto. |
| HYP.126 | `W-1/W-2/J-A/J-B` all-O | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED) | consumers are `[H-a]–[H-c]`, out of cone; the W-1 transport's own row is HYP.139 (live, dispositioned there). |
| HYP.127 | `DU lemma` all-O | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED) | "named in S7.1's pricing only". |
| HYP.128 | `W-10` all-O | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED) | census O-11, out of cone. |
| HYP.129 | `J-D0` all-O | **DISCHARGED-BY** (late-binding: F, structural) | the generality edge terminates in the ∀`O` form of F's `GaugeFormPerimeter` statement — in Lean the all-O claim IS the statement's binder. |
| HYP.130 | `L2core` all-O | **NOT-ON-CAPSTONE-PATH** (POLICY) | quarry-side (the `lean/` mirror of HUMAN_PROOF); `leanfinal` does not consume it. |
| HYP.131 | HUMAN_PROOF all-O | **NOT-ON-CAPSTONE-PATH** (POLICY) | same: the leanfinal capstone route is not HUMAN_PROOF's. |
| HYP.132 | local-integrals all-O | **NOT-ON-CAPSTONE-PATH** (POLICY — the explicit route exclusion the row demanded) | the measure route is quarantined (Q7); "removable only by explicit route exclusion" — Q7 IS that exclusion, recorded. |
| HYP.133 | `(CONV)=α⁻¹` bridge | **NOT-ON-CAPSTONE-PATH** (NO-CONSUMER) | `leanfinal` is monic-native (`Coeff O n N` counts monic classes); no projective-to-monic transfer node exists in any committed chapter. Re-entry: a bridge node if a projective object ever enters. |
| HYP.134 | GENHN count all-O | **DISCHARGED-BY** (contract) H §7 at `μ = 2` (∀`O` statements) | the `μ ≥ 3` half rides HYP.81/HYP.148 and is accounted there. |
| HYP.135 | `F4-JOINT` graded model | **NOT-ON-CAPSTONE-PATH** (PROCESS) | battery supply-model bookkeeping (kept separate from HYP.62); D's teeth table. |

### 3.9 v3/v4/v7 additions (HYP.136–154) and the terminal open item

| row | title | category | disposition detail |
|---|---|---|---|
| HYP.136 | `S-0` tripwire | **NOT-ON-CAPSTONE-PATH** (CLOSED) | GREEN post-campaign; retained as reference. |
| HYP.137 | `HEX3-BOX-1` tail-σ lemma | **NOT-ON-CAPSTONE-PATH** as a conjunct (disclosure-without-promotion, Q9) | **stays MATH in the ledger** — the lemma is real and unproved; its only live consumer is the W-12.B corroboration aside. NON-NODE everywhere (G H-2's tripwire `BLOCKED: HYP.137` stands; honesty I-5). |
| HYP.138 | N3_CHECK §6d HEX3 reconciliation | **NOT-ON-CAPSTONE-PATH** (PROCESS) | the two readers' counts measure different sets; until reconciled neither is citable as confirming/refuting HEX3.A — carried as a regression caveat on HYP.29's teeth, not a conjunct. |
| HYP.139 | `W-1` transport | **OPEN-MATH** — owner: F (carrier, late-binding) riding under HYP.148 | missing: the harness `(w, 𝑅) →` FGMN-objects transport (TR-3′-GEN, OPEN at general order); class MATH. Retired as a side effect IF WELD-ZERO lands and passes (I-7); until then full strength. |
| HYP.140 | `GENTOW5_WI` stale grade box | **NOT-ON-CAPSTONE-PATH** (PROCESS) | SOL row 18 (2026-08-12) is HEAD-of-record; strike/append is MQ-class hygiene. |
| HYP.141 | shard source-designation refutations | **NOT-ON-CAPSTONE-PATH** (PROCESS) | the register discipline ("grep-verifiable designation or marked undesignated") is inherited by D's SOURCE fields (HYP.54/55 rows above). |
| HYP.142 | `GENHN-ERR-1` dual disposition | **OPEN-MATH** — owner: the H/C seam at `f₁ ≥ 2` count laws | missing: reconcile the two records (GENHN L2593 settled vs HE6R1 L926 owes-a-lemma) and say which governs; if HE6R1's reading governs, the `f₁ ≥ 2` count argument on the corrected region is a NEW lemma. Feeds the `n ≥ 8` leg (HYP.82) and the `μ ≥ 3` censuses (HYP.23). |
| HYP.143 | `HE3-BOX-6` ramified branch (ii) | **OPEN-MATH** — owner: C (GC-7's explicit-`O₂` rider; Brief C trap (ii)); live at `μ ≥ 4` / `n ≥ 8` | missing: test keys at non-integer dv heights (the higher-order Montes construction) OR an honest explicit-`O₂` base change under which `Φ′` irreducibility is re-established. Supplier-side under HYP.81; adds no conjunct. |
| HYP.144 | `GENTOW4-BOX-1/-2/-4` | **SPLIT**: BOX-1 **DISCHARGED-BY** (contract, cite-conditional) C.67 through C.66's FGMN axiom · BOX-2 **OPEN-MATH** (owner C; the partial-side COUNT layer, `n ≥ 8` family) · BOX-4 **NOT-ON-CAPSTONE-PATH** (PROCESS; a grade cap) | C.67's own header: "closes `GENTOW4-BOX-1` = `HYP.144`, cite-conditionally". |
| HYP.145 | GENTOW2 S6.1 rows 23–24 | **DISCHARGED-BY** (contract) C §10 | the descriptive fence + two-leg elevation debt preserved in C's dictionary-layer discipline (C-H10). |
| HYP.146 | `W11-BOX-1` | **NOT-ON-CAPSTONE-PATH** (NOT-REACHED as a route) | the general W-11 menu tie is a program the taken route (GENIND) supersedes; the `n = 2` instance is landed via chapter G. Stays MATH in the ledger as a corpus item. |
| HYP.147 | `exists_anisotropic` | **DISCHARGED-BY** (landed) `Uniformity.Density.exists_anisotropic` (`AnisotropicForms.lean:149`, CN-15) | residual (gate_bracket general-`O` integration; `exists_aniForm`/`exists_aniK` dedup) = MQ-5/MQ-6 class, not on the path. |
| HYP.148 | `GENHN-BOX-2` / W-9 face | **OPEN-MATH** — Display-A conjunct (`if n ≥ 6`); owner: F (carrier, late-binding: `EFF.GENHN.50` [supplied-by: chapter F]) | the ONE weld face inside a count law on the whole path. CARRY at full strength (WELD-ZERO 1-of-2, I-7); carries HYP.139 as sub-residue; compensating instrument GN-REFINE3 recorded. |
| HYP.149 | WELD-ZERO route | **NOT-ON-CAPSTONE-PATH** as an obligation (IN-PROGRESS route) | asserted by no accepted note; licenses nothing; if it lands + passes, HYP.148/139's fields are removed by the gate-(a) amendment route (I-7). |
| HYP.150 | EFF-HE6 OPEN-CALL 2, T2-closed | **NOT-ON-CAPSTONE-PATH** (CLOSED-FOR-T2) | residual (HE7/HE6R1 consumption vs A3 F-1/F-3/F-4) recorded at E §14 item 8 — an open LEDGER residual, not a capstone conjunct. |
| HYP.151 | A3 F-1 defect record | **NOT-ON-CAPSTONE-PATH** (CLOSED, historical) | zero live consumers of the false pre-A3 reading. |
| HYP.152 | consumption-not-citation protocol | **NOT-ON-CAPSTONE-PATH** (PROCESS) | standing protocol; no mathematics. |
| HYP.153 | compiler-invented-no-span rule | **NOT-ON-CAPSTONE-PATH** (PROCESS) | standing process rule. |
| HYP.154 | `LEMMA HE6-0` tenth-pin concern | **NOT-ON-CAPSTONE-PATH** (PROCESS — chapter-cut bookkeeping) | recorded FOR the B/C stub stages: a cut assembling HE6-adjacent material from T2's pins alone must source `LEMMA HE6-0` from HE6 itself. No pin owed. |

**T-1 (the terminal open item, no row number): THE INDUCTIVE STEP.** `(IH) + [GENIND-H(n)] ⟹
P(n)` at `n ≥ 4` — the content of Display A's hypothesis block as a single implication. **NO
NODE ANYWHERE** (honesty I-2, the GENIND.B fence). It is not a ledger row because it is not a
single hypothesis: it is the conjunction the whole block names, and its Lean-facing shadow is
exactly "supply `InductionPackage n` at every `n`" (H.98's `hp`). Recorded here so the table's
completeness claim is honest: closing every OPEN-MATH row above is NECESSARY for the capstone;
it becomes SUFFICIENT only through this step, whose formal composition is future work owned by
the orchestrator's post-blueprint program.

### 3.10 The CAP and COND nodes

| node | category | disposition detail |
|---|---|---|
| `CAP:UniformityStatement` | **landed target** (`Statement.lean:71`) | owner gate (a) guards any change. Consumed by I.16; fired unconditionally at `n ≤ 2` (gate I.23). |
| `CAP:UniformityStatementDecided` | **landed target** (`Statement.lean:84`) | the certified-form target; the count layer's assembly point (I.02/I.17). |
| `COND:A1_n` | **RESOLVED** at I.13 | = HYP.26's content; formal carrier H.93/H.94/H.95 menu clause + I.03. DAG_README flag 6, first orphan: cured. |
| `COND:A2_n` | **RESOLVED** at I.12 | = HYP.27's content; formal carrier = landed `DrainageAt n` (`Statement.lean:118`). Second orphan: cured. |
| `COND:H-e)-window-pinning` | **RESOLVED** at I.14 | = HYP.24's pinning half; suppliers H.89 (`e₁ = 2`) + `StageInterface.hwin` (general, carried) + orchestrator item O-2. Third orphan: cured. (The literal DAG id drops the leading paren — [F7]; matched on that form.) |

### 3.11 Census and reconciliation

**Category counts over the 154 rows** (each row exactly once; splits counted at their primary):

| category | count | rows |
|---|---:|---|
| DISCHARGED-BY (landed) | 6 | 03, 04, 05, 06, 10, 147 |
| DISCHARGED-BY (contract/structural) | 16 | 07, 13, 14, 37, 40, 43, 44, 72, 87, 101, 102, 103, 116, 121, 134, 145 |
| DISCHARGED-BY (late-binding: D/F) | 25 | 46–56, 58, 60, 61, 99, 104, 106–108, 112–115, 118, 129 |
| CITE (gate (b)) | 2 | 15 ([AGNPRW] via C.94), 38 (FGMN via C.66/C.92) — *[A-F.10: plus the chapter-B-owned [GN15] Thm 2.3 via B.42 (no ledger row of its own; see the 2026-08-16 addendum) — the gate-(b) signature queue is three deep]* |
| DISCHARGE-NODE-HERE | 7 | 01, 12, 17, 91, 98, 105, 111(def-half) |
| OPEN-MATH | 36 | 08, 09, 11, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 35, 36, 41, 42, 57, 63, 67–71, 74, 78, 79, 80, 81, 82, 88, 139, 142, 143, 144(BOX-2), 148 |
| NOT-ON-CAPSTONE-PATH | 62 | 02, 16, 18, 19–22, 31, 34, 39, 45, 59, 62, 64–66, 73, 75–77, 83–86, 89, 90, 92–97, 100, 109, 110, 117, 119, 120, 122–128, 130–133, 135–138, 140, 141, 146, 149–154 (+ 111's deep-tail half, secondary) |
| **total** | **154** | 6+16+25+2+7+36+62 = 154 (111 counted once, at its primary; 144 counted once, at BOX-2) |

**Reconciliation against the ledger's own v7 tally** (35 CARRY · 18 MATH · 81 NODE · 4 MERGED
· 13 CLOSED · 2 POLICY · 1 IN-PROGRESS): all 18 MATH rows land in OPEN-MATH except HYP.07
(terminates at B's committed contract), HYP.137 and HYP.146 (both stay MATH in the ledger but
are NOT capstone conjuncts — disclosure-without-promotion and route-not-taken respectively);
all 13 CLOSED + 2 POLICY + the IN-PROGRESS row land in NOT-ON-CAPSTONE-PATH; all 4 MERGED land
in NOT-ON-CAPSTONE-PATH (MERGED); the 35 CARRY rows split into the Display-A conjunct carriers
(OPEN-MATH), the cite (HYP.15), and the all-O block's per-row terminations (§3.8). **No row is
silently dropped: 6+16+26+2+7+36+61 = 154.**

---

## 4. §4 — THE DISPLAY-A CARRIERS AND THE CAPSTONE HYPOTHESIS STRUCTURE

> **Section contract.** One field per Display-A conjunct, at exactly ledger strength,
> degree-indexed where the display is (`if n ≥ 6`, `if n ≥ 8`). Under Part V gate (a), the
> field list of I.10 is capstone-conditionality state: **any field change (add, remove,
> restate) is owner-gated** — including the removal WELD-ZERO would license (I-7). Carrier
> `def`s are `Prop`s; none is proved; non-vacuity is a leanspec elaboration check plus the
> `n ≤ 2` conclusion gates (I.23), never a claimed instance (a `Prop` structure's
> instantiability IS the open mathematics).

### NODE I.01 [def] [fresh]

**STATEMENT.** *`NS7(O)` — the termination hypothesis, at exactly HYP.15's strength.* The
project's MacLane/Okutsu key-polynomial descent terminates over every complete DVR in scope:
for every `O` in the bundle and every monic squarefree `f` over `O`, every descent history of
the tower grammar on `f` reaches multiplicity `1` (or a terminating α-refine chain) in
finitely many steps. **This is the carried-hypothesis form**; the DISCHARGE is the gate-(b)
cite C.94 ([AGNPRW] Thm 5.2) — once C.94's axiom is signed and landed, this `Prop` is proved
from it and the field becomes cite-conditional, visible to `#print axioms` (gate I.25).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `NS7(O)` (Display A line 1; ledger HYP.15, CARRY-as-CITE): OM descent terminates over
every complete DVR with finite residue field. Discharged by chapter C's gate-(b) cite C.94
([AGNPRW] Thm 5.2) once signed; carried as a named Prop until then. -/
def NS7Termination : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    True  -- ⚠ STUB-STAGE BODY: the real body quantifies over C's descent-history type
          -- (C §5's level-datum chain over the FIXED bundle, GC-7) and asserts finiteness.
          -- FROZEN HERE: the name, the bundle quantifier, the Prop kind. The body is typed
          -- against C's committed §5 carriers at stub time (GC-13 tier (b): C is committed).
```

**⚠ BLOCKED-UNTIL-RESOLUTION (the E.51-class pattern, disclosed).** The body references
chapter C's descent-history carrier by name; C is committed but its §5 Lean types land at stub
stage. Per CHAP-E's precedent (its four `True`-placeholder nodes, E §14 item 11) this node is
**BLOCKED-UNTIL-RESOLUTION: the fleet must not fire on it while the placeholder body reads
`True`** — the orchestrator's stub-resolution pass types it. It is listed so in §11.

**DEPENDS.** C §5's level-datum/descent types [C committed; exact names at stub time] · C.94
(the discharging cite). **PROOF.** definitional. **SIZE.** 14 lines.
**SOURCE.** ledger HYP.15 (verbatim disposition, Q1's answer: *"in Lean, NS7 stays a carried
hypothesis until proved or declared-with-faithfulness"*); Display A line 1.
**TEETH.** none (a carrier); the cite's teeth are C.94's faithfulness entry + audit A-3.
**ENVIRONMENT.** ENV-I1.

---

### NODE I.02 [def] [fresh]

**STATEMENT.** *`A0_n` — the decided-value law at degree `n` (HYP.25's Lean-facing slice).*
The degree-`n` slice of the certified target: for every splitting type `σ` of degree `n` there
exist `num, den ∈ ℚ[x]`, `den ≠ 0`, with `decidedDensity O n σ = num(q)/den(q)` (and
`den(q) ≠ 0`) at every `O` in the bundle — i.e. exactly `UniformityStatementDecided`'s body
with `n` fixed. The `∃` stands outside the `∀ O` (the uniformity order).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `A0_n` (Display A; ledger HYP.25): the degree-`n` decided-value law — the degree-`n`
slice of `UniformityStatementDecided`. FAITHFULNESS: the corpus states `(A0)` on the
`disc ≠ 0` locus; `decidedDensity` counts the every-lift decided classes (GC-9, the
strictly stronger read) — divergence recorded, honesty I-6. -/
def DecidedSliceAt (n : ℕ) : Prop :=
  ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
```

**DEPENDS.** landed `UniformityStatementDecided` (the body is its literal slice — copy the
landed body, do not re-type it), `decidedDensity`, `residueCard`, `FactorizationType`.
**PROOF.** definitional. **SIZE.** 14 lines.
**SOURCE.** ledger HYP.25 (`A0` lift well-posedness, "fixed-n public assumption with
load-bearing fence"); H.95's SIGNATURE NOTE (the (A0)-routes-to-`hdec` decision, consumed
here as the slice form); `Statement.lean:84–91` (the body).
**TEETH.** none (carrier); the `n = 2` instance is FIRED unconditionally by gate I.23 (from
landed `genuineDensity_two_exact` + the `n = 2` drainage tie), which is the field's
non-vacuity witness.
**ENVIRONMENT.** ENV-I1.

---

### NODE I.03 [def] [fresh]

**STATEMENT.** *`A1_n` — the exact-core-menu law at degree `n` (HYP.26, at ledger strength).*
For degree `n`: there is a finite covering menu — `∃ S : Finset FactorizationType` with
`CoveringMenu O n S` for every `O` — **whose shape is `(A1)`-admissible**: the menu is carried
by an `A1Family` (H.93's cells with σ-labels, q-independent coefficients, affine exponents)
whose cells' σ-labels enumerate `S`. Fixed `n`, all `q` simultaneously; σ is not an A1 binder
(the labels are internal data — ledger wording).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `A1_n` (Display A; ledger HYP.26; COND:A1_n's resolution — I.13): a q-independent
`(A1)`-admissible family list carrying a covering menu at degree `n`. The shape clause uses
chapter H's committed `A1Family`/`A1Cell` (H.93, with W-12 r4's σ-label field). -/
def MenuLawAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ F, C.σ ∈ S) ∧ (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S
```

**⚠ SIGNATURE NOTE.** The exact-weights clause of HYP.26 ("internal σ_F labels and exact
weights") is carried by the `A1Cell.coeff` field plus the count laws (C.114/H §7) — this
carrier states the menu + shape + labels; the WEIGHT-correctness tie is part of the count
layer (OPEN-MATH, §3 rows HYP.23/32/35), deliberately not smuggled into the carrier. Recorded
as the carrier's one under-statement; the cross-read checks it (§13 item 4).

**DEPENDS.** H.93 (`A1Cell`, `A1Family`; committed contract) · landed `CoveringMenu`,
`FactorizationType`. **PROOF.** definitional. **SIZE.** 16 lines.
**SOURCE.** ledger HYP.26 (verbatim: "a finite disjoint q-independent family list carries
internal σ_F labels and exact weights; σ is not an A1 binder"); `EFF.GENIND.13` (the package's
menu member); DAG_README flag 6 (the `COND:A1_n` orphan this resolves with I.13).
**TEETH.** the `n = 2`/`n = 3` menu instances are landed (`coveringMenu_two`,
`coveringMenu_three`) — gate I.23 fires them as the field's non-vacuity witnesses (menu
clause only; the A1Family shape at `n ≤ 3` is a stub-stage exercise flagged in §11).
**ENVIRONMENT.** ENV-I1.

---

### NODE I.04 [note] — `A2_n` IS LANDED `DrainageAt n` (no new Lean)

`A2_n`'s formal carrier exists: `Uniformity.Density.DrainageAt` (`Statement.lean:118`),
PROVED at `n = 1` (`drainage_one`) and `n = 2` (`drainage_two`), open at `n ≥ 3`. Chapter I
declares **no** parallel drainage Prop (that would double-count the leg — honesty I-4). The
COND resolution is I.12; the structure field `a2` (I.10) binds the landed name directly.
DAG rows: `BP.I.04 → lean:DrainageAt`, `BP.I.04 → HYP.27`, `COND:A2_n → BP.I.04`.

---

### NODE I.05 [def] [fresh]

**STATEMENT.** *`(H-e)-window-pinning` — the pinning carrier (HYP.24's pinning half; the
third COND orphan).* All read data consumed by a stage decision are pinned inside the stage
window: no read consults a height in the ragged band, and every consulted position is
`≤ N − 1` in window coordinates. At `e₁ = 2` this is DISCHARGED by H.89's ledger (contract:
`consulted_ram`/2SIDED/SPLITEQ clauses); at general genres it is the `StageInterface.hwin`
field's content, per-genre (GC-5's table).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `(H-e)-window-pinning` (Display A; ledger HYP.24's pinning half; COND resolution I.14).
Supplier re-sourcing per v4: LEMMA GENHN-3 + GENIND-2's consulted-height bound — NOT the
off-route (H-a)/(H-b) leg. Discharged at `e₁ = 2` by H.89; general case = per-genre `hwin`. -/
def WindowPinningAt (n : ℕ) : Prop :=
  True  -- ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the
        -- degree-n stage data (H.09's StageInterface instances) and asserts the hwin
        -- clause at every stage of every genre of degree n. Typed at stub time against
        -- H.09's committed field list; FROZEN HERE: name, degree index, Prop kind.
```

**DEPENDS.** H.09 (`StageInterface.hwin`, committed) · H.89 (the `e₁ = 2` discharge,
committed). **PROOF.** definitional. **SIZE.** 10 lines.
**SOURCE.** ledger HYP.24 (the v4 SUPPLIER RE-SOURCED block, verbatim: "the pinning is
supplied elementarily, by `LEMMA GENHN-3` … together with GENIND-2's consulted-height
bound"); `EFF.GENHN.29`; CHAP-H H.89 + §16 item 3 (the `hwin` carry).
**TEETH.** none (carrier); H.89's own audit rows are the `e₁ = 2` teeth.
**ENVIRONMENT.** ENV-I1.

---

### NODE I.06 [def] [fresh]

**STATEMENT.** *`[GENHN-HE(μ ≥ 3)]` — the deep-leaf σ-decision carrier (HYP.81), degree-
indexed `n ≥ 6`.* Stage leaves of multiplicity `μ ≥ 3` arising in the degree-`n` problem have
the required σ-decision (separable stage residuals decide σ with the `(eE, f[K-ext])`
transport for all lifts — GC-9 form). Scope split carried IN the docstring: `μ = 3`
(first-live `n = 6, 7`) is corpus-unconditional (HE3.A) awaiting a transcription owner (O-1);
`μ ≥ 4` (`n ≥ 8`) rides HYP.143.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `[GENHN-HE(μ ≥ 3)]` (Display A, `if n ≥ 6`; ledger HYP.81). μ = 3 slice: THEOREM HE3.A,
unconditional in the corpus, transcription owner UNASSIGNED (orchestrator O-1). μ ≥ 4: open
(HE3-BOX-6, HYP.143). Consumers return `BLOCKED: HYP.81`, never assume. -/
def GenhnHEAt (n : ℕ) : Prop :=
  True  -- ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): quantifies over degree-n stage
        -- leaves with μ ≥ 3 (H's StageLeaf/GenreDatum layer) asserting the σ-decision
        -- clause. Typed at stub time against H.01/H.09 + the O-1 resolution.
```

**DEPENDS.** H.01/H.09 (committed carriers) · the O-1 transcription (future).
**PROOF.** definitional. **SIZE.** 10 lines.
**SOURCE.** ledger HYP.81 (incl. the v3 SCOPE SPLIT verbatim); `EFF.GENHN.40`.
**TEETH.** none (carrier). **ENVIRONMENT.** ENV-I1.

---

### NODE I.07 [def] [fresh]

**STATEMENT.** *`[GENHN-TOW-1]` — the deep-tower supplier carrier (HYP.82), degree-indexed
`n ≥ 8`.* The `n ≥ 8` tower leg satisfies the additional GENHN supplier law — the census
C.93 makes formal ("seven items under six numerals" [F8]; items (1)–(5)+(6)(β) are C
theorems, (6)(α) at depth 3 is C.90/C.91, depth ≥ 4 claimed nowhere).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- `[GENHN-TOW-1]` (Display A, `if n ≥ 8`; ledger HYP.82). Keyed to chapter C's census
C.93: the boxed remainder is the n ≥ 8 open family (HYP.67–71/78–80/142/143/144-BOX-2). -/
def GenhnTow1At (n : ℕ) : Prop :=
  True  -- ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the census conjunction, typed
        -- against C.93's #check-suite names at stub time (C committed).
```

**DEPENDS.** C.93 (committed contract). **PROOF.** definitional. **SIZE.** 8 lines.
**SOURCE.** ledger HYP.82; C.93's STATEMENT (the census made formal).
**TEETH.** none (carrier); C.93's S4-witness regression is the census's teeth.
**ENVIRONMENT.** ENV-I1.

---

### NODE I.08 [def] [late-binding: chapter F] — `JD0-BOX-2`

**STATEMENT (placeholder at GC-13(c) strength).** *The unit-character gauge-form perimeter
(HYP.74).* The weld's entire conditional value dictionary acts by slot-wise unit characters —
`EFF.JD0.05` [supplied-by: chapter F]. Chapter F's §4 composes the carrier
(`GaugeFormPerimeter`/`JD0Box2`, F.01–F.06 at F's current §2 index) and the per-site strike
ledger; chapter I binds the FIELD NAME `jd0` (I.10) to F's carrier at F's freeze (§9). Until
then this node is a placeholder: **no Lean file**; the DAG row targets `EFF.JD0.05`.

**SOURCE.** ledger HYP.74 (CARRY, reachability SIGNED; grade bar signed at HYP.39); Display A.
**RESOLUTION.** §9 item L-1 (orchestrator, at F freeze).

---

### NODE I.09 [def] [late-binding: chapter F] — `GENHN-BOX-2` + the W-1 sub-residue

**STATEMENT (placeholder at GC-13(c) strength).** *The W-9 graded face (HYP.148, `if n ≥ 6`)
with its W-1 transport sub-residue (HYP.139).* LEMMA GENHN-4's layer 1 at `μ ≥ 3` consumes
COROLLARY W-9's twisted group algebra as the carry bookkeeping — `EFF.GENHN.50` [supplied-by:
chapter F] (F §5's `GenhnBox2` + `W1Transport` carriers). The WELD-ZERO arc note travels with
the field (I-7): IN-PROGRESS, 1-of-2, licenses nothing; removal on a passed arc is owner-gated.
**No Lean file** until F freezes; DAG rows target `EFF.GENHN.50` and HYP.139/148.

**SOURCE.** ledger HYP.148 (incl. v6/v7 ARC NOTEs), HYP.139; Display A.
**RESOLUTION.** §9 item L-2.

---

### NODE I.10 [structure] [fresh] — **THE CAPSTONE HYPOTHESIS STRUCTURE**

**STATEMENT.** *Display A, made formal: one field per conjunct, at ledger strength,
degree-indexed where the display is.* For a degree `n`, `CapstoneHypotheses n` carries:
`ns7` (I.01); `ladder` — the σ-ladder supply quantified over rung instantiations
(E.24's `LadderSupply`, which packages `HE7A[…]`, `(LB1)` = E.39, `(MP1)` = E.40, and the
`∀ i ≥ 3` deep-twist carriers E.61/E.62 — one field here because E.24 is ONE committed
bundle; its `.lb1`/`.mp1`/`.vartheta` projections are the ledger's three conjuncts); `a0`
(I.02); `a1` (I.03); `a2` (landed `DrainageAt n`); `jd0` (I.08, late-binding); `genhnBox2`
(`6 ≤ n →`, I.09, late-binding); `windowPinning` (I.05); `genhnHE` (`6 ≤ n →`, I.06);
`genhnTow1` (`8 ≤ n →`, I.07). The `AllOInterfaces` conjunct is NOT a field — §4.3's signed
reconciliation (honesty I-10).

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **Display A** (`spec/HYPOTHESIS_LEDGER.md`, FROZEN v5), one field per conjunct.
Kind note [F7]: H.95's `InductionPackage` is a `def`-Prop existential; this carrier is a
`structure` and does NOT claim to mirror H.95's kind. Field-list changes are owner gate (a)
events (CONVENTIONS Part V). -/
structure CapstoneHypotheses (n : ℕ) : Prop where
  ns7 : NS7Termination
  ladder : ∀ (O : Type) [CommRing O] /- bundle -/ (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C),
      Ladder.LadderSupply C B          -- E.24: HE7A + LB1 + MP1 + ∀ i ≥ 3 carriers
  a0 : DecidedSliceAt n
  a1 : MenuLawAt n
  a2 : DrainageAt n
  jd0 : True                            -- ⚠ LATE-BINDING F (I.08); typed at F freeze
  genhnBox2 : 6 ≤ n → True              -- ⚠ LATE-BINDING F (I.09); typed at F freeze
  windowPinning : WindowPinningAt n
  genhnHE : 6 ≤ n → GenhnHEAt n
  genhnTow1 : 8 ≤ n → GenhnTow1At n
```

**⚠ THE TWO `True` FIELDS ARE PLACEHOLDERS, NOT VACUITIES-BY-DESIGN.** They are the
chapter-E BLOCKED-UNTIL-RESOLUTION pattern applied to a parallel chapter: the orchestrator's
§9 pass types them against F's frozen carrier names before ANY stub is signed (E §14 item 11
precedent — "the fleet must not fire on them before that"). A signed stub with a `True` field
here would be a false conditionality claim — listed as a §11 blocker.

**⚠ QUANTIFIER DISCLOSURE (the `ladder` field).** Display A assumes the ladder suite
"uniformly in O"; E's carriers are instance-level (per `SlotCarrier`/`BlockData`). The field
quantifies over ALL instantiations — the strongest uniform reading, matching the ledger's
"assume uniformly in O" preamble. If the eventual assembly needs only the instantiations
arising from degree-`n` inputs, weakening the field is a gate-(a) statement change (it
weakens a hypothesis, hence STRENGTHENS the theorem — still owner-visible because the field
list is the public conditionality). Cross-read item (§13 item 5).

**DEPENDS.** I.01, I.02, I.03, I.05, I.06, I.07 · E.24 (`LadderSupply`, committed; via it
E.39/E.40/E.61/E.62) · landed `DrainageAt` · I.08/I.09 (late-binding).
**PROOF.** definitional. **SIZE.** 24 lines.
**SOURCE.** Display A verbatim (`spec/HYPOTHESIS_LEDGER.md` "Display A — public interface —
FROZEN"); ledger rows HYP.15/41/42/57/63/25/26/27/74/148/24/81/82; Brief I product (1) as
modified by Part V item 2.
**TEETH.** the structure's teeth are the gates (I.23–I.25) + §12's reconciliation.
**ENVIRONMENT.** ENV-I1.

---

### 4.3 — NODE I.11 [note] — THE `AllOInterfaces` RECONCILIATION (signed, row by row)

Display A's final conjunct names 14 interface-generality edges. On the Lean side (honesty
I-10) each terminates as follows — this list is §12's GC-8-rider-(iii) reconciliation, and it
is SIGNED here rather than carried as a Lean field:

| name | ledger row | Lean-side termination |
|---|---|---|
| GENIND-1 | HYP.121 | ∀`O`-free by form: H.93/H.94 (contract) |
| RMG | HYP.122 | out of cut (`EXT:RMENGINE`); route re-derives — NO import to generalize |
| ILN | HYP.123 | consumers out of cone; residual rides HYP.148's ∀`O` carrier |
| GRB | HYP.124 | out of cut (`EXT:GRB_ORDER2`); no import |
| ITER-LAW | HYP.125 | out of cut (`EXT:ITERLAWN`); no import |
| W/J | HYP.126 | consumers `[H-a]–[H-c]` out of cone |
| DU | HYP.127 | pricing-only; no import |
| W-10 | HYP.128 | census O-11 out of cone |
| J-D0 | HYP.129 | the ∀`O` binder of F's carrier statement (late-binding) |
| L2core | HYP.130 | quarry-side; leanfinal does not consume |
| HUMAN_PROOF | HYP.131 | quarry-side; Q7 policy |
| local-integrals | HYP.132 | measure route quarantined — Q7 IS the demanded route exclusion |
| CONV | HYP.133 | leanfinal is monic-native; no projective transfer exists |
| GENHN-count | HYP.134 | H §7 ∀`O` statements at `μ = 2` (contract); `μ ≥ 3` rides HYP.81/148 |

**The sanity check GC-8 demands passes:** every signed-out name above either has NO consumer
on the Lean route (rows marked out of cut/cone/quarry — matching §3's NOT-ON-CAPSTONE
justifications) or terminates in a ∀`O` statement form; none of the 14 hides an unstated
mathematical assumption of the Lean capstone. **What this does NOT say:** nothing here
generalizes the INFORMAL corpus's uses — the informal Display A keeps its conjunct untouched;
this reconciliation is about what the LEAN chain rests on.

---

## 5. §5 — THE COND RESOLUTIONS (DAG_README flag 6, discharged)

The 0c DAG carried three Display-A conjuncts that matched no ledger row, as `COND:` orphan
nodes. Each is now either tied to an existing row's content or given the formal carrier it
lacked — "each COND orphan either gets a row or is proved equal to an existing row's content"
(Brief I product (4)). All three resolutions are [note] nodes: their product is DAG rows +
this record, no Lean.

### NODE I.12 [note] — `COND:A2_n` RESOLVED

`A2_n` **is** ledger row HYP.27's content, and its formal carrier is **landed**:
`Uniformity.Density.DrainageAt n` (`Statement.lean:118`). The 0c matcher missed it because
HYP.27's title is "`A2` drainage" (no `_n` suffix) — a name-form miss, not a missing row.
Status by degree: `n = 1, 2` PROVED (`drainage_one`, `drainage_two`); `n = 3` open (the
HYP.08/09 frontier); `n ≥ 4` open (via H.98 ⇐ `InductionPackage`). DAG rows:
`COND:A2_n → HYP.27`, `COND:A2_n → lean:DrainageAt` (via BP.I.12).

### NODE I.13 [note] — `COND:A1_n` RESOLVED

`A1_n` **is** ledger row HYP.26's content; its formal carrier is composed here as I.03
(`MenuLawAt`), typed against chapter H's committed `A1Cell`/`A1Family` (H.93) — the
strengthened (σ-labelled) predicate, whose closure is H.94. The 0c matcher missed HYP.26 for
the same name-form reason. DAG rows: `COND:A1_n → HYP.26`, `COND:A1_n → BP.I.03`,
`BP.I.03 → BP.H.93`.

### NODE I.14 [note] — `COND:H-e)-window-pinning` RESOLVED

The pinning conjunct **is** ledger row HYP.24's pinning half (the row's v4 SUPPLIER
RE-SOURCED block is the authority: supplied by `LEMMA GENHN-3` + GENIND-2's consulted-height
bound, NOT the off-route `(H-a)/(H-b)` leg). Formal carriers: I.05 (`WindowPinningAt`) +
H.89 (the `e₁ = 2` discharge) + `StageInterface.hwin` (the carried general field). **Supplier
gap recorded, not hidden:** `EFF.GENHN.29`'s cap/consultation clauses are consumed by
committed H only at the (c) congruence bound (H.51) — orchestrator item O-2 books the missing
transcription (§9.3). DAG rows: `COND:H-e)-window-pinning → HYP.24`,
`COND:H-e)-window-pinning → BP.I.05`, `BP.I.05 → BP.H.89`.
(Literal DAG id: `COND:H-e)-window-pinning`, leading paren dropped [F7].)

---

## 6. §6 — THE ASSEMBLY (the structure fired through the landed and committed spine)

> **Section contract.** Everything here is bookkeeping (honesty I-1): projections of I.10 and
> applications of `UniformityStatement.ofDecided` (landed) / `uniformity_of_package` (H.98,
> contract) / `totalMassOne_of_drainage` (landed). No theorem in this section makes the
> capstone less conditional; each makes the conditionality MACHINE-READABLE.

### NODE I.15 [theorem] [fresh]

**STATEMENT.** *The drainage projection.* If `CapstoneHypotheses n` holds for every `n`, then
`DrainageAt n` holds for every `n`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem drainage_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses n) : ∀ n, DrainageAt n
```

**DEPENDS.** I.10. **PROOF.** 1. `intro n; exact (h n).a2`. **SIZE.** 4 lines.
**SOURCE.** Display A's `A2_n` conjunct; `Statement.lean:118`.
**TEETH.** none (projection). **ENVIRONMENT.** ENV-I1.

---

### NODE I.16 [theorem] [fresh]

**STATEMENT.** *The decided-target projection.* If `CapstoneHypotheses n` holds for every
`n`, then `UniformityStatementDecided` holds. (The content: the `a0` fields ARE the
degree-slices of the decided target; re-indexing is the whole proof. This is where the
count layer's openness is made visible: nobody can supply `∀ n, CapstoneHypotheses n` today
precisely because `a0`/`a1` are open at `n ≥ 3`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem decided_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses n) : UniformityStatementDecided
```

**DEPENDS.** I.02, I.10 · landed `UniformityStatementDecided`.
**PROOF.** 1. `intro n hn σ hσ`. 2. `exact (h n).a0 σ hσ` (the slice body is literal —
`DecidedSliceAt` was copied from the landed target's body, so `exact` closes it; if
elaboration balks on instance order, `peel`/`intro O` and reapply).
**SIZE.** 6 lines.
**SOURCE.** `Statement.lean:84`; I.02's body-copy discipline.
**TEETH.** none. **ENVIRONMENT.** ENV-I1.

---

### NODE I.17 [theorem] [fresh]

**STATEMENT.** *THE HONEST CAPSTONE ASSEMBLY.* If `CapstoneHypotheses n` holds for every `n`,
then `UniformityStatement` holds. Proof = landed `UniformityStatement.ofDecided` on I.15 +
I.16. **This is the chapter's terminal theorem**: the capstone modulo exactly the §4
structure — every named cite, every named open hypothesis, nothing else.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **The capstone, modulo Display A.** `UniformityStatement` follows from the ledger's
frozen hypothesis block and nothing else. What remains open is exactly the block's fields:
see the chapter-I disposition table. -/
theorem uniformity_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses n) : UniformityStatement :=
  UniformityStatement.ofDecided (drainage_of_capstoneHypotheses h)
    (decided_of_capstoneHypotheses h)
```

**DEPENDS.** I.15, I.16 · landed `UniformityStatement.ofDecided` (check argument order:
`(hd) (h)` per `Statement.lean:124`). **PROOF.** as displayed (term-mode). **SIZE.** 8 lines.
**SOURCE.** `Statement.lean:124–131`; Brief I product (2).
**TEETH.** gate I.24 prints its axiom footprint (must be Lean-core exactly, since every open
input is a HYPOTHESIS, not an axiom — the design's whole point).
**ENVIRONMENT.** ENV-I1.

---

### NODE I.18 [theorem] [fresh]

**STATEMENT.** *`TotalMassOne`, not double-counted.* From the same structure, `TotalMassOne`
— via the `a2` fields and landed `totalMassOne_of_drainage` ONLY (honesty I-4: the mass law
is the drainage leg in disguise and gets no field of its own).

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem totalMassOne_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses n) : TotalMassOne :=
  totalMassOne_of_drainage (drainage_of_capstoneHypotheses h)
```

**DEPENDS.** I.15 · landed `totalMassOne_of_drainage` (`Statement.lean:174`).
**PROOF.** as displayed. **SIZE.** 5 lines.
**SOURCE.** `Statement.lean:166–176`; ledger synthesis note (v5 dedup: "not a strengthening
of the capstone — the drainage leg wearing a different hat").
**TEETH.** none. **ENVIRONMENT.** ENV-I1.

---

### NODE I.19 [note] — THE PACKAGE ROUTE (H.98 consumed, not re-proved)

The second assembly route is CHAP-H's committed pair, consumed by name and NOT re-exported
(one-public-declaration discipline; a verbatim re-export adds a name, not content):

* `Uniformity.Density.drainage_of_package : (∀ n, InductionPackage n) → ∀ n, DrainageAt n`
  (H.98) — the rate route to the `a2` fields;
* `Uniformity.Density.uniformity_of_package : UniformityStatementDecided →
  (∀ n, InductionPackage n) → UniformityStatement` (H.98) — the package form of I.17.

Base cases at HEAD-of-contract: `package_two` UNCONDITIONAL (H.96, a chapter-G payoff);
`package_three_of_rate` (H.97's adopted form — `package_three_of_drainage` is DECLARED
UNPROVABLE by H.97's own ⚠ and **must not be assigned**). **The GENIND.B fence applies in
full (honesty I-2): no node here or anywhere composes `InductionPackage n` for `n ≥ 4`.**
DAG rows tie this note to BP.H.95–H.98 and HYP.27/30.

### NODE I.20 [note] — THE STAGE DISPLAY (what fires at each stage of discharge)

The honest "capstone modulo …" statement at each stage, for the record and for §12's teeth:

| stage | fires | modulo (named) |
|---|---|---|
| **S0 — today, landed** | `n = 1`: drainage, total mass (`drainage_one`, `totalMass_one`); `n = 2`: drainage, total mass, the exact densities, THE CAPSTONE SLICE (`drainage_two`, `totalMass_two`, `genuineDensity_two_exact`, `uniformityStatement_two`); `q`-instances at `q = 2, 3` (`gate_two_padic_*`) | nothing — unconditional, Lean-core |
| **S1 — chapters B–H land** | the leaf layer, the schema, the rate calculus, `package_two`, the σ-μ2 chain, the count laws at order 1 | the gate-(b) cites (C.66/C.92/C.94) where consumed |
| **S2 — the `n = 3` frontier closes** | `DrainageAt 3` (via H.97+H.98), cubic total mass unconditionally | `hrate₃` (HYP.08) + the cubic value layer (HYP.11/28/29) for the `n = 3` capstone slice |
| **S3 — the open surface** | `UniformityStatement` via I.17 | **exactly the §4 field list**: LB1, MP1, HE7A instantiations, ∀ i ≥ 3 deep-twist/𝒲, A0/A1 at every degree, JD0-BOX-2, GENHN-BOX-2 (n≥6), window pinning, GENHN-HE (n≥6), GENHN-TOW-1 (n≥8) — i.e. §3's 36 OPEN-MATH rows + 2 CITEs, and nothing else |

**No stage claims more than its row.** The sentence a report may use verbatim: *"proved
unconditionally at `n ≤ 2`; at general `n` the capstone is machine-checkably equivalent to
the frozen Display-A block, whose open rows are enumerated at §3 census: 36 OPEN-MATH + 2
CITEs + 7 chapter-I audit items."*

---

## 7. §7 — THE `typeOf` FAITHFULNESS BRIDGE AND THE CORE-SET AUDIT LEDGER

### NODE I.21 [def] [fresh]

**STATEMENT.** *`TypeOfFaithful` — the trust-boundary bridge statement (HYP.01 + HYP.105
named; GC-3: chapter I "speaks both languages and owns the bridge statement").* On the
`disc ≠ 0` locus over the bundle: for monic `f` with `disc f ≠ 0`, the gcd-engine multiset
`typeOf f` equals the classical ideal-theoretic multiset — over the factors `g` of `f`, the
pairs `((maximalIdeal S).ramificationIdx' R, (maximalIdeal S).inertiaDeg' R)` computed at the
MAXIMAL order `S` of each factor field (GC-3's primed rank-form API), with the ordering/
normalization convention of HYP.12. This is a STATEMENT definition (`Prop`), not a theorem:
it is the core-set review object, and its eventual discharge is a future proof unit or a
gate-(b) cite — Part V's two terminals, explicitly open today.

**SIGNATURE.**
```lean
namespace Uniformity.Density

/-- **THE TRUST BOUNDARY, NAMED** (ledger HYP.01 [CORE-SET] + HYP.105; GC-3's kept-apart
rule): `typeOf`'s gcd multiset (over the ORDER `AdjoinRoot g`) agrees on the `disc ≠ 0`
locus with the ideal-theoretic `(e, f)` multiset (over the maximal order/DVR), in the primed
rank-form generation. NO chapter may silently identify the two APIs (GC-3); a node needing
the identification hypothesizes THIS name or returns `BLOCKED: HYP.01`. -/
def TypeOfFaithful : Prop :=
  True  -- ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the
        -- bundle and monic f with disc f ≠ 0, and equates (typeOf f).data with the
        -- maximal-order multiset via `Ideal.ramificationIdx'`/`inertiaDeg'`. Typing it
        -- needs the factor-field valuation-ring carrier — the same object B-BOX-1's repair
        -- route (B.56, OPTIONAL) would build. FROZEN HERE: name, locus, both APIs by name.
```

**DEPENDS.** landed `typeOf`, `FactorizationType` · `Quarry/RamificationInertiaLocal` (GC-3's
primed API) · the maximal-order carrier (B.56's layer IF fired, else fresh at discharge time).
**PROOF.** definitional. **SIZE.** 16 lines.
**SOURCE.** ledger HYP.01 (verbatim STATEMENT + the Q4 non-lift), HYP.105 (the v5 placement:
"name the theorem inside the core-set audit"), HYP.12 (the convention clause); GC-3's
KEPT-APART paragraph.
**TEETH.** none until discharged; audit A-1 is the human leg.
**ENVIRONMENT.** ENV-I1.

---

### NODE I.22 [note] — THE CORE-SET AUDIT LEDGER (A-1 … A-7)

Under Part V item 2: cite/def-faithfulness rows stay **gate-(b)-adjacent human reads**; the
rest are absorbed into the standing fresh-eyes cadence (auto-memory: periodic fresh-context
audits during the build; findings are stop-the-line). No audit row is a fleet node.

| id | row(s) | object | class | when |
|---|---|---|---|---|
| A-1 | HYP.01, HYP.105 | `typeOf` faithfulness — review I.21's statement against the classical (e,f) multiset; the engine of the type definition | gate-(b)-adjacent (def-faithfulness), human | before any node hypothesizes `TypeOfFaithful`; refreshed at each fresh-eyes pass |
| A-2 | HYP.12 | `(e,f)` ordering/multiset normalization vs the classical convention | gate-(b)-adjacent (def-faithfulness), human — one clause of A-4 | with A-4 |
| A-3 | HYP.17 | [AGNPRW] Thm 5.2 / GN15 / Kuhlmann publisher-numbering | gate-(b)-adjacent (cite), bounded lookup | **BEFORE C.94/C.66/C.92 sign** — load-bearing since Q1 cites by number |
| A-4 | HYP.98 | the core set: the types, `UniformityStatement`, `genuineDensity`/`decidedDensity`, the cites, changed-definition faithfulness paragraphs | RECURRING fresh-eyes (append #49 directive 2) | at chapter milestones; next at the D/F freeze |
| A-5 | HYP.111 (def half) | the "decided" predicate's meaning (what `decidedDensity` counts) | rides A-4 | with A-4 |
| A-6 | (I.10) | the field list of `CapstoneHypotheses` vs frozen Display A — one-to-one, nothing added, nothing dropped, §4.3 reconciliation intact | fresh-eyes, decorrelated arm | at this chapter's cross-read + each gate-(a) event |
| A-7 | HYP.91 | OB-a…OB-d representation: OB-a = H.89 + `hwin` ✓; OB-b/c/d checked against CHAP-H's committed text + `DAG_BLUEPRINT_H.tsv` | bounded, one pass | at the H stub stage |

DAG rows tie A-* to their HYP rows via `BP.I.22`.

---

## 8. §8 — GATES (GC-11; the `n ≤ 2` re-fire, AXCHK, the cite footprint)

### NODE I.23 [gate] [fresh]

**STATEMENT.** *The unconditional-slice gate (`q = 2` AND `q = 3`; the landed `n ≤ 2`
capstone slices re-fired as regression anchors).* A census file, no public declaration:
(i) `#print axioms` on the landed unconditional set — `drainage_one`, `totalMass_one`,
`drainage_two`, `totalMass_two`, `coveringMenu_two`, `coveringMenu_three`,
`genuineDensity_two_exact`, `uniformityStatement_two`, `gate_two_padic_two_exact`,
`gate_two_padic_three_exact` — every line must print exactly
`[propext, Classical.choice, Quot.sound]`; (ii) the chapter-G landed `n = 2` values re-stated
as `#check`-level regression anchors with the expected numbers in comments: at `q = 2` the
three densities are `1/3, 1/3, 1/3`; at `q = 3` they are `3/8, 3/8, 1/4`; the exact drainage
law `undecidedCount O 2 N = q^N` at both primes (G.36); (iii) non-vacuity `#check`s for I.02/
I.03's `n = 2` instances (the slice of `UniformityStatementDecided` recoverable from
`genuineDensity_two_exact` + `genuineDensity_eq_decidedDensity_two`).

**GC-11 compliance.** Two primes ✓ (`q = 2` and `q = 3` via `gate_two_padic_*`); the
`e > 1 ∧ f > 1` witness clause is **signed non-applicable at `n = 2`** (a degree-2 type has
`e·f = 2`, so `e > 1 ∧ f > 1` is impossible; the meaningful witnesses live in B/C/E's gates
— e.g. B.85 — and I.24 re-prints their footprints once landed). Disposition recorded in §12.

**DEPENDS.** the landed set named in (i). **PROOF.** none (census). **SIZE.** ~40 lines.
**SOURCE.** GC-11 ("I's gates additionally re-run the capstone-slice values (chapter G's
landed `n = 2` numbers) as regression anchors"); `ChapG/G49.lean` (the values).
**TEST.** compiles; every footprint line exact; anchor comments match. **ENVIRONMENT.** ENV-I2.

---

### NODE I.24 [gate] [fresh] — **AXCHK: the maintained interface census**

**STATEMENT.** *`spec/AXCHK.lean` — REVISION 2's planned artifact, composed here.* A
maintained, diffable census file listing EVERY exported capstone-facing interface of
`leanfinal` with its `#print axioms` line: the `Statement.lean` API (both CAP targets and the
cross-implications), the density/drainage layer, the chapter roll-ups' terminal supplies as
they land (G now; B/C/E/H/D/F at their landings), and this chapter's I.15–I.18. Output
committed as `spec/AXCHK_output.txt` (the diffable artifact); a footprint regression is
stop-the-line (repo standing rule). Pattern source: `lean/LeanUrat/AxChk_baseline.lean`
(the quarry's working ancestor).

**Location decision (recorded):** REVISION 2 names `spec/AXCHK.lean`; the file must live
where `lake env lean` can elaborate it against `leanfinal` — the composed artifact is
`leanfinal/AXCHK.lean` with a one-line pointer at `spec/` (this keeps `spec/` Lean-free; the
orchestrator may override at stub time; either way the OUTPUT commits under `spec/`).

**Maintenance rule.** Every chapter's stub-gate agent APPENDS its chapter's terminal names on
landing (the file is the one place the whole trusted surface is greppable — GC-8's "keeps the
capstone's honesty audit greppable" rationale, applied to axioms).

**DEPENDS.** the landed tree; grows monotonically. **PROOF.** none. **SIZE.** ~60 lines at
composition; grows. **SOURCE.** REVISION 2 fleet-protocol repairs ("a maintained leanfinal
analogue of AxChk_baseline (spec/AXCHK.lean listing every exported interface, diffable output
committed)"); Brief I product (6). **TEST.** output diff empty against committed baseline
except intended additions. **ENVIRONMENT.** ENV-I2.

---

### NODE I.25 [gate] [fresh] — **THE CITE-FOOTPRINT GATE**

**STATEMENT.** *Axiom hygiene under Part V: Lean core + exactly the signed cites, nowhere
else.* A census block asserting, at every AXCHK run: (i) every declaration NOT downstream of
a gate-(b) import prints exactly Lean core; (ii) every cite-conditional declaration (C.67's
pattern: "the conditionality is IN the axiom dependency") prints Lean core + exactly the
signed cite axioms it declares — the honest carrier the ledger wants; (iii) the FORBIDDEN
list is enforced mechanically: `AX_cellRecursion`-family (quarry-quarantined, Q7),
`Lean.ofReduceBool` (`native_decide` — stop-the-line per H.99's precedent), and any axiom
not in the signed registry. The signed registry at composition time: **empty** (no gate-(b)
cite is signed yet); expected entries: C.94's [AGNPRW] axiom, C.66/C.92's FGMN axiom group
(one or two entries per the orchestrator's subsumption choice, §9.3 O-4).

**DEPENDS.** I.24 (runs with it). **PROOF.** none. **SIZE.** ~25 lines.
**SOURCE.** Part V gate (b); C.66/C.67/C.92/C.94's committed footprint design; repo axiom
policy (CLAUDE.md). **TEST.** registry match exact. **ENVIRONMENT.** ENV-I2.

---

## 9. §9 — LATE-BINDING: CHAPTERS D AND F (composing in parallel — placeholders + the resolution pass)

> **⚠ THIS SECTION IS EXPLICITLY INCOMPLETE BY DESIGN.** Chapters D and F are being composed
> NOW, in parallel with this chapter. Every supply below is taken at GC-13(c) placeholder
> strength (`EFF.<NOTE>.<nn> [supplied-by: chapter <X>]`), never a guessed node ID. **The
> completion of this section is a RECORDED ORCHESTRATOR ITEM at the D/F freeze** (the charge's
> instruction, verbatim); until the resolution pass runs, the §11 stub list's blocked entries
> stand and no fleet agent fires on I.01/I.05/I.06/I.07/I.08/I.09/I.10/I.21.

### 9.1 Chapter-D residue (placeholders)

| what | placeholder | binds |
|---|---|---|
| the ϑ four-way orientation table | anchor **`D-THETA-TABLE`** (D.06 per D's front matter) | no chapter-I node reads ϑ; recorded because §3's D-rows (HYP.46–61, 99, 104, 106–108, 112–115, 118) resolve to D node IDs at freeze |
| T1/T3/T4/T5 supplier-interface nodes | `EFF.T1.*`/`EFF.T3.*`/`EFF.T4.*`/`EFF.T5.*` [supplied-by: chapter D] | the 25 late-binding rows of §3.5/§3.8 |
| the `𝒲_(≤i)` carriers (D product (4)) | handed to E/I by name — E.62 is the committed socket | I.10's `ladder` field consumes them THROUGH E.24; no direct D edge |
| D-H8's JD0 ruling | "chapter D opens no JD0 node; `JD0-BOX-2` lands in chapter I as the named hypothesis" | confirmed: I.08 is that landing (via F's carrier composition) |

### 9.2 Chapter-F residue (placeholders)

| what | placeholder | binds |
|---|---|---|
| Display A weld conjunct 1: `JD0-BOX-2` | `EFF.JD0.05` [supplied-by: chapter F] (F §4: `GaugeFormPerimeter`/`JD0Box2` + the per-site strike ledger) | I.08 → I.10's `jd0` field |
| Display A weld conjunct 2: `GENHN-BOX-2` + W-1 | `EFF.GENHN.50` [supplied-by: chapter F] (F §5: `GenhnBox2` + `W1Transport`) | I.09 → I.10's `genhnBox2` field |
| the `WeldSupply`/`WeldObligations` package for I | F §9's terminal supply (name per F's front matter) | the §3 rows HYP.74/139/148's carrier column |
| WELD-ZERO status | **1 of 2 clean passes; pass 2 LAUNCHED, IN FLIGHT** (append #56; no landing commit at HEAD) | honesty I-7; F's §8 pending arc; NOTHING here moves until it lands AND passes |

### 9.3 Recorded orchestrator items (the resolution pass + the gaps this chapter found)

| id | item | trigger |
|---|---|---|
| **L-1** | type I.08/I.10's `jd0` field against F's frozen carrier name; replace the `True` placeholder; re-run §11's blocked list | F freeze |
| **L-2** | type I.09/I.10's `genhnBox2` field against F's frozen `GenhnBox2`/`W1Transport`; arc note travels with the field | F freeze |
| **L-3** | resolve §3.5/§3.8's 25 D-rows to D node IDs; re-emit the affected `DAG_BLUEPRINT_I.tsv` rows with exact endpoints | D freeze |
| **O-1** | **book the `[GENHN-HE(μ = 3)]` transcription** (THEOREM HE3.A at `μ = 3`, first-live `n = 6, 7` — corpus-unconditional, NO owner in any committed chapter; honesty I-11(i)). Candidate homes: a chapter-B appendix (HE3 is B's note) or a chapter-E instance section; cheap relative to its Display-A weight | now (this chapter's finding) |
| **O-2** | **book the `LEMMA GENHN-3` cap/consultation transcription** (`EFF.GENHN.29` beyond the (c) bound H.51 consumes) — the general window-pinning supplier; candidate: an H-appendix node next to H.89 | now (this chapter's finding) |
| **O-3** | if WELD-ZERO lands + passes both arcs: the gate-(a) amendment removing I.10's `jd0`-adjacent `genhnBox2` field and retiring HYP.139/148 rows — owner-visible, never a fleet edit | WELD-ZERO acceptance |
| **O-4** | the C.66 ⊂ C.92 FGMN-axiom subsumption choice (one axiom group or two) — affects I.25's registry | before the C stub gate signs |
| **O-5** | the `n = 3` frontier package (HYP.08/09/11/28/29 + G's H-1 bridge) — a single post-blueprint unit brief exists implicitly across G/H; book it as the first post-fleet mathematics unit | orchestrator scheduling |

---

## 10. DAG ADDITIONS

Written to **`spec/DAG_BLUEPRINT_I.tsv`** in `dag_build.py`'s 9-column contract: **97 rows**,
all endpoints exact (BP.I.\*, committed BP.{H,E,C}.\* node IDs, ledger `HYP.*`, the two `CAP:`
nodes, the three `COND:` nodes, `EFF.*` placeholders for the D/F late-bindings, and landed
`lean:*` nodes; landed declarations with no `lean:` node are carried in the evidence column —
the CHAP-B H-9 mitigation). **Verified at composition: `python3 spec/dag_build.py &&
python3 spec/dag_check.py` → `RESULT: PASS`** (3,045 nodes, 4,570 edges; the four
pre-existing SCCs stay adjudicated; zero new cycles; the seven signed-out rows stay
unreachable).

Two recorded emission decisions:

1. **The CAP-node double-edge is deliberately avoided.** `BP.I.02`'s statement is the slice
   of the decided target; the CAP node's own out-edge is the assembly route
   (`CAP:UniformityStatementDecided → BP.I.16`). Emitting both `BP.I.02 → CAP:…` and
   `CAP:… → BP.I.16` manufactures a false 4-cycle (caught by the checker on the first build);
   the statement-source edge therefore targets `lean:UniformityStatementDecided` (the landed
   declaration node) and the decision is recorded in the row's evidence column.
2. **No `HYP.* → BP.<other-chapter>.*` edges.** Supplier chapters emit their own discharge
   edges (`BP.B.65 → HYP.14`, `BP.G.36 → HYP.27` precedents); this chapter emitting the
   reverse direction would create 2-cycles. The §3 table is the durable record of
   row-to-supplier bindings; the TSV carries only chapter-I-owned edges (from `BP.I.*`,
   `COND:*`, and the two `CAP:` assembly-route rows).

**Orchestrator note (PA-3(ii) pattern):** `spec/DAG.tsv`/`DAG_NODES.tsv` regeneration is the
orchestrator's — this chapter's build/check run was verification-only and the regenerated
shared files were NOT committed (parallel composers are live; D and F will add TSVs of their
own; one re-run books all three).

---

## 11. LEANSPEC STUB LIST (stage 0e)

Per GC-6.6: stubs wrap in **`namespace LeanspecI`**, one file `leanspec/Leanspec/ChapI.lean`
(the ChapG retire-to-examples route is the recorded alternative; whichever the stub agent
picks, say so in the file header). Gate order GC-6.6: (a) elaborate fragile signatures, (b)
land `def` bodies, (c) run numeric blocks at `q = 2` AND `q = 3`, (d) sign `axiom` stubs;
0e type-diff per declaration against the fully-qualified `leanfinal` twin.

**Stub order (topological):** I.01, I.02, I.03, I.05, I.06, I.07 (defs; carrier layer) →
I.10 (structure) → I.15–I.18 (theorems; land REAL, not axiom — their proofs are projections
and term applications, provable at stub time modulo dependencies) → I.21 (def) → I.23–I.25
(gates, per GC-6.6(c)).

**BLOCKED-UNTIL-RESOLUTION (do NOT stub as signed):**

| node | blocker | unblocks |
|---|---|---|
| I.01 (`NS7Termination` body) | C §5 descent-history types land at C's stub stage | C stub stage |
| I.05 (`WindowPinningAt` body) | H.09 `StageInterface` stub lands | H stub stage (in progress — `ChapH/*.lean` landings visible at HEAD) |
| I.06 (`GenhnHEAt` body) | H.01/H.09 stubs + the O-1 transcription decision | H stub stage + O-1 |
| I.07 (`GenhnTow1At` body) | C.93's `#check`-suite names | C stub stage |
| I.08/I.09 and I.10's `jd0`/`genhnBox2` fields | **chapter F freeze** (L-1/L-2) | F freeze — **a signed I.10 stub with `True` fields is a false conditionality claim; forbidden** (I.10's ⚠) |
| I.16 (`decided_of_capstoneHypotheses`) | I.02's body must be the literal slice (else `exact` fails) | I.02 typed |
| I.21 (`TypeOfFaithful` body) | the maximal-order carrier (B.56 IF fired, else the discharge unit's own) | orchestrator |

**Numeric block (GC-6.6(c)) for this chapter:** gate I.23's anchors — the `q = 2` triple
`(1/3, 1/3, 1/3)` and `q = 3` triple `(3/8, 3/8, 1/4)` from `gate_two_padic_*`, plus
`undecidedCount O 2 N = q^N` spot values `(2,1)↦2, (2,3)↦8, (3,2)↦9`. Both primes ✓.

---

## 12. TEETH DISPOSITIONS (GC-8)

**Chapter I has no source batteries** (GC-8's own battery-inheritance row: "I: no batteries —
its teeth are the gate nodes"). The full disposition summary, in the closed vocabulary:

| object | disposition |
|---|---|
| the landed `n ≤ 2` slices (drainage, mass, densities, the capstone slice) | **Lean theorem** (landed; re-fired by gate I.23 with the `q = 2`/`q = 3` anchors) |
| the assembly theorems I.15–I.18 | **Lean theorem** (this chapter's contracts) |
| the axiom surface (Lean core + signed cites only) | **executable regression retained**: AXCHK (I.24) + the cite-footprint gate (I.25), output committed under `spec/` |
| the carrier defs I.01–I.10, I.21 | **signed non-applicability** (hypothesis carriers have no teeth ANYWHERE by design — "the fields with no teeth are exactly the capstone's conditionality", H.09's line, which is THIS chapter's organizing fact) |
| GC-11's `e > 1 ∧ f > 1` witness clause at gate I.23 | **signed non-applicability at `n = 2`** (impossible at degree 2: `e·f = 2`); the witnesses live in B.85/C §13/E §10's gates, whose footprints I.24 re-prints on landing |
| the `AllOInterfaces` conjunct | **signed non-applicability as a Lean field**, reconciled row-by-row at §4.3 (the GC-8 rider-(iii) check: every signed-vacuity row reconciles against Display A ✓) |
| the grade-cap rows (HYP.45/89/109/144-BOX-4) | recorded as PROCESS rows in §3; no Lean object carries them |

**The rider-(iii) sanity check, run:** Display A's conjunct list vs the signed-vacuity rows —
the only Display-A content NOT carried as a typed Lean field is the `AllOInterfaces` conjunct
(§4.3, signed) and the two late-binding F fields (placeholders with a forbidden-to-sign rule,
§11). Nothing else on the frozen display lacks a carrier. ✓

---

## 13. FLAGGED FOR THE CODEX CROSS-READ (and for the orchestrator)

1. **The §3 table is the chapter's load-bearing artifact — audit it row by row.** Charges:
   (i) is any of the 154 rows mis-categorized (esp. the 62 NOT-ON-CAPSTONE-PATH rows — each
   must have a verifiable reason code); (ii) is any OPEN-MATH row's "exact missing statement"
   weaker than its ledger row; (iii) the census arithmetic (6+16+25+2+7+36+62 = 154).
2. **The two supplier-gap findings (I-11, O-1/O-2).** Verify independently: (i) that NO
   committed chapter transcribes THEOREM HE3.A at `μ = 3` beyond B's `e₁ = 1` shadow (grep
   the four committed blueprints for `EFF.HE3.16`/`HE3.A`); (ii) that `EFF.GENHN.29`'s
   cap/consultation clauses are consumed by committed H only at H.51's (c) bound.
3. **HYP.07's discharge claim** (the cubic nonintegral-slope branch = B.42+B.58 at
   `(ℓ, m, d) = (3, 1, 1)`, unconditional at `d = 1`): check the instance really needs no
   `B-BOX-1` and that the recursion context supplies B.42's polygon hypotheses.
4. **I.03's under-statement** (the exact-weights clause carried by the count layer, not the
   menu carrier): confirm no consumer reads `MenuLawAt` as carrying weight-correctness.
5. **I.10's `ladder` field quantifier** (ALL instantiations vs degree-`n`-arising ones): the
   strongest uniform reading was chosen; check Display A's "assume uniformly in O" preamble
   licenses it and that E.24's carrier types admit the quantification as written.
6. **The NOT-ON-CAPSTONE-PATH treatment of HYP.78/79** (kept OPEN-MATH at `n ≥ 8`
   conservatively) **and HYP.80** (likewise) — an audit could sign all three fully out; this
   chapter chose the conservative reading. Either answer changes only the `n ≥ 8` box family's
   size.
7. **The CAP-edge emission decision (§10 item 1)** — confirm the checker-visible shape (CAP
   nodes reach the assembly nodes, the assembly nodes reach the hypothesis rows) is the
   intended reachability semantics for the capstone cone.
8. **Gate I.24's location decision** (`leanfinal/AXCHK.lean` + pointer at `spec/`) — REVISION
   2 says `spec/AXCHK.lean`; the deviation is recorded; orchestrator may override.
9. **The stage display (I.20)** — the S3 row's "and nothing else" claim is checkable: it must
   equal §3's OPEN-MATH ∪ CITE census exactly.
10. **The late-binding resolution pass (§9, L-1..L-3)** is owed at D/F freeze — the recorded
    orchestrator item; this chapter is INCOMPLETE by design until it runs (and says so).

---

## FINAL STATE

All 25 nodes composed (§§4–8); the 154-row disposition table complete (§3, census
reconciled); the three COND orphans resolved (§5); `spec/DAG_BLUEPRINT_I.tsv` emitted
(97 rows; `dag_check.py` PASS at composition, regenerated shared files left uncommitted for
the orchestrator's merge run); leanspec stub list with its blocked set (§11); TEETH summary
(§12); cross-read queue (§13, 10 items). LATE-BINDING section §9 is explicitly open until
chapters D and F freeze (items L-1/L-2/L-3). CODEX CROSS-READ OWED.

<!-- RESUME: CHAPTER COMPLETE. Remaining external actions: (i) L-1/L-2/L-3 at D/F freeze;
(ii) orchestrator items O-1..O-5 (§9.3); (iii) cross-read per §13; (iv) leanspec stub stage
per §11; (v) orchestrator dag_build merge re-run. -->

---

### DATED ADDENDUM (2026-08-15, CHAP-B A-F.7 — OPEN-MATH routing per the leaf-layer refutations)

**The `ℓ = 1, m ≥ 2, d ≥ 2` leaf region is OPEN-MATH, carried by `B-BOX-1` (B.61's `hBOX`).**
CHAP-B amendment A-F.7 (2026-08-15): B.59's frozen general-key signature was REFUTED by a compiled
witness (`leanfinal/Uniformity/ChapB/B59_REFUTATION.lean.txt`) and the conjectured general-`φ`
extraction B.44′ was REFUTED by adjudication (counterexample `φ = X²+1`, `g = X²+4` over `ℤ₃`), so
B.59/B.60 are re-signed at the linear key and CHAP-B's unconditional leaf perimeter is now
`{d = 1} ∪ {ℓ = 1, m = 1}` — the integral-slope leaves with key degree `m ≥ 2` and residual degree
`d ≥ 2` are CONDITIONAL on `B-BOX-1`, exactly like the `ℓ ≥ 2, d ≥ 2` region (they were previously
booked unconditional; nothing landed in `leanfinal` is affected — the touched nodes are unfired
stubs). **Owner:** CHAP-B (B.61/B.62 and the H-7 root-label item; ledger neighbours `HYP.01`,
`HYP.12`, both [CORE-SET]). **Exact missing statement:** B.61's `hBOX` at `ℓ = 1` — for `g` monic
`(u,1)`-pure at a key `φ` of degree `m ≥ 2` with irreducible residual of degree `d ≥ 2`:
`∀ g' ∈ monicFactors g, m * d ∣ inertiaDegOf g'`. **Two known repair routes:** (a) the corpus's
`EFF.HE3.68` (LEMMA HE3-4U) unramified base change with split-component summation — needs the
H-6-excluded base-change + descent machinery (B.62-tier own design pass); (b) the order-level root
label of GMN Cor 1.20 / `EFF.HE6.29` (Cor HE6-2″) — the residue class of `φ(θ)/π^u` generates a
degree-`d` extension of `resField φ`, an element of the field not known to lie in the order
`AdjoinRoot g` (the same order/field gap as `HYP.01`). This addendum is cross-referenced from
CHAP-B's D-3 table and amendment A-F.7; it adds no new ledger row — it widens the recorded scope of
the `B-BOX-1` conditionality that §3's disposition already carries through B.61's consumers.

### DATED ADDENDUM (2026-08-16, CHAP-B A-F.10 — GATE-(b) CITE QUEUE ADDITION: [GN15] Thm 2.3 for B.42)

**The chapter-B side dissection (NS-1, the order-1 theorem of the polygon) enters the owner's
gate-(b) queue as the THIRD literature cite** (after HYP.15's C.94 = [AGNPRW] Thm 5.2 and
HYP.38's C.66/C.92 = FGMN). CHAP-B amendment A-F.10 (2026-08-16): B.42's signed proof route is
machine-checked UNREACHABLE (committed obstruction record
`leanfinal/Uniformity/ChapB/B42_ROUTE_BLOCKED.lean.txt` — B.41's `hpure` is unavailable exactly
in the multi-side inductive case, since purity forces a one-sided polygon; independently the
peel's degree arithmetic is unsatisfiable), the missing mechanism (a graded Hensel at a vertex,
Weierstrass-type) has NO corpus proof at general keys (the candidate extraction is A-F.7's
CLOSED-REFUTED B.44′), and the statement is published at COVERS-ALL-O scope. Under Part V gate
(b) — which names [GN15] Thm 2.3 as its own example of an exercisable cite — B.42 is retagged
`[theorem] [cite:GN15 Thm 2.3]`. **Queue mechanics: the owner signs this cite individually;
until signature, CHAP-B's §8/§9/§10 upper layer (B.63 up, gates included) stays gated — on the
signature instead of on an impossible proof.** Conditionality inheritance list: CHAP-B H-14.
Census impact on §3.11: **CITE (gate (b)) count 2 → 3** (this cite is chapter-B-owned, not a new
ledger row; HYP.13's row is annotated in place). Nothing landed in `leanfinal` is affected.

**THE EXACT LEAN STATEMENT to be signed** (the leanspec stub `LeanspecB.exists_slope_factorization`
is the signable artifact, byte-identical modulo namespace to the `leanfinal` landing; ENV-C =
complete DVR `O`, finite residue field; vocabulary: `dev`/`npHgt`/`sideSet`/`sideMin`/`IsPure`/
`resPoly` per CHAP-B §§3–4, landed):

```lean
theorem exists_slope_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O),
      (∀ p ∈ s, 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 * q.2 ≠ q.1 * p.2) ∧
      (∀ p ∈ s, (F p).Monic ∧ IsPure φ (F p) p.1 p.2 ∧
        φ.natDegree ∣ (F p).natDegree ∧
        dev φ (F p) 0 ≠ 0 ∧ 0 < (F p).natDegree) ∧
      f = ∏ p ∈ s, F p ∧
      (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
        (1 < (sideSet φ f u ℓ).card ↔ (u, ℓ) ∈ s)) ∧
      (∀ p ∈ s, ∀ (hne : (sideSet φ f p.1 p.2).Nonempty)
        (hne' : (sideSet φ (F p) p.1 p.2).Nonempty) (H₀ H₀' : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
        npHgt φ (F p) (sideMin φ (F p) p.1 p.2 hne') = (H₀' : ℕ∞) →
        ∃ c : (resField φ)ˣ,
          resPoly π φ f p.1 p.2 hne H₀ =
            Polynomial.C (c : resField φ) * resPoly π φ (F p) p.1 p.2 hne' H₀')
```

**FAITHFULNESS ENTRY (draft, for the fresh-context audit + signature).**

* **Published source (primary).** [GN15] J. Guàrdia, E. Nart, *Genetics of polynomials over
  local fields*, Contemp. Math. **637** (2015) 207–241, **Theorem 2.3**. Standing setting
  (verbatim, `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §1): *"an arbitrary discrete valued
  field `(K,v)`"* — our complete `O` is the case `K = K_v`. Statement (verbatim, NS-2): *"every
  monic polynomial `g ∈ O_v[x]` factorizes into a product of monic polynomials in `O_v[x]`:
  `g = g₀ · φ^{ord_φ(g)} · ∏_{(λ,ψ)} g_{λ,ψ}`, where `−λ` runs on the slopes of `N⁻(g)` and `ψ`
  runs on the prime factors of `R_λ(g)` … `deg g₀ = deg g − ℓ(N⁻(g))·deg φ`,
  `deg g_{λ,ψ} = e_λ·ord_ψ(R_λ(g))·deg ψ·deg φ`"* — instantiated at MacLane chain length
  `r = 0` (the Gauss valuation; `φ` = an order-1 key). *[A-3 disposition, 2026-08-16 — **this
  source line is one citation short**: the standing hypothesis `φ ≁_µ φ_r` reads `φ ≁_{µ₀} x` at
  `r = 0` and so excludes the keys with `φ̄ = x̄`; add **[FGMN] Thm 6.6** (arXiv:1305.0775v3 —
  same display, hypothesis "proper key polynomial", satisfied by every `φ ∈ KP(µ₀)`) as a
  CO-PRIMARY covering the full `IsKey` range. See the "STANDING HYPOTHESIS ON `φ`" bullet below.]*
  **Secondary displays:** GMN Thm 1.15
  (`docs/GMN_citations.md` §1: *"`f_φ = F_1 … F_g` factors in `O[x]` with `N_φ(F_i)` one-sided
  of slope `λ_i` and `R_{λ_i}(F_i) ∼ R_{λ_i}(f)`"* — the per-slope grouping and clauses 3/6
  transcribed here, at ℚ_p scope); [AGNPRW] Thm 4.4 (arbitrary valued field — NS-1's verbatim
  quote) and [FGMN] Thm 2.8 / [AGNPRW] Thm 4.6 + Cor 2.9 (NS-9 residual multiplicativity, the
  general-scope leg of clause 6).
* **Clause mapping (import ↔ source).** `h0 : dev φ f 0 ≠ 0` ↔ `ord_φ(f) = 0` (the source peels
  `φ^{ord_φ}` explicitly; `hres` + `h0` then force `deg g₀ = 0`, `g₀ = 1` — verified end-to-end
  at CHAP-B amendment A-F.9 (III)); `s` ↔ the (negated-)slope set, in lowest terms `(u,ℓ)`,
  positive by `hres` (A-F.6 verification); `F p` ↔ `∏_ψ g_{λ,ψ}` at fixed `λ` (GMN Thm 1.15's
  `F_i`); clause 3's `IsPure` ↔ "`N_φ(F_i)` one-sided of slope `λ_i`" (the dictionary is B.34's
  definitional reading; the CONVERSE direction pure ⟹ one-point-sides-elsewhere is
  machine-checked — CHAP-B NODE B.42a, committed proof); clause 3's divisibility/positivity/
  `dev ≠ 0` ↔ the source's degree law + one-sidedness bookkeeping (A-F.9 (IV)); clause 4 ↔ the
  product display; clause 5 (`↔`) ↔ "`−λ` runs on the slopes" + N⁻ additivity (NS-9); clause 6
  ↔ `R_{λ_i}(F_i) ∼ R_{λ_i}(f)` (GMN Thm 1.15 verbatim; generally from `R(gh) = R(g)R(h)` with
  the co-factors' `R` constant at `λ_i`). `∼` = equality up to a unit of
  `resField φ = F_φ`, matching the `∃ c : (resField φ)ˣ` form.
* **Clause mapping, the STANDING HYPOTHESIS ON `φ`** — `hφ : IsKey φ` ↔ `φ ∈ KP(µ)`, `φ ≁_µ φ_r`
  at `r = 0` *(added [A-3 disposition, 2026-08-16]; this bullet REPLACES the audit's omission flag,
  caveat (1) last sentence. Sources read directly: arXiv:1309.4340v2 = [GN15], and
  `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` = [FGMN] arXiv v3. **MIXED VERDICT —
  half of the hypothesis is an exact match, half is NOT implied and needs a second cite; read the
  fourth paragraph before signing.**)*
  * **(i) `IsKey φ ⟺ φ ∈ KP(µ₀)` — EXACT, verbatim, both directions.** [GN15] §1.1 (after Def 1.1):
    *"A key polynomial for `µ` is a monic polynomial `φ ∈ K[x]` which is `µ`-minimal and
    `µ`-irreducible. We denote by `KP(µ)` the set of all key polynomials for `µ`. For instance,
    `KP(µ₀)` is the set of all monic polynomials `g ∈ O[x]` such that `[ḡ]` is irreducible in
    `F[x]`."* (The overline on the second `g` is dropped by PDF text extraction in **both** this
    source and the identical [FGMN] §1.2 sentence; the reading is forced — "irreducible in `F[x]`"
    is a statement about the reduction. Non-textual leg: `g` itself lies in `O[x]`, where
    irreducibility over `F[x]` is not even typed.) This is `IsKey` clause-for-clause —
    `monic : φ.Monic` ↔ "monic", `irred : Irreducible (φ.map (IsLocalRing.residue O))` ↔ "`ḡ`
    irreducible in `F[x]`", and `pos : 0 < φ.natDegree` is *implied* by the source side (an
    irreducible in `F[x]` has degree `≥ 1`, and monicity gives `deg φ̄ = deg φ`), so it adds no
    strength and loses none: the two predicates have the same extension. Independent corroboration
    at the same `r`: [FGMN] Lemma 5.3 (arXiv v3) read at `r = 0` (`m₀ = 1`, `φ₀ = x`) — its two
    branches, *"deg g = m_r and g ∼_µ φ_r"* and *"s(g) = 0, deg g = s′(g)m_r and R_r(g) is
    irreducible in F_r[y]"*, have union exactly "`ḡ` irreducible in `F[x]`".
  * **(ii) `φ ≁_µ φ_r` at `r = 0` is NOT vacuous and is NOT implied by `IsKey` — it excludes
    `{x + a : a ∈ m}`.** [GN15] §1.4 fixes the `r = 0` slot of the chain data: *"Take
    `π₀ = π₁ = π`, `Φ₀ = φ₀ = γ₀ = x`"* — so at `r = 0` the hypothesis reads `φ ≁_{µ₀} x`. With
    `∼_µ` per [GN15] Def 1.1 (*"g, h are µ-equivalent, and we write g ∼_µ h, if H_µ(g) = H_µ(h)"*)
    and Thm 1.10 at `r = 0` (`∆₀ ≅ F[y]`, `g + P₀⁺ ↦ R₀(g)(y)`, with `R₀(g) = g/π^{µ₀(g)}` per
    §1.4, i.e. `R₀(φ) = φ̄` for monic `φ`), for monic `φ ∈ O[x]`:
    `φ ∼_{µ₀} x ⟺ µ₀(φ − x) > 0 ⟺ φ̄ = y in F[y] ⟺ deg φ = 1 and φ ≡ x (mod m)`
    (for `deg φ ≥ 2` the difference `φ − x` is monic, so `µ₀(φ − x) = 0`). **Hence the source
    theorem, as literally stated, does not cover the sub-case `φ ∈ {x + a : a ∈ m}` — nonempty,
    containing `φ = x`, and in fact the import's MOST-USED instance (every `f̄ = φ̄^μ` with
    `φ̄ = x̄`: Eisenstein `f`, the whole totally-ramified branch, the landed `m = ℓ = 1` instance
    B.44).** *This one line is a repo-side derivation from the quoted definitions, labelled as
    such — not a source quote.*
  * **(iii) The excluded sub-case is covered by the SAME theorem in its intrinsic form, at the same
    (COVERS-ALL-O) scope — so there is NO mathematical gap.** [GN15] §2 opens *"All results in this
    section are extracted from [3]"* ([3] = [FGMN]). The FGMN original is **Thm 6.6** (arXiv v3):
    *"Let `µ` be an inductive valuation and let `φ` be a **proper** key polynomial for `µ`. Then,
    every monic polynomial `g ∈ O_v[x]` factorizes into a product of monic polynomials in
    `O_v[x]`: `g = g₀ φ^{ord_φ(g)} ∏_{(λ,L)} g_{λ,L}` … `deg g₀ = deg g − ℓ(N⁻_{µ,φ}(g)) deg φ`,
    `deg g_{λ,L} = e_λ ord_L(R_{µ_λ}(g)) deg L deg φ`. Moreover, if `ord_L(R_{µ_λ}(g)) = 1`, then
    `g_{λ,L}` is irreducible in `O_v[x]`."* — identical display and identical degree laws to the
    [GN15] Thm 2.3 quoted above (`Max(∆(µ_λ)) ∋ L ↔ ψ ∈ F_{r+1}[y]` with `deg L = deg ψ` by [FGMN]
    Def 6.5), with **"proper"** in place of **"`φ ≁_µ φ_r`"**. And at `r = 0` EVERY key is proper,
    on two independent legs: [FGMN] Def 5.10 — *"We say that `φ` is a proper key polynomial for `µ`
    if `deg φ` is a multiple of `e_r(µ)m_r(µ)`. … We say that `φ` is a strong key polynomial for
    `µ` if `r = 0` or `deg φ > m_r(µ)`. … By Lemma 5.3, `KP(µ)_str ⊂ KP(µ)_pr ⊂ KP(µ)`. …
    **Note that `KP(µ₀)_str = KP(µ₀)`.**"* — leg (a) is that quoted final sentence plus the quoted
    inclusion `str ⊂ pr`; leg (b) is direct arithmetic, `e₀ = m₀ = 1` ([GN15] §1.4: *"Take
    `e₀ = m₀ = 1` and `ν₀ = λ₀ = h₀ = w₀ = V₀ = 0`"*), so "multiple of `e₀m₀ = 1`" holds for any
    degree. [GN15]'s own Def 2.4 says the same thing in its own voice: *"a key polynomial `φ` for
    an inductive valuation `µ` of depth `r` is strong if **either `r = 0`** or `deg φ > m_r(µ)`"*.
    Scope is not narrowed by the swap: [FGMN]'s standing setting is *"Let `K` be a field equipped
    with a discrete valuation `v`"* (abstract/§1) — the same arbitrary discrete valued field as
    [GN15], hence COVERS-ALL-O and ENV-C in both characteristics.
  * **(iv) Structural corroboration that `r = 0` really is the exempt slot.** (a) [GN15]'s own
    chain definition imposes the `≁` condition only from the first augmentation onward: *"A chain
    of augmented valuations as in (1.1) is called a MacLane chain of length `r` of `µ` if
    `φ_{i+1} ≁_{µ_i} φ_i` for all **`1 ≤ i < r`**"* — the `i = 0` slot (`φ₀ = x`) is deliberately
    exempt, so appending `(φ, λ)` to `µ₀` is a MacLane chain of length 1 for *every*
    `φ ∈ KP(µ₀)`; and the theory carries the `φ̄ = x` case rather than excluding it (§1.4: *"For
    `i = 0` we have `z₀ = 0` (and `ψ₀ = y`) if and only if `φ̄₁ = x` in `F[x]`"*). (b) The
    theorem's residue-field display stays correct in the excluded case: since `R₀(φ) = φ̄`, when
    `φ̄ = y` the two branches of [GN15] Cor 1.12(5) (*"`R(φ) = R_r(φ)(y_r) ∆` if `φ ≁_µ φ_r`, and
    `R(φ) = y_r ∆` otherwise"*) **coincide**, and `F_{r+1} = F_r[y]/(R_r(φ)) = F[y]/(y) = F = F_φ`
    — agreeing with [FGMN] Cor 5.5 (*"take `ψ = R_r(φ)`, if `φ ≁_µ φ_r`, and `ψ = y`, if
    `φ ∼_µ φ_r` … `F_φ ≃ F_r[y]/(ψ)` and `f(φ) = f₀⋯f_{r−1} deg ψ`"*), which gives `f(φ) = 1` for
    `φ = x` — correct. (c) Mixed-characteristic-only corroboration: GMN Thm 1.15 (printed TAMS,
    verified at A-3) imposes **no** hypothesis on `φ` beyond monic with irreducible reduction, so
    it covers `φ = x` outright — but its standing setting is *"We fix a finite extension `K` of
    `ℚ_p` as a base field"* (`docs/references/HigherNewton.tex` §1.1), so it does **not** reach
    ENV-C's equal-characteristic case. **[FGMN] Thm 6.6 is therefore the load-bearing leg, not
    GMN.**
  * **(v) CONSEQUENCE FOR THE SIGNATURE — one line, owner's call, no Lean statement change.** The
    import's `∀ φ, IsKey φ` range is *sound* but is **not** covered by "[GN15] Thm 2.3" alone.
    Sign the cite as **[FGMN] Thm 6.6 (proper key polynomials; every Gauss key is proper) for the
    whole `IsKey` range, with [GN15] Thm 2.3 as the chain-relative restatement covering
    `φ ≁_{µ₀} x`** — i.e. add the FGMN properness leg to the primary source line above. Do NOT
    sign [GN15] Thm 2.3 as if it covered `∀ φ, IsKey φ`. *No change to
    `LeanspecB.exists_slope_factorization` is required or implied — the statement is faithful; only
    the source line is short one citation.* **Numbering caveat, owed (same class as this file's
    other FGMN rows):** [FGMN]'s published (J. Algebra) numbers drift uniformly by `−1` across
    §§5–6 per `docs/CITE_NUMBERING_AUDIT_2026-08-16.md` §4 (Lemma 5.3 → 5.2, Cor 5.4 → 5.3,
    Prop 5.7 → 5.6, Thm 5.8 → 5.7, Thm 6.3 → 6.2, Cor 6.4 → 6.3), so print is **PREDICTED**
    Def 5.10 → **Def 5.9** and Thm 6.6 → **Thm 6.5** — *predicted, NOT verified* (arXiv 1305.0775
    has only v1–v3, none carrying the published numbering; confirmed against the arXiv abs page
    this session). Confirm both numbers against the Elsevier PDF — the same two-minute check §7 of
    the numbering audit already lists as the FGMN residual — before signature.
* **Known caveats, disclosed.** (1) ~~**Numbering verification owed (the HYP.17 class,
  extended):**~~ **DONE — [verified: A-3, 2026-08-16]** (`docs/CITE_NUMBERING_AUDIT_2026-08-16.md`).
  [GN15] Thm 2.3: **VERIFIED** — volume/pages from the publisher (AMS CONM 637 ToC: 207–241;
  Crossref DOI 10.1090/conm/637/12767; zbMATH Zbl 1396.11143), and the statement quoted above
  confirmed verbatim in TWO copies straddling the referee round — the `upcommons.upc.edu` author
  PDF **and arXiv:1309.4340v2 ("revised according to suggestions by a referee")**, which the repo's
  docs did not know existed; cite it as the freely checkable witness. Printed AMS chapter itself
  not read (LibLynx paywall) → residual risk LOW. GMN Thm 1.15: **VERIFIED against the printed
  TAMS pages** (free AMS PDF; header "Volume 364, Number 1, January 2012, Pages 361–416"), clauses
  (1)(2)(3) as transcribed — this also discharges `docs/GMN_citations.md`'s printed-TAMS caveat.
  **Secondary displays DRIFTED, do not sign the numbers as written:** [AGNPRW] Thm 4.4 →
  **Thm 4.10**, Thm 4.6 → **Thm 4.15**, Cor 2.9 → **Cor 2.17** (published = Found. Comput. Math.
  **25 (2025), no. 2, 631–681**; the repo's numbers are arXiv-v1 numbers and arXiv was never
  updated); [FGMN] Thm 2.8 → **Thm 2.8** (stable). ~~One non-numbering observation for the math
  owner: the source Thm 2.3 carries the hypothesis **`φ ∈ KP(µ)` with `φ ≁_µ φ_r`**, which the
  display quoted above omits.~~ **DISPOSED — [A-3 disposition, 2026-08-16]**, in the
  "STANDING HYPOTHESIS ON `φ`" clause-mapping bullet above. Verdict in one line: `IsKey φ ⟺ φ ∈
  KP(µ₀)` is EXACT, but `φ ≁_{µ₀} φ₀ = x` is **NOT** implied by `IsKey` — it excludes
  `{x + a : a ∈ m}` (`φ = x` itself, the import's commonest instance) — so the range is faithful
  mathematics but needs a SECOND cite: **[FGMN] Thm 6.6** ("proper" key polynomial; every Gauss key
  is proper, `KP(µ₀)_str = KP(µ₀)`, `e₀ = m₀ = 1`), same arbitrary-discrete-valued-field scope. Do
  not sign [GN15] Thm 2.3 alone as covering `∀ φ, IsKey φ`. No Lean statement change implied. (2)
  **Clause 6 is the one clause of the import never refutation-tested** (clauses 1–5 survived
  two machine-refutation waves, A-F.6/A-F.9, and were then source-verified clause-by-clause at
  A-F.9 (II)–(III)); it sits inside the digit-read transcription's verified faithful scope
  (`u ≥ 1`, `m ∣ deg`, PA-1 `sideMin` pins) — **audit this clause first** (transcription-shear
  risk: the chapter's `resPoly` is the digit read at the side line, not the intrinsic graded
  normalization; the A-F.6 record documents the two known shear modes and why clause 1/clause 3
  hypotheses exclude them). (3) Sign convention: the chapter's slopes `(u,ℓ)` are the source's
  `−λ` in lowest terms; `e_λ = ℓ`. (4) The import is stated for `f̄ = φ̄^μ` (the single-branch
  case); the source's arbitrary monic `g` is strictly more general — no strengthening is
  smuggled in.
* **Corroboration on record.** `W12-SHAPE` (0/164 over 23 rows, BOTH directions — the
  completeness half is exactly clause 5); `HE6-SEP` (4,232 strict-excess certificates); the
  quartic PARI oracle harness (`verification/quartic_oracle.py` family); the landed `m = ℓ = 1`
  instance B.44 (deriving it from the axiom is the booked decorrelation check, CHAP-B B.42a's
  TEETH); two refuted earlier transcriptions caught by the wave process BEFORE import (evidence
  the audit pipeline has teeth). **Retirement route** (fresh proof, retires the cite): the
  obstruction record's "missing mechanism" display — the general-key graded vertex split,
  `B-BOX-1`-tier own design.

This addendum adds no new ledger row; it is cross-referenced from CHAP-B's NODE B.42, amendment
A-F.10, and honesty item H-14.

<!-- SENTINEL: BP-I END OF FILE -->






