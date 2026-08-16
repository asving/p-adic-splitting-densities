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
**⚠ READ AMENDMENT A-I.1 (2026-08-16, at the end of this file) BEFORE CONSUMING ANY NODE.** It
adjudicates the stage-0e stub gate's blueprint-side defects and RE-SIGNS three of them: NODE
I.10's field list (the `ladder` field's application and its arising-configuration binding; a NEW
`deepTwist` field for the `𝒲_{≤i}` conjunct that had no carrier; NEW socket nodes I.10a/I.10b),
NODE I.03's `(A1)` clause (which was provably vacuous as signed), and NODE I.01's resolution
instruction (which pointed at a machine-REFUTED statement). It also records defect **I-D13**:
as signed, the Display-A carrier fields are REFUTABLE, so the capstone hypothesis block is
contradictory until chapter C types the two sockets — **no positive conditional claim may be
made from I.17 until then.**

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

*[A-I.1 rider, 2026-08-16: **27 nodes**. The amendment adds two `def` nodes — **I.10a**
`CanonicalLadderConfig` and **I.10b** `CanonicalDeepTwistConfig`, the arising-configuration
sockets that guard I.10's two ladder fields (GC-13(c) placeholders, bodies owed at chapter C's
freeze). They live in §4 with I.10, share its Lean file, and need DAG rows at the
orchestrator's next `dag_build` run.]*

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

> **[ANNOTATED 2026-08-16 — unit T-1 BLUEPRINT-CONVERSION (OM-2, owner mandate #66):
> REDUCED-TO CHAP-H §17, nodes H.100–H.124.]** The "NO NODE ANYWHERE" sentence above is
> HISTORICAL as of this date: OM-2's certified skeleton
> (`docs/openmath-campaign/OM-2_genind-b_2026-08-16.md`, 612/612) is converted to signed
> CHAP-H contracts. The composed implication now has the node **H.124**
> (`inductionPackage_of_clusterRates`: `(IH) + FullClusterRateBound n ⟹ InductionPackage n`
> — the reduction AS A CONDITIONAL, hypothesis carried, the H.98/I-2 fence intact), fed by
> the level-0 transport **H.100–H.105**, the cluster event grammar **H.106–H.117**, and the
> conservative-verdict/rate/bridge layer **H.118–H.123** (unconditional at `d = 1, m ≤ 3`;
> the S-1 bridge H.123 is an INEQUALITY, F-2-fenced, and consumes the owner-signed B.42
> axiom footprint-visibly). **The NAMED RESIDUAL of T-1 after this reduction** — what
> discharging `FullClusterRateBound n` still costs beyond `m ≤ 3, d = 1`: the stage legs
> `HYP.36`/`HYP.32`/`HYP.33`/`HYP.30` (CS mass at `m ≥ 4`, per genre, via H.72 +
> `StageInterface`), `HYP.81` (`μ ≥ 3`, first live `n = 6`), `HYP.82` (`n ≥ 8` tower),
> `B-BOX-1` (`d ≥ 2` leaf reads), the W12 transcription debt (OM-2 D-1, unowned), and the
> TRACK-V value rows `HYP.24/25/26/35` (consumed by `hdec`, not by this step). Blueprint
> mechanics: FINDING F-H17.1 + PA-H17.1 (H.71's fixed `n₀` vs the window-dependent α-range)
> are recorded at CHAP-H §17.0; the §17 0e gate is OPEN. This annotation updates the
> completeness sentence: closing the OPEN-MATH rows above becomes SUFFICIENT through
> H.124 + H.98, whose composition is now a contract, not future prose.

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
*[A-C.1 rider, 2026-08-16: ~~the wait is OVER — C's §5 carriers landed (`DescentState`,
`DescentStep`, `NS7TerminationStatement`, amendment A-C.1 at CHAP-C NODE C.94), and the typed
body is `NS7TerminationStatement`'s matrix; see this file's 2026-08-16 A-C.1 addendum. The
placeholder may be resolved at the next stub-resolution pass.~~]*
**⛔ STRUCK BY AMENDMENT A-I.1 (2026-08-16), defect I-D3/I-D6 series — the struck text is kept
verbatim above because a fleet agent that followed it would land an inconsistency.**
`Uniformity.Density.Tower.NS7TerminationStatement` was MACHINE-REFUTED at A-C.6
(`leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt` proves it implies `False`, absolutely,
over `ℤ_[2]`, Lean-core and sorry-free) and the name does not exist in `leanfinal` at HEAD.
**The live resolution target is the A-C.6 REDRAFT** `LeanspecC.NS7TerminationStatementR` over
`LeanspecC.DescentStepR` (`leanspec/Leanspec/ChapC.lean`, commit `958cc39b`), which is
**cite-conditional and awaiting the owner's gate-(b) signature**: until that signature, I.01
stays at its signed `True` placeholder and the stub-resolution pass may NOT type it. On
signature the resolution is `NS7Termination := NS7TerminationStatementR`'s matrix (bundle
quantifier frozen), the discharging axiom is `agnprw_termination : NS7TerminationStatementR`,
and I.01's consumers move from `#axiom_core` to `#axiom_reg … [agnprw_termination]` (gate I.25).
See AMENDMENT A-I.1 §I-D6.

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

**⛔ THE SIGNATURE ABOVE IS VOIDED AND RE-SIGNED BY AMENDMENT A-I.1 (2026-08-16), defects I-D5
and I-D9.** The block is kept verbatim because it is the object of a machine refutation: as
written the `(A1)`-admissibility clause is **provably vacuous** (`r = 0, F = []` satisfies it
for every `S`, so `MenuLawAt n` is EQUAL to its bare menu clause — proved in the 0e gate and
preserved as `MenuLawAtVoided` in `leanspec/Leanspec/ChapI.lean`), and it does not elaborate
(`A1Family` is a plain `def`; instance search will not find `Membership` through it). **The
signed form is:**

```lean
namespace Uniformity.Density

/-- `A1_n` (Display A; ledger HYP.26; COND:A1_n's resolution — I.13): a q-independent
`(A1)`-admissible family list **whose σ-labels ENUMERATE** a covering menu at degree `n`
[A-I.1: the enumeration is two-directional — the STATEMENT's "whose cells' σ-labels enumerate
`S`" — the ⊆ half alone is vacuous]. The shape clause uses chapter H's landed
`A1Family`/`A1Cell` (H.93, with W-12 r4's σ-label field); the `@id` spelling is A-I.1's
elaboration repair for `A1Family`'s plain-`def` reducibility (I-D5), and is type-identical. -/
def MenuLawAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧
    (∀ σ ∈ S, ∃ C ∈ @id (List (Induction.A1Cell r)) F, C.σ = σ) ∧
    (∀ σ ∈ S, σ.degree = n) ∧
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

**⛔ THE `ladder` FIELD ABOVE IS VOIDED AND RE-SIGNED, AND ONE FIELD IS ADDED, BY AMENDMENT
A-I.1 (2026-08-16) — defects I-D3, I-D4, I-D13. This is an owner gate-(a) field-list change.**
The block above is kept verbatim because it is the object of the amendment's machine
refutation: `Ladder.LadderSupply C B` is UNDERAPPLIED by eight arguments against landed E.24,
and its `∀`-over-all-configurations reading is REFUTABLE (§I-D13), i.e. it makes
`CapstoneHypotheses n` uninhabited. **The signed form is** (universes
`CapstoneHypotheses.{uW, uG, uKt, uL}`; the sockets are NODES I.10a/I.10b):

```lean
structure CapstoneHypotheses (n : ℕ) : Prop where
  ns7 : NS7Termination
  -- [A-I.1] E.24's application REPAIRED (level data bound, six universes spelled), and GUARDED
  -- by I.10a: the supply is demanded at the ARISING configurations, at chapter C's canonical
  -- node-point residue read — never at an arbitrary `(C, B, ρ)`.
  ladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q
  -- [A-I.1, defect I-D4 — THE FIELD THAT WAS MISSING] Display A's `∀ i ≥ 3` conjunct, BOTH
  -- halves, at E.63's `DeepTwistConjunct` (E.61's typed ϑ socket ∧ E.62's typed `𝒲` socket,
  -- one use-height family `q` serving both, per E.63's own fence).
  deepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w n →
      Ladder.DeepTwistConjunct v ρ q A R w
  a0 : DecidedSliceAt n
  a1 : MenuLawAt n                      -- at A-I.1's re-signed I.03 (the enumeration)
  a2 : DrainageAt n
  jd0 : True                            -- ⚠ UNCHANGED placeholder; A-I.1 §I-D7 rules why
  genhnBox2 : 6 ≤ n → True              -- ⚠ UNCHANGED placeholder; A-I.1 §I-D7/§I-D8 rule why
  windowPinning : WindowPinningAt n
  genhnHE : 6 ≤ n → GenhnHEAt n
  genhnTow1 : 8 ≤ n → GenhnTow1At n
```

**NEW NODES I.10a / I.10b [def] [A-I.1] — the arising-configuration sockets** (GC-13(c)
placeholders, `Prop`-valued, bodies owed at chapter C's tower-instantiation freeze — the same
GC-13/GC-14 pass that typed E.61/E.62):

```lean
/-- I.10a: the block `(C, B)` is the one chapter C's OM ladder produces for a degree-`n` input
over `O`, and `(G, K_t, L, N, v, ρ, q)` is that tower's level data with `ρ` the CANONICAL
node-point residue datum (OM-8's pinning). -/
def CanonicalLadderConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  True  -- ⚠ SOCKET, BLOCKED-UNTIL-RESOLUTION (chapter C's freeze). FROZEN: name, argument
        -- block, degree index, Prop kind.

/-- I.10b: I.10a's configuration together with the level-indexed gauge-arena family `(A, R, w)`
chapter D's `𝒲` leg reads. The conjunction spelling makes the refinement
`CanonicalDeepTwistConfig → CanonicalLadderConfig` hold BY CONSTRUCTION. -/
def CanonicalDeepTwistConfig … (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt)
    (w : ℕ → Ktˣ) (n : ℕ) : Prop :=
  CanonicalLadderConfig C B G Kt L N v ρ q n ∧ True   -- ⚠ second conjunct = the arena half's
                                                      -- socket, owed at the same freeze
```

Both are elaborated, with the whole consumption suite, in `leanspec/Leanspec/ChapI.lean`
(A-I.1 pass; `lake build Leanspec.ChapI` green).

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

> **⛔ DATED NOTE (2026-08-16, Display-A carrier adjudication — THE CONSUMPTION RULE FOR
> THIS BLOCK; supersedes the OM-4 addendum's FINDING-0 fence, which it executes).** Two of
> this structure's Display-A conjunct carriers were machine-refuted VACUOUS as committed and
> have been re-signed; chapter I consumes them at the re-signed forms ONLY:
>
> 1. **`LB1 ∧ MP1` (rows HYP.41/HYP.42; the `ladder` field's `.lb1`/`.mp1` projections
>    through E.24/E.44):** consumed at the **A-E.2 forms** — `LB1Carrier` concluding
>    `Nonempty (BlockSuite I)` (the full S1.7A record) and `MP1Carrier` concluding
>    `Nonempty (MidPeelEmission B B')` (`EFF.T2.23` items 2–5, item 5 = `Φ″`-irreducibility
>    + emission, the cite-consuming clause) — and consumed
>    **universe-polymorphically** in `uW` (honesty E-12: this structure's Lean form carries
>    the `{uO, uK, uW}` parameters; any fixed `uW` choice must be recorded).  The committed
>    shadows are NAMED-AND-VOIDED as `OM4Shadow.LB1CarrierVoided`/`MP1CarrierVoided`/
>    `LadderObligationsVoided` (`verification/om4_shadow_vacuity.lean` proves all three
>    trivially — that file is the permanent refutation record): **no discharge, gate, or
>    census row may cite them**, and any proposed weakening of the A-E.2 forms must first
>    show those vacuity witnesses fail against it.
> 2. **`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` (rows HYP.57/HYP.63; the `ladder` field's `.vartheta`
>    projection, with E.62's/C.89's `𝒲` socket):** consumed at the **A-D.2 form** —
>    D.62's SITEWISE `HVarthetaRes G K L N v ρ q` against the level's GIVEN ambient residue
>    datum `ρ` at the level's use-height `q` (DECISION D-2; `EFF.T1.09`'s display verbatim),
>    conjoined per D.63's fence.  The committed existential form is NAMED-AND-VOIDED as
>    `HVarthetaResVoided` (provably equivalent to the exact-height fact — D-D12): **no
>    consumer or discharge may cite it**.  In particular, when E.61's BLOCKED socket
>    (`VarthetaRes i`, `supplied : True`) is typed at the GC-13/GC-14 resolution, it must be
>    typed against the A-D.2 sitewise carrier with chapter C's/D's level-`i` instantiation
>    data — typing it against the voided form (or leaving an untyped `True`) would
>    reintroduce a vacuous Display-A conjunct, which is exactly what this note fences.
>
> Non-triviality of both re-signed forms is machine-certified
> (`verification/om4_resign_nontriviality.lean`: each is FALSE at a concrete instance, so
> the conjuncts now track genuine conditionality).  Records: CHAP-E AMENDMENT A-E.2,
> CHAP-D DECISION D-2 + AMENDMENT A-D.2 (both 2026-08-16).  Effect on this node: I.10's
> field list is UNCHANGED; the rule binds what the fields MEAN — §3.4's HYP.41/42/57/63
> rows and §12's reconciliation read their carriers as the re-signed forms by reference.
>
> **ARC NOTE (2026-08-16, unit OM-8 — the HYP.57/HYP.63 conjunct's state advanced; rows
> stay CARRY).** (1) The ϑ-half's named adjudication (does GENTOW5 S2.1 imply
> `(H-VARTHETA-RES)_i`?) is PERFORMED: YES at every DEF GENTOW5-1 instantiation with the
> canonical node-point residue read, NO at arbitrary `ρ` (the ρ-defeat is now machine-shown
> at REAL tower exponents — `verification/om8_vartheta_deep.py` LEG D2 — which is this
> note's fence with an executable reason: **typing E.61's socket at anything but chapter
> C's canonical residue data leaves the conjunct undischargeable**). The lattice core is
> Lean-general (`leanfinal/Uniformity/ChapD/D62w.lean`: `triangular_descent`/`dvd_stage`;
> depths 2/3 concrete; `i ∈ {1,2}` corpus proofs transcribed), and NODE D.62 itself is
> landed in leanfinal at the A-D.2 signature (`D62.lean`; voided form NOT re-landed).
> (2) The `𝒲`-half's empty-base closure (T5 S12.1's re-verification obligation) is
> PERFORMED: interleaved-induction skeleton PROVED (`wle_of_interleaved`), footprint walk
> recorded; when this chapter's discharge node composes the `𝒲` citation
> {GENTOW2 base, WI step (SOL row 18, 2/2), frozen (a)→(b) chain}, it should commission
> ONE fresh-context hostile pass on OM-8's C-3/C-5 index-alignment reading. New machine
> coverage both halves: first `f₄ = 3` three-slot frame, first non-prime-field deep ϑ
> (`F₉`), first equal-characteristic deep-twist rows. Ledger ARC NOTEs at HYP.57/HYP.63;
> unit record `docs/openmath-campaign/OM-8_deep-twist_2026-08-16.md`.

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

*[A-I.1 rider, 2026-08-16, defect I-D9: what this resolution DELIVERS is stated exactly. As
committed, I.03's shape clause was one-directional and therefore VACUOUS (machine-proved), so
`COND:A1_n` resolved to the MENU clause alone. A-I.1 re-signs I.03 at the two-directional
enumeration, so the resolution now delivers **menu + σ-label enumeration**; the WEIGHT tie
(HYP.23/32/35) is still NOT delivered and I.03's ⚠ SIGNATURE NOTE still governs.]*

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

**No stage claims more than its row.** ~~The sentence a report may use verbatim: *"proved
unconditionally at `n ≤ 2`; at general `n` the capstone is machine-checkably equivalent to
the frozen Display-A block, whose open rows are enumerated at §3 census: 36 OPEN-MATH + 2
CITEs + 7 chapter-I audit items."*~~

**⛔ THE S3 ROW AND THE REPORT SENTENCE ARE STRUCK AS FALSE-AS-WRITTEN BY AMENDMENT A-I.1
(2026-08-16), defects I-D4 and I-D13; the corrected forms are below.** Two independent
falsities, both machine-found at the 0e gate and adjudicated at A-I.1:

1. *"exactly the §4 field list"* was SHORT of Display A by one conjunct — `𝒲_{≤i}` (HYP.63) had
   no field (I-D4). **Cured**: A-I.1's `deepTwist` field carries it (with the ϑ-half) at E.63.
2. *"machine-checkably equivalent to the frozen Display-A block"* claimed an EQUIVALENCE that
   I.17 never proved (I.17 is one direction: block ⟹ statement) — and, worse, while the
   `ladder` field quantifies over all configurations the block is REFUTABLE (I-D13), so the
   implication fires from a contradiction and reports nothing.

**Corrected S3 row:** `UniformityStatement` via I.17, modulo **exactly the A-I.1 field list**:
`ns7`; `ladder` (HE7A + LB1 + MP1 + the ϑ-half) and `deepTwist` (`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}`),
**both at the arising configurations of I.10a/I.10b — sockets NOT YET TYPED**; `a0`/`a1`/`a2` at
every degree; the two weld placeholders `jd0`/`genhnBox2` (`True`-valued, with the `w1` debt);
`windowPinning`; `genhnHE` (`n ≥ 6`); `genhnTow1` (`n ≥ 8`) — i.e. §3's 36 OPEN-MATH rows + the
CITEs, **plus the two untyped sockets, which are chapter I's own open item, not one of §3's.**

**Corrected report sentence (the one a report may use verbatim TODAY):** *"Proved
unconditionally at `n ≤ 2`. At general `n` the capstone is stated as an IMPLICATION from the
frozen Display-A block (I.17, one direction only), whose open rows are §3's census — 36
OPEN-MATH + the gate-(b) CITEs — and whose two ladder fields are, until chapter C types the
arising-configuration sockets, not yet a satisfiable hypothesis: no positive conditional claim
may be made from I.17 until then."*

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
| **L-1** | type I.08/I.10's `jd0` field against F's frozen carrier name; replace the `True` placeholder; re-run §11's blocked list | ~~F freeze~~ → **[A-I.1 §I-D7] the weld site-supply socket** — F has frozen and `Weld.JD0Box2` (F.04) is landed, but the `∀`-over-all-sites shape is not bindable (see L-2's machine reason); L-1 binds through a per-site arising predicate on the I.10a pattern |
| **L-2** | type I.09/I.10's `genhnBox2` field against F's frozen `GenhnBox2`/`W1Transport`; arc note travels with the field; **[A-I.1 §I-D8] and bind the THIRD field `w1`, which I.10's committed list omits** (F.28's `WeldObligations` has three) | ~~F freeze~~ → **the weld site-supply socket**: `∀ (K ι) (Rh RG : ι → K), W1Transport Rh RG` is FALSE (F.12w's `w1Transport_iff_zero_iff` + mismatched vanishing loci; machine-proved in `leanspec/Leanspec/ChapI.lean`'s §4 gate item (13)), so binding at that shape would make the hypothesis block contradictory |
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
| I.08/I.09 and I.10's `jd0`/`genhnBox2` fields | ~~**chapter F freeze** (L-1/L-2)~~ → **[A-I.1, I-D7/I-D8] the WELD SITE-SUPPLY SOCKET** (F froze; the carriers F.04/F.11/F.12 landed at OM-9, and binding them at their `∀`-over-all-sites shapes is REFUTABLE — proved for `W1Transport` at `ι = Fin 1`, `K = ZMod 3`) | the site-supply socket, per A-I.1 §I-D7 — **a signed I.10 stub with `True` fields is a false conditionality claim; forbidden** (I.10's ⚠, IN FORCE), and a signed stub at the unguarded site shape would be a CONTRADICTORY one, which is worse |
| **[A-I.1, NEW] I.10a/I.10b (the arising-configuration sockets) and hence I.10's `ladder`/`deepTwist` fields** | chapter C's tower-instantiation freeze (the GC-13/GC-14 pass that typed E.61/E.62) | C's freeze — until then the two fields are equivalent to their unguarded readings, which are REFUTABLE (A-I.1 §I-D13): **the block is contradictory and I.10 is an ELABORATION GATE, not a signature** |
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
§11). ~~Nothing else on the frozen display lacks a carrier. ✓~~

**⛔ STRUCK AS FALSE-AS-WRITTEN, AND RE-RUN, BY AMENDMENT A-I.1 (2026-08-16), defect I-D4.** At
composition the check was WRONG: `𝒲_{≤i}` (row HYP.63, the second half of Display A's
`∀ i ≥ 3` conjunct) had no carrier at all — E.24 packages the ϑ-half only, and chapter I added
no field for the other half. **Re-run under A-I.1's field list:** the `deepTwist` field carries
`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` at E.63's packaging, so the only Display-A content without a typed
field is again `AllOInterfaces` (signed non-applicability, §4.3) plus the two weld placeholders
(`jd0`, `genhnBox2` — `True`-valued, forbidden to sign, ruling at A-I.1 §I-D7/§I-D8, and the
`w1` sub-conjunct rides there as a NAMED DEBT). ✓ *with those three exceptions named, which is
the honest form of this row.*

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
   *[A-I.1 rider: the cross-read must now also check the SECOND under-statement this item
   missed — the shape clause was one-directional and therefore VACUOUS (I-D9), re-signed at the
   enumeration. The weight-correctness question is unchanged and still owed.]*
5. **I.10's `ladder` field quantifier** (ALL instantiations vs degree-`n`-arising ones): the
   strongest uniform reading was chosen; check Display A's "assume uniformly in O" preamble
   licenses it and that E.24's carrier types admit the quantification as written.
   *[A-I.1 rider: ANSWERED, in the negative, with machine evidence. E.24's carrier types do NOT
   admit the quantification as written (underapplied by eight arguments, I-D3), and the "ALL
   instantiations" reading is REFUTABLE (I-D13), not merely strong. The signed reading is the
   arising one, at sockets I.10a/I.10b. What the cross-read should now check is the SOCKETS'
   eventual bodies against the NON-SWALLOWING fence.]*
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
   *[A-I.1 rider: CHECKED and FAILED twice at the 0e gate — short by the `𝒲_{≤i}` conjunct
   (I-D4) and calling I.17 an equivalence when it is one implication. Both struck-and-corrected
   at NODE I.20; the corrected S3 row adds chapter I's own two untyped sockets to the modulo
   list, which are NOT one of §3's rows.]*
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

*[A-I.1 rider, 2026-08-16: the count is now **27 nodes** — I.10a and I.10b are added by the
amendment — and the stub stage HAS RUN (`leanspec/Leanspec/ChapI.lean`, green), which is what
produced the defect list A-I.1 adjudicates. §9's L-1/L-2 triggers are re-pointed there, and
three node blocks (I.01, I.03, I.10) carry struck-and-re-signed text.]*

<!-- RESUME: CHAPTER COMPLETE, THEN AMENDED (A-I.1, 2026-08-16 — read it first). Remaining
external actions: (i) chapter C types sockets I.10a/I.10b (lifts defect I-D13, the contradictory
block); (ii) the weld site-supply socket, then L-1/L-2 (three fields: jd0, genhnBox2, w1);
(iii) L-3 at D freeze; (iv) orchestrator items O-1..O-5 (§9.3; O-1/O-2 discharged at OM-7/OM-6,
O-4 moot at A-C.6); (v) cross-read per §13, with A-I.1's riders on items 4/5/9; (vi) the owner's
gate-(a) read of A-I.1's field-list change and gate-(b) signature on the C.94/C.66 REDRAFTS;
(vii) orchestrator dag_build merge re-run (I.10a/I.10b need DAG rows). -->

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

### DATED ADDENDUM (2026-08-16, CHAP-C A-C.1 — THE THREE C-SIDE GATE-(b) STATEMENTS NOW EXIST;
the "on file" overstatement corrected)

**Correction of record (the stub gate's D23).** `PROJECT_STATE.md` append #66 (2026-08-16)
stated that the three chapter-C cites' *"exact statements + faithfulness entries are on file
(CHAP-I §3 + addendum) for individual inspection at will"*. **At the time of writing that was
true of B.42's cite and of no other** — this file's 2026-08-16 addendum carried THE EXACT LEAN
STATEMENT for `LeanspecB.exists_slope_factorization` only, while C.66/C.92/C.94's own STATEMENT
fields all read "Exact Lean statement drafted at stub stage". The overstatement is hereby
corrected **and cured**: amendment **A-C.1** (2026-08-16, `blueprint/CHAP-C_tower_grammar.md`
A-§ block + per-node blocks) drafted and elaborated all three. The gate-(b) signature queue is
now FOUR statements deep, each with an elaborated leanspec twin:

| cite | Lean statement (in `leanspec/Leanspec/ChapC.lean`, blueprint block at the node) | published locus (A-3-verified) | status |
|---|---|---|---|
| B.42 `[cite:GN15 Thm 2.3 + FGMN Thm 6.6]` | `LeanspecB.exists_slope_factorization` (this file, above) | Contemp. Math. 637 (2015) 207–241, Thm 2.3 + J. Algebra 427 (2015) Thm 6.6 [predicted 6.5 in print] | statement drafted + audited; owner signs |
| C.66 `[cite:FGMN]` | `fgmn_residual_mul` (CHAP-C NODE C.66) | J. Algebra 427 (2015) 30–75: **Thm 2.8 + Cor 4.12(3) + Cor 4.9(3)** | SIGNED-AT-CATEGORY (append #66), **statement-UNINSPECTED** — three drafting decisions flagged at the node |
| C.92 `[cite:FGMN-chain]` | `FGMNCalculus` (class, one field per consumed clause) + `fgmn_calculus_exists` (CHAP-C NODE C.92) | J. Algebra 427: **Lemma 1.8, Cor 1.10, Lemma 5.2(2), Prop 5.6 + eq (11), Cor 4.12(1)/(3), Cor 4.9(3), Thm 6.2, Cor 6.3** | SIGNED-AT-CATEGORY, **statement-UNINSPECTED** — four drafting flags + TWO booked residual fields (C.90(b)'s Cor 6.3 leg; C.102's letter reads) at the node |
| C.94 `[cite:AGNPRW]` | `DescentState`/`DescentStep` + `NS7TerminationStatement` + `agnprw_termination` (CHAP-C NODE C.94) | Found. Comput. Math. **25 (2025), no. 2, 631–681**: **Thm 5.6** (the repo's "Thm 5.2" is the arXiv-v1 number and COLLIDES with a different published theorem — audit §3) | SIGNED-AT-CATEGORY, **statement-UNINSPECTED** — four drafting decisions flagged at the node |

**Faithfulness entries:** each node's block carries the drafting-decision list and the
A-3-corrected numbering inline; the full `docs/AXIOM_FAITHFULNESS.md` entries are owed at
fleet landing time (the axioms live in `leanspec`, not `leanfinal`, until then) — the entry
drafts ARE the node blocks. Audit A-3's pre-signing numbering check is DONE for all three
(this was HYP.17's row); the residual print-reads (audit §7.1/§7.2) remain the owner's
two-minute closing checks.

**⛔ ~~I.01 UNBLOCKED (the D24 deadlock, broken on the C side).~~ STRUCK BY AMENDMENT A-I.1
(2026-08-16), defect I-D6 — the paragraph is kept verbatim below because it is an UNSAFE
INSTRUCTION that a fleet agent might otherwise execute; see A-I.1 §I-D6 for the live target.**
~~`I.01`'s `NS7Termination` was
committed with a literal `True` placeholder body, `BLOCKED-UNTIL-RESOLUTION`, waiting on "C's
committed §5 carriers at stub time". Those carriers now exist (A-C.1: `DescentState`,
`DescentStep`, both typed against C's §5 layer — `HasLabel`, `IsTestKey`, `LevelDatum`), and
the typed body is exactly `Uniformity.Density.Tower.NS7TerminationStatement`'s matrix: **the
orchestrator's stub-resolution pass may now type I.01's body** (either
`NS7Termination := NS7TerminationStatement` — the bundle quantifier is the statement's own —
or its unfolding under I.01's frozen name/kind). Display A's line-1 conjunct stops being
vacuous in Lean at that pass; `I.25`'s registry expectation (`agnprw_termination` on C.94's
consumers) is now declarable.~~

**Why struck:** A-C.6 machine-refuted `NS7TerminationStatement` (it implies `False` over
`ℤ_[2]`; record `leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt`), and the name does not
exist in `leanfinal` at HEAD, so the instruction is both unsafe and unexecutable. I.01 is
**still BLOCKED**, now on the owner's gate-(b) signature of the A-C.6 REDRAFT
`LeanspecC.NS7TerminationStatementR` (over `DescentStepR`), not on chapter C's carriers.

### DATED ADDENDUM (2026-08-16, OM-4 — THE `(LB1)`/`(MP1)` TERMINAL-FATE ADJUDICATION: one new gate-(b) cite, one decomposition, one stop-the-line carrier finding)

*(OM-4 unit, ledger rows HYP.41/HYP.42; full record with certification tables in
`docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md`; scripts
`verification/om4_lb1_block_suite.py`, `verification/om4_mp1_recentered_key.py`; machine
witness `verification/om4_shadow_vacuity.lean`. This addendum adds CITE DRAFTS ONLY — no
landed statement is touched; §3.4's rows are annotated by reference, not edited.)*

**FINDING 0 (stop-the-line for §4's consumption; machine-checked). *[EXECUTED 2026-08-16:
the re-signs have LANDED — CHAP-E AMENDMENT A-E.2 (`BlockSuite`/`MidPeelEmission`) and
CHAP-D DECISION D-2 + AMENDMENT A-D.2 (the sitewise `(H-VARTHETA-RES)` carrier); the
consumption rule is the dated note at NODE I.10; non-triviality certificates in
`verification/om4_resign_nontriviality.lean`. The fence below is superseded AT THE A-E.2
FORMS.]*** The landed carriers
`LeanspecE.LB1Carrier` (E.39), `LeanspecE.MP1Carrier` (E.40) and the record
`LeanspecE.LadderObligations` (E.44) are **trivially provable as committed** —
`verification/om4_shadow_vacuity.lean` proves all three outright (Lean-core footprint;
`LB1Carrier` by the singleton self-block list, `MP1Carrier` by a fabricated one-side
numerical-shadow interface plus the carrier's own `(eC, fC)`). E.39's SIGNATURE NOTE
abbreviated away exactly the clauses that carried the strength. Consequence: **§4's
Display-A conjunct `LB1 ∧ MP1` must NOT be transcribed as `LadderObligations` until the
stub stage lands the full `BlockSuite`/emission records** (E.39/E.40 SIGNATURE NOTEs; the
E.40 strengthening is amendment-level — owner gate). Until then the conjunct's honest Lean
carrier does not exist, and any "discharge" of the current one is content-free. The two
cite drafts below are therefore drafted against the CONCRETE chapter-C vocabulary (landed,
non-vacuous), not against E.39/E.40's current shadows.

**HYP.42 `(MP1)` — the new gate-(b) cite (the FOURTH in the signature queue).** The corpus's
own narrowing locates the whole open content at item 5 of the `(MID-PEEL)` suite:
`EFF.T2.23` — *"No pin proves the recentered level-one key's orbit/`(e,f)` item, so `(MP1)`
remains open"*; `EFF.T2.61` — *"Peeling a recentered level-one key still needs item 5 … which
requires `Φ″` irreducible, asserted nowhere"*; items 2–4 at `Φ″` are S1.8C's four-pin
transport (relative — they carry `Φ′`'s conditionality). The missing statement is published:

**THE EXACT LEAN STATEMENT to be signed** (chapter-C vocabulary, all landed in
`leanspec/Leanspec/ChapC.lean` + `leanfinal` `typeOf`; ENV-C):

```lean
namespace Uniformity.Density.Tower

/-- `(MP1)` item 5 [cite:GN15 Thm 2.3 + eq (2.1)]: an in-window recentering of the
level-one key is irreducible, with the frame's own single-orbit `(e, f)`. -/
theorem recentered_key_emission {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {Λ : Polynomial O} (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree < F.key.natDegree)
    (hwin : (((F.e₁ * F.f₁) * F.h : ℕ) : ℕ∞) < F.stageHeight Λ) :
    Irreducible (F.key - Λ) ∧ typeOf (F.key - Λ) = ⟨{(F.e₁, F.f₁)}⟩
```

**FAITHFULNESS ENTRY (draft, for the fresh-context audit + signature).**

* **Published source (primary, COVERS-ALL-O).** [GN15] J. Guàrdia, E. Nart, *Genetics of
  polynomials over local fields*, Contemp. Math. 637 (2015) 207–241, **Theorem 2.3** (the
  NS-2 verbatim display, standing setting an arbitrary discrete valued field), applied to
  `g := Φ″ = F.key − Λ` at the node `(µ₁, φ = F.key)` (`µ₁` = the frame's inductive
  valuation, MacLane chain `µ₀ →(x, λ₁) µ₁`): `ord_φ(Φ″) = 0` and `deg Φ″ = deg φ` force,
  in the source's own degree law `deg g_{λ,ψ} = e_λ·ord_ψ(R_λ(g))·deg ψ·deg φ`, one factor
  with `e_λ = ord_ψ = deg ψ = 1` and `deg g₀ = 0` — so `Φ″ = g_{λ,ψ}` and the source's
  final clause (*"if `ord_ψ(R_λ(g)) = 1`, then `g_{λ,ψ}` is irreducible in `O_v[x]`"*)
  gives irreducibility. **`(e,f)` leg:** [GN15] eq **(2.1)**: *"`e(F) = e(µ_F) = e₀⋯e_r`,
  `f(F) = f₀⋯f_r`"* — at the length-1 integer-slope side this is `(e₁·1, f₁·1) = (e₁, f₁)`.
* **Secondary (ℚ_p-specialized, the tightest shape match).** GMN **Theorem 2.11**
  (`docs/references/HigherNewton.tex` 1258–1282, label `phir`, printed-numbering verified at
  A-3's standard): *"We can effectively construct a monic polynomial `φ_r(x)` of type `t`
  such that `R_{r−1}(φ_r)(y) ∼ ψ_{r−1}(y)`. **This polynomial is irreducible over
  `Z_p[x]`**"* — and its construction at the refined type `(t; λ, y − s)` (with `e_r = 1`,
  `f_r = 1`, so `m_{r+1} = m_r`) produces `φ_{r+1} = φ_r + P` with `P` EXACTLY a height-λ
  digit-lift of degree `< m_r`: the recentered key IS the theorem's constructed
  representative. The definition following it (*"A representative … without necessarily
  assuming that it has been constructed by the method"*) plus the proof's product-theorem
  argument (line 1281) and the §2.1 chain sentence (line 887: *"By the Theorem of the
  product in orders 1,…,r−1, the polynomials `φ_i(x)` are all irreducible over `Z_p[x]`"*)
  cover every permitted lift choice. Corroborating general-scope remark: [AGNPRW] Thm 4.4
  (*"If `v` has rank one, then `φ = Q`"* — keys are irreducible over the rank-one
  henselization).
* **Clause mapping.** `hdeg`/`hΛ` ↔ the recentering increment (`deg L < D′`, `Λ ≠ 0`);
  `hwin : T = D′·h < dv(Λ)` ↔ the `(WINDOW)` floor — source-side, it makes `Φ″` "of type
  `t`" (the below-window read of `Φ″` coincides with `Φ′`'s) and makes the `(µ₁, Φ′)`-polygon
  of `Φ″` ONE side of LENGTH 1 and integer slope `dv(Λ) − T`; `Irreducible (F.key − Λ)` ↔
  the source's mult-1 irreducibility clause; `typeOf … = ⟨{(e₁, f₁)}⟩` ↔ the certified
  single-orbit `(e,f)` decomposition, [GN15] (2.1) / GMN Cor 3.3 (*"if `d(S) = 1` the
  polynomial is irreducible … `f(L/K) = m`, `e(L/K) = e`"*).
* **Standing-hypothesis caveat (same genus as B.42's `φ ≁_µ φ_r` bullet).** [GN15] Thm 2.3
  at the node `(µ₁, F.key)` needs `F.key ≁_{µ₁} x`; for `deg F.key = e₁f₁ ≥ 2` this is
  automatic (the difference is monic of positive degree, same derivation as the B.42
  addendum's bullet (ii)); the degenerate frame `e₁ = f₁ = 1` (`h = 0`, `D′ = 1`) has a
  LINEAR recentered key — irreducible outright, no cite consumed. So no [FGMN] co-primary
  is needed here; record the two-case split in the faithfulness entry at signing.
* **Certification record (OM-4 §2.2).** Both primes, both characteristics: unramified stage
  (f₁ = 2): 336 + 90 recentered keys, ALL irreducible; ramified stage (e₁ = 2): the defeat
  system `{dv(Λ) > T, Φ″ reducible}` INFEASIBLE over 168 (p = 2) + 624 (p = 3) frame-valid
  sweeps and 78 char-p sweeps, and **SHARP at the boundary** `dv(Λ) = T` (explicit reducible
  witnesses `x² − 4` at `p = 2`, `x² − 3x − 18` at `p = 3` — so the window hypothesis is
  load-bearing, not decorative); `(e,f)` emission confirmed 160/160 against PARI
  `idealprimedec` (decorrelated round-4 implementation). Exact infeasibility proof for the
  swept genre transcribed at OM-4 §3.2.
* **What the cite does NOT close (`(MP1)`'s honest residue).** Items 2–4 remain S1.8C's
  RELATIVE transport (they carry the level-one records' own conditionality, per
  `EFF.T2.61`); and the E-layer consumption needs the strengthened `MP1Carrier` (FINDING 0)
  discharged from this cite at the instance rows — a chartered stub-stage unit, not
  mathematics. At level two nothing is needed (E.42's discharge, landed).

**HYP.41 `(LB1)` — DECOMPOSITION onto chapter C's signed §5 layer, with one CONTINGENT
cite.** The concrete level-one content of the block suite is ALREADY carried, at exactly
the right frame, by two committed chapter-C nodes: **C.33**
`exists_dvDissection`/`dvDissection_unique` (the side dissection = `(SIDE-PROD)` +
single-side purity + the `(SEP)`-free degree law + slope detection) and **C.34**
`exists_dv_residual_dissection` (the label dissection = `(LABEL-PROD)`/`(LABEL-PURE)`-shaped
block split with uniqueness — a fleet proof via B.48's graded-coprime route, and B.48 is
LANDED, so this leg mirrors a proved node). `(LABEL-OWN)` is the degree law of the two
dissections combined; disjoint/exhaustive partitions are the product identities under
`Squarefree`; inherited continuation data is C.35's `BlockContext`/`blockFactor` packaging.
**Terminal fate of HYP.41, adjudicated: REDUCES-TO(C.33 + C.34 + an E-side
strengthening/discharge unit).** ⚠ **RISK FLAG on C.33's route, with the contingent cite
that retires it.** C.33's DEPENDS is explicit that B.41/B.42 are *"route templates — NOT
consumable directly: they require `IsKey φ`, false for `F.key` at `h ≥ 1`"* — and B.42's
own committed route was **machine-refuted** at order 1 (A-F.10: `hpure` unavailable in the
multi-side inductive case; the vertex-split mechanism has *"NO corpus proof … at general
keys"*). The same obstruction plausibly recurs at C.33's `dv`-graded rerun. If it does,
C.33's disposition follows B.42's precedent: retag `[cite:GN15 Thm 2.3]` — the SAME
published display at MacLane chain length `r = 1` instead of `r = 0` (NS-2/NS-3: the source
is simultaneously the order-1 and order-`r` statement), with [FGMN] Thm 6.6 as the same
co-primary for the proper-key range. *Recommended queue shape in that branch:* ONE
general-order [GN15] Thm 2.3 signature event covering B.42 AND C.33 (the two faithfulness
entries share their primary verbatim quote; nothing mathematical changes). Certification
record (OM-4 §2.1): the full S1.7A display list verified exactly on 22 constructed trigger
suites over {p = 2,3} × {ℚ_p, 𝔽_p((t))} (multi-side, mixed, deg r′ = 2, e′ = 2, and an
𝔽₄-stage showcase) + 300 random squarefree states against PARI factorpadic, 0 violations.

**Queue mechanics.** CITE (gate (b)) count **3 → 4 (+1 contingent)**: the [AGNPRW] Thm 5.2
cite (C.94), the FGMN cite (C.66/C.92), the [GN15] Thm 2.3 cite (B.42), NEW: [GN15]
Thm 2.3 + (2.1) at the recentered key (`recentered_key_emission`, HYP.42's item 5), and
CONTINGENT: [GN15] Thm 2.3 at `r = 1` for C.33 (= HYP.41's side leg) if its committed route
hits B.42's refuted-mechanism wall — in which case merge it into B.42's signature event as
one general-order cite. §3.4's HYP.41/HYP.42 rows' "none is known today" is superseded by
this addendum (annotation by reference; the rows are not edited). Owner signs per cite; the
HYP.17/A-3 numbering discipline applies ([GN15] numbers above were read from
arXiv:1309.4340v2 this campaign; Contemp. Math. print check is the standing A-3 residual).

### DATED ADDENDUM (2026-08-16, OM-5 — GATE-(b) CITE-CANDIDATE: the leaf dichotomy for `B-BOX-1`)

**`B-BOX-1` (B.61's `hBOX`, chapter B's sole open box, scope-widened at A-F.7) is a
CITE-CANDIDATE, and this addendum is its queue draft at the B.42 standard.** Unit note:
`docs/openmath-campaign/OM-5_bbox1_2026-08-16.md`; certification battery
`verification/om5_bbox1_cert.gp` (**128 checks, 0 failures**: the leaf `(e,f) = (ℓ, m·d)` and
the order-level gcd `inertiaDegOf = m·d` at `d ≥ 2` over both primes `{2,3}` and both
characteristics, including the A-F.7 `ℓ = 1, m ≥ 2, d ≥ 2` region, the wild `p ∣ ℓ` rows and a
`p ∣ d` row; the multiplicity-`≥ 2` and non-coprime defeats; LEMMA HE3-4U's base-change
mechanism executed at an `m ≥ 2` equal-characteristic instance). **Nothing is retagged and no
box is discharged by this addendum**: until the owner signs, `B-BOX-1` stays carried exactly
as today.

**THE EXACT LEAN STATEMENT to be signed** is LANDED (compiled, Lean-core footprint, **no
axiom, no `sorry`** — the `Prop` is stated, not asserted):
`Uniformity.Density.Leaf.BBox1CiteStatement`
(`leanfinal/Uniformity/ChapB/BBox1CiteStatement.lean`) — B.61's binder list plus the `H₀` pin
and `hirr : Irreducible (resPoly π φ g u ℓ hne H₀)`, concluding B.61's `hBOX` verbatim
(`∀ g' ∈ monicFactors g, φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g'`). The same file
lands the **machine-checked wiring** `typeOf_leaf_of_cite`: `BBox1CiteStatement` → B.61's
conclusion `typeOf g = ⟨{(ℓ, m·d)}⟩` under the leaf hypotheses — so signature alone completes
the `d ≥ 2` leaf rows, with the axiom name in every downstream `#print axioms` (the H-14
inheritance pattern). Post-signature form: `axiom bBox1_cite : BBox1CiteStatement` plus the
`docs/AXIOM_FAITHFULNESS.md` entry distilled from this draft.

**FAITHFULNESS ENTRY (draft, for the fresh-context audit + signature).**

* **This is a COMPOSITE cite, and that is disclosed up front.** The mathematical core is the
  published leaf dichotomy (ingredient (A)); reading it in `inertiaDegOf`'s order-level gcd
  vocabulary — the only vocabulary `leanfinal` has, since the factor-field valuation-ring
  carrier does not exist in the tree (I.21's stub note) — consumes two classical
  valuation-theory legs (B), (C) that are standard but NOT Montes literature, plus one
  mathlib-checkable leg (D). B.42's precedent already accepts repo-side dictionary glue
  audited in the faithfulness entry; this draft has one more glue *class* and names it.
  If the owner's gate-(b) discipline excludes composite cites, the recorded fallback is
  REDUCES-TO(B.62) — OM-5 §3.1 proves there is NO route through landed vocabulary (at every
  `d ≥ 2` leaf the order `AdjoinRoot g` has residue field `resField φ` of degree `m < m·d`,
  hence is never a DVR: the box's region lies entirely off the monogenic-maximal locus that
  `TypeOfFaithful.lean`/`typeOf_inert_faithful` reach).
* **(A) Published source (primary): [FGMN] Thm 6.6** (arXiv:1305.0775v3; J. Algebra print
  PREDICTED Thm 6.5 per `docs/CITE_NUMBERING_AUDIT_2026-08-16.md` §4 — *predicted, NOT
  verified*, the same two-minute Elsevier check as B.42's residual). Verbatim (already quoted
  at the B.42 entry): *"Let `µ` be an inductive valuation and let `φ` be a **proper** key
  polynomial for `µ`. Then, every monic polynomial `g ∈ O_v[x]` factorizes into a product of
  monic polynomials in `O_v[x]` … `deg g_{λ,L} = e_λ ord_L(R_{µ_λ}(g)) deg L deg φ`. Moreover,
  if `ord_L(R_{µ_λ}(g)) = 1`, then `g_{λ,L}` is irreducible in `O_v[x]`."* — at the Gauss
  valuation `µ₀`, where EVERY key is proper (`KP(µ₀)_str = KP(µ₀)`, [FGMN] Def 5.10; the whole
  `IsKey` range, inheriting B.42's A-3 disposition verbatim — do NOT sign [GN15] Thm 2.3 alone
  over `∀ φ, IsKey φ`). **Co-primary: [GN15] Thm 2.3** (VERIFIED at A-3, arXiv:1309.4340v2 +
  author PDF; the chain-relative restatement covering `φ ≁_{µ₀} x`) **+ [GN15] eq. (2.1)**
  for the explicit invariants: *"`e(F) = e(µ_F) = e₀⋯e_r`, `f(F) = f₀⋯f_r`"* — at order 1
  (`e₀ = m₀ = 1`, `f₀ = deg φ = m`, `e₁ = ℓ`, `f₁ = deg ψ = d`): `e(F) = ℓ`, `f(F) = m·d`.
  Standing setting of both: an arbitrary discrete valued field — **COVERS-ALL-O**, both
  characteristics (`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2, resolved verdict).
  **Secondary display (ℚ_p scope only):** GMN Thm 1.19 + Cor 1.20 (`docs/GMN_citations.md`
  §1 verbatim: *"`f(L/K)` is divisible by `m·deg ψ_i` … in particular, if `a_i = 1` then
  `G_i` is irreducible, `f(L/K) = m·deg ψ_i`, `e(L/K) = e`"*) — the cleanest display of
  exactly the box's content, but GMN's standing setting is a finite extension of `ℚ_p`
  (`docs/references/HigherNewton.tex` §1.1), so as in B.42's entry **[FGMN]/[GN15] are the
  load-bearing legs, not GMN**.
* **(B) Glue leg, classical: the maximal-order carrier.** `O` complete DVR, `L = K[x]/(g)`
  of degree `n` ⟹ the integral closure `O_L` of `O` in `L` is a DVR, finite free of rank
  `n` over `O`, residue degree `f(L/K)`, unique valuation extension `w`. Standard complete-DVR
  theory — Serre, *Corps Locaux* / *Local Fields* (GTM 67) Ch. II §2 (Prop. 3 is the
  PREDICTED display) and Neukirch, *Algebraic Number Theory*, Ch. II §§4, 6. ⚠ **Exact
  proposition numbers FLAGGED FOR LOOKUP at signature time** (neither book is in
  `docs/references/`; the repo rule "never trust a number from memory" applies — HYP.17/A-3
  class residual).
* **(C) Glue leg, classical: the norm-valuation identity.** `v(N_{L/K}(x)) = f(L/K) · w(x)`
  for `x ∈ L^×`, `w` normalized on `L`. Published form: the henselian uniqueness display
  `w = (1/n) · v ∘ N_{L/K}` (Neukirch ANT Ch. II, Thm 4.8 is the PREDICTED number — same
  lookup flag) combined with the fundamental identity `e·f = n` for complete discrete
  valuations. **In-repo corroboration of exactly this mechanism, machine-checked:**
  `Uniformity.Density.exists_ramification_data` + `inertiaDegOf_eq_inertiaDeg'`
  (`leanfinal/Uniformity/Density/TypeOfFaithful.lean`) prove (C) shape-for-shape for ANY
  carrier with `[IsDiscreteValuationRing A]` — normal form `x = unit·ϖ^j` gives
  `v(N x) = j·v(N ϖ)` and the Quarry fundamental identity
  (`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`) pins `v(N ϖ) = f`. The
  missing Lean object is ONLY (B)'s carrier, never this identity.
* **(D) Glue leg, mathlib-tier: order norm = field norm.** For `x` in the order,
  `Algebra.norm O x ↦ N_{L/K}(x)` under fraction-field base change of the free module —
  `Algebra.norm_localization`, PRESENT at our pin
  (`Mathlib/RingTheory/Localization/NormTrace.lean:63`, mathlib `fabf563a`).
* **Derivation (A)+(B)+(C)+(D) ⟹ the statement**, three lines: under the hypotheses, (A)
  forces `g` irreducible (so `monicFactors g = {g}` — the `∀ g'` ranges over `{g}`) with
  `f(L/K) = m·d`; for `0 ≠ x` in the order, (D) reads `addVal O (Algebra.norm O x)` as
  `v(N_{L/K} x)`, which by (B)+(C) is `(m·d)·w(x)`; hence `m·d` divides every norm-valuation,
  i.e. `m·d ∣ inertiaDegOf g` — the gcd semantics of `TypeOf.lean:193`. **Direction check
  (D-3's order-not-field reading):** the order's norm-value set is a subset of the field's,
  and a gcd over a subset is a multiple of the gcd over the superset — the box's divisibility
  direction is exactly the one that survives the order reading; the reverse divisibility is
  landed B.54 and needs no field.
* **Clause mapping (import ↔ source).** `hφ : IsKey φ` ↔ `φ ∈ KP(µ₀)` (EXACT both
  directions — B.42's A-3 bullet (i), inherited verbatim, [FGMN]-properness leg included);
  `hpure`/`hne`/`hd` ↔ the one-sided `φ`-polygon of slope `−u/ℓ` in lowest terms (B.34's
  dictionary; B.42a's machine-checked converse); `hres` ↔ the single-branch case `f̄ = φ̄^μ`
  (strictly narrower than the source's arbitrary monic `g` — no strengthening smuggled);
  `hirr : Irreducible (resPoly …)` ↔ `ord_L(R_{µ_λ}(g)) = 1` **with** `deg L = deg R` (the
  residual is a unit times a single irreducible of full side degree — the multiplicity-1
  clause; `resPoly` is not normalized monic, and irreducibility is unit-insensitive, B.30's
  degree/constant-term theorem supplying `deg resPoly = d`); conclusion ↔ the source's
  irreducibility + `(e,f)` display, deliberately WEAKENED to the divisibility form that is
  byte-identical to B.61's `hBOX` (the full leaf conclusion is then recovered by the LANDED
  B.61 through the landed wiring `typeOf_leaf_of_cite` — machine-checked, not cited).
* **Necessity of `hirr`, certified by constructed counterexample** (CERT-C(i), both
  characteristics): `g = (x²−p)²` is `(1,2)`-pure at `X` with `sideDeg = 2` and residual
  `(y−1)²`; its factor `x²−p` has `inertiaDegOf = 1` and `m·d = 2 ∤ 1` — the statement is
  FALSE at multiplicity `≥ 2`, so the clause cannot be dropped. (Cor 1.20's divisibility by
  `m·deg ψ_i` still holds there — `1 ∣ 1`; the defeat is of `d = sideDeg`, not of the
  source.) Do not conflate with HE6-BOX-1 (B.61's TEETH warning, unchanged).
* **Known caveats.** (1) The composite-cite question is the OWNER'S DECISION — this draft
  does not presume it (fallback recorded above). (2) `resPoly` transcription-shear risk:
  B.42's caveat (2) applies verbatim since `hirr` reads `resPoly`; the same A-F.6-documented
  hypotheses exclude the two known shear modes; `hirr` sits in the digit-read transcription's
  verified faithful scope. (3) Numbering: [FGMN] print number PREDICTED (−1 drift); Serre and
  Neukirch display numbers FLAGGED FOR LOOKUP (leg (B)/(C) bullets); [GN15] Thm 2.3 and GMN
  printed-TAMS already VERIFIED at A-3. (4) The `Finite (ResidueField O)` binder is
  mathematically unnecessary for (A)–(D) but is kept: it narrows the axiom to ENV-C (the
  capstone's `O`), and a narrower axiom is a smaller trust surface.
* **Consumer effects on signature.** B.61's `d ≥ 2` rows (hence B.71, B.79, and B.63's
  `hperim` general branch) re-gate from OPEN-MATH onto the signature; the 2026-08-15 A-F.7
  addendum's `ℓ = 1, m ≥ 2, d ≥ 2` OPEN-MATH routing is superseded-on-signature (annotation
  by reference; the rows are not edited). **`C-BOX-1` (C.60):** the SAME published statement
  covers the level-2 residue leg ([GN15] Thm 2.3 at any chain length — NS-2/NS-3), but the
  level-2 axiom instance is a separate signable statement in C's vocabulary
  (`CBox1Side`/`KeyFrame`/`LevelDatum`) — flagged to CHAP-C, not drafted here. `HYP.01`/
  `HYP.12` [CORE-SET] are untouched: the axiom stays in the gcd/order vocabulary and
  identifies no APIs (GC-3 respected).

**Queue mechanics.** CITE (gate (b)) count **4 (+1 contingent) → 5 (+1 contingent)**: [AGNPRW]
Thm 5.2 (C.94) · FGMN (C.66/C.92) · [GN15] Thm 2.3 (B.42) · [GN15] Thm 2.3 + (2.1) at the
recentered key (OM-4/HYP.42 item 5) · **NEW: [FGMN] Thm 6.6 + [GN15] Thm 2.3 & eq. (2.1) for
`B-BOX-1` (`BBox1CiteStatement`), with the (B)/(C) classical glue legs and (D)** · contingent
[GN15]-at-`r = 1` for C.33 unchanged. **Merge option, owner's call:** this cite's (A) shares
both primary sources and their verbatim displays with B.42's signature event — one
general-order [GN15]/[FGMN] signature event could cover B.42, OM-4's item 5, the contingent
C.33, AND this cite's ingredient (A), leaving only the (B)/(C) glue legs as this cite's own
increment. Owner signs per cite; the HYP.17/A-3 numbering discipline applies throughout.

### DATED ADDENDUM (2026-08-16, OM-6 — ORCHESTRATOR ITEM O-2 BOOKED: the `LEMMA GENHN-3` cap/consultation transcription)

*(OM-6 unit, ledger row HYP.24; full record `docs/openmath-campaign/OM-6_window-pinning_2026-08-16.md`;
numeric leg `verification/om6_window_pinning_check.py`, 26/26.)* §9.3's item **O-2** is
DISCHARGED at exactly its named candidate home: `leanfinal/Uniformity/ChapH/H89w.lean`, an
H.89-adjacent appendix file (H09w precedent), registered by CHAP-H AMENDMENT A-H.3 —
`EFF.GENHN.29`'s clauses (b)/(c) at general `e₁`, (a)'s rider-corrected interior criterion
with the no-tie/undercut pair, the `[r2]`/CAP-GEN band-census arithmetic (tied to H.44's
`pinCensus` at the committed `(1,3,2)` instances), and (d)'s update-map descent (both ring
types); 17 declarations, sorry-free, Lean-core only. One finding (F-OM6.1, A-H.3): the (c)
display's "inside the string" requires an occupancy scope pin — machine-refuted unpinned at
`(e₁,h,m) = (3,2,1)`, landed in the occupied form, source not edited. **I.14's resolution
is unchanged**: the pinning conjunct is still HYP.24's pinning half, still CARRY — H89w
narrows the SUPPLIER gap (I-11(ii)), it does not discharge `hwin` (HYP.36, GC-5) and it
does not formalize `GENHN-CAP-GEN`'s reader rule (CHAP-H §16 item 3 upheld). I.05's stub
body gains concrete general clauses to bind to at resolution time; I.05/I.14's text is
untouched. This addendum adds no new ledger row.

---

## ADDENDUM (2026-08-16, unit OM-7) — ORCHESTRATOR ITEM O-1 DISCHARGED: `[GENHN-HE(μ = 3)]`
## HAS A TRANSCRIPTION OWNER; HYP.82's THRESHOLD NODE PROVED

**O-1 (honesty I-11(i)) is BOOKED.** The `[GENHN-HE(μ = 3)]` transcription (THEOREM HE3.A at
μ = 3, first-live `n = 6, 7`, corpus-unconditional, previously NO owner in any committed
chapter) now lives at `leanfinal/Uniformity/ChapH/H73w.lean` — an H.73-adjacent appendix
file (H09w/H89w precedent), registered by CHAP-H AMENDMENT A-H.4. Owner-home adjudication
(the §8 candidates): a chapter-E instance section violates E's trap E-3 (E never
proves/transcribes μ ≥ 3 σ-decision content); a chapter-B appendix or C-side node is
wrong-scoped (B owns order-1 leaves; C owns `n ≥ 8` towers; the μ = 3 slice is the
`n = 6, 7` composite-stage case, i.e. H's stage grammar); the H.73-adjacent home types
completely against landed H.01/H.02/H.73/H.74 vocabulary. Landed content: the HE3.A
transport `(e, f) ↦ (e₁e, f₁f)` with its degree law; the five-type μ = 3 dictionary with
degree conservation (the H.74 analogue); five-type EXHAUSTIVENESS; the μ = 2 consistency
theorem (H.73's `stageSigma` = the transport's μ = 2 shadow — the no-circularity
cross-check as a theorem); HE3.B's unconditionality arithmetic (stage-CS ⟹ μ ≥ 4, strict
descent, branch-(ii) ⟹ μ ≥ 4, first-live `n = 6` sharp / `μ ≥ 4` at `n ≥ 8`). Trust
boundary = H.73's own standard verbatim: the σ-DECISION analytics stay corpus-side, toothed
by `verification/openmath/om7_cert.py` (97 rows GREEN, 6/6 planted mutants: the FIRST
embedded `n = 7` rows — closing `EFF.HE3` source defect 9 — the first equal-characteristic
μ = 3 rows — closing HE3-BOX-4b's ℤ_p-only gap — the first `f₁ ≥ 2` frame at `D′ = 4`, and
the first `h = 3` frame) plus HE-SIG (947). **I.06's row updates**: its docstring's
"transcription owner UNASSIGNED (orchestrator O-1)" is resolved to H73w at chapter I's next
edit pass; the stub body and the BLOCKED-consumer discipline are UNCHANGED — `μ ≥ 4` still
rides HYP.143 (E trap (iii)/GC-5 untouched), and the Display-A conjunct stays on the §4/S3
open surface as a carried hypothesis. This addendum discharges an ORCHESTRATION item, not
a conjunct.

**I.07-adjacent**: NODE C.93's clause (i) — the threshold `n = D_r·μ_r ≥ 2^{r+1}` the
HYP.82 census rests on — is PROVED at the A-C.1-signed signature verbatim
(`leanfinal/Uniformity/ChapC/C93.lean`, `tower_first_live` + sharpness; Lean-core; wired
into the ChapC roll-up by the fleet's layer-close-13 regeneration, commit `da716fae`). Census disposition
re-verified at HEAD (C-H4's table; depth ≥ 4 claimed by no node); the open remainder
(HYP.67–71/78–80/142/143/144-BOX-2) verified `n ≥ 8`-scoped row-by-row — nothing leaks
below the `if n ≥ 8` conjunct. HYP.82 stays CARRY.

Unit record: `docs/openmath-campaign/OM-7_genhn-he-tow_2026-08-16.md`; ledger ARC NOTEs at
HYP.81/HYP.82 (dispositions unchanged). This addendum adds no new ledger row.

## ADDENDUM (2026-08-16, unit OM-9) — THE TWO WELD CONJUNCTS' CARRIERS ARE LANDED (I.08/I.09
## LATE-BINDING TARGETS NOW EXIST); THE `w1` FIELD'S STRENGTH IS PINNED; WELD-ZERO UNTOUCHED

**I.08 (`JD0-BOX-2`).** Chapter F's §4 is landed in `leanfinal` (AMENDMENT A-W.2):
`Uniformity.Density.Weld.JD0Box2` (F.04) and the strike ledger `JD0SiteStrike` (F.05) exist
at the gate-pinned bodies, with the fold route's site-independent half PROVED
(`F04w.lean`: `JD0SiteStrike.jd0Box2` — a strike with its ledger leg witnesses the
perimeter) and the mechanism layer proved (F.02/F.03/F.06 stubs now theorems; NEW
`gaugeCobdry_isCocycle`, the perimeter's consistency). §9 item **L-1** can bind `jd0` to a
real declaration at F's freeze. **The conjunct itself is UNCHANGED** (CARRY; the
four-line-form warrant is synthesis at GRTJA 1/2): I.08's placeholder status resolves to a
named landed carrier, not to a discharge. Each per-site strike record, once chapter-H/C
site objects exist (GC-13), discharges its site by one application of
`JD0SiteStrike.jd0Box2`.

**I.09 (`GENHN-BOX-2` + W-1).** `GenhnBox2` (F.11, clause (iv) structurally absent, μ ≥ 3
guard in the Prop) and `W1Transport` (F.12) are landed at gate signatures; W-9's abstract
clauses (i)–(iii) are PROVED behind the carrier (F.07–F.10b, F.13 — assoc from the cocycle
identity, dimension/cardinality, the JC-F1 power basis, plus the fresh certified theorem
`CarryCocycle.c_comm`). **L-2's typing note, sharpened by a machine-checked fact:**
`w1Transport_iff_zero_iff` (F12w) proves the `w1` field's type is equivalent to equality of
vanishing loci — the carrier is the transport's SIGNATURE, so a site-level instantiation of
`w1` at nonvanishing families is FORMALLY trivial (`w1Transport_of_ne_zero`) and would
discharge NOTHING of HYP.139 (MATH content = TR-3′-GEN's compatible dictionary at general
order). **Consequence for I.10/I.17's open-surface accounting:** the `w1` conjunct field
should carry this note when bound, so no later pass mistakes a typed instantiation for a
discharge (the same trap class as I-11's owner rules). The WELD-ZERO arc note travels with
the field exactly as I-7 states: IN-PROGRESS, clean-pass 1 of 2, pass 2 IN FLIGHT
(Fable-max), licenses nothing; this addendum consumed nothing from it.

Unit record: `docs/openmath-campaign/OM-9_weld_2026-08-16.md`; ledger ARC NOTEs at
HYP.74/HYP.139/HYP.148 (dispositions unchanged: CARRY/MATH/CARRY). This addendum adds no
new ledger row and moves no bucket.

## AMENDMENT A-I.1 (2026-08-16, unit A-I.1 — THE STAGE-0e DEFECT ADJUDICATION: the Display-A
## carrier fields re-signed at the ARISING-CONFIGURATION binding, the `𝒲` conjunct given a
## field, I.03's vacuous clause repaired, I.01's resolution instruction re-pointed)

**What this amendment is.** The stage-0e stub gate
(`leanspec/Leanspec/ChapI.lean`, commits `e92c4e0f`/`529cfc87`/`3dbd4269`/`46d3c0ac`) elaborated
every chapter-I signature against the landed corpus and recorded twelve defects, I-D1 … I-D12.
I-D1/I-D2 are `leanfinal`-side (duplicate declarations, roll-up gaps) and are cured elsewhere.
This amendment adjudicates the BLUEPRINT-side defects from their sources and re-signs, per
defect, the honest form: **I-D3** (the `ladder` field: repaired application AND the
canonical-binding ruling), **I-D4** (the `𝒲_{≤i}` conjunct's missing field), **I-D5** (I.03's
`A1Family` membership), **I-D6** (I.01's unsafe resolution instruction), **I-D9** (I.03's
provably vacuous `(A1)`-admissibility clause), plus rulings on **I-D7/I-D8** (the weld
placeholders) and one **NEW** defect the adjudication found, **I-D13** (below), which is the
sharpest finding of the unit.

**Owner-facing flag (CONVENTIONS Part V gate (a)).** §I-D3 and §I-D4 CHANGE THE FIELD LIST OF
`CapstoneHypotheses` — the public conditionality display. They are taken under the standing
statement-change authority as *strengthening-toward-dischargeability* (no conjunct dropped, one
conjunct added, the conclusion `UniformityStatement` untouched, `UniformityStatement` itself not
edited), and they are listed at the top of this amendment's OWNER-FACING FLAG LIST so the owner
reads them at the next visit. **`UniformityStatement` (gate (a)'s main statement) is untouched
by this amendment.**

---

### I-D13 (NEW, stop-the-line, machine-transported) — the ∀-over-all-configurations reading of
### the Display-A carrier fields is not merely UNDISCHARGEABLE, it is REFUTABLE

The 0e gate recorded (I-D3) that a `∀ ρ` binder puts the `ladder` field in OM-8's ρ-defeat
regime, i.e. *undischargeable*. The adjudication finds the stronger and worse fact:

> **The signed `ladder` field is FALSE.** Its binders range over ALL `(O, K, C, B)` and (after
> the 0e repair) all level data. The A-E.2 re-signed carriers are machine-certified **FALSE at
> concrete legal instances** — `lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁` over
> `C₁ : SlotCarrier ℤ ℚ` with `B₁.F = X² + X + 1`, and `mp1_resigned_not_trivial :
> ¬ MP1Carrier C₂ B₂` at key `X²`, `F = X⁴ − 5X² + 4`
> (`verification/om4_resign_nontriviality.lean`). **The antecedent was RE-RUN at this amendment,
> not taken on a docstring's word**: `cd leanspec && lake env lean
> ../verification/om4_resign_nontriviality.lean` exits 0 today, with
> `lb1_resigned_not_trivial`/`mp1_resigned_not_trivial`/`hvarthetaRes_resigned_not_trivial` all
> Lean-core; and the carriers it refutes were diffed against the landed ones — `LB1Carrier` and
> `BlockSuite` are byte-identical modulo namespace, `RungInterface` differs only in universe-
> variable spelling (`Type*` vs `Type uO`/`uK`/`uW`). Instantiating the field at
> `(ℤ, ℚ, C₁, B₁)` and any level data yields `LB1Carrier C₁ B₁`, contradiction.

Consequences, stated flatly: `CapstoneHypotheses n` as signed is **uninhabited for every `n`**;
`∀ n, CapstoneHypotheses n` is FALSE; and I.17 (`uniformity_of_capstoneHypotheses`) therefore
**proves `UniformityStatement` from a contradiction** — the assembly is vacuous, and the
"honest conditionality display" displays a hypothesis nobody can hold rather than one nobody
has yet proved. This is the OM-4 FINDING-0 genre with the sign flipped (FINDING 0: a conjunct
too weak to say anything; I-D13: a conjunct too strong to be true), and it is stop-the-line by
the same rule.

**The pincer that forces the cure.** Three readings of the level/block data were available, and
the two obvious ones are both closed by machine evidence already in the tree:

| reading | verdict | evidence |
|---|---|---|
| `∀` over ALL configurations (as signed) | **REFUTABLE** — contradictory hypothesis block | `lb1_resigned_not_trivial`, `mp1_resigned_not_trivial`, `hvarthetaRes_resigned_not_trivial` (`verification/om4_resign_nontriviality.lean`); OM-8 LEG D2's ρ-defeat at REAL tower exponents |
| `∃`-bundled data (or, equivalently, the data threaded as parameters of `CapstoneHypotheses` and supplied at I.17) | **FABRICABLE** — a degenerate configuration satisfies it, so the conjunct stops tracking conditionality | defect D-D12 (the voided `HVarthetaResVoided`); E.24's own recorded rejection of this option (`ChapE/E24.lean`, "⚠ THE `vartheta` FIELD'S DATA THREADING", option 2) |
| `∀` over the **arising** configurations (this amendment) | the honest reading: the corpus's own claim | E.24 option 1's rejection reason read positively; OM-8 §3.1's verdict (YES at every DEF GENTOW5-1 instantiation with the canonical node-point residue read) |

**Rule installed (binding on every later pass).** *No Display-A carrier field may quantify over
a configuration space larger than the arising one, and no such field may be typed at a guard
that already implies its own carrier* (the NON-SWALLOWING fence — see §I-D3).

---

### I-D6 — I.01's resolution instruction, RE-POINTED (signed)

**Verdict: the instruction was UNSAFE AND UNEXECUTABLE; struck at both sites, re-pointed at
the A-C.6 REDRAFT.** The two struck sites are NODE I.01's A-C.1 rider and the 2026-08-16 A-C.1
addendum's "I.01 UNBLOCKED" paragraph; both keep their text verbatim under a strike marker (a
fleet agent must be able to see what it was told, and why it is wrong).

**Signed resolution instruction (replaces the struck one):**

> I.01 stays at its signed `True` placeholder. Its live discharge target is the A-C.6 REDRAFT
> `LeanspecC.NS7TerminationStatementR` (over `LeanspecC.DescentStepR`,
> `leanspec/Leanspec/ChapC.lean`, commit `958cc39b`), which is **cite-conditional and awaiting
> the owner's gate-(b) signature**. Until that signature: no pass may type I.01's body. On
> signature: `NS7Termination` is resolved to `NS7TerminationStatementR`'s matrix under I.01's
> FROZEN name / bundle quantifier / `Prop` kind, the discharging axiom is
> `agnprw_termination : NS7TerminationStatementR`, and I.01's consumers move from
> `#axiom_core` to `#axiom_reg … [agnprw_termination]` at gate I.25.
> **Forbidden, permanently:** resolving I.01 against `Uniformity.Density.Tower.NS7TerminationStatement`
> (machine-refuted: it implies `False` — `leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt`),
> and citing that name at all — it does not exist in `leanfinal` at HEAD.

---

### I-D3 — the `ladder` field: BOTH halves signed (the repaired application AND the
### canonical binding)

**(a) The mechanical half — signed.** The committed `Ladder.LadderSupply C B` is underapplied
by eight arguments against landed E.24, whose structure is
`LadderSupply {O} [CommRing O] {K} [Field K] (C) (B) (G) [CommGroup G] (Kt) [Field Kt] (L)
[Field L] [Algebra Kt L] (N : NormSection G) (v) (ρ) (q)`. The signed application binds the
level data in the field and spells the six universes: `Ladder.LadderSupply.{0, 0, uW, uG, uKt,
uL} C B G Kt L N v ρ q`, with `CapstoneHypotheses.{uW, uG, uKt, uL}` universe-polymorphic in
`uW` (honesty E-12: `uW` is the `(SEC-RANK)` rank carrier's universe and is NOT inferable; a
`Prop` cannot quantify over universes, so the structure carries them and every consumer records
its choice). This is E.24's own recorded consumer obligation, discharged: *"When I.10 lands it
must also bind (or quantify over) the tower data block — the same choice E.61 forced here."*

**(b) The mathematical half — the binding, derived.** E.24 faced the identical question at its
own `vartheta` field and recorded three options with reasons; chapter I inherits the same three,
and TWO are closed by machine evidence (the pincer of §I-D13):

* *quantify over the data* — E.24's rejected option 1 (*"this asserts the carrier at an
  ARBITRARY ambient residue datum `ρ`, and the ρ-defeat is machine-shown at REAL tower
  exponents"*). At chapter I it is worse than undischargeable: it is FALSE (§I-D13).
* *bundle the data existentially, or thread it as parameters and supply it at I.17* — E.24's
  rejected option 2, the D-D12 fabricable shape. (Note the equivalence a reader may miss:
  `(data) → (block at data) → C` IS `(∃ data, block at data) → C`; parameterizing the structure
  and letting I.17 take the data is therefore the SAME move as the existential bundle, and
  falls to the same refutation genre.)
* *bind the data* — what E.24 did (threading), and what chapter I must do in the only form
  available to a `Prop` whose data are not yet constructible: a NAMED SOCKET restricting the
  quantifier to the arising configurations. **Signed: NODES I.10a/I.10b, with the `ladder` field
  guarded by I.10a.**

**Why the socket and not a landed sufficient condition.** Everything landed today that pins `ρ`
enough to help *already implies the carrier* — `Gauge.hvarthetaRes_of_arena_agree` (agreement
with an arena's residue read) and `Gauge.hvarthetaRes_of_tau_letters` (the τ-letter law) both
CONCLUDE `HVarthetaRes`. Guarding with either would retire ledger row HYP.57 by
hypothesis-shuffling: the conjunct would still be printed on Display A while carrying nothing.
Hence the **NON-SWALLOWING FENCE** (installed at §I-D13, restated at the nodes): *the socket
constrains the CONFIGURATION — that it is the one chapter C's tower produces — never the residue
law.* The typing template is OM-8's: `hvarthetaRes_deep3`'s hypothesis shape (the three letter
memberships that the corpus's canonical node-point read supplies).

**Certification (A-C.3's certify-before-sign; all machine-run in `leanspec/Leanspec/ChapI.lean`):**

1. the repaired application ELABORATES against landed E.24, and all three projections
   (`.lb1` at `Nonempty (BlockSuite I)`, `.mp1` at `Nonempty (MidPeelEmission B B')`, `.vartheta`
   at chapter D's sitewise `HVarthetaRes`) are extracted from the guarded field as TERMS;
2. **the re-sign weakens nothing today**: with I.10a at its placeholder body, the guarded field
   type is proved `↔` the 0e unguarded one — the narrowing to arising configurations is
   deferred to, and happens exactly at, the socket's typing (which is the gate-(a) event the
   owner is flagged on);
3. **the refutation that forces the socket is exhibited** (§I-D13's transport), and its reach
   into the re-signed structure is proved: while I.10a reads `True`,
   `¬ CapstoneHypotheses.{…} n` follows from one certified-false `(C, B)`;
4. the I.10b→I.10a refinement is proved by construction (`.1`).

**What is NOT claimed.** Signing the socket does not repair the contradiction — only TYPING it
does. Until then I.10 remains what the 0e gate called it: an ELABORATION GATE, not a signature,
and no fleet agent may fire on it.

---

### I-D4 — the `𝒲_{≤i}` half of the `∀ i ≥ 3` conjunct: the missing field, SIGNED at E.63

**Verdict: a frozen Display-A conjunct had no carrier; the field is added, at E.63's packaging
of BOTH halves.** Display A's conjunct is `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` (rows HYP.57/HYP.63).
The `ladder` field reaches E.24's `LadderSupply`, and landed E.24 packages the ϑ-half ONLY —
its own docstring says so: *"E.62's `𝒲` leg is conjoined at chapter I, not here."* So as signed,
chapter I dropped `𝒲_{≤i}` silently.

**Signed:** a new field `deepTwist`, consuming landed `Ladder.DeepTwistConjunct` (E.63,
`leanfinal/Uniformity/ChapE/E63.lean`), which packages both halves at the TYPED sockets
(E.61's `VarthetaRes` → chapter D's A-D.2 sitewise `HVarthetaRes`; E.62's `WFrame` → D.55's
cumulative `Wle` at D.44's `GentowW`) and threads ONE use-height family `q` through both — E.63's
own fence: *"Splitting it into two independent families here would let a consumer satisfy the
HVR leg at one set of use-heights and the `𝒲` leg at another, which is not the corpus's
conjunct."* The field is guarded by I.10b (the arena family needs the same arising restriction:
`GentowW` at an arbitrary `(A, R, w)` is refutable for the same reason as everything else in
§I-D13).

**Recorded redundancy (deliberate, harmless):** the ϑ-half is now carried twice — inside
`ladder`'s `.vartheta` projection and as `deepTwist`'s first component — at the SAME level data,
because E.24 is one committed bundle and its field list is not chapter I's to edit. The
field-level source of truth for the `∀ i ≥ 3` conjunct is `deepTwist`. **Certification:** both
halves are extracted from the new field as terms (`.1.supplied : HVarthetaRes …`,
`.2 : WFrame A q R w i`) in the §4 gate.

**Two consequences that were FALSE AS WRITTEN and are corrected here (strike-and-note, §12 and
NODE I.20 both amended inline):**

* §12's rider-(iii) sanity check read *"Nothing else on the frozen display lacks a carrier ✓"* —
  false at composition (`𝒲_{≤i}` lacked one), TRUE again under A-I.1's field list;
* NODE I.20's S3 row read *"**exactly the §4 field list** — i.e. §3's 36 OPEN-MATH rows + the
  CITEs, and nothing else"* — false at composition (the field list was SHORT of Display A by one
  conjunct), and true again under A-I.1's field list, with the standing caveat that the two weld
  placeholders (§I-D7/§I-D8) are still `True` and therefore carry no content.

---

### I-D7 / I-D8 — the weld placeholders and the missing `w1` field: RULED, not signed

**Verdict on I-D7 (I.10 signed in a state §11 forbids): the prohibition STANDS, its blocker is
RE-POINTED, and the fields stay at `True`.** The 0e gate reasoned that OM-9's landings
(`Weld.JD0Box2` F.04, `Weld.GenhnBox2` F.11, `Weld.W1Transport` F.12) make the placeholders
stale — that L-1/L-2 are executable now. **They are not**, and the reason is machine-checkable:
the consumption shapes the 0e gate exhibited quantify over ALL sites, and at least one of them
is REFUTABLE. `W1Transport Rh RG` is equivalent to equality of vanishing loci (F.12w's
`w1Transport_iff_zero_iff`), and mismatched loci refuse every transport, so
`∀ (K ι) (Rh RG : ι → K), W1Transport Rh RG` is FALSE — proved in this amendment's gate at
`ι = Fin 1`, `K = ZMod 3`. Binding the weld fields at those shapes would add a SECOND,
independent contradiction to the hypothesis block. The same site-supply socket the ladder needed
(I.10a's pattern) is what L-1/L-2 must bind through.

**Ruling, binding on the resolution pass:** §9.3's items L-1 and L-2 have their trigger changed
from *"F freeze"* (which has occurred) to **"the weld site-supply socket"** — a per-site-type
arising predicate, composed on the same GC-13(c) pattern as I.10a/I.10b, at chapter F's site
layer or chapter I's next amendment. Until then `jd0` and `genhnBox2` stay at `True`, §11's
forbidden-to-sign row stays in force, and I.10 stays an elaboration gate.

**Verdict on I-D8 (no `w1` field for OM-9's note to ride on): the omission is REGISTERED as
owed, at the same trigger.** F.28's landed `WeldObligations` carries three fields
(`jd0box2`, `genhnBox2`, `w1`); I.10 carries one and a half. When L-2 binds, it binds **three**
fields, and the `w1` field carries OM-9's honesty note verbatim: *`w1Transport_iff_zero_iff`
proves the carrier is the transport's SIGNATURE, and `w1Transport_of_ne_zero` makes any
instantiation at nonvanishing families FORMALLY TRIVIAL — a typed `w1` field discharges NOTHING
of HYP.139* (whose MATH content is TR-3′-GEN's compatible dictionary at general order). A-I.1
does not add the field, because adding it at the only shape available today is exactly the
contradiction above; it makes the omission a NAMED DEBT instead of a silent one.

---

### I-D9 — I.03's `(A1)`-admissibility clause: the source CARRIES content; the clause is
### RE-SIGNED at the enumeration (not struck)

**Verdict: CONTENTFUL, and the signed clause lost the content.** The adjudication is from the
node's own STATEMENT and from the ledger row, both of which say more than the signed Lean:

* NODE I.03 STATEMENT, verbatim: *"the menu is carried by an `A1Family` … **whose cells'
  σ-labels enumerate `S`**"*. **Enumerate is two-directional.** The signed clause carried the
  ⊆ half only (`∀ C ∈ F, C.σ ∈ S`), and the missing ⊇ half is exactly what the empty family
  exploits.
* ledger HYP.26, verbatim: *"a finite disjoint q-independent family list carries internal σ_F
  labels and exact weights; σ is not an A1 binder"* — a family that carries labels for the
  menu's types, not a family that may be empty.

So the clause is NOT redundant and must NOT be struck; it is re-signed with the reverse
inclusion added (signature block at NODE I.03 above):

```lean
    (∀ σ ∈ S, ∃ C ∈ @id (List (Induction.A1Cell r)) F, C.σ = σ) ∧
```

**Certification (the A-E.2 standard: the re-signed form must not be satisfiable by the witness
that killed the old one), all machine-checked in `leanspec/Leanspec/ChapI.lean`'s §4 gate:**

1. **The refutation of the OLD form is PRESERVED VERBATIM** as `MenuLawAtVoided` (named-and-
   voided, the `OM4Shadow.*` pattern) together with its proof
   `MenuLawAtVoided n ↔ ∃ S, (∀ σ ∈ S, σ.degree = n) ∧ ∀ O …, CoveringMenu O n S` — the
   `A1Family` existential adds nothing. **No consumer, gate or census row may cite
   `MenuLawAtVoided`.**
2. **The empty family no longer satisfies the re-signed shape clause at any nonempty menu**:
   `¬ (∀ σ ∈ ({σ₀} : Finset FactorizationType), ∃ C ∈ ([] : List (A1Cell 0)), C.σ = σ)`,
   proved. So the OM-4 FINDING-0 witness genre is dead against the new form.
3. **Non-vacuity is preserved where it was earned**: `MenuLawAt 2` is still PROVED
   unconditionally at gate I.23 — but now with a REAL three-cell family (σ-labels
   `splitType`, `inertType`, `ramType` at `r = 0`), not the empty list. The old witness was
   cheap precisely because the clause was empty; the new one exhibits the enumeration.

**What the re-sign does NOT close (disclosed, unchanged):** the WEIGHT-correctness tie
(`A1Cell.coeff` + the count laws, §3 rows HYP.23/32/35) stays OPEN-MATH and outside the
carrier — I.03's own ⚠ SIGNATURE NOTE is untouched and still governs. The re-sign kills the
vacuity, not the disclosed gap. **I.13's COND resolution is correspondingly upgraded**: what
`COND:A1_n` resolves to today is the menu clause **plus the label enumeration**, still not the
weight tie.

---

### I-D5 — I.03's `∀ C ∈ F`: the intended membership, adjudicated and signed

**Verdict: the intended membership is LIST membership on `A1Cell r`, and the `@id` spelling is
signed as the blueprint form (not merely a stub-side repair).** H.93 lands
`def A1Family (r : ℕ) : Type := List (A1Cell r)` — a plain `def`, so `Membership` instance
search does not see through it and the committed `∀ C ∈ F` fails to elaborate (cascading into
`cannot resolve field 'σ'`). A type ascription does not cure it (ascription is transparent).
The signed spelling is `∀ C ∈ @id (List (Induction.A1Cell r)) F, …`, which is TYPE-IDENTICAL
(the two types are definitionally equal) and elaborates.

**Root-cure option left open for the fleet** (either is acceptable, neither is required by this
amendment): make H.93's `A1Family` an `abbrev`, or land a
`Membership (A1Cell r) (A1Family r)` instance. **If the root cure lands, this amendment's
`@id` spelling reverts to the plain `∀ C ∈ F` with no other change** — the statement is the
same either way, which is why this defect is an elaboration repair and not a strength event.

---

### A-I.1's OWNER-FACING FLAG LIST (read at the next visit; nothing here waits on it)

| # | what changed | why it is not a weakening | where |
|---|---|---|---|
| **1** | **I.10's FIELD LIST: the `ladder` field is guarded by a new socket (I.10a), and a NEW field `deepTwist` is added (guarded by I.10b).** This is the public conditionality display — CONVENTIONS Part V gate (a). | No conjunct dropped; ONE conjunct ADDED (`𝒲_{≤i}`, which had no carrier at all); the conclusion `UniformityStatement` untouched; and the guard is proved to change nothing while the sockets read `True`. The eventual narrowing (when chapter C types them) restricts a HYPOTHESIS, i.e. strengthens the theorem — the direction the blueprint's own quantifier disclosure already contemplated. | §I-D3, §I-D4; signature block at NODE I.10 |
| **2** | **Two NEW nodes, I.10a/I.10b** (`CanonicalLadderConfig`, `CanonicalDeepTwistConfig`), GC-13(c) sockets with `True` bodies owed at chapter C's freeze. | They are the binding site the field list previously lacked; their `True` bodies make the guarded fields equivalent to the unguarded ones today (machine-proved), so signing them moves no strength. | §I-D3; NODE I.10's block |
| **3** | **I.03 (`MenuLawAt`) is RE-SIGNED** with a second clause (the σ-label enumeration). | Strictly stronger as a carrier: re-signed ⟹ voided is proved, and the empty-family witness that satisfied the old clause is proved to fail the new one. *Note the direction, deliberately: strengthening a HYPOTHESIS field makes I.17 assume more — which is what the honesty doctrine demands here, because the old clause was VACUOUS and a trivially satisfiable conjunct tracks no conditionality (OM-4 FINDING-0). What is now carried is Display A's own conjunct, so the CLAIM does not shrink; the conditionality display stops overstating what has been reduced.* | §I-D9 |
| **4** | **The stop-the-line disclosure (I-D13)**: as of today the capstone hypothesis block is CONTRADICTORY, so I.15–I.18 fire from `False` and no positive conditional claim may be made from I.17. | Not a change — a DISCLOSURE of what the signed statements already meant. The repair is chapter C's socket typing. | §I-D13; NODE I.20's corrected report sentence |
| **5** | **`UniformityStatement` is untouched** (gate (a)'s main statement), and no literature cite was imported or signed (gate (b)); I.01's cite instruction was re-pointed at an already-drafted REDRAFT that still awaits the owner's signature. | — | §I-D6 |

---

### A-I.1's CLOSING STATE (what the next agent inherits)

**Signed by this amendment:** the `ladder` field's repaired application + arising binding (I-D3);
the `deepTwist` field (I-D4); NODES I.10a/I.10b (new); I.03's enumeration clause + `@id`
membership (I-D9, I-D5); I.01's re-pointed resolution instruction (I-D6). **Ruled, not signed:**
I-D7/I-D8 (weld placeholders stay; `w1` is a named debt; L-1/L-2 re-triggered). **Disclosed:**
I-D13. **Untouched:** `UniformityStatement`; every ledger row's disposition (no row moved
bucket, none was discharged); the tame/cite queue; WELD-ZERO (I-7 licenses nothing, still).

**Machine state:** `leanspec/Leanspec/ChapI.lean` carries every signed form, elaborated —
`lake build Leanspec.ChapI` green, zero `sorry`, zero `native_decide`, 70 enforced `#axiom_core`
guards, all Lean-core. The §4 gate now runs 14 checks, five of them A-I.1's certifications: the
I-D13 transport (`¬` the 0e field type, and `¬ CapstoneHypotheses n`), the never-weaken `↔`, the
I.10b→I.10a refinement, the I-D9 pair (empty family fails the new clause; new ⟹ voided), and
the weld-shape refutation behind the I-D7/I-D8 ruling.

**The next three moves, in dependency order:** (1) chapter C types I.10a/I.10b under the
NON-SWALLOWING fence — this is what lifts I-D13; (2) the weld site-supply socket, then L-1/L-2
bind `jd0`/`genhnBox2`/`w1`; (3) the owner's gate-(b) signature on the C.94 REDRAFT, after which
I.01 resolves and gate I.25 gains its first `#axiom_reg` entry. Defects I-D1/I-D2 (`leanfinal`
duplicate declarations and roll-up gaps) remain the precondition for landing chapter I at all,
and are cured on the `leanfinal` side, not here.

<!-- SENTINEL: BP-I END OF FILE -->






