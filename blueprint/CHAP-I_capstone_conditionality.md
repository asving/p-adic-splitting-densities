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
only). Lean files: I01–I03, I05–I10, I15–I18, I21, I23–I25 (16 files).

<!-- RESUME: front matter + honesty + index committed. Next: §3 disposition table. -->
