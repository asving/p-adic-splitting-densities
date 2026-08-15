# CHAPTER E — THE σ-LADDER (T2's master suite, the HE7 rung machinery, and the ladder's σ dictionary)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs), under
`blueprint/CONVENTIONS_2026-08-15.md` (GC-1…GC-14 + BRIEF E; Part V owner ruling in force).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **E = σ-LADDER MASTER** — 105 DAG
nodes by the old cut (`EFF-T2` alone). **The czar ruling (BRIEF E, ratified Part IV item 2 /
Part V item 2) adds `EFF-HE7`** (137 units: the `(SLOT₂)/(LIFT₂)` level-2 machinery and the HE7.A
master suite) to this chapter. **True planning figure: 242 source units** (105 T2 + 137 HE7),
of which the node-bearing mathematical mass is far smaller — T2 is an ACCEPTED T-unit whose late
units are acceptance-boxes/fences/changes-records, and HE7's records likewise; the unit-by-unit
disposition census (§13) accounts for every one of the 242. **Blueprint node count: 68 nodes**
(§2's index is the authority; the census disposes the rest).
**Sources transcribed:** `spec/EFF-T2.md` (105 units, contiguous, merged from six shards) and
`spec/EFF-HE7.md` (137 units, contiguous, merged from three shards). Both cited at merged,
contiguous IDs per GC-12.
**Supplier chapters consumed:** **H §8 ONLY** (H.51–H.58, the slot/lift layer — the sanctioned
entry point per GC-5/H-14; H.54's `normIdx` is WITHDRAWN and is not consumed), **B** (§7/§9 by
committed node ID, on the `e₁ = 1` slice only), **C** by GC-13 placeholder (level data, twist/ϖ
layer, class-size counts), **D** by GC-14 anchor (the ϑ-orientation table), **A/G** (the landed
kernel) by declaration name.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle). New definitions in
`Uniformity.Density.Ladder` (GC-6.2).
**Authored:** 2026-08-15, Fable-max arm (append #56 substitution regime).
**CODEX CROSS-READ OWED** (queued post-Tuesday per the budget regime; a Fable-max fresh-context
read may discharge the obligation earlier per Part IV item 6's precedent).

---

## 0. How to read this chapter

### 0.1 The standing environments (chapter-prefixed per GC-6.3)

Every node names its environment as `ENV-E1` … `ENV-E4` plus deltas. Bare `ENV-A/B/C` are retired.

**ENV-E1 — the arithmetic arena** (the ladder's exponent/height bookkeeping; no `O`):

```lean
import Uniformity
namespace Uniformity.Density.Ladder
open Finset
```

**ENV-E2 — the density arena** (= CHAP-H's ENV-H2, verbatim; stated here in full per GC-6.3):

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}
```

`ENV-E2′` abbreviates ENV-E2 with `π` promoted to an explicit hypothesis `(hπ : Irreducible π)`
(landed precedent `Drainage.lean:85`, `DensityAPI.lean:124`).

**ENV-E3 — the stage-field arena** (= CHAP-H's ENV-H4, verbatim — pure finite-field algebra, no
`O`; abstract-then-instantiate per GC-7):

```lean
import Uniformity
namespace Uniformity.Density.Ladder
open Polynomial
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K]
```

**ENV-E4 — the polygon/support arena** (CHAP-B's D-1 objects consumed by node ID; the slot-seam
evaluation layer): ENV-E2 plus CHAP-B's development/`suppVal`/`npHgt` API in scope by import of
the (future) landed `ChapB` modules. Per GC-1, every residual-read pin in this arena is the
`sideMin` pin; per GC-2, every polygon statement is an argmin/support-function statement — no
hull object, no `ℚ`.

Environments are declared per NODE, not per section (GC-6.4). `[Finite (ResidueField O)]`
appears only where a node counts or names `Res`/`Coeff`/`residueCard`/`DecidedAt`-family objects.

### 0.2 File layout and naming (GC-6)

* One Lean file per node: `leanfinal/Uniformity/ChapE/E<nn>.lean`, module
  `Uniformity.ChapE.E<nn>`; micro-nodes suffix a letter (`E10a.lean`).
* Chapter roll-up `leanfinal/Uniformity/ChapE.lean` imports node modules in this file's
  topological order; `Uniformity.lean` gains one line. `ChapE.lean` imports `Uniformity.ChapH`
  (for H.51–H.58 ONLY — consuming any other H node from E is a blueprint defect, GC-5) and the
  future `Uniformity.ChapB` modules named in DEPENDS fields.
* New *definitions* live in `Uniformity.Density.Ladder`; new *theorems about landed objects* live
  in `Uniformity.Density`. Other chapters' sub-namespaces (`.Menu`, `.Leaf`, `.Induction`,
  `.Tower`, `.Gauge`) are READ, never extended.
* One PUBLIC declaration per node; reusable helpers trigger RE-PLAN, never a silent second name.
* Leanspec stubs wrap in `namespace LeanspecE` (GC-6.6), file `leanspec/Leanspec/ChapE.lean`;
  gate order = CHAP-H §15's (elaborate fragile signatures → land `def` bodies → run the §10
  numeric block at `q = 2` AND `q = 3` → only then sign `axiom` stubs).

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (chapter A, the landed kernel).** Consumed by name:
`FactorizationType`, `FactorizationType.degree`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_degree`, `typeOf_mul`, `monicFactors`, `efPair`, `ramIndexOf`, `inertiaDegOf`,
`Coeff`, `Res`, `proj`, `residueCard`, `two_le_residueCard`, `DecidedAt`, `decidedAt_of_congr`,
`UniformityStatement`, `UniformityStatement.ofDecided`, `DrainageAt`.

**From `Uniformity.Density.Induction` (CHAP-H §8, the sanctioned slice H.51–H.58 ONLY).**
`class_sep`, `class_sep_bij` (H.51); `slot_height_injective`, `slot_min_unique` (H.52);
`eta_independent` (H.53); `stageLift'` (H.54 — the SIGNED form; `normIdx` is WITHDRAWN and no
chapter-E node consumes it); `stageLift_index_lt`, `stageLift_integral`, `stageLift_height`
(H.55); `stageLift_summand_eq` (H.56); `wrap_div_mod`, `wrap_height` (H.57); `divMod_bij`,
`card_composedBasis` (H.58). Also `GenreDatum` and its derived fields (H.01/H.02), which the
H.51–H.58 signatures carry — consumed as their parameter types, nothing more of H.

**From CHAP-B (committed blueprint node IDs; `e₁ = 1` slice).** By node ID per GC-13(b):
B.19/B.20 (`suppVal`, side lengths), B.28–B.30 (`resPoly` + correctness under the `sideMin` pin,
GC-1/PA-1), B.51 (residual index), B.58 (the order-1 `(e,f)` read), B.63/B.73/B.74 (separability
hypothesis + `NeedsDescent`, as REPAIRED by PA-1), B.77 (`resPoly_congr`, convention-free),
B.79–B.82 (level-`N` certificates).

**From chapters C and D (unauthored at composition time).** GC-13(c) placeholders only —
`EFF.<NOTE>.<nn> [supplied-by: chapter C]` — and GC-14 anchors for the ϑ table (chapter D owns
the canonical copy; no chapter-E node restates its content).

### 0.4 The chapter's mathematical spine, in one page

T2 is the corpus's σ-ladder MASTER: it does not prove new ladder mathematics — it *organizes*
the HE-chain's rung results (HE7's level-2 `(SLOT₂)/(LIFT₂)` machinery, HE6's seam evaluations,
HE6R1's level dictionary) into one master suite, `HE7.A`, whose five clauses
`[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]` are Display A's `HE7A[…]` conjunct.
The chapter's Lean character therefore splits three ways, exactly as CHAP-H's did:

| layer | corpus content | Lean character | sections |
|---|---|---|---|
| **carrier/schema** | the rung datum, the ladder as iterated rungs, the HE7.A clause family | `structure`s with hypothesis fields at EXACTLY corpus strength (the `StageInterface` lesson) | §3, §4 |
| **algebraic/arithmetic** | slot-seam exponent bookkeeping, the level-2 slot/lift laws (SLOT₂/LIFT₂), degree conservation, the σ dictionary | provable outright from H.51–H.58 + B's API + `ℕ` arithmetic | §5, §7 |
| **carried hypotheses** | (LB1), (MP1), `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` (∀ i ≥ 3), the μ ≥ 3 σ-decision, exhaust/root-continuation at depth | NOT provable at transcription grade — named, indexed hypothesis carriers handed to chapter I | §4, §6, §8, §9 |

The terminal supply — what H's §11 dictionary and the drainage recursions consume from E — is
named prominently in §2 and §7: the **ladder transport laws** (`ladderSigma` + its degree
conservation `ladderSigma_degree`, the rung-composition law `rungStep_sigma`) and the
**stage-transport carriers** (`RungInterface` instances). GC-4 binds every σ output: every
σ-valued thing in this chapter is a `Uniformity.Density.FactorizationType` produced by a named
dictionary function shipping a degree-conservation lemma.

---

## 1. HONESTY BLOCK (read before consuming any node)

**E-1 — THE HE6/T2 ADJUDICATION (HYP.150–154) GOVERNS THE 48 SLOT-SEAM CITES.** *(Detailed
dispositions in the nodes; summary here.)* `EFF-HE6.md` OPEN-CALL 2 found that A3 corrections
F-1/F-3/F-4 land outside every one of T2's nine HE6 pin spans, with F-1 rendering the frozen
`HE6-SLOT-SEAM` bare display VACUOUS (affirmatively FALSE for `k > (D′−1)h`, HYP.151) while T2
cites that span 48×. The adjudication (T2 EOF append, commit `66062771`; ledger rows HYP.150–154,
v7) returns: T2's own `(GAMMA)`/`(HE6-SEAM)` displays already ARE F-1's corrected form
letter-for-letter, so **no chapter-E node ever transcribes the bare pre-A3 `HE6-SLOT-SEAM`
display**; every seam evaluation in §5 is stated in the corrected `γ_k(A)` form via T2's own
displays. HYP.154: T2 consumes NO disk criterion (`LEMMA HE6-0`) — no E node states one; a
consumer needing HE6-0 is a chapter-cut concern outside E (route: the C placeholder layer).
**Residual carried honestly:** HYP.150 is scoped to T2 ONLY; HE7's own consumption of the three
A3-corrected HE6 spans is UNCHECKED at the ledger (HYP.150's explicit residual). Every §4/§5 node
whose SOURCE is an HE7 unit citing an HE6 span therefore carries the flag `[HE6-A3-UNADJUDICATED
FOR HE7]` and states the content from HE7's own displays, never from HE6 frozen text.

**E-2 — the nine HE6 pin anchors resolve per the F1 routing, and two of them leave the chapter.**
The pin anchors (`EFF.HE6.09 .13 .14 .15 .17 .29 .30 .32 .56`) resolve to CHAP-B node IDs only on
the `e₁ = 1` slice (where B transcribed them). The class-size/count route in `.30`/`.32` is
CHAP-B's H-2 refusal — it must come from chapter C (Brief C trap (i) owns the decision), and the
`e₁ ≥ 2` twist/ϖ-normalizer content of `.13`/`.14` is CHAP-B H-1 out-of-scope: both resolve to
**chapter-C GC-13 placeholders** (`EFF.HE6.30/.32 [supplied-by: chapter C]`,
`EFF.HE6.13/.14 [supplied-by: chapter C]`), never to HE6 frozen text and never to a nonexistent
B node. No chapter-E node may cite those four anchors any other way.

**E-3 — the σ-decision at `μ ≥ 3` is `BLOCKED: HYP.81` for everyone, and the ladder CARRIES it,
never proves it.** (First live `n = 6`.) The ladder's σ dictionary (§7) extends H §11's σ-decision
content ALONG the ladder — i.e. transports σ through rungs — which is exactly GC-5's `hsigma`
assignment to E. What E does NOT do: decide σ at a stage leaf of multiplicity `μ ≥ 3`. Every node
whose corpus text touches that case carries `(hσ₃ : …)` as an explicit hypothesis field routed to
chapter I's hypothesis block, or returns `BLOCKED: HYP.81`. A fleet agent reaching for a `μ ≥ 3`
σ-decision has left the chapter.

**E-4 — (LB1) and (MP1) are Display A conjuncts and their disposition is decided per node, not
assumed.** BRIEF E clause (2): if a discharge exists in T2's effective text, it is a discharge
node; else a carried hypothesis routed to I (Part V: each such carry must terminate as a
discharge node or a literature cite through owner gate (b) — no third category). §6 records the
adjudication per unit with T2's own text quoted.

**E-5 — `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` (Display A's `∀ i ≥ 3` conjunct) are INDEXED CARRIERS.**
E supplies the named, `i`-indexed hypothesis structures (§9); the `𝒲_(≤i)` content itself is
chapter D's w-frame (T5) by GC-13, and the ϑ-residue content cites chapter D's canonical
orientation table by anchor (GC-14) — no chapter-E node restates the four-way table, and no
chapter-E node adjudicates the ϑ ↔ ϑ_t correspondence.

**E-6 — the q = 2-only coincidence regime is a standing trap in exactly this chapter's numerics.**
HYP.151's own witness `(e₁,f₁,h) = (2,2,3)`, `k = 3` sits in the coincidence regime
`k ≤ (D′−1)h` where bare and corrected seam readings agree — four hostile rounds missed the
defect for exactly that reason. Chapter E's gates (§10) therefore include a seam witness in the
NON-coincidence regime `k > (D′−1)h` at BOTH `q = 2` and `q = 3`, plus an `e > 1 ∧ f > 1`
witness (GC-11). A gate that only exercises `k ≤ (D′−1)h` is a defect.

**E-7 — the 44-edge cluster at `EFF.T2.31` is a governing-unit placeholder artifact.** The edges
land there because citing designations were unresolved at harvest time (DAG_README's gov rule),
not because `.31` is the real consumer. This chapter's DEPENDS fields re-home those edges unit by
unit; §11's DAG-addition rows carry the re-homing with contiguous IDs in the evidence column
(GC-12).

**E-8 — `HEX3-BOX-1` (HYP.137) is a NON-NODE here**, as in G (H-2) and H (H-4). A fleet agent
needing the tail-σ certification lemma returns `BLOCKED: HYP.137`.

**E-9 — no every-lift weakening (GC-9), even where T2's prose quantifies over `disc ≠ 0` roots.**
Ladder certificates conclude `DecidedAt` unweakened; σ is read through `monicFactors`/`typeOf`
(total on monic polynomials); divergences from root-read prose are flagged per node in
FAITHFULNESS. No uniform-`N` law anywhere (GC-9.3): certificates are per-member at explicit `N`.

**E-10 — transcription grade (GC-10) governs T2 nodes; HE7 nodes inherit the same rule.** T2 is
an ACCEPTED T-unit: the EFF canonical statements are the spec; fresh mathematics enters only via
a dated AMENDMENT block. Trichotomies/case splits are re-derived from the note's own displays,
never from a verifier's phrasing (the GENH4-CAP `[r2]` lesson); no false-reason parentheticals
are transcribed (the WZ-BOX-7 lesson — side with conclusions).

**E-11 — codex cross-read status: OWED.** Flagged items aggregated in §14.

*(Amendments to this block as composition proceeds are dated in place.)*

---

## 2. NODE INDEX

*(committed early; refined per section as composed — the per-section node lists below are the
authority once their section is composed; counts updated at completion)*

| § | nodes | content |
|---|---|---|
| 3 | E.01–E.09 | **THE RUNG/LADDER SCHEMA**: the rung datum, the ladder carrier, the reconciliation to `GenreDatum`/H §8 |
| 4 | E.10–E.24 | **THE MASTER HE7.A SUITE**: the five clauses `[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]` as fields + the five instance records |
| 5 | E.25–E.38 | the slot-seam evaluation layer (corrected `γ_k(A)` form; B's `suppVal` API; SLOT₂/LIFT₂) |
| 6 | E.39–E.44 | (LB1)/(MP1): adjudicated dispositions |
| 7 | E.45–E.54 | **the σ dictionary + degree conservation** (GC-4; terminal supply) |
| 8 | E.55–E.60 | root-continuation / exhaust clauses at ladder depth |
| 9 | E.61–E.64 | the `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers |
| 10 | E.65–E.68 | gates (GC-11: `q = 2` AND `q = 3`; non-coincidence seam witness; `e > 1 ∧ f > 1`) |
| 11 | — | DAG additions (incl. the EFF.T2.31 re-homing rows) |
| 12 | — | leanspec stub list (stage 0e, `LeanspecE`) |
| 13 | — | unit-disposition census (all 242 source units) + TEETH summary (GC-8) |
| 14 | — | flagged for the codex cross-read |

**Terminal supply (what other chapters consume from E), named now:** `RungDatum` (E.01),
`RungInterface` (E.10) with the HE7.A clause fields, `LadderData` (E.05), the σ dictionary
`ladderSigma` + `ladderSigma_degree` (E.45/E.46), the rung transport law `rungStep_sigma` (E.48),
the stage-transport/composition laws (E.49–E.51), the indexed carriers `VarthetaRes` / `WFrame`
(E.61/E.62), and the HE7A conjunct package `HE7APackage` (E.24) — the object chapter I's
hypothesis block receives.

---

<!-- RESUME: skeleton committed. Next: read EFF-T2 units .01–.44 + lemma units, EFF-HE7 math units, then compose §3. -->

*(sections §3–§14 follow in dependency order; composed incrementally, committed per 2–3 nodes)*
