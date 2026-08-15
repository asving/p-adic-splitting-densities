# CHAPTER F — THE GRT WELD LAYER (consumer-first from Display A's two surviving weld conjuncts)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs), under
`blueprint/CONVENTIONS_2026-08-15.md` (GC-1…GC-14 + BRIEF F; Part V owner ruling in force).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **F = GRT WELD LAYER** —
**538 DAG nodes** over `GRTJA, GRTJB, GRTJC, GRTW2, WELDMASTER, LIFTCORNER, SIGMALAW` at the
harvest's counting (the raw `###` heading recount at HEAD is 540; BRIEF F's SERIES-aware unit
count is **567** — GRTJB carries 173 units under 157 headings and GRTJC 132 under 121, SERIES
constructs holding multiple units per heading; all three figures recorded, none silently
substituted). **But the weld-face audit (2026-08-13, ledger fold v4/v5) signed most of this
layer OUT of the capstone cone**: 9 of its 10 chartered rows returned NOT-REACHED, the whole
`[H-c]` value package left Display A, and the spine consumes exactly TWO weld faces. This
chapter is therefore authored **consumer-first from Display A's two surviving weld conjuncts
backwards** (BRIEF F), and the out-of-cone mass is disposed by census (§3, §13), never
transcribed. **Blueprint node count: 30 nodes** (§2's index is the authority; the census
disposes the rest — the compression from 538 DAG nodes to 30 is the chapter's honest content).
**Sources transcribed:** `spec/EFF-GRTJA.md` (36 units), `spec/EFF-GRTJB.md` (173 SERIES
units), `spec/EFF-GRTJC.md` (132 SERIES units), `spec/EFF-GRTW2.md` (60, merged),
`spec/EFF-WELDMASTER.md` (30), `spec/EFF-LIFTCORNER.md` (118, merged), `spec/EFF-SIGMALAW.md`
(18). All cited at merged, contiguous IDs per GC-12 (every one of these seven notes has a
merged spec at HEAD; no shard-local remap is needed for F). One out-of-chapter source is
consumed for ONE interface statement: `spec/EFF-JD0.md` (chapter G's note; G closed WITHOUT
transcribing JD0, and BRIEF F product (1) assigns the `JD0-BOX-2` interface statement here).
**Supplier chapters consumed:** **H** by committed node ID (H.61's fibre count and H.87's
carry cancellation — the two theorems that replace type-preservation claims; plus H.98's
package pattern read as format only), **D** by GC-13 placeholder (T-chain faces) and GC-14
anchor (the ϑ-orientation table — D owns the canonical copy; no F node restates it), **C/E**
by GC-13 placeholder, **A/G** (the landed kernel) by declaration name.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle). New definitions
in `Uniformity.Density.Weld` (GC-6.2).
**Authored:** 2026-08-15, Fable-max arm (append #56 substitution regime).
**CODEX CROSS-READ OWED** (queued post-Tuesday per the budget regime; a Fable-max
fresh-context read may discharge the obligation earlier per Part IV item 6's precedent).

---

## 0. How to read this chapter

### 0.1 The standing environments (chapter-prefixed per GC-6.3)

Every node names its environment as `ENV-F1` … `ENV-F3` plus deltas. Bare `ENV-A/B/C` are
retired (GC-6.3).

**ENV-F1 — the arithmetic/carrier arena** (multiset, character-exponent and interface
bookkeeping; no `O`):

```lean
import Uniformity
namespace Uniformity.Density.Weld
open Finset
```

**ENV-F2 — the density arena** (= CHAP-H's ENV-H2, verbatim; stated in full per GC-6.3):

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}
```

`ENV-F2′` abbreviates ENV-F2 with `π` promoted to an explicit hypothesis
`(hπ : Irreducible π)` (landed precedent `Drainage.lean:85`, `DensityAPI.lean:124`).

**ENV-F3 — the stage-field arena** (= CHAP-H's ENV-H4, verbatim — pure finite-field algebra,
no `O`; abstract-then-instantiate per GC-7). The twisted-algebra/character content of §5
lives here:

```lean
import Uniformity
namespace Uniformity.Density.Weld
open Polynomial
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K]
```

Environments are declared per NODE, not per section (GC-6.4). `[Finite (ResidueField O)]`
appears only where a node counts or names `Res`/`Coeff`/`residueCard`/`DecidedAt`-family
objects.

### 0.2 File layout and naming (GC-6)

* One Lean file per node: `leanfinal/Uniformity/ChapF/F<nn>.lean`, module
  `Uniformity.ChapF.F<nn>`; micro-nodes suffix a letter.
* Chapter roll-up `leanfinal/Uniformity/ChapF.lean` imports node modules in this file's
  topological order; `Uniformity.lean` gains one line. `ChapF.lean` imports `Uniformity.ChapH`
  (for H.61/H.87 only, by node ID) and nothing from unauthored chapters (GC-13(c)
  placeholders resolve at the orchestrator pass).
* New *definitions* live in `Uniformity.Density.Weld`; new *theorems about landed objects*
  live in `Uniformity.Density`. Other chapters' sub-namespaces (`.Menu`, `.Leaf`,
  `.Induction`, `.Tower`, `.Ladder`, `.Gauge`) are READ, never extended.
* One PUBLIC declaration per node; reusable helpers trigger RE-PLAN, never a silent second
  name.
* Leanspec stubs wrap in `namespace LeanspecF` (GC-6.6), file `leanspec/Leanspec/ChapF.lean`;
  gate order = CHAP-H §15's (elaborate fragile signatures → land `def` bodies → run the §10
  numeric block at `q = 2` AND `q = 3` → only then sign `axiom` stubs).

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (chapter A, the landed kernel).** Consumed by name:
`FactorizationType`, `FactorizationType.degree`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_degree`, `monicFactors`, `efPair`, `Coeff`, `Res`, `proj`, `residueCard`,
`DecidedAt`, `UniformityStatement`, `DrainageAt`.

**From CHAP-H (committed blueprint node IDs).** H.61 (the fibre count) and H.87 (the carry
cancellation) — BRIEF F names these as "the two theorems that replace type-preservation
claims" (honesty F-3); consumed by node ID per GC-13(b). No slot/lift-layer H node is
consumed (H §8 is B/E's entry point; F needs none of it).

**From chapters C, D, E (unauthored or parallel at composition time).** GC-13(c)
placeholders only — `EFF.<NOTE>.<nn> [supplied-by: chapter <X>]` — and GC-14 anchors for the
ϑ table (chapter D owns the canonical copy; no F node restates or adjudicates ϑ-orientation
content).

### 0.4 The chapter's mathematical spine, in one page

The weld layer is the corpus's largest note mass (seven notes, 538 DAG nodes) and its
smallest surviving capstone surface. The weld-face audit (`runs/qgen/WELD_FACE_AUDIT.md`,
2026-08-13; ledger v4 fold, COR-WFA-01…13; ORPHAN-1 cured at v5) established, with per-site
re-verification at HEAD, that the capstone spine consumes exactly **two** weld faces:

1. **`JD0-BOX-2`** (HYP.74, CARRY; grade bar SIGNED at HYP.39) — the *unit-character
   gauge-form perimeter*: the warrant that the weld's entire conditional value dictionary
   acts by slot-wise unit characters. J-D0 is consumed DIRECTLY at seven cone notes at FRAME
   grade (W11, W12, HMENU3, HEX3, GENIND, GENH4, GENHN — every site exhibits the bijection
   itself); the surviving obligation is the perimeter statement those sites inherit.
2. **`GENHN-BOX-2`** (HYP.148, CARRY; live at `n ≥ 6`) — the *W-9 graded face*: LEMMA
   GENHN-4's layer 1 at `μ ≥ 3` consumes COROLLARY W-9's twisted group algebra as the carry
   bookkeeping — "the ONE weld face inside a count law" on the whole capstone path. It
   carries HYP.139 (the W-1 transport, MATH/ATTEMPT) as its sub-residue.

Everything else — the `[H-c]` value package (`VD-m`, `C-coll`, `R-coll`, `PERIM-μ`,
`DMULT-S`, `W2-VALUE`), the JB no-leg rows, the W-2→W-5 seam — is **NOT-REACHED** and gets
NON-NODE treatment (§3). The chapter's Lean character therefore splits three ways:

| layer | content | Lean character | sections |
|---|---|---|---|
| **interface carriers** | the two surviving conjuncts + the W-1 transport, at exactly ledger strength | named `Prop`-carriers handed to chapter I | §4, §5, §9 |
| **provable supply** | the Σ-law dictionary (SIGMALAW, PROVED in the corpus), the unit-character action's algebra, the structural-clause shells | theorems/defs outright | §5, §6, §7 |
| **disposed mass** | out-of-cone packages, acceptance/process records, the value layer | census rows, never nodes | §3, §13 |

Terminal supply — what chapters D, H(landed), and I consume from F — is named in §2 and §9:
the `JD0-BOX-2` carrier (`GaugeFormPerimeter`/`JD0Box2`), the `GENHN-BOX-2` carrier
(`GenhnBox2` + `W1Transport`), the Σ-law dictionary (`sigmaLawSigma` + degree conservation),
and the `WeldSupply`/`WeldObligations` package for chapter I.

---

## 1. HONESTY BLOCK (read before consuming any node)

**F-1 — THE OUT-OF-CONE RULING GOVERNS: no node for the value package, anywhere.** The v4
weld-face audit (widened charter, ten rows, AUDIT-ONLY) returned **1 REACHABLE-AND-CONSUMED ·
9 NOT-REACHED** (HYP.73's closure record), and the v5 ORPHAN-1 verification re-checked the
four orphaned value rows from scratch. OUT of the cone at HEAD: `HYP.21` (`[H-b]`/JB row 12),
`HYP.75` (`JB-NOLEG`), `HYP.76` (`W2-VALUE`), `HYP.77` (`DMULT-S`), `HYP.83` (`VD-m`),
`HYP.84` (`(C-coll)`), `HYP.85` (`(R-coll)`), `HYP.86` (`PERIM-μ`), plus `HYP.22` (the whole
`[H-c]` package). `dag_check.py` confirms all are unreachable from the capstone (7/7 on the
checked list). **A fleet agent asked for any of these returns `BLOCKED: OUT-OF-CONE (HYP.<nn>)`
— a node for them is wasted fleet mass and a false conditionality entry** (BRIEF F trap (i)).
§3 is the row-by-row census.

**F-2 — WELD-ZERO IS PENDING; NOTHING IN THIS CHAPTER RELIES ON IT.** Status verified at HEAD
(2026-08-15, this composition): `HYP.149` is **IN-PROGRESS at clean-pass 1 of 2** — the
composed unit passed its r1 repair round plus the Opus-arm hostile pass
(`runs/comp13/WZP2_output.log`, 0 CRITICAL + 0 GAP + 6 minors, folded); the second
(model-diverse) confirmation pass was REASSIGNED from gpt-5.6-sol to a Fable-max agent
(`docs/PROJECT_STATE.md` append #56: "WELD-ZERO confirmation pass (pass 2 of 2) runs on
Fable-max now") and is **IN FLIGHT with no landing commit in the tree** (checked through
append #61; `leanfinal/notes/` carries no WELD-ZERO note; the unit note is
`lean/notes/openmath/WELDZERO_2026-08-14.md`, status line "composed, attempt 0/2, hostile
arc owed"). Consequences, per BRIEF F trap (ii): WELD-ZERO has NO effective spec
(`EXT:WELDZERO_2026-08-14.md`), F **transcribes no WELDZERO content**, and the arc is carried
as PENDING (§8) with the ledger rows cited. HYP.148 stays CARRY and HYP.139 stays MATH at
full strength in every §5 statement; §8 records exactly what a landed pass would change and
under whose authority.

**F-3 — THE WZ-BOX-7 RULE: never state a type-preservation claim about a twist map.** The
twist dictionary is NOT type-preserving — 972/972 live-wrap flips, machine witness; the
WELDZERO r1 round withdrew exactly such a claim (WZ-3(ii)) as FALSE at live ϑ. Per BRIEF F
trap (iii) and GC-10's rider: every §5/§7 node sides with **conclusions** — cancellation
identities and cardinalities — and the two theorems that replace type-preservation claims
are consumed by name: **H.87** (carry cancellation) and **H.61** (fibre count). A node whose
draft statement says "the twist preserves the type/form of …" is a defect.

**F-4 — DMULT rides the citable `(DMULT-w)` tier, never `DMULT-S`.** COROLLARY W-9's
multiplicity input is the PDF-VERIFIED `(DMULT-w)` cite (census I-4 fold, 2026-08-12);
`DMULT-S` (the exact ω≡1 tier, HYP.77) is OUT of the cone and appears in no F statement.
GRTJC's own conditionality line (re-verified in the ledger at HYP.77): "if only (DMULT-s)
failed, JC-COB's sharp values and R1-COB's exact predicate fail **while the structural
clauses stand**." Per Part V, the exercised `(DMULT-w)` cite is a gate-(b) literature-cite
item routed through chapter I (§9).

**F-5 — transcription grade (GC-10) governs every node.** The weld notes are
transcription-grade sources: the EFF canonical statements are the spec; fresh mathematics
enters only via a dated AMENDMENT block; trichotomies are re-derived from the notes' own
displays, never from a verifier's phrasing; no false-reason parentheticals are transcribed
(WZ-BOX-7 is this chapter's own exhibit). The two DECISION blocks in §7 (the mutual-recon
directions) decide *statement-dependency direction*, not mathematics.

**F-6 — the two surviving conjuncts are CARRIED, not proved.** `JD0-BOX-2` is synthesis, not
a proved theorem (HYP.74's own words: "the synthesis §3.2 reading of JA-RES [GRTJA, 1/2],
the (ξ,w) covariance family [GRTW2, ACCEPTED], and the ℓ-orbit rescalings ORB-RES [J-A]");
`GENHN-BOX-2` stands on one accepted weld face plus the W-1 transport (ATTEMPT). F's §4/§5
nodes state the carriers at EXACTLY ledger strength and hand them to chapter I, where (Part V
ruling) each must terminate as a discharge node or a gate-(b) literature cite — no third
category. No F node claims either conjunct as a theorem.

**F-7 — GRTJA is the single priced input on J-D0's critical path, and its grade is 1/2.**
`EFF.JD0.25`'s supplier table, carried verbatim: everything load-bearing in J-D0's S2.1–S2.3
rides ACCEPTED suppliers *except* GRTJA (arc 1/2), which supplies BOTH the JA-RES
slot-character form and JA-GRID. §4's carrier statements and §7's structural-clause nodes
carry this grade cap explicitly; nothing in F upgrades it.

**F-8 — the σ-law enters through a GC-4 dictionary, with degree conservation, and the σ
output carrier is `FactorizationType` — nothing else.** SIGMALAW's Σ-law is PROVED in the
corpus (GRTW2 ANNEX 3, `EFF.GRTW2.50`, with two corrections to the boxed display — the
corrected form governs); §6 transcribes it with a named dictionary and the mandatory
`_degree` lemma. Ordering questions route to HYP.12 [CORE-SET]; F re-decides nothing.

**F-9 — numeric gates obey GC-11 with the coincidence-regime trap in view.** Both `q = 2`
AND `q = 3`; where meaningful an `e > 1 ∧ f > 1` witness; a value verified only at `q = 2`
is not verified. F's arithmetic content is the Σ-law dictionary and the character/carry
bookkeeping; §10's gates fire on exactly those.

**F-10 — fence adjudication is explicit.** The global DAG records 82 fence-crossing edges;
the weld notes' share and the `{GRTJA, GRTJB}` mutual cluster are adjudicated one line each
in §11 (BRIEF F trap (v)), and the two genuine MUTUAL-RECON SCCs (`GRTW2.20 ↔ LIFTCORNER.72`,
`GRTW2.35 ↔ LIFTCORNER.62`) are DECIDED in §7 (DAG_README SCC items 3–4 defer exactly this
to this chapter).

**F-11 — codex cross-read status: OWED.** Flagged items aggregated in §14.

*(Amendments to this block as composition proceeds are dated in place.)*

---

## 2. NODE INDEX

*(final — all sections composed; this index is the authority)*

| § | nodes | content |
|---|---|---|
| 3 | — (NON-NODE census) | **THE OUT-OF-CONE CENSUS**: the value package and every NOT-REACHED row, disposed row by row |
| 4 | F.01–F.06 | **THE `JD0-BOX-2` INTERFACE**: the unit-character gauge form, the perimeter carrier, the per-site strike ledger |
| 5 | F.07–F.13 | **THE `GENHN-BOX-2` / W-9 FACE**: the twisted-algebra carry interface at ledger strength, the W-1 transport carrier |
| 6 | F.14–F.18 | **THE Σ-LAW (SIGMALAW)** through a GC-4 dictionary + degree conservation |
| 7 | F.19–F.26 | mutual-recon adjudications (2 DECISIONs) + the reachable GRT structural-clause interfaces |
| 8 | — (PENDING arc) | WELD-ZERO: status of record, what a landed pass changes, licensed by whom |
| 9 | F.27–F.28 | the chapter-I handoff package (`WeldSupply` / `WeldObligations`) |
| 10 | F.29–F.30 | gates (GC-11: `q = 2` AND `q = 3`; `e > 1 ∧ f > 1` witness) |
| 11 | — | DAG additions + fence adjudications |
| 12 | — | leanspec stub list (stage 0e, `LeanspecF`) |
| 13 | — | unit-disposition census (all 567 SERIES units over 7 notes) + TEETH summary (GC-8) |
| 14 | — | flagged for the codex cross-read |

**Terminal supply (what other chapters consume from F), named now:** the gauge-form action
`UnitCharAction` + perimeter carrier `JD0Box2` (F.01–F.03), the twisted-carry interface
`TwistedCarrySpec` + face carrier `GenhnBox2` + `W1Transport` (F.07–F.10), the Σ-law
dictionary `sigmaLawSigma` + `sigmaLawSigma_degree` (F.14–F.16), the structural-clause
interfaces (F.19–F.26), and the chapter-I package `WeldSupply`/`WeldObligations` (F.27–F.28).

**Kind census** (mechanically counted over this file's `### NODE` headings): 10 `def`,
7 `lemma`, 4 `theorem`, 7 `interface-carrier` (Prop-valued `def`s at ledger strength), 2
`gate` — **30 nodes**. **BRIEF F estimated 50–70; the shortfall is deliberate and §13
accounts for it**: the estimate predated this composition's finding that the GRTJB/GRTJC
structural mass consumed by the two surviving conjuncts enters as *supplier-grade rows on
carrier statements* (INSTANCE-ROW/RECORDED), not as per-clause Lean nodes — transcribing
them as nodes would re-create the out-of-cone build the census exists to prevent.

**Graph shape** (from `spec/DAG_BLUEPRINT_F.tsv`, computed from the DEPENDS fields): 121
rows; intra-chapter proof-dep graph ACYCLIC, 5 layers, widths `9, 9, 6, 4, 2`; critical path
4 edges. No HARD node; the two carriers with GC-13 placeholders (F.10, F.24) are
blocked-until-resolution.

---

<!-- RESUME: skeleton committed; next = §3 out-of-cone census, then §4 (JD0-BOX-2) onward in
section order. Index above is provisional until FINAL STATE says otherwise. -->

<!-- SENTINEL: BP-F END OF FILE -->
