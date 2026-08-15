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

## 3. THE OUT-OF-CONE CENSUS (NON-NODE table — row by row, citing the v4 fold)

This section executes BRIEF F's §3: every weld package the ledger signed out of the capstone
cone is disposed here, ONE row each, with the signing citation. **Disposition vocabulary:**
`NON-NODE` = no Lean node exists or will exist for this content in any chapter; a fleet agent
needing it returns the row's BLOCKED string. Rows stay in the EFF specs (byte-frozen) and in
the ledger as weld-internal frontier rows — nothing here deletes mathematics; it declines to
build it into the capstone.

| # | label | ledger row | signing verdict (citation) | BLOCKED string |
|---|---|---|---|---|
| 1 | `[H-b]` / JB row 12 (`u ≥ 0` on the unbounded grid) | HYP.21 | NOT-REACHED (WELD-FACE-AUDIT 2026-08-13, COR-WFA-06; W12's own ledger L1508: the six accepted weld notes are consumed "ONLY in §S5's composition display and as [W12-H]'s named inputs"; GENIND L860: "n ≤ 3 program never consulted [W12-H]") | `BLOCKED: OUT-OF-CONE (HYP.21)` |
| 2 | `[H-c]` / the J-D1 value package (whole) | HYP.22 | NOT-REACHED (COR-WFA-07; the (A0)/(A1) suppliers at n ≥ 4 are GENH4.C/GENHN.C, both declaring "no weld face sits inside any count law"; the package left Display A at v4) | `BLOCKED: OUT-OF-CONE (HYP.22)` |
| 3 | `JB-NOLEG` (GRTJB rows 4 GRID, 5 RES, 12 d4/u≥0, 22 v=0) | HYP.75 | NOT-REACHED (COR-WFA-03; row 12 reaches only JD0-BOX-1's B(c)-tie → W-10, itself out of cone, and `[W12-H](H-b)`, the route W-12 priced but did not take; J-D0's own L4 leg consumes JB-VTX/JB-DEV, the ACCEPTED faces, NOT the no-leg rows) | `BLOCKED: OUT-OF-CONE (HYP.75)` |
| 4 | `W2-VALUE` (GRTW2 §5.3's value formula + side conditions; `W2-OPEN-1`, `EFF.GRTW2.35`) | HYP.76 | NOT-REACHED (COR-WFA-04; GRTW2 L900: the W-2 → W-5 seam "is NOT claimed here"; four cone notes state the seam is off — GENH4 L69/L870, GENHN L120, HEX3 L503; the two W12 occurrences at L1190/L1509 are non-consuming display bookkeeping, per the v4 fold's own correction of the audit's over-general "zero occurrences") | `BLOCKED: OUT-OF-CONE (HYP.76)` |
| 5 | `DMULT-S` (the exact ω ≡ 1 tier, `EFF.GRTJC.69`) | HYP.77 | NOT-REACHED (COR-WFA-05; the one reachable GRTJC face, COROLLARY W-9, rides the citable `(DMULT-w)` tier — see F.26; GRTJC's own blast radius: if only (DMULT-s) failed, "JC-COB's sharp values and R1-COB's exact predicate fail while the structural clauses stand") | `BLOCKED: OUT-OF-CONE (HYP.77)` |
| 6 | `(VD-m)` (value decomposition, m ≥ 2) | HYP.83 | verified UNREACHABLE at v5 (COR-ORPH-01, the ORPHAN-1 fresh verification: one cone occurrence and it is W-12.A's census display recording their ABSENCE; J-D0 L277–278 is "the theorem that deletes them" from count-layer consumers) | `BLOCKED: OUT-OF-CONE (HYP.83)` |
| 7 | `(C-coll)` (the W-2-side collection law) | HYP.84 | verified UNREACHABLE at v5 (COR-ORPH-02; the W-2 parent HYP.76 is itself NOT-REACHED — no live parent on either side) | `BLOCKED: OUT-OF-CONE (HYP.84)` |
| 8 | `(R-coll)` (the J-A-side residual collection law) | HYP.85 | verified UNREACHABLE at v5 (COR-ORPH-03; enters GRTJC only as JA-BOX-2's fence at m ≥ 3 inside §3.3's germ display, which no cone note names) | `BLOCKED: OUT-OF-CONE (HYP.85)` |
| 9 | `PERIM-μ` (the one-perimeter law "holds on all claimed order-≥2 faces") | HYP.86 | verified UNREACHABLE at v5 (COR-ORPH-04; the string occurs in ZERO of the twenty cone notes; WELDMASTER is "named in S7.1's (CS-1..3) pricing only") — **the CRITERION for it (WM-FENCE, an iff about fixed data) is a different object and IS transcribed, at F.23** | `BLOCKED: OUT-OF-CONE (HYP.86)` |
| 10 | `W2-OPEN-2` / `OPEN-2a` (the chain-level carry-analysis box, `EFF.GRTW2.33`) | — (inside HYP.76's mass) | the box is GRTW2's own open surface, narrowed by the Σ-LAW annex (`EFF.GRTW2.49/.50`); its unproved residue is value-layer content with no cone consumer; SL-C2's proved direction is transcribed at F.16 | `BLOCKED: OUT-OF-CONE (W2-OPEN-2; HYP.76)` |
| 11 | the W-2 → W-5 seam (junction J-B carry analysis) | — (named inside HYP.76/HYP.22) | "NOT claimed" by GRTW2's own honest-distance paragraph (`EFF.GRTW2.35`); the owed analysis has no accepting note | `BLOCKED: OUT-OF-CONE (W-2→W-5 seam)` |
| 12 | `JC-COB` sharp values / `R1-COB` exact predicate (the (DMULT-s) consumers) | — (inside HYP.77) | no cone consumer (HYP.77's row, re-verified: "the only (DMULT-s) consumers have no cone consumer") | `BLOCKED: OUT-OF-CONE (HYP.77)` |
| 13 | `W-10` / the B(c)-tie at the welded grid | HYP.128 (all-O row lives at I); census O-11 OUT | J-D0's consumer display (`EFF.JD0.24`): W-10's obligations ride JA-GRID + JB row 12's proviso — row 12 is out (row 3 above); W-10 itself is census O-11, out of cone | `BLOCKED: OUT-OF-CONE (W-10 / census O-11)` |

**Reconciliation with Display A (the GC-8/H.09 sanity check, run now):** after these thirteen
rows, the weld layer's surviving Display-A footprint is exactly `JD0-BOX-2` (§4),
`(GENHN-BOX-2 if n ≥ 6)` with its `W-1` sub-residue (§5), and the `AllOInterfaces[… W/J,
J-D0 …]` generality conjuncts (HYP.126/HYP.129, carried at §9). That matches the v4 fold's
own summary ("the weld layer's one genuine contribution, GENHN-BOX-2, is displayed in their
place" — plus JD0-BOX-2, the audit's single REACHABLE-AND-CONSUMED chartered row). Nothing
else weld-side conditions the capstone; a blueprint node outside §§4–7's scope would be a
false conditionality entry.

**dag_check consistency (verified at HEAD):** the checker's own reachability audit confirms
HYP.21/75/76/83/84/85/86 all unreachable from the capstone (7/7), and its first-pass
mismatch — matching Display A's `JD0-BOX-2` conjunct to HYP.76 — is the recorded lesson that
the conjunct's real home is HYP.39/HYP.74 (the matcher now prefers title matches and skips
off-cone rows).

---

## 4. §4 — THE `JD0-BOX-2` INTERFACE (the unit-character gauge-form perimeter)

**Section contract.** Product (1) of BRIEF F: state the `JD0-BOX-2` interface — the named
hypothesis chapter I will carry — at EXACTLY ledger strength (HYP.74; grade bar signed at
HYP.39), plus the small provable algebra that every consuming site actually exhibits
(the fold route: "record per site that the gauge consumed there is an explicit z-power unit
character verified in-note, which strikes the inheritance"). Source note: `spec/EFF-JD0.md`
(chapter G's note; G closed without transcribing JD0 — BRIEF F product (1) and BRIEF D trap
(v) both route the interface here, and D "does not adopt orphans silently"). J-D0 itself is
NOT re-proved here: the lemma's content (gauge-invariance + value-blindness of the stratum
count, re-keyed by S10.1 to the count-shape T̂) lives at FRAME grade at its seven consuming
sites; F supplies the perimeter object and the algebraic shell.

### NODE F.01 [def] [fresh]

**STATEMENT.** *The unit-character gauge action (the four-line perimeter, `EFF.JD0.05`).*
Over a finite field `K`, a **carry gauge** on an index type `Γ` is a family
`u : Γ → Kˣ`. Its documented action, transcribed from the note's four-line display:
(1) **ledger**: a 2-cochain `c : Γ → Γ → Kˣ` transforms by the coboundary,
`c(γ,γ′) ↦ c(γ,γ′) · u γ · u γ′ · (u (γ+γ′))⁻¹` (when `Γ` carries addition);
(2) **slot**: a slot value `v : K` transforms by `v ↦ u γ • v` (unit character per read
slot); (3) **residual**: a polynomial `R : K[y]` transforms by
`R ↦ ξ^(−deg R) • R(ξ·y)` for a unit `ξ` (the JA-RES geometric character; the overall
`(ξ,w)` unit dies in monic form); (4) **positions, δ, D_j, grid abscissas: UNCHANGED** —
represented structurally: the action is defined only on the value-carrying fields, so no
position field exists for it to move. This Lean node lands (1) and (2) as definitions
(`gaugeCobdry`, `slotScale`); (3) is F.03's object; (4) is honoured by omission.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The coboundary transform of a `Kˣ`-valued 2-cochain by a 1-cochain `u`
(`EFF.JD0.05` line 1: `c ↦ c·∂u`). -/
def gaugeCobdry {Γ : Type*} [AddCommGroup Γ] {K : Type*} [Field K]
    (u : Γ → Kˣ) (c : Γ → Γ → Kˣ) : Γ → Γ → Kˣ :=
  fun γ γ' => c γ γ' * u γ * u γ' * (u (γ + γ'))⁻¹

/-- The slot-wise unit action (`EFF.JD0.05` line 2): coordinatewise unit scaling of a
slot family. -/
def slotScale {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) (v : Γ → K) : Γ → K :=
  fun γ => (u γ : K) * v γ
```

**DEPENDS.** none (landed kernel only).

**PROOF.** definitional.

**SIZE.** 14 lines.

**SOURCE.** `EFF.JD0.05` (the four-line display, verbatim above; its CONDITIONALITY line:
"unit values (u_γ ∈ K^*); the four-line action is the whole quantified class"); the E8
adjudication carried with it ("the perimeter was declared up front, so restricting to it is
not post-hoc narrowing").

**FAITHFULNESS.** The note's `Γ` is the carry index of a realized tower; here `Γ` is
abstract (`AddCommGroup` only where the coboundary needs `+`). The four-line action is the
WHOLE quantified class — a fleet agent must not enlarge it (the E8 finding-#1 lesson: an
independent diagonal rescaling of polynomial coefficients is NOT this action).

**TEETH.** JD0-COB checks (1)–(4) (executable regression, retained — see §13); the perimeter
boundary is F.30's NONCHAR gate.

**ENVIRONMENT.** ENV-F1 (+ `[Field K]`; no `O`).

---

### NODE F.02 [lemma] [fresh]

**STATEMENT.** *The slot action is a bijection; counts are blind to it.* For any `u : Γ → Kˣ`,
`slotScale u` is an equivalence of `Γ → K` (inverse: `slotScale u⁻¹`), and consequently for
every finite set `S` of slot families closed under `slotScale u`, the count of `S` is
preserved: `Nat.card ↥(slotScale u '' S) = Nat.card ↥S` (and `slotScale u '' S = S` when `S`
is closed). This is the abstract mechanism shadow of J-D0's clause (i): a unit-character
gauge acts by a bijection, hence stratum counts computed through the gauged read equal
direct counts *wherever the stratum is carried onto itself* — which closure is exactly what
each consuming site verifies in-note (HYP.74's fold route).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- Slot-wise unit scaling is an equivalence (`EFF.JD0.06` clause (i)'s mechanism shadow). -/
def slotScaleEquiv {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) :
    (Γ → K) ≃ (Γ → K) where
  toFun := slotScale u
  invFun := slotScale u⁻¹
  left_inv := by intro v; funext γ; simp [slotScale]
  right_inv := by intro v; funext γ; simp [slotScale]

theorem card_image_slotScale {Γ K : Type*} [Field K] (u : Γ → Kˣ) (S : Set (Γ → K)) :
    Nat.card ↥(slotScale u '' S) = Nat.card ↥S
```

**DEPENDS.** F.01; mathlib `Nat.card_image_of_injective`, `Units.mul_inv_cancel_left`.

**PROOF.** 1. `slotScale u⁻¹ (slotScale u v) = v` pointwise: computation
`(u γ)⁻¹ * ((u γ) * v γ) = v γ` (unit cancellation). 2. Same for the right inverse.
3. The card identity: by mathlib `Nat.card_image_of_injective` with the equivalence's
injectivity. FORBIDDEN adaptations: none — this is elementary.

**SIZE.** 22 lines.

**SOURCE.** `EFF.JD0.06` (LEMMA J-D0 clause (i)'s mechanism, at the abstract level ONLY —
the full clause (i) is site content, not transcribed); HYP.74's discharge route ("record per
site that the gauge consumed there is an explicit z-power unit character … which strikes the
inheritance") — this lemma is the site-independent half of every such strike.

**FAITHFULNESS.** The Lean statement is deliberately WEAKER than LEMMA J-D0: it asserts
count-blindness of the abstract action, not of the stratum count of a decided shape (which
would need the L3 × L4 assembly, `JD0-BOX-4` — consumed by no F node). No F node states
J-D0(ii) (value-blindness): its S10.1 re-keying to the count-shape `T̂` is chapter-G-adjacent
count-layer content signed out with G's closure.

**TEETH.** JD0-BLIND / JD0-STRAT ride the sites (RECORDED, §13); this node's own tooth is
F.30's `q = 2`/`q = 3` count check.

**ENVIRONMENT.** ENV-F1 (+ `[Field K]`).

---

### NODE F.03 [lemma] [fresh]

**STATEMENT.** *The residual ξ-twist's conclusions (degree, monicity, root census).* For a
unit `ξ : Kˣ` define the residual twist `resTwist ξ R := ξ^(−natDegree R) • R.comp (C ξ * X)`
(the JA-RES geometric character read, `EFF.JD0.05` line 3, monic-normalized). Then, stated
as CONCLUSIONS per the WZ-BOX-7 rule (honesty F-3): (a) `natDegree (resTwist ξ R) =
natDegree R`; (b) `R.Monic → (resTwist ξ R).Monic`; (c) `r` is a root of `resTwist ξ R` iff
`ξ · r` is a root of `R` — the root multiset is carried bijectively by `x ↦ ξ⁻¹ · x`. No
clause of this node says "the twist preserves types"; the three displayed conclusions are
what the consuming sites use.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld
open Polynomial

/-- The monic-normalized residual twist by a unit `ξ` (`EFF.JD0.05` line 3). -/
noncomputable def resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) : K[X] :=
  C ((ξ : K) ^ R.natDegree)⁻¹ * R.comp (C (ξ : K) * X)

theorem natDegree_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) :
    (resTwist ξ R).natDegree = R.natDegree

theorem monic_resTwist {K : Type*} [Field K] (ξ : Kˣ) {R : K[X]} (hR : R.Monic) :
    (resTwist ξ R).Monic

theorem isRoot_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) (r : K) :
    (resTwist ξ R).IsRoot r ↔ R.IsRoot ((ξ : K) * r)
```

**DEPENDS.** none (landed kernel + mathlib `Polynomial.natDegree_comp`,
`Polynomial.Monic.comp`, `Polynomial.leadingCoeff_comp`, `Polynomial.eval_comp`,
`Polynomial.IsRoot`).

**PROOF.** 1. (a): `natDegree (R.comp (C ξ * X)) = natDegree R * natDegree (C ξ * X) =
natDegree R` (mathlib `natDegree_comp`, `natDegree_C_mul_X` with `ξ ≠ 0`), and the `C`-unit
factor leaves it fixed. 2. (b): leading coefficient of the composite is
`leadingCoeff R · ξ^natDegree R`; the normalizing factor cancels it to `1` — computation.
3. (c): `eval r (R.comp (C ξ * X)) = eval (ξ·r) R` (mathlib `eval_comp`); a unit factor does
not change root-ness. A step needing more than 3 tactics: (b)'s leading-coefficient
computation — split candidate `F.03a` if the fleet agent needs it.

**SIZE.** 34 lines.

**SOURCE.** `EFF.JD0.05` line 3 (the residual action, "the (ξ,w) overall unit dies in monic
form"); the JA-RES display (`EFF.GRTJA.08`, the pure character `z^{−i·A}` in the abscissa)
supplies the exponent's provenance — consumed here as the ACTION's shape only, at GRTJA's
recorded grade (honesty F-7); the LAW that the weld's residuals transform this way is F.04's
carried perimeter, never this node's claim.

**FAITHFULNESS.** WZ-BOX-7-compliant by construction: three conclusions (degree, monicity,
root census), no "type-preservation" clause. The note's own NONCHAR failure display ("an
additive slot shift is a bijection that breaks type preservation, hence counts") is F.30's
gate, not a theorem here.

**TEETH.** JD0-T-NONCHAR (the failure mode OUTSIDE the class) → F.30 gate; CK-RES's 443
scored rows (GRTJA) remain the sites' evidence — RECORDED.

**ENVIRONMENT.** ENV-F1 (+ `[Field K]`).

---

### NODE F.04 [interface-carrier] [fresh]

**STATEMENT.** *`JD0-BOX-2`, the gauge-form perimeter — the named hypothesis chapter I
carries.* Transcribed at EXACTLY ledger strength (HYP.74; `EFF.JD0.22` BOX-2 verbatim): "That
the weld's ENTIRE conditional value dictionary acts by slot-wise unit characters is the
synthesis §3.2 reading of JA-RES [GRTJA, 1/2], the (ξ,w) covariance family [GRTW2, ACCEPTED],
and the ℓ-orbit rescalings ORB-RES [J-A]. J-D0's proof covers unit-character gauges; any
value layer NOT of that form is outside the perimeter." As a Lean object: a `Prop`-valued
carrier over an abstract SITE datum — a site supplies its value-dictionary action as a map
`act : Γ → (Γ → K) → (Γ → K)`, and the perimeter asserts the existence of a carry gauge `u`
realizing it: `∀ γ, act γ = fun v => slotScale u v` (slot leg) — the residual and ledger legs
enter as the corresponding `resTwist`/`gaugeCobdry` clauses. **This is synthesis, not a
theorem** (HYP.74: "JD0 unit-character warrant is synthesis, not proved theorem"); the
carrier is instantiated per site by the fold route, never proved in general. The grade bar
is SIGNED (HYP.39, Q6: 68,523/0 machine grade; the two-clean hostile arc is not required).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- A weld VALUE-DICTIONARY site: an indexed action on slot families, with its residual and
ledger legs. Abstract — instances are the seven cone sites' in-note data. -/
structure ValueDictSite (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  slotAct : (Γ → K) → (Γ → K)
  ledgerAct : (Γ → Γ → Kˣ) → (Γ → Γ → Kˣ)

/-- `JD0-BOX-2` at ledger strength (HYP.74): the site's dictionary is realized by a
slot-wise unit character — a carry gauge in the `EFF.JD0.05` class. CARRIED, not proved;
chapter I's conjunct field. -/
def JD0Box2 {Γ K : Type*} [AddCommGroup Γ] [Field K] (site : ValueDictSite Γ K) : Prop :=
  ∃ u : Γ → Kˣ, site.slotAct = slotScale u ∧ site.ledgerAct = gaugeCobdry u
```

**DEPENDS.** F.01. Supplier-grade provenance (carried as annotations, not Lean deps):
JA-RES = `EFF.GRTJA.08` at GRTJA arc 1/2 (F.19); the (ξ,w) covariance = `EFF.GRTW2.19` at
ACCEPTED fenced scope (F.21); ORB-RES = `EFF.GRTJA.11`'s orbit legs (machine ORB-RES 444).

**PROOF.** definitional (a carrier; nothing to prove).

**SIZE.** 18 lines.

**SOURCE.** `EFF.JD0.22` (BOX-2 verbatim, quoted above); HYP.74 (statement, class
`hypothesis-box`, disposition CARRY with reachability SIGNED at the seven sites: W11 L599,
W12 L1499, HMENU3 L717, HEX3 L720, GENIND L1518, GENH4 L938, GENHN L1515 — all re-verified
by the audit at HEAD); HYP.39 (the signed grade bar; the optional codex pass survives as
MQ-4 and gates nothing).

**FAITHFULNESS.** Ledger strength exactly: existence of the realizing gauge per site — not
"every value dictionary anywhere is a unit character" (the general census S-5 proposed is
explicitly "NOT needed on the capstone path", HYP.74). The residual leg is deliberately NOT a
third conjunct of the Lean `Prop`: the sites consume it through the JA-RES form whose grade
cap (GRTJA 1/2) must stay visible at chapter I rather than be absorbed into an ∃ — the
carrier for that leg is F.19, referenced by chapter I alongside this one. **Per Part V:
this carrier must terminate in I as a discharge node (the per-site fold, if executed) or a
gate-(b) literature cite; no third category.**

**TEETH.** signed non-applicability (a carried hypothesis has no teeth by design — H.09's
rule; reconciled in §13's sanity check).

**ENVIRONMENT.** ENV-F1 (+ `[AddCommGroup Γ] [Field K]`).

---

### NODE F.05 [def] [fresh]

**STATEMENT.** *The per-site strike ledger (the fold route made a datum).* HYP.74's
discharge route is a FOLD: "record per site that the gauge consumed there is an explicit
z-power unit character verified in-note, which strikes the inheritance." This node lands the
witness shape: a `JD0SiteStrike` is a site together with an explicit exponent family
`a : Γ → ℤ` and a letter `z : Kˣ` such that the site's gauge is the z-power character
`u γ = z ^ a γ` — the explicit form every audited site exhibits. The SEVEN strike
obligations (one per cone site) are INSTANCE-ROWS, not nodes: W11 (its L602–603 inheritance
gloss), W12 (L1502–1504), HMENU3, HEX3, GENIND, GENH4, GENHN — each strike is one
`JD0SiteStrike` instance whose data is read off the consuming note's own verified display,
instantiable only when the corresponding chapter's Lean site objects exist (G is closed
without them; the count-layer instances ride H/C landings — GC-13).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- A per-site STRIKE (HYP.74's fold route): the site's gauge exhibited as an explicit
z-power unit character. One instance per audited cone site. -/
structure JD0SiteStrike (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  site : ValueDictSite Γ K
  z : Kˣ
  a : Γ → ℤ
  strike : site.slotAct = slotScale (fun γ => z ^ a γ)
```

**DEPENDS.** F.01, F.04.

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** HYP.74's disposition line (the fold route, verbatim above); the seven-site list
with line numbers from the audit (re-verified at HEAD by the v4 fold).

**FAITHFULNESS.** A strike witnesses `JD0Box2` for its site (the `∃ u` with
`u = fun γ => z ^ a γ` and the ledger leg by computation) — so seven landed strikes plus the
residual-leg carrier would DISCHARGE the conjunct's slot half; that execution is chapter I's
disposition decision, not this chapter's claim.

**TEETH.** the strike data per site is in-note verified content (RECORDED at the sites).

**ENVIRONMENT.** ENV-F1.

---

### NODE F.06 [lemma] [fresh]

**STATEMENT.** *The `F₂` degeneracy disclosure, made structural (`JD0-BOX-5`).* If `K` has
exactly two elements then `Kˣ` is a subsingleton and every carry gauge acts trivially:
`slotScale u = id` and `gaugeCobdry u c = c` for every `u`. Consequently J-D0's clause (i)
is VACUOUS at `F₂` levels — exactly the note's own disclosure ("Over K_j = F₂ the unit group
is trivial: clause (i) is vacuous at such levels … Clause (ii) is NOT vacuous at F₂"), which
the battery census reports (252 residual-gauge levels nontrivial, 57 trivial). The
non-vacuity of clause (ii) at `F₂` is a site-level fact (value-blindness does not mention
units) and is not a Lean claim here.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem slotScale_eq_id_of_card_two {Γ K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) (u : Γ → Kˣ) : slotScale u = id
```

**DEPENDS.** F.01; mathlib `Fintype.card_units` (`card Kˣ = card K − 1`),
`Subsingleton.elim`.

**PROOF.** 1. `Fintype.card Kˣ = 1` from `hK` (computation). 2. `u γ = 1` for every `γ`
(subsingleton with the unit `1`). 3. `slotScale 1 = id` — funext + `one_mul`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.JD0.22` BOX-5 (verbatim clause), with the S9 census figures (P-2: "252
residual-gauge levels nontrivial, 57 trivial (F₂/unit-group-1 levels, per BOX-5)"; P-4: the
all-F₂ tower C4A is the one residue-trivial row).

**FAITHFULNESS.** This is a vacuity DISCLOSURE promoted to a theorem — the strongest honest
form (GC-8's signed-vacuity sub-case, here with a proof). It is why F.30's gates run the
unit-character checks at `q = 2` on `F₄` (where `Kˣ` is nontrivial), never on `F₂` alone —
the coincidence-regime discipline (GC-11) applied to this chapter's own degeneracy.

**TEETH.** Lean theorem (this node); the F₂ census rows RECORDED.

**ENVIRONMENT.** ENV-F1 (+ `[Fintype K]`).

---

## 5. §5 — THE `GENHN-BOX-2` / W-9 FACE (the twisted-algebra carry interface, at ledger strength)

**Section contract.** Product (2) of BRIEF F: the supplier statement — COROLLARY W-9's
twisted group algebra as the `μ ≥ 3` carry bookkeeping — at EXACTLY ledger strength
(HYP.148, CARRY, first live degree `n = 6`; sub-residue HYP.139, the W-1 transport, MATH).
Source unit: `EFF.GRTJC.89` (the special-care unit, byte-verbatim in the spec) with its
proofs unit `.90` and the JC-F1 consequence `.91`. **Consumption geography, verified by the
spec's own three-source check:** W-9 is consumed at GENHN-4 **layer 1** (GENHN S6.1, exactly
one line, L874), `μ ≥ 3`, "the ONE weld face inside a count law" on the whole capstone path;
clauses (i)–(iii) are what layer 1 takes; **clause (iv) is NOT consumed** (the wrap letter
layer 1 uses is derived elsewhere); everything W-9 rides, W-8/W-7 ride: `(DMULT-w)` (F.26),
`[ILN]†`'s scored stratum for the value half, `e_m ≥ 2` for the sharp forms. The abstract
twisted-algebra mathematics of clauses (i)–(iii) is elementary finite algebra and is
transcribed as PROVABLE nodes (F.07–F.10, plus the count identity F.13); the claim that
GENHN-4 layer 1's carry bookkeeping IS an instance of that shape is the CARRIED face
(F.11), and its FGMN-transport residue is F.12. Per honesty F-2, nothing here consumes
WELDZERO's replacement route.

### NODE F.07 [def] [fresh]

**STATEMENT.** *The carry-cocycle datum (W-9 clauses (i)+(ii) as a structure).* Over a
finite field `K` and a modulus `E ≥ 1`: a **carry cocycle** is a pair of families
`c : ZMod E → ZMod E → Kˣ` and `δ : ZMod E → ZMod E → ℕ` with (i) the `Kˣ`-valued 2-cocycle
identity `c a b * c (a+b) d = c b d * c a (b+d)` (COROLLARY W-9(i): "this is [ILN]†'s COR-2,
and on the gr side it is nothing but associativity of gr(w)'s multiplication"); (ii) the
integer cocycle identity `δ a b + δ (a+b) d = δ b d + δ a (b+d)` with `δ` `{0,1}`-valued
(W-9(ii): "the {0,1}-valued carry cocycle"). The y-degree tie `deg A(a,b) = δ(a,b)`
(JC-CARRY-m) is instance content at the consuming site, not a field.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- A carry cocycle over `ZMod E` (`EFF.GRTJC.89` clauses (i)/(ii)): the `Kˣ`-valued
2-cocycle with its `{0,1}`-valued integer shadow. -/
structure CarryCocycle (E : ℕ) [NeZero E] (K : Type*) [Field K] where
  c : ZMod E → ZMod E → Kˣ
  δ : ZMod E → ZMod E → ℕ
  cocycle : ∀ a b d, c a b * c (a + b) d = c b d * c a (b + d)
  δ_le_one : ∀ a b, δ a b ≤ 1
  δ_cocycle : ∀ a b d, δ a b + δ (a + b) d = δ b d + δ a (b + d)
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GRTJC.89` clauses (i)/(ii), byte-verbatim in the spec (its own source-range
verification: GRTJC L1777–1788 at HEAD, exact); `EFF.GRTJC.90` (the one-line proofs — NOT
transcribed as proofs here: in the corpus (i)/(ii) are CONCLUSIONS given W-6..W-8; in this
abstract structure they are FIELDS, so the corpus conditionality is carried by
instantiation, never silently discharged).

**FAITHFULNESS.** Kind inversion, disclosed: the corpus proves (i)/(ii) from the GRTJC stack
(W-6/W-7/W-8 + `(MULT-B)|gr` + `(DMULT-w)`); F carries them as structure fields because the
stack's objects (the harness chain, `𝒜(T)`) have no leanfinal carrier and building them
would be out-of-cone mass (§3). An instance of `CarryCocycle` at a concrete site is
therefore exactly "W-9's conclusion holds there" — ledger strength preserved.

**TEETH.** JC7 (581 samples, 0 violations; 261 triples satisfy BOTH identities; E-fold chain
matched on all 15 rows with E ≤ 8) → executable regression RECORDED at the source; the Lean
instances fire at F.29's gate.

**ENVIRONMENT.** ENV-F1 (+ `[NeZero E] [Field K]`).

---

### NODE F.08 [def] [fresh]

**STATEMENT.** *The twisted group algebra `K^c[ℤ/E]` (W-9 clause (iii)'s object).* For a
carry cocycle `cc`: the carrier `ZMod E → K` with the `c`-twisted convolution
`(f ⋆ g) t = Σ_{a+b=t} c a b · f a · g b`. One public definition; the `Mul`/`One` instances
and helper lemmas live below it in the same file (GC-6.5's helper clause).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The twisted group algebra `K^c[ℤ/E]` of the abscissa-coset group over the carry cocycle
(`EFF.GRTJC.89` clause (iii)). Carrier: `ZMod E → K`; multiplication: `c`-twisted
convolution. -/
def TwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Type _ := ZMod E → K

-- helpers below the contract declaration (same file):
--   instance : Mul (TwistedAlgebra cc) — (f ⋆ g) t = ∑ a, cc.c a (t − a) * f a * g (t − a)
--   def single (a : ZMod E) (x : K) : TwistedAlgebra cc
--   instance : AddCommGroup (TwistedAlgebra cc) := Pi.addCommGroup
--   instance : Module K (TwistedAlgebra cc) := Pi.module _ _ _
```

**DEPENDS.** F.07; mathlib `Finset.sum` over `ZMod E` (`Fintype (ZMod E)` via `NeZero E`).

**PROOF.** definitional.

**SIZE.** 20 lines (with helpers).

**SOURCE.** `EFF.GRTJC.89` clause (iii) ("𝒜(T) is the twisted group algebra K^{c}[ℤ/E] of
the abscissa-coset group over the carry cocycle"); the clause's consumer reading from the
spec's four-supply table: "one K-line per dv-height, i.e. dim_K 𝒜(T) = E".

**FAITHFULNESS.** The corpus object `𝒜(T)` is a subquotient of the harness chain; W-9(iii)
says it IS this twisted algebra. F declares the abstract right-hand side only; the
identification is inside F.11's carried face. `Type _`-level `def` (not `abbrev`) so the
twisted `Mul` instance cannot leak onto plain `ZMod E → K`.

**TEETH.** F.29 gate instances at `q = 2` and `q = 3`.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.09 [theorem] [fresh]

**STATEMENT.** *Associativity IS the cocycle identity (W-9(i)'s elegance, abstract half).*
For a carry cocycle `cc`, the twisted convolution on `TwistedAlgebra cc` is associative, and
`single 0 (cc.c 0 0)⁻¹` is a two-sided unit. The proof is the source's own one-liner run in
reverse: expanding `(f ⋆ g) ⋆ h` and `f ⋆ (g ⋆ h)` termwise, the coefficients match exactly
by `cocycle` — "the cocycle identity is not an extra hypothesis but a consequence of the
ring being a ring" (`EFF.GRTJC.90`'s reading), here used in the direction the abstract
carrier needs (cocycle ⟹ associative).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem TwistedAlgebra.mul_assoc {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) (f g h : TwistedAlgebra cc) :
    f * g * h = f * (g * h)
```

**DEPENDS.** F.07, F.08; mathlib `Finset.sum_comm`, `Finset.sum_bij` (re-indexing the double
convolution sum), `Finset.mul_sum`.

**PROOF.** 1. Expand both sides to double sums over `(a, b)` with `a + b + d = t`
(computation). 2. Re-index by `Finset.sum_bij` (the pairing `(a+b, d) ↔ (a, b+d)`).
3. Coefficient match per term: `cc.cocycle a b d` (one rewrite). Split candidate if the
re-indexing exceeds the size box: `F.09a` (the double-sum re-indexing as its own lemma).

**SIZE.** 38 lines.

**SOURCE.** `EFF.GRTJC.89`(i) + `EFF.GRTJC.90` proof (i) (associativity of `gr(w)` expanded
with `(MULT-B)|gr` yields the identity; reduced mod `ψ_m` gives the `Kˣ` form). Direction
reversed for the abstract carrier — disclosed, not fresh mathematics (the equivalence of a
2-cocycle law with twisted-convolution associativity is classical algebra; the corpus walks
it right-to-left, this node left-to-right).

**FAITHFULNESS.** Stated on the abstract object only. Nothing here claims `𝒜(T)` facts.

**TEETH.** JC7's cocycle leg (RECORDED); F.29 executes the abstract instance at both primes.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.10 [theorem] [fresh]

**STATEMENT.** *Dimension `E` and the power basis (clause (iii)'s count + JC-F1's cyclic
presentation).* For a carry cocycle `cc`: (a) `Module.finrank K (TwistedAlgebra cc) = E`
("one K-line per dv-height" — the graded shadow GENHN-2 cites as frame); (b) with
`v := single 1 1`, the powers satisfy `v ^ k = single k (β k)` with
`β k = ∏_{i=1}^{k−1} cc.c 1 i ∈ Kˣ` for `1 ≤ k ≤ E`, so `{v^0, …, v^{E−1}}` is a `K`-basis
and `v ^ E = ζ • 1` with `ζ := ∏_{k=1}^{E−1} cc.c 1 k` — `EFF.GRTJC.91`'s display
"`𝒜(T) ≅ K[v]/(v^E − ζ_T)` as a K-algebra — at EVERY composite stage" in its abstract form.
The anchor-INDEXED presentation claim the blueprint fence guards ("`𝒜(T)` is NOT
`F′[u′]/(u′^E − ζ′)`" as a presentation statement, JC-BOX-5 REVIEW-OWED) is NOT contradicted
and NOT transcribed: (b) is the abstract-isomorphism fact only, exactly the correction JC-F1
records.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem TwistedAlgebra.finrank_eq {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Module.finrank K (TwistedAlgebra cc) = E

theorem TwistedAlgebra.pow_card_single {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) :
    (single 1 1 : TwistedAlgebra cc) ^ E
      = (∏ k ∈ Finset.Ico 1 E, (cc.c 1 (k : ZMod E) : K)) • single 0 1
```

**DEPENDS.** F.07, F.08, F.09; mathlib `Module.finrank_pi` (`finrank K (ZMod E → K) =
card (ZMod E)`), `ZMod.card`, `Finset.prod_Ico_succ_top` (the orbit-product induction).

**PROOF.** 1. (a): the carrier is `ZMod E → K`; `finrank = Fintype.card (ZMod E) = E` —
mathlib. 2. (b): induction on `k ≤ E`: `v ^ (k+1) = v * v ^ k`; the convolution of two
`single`s is `single (a+b) (c a b · x · y)` (helper lemma below F.08); the product
telescopes. 3. At `k = E`: `(E : ZMod E) = 0`, giving the `single 0` form. Split-mandated:
**F.10 → 2 files** (F.10a the single-convolution helper + finrank; F.10b the power
induction) — the induction plus helper exceeds the 40-line box.

**SIZE.** 2 × ~30 lines.

**SOURCE.** `EFF.GRTJC.89` clause (iii) consumer column ("dim_K 𝒜(T) = E"); `EFF.GRTJC.91`
(FINDING JC-F1's displayed derivation: `v^k = β_k·[φ_{γ_k}]`, powers in pairwise distinct
`ℤ/E`-degrees, dimension count `E = E`; "THROUGH, general m, on (DMULT-w) + JC-IND" — the
conditionality lands on F.11's instance, not on this abstract node); JC-BOX-5's REVIEW-OWED
fence honoured by scope (abstract isomorphism only).

**FAITHFULNESS.** The abstract (b) uses only the structure's own fields; the corpus's
`(DMULT-w)`-riding enters where an instance is claimed (F.11). Degree/normalization
conventions: `single 0 1` is not the unit unless `cc.c 0 0 = 1` — the statement is therefore
in `•`-form against `single 0 1`, not against `1`; a fleet agent must not "fix" this by
normalizing `cc` (statement fence).

**TEETH.** JC8's power-basis leg (the E-fold chain, 15 rows E ≤ 8 — RECORDED); F.29 executes
`v^E = ζ • single 0 1` at concrete instances, both primes.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.11 [interface-carrier] [fresh]

**STATEMENT.** *`GENHN-BOX-2` at ledger strength — the ONE weld face inside a count law.*
Transcribed from HYP.148 (CARRY) and GENHN's own dependency ledger (verbatim at HEAD, quoted
in the ledger row): "GRTJC W-6..W-9 + JC-LOAD/W-8 are consumed at LEMMA GENHN-4 layer 1
(μ ≥ 3) — the ONE weld face inside a count law, disclosed (GENHN-BOX-2); elsewhere
frame-only"; the box's own pricing: "the count laws at μ ≥ 3 stand on one accepted weld
face." As a Lean carrier: a `Prop`-valued structure asserting, for a composite-stage carry
site at multiplicity `μ ≥ 3` (site data abstract; the concrete stage objects are chapter
H/C's — `GenreDatum`-keyed, GC-13), the EXISTENCE of a `CarryCocycle` instance whose twisted
algebra realizes the stage's carry bookkeeping (clauses (i)–(iii)); **clause (iv) is
deliberately absent** (not consumed at layer 1 — the spec's four-supply table, row (iv):
"NOT CONSUMED"). Scope pins carried in the statement: first live degree `n = 6` (the same
threshold as `[GENHN-HE(μ≥3)]`, HYP.81); NOT inherited by the σ chain (HE3 L1293: "the W-9
weld face (GENHN-BOX-2) is absent from the σ chain") and NOT by the tower leg (GENTOW5
L157). Compensating instrument standing: GN-REFINE3 (GENHN L1834) — recorded, not a
discharge.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- A composite-stage CARRY SITE at multiplicity `μ`: the stage's carry bookkeeping as an
abstract indexed family. Instances are chapter-H/C stage objects (GC-13). -/
structure CarrySite (K : Type*) [Field K] where
  E : ℕ
  hE : 1 ≤ E
  μ : ℕ
  carry : ZMod E → ZMod E → K   -- the stage's own carry table (site data)

/-- `GENHN-BOX-2` at ledger strength (HYP.148): at `μ ≥ 3` the site's carry bookkeeping is
realized by a carry cocycle's twisted algebra — W-9 clauses (i)–(iii), clause (iv) absent.
CARRIED, not proved; chapter I's `n ≥ 6`-indexed conjunct field. -/
def GenhnBox2 {K : Type*} [Field K] (s : CarrySite K) : Prop :=
  3 ≤ s.μ → ∃ (h : NeZero s.E) (cc : CarryCocycle s.E K),
    ∀ a b, (cc.c a b : K) = s.carry a b
```

**DEPENDS.** F.07 (statement), F.08–F.10 (the consumer-facing laws an instance inherits).
Cross-chapter: the concrete site instances are `EFF.GENHN [supplied-by: chapter H — landed
H.61/H.87 layer]` and composed-stage data `[supplied-by: chapter C]` (GC-13(c)); no F node
constructs one.

**PROOF.** definitional (a carrier).

**SIZE.** 22 lines.

**SOURCE.** HYP.148 (statement + CONSUMED-BY, quoted; v6/v7 ARC NOTEs: CARRY at full
strength, the discharge route is HYP.149 = WELD-ZERO, pending — honesty F-2); `EFF.GRTJC.89`
(the four-supply table's per-clause consumer column; the three annex survivals: Annex #4
"W-9's cocycle semantics and the residue-chain statement survive", Annex #5, Annex #6);
`SG2_PROBE_2026-08-10.md` L26–29 (NEEDS-X: GENHN-4 is NOT re-derivable from WELDMASTER
(M0)–(M4) + WM-COB + J-D0 as stated — why this is a carry, not a theorem).

**FAITHFULNESS.** Ledger strength exactly: the `μ ≥ 3` guard is in the `Prop` (below it the
site owes nothing weld-side — GENHN-2 re-proves the slot geometry elementarily); the `n ≥ 6`
degree threshold is chapter I's index on the conjunct field (F does not carry `n`); clause
(iv) structurally absent. **Per Part V: terminates in I as a discharge node (if WELD-ZERO
lands and is folded by dated amendment, §8) or stays a named capstone hypothesis.**

**TEETH.** signed non-applicability (carried face; H.09's rule — reconciled §13). Machine
corroboration at the source: GENHN L1710 pin checks, 0 violations (RECORDED).

**ENVIRONMENT.** ENV-F1.

---

### NODE F.12 [interface-carrier] [fresh]

**STATEMENT.** *The `W-1` transport, `GENHN-BOX-2`'s sub-residue (HYP.139, MATH).* At ledger
strength, verbatim from the census: "Residue is NOT the cite but the transport: W-1 (harness
w, 𝑅 → FGMN objects) stays ATTEMPT"; GRTJC L1990–1993: "Transport of the harness w and 𝑅 to
the FGMN objects is still W-1 (ATTEMPT) — and the corpus's own march-level dictionary for
that transport, TR-3′-GEN, is OPEN at general order." As a Lean carrier: a `Prop` asserting,
for a carry site consumed through the FGMN frame, the existence of the transport dictionary
(a line-wise unit system `c_λ` with `𝑅_λ = c_λ · R^GMN_λ` — the `(IN-3)` transport clause's
shape) at the site's order. This is a PROOF obligation, not a citation one (the census's own
words) — class MATH, distinct from F.11's CARRY: it does NOT discharge with a transcription
fold.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- `W-1` (HYP.139) at ledger strength: the harness-to-FGMN transport dictionary exists at
the site's order — a line-wise unit system relating the two residual operators. MATH-class
obligation; chapter I's field, riding under `GenhnBox2`. Abstract shape: the two operator
families and the unit system are site data. -/
def W1Transport {K : Type*} [Field K] {ι : Type*}
    (Rharness RGMN : ι → K) : Prop :=
  ∃ c : ι → Kˣ, ∀ λ, Rharness λ = (c λ : K) * RGMN λ
```

**DEPENDS.** none (shape only). The FGMN-side objects are gate-(b) literature-cite content
(`(IN-3)`, F.26's provenance); the harness side is GRTJC-internal.

**PROOF.** definitional (a carrier).

**SIZE.** 12 lines.

**SOURCE.** HYP.139 (statement + the consumer chain "W-9 (proved GIVEN W-6..W-8) → GENHN-4's
layer-1 carry bookkeeping at μ≥3 (GENHN-BOX-2) → count laws at μ≥3"; the v4 note: the
WELD-ZERO route would retire this row WITH HYP.148 — pending, licenses nothing, honesty
F-2); `EFF.GRTJC.69`'s CONDITIONALITY ("(IN-3)'s transport prices 𝑅 = c·R^GMN at a line-wise
unit, and TR-3′-GEN is OPEN beyond its closed strata").

**FAITHFULNESS.** The `ι`-indexed shape is the transport's SIGNATURE only — the mathematics
(that the unit system exists compatibly at general order) is exactly what is OPEN; stating
more would manufacture a discharge. The carrier is `∃`-form because the ledger's obligation
is existence of the dictionary; per-λ explicitness is what TR-3′-GEN's closed strata supply
where they apply.

**TEETH.** signed non-applicability (MATH-class carry; §13).

**ENVIRONMENT.** ENV-F1.

---

### NODE F.13 [lemma] [fresh]

**STATEMENT.** *The count form of the twisted layer (conclusions, not type-preservation).*
For a carry cocycle `cc`: `Nat.card (TwistedAlgebra cc) = (Nat.card K) ^ E`. Together with
F.10(a) this is the cardinality/dimension pair the count laws consume — the WZ-BOX-7-
compliant packaging (cancellation identities and cardinalities; honesty F-3). The two landed
theorems that replace type-preservation claims in the consuming count layer are cited here
by node ID as the interface: **H.87** (`carry_cancel`/`carry_cancel_char_two` — the
three-term carry cancellation, both characteristics) and **H.61**
(`TriangularUnitPivot.card_fibre` — the target-independent fibre count); no F node re-proves
either, and no F node states a twist-map type-preservation claim in their place.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem TwistedAlgebra.nat_card {E : ℕ} [NeZero E] {K : Type*} [Field K] [Finite K]
    (cc : CarryCocycle E K) :
    Nat.card (TwistedAlgebra cc) = Nat.card K ^ E
```

**DEPENDS.** F.08; mathlib `Nat.card_fun`/`Nat.card_pi`, `ZMod.card`. Interface citations
(DEPENDS-as-annotation, GC-13(b)): H.87, H.61.

**PROOF.** 1. The carrier is `ZMod E → K` — `Nat.card` of a function type (mathlib).
2. `Nat.card (ZMod E) = E` (mathlib). One-step.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GRTJC.89` clause (iii)'s consumer reading ("one K-line per dv-height");
BRIEF F's interface list (H.87 carry cancellation, H.61 fibre count — "the two theorems that
replace type-preservation claims"); WZ-BOX-7 (the 972/972 live-wrap machine witness against
twist type-preservation — the rule this node's form obeys).

**FAITHFULNESS.** Trivial mathematics, load-bearing FORM: the node exists so the consuming
chapters have a named cardinality interface instead of a type-preservation shortcut.

**TEETH.** Lean theorem; re-fired numerically at F.29.

**ENVIRONMENT.** ENV-F1 (+ `[Finite K]`).

---

## 6. §6 — THE Σ-LAW (SIGMALAW), transcription of the proved ledger identity

**Section contract.** Product (3) of BRIEF F. SIGMALAW is the weld layer's one fully
ACCEPTED-and-CERTIFIED proof note (2/2 + SOL-certified; the shortest arc in its queue, with
two independent re-derivations); it proves the Σ-LAW — the per-coordinate ledger identity
`Prnt_j(A) = u_j·Σ_m(R_m v(A))` (THEOREM SL-1's `(Σ-LEDGER)`) and its corollaries SL-C1
(`δ_j = ρ_j/Σ_m(ρ_j)`) and SL-C2 (strict ⟹ byte-equal) — narrowing GRTW2's `W2-OPEN-2` box
(`EFF.GRTW2.49/.50`). F transcribes the abstract algebraic core as provable nodes and the
corpus-scope statement as an interface with GC-13 placeholders for the tower objects.

**DECISION D-F3 — the GC-4 reading for this section (dated 2026-08-15).** BRIEF F phrases
product (3) as "the σ-law (SIGMALAW) through a GC-4 dictionary". Adjudication against the
source: SIGMALAW's Σ is a **coordinate map on the level-`m` residue algebra** (a
character-twisted `K₀`-linear bijection, an automorphism on the `(EC-q)` perimeter), and NO
unit of `EFF-SIGMALAW.md` outputs a factorization type — there is no σ-valued output for
GC-4 to bind. GC-4 is therefore satisfied by CONSUMPTION, not by declaring a dictionary:
where the weld's σ-law faces need σ-valued outputs they consume chapter E's landed
dictionary by name (`ladderSigma` + `ladderSigma_degree` — CHAP-E §7's own header names
chapter F as that consumer), and no F node declares a `FactorizationType`-valued function.
Flagged for the cross-read (§14 item 4). This decision changes no statement of the source —
it reads the brief's packaging instruction against the note's actual content, per GC-10.

### NODE F.14 [def] [fresh]

**STATEMENT.** *The abstract ledger junction.* Over a field `K` (the level-`m` residue
algebra, abstracted): a **ledger junction** consists of a coordinate map `Σ : K → K`, a slot
family of constants `u : ι → Kˣ` (slot-constant — the point of SL-1), and per-slot print and
read maps `Prnt, read : ι → α → K` (with `α` the abstract object type), subject to the
hypothesis field `hledger : ∀ j a, Prnt j a = (u j : K) * Σ (read j a)` — THEOREM SL-1's
`(Σ-LEDGER)` display as a structure, at the abstraction level where its corollaries are
provable. Properties of `Σ` (multiplicativity = the `(EC-q)` automorphism law; injectivity +
`Σ 1 = 1` for the SL-C2 economy) enter as hypotheses of the consuming lemmas, never as
fields — matching the source's own care that SL-C2 needs strictly less than SL-C1.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- An abstract ledger junction (`EFF.SIGMALAW.05`'s `(Σ-LEDGER)` as a structure):
prints = slot constant × Σ of reads. -/
structure LedgerJunction (K : Type*) [Field K] (ι α : Type*) where
  Σmap : K → K
  u : ι → Kˣ
  Prnt : ι → α → K
  read : ι → α → K
  hledger : ∀ j a, Prnt j a = (u j : K) * Σmap (read j a)
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 14 lines.

**SOURCE.** `EFF.SIGMALAW.05` (THEOREM SL-1, `(Σ-LEDGER)` verbatim: "Prnt_j(A) = u_j ·
Σ_m(R_m v(A)), u_j = z_m^{−k_j·A_m}·ε_m(β_j)·U_m(β_j) — slot-constant"); the concrete `u_j`
formula is instance content (F.17).

**FAITHFULNESS.** The abstraction keeps exactly what SL-C1/SL-C2 consume: the ledger shape
and slot-constancy. The scope pin ("every on-line level-m object at every shared-below
junction, every m ≥ 1" — the acceptance record's governing re-display, E10 #1's resolution)
is F.17's, not this structure's.

**TEETH.** SL-VDM (2,828 leak-free samples) RECORDED at source; abstract instances at F.30.

**ENVIRONMENT.** ENV-F1 (+ `[Field K]`).

---

### NODE F.15 [lemma] [fresh]

**STATEMENT.** *SL-C1's core: the slot constant cancels and `δ = ρ/Σ(ρ)`.* Let `J` be a
ledger junction, `j` a slot, and `C, P : α` two objects with reads `x := J.read j C ≠ 0` and
`J.read j P = ρ · x` for a unit `ρ : Kˣ`. Assume `Σmap` is multiplicative on the pair
(`hmul : J.Σmap (ρ * x) = J.Σmap ρ * J.Σmap x` — supplied at instances by the `(EC-q)`
automorphism law) and `J.Σmap x ≠ 0`, `J.Σmap ρ ≠ 0`. Then the ledger ratio
`δ_j := (Prnt j C · (ρ·x)) / (Prnt j P · x)` equals `ρ / Σmap ρ` — E10 #5's four-line
derivation, transcribed: by `hledger` both prints factor through `u j`, which cancels
("which is the point of its being slot-constant"), leaving `(ρ·x/x)·Σ(x)/Σ(ρx) = ρ/Σ(ρ)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem LedgerJunction.delta_eq {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) (j : ι) (C P : α) (ρ : Kˣ)
    (hx : J.read j C ≠ 0) (hP : J.read j P = (ρ : K) * J.read j C)
    (hmul : J.Σmap ((ρ : K) * J.read j C) = J.Σmap (ρ : K) * J.Σmap (J.read j C))
    (hΣx : J.Σmap (J.read j C) ≠ 0) (hΣρ : J.Σmap (ρ : K) ≠ 0) :
    (J.Prnt j C * ((ρ : K) * J.read j C)) / (J.Prnt j P * J.read j C)
      = (ρ : K) / J.Σmap (ρ : K)
```

**DEPENDS.** F.14; mathlib `div_eq_div_iff`, `mul_comm`/`mul_assoc` (field algebra),
`Units.ne_zero`.

**PROOF.** 1. Rewrite both prints by `hledger` and `hP`. 2. `u j` cancels (unit, both
occurrences). 3. Rewrite `Σ(ρx)` by `hmul`; `field_simp` closes. Each step ≤ 3 tactics.

**SIZE.** 26 lines.

**SOURCE.** `EFF.SIGMALAW.08` (COROLLARY SL-C1 "δ_j = ρ_j / Σ_m(ρ_j)"; proof form = E10
#5's complete derivation, whose arithmetic the spec re-checked: "`u_j` cancels, which is the
point of its being slot-constant"; CHAIN terminal E10 #5 — the frozen proof's dangling
ellipsis is NOT transcribed).

**FAITHFULNESS.** The `hmul` hypothesis is stated PER-PAIR rather than as "`Σ` is a ring
automorphism" — the automorphism property is the `(EC-q)` perimeter's content
(`EFF.SIGMALAW.07`, the hostile-pass-derived law) and lives at F.17's instance level; taking
it per-pair here keeps the abstract lemma exactly as strong as the derivation needs. The
`δ_j` normalization (multiplied form rather than a division tower) avoids `0/0` junk while
remaining literally equivalent on the hypotheses — spelled out so the stub stage does not
"simplify" it back.

**TEETH.** SL-DELTA (1,414 leak-free rows keying the element identity directly) — RECORDED;
abstract instance re-fired at F.30.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.16 [lemma] [fresh]

**STATEMENT.** *SL-C2's core: strict ⟹ unit-trivial, on the weaker hypotheses.* Let
`Σ : K → K` be INJECTIVE with `Σ 1 = 1` (no automorphism property — the source's own
economy: "Σ_m is a K₀-linear coordinate BIJECTION fixing 1 … no automorphism property
needed, OA-M1 not consumed"). If `ρ : Kˣ` satisfies `Σ (ρ : K) = 1` — SL-C1's δ being
strict (`δ_j = ρ_j`) forces exactly this at the consuming site — then `(ρ : K) = 1`. Chain:
`Σ ρ = 1 = Σ 1` ⟹ `ρ = 1` by injectivity. This is the Σ-leg that made THEOREM OPEN-2a-Σ
"unconditional on its Σ-leg"; the CONVERSE remains UNPROVED (the note's N-1) and no F node
states it.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem unit_eq_one_of_sigma_eq_one {K : Type*} [Field K]
    {Σmap : K → K} (hinj : Function.Injective Σmap) (h1 : Σmap 1 = 1)
    (ρ : Kˣ) (hρ : Σmap (ρ : K) = 1) : (ρ : K) = 1
```

**DEPENDS.** none (mathlib `Function.Injective`).

**PROOF.** 1. `Σmap ρ = Σmap 1` from `hρ` and `h1`. 2. `hinj` closes. Two steps.

**SIZE.** 8 lines.

**SOURCE.** `EFF.SIGMALAW.09` (COROLLARY SL-C2 = THEOREM OPEN-2a-Σ, proof chain verbatim:
"strict ⟹ δ_j = ρ_j on supp (OA-L3) ⟹ Σ_m(ρ_j) = 1 = Σ_m(1) (SL-C1) ⟹ ρ_j = 1 (Σ_m is a
K₀-linear coordinate BIJECTION fixing 1 …) ⟹ byte-equal (OA-L4)"). The OA-L3/OA-L4 legs
(strictness ⟹ δ = ρ; unit-trivial ⟹ byte-equal) are OPEN2ATTACK content — an `EXT:` note
with no effective spec, so those legs stay at their consuming instances (F.17), cited not
transcribed (GC-10).

**FAITHFULNESS.** "A genuinely weaker hypothesis for the weaker conclusion, correctly
identified" (the spec's own audit) — preserved by taking injective + fixes-1 instead of
automorphism.

**TEETH.** SL-PHIR (1,414) + the separator censuses (SL-SEP2 = 96, SL-SEP3 = 27, exact) —
RECORDED at source.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.17 [interface-carrier] [fresh]

**STATEMENT.** *THEOREM SL-1 at corpus scope (the interface the abstract core instantiates).*
At every **shared-below junction at level `m + 1`**, for every supported slot `j` and every
on-line level-`m` object `A` at weight `β_j` (gap rows included with no correction term —
LEMMA SL-L1's load-bearing gap clause), the ledger identity holds with the §3.4 formula
characters: `Prnt_j(A) = u_j · Σ_m(R_m v(A))`, `u_j = z_m^{−k_j·A_m}·ε_m(β_j)·U_m(β_j)`
slot-constant, where `Σ_m` is the composite of the per-level twists by
`ξ_q = χ_{q−1}^{γ_q}·z_{q−1}^{−e_{q−1}A_{q−1}}` (NOT the bare interior twist σ′ — the note's
defining correction, `EFF.SIGMALAW.02`: the boxed σ′ is the WRONG map, coinciding with Σ_m
exactly on involution geographies, which is why it survived 468 sealed rows), and `Σ_m` is a
ring automorphism by the `(EC-q)` eigen-coefficient law (`ψ_{q−1} ↦ ξ_q^{g_{q−1}}·ψ_{q−1}`,
ideal preservation). **Grade: ACCEPTED 2/2 + CERTIFIED** — citable supply; the Lean form is
a `LedgerJunction` instance whose data (levels, letters `z_q`, characters, evaluators
`H_q`/`P_q`) is tower content: `EFF.SIGMALAW.03/.04 [supplied-by: chapter C]` (the level-`m`
residue-algebra carriers) — the instance node fires at the orchestrator's GC-13 resolution,
blocked until then.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- SL-1's Σ-properties package: what the corollaries consume from the corpus theorem.
The corpus discharge (ACCEPTED 2/2) lands at the C-side junction instance —
BLOCKED: GC-13 (chapter C level carriers); stub as axiom with header per §12. -/
def SigmaLedgerLaw {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) : Prop :=
  Function.Injective J.Σmap ∧ J.Σmap 1 = 1 ∧
    ∀ x y, J.Σmap (x * y) = J.Σmap x * J.Σmap y
```

**DEPENDS.** F.14; `EFF.SIGMALAW.03/.04/.05/.06/.07 [supplied-by: chapter C]` for the
concrete junction instance (GC-13(c)); E's `ladderSigma`/`ladderSigma_degree` by GC-13(b)
node ID where a σ-face consumes the law (D-F3).

**PROOF.** definitional (the carrier `Prop`; the corpus theorem is its instance-level
discharge, ACCEPTED — the instance obligation is booked in §12 as blocked-until-resolution).

**SIZE.** 16 lines.

**SOURCE.** `EFF.SIGMALAW.05` (SL-1 verbatim + the governing scope from the acceptance
record); `.06` (SL-L2, the gauge-ratio law `Λ_q(w) = χ_q^{−w}`, simultaneous induction —
instance content); `.07` (`(EC-q)`, the hostile-pass-derived automorphism law); `.04`
(SL-L1's gap clause); `.02` (the corrected-map headline). Grade: `.11` (ACCEPTED 2/2, six of
six commit pins verified) + `.01` (ledger-CERTIFIED).

**FAITHFULNESS.** The carrier packages exactly the three Σ-properties the corollaries
consume (injective, fixes 1, multiplicative); SL-1's full quantifier lives at the C-side
instance. The wrong-map lesson is carried as a statement fence: no F or C node may define
`Σ_m` as the bare `sigma_twist` (`z_q ↦ θ_q z_q`) — the corrected ξ-composite is the only
sanctioned definition (`EFF.SIGMALAW.02`'s two machine-witnessed non-involution separators
are the refutation of record).

**TEETH.** the sealed battery (6,970 samples; all preregistered families GREEN; all six
teeth rows CAUGHT) + SL-INVREC 218/218 (why the wrong map survived) — RECORDED; F.30 fires
the `ξ₂ = θ₂⁻¹` degeneration numerically.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.18 [def+lemma] [fresh]

**STATEMENT.** *The formula character and its `q = 2` degeneration.* Over `K` with letters
`z χ : Kˣ` and exponents `γ e A : ℤ` (integer exponents — `zpow`), define the **formula
character** `xiChar χ γ z e A := χ ^ γ * z ^ (−(e * A))` (`ξ_q = χ_{q−1}^{γ_q} ·
z_{q−1}^{−e_{q−1}A_{q−1}}`, `EFF.SIGMALAW.02/.03`; `ξ₁ := 1` is the E10 #2 supplement,
covered by the base instance). Lemma (the spec's own arithmetic audit, transcribed): at the
base level `χ = 1`, `xiChar 1 γ z e A = (z ^ (e * A))⁻¹` — i.e. `ξ₂ = θ₂⁻¹` where
`θ₂ = z₁^{e₁A₁}` is the boxed interior twist: **at `q = 2` the true map is exactly the
inverse of the boxed one**, and at `q ≥ 3` it differs further by the χ-chain factor — the
divergence the non-involution separators witness.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The §3.4 formula character `ξ = χ^γ · z^{−eA}` (`EFF.SIGMALAW.03`). -/
def xiChar {K : Type*} [Field K] (χ : Kˣ) (γ : ℤ) (z : Kˣ) (e A : ℤ) : Kˣ :=
  χ ^ γ * z ^ (-(e * A))

theorem xiChar_base {K : Type*} [Field K] (γ : ℤ) (z : Kˣ) (e A : ℤ) :
    xiChar 1 γ z e A = (z ^ (e * A))⁻¹
```

**DEPENDS.** none (mathlib `one_zpow`, `zpow_neg`).

**PROOF.** 1. `1 ^ γ = 1` (mathlib). 2. `z ^ (−(eA)) = (z ^ (eA))⁻¹` (`zpow_neg`).
3. `one_mul`. Three rewrites.

**SIZE.** 14 lines.

**SOURCE.** `EFF.SIGMALAW.02` (the corrected map, verbatim: "ξ_q = χ_{q−1}^{γ_q}·
z_{q−1}^{−e_{q−1}A_{q−1}} — i.e. θ_q^{−1} at q = 2, and θ_q^{−1}·(the χ-chain correction
χ_{q−1}^{γ_q}) at q ≥ 3"; the spec's arithmetic audit of exactly this: "At q = 2, χ₁ = 1
(the base), so ξ₂ = z₁^{−e₁A₁} = θ₂⁻¹ ✓"); `.13`'s `ξ₁ := 1` supplement RECORDED.

**FAITHFULNESS.** Pure character bookkeeping; the tower indexing (which `χ`, `z`, `γ`, `e`,
`A` at which level) is C's instance data.

**TEETH.** F.30 fires `xiChar` instances at `q = 2` and `q = 3` including a NON-involution
geography (SL-INVREC's lesson: involution geographies hide the wrong map — the gate must
include a separator-style instance).

**ENVIRONMENT.** ENV-F1.

---

<!-- RESUME: §6 composed (F.14–F.18, DECISION D-F3). Next: §7 (recon + structural clauses,
F.19–F.26, DECISIONs D-F1/D-F2). -->

<!-- SENTINEL: BP-F END OF FILE -->
