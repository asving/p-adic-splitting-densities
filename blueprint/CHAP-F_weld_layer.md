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

<!-- RESUME: §§3–4 composed (F.01–F.06). Next: §5 (GENHN-BOX-2 / W-9, F.07–F.13), then §6
(SIGMALAW, F.14–F.18), §7 (recon + structural, F.19–F.26), §8, §9 (F.27–F.28), §10 gates
(F.29–F.30), §§11–14. -->

<!-- SENTINEL: BP-F END OF FILE -->
