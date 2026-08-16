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

> **AMENDMENT BANNER 2026-08-16 — THE STAGE-0e STUB GATE HAS RUN, AND SIX DEFECTS ARE REPAIRED IN
> PLACE.** `leanspec/Leanspec/ChapF.lean` (commits `1905bb6b` / `3212150a`; green: **41 signed
> declarations**, 50 executed gate `example`s + 6 in-instance `decide`s at `q = 2` AND `q = 3`,
> zero `sorry`, zero `native_decide`, `autoImplicit` off) recorded **F-D1…F-D6** in its header.
> Every repair is tagged `[repaired: A-W.1/F-D<n>]` at the passage it touches, and the record —
> findings, verbatim originals, evidence — is **AMENDMENT A-W.1** at the end of this file.
> Load-bearing beyond spelling: **F-D3** adds the `One`/`Pow` instances F.10's `^` needs **with
> the inverse taken in `Kˣ`, not in `K`** (with the `K`-side spelling the executed `q = 3` gate
> leg cannot `decide`); **F-D4** gives F.22's injectivity helper a signed type (machine-checked at
> this amendment, `e ≠ 0` shown necessary); **F-D5/F-D6** replace five §10 gate FORMS
> (noncomputable `finrank`/`Nat.card`, non-reducing `orderOf` and `Inv (ZMod n)`, set-level
> images, the unregistered `Fact (Nat.Prime 5)`) and make the table-built `F₄`/`F₉` — not
> `AdjoinRoot` — the gate's field constructions of record. Read A-W.1 before consuming F.08,
> F.09, F.10, F.12, F.14, F.15, F.16, F.17, F.22, F.27, F.29 or F.30.
>
> **AMENDMENT-SERIES NAME, DECLARED ONCE.** This chapter's series is **`A-W.<n>`** ("W" for
> *weld*), **not** `A-F.<n>`: chapter B's amendment series already occupies `A-F.<n>`
> (`A-F.3`, `A-F.5`, `A-F.6`, `A-F.7`, `A-F.10` in `blueprint/CHAP-B_leaf_layer.md`, where the
> "F" means *finisher*, not *chapter F*), so an `A-F.1` here would collide across files in exactly
> the `grep '\[repaired: A-'` the fleet uses to find repairs. Defect IDs keep the chapter letter
> (`F-D<n>`, as the stub gate's header spells them); the amendment tag is `A-W.<n>/F-D<n>`. The
> sibling series for reference: `A-E.<n>` (chapter E), `A-H.<n>` (chapter H), `A-1` (chapter D),
> undated `§A-<n>` blocks (chapter G).

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
`gaugeCobdry`/`slotScale`/`resTwist` + the perimeter carrier `JD0Box2` + the strike shape
`JD0SiteStrike` (F.01–F.05); the twisted-carry layer `CarryCocycle`/`TwistedAlgebra` with
its laws + the face carrier `GenhnBox2` + `W1Transport` (F.07–F.12); the Σ-law core
`LedgerJunction`/`delta_eq`/`unit_eq_one_of_sigma_eq_one`/`SigmaLedgerLaw`/`xiChar`
(F.14–F.18 — σ-valued outputs are E's `ladderSigma`, per DECISION D-F3); the
structural-clause interfaces `JAResLaw`/`JAGridLaw`/`XiWSatisfies`/`JBVtxFace`/`wmFence_*`/
`WeldMPkg`/`gaugeBdry_eq_iff`/`DmultW` (F.19–F.26, incl. chapter D's C7 anchors F.23/F.24);
and the chapter-I package `WeldSupply`/`WeldObligations` (F.27–F.28).

**Kind census** (mechanically counted over this file's `### NODE` headings): 8 `def`
(F.01, F.05, F.07, F.08, F.14, F.24, F.27, F.28), 8 `lemma` (F.02, F.03, F.06, F.13, F.15,
F.16, F.23, F.25), 2 `theorem` (F.09, F.10), 1 `def+lemma` (F.18), 9 `interface-carrier`
(Prop-valued carriers at ledger strength: F.04, F.11, F.12, F.17, F.19–F.22, F.26), 2
`gate` (F.29, F.30) — **30 nodes**. **BRIEF F estimated 50–70; the shortfall is deliberate
and §13 accounts for it**: the estimate predated this composition's finding that the
GRTJB/GRTJC structural mass consumed by the two surviving conjuncts enters as
*supplier-grade rows on carrier statements* (INSTANCE-ROW/RECORDED), not as per-clause Lean
nodes — transcribing them as nodes would re-create the out-of-cone build the census exists
to prevent. **Split-mandated:** F.10 → 2 files; split candidates F.03, F.09. **Fleet
planning figure: ≈ 31–33 Lean files.**

**DECLARATION census, LANDED at the stage-0e gate** *[added: A-W.1/F-D5 bookkeeping;
`leanspec/Leanspec/ChapF.lean`, mechanically counted]*: the 30 nodes carry **41 signed
declarations** = **8 `structure`** (`ValueDictSite` F.04, `JD0SiteStrike` F.05, `CarryCocycle`
F.07, `CarrySite` F.11, `LedgerJunction` F.14, `WeldMPkg` F.24, `WeldSupply` F.27,
`WeldObligations` F.28) + **18 `def`** (`gaugeCobdry`, `slotScale` F.01; `slotScaleEquiv` F.02;
`resTwist` F.03; `JD0Box2` F.04; `TwistedAlgebra`, `single` F.08; `GenhnBox2` F.11;
`W1Transport` F.12; `SigmaLedgerLaw` F.17; `xiChar` F.18; `JAResLaw` F.19; `JAGridLaw` F.20;
`XiWSatisfies` F.21; `jbShear`, `JBVtxFace` F.22; `gaugeBdry` F.25; `DmultW` F.26) + **15
theorem-shaped rows over 11 nodes** (F.02 ×1, F.03 ×3, F.06, F.09, F.10 ×2, F.13, F.15, F.16,
F.18, F.23 ×2, F.25 — `axiom`s at the exact signed types in the stub, theorems at landing).
**Plus, below the contract line:** F.08's **5** instances (`Mul`, `AddCommGroup`, `Module K`, and
F-D3's `One`/`Pow`) and F.22's `jbShear_injective` (added at A-W.1/F-D4), which the fleet lands
but which are not one-public-declaration-per-node rows. Nodes with no declaration of their own:
F.29/F.30 (gates — their contract is the executed check list) and the two §7 DECISIONs D-F1/D-F2
(DAG rulings, not Lean objects).

**Graph shape** (from `spec/DAG_BLUEPRINT_F.tsv`, computed mechanically from the DEPENDS
fields): **114 rows over the 30 nodes; intra-chapter proof-dep graph ACYCLIC, 6 layers,
widths `12, 8, 6, 1, 2, 1`**; critical path 5 edges (F.07 → F.08 → F.09 → F.10 → F.11 →
F.28). No HARD node. **Blocked-until-resolution (GC-13):** F.17's C-side instance discharge
and F.24's M4 instance — the carrier DECLARATIONS themselves elaborate now; only the
instance obligations wait (§12).

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
and helper lemmas live below it in the same file (GC-6.5's helper clause) — **six helpers, not
four** *[repaired: A-W.1/F-D3: the committed list omitted the `One`/`Pow` pair that F.10's `^`
resolves through]*.

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
-- [repaired: A-W.1/F-D3] the two helpers F.10's `^` needs, and the committed list omitted;
-- bodies are F.09's own prose ("`single 0 (cc.c 0 0)⁻¹` is a two-sided unit"), executed:
--   instance : One (TwistedAlgebra cc) := ⟨single 0 (((cc.c 0 0)⁻¹ : Kˣ) : K)⟩
--   instance : Pow (TwistedAlgebra cc) ℕ := ⟨fun f n => npowRec n f⟩
```

**⚠ SIGNATURE NOTE — THE UNIT'S INVERSE IS TAKEN IN `Kˣ`, NEVER IN `K`** *[added:
A-W.1/F-D3; this is the gate's load-bearing subtlety, not a spelling preference]*. The `One`
body must form the inverse in the UNIT GROUP and coerce afterwards,
`(((cc.c 0 0)⁻¹ : Kˣ) : K)` — **not** `((cc.c 0 0 : K))⁻¹`. Machine-checked reason (the executed
`q = 3` leg of F.29 check 4): mathlib's `Inv (ZMod n)` is `Nat.gcdA`-based well-founded
recursion, so a `K`-side inverse does **not** kernel-reduce and the `decide` gate on
`(single 1 1)^2 = ζ • single 0 1` dies at `K = ZMod 3`; `Kˣ`'s `Inv` is projection to the stored
`inv` field and reduces. Same wall as F-D5(iv). A fleet agent landing a full `Monoid`/`Ring`
instance instead (the natural target once F.09 is proved) inherits the constraint on its `one`,
and `Pow` must agree with `npowRec` (Monoid's default `npow`) or F.10(b)'s statement moves.

**DEPENDS.** F.07; mathlib `Finset.sum` over `ZMod E` (`Fintype (ZMod E)` via `NeZero E`),
`npowRec` *[added: A-W.1/F-D3]*.

**PROOF.** definitional.

**SIZE.** 26 lines (with all six helpers) *[repaired: A-W.1/F-D3 — was 20]*.

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

**⚠ SIGNATURE NOTE — THE SIGNED CONTRACT IS ASSOCIATIVITY ONLY** *[added: A-W.1/F-D3 rider; the
E-D13 precedent — recorded so the gap is not read as a transcription loss]*. The STATEMENT's
second half ("`single 0 (cc.c 0 0)⁻¹` is a two-sided unit") has **no conjunct in the signature**;
it is carried by F.08's `One` instance, whose body IS that element *[A-W.1/F-D3, with the `Kˣ`
inverse]*. A landing agent that wants the unit claim in theorem form adds `one_mul`/`mul_one`
below the contract line in F.08's file (helpers, GC-6.5), not a second public declaration here;
nothing in the chapter consumes them — F.10(b) needs `Pow`, not a `Monoid`.

**DEPENDS.** F.07, F.08 (including F-D3's `One`); mathlib `Finset.sum_comm`, `Finset.sum_bij`
(re-indexing the double convolution sum), `Finset.mul_sum`.

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

**⚠ SIGNATURE NOTE — WHAT `^` RESOLVES THROUGH** *[added: A-W.1/F-D3]*. `(single 1 1 :
TwistedAlgebra cc) ^ E` needs `Pow (TwistedAlgebra cc) ℕ`, hence (through `npowRec`) a `One`;
both are F.08's helpers **as of A-W.1** and were absent from the committed helper list — the
committed F.10 signature did not elaborate. With F-D3's bodies (`npowRec`, and `One` = F.09's
two-sided unit with the inverse formed in `Kˣ`) the statement's CONTENT is unchanged: `npowRec`
is the `npow` any later `Monoid` instance carries. The `single 0 1` normalization on the
right-hand side is untouched and remains a statement fence.

**DEPENDS.** F.07, F.08 (`single`, `Mul`, `Module`, and F-D3's `One`/`Pow` — *[added:
A-W.1/F-D3]*), F.09; mathlib `Module.finrank_pi` (`finrank K (ZMod E → K) =
card (ZMod E)`), `ZMod.card`, `Finset.prod_Ico_succ_top` (the orbit-product induction),
`npowRec`.

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
  -- [repaired: A-W.1/F-D2] was `∀ λ, Rharness λ = (c λ : K) * RGMN λ`: `λ` is the lambda
  -- keyword, a hard parse error. The type is IDENTICAL (binder names are not part of it).
  ∃ c : ι → Kˣ, ∀ l, Rharness l = (c l : K) * RGMN l
```

**⚠ BINDER SPELLING — DECLARED ONCE FOR THE WHOLE CHAPTER** *[added: A-W.1/F-D2]*. At our pin
`λ` is the lambda keyword, so `∀ λ, …` fails with *"unexpected token 'λ'; expected '(', '[', '_',
'{', '⦃' or identifier"* — the same family as CHAP-E's E-D3 (`hλ`) and this chapter's F-D1 (`Σ`).
**Chapter rule:** no binder, hypothesis or field name may carry a non-`isLetterLike` Greek token
(`λ`, `Σ`, `Π`); Greek stays in prose and in display mathematics. **The choice, recorded:** this
node's binder is **`l`** — the form the stage-0e gate executed, and the reading is a bare index of
the abstract `ι`, not the source's slope letter. F.26's `∀ lam mu : Λ` stays **byte-unchanged**:
it was already legal, and there the two binders transliterate the source's λ/μ *line pair*, where
`lam`/`mu` reads better than `l`/`m`. Both spellings are legal and **binder names are not part of
the type**, so a landing agent may spell this node's binder `lam` and is not BLOCKED either way;
`λ` itself is never legal. (The two nodes were internally inconsistent as committed — F.26 avoided
the trap that F.12 walked into; the inconsistency is now a declared convention with a reason.)

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
algebra, abstracted): a **ledger junction** consists of a coordinate map `Σ : K → K` (**Lean field
name `sigmaMap`** — *[repaired: A-W.1/F-D1: `Σmap` is not a legal identifier at the pin]*), a slot
family of constants `u : ι → Kˣ` (slot-constant — the point of SL-1), and per-slot print and
read maps `Prnt, read : ι → α → K` (with `α` the abstract object type), subject to the
hypothesis field `hledger : ∀ j a, Prnt j a = (u j : K) * sigmaMap (read j a)` — THEOREM SL-1's
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
  -- [repaired: A-W.1/F-D1] field renamed `Σmap` → `sigmaMap`: `Σ` (U+03A3) is EXCLUDED from
  -- `isLetterLike` at Lean 4.31 (it is the Sigma-type token), so `Σmap : K → K` fails with
  -- "unexpected token 'Σ'; expected command". A FIELD name is part of the contract — this is
  -- the spelling the fleet must land, and the signed one cannot be landed at all.
  sigmaMap : K → K
  u : ι → Kˣ
  Prnt : ι → α → K
  read : ι → α → K
  hledger : ∀ j a, Prnt j a = (u j : K) * sigmaMap (read j a)
```

**⚠ CONTRACT NOTE — THE RESPELLED FIELD NAME IS PART OF THE TYPE** *[added: A-W.1/F-D1]*. Two of
F-D1's five renames touch FIELD names (`LedgerJunction.sigmaMap` here, `WeldSupply.hSigma` at
F.27) and therefore change the projections every consumer writes (`J.sigmaMap`, `W.hSigma`);
the other three (F.15's `hSigmax`/`hSigmarho`, F.16's `sigmaMap` binder) are binder names and
carry no type content. Every use site in §6 and §9 is threaded. The `Σ` of the source's
`(Σ-LEDGER)` display stays `Σ` in prose and in the display — only Lean identifiers move.

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
`J.read j P = ρ · x` for a unit `ρ : Kˣ`. Assume `sigmaMap` is multiplicative on the pair
(`hmul : J.sigmaMap (ρ * x) = J.sigmaMap ρ * J.sigmaMap x` — supplied at instances by the
`(EC-q)` automorphism law) and `J.sigmaMap x ≠ 0`, `J.sigmaMap ρ ≠ 0` *[repaired: A-W.1/F-D1
throughout this node — `Σmap` → `sigmaMap`, `hΣx`/`hΣρ` → `hSigmax`/`hSigmarho`]*. Then the
ledger ratio `δ_j := (Prnt j C · (ρ·x)) / (Prnt j P · x)` equals `ρ / sigmaMap ρ` — E10 #5's
four-line
derivation, transcribed: by `hledger` both prints factor through `u j`, which cancels
("which is the point of its being slot-constant"), leaving `(ρ·x/x)·Σ(x)/Σ(ρx) = ρ/Σ(ρ)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem LedgerJunction.delta_eq {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) (j : ι) (C P : α) (ρ : Kˣ)
    (hx : J.read j C ≠ 0) (hP : J.read j P = (ρ : K) * J.read j C)
    -- [repaired: A-W.1/F-D1] `J.Σmap` → `J.sigmaMap` (F.14's field), and the two hypothesis
    -- binders `hΣx`/`hΣρ` → `hSigmax`/`hSigmarho` ("unexpected token 'Σ'; expected ')'").
    (hmul : J.sigmaMap ((ρ : K) * J.read j C)
      = J.sigmaMap (ρ : K) * J.sigmaMap (J.read j C))
    (hSigmax : J.sigmaMap (J.read j C) ≠ 0) (hSigmarho : J.sigmaMap (ρ : K) ≠ 0) :
    (J.Prnt j C * ((ρ : K) * J.read j C)) / (J.Prnt j P * J.read j C)
      = (ρ : K) / J.sigmaMap (ρ : K)
```

**DEPENDS.** F.14; mathlib `div_eq_div_iff`, `mul_comm`/`mul_assoc` (field algebra),
`Units.ne_zero`.

**PROOF.** 1. Rewrite both prints by `hledger` and `hP`. 2. `u j` cancels (unit, both
occurrences). 3. Rewrite `sigmaMap (ρx)` by `hmul`; `field_simp` closes (the two non-vanishing
hypotheses enter as `hSigmax`/`hSigmarho`). Each step ≤ 3 tactics.

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
    -- [repaired: A-W.1/F-D1] implicit binder `{Σmap : K → K}` → `{sigmaMap : K → K}`; a binder
    -- name, so no type content moves (but named-argument call sites must use the new spelling).
    {sigmaMap : K → K} (hinj : Function.Injective sigmaMap) (h1 : sigmaMap 1 = 1)
    (ρ : Kˣ) (hρ : sigmaMap (ρ : K) = 1) : (ρ : K) = 1
```

**DEPENDS.** none (mathlib `Function.Injective`).

**PROOF.** 1. `sigmaMap ρ = sigmaMap 1` from `hρ` and `h1`. 2. `hinj` closes. Two steps.

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
BLOCKED: GC-13 (chapter C level carriers). -/
-- [repaired: A-W.1 bookkeeping] the docstring's trailing "stub as axiom with header per §12"
-- is STRUCK: this carrier is a real `def` (§12(b), and the gate landed it as one); it is the
-- C-side INSTANCE that is blocked-until-resolution and never stubbed as provable.
def SigmaLedgerLaw {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) : Prop :=
  -- [repaired: A-W.1/F-D1] `J.Σmap` → `J.sigmaMap` (three occurrences; F.14's field name)
  Function.Injective J.sigmaMap ∧ J.sigmaMap 1 = 1 ∧
    ∀ x y, J.sigmaMap (x * y) = J.sigmaMap x * J.sigmaMap y
```

**DEPENDS.** F.14; `EFF.SIGMALAW.03/.04/.05/.06/.07 [supplied-by: chapter C]` for the
concrete junction instance (GC-13(c)). **E's dictionary, UPGRADED to GC-13(a) landed
declaration names** *[repaired: A-W.1 cross-chapter note 1, verified at the stage-0e gate
2026-08-16]*: E.45/E.46 have LANDED in `leanfinal` (`Uniformity/ChapE/E45.lean`, `E46.lean`), so
the committed GC-13(b)-by-node-ID entry becomes the two landed names
`Uniformity.Density.Ladder.ladderSigma` and `Uniformity.Density.Ladder.ladderSigma_degree`
(E46 also lands `ladderSigma_degree_eq_deg`, the conditional block-degree form — not consumed
here). Per D-F3 **no F SIGNATURE references either name** — SIGMALAW has no σ-valued output, so a
Lean dependency would be manufactured; the upgrade is a citation-form upgrade only.
**Wiring caveat (the ORCHESTRATOR's item, not an F defect):** `ladderSigma` is reachable from
`import Uniformity`, but `ladderSigma_degree` is **not** — `E46.lean` is imported only by
`E47.lean` and `Uniformity/ChapE.lean`'s roll-up lists `E01, E07, E25, E26, E34, E45` only, so the
GC-4 degree-conservation leg sits outside the root import graph at HEAD (the gate's `#check` on it
is commented out for exactly that reason). Any F consumer that ever needs the name by import waits
on the ChapE roll-up.

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

## 7. §7 — MUTUAL-RECON ADJUDICATIONS + THE REACHABLE GRT STRUCTURAL CLAUSES

**Section contract.** Products (4) and (5) of BRIEF F. First the two DECISIONs the global
DAG defers to this chapter (DAG_README SCC items 3–4: "the chapter blueprint must decide
which direction is the statement dependency; this draft does not"); then the structural
clauses that Display A's `AllOInterfaces[… W/J …]` conjunct (HYP.126: "Weld/J suppliers are
characteristic-general at every use") and the two surviving faces' supplier stacks actually
name — each an interface-carrier at its recorded scope and grade, never an upgrade.

**DECISION D-F1 — the `EFF.GRTW2.20 ↔ EFF.LIFTCORNER.72` SCC (the W2-OPEN-2-designation
pair; dated 2026-08-15).** **Ruling: the statement dependency is `EFF.LIFTCORNER.72 →
EFF.GRTW2.20` (LIFTCORNER depends on GRTW2); the reverse recorded edge is consumer-
acknowledgment provenance, not a dependency.** Grounds, from the units' own text: (i)
LIFTCORNER.72 IS a consumption census — "COR 2 and the S1 orbit frame consume GRTW2 clause 3
(the ψ-transport definition + its corner degeneration)", with the grade-cap consequence
("the unit's grade is CAPPED at that consumption"); its content quantifies over GRTW2's
objects. (ii) The opposite direction exists in the harvest only because GRTW2's acceptance
record ACKNOWLEDGES the consumer by name ("the accepted LIFTCORNER's shift-descent
consumption … now ride[s] an ACCEPTED supplier at its fenced scope") — the spec itself calls
this "the ONE fully closed supplier-consumer loop in the shard": declaration on one side,
acknowledgment on the other. An acknowledgment row is `ledger-index`-class provenance under
the DAG's own vocabulary. (iii) Corroborating: GRTW2.20's own SUPERSESSION KIND for the
Σ-LAW's re-derivation of the same recursion is "license (corroboration, nothing moves)" —
GRTW2.20's statement consumes nothing of LIFTCORNER. **DAG consequence (§11):** the TSV
emits `EFF.LIFTCORNER.72 → EFF.GRTW2.20 (stmt-dep)` and re-classes the reverse edge
`provenance` — breaking SCC 3.

**DECISION D-F2 — the `EFF.GRTW2.35 ↔ EFF.LIFTCORNER.62` SCC (the W2-OPEN-1-designation
pair; dated 2026-08-15).** **Ruling: the statement dependency is `EFF.LIFTCORNER.62 →
EFF.GRTW2.35`; the reverse edge is again consumer-acknowledgment provenance.** Grounds: (i)
LIFTCORNER.62 is the WITHDRAWN-identification record — its entire content is a claim ABOUT
W2-OPEN-1's statement ("W2-OPEN-1 as recorded (GRTW2 §5.3) quantifies over the committed
value/cocycle battery … with the transported classifier lifts"), itemizing what is owed
((a) the orbit-membership display; (b) the battery legs, K12 above all) before any slice of
it may be claimed — a reference to GRTW2.35's statement, hence a stmt-dep. (ii) GRTW2.35's
own three E5 re-affirmations ("W2-OPEN-1 remains open …") make no reference to LIFTCORNER
content; the reverse harvest edge is LIFTCORNER's appearance in GRTW2's consumer tables.
(iii) Scope note: BOTH units are out-of-cone mass (§3 rows 4 and 10–11's neighborhood —
the value layer); this adjudication is DAG hygiene, not capstone conditionality. **DAG
consequence (§11):** `EFF.LIFTCORNER.62 → EFF.GRTW2.35 (stmt-dep)`; reverse re-classed
`provenance` — breaking SCC 4.

*(Both rulings follow one principle, stated once so the cross-read can attack it: where an
SCC pairs a CONSUMPTION/WITHDRAWAL record with the unit it consumes or corrects, the record
depends on the unit; an acceptance record's acknowledgment of its consumer is provenance.
The two SCCs are the only two genuine MUTUAL-RECON pairs in the exact-resolved subgraph.)*

### NODE F.19 [interface-carrier] [fresh]

**STATEMENT.** *THEOREM JA-RES at its recorded scope (the per-slot law — `JD0-BOX-2`'s
residual leg and JB-DEV(iii)(RES)'s supplier).* Verbatim scope from `EFF.GRTJA.08`: level
`m ≥ 2`, shared keys below `m`; IF `(VD-(m−1))` holds at every on-line digit `a_i` of `A`
(the PER-DIGIT PROVISO), THEN for every attained abscissa `i`:
`c_i = z_{m−1}^{−i·A_{m−1}} · C_i` — the print's order-`m` residual coefficient equals the
harness packed digit times the PURE CHARACTER in the abscissa. **Unconditional at `m = 2`**
(the proviso is `(VD-1)` = W2-L3, consumed); **proviso-scoped at `m ≥ 3`**, root-inclusive
`[r2]`. **Grade: GRTJA arc 1/2 — the single priced input on J-D0's critical path (honesty
F-7); carried, never upgraded.** Lean form: a `Prop`-carrier over abstract site data (the
print/harness coefficient families and the exponent datum), whose instance is the priced
supplier obligation chapter I sees through F.04's provenance.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- JA-RES at recorded scope (`EFF.GRTJA.08`): the per-slot pure-character law relating
print residual coefficients to harness packed digits. Carried at GRTJA arc 1/2. -/
def JAResLaw {K : Type*} [Field K] {ι : Type*}
    (printCoeff harnessDigit : ι → K) (z : Kˣ) (A : ℤ) (abscissa : ι → ℤ) : Prop :=
  ∀ i, printCoeff i = (z ^ (-(abscissa i * A)) : Kˣ) * harnessDigit i
```

**DEPENDS.** none (shape). Instance provenance: `EFF.GRTJA.08` (+ its proviso structure);
the m = 2 unconditional instance additionally consumes W2-L3 = `EFF.GRTW2.14`.

**PROOF.** definitional (a carrier).

**SIZE.** 12 lines.

**SOURCE.** `EFF.GRTJA.08` (statement + proof + the spec's re-derived exponent audit: "the
cancellation is exact and the character is purely abscissa-linear — which is precisely what
makes JA-BOX-1's slot-independent form false"); `EFF.GRTJA.24` (grade record superseding the
stale 0/2 self-descriptions); C2-1's consumer sweep ("JA-RES survives unchanged").

**FAITHFULNESS.** The carrier fixes the law's SHAPE (one `z`-power per abscissa — exactly
what F.05's strikes instantiate); the per-digit proviso and the root-inclusive perimeter are
instance-side hypotheses (they quantify over tower digits F has no carrier for). JA-BOX-1's
refuted slot-independent form is fenced by construction: the exponent is `abscissa i * A`,
never a constant.

**TEETH.** CK-RES 443 scored + the 16-row proviso-failing boundary census — RECORDED.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.20 [interface-carrier] [fresh]

**STATEMENT.** *THEOREM JA-GRID at its C2-4-pinned scope (J-D0's grid leg).* Governing form
`THEOREM JA-GRID-CORR` (`EFF.GRTJA.07`'s supersession, TERMINAL C2-4): **only the arithmetic
grid identity (eq-(12-int) digits = abscissa/side coordinates) and the carry clause are
unconditional; the print T-point additionally needs `u(V) ≥ 0`.** Consumed by J-D0 at
GRTJA's arc grade (BOX-1's own wording: "rides JA-GRID at GRTJA's arc grade"). The `u ≥ 0`
proviso's unbounded-grid form is HYP.21 — OUT of cone (§3 row 1); the carrier therefore
states the unconditional half only, with the T-point clause explicitly absent.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- JA-GRID-CORR's unconditional half (`EFF.GRTJA.07`, terminal C2-4): the integer-grid
digit/coordinate identity with its carry clause, as an abstract indexed law. Carried at
GRTJA arc 1/2; the print T-point clause (needs `u(V) ≥ 0`) is deliberately absent. -/
def JAGridLaw {ι : Type*} (digit : ι → ℤ) (coord : ι → ℤ) (carry : ι → ℤ) : Prop :=
  ∀ i, digit i = coord i + carry i
```

**DEPENDS.** none.

**PROOF.** definitional (a carrier).

**SIZE.** 10 lines.

**SOURCE.** `EFF.GRTJA.07` (+ the C-4 freeze-predicate row: "only the arithmetic grid and
carry are unconditional; the print T-point needs `u(V) ≥ 0`" — supersession kind scope-pin,
TERMINAL C2-4); `EFF.JD0.25` (the priced-supplier table: "JA-GRID grid = T-side abscissas;
J-D0 consumes both AT THAT GRADE").

**FAITHFULNESS.** The abstract shape (digit = coordinate + carry) is the eq-(12-int)
identity's skeleton; the concrete grid objects are the sites'. Scope-pin honoured by
omission of the T-point clause.

**TEETH.** CK-GRID 3,248 GREEN — RECORDED.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.21 [interface-carrier] [fresh]

**STATEMENT.** *The `(ξ, w)` covariance family at its accepted fenced scope (`JD0-BOX-2`'s
GRTW2 leg).* From `EFF.GRTW2.19` (the closed form: THE DISPLAYED PAIR SATISFIES the orbit
equations — deliberately NOT "is the pair", the support-stabilizer non-uniqueness of `.21`)
and `EFF.GRTJA.11` (the orbit action; ORB legs PROVED/machine, chamber half consumed at
split grade riding W2-OPEN-2 — the chamber half is out-of-cone value mass, §3 row 10, and
is NOT carried here). Lean form: the orbit-equation predicate — a pair `(ξ, w)` SATISFIES
the covariance equations for a residual `ψ` when `w • ψ(ξ·y) = ψ`-transported form holds;
carried as the abstract satisfaction predicate with the non-uniqueness disclosure in the
statement gloss (distinct satisfying characters exist on sparse supports — the
invisible-twist genre, machine-recorded at I4B r = 4 with `ξ = −1` invisible on
`supp = {0,2}`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld
open Polynomial

/-- The (ξ,w) orbit-equation predicate (`EFF.GRTW2.19`): the displayed pair SATISFIES the
covariance equations — an existence/satisfaction form, never uniqueness (`EFF.GRTW2.21`). -/
def XiWSatisfies {K : Type*} [Field K] (ξ w : Kˣ) (R ψ : K[X]) : Prop :=
  R = (w : K) • ψ.comp (C (ξ : K) * X)
```

**DEPENDS.** F.03 (the `resTwist` normal form is the monic-normalized special case).

**PROOF.** definitional (a carrier).

**SIZE.** 10 lines.

**SOURCE.** `EFF.GRTW2.19` (the closed form, ACCEPTED); `EFF.GRTW2.21` (remark 2: the
stabilizer non-uniqueness + the I4B r = 4 invisible twist, with the spec's own stabilizer
arithmetic `ξ² = 1 ⟹ ξ ∈ {±1}` over `F₃`); `EFF.GRTJA.11` (the orbit action's machine legs
ORB-EPS 1,744 / ORB-RES 444 / TW-INST 1,452); `EFF.JD0.25` (consumed as "part of the gauge
dictionary (BOX-2); anchor re-choice legitimacy rides the accepted lift covariance, with
LIFTCORNER as its corner cap").

**FAITHFULNESS.** Satisfaction, not uniqueness — the exact deliberate weakening the source
records; a fleet agent adding a uniqueness clause has left the source. The LIFTCORNER corner
cap is provenance on F.04, not a Lean dependency.

**TEETH.** CK-XI (21 perimeter junctions, 0 violations, invisible twist RECORDED not
hidden) — RECORDED; F.30 exhibits an invisible-twist instance numerically (`q = 3`:
`ξ = −1` on `supp = {0,2}` over `F₃`).

**ENVIRONMENT.** ENV-F1.

---

### NODE F.22 [interface-carrier] [fresh]

**STATEMENT.** *The JB position faces at ACCEPTED 2/2 (J-D0's L4 leg).* From `EFF.JD0.25`'s
accepted-supplier table: "JB-VTX vertex-for-vertex polygon, JB-DEV same-division — the
position faces S2.1(a)/(c); row 12's `u ≥ 0` proviso carried where B-ties are consumed
(BOX-1)". The B-ties are out of cone (§3 rows 1, 3, 13), so the proviso is NOT carried here
— what the cone consumes is: (JB-DEV) the harness division chain and the classifier's
division chain are the SAME division (clause (i), `EFF.GRTJB.89`), and (JB-VTX) the shear
`Σ_q(i,u) = (i, e_q·u + h_q·i)` carries the harness polygon vertex-for-vertex to the print
polygon (clauses (a)/(b), `EFF.GRTJB.101/.102`; the certifier annex E-3 correction: (c)'s
run datum is the ABSCISSA RUN, not ambient lattice data). Lean form: the shear as a def
(provable content — it is an explicit affine map) plus the face predicate.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The JB frame shear `Σ_q(i,u) = (i, e·u + h·i)` (`EFF.GRTJB.86/.101`). -/
def jbShear (e h : ℤ) : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, e * p.2 + h * p.1)

/-- JB-VTX's vertex transport, abstract: the shear maps the harness vertex set onto the
print vertex set (`EFF.GRTJB.102`). ACCEPTED 2/2; instances are site data. -/
def JBVtxFace (e h : ℤ) (harnessVtx printVtx : Set (ℤ × ℤ)) : Prop :=
  jbShear e h '' harnessVtx = printVtx

-- [added: A-W.1/F-D4] the below-the-line helper, NOW SIGNED (it was prose-only, so the stub
-- stage had no type to land and signed nothing — the gate used pointwise images instead).
-- Machine-checked at this amendment (elaborates AND proves at the pin; see A-W.1/F-D4).
theorem jbShear_injective {e h : ℤ} (he : e ≠ 0) :
    Function.Injective (jbShear e h)
```

**⚠ HELPER NOTE — WHY THE HYPOTHESIS IS `e ≠ 0` AND WHAT THE HELPER IS FOR** *[added:
A-W.1/F-D4]*. `e ≠ 0` is necessary, not defensive: at `e = 0` the shear collapses the u-coordinate
(`jbShear 0 1 (0,0) = jbShear 0 1 (0,1) = (0,0)`), machine-checked at this amendment as a negative
control. The helper's consumers are set-level: `JBVtxFace` is an image equality, and injectivity is
what lets a consumer transport a vertex COUNT across the shear (and recover the harness vertex from
its print image). It stays **below the contract line** in F.22's file (GC-6.5 helper clause), so
F.22 keeps one public declaration pair; the corpus frames have `e = e_q ≥ 1`, so the hypothesis is
free at every intended site.

**DEPENDS.** none (mathlib `Function.Injective`, `mul_left_cancel₀`, `Prod.ext`).

**PROOF.** `jbShear`/`JBVtxFace`: definitional. `jbShear_injective` *[added: A-W.1/F-D4 —
this proof was run at the amendment, not merely sketched]*: `intro p q hpq`;
`simp only [jbShear, Prod.mk.injEq] at hpq` splits it into `p.1 = q.1` and
`e * p.2 + h * p.1 = e * q.2 + h * q.1`; rewrite the first into the second and `linarith` gives
`e * p.2 = e * q.2`; `mul_left_cancel₀ he` then `Prod.ext`. 6 tactic lines.

**SIZE.** 22 lines *[repaired: A-W.1/F-D4 — was 14, before the helper was signed]*.

**SOURCE.** `EFF.GRTJB.86` (the two frames and the shear), `.89/.90` (JB-DEV (i)/(ii)),
`.100–.105` (JB-VTX (a)–(e); E-3's abscissa-run correction at `.172` carried: no ambient-
lattice datum appears in the carrier), `.165` (the acceptance record); `EFF.JD0.25` (the
consumption row, verbatim above).

**FAITHFULNESS.** Face-level only: the division-chain identity (JB-DEV(i)) has no leanfinal
carrier for "the classifier's division" yet (chapter C's descent layer), so JB-DEV enters as
provenance on F.04/F.11 rather than a Lean predicate here; JB-VTX's shear IS carried because
it is bare integer affine geometry. Row 12/row 22's no-leg rows: §3 (out).

**TEETH.** the 18-family sealed verdict table + `jb_dev`/`jb_eps` IND legs — RECORDED;
F.30 exercises `jbShear` on a concrete polygon at both primes.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.23 [lemma] [fresh]

**STATEMENT.** *WM-FENCE, the fixed-data character-triviality criterion (PROVABLE — the
criterion, not the out-of-cone law).* For a finite field `K`, `z : Kˣ`, `A : ℤ`: (absolute
form) `(∀ i : ℤ, z ^ (i * A) = 1) ↔ (orderOf z : ℤ) ∣ A`; (slot-grid form)
`(∀ i : ℤ, z ^ (e * i * A) = 1) ↔ (orderOf z : ℤ) ∣ e * A`. Transcribed from
`EFF.WELDMASTER.25`'s displayed pair with the F-4 scoping carried in the statement gloss:
**"Neither display contains an existential quantifier over the fixed inputs"** — the
criterion tests fixed data; it supplies NO freedom or existence theorem for varying `z`,
`A`, the attained set, or the representative (any such variation a consumer needs must be
proved by J-D0 independently — the corrected S6 clause). A DAG edge into WM-FENCE carries
this scoping (§11).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

theorem wmFence_absolute {K : Type*} [Field K] [Finite K] (z : Kˣ) (A : ℤ) :
    (∀ i : ℤ, z ^ (i * A) = 1) ↔ ((orderOf z : ℤ) ∣ A)

theorem wmFence_slotGrid {K : Type*} [Field K] [Finite K] (z : Kˣ) (e A : ℤ) :
    (∀ i : ℤ, z ^ (e * i * A) = 1) ↔ ((orderOf z : ℤ) ∣ e * A)
```

**DEPENDS.** none (mathlib `orderOf_dvd_iff_zpow_eq_one` and `zpow` arithmetic).

**PROOF.** 1. (⟸) if `ord ∣ A` then `z^{iA} = (z^A)^i = 1` — two rewrites. 2. (⟹)
instantiate `i = 1`; `z^A = 1` gives `ord ∣ A` by mathlib `orderOf_dvd_iff_zpow_eq_one`
(integer form). 3. Slot-grid form: apply the absolute form to `A' := e*A` after re-indexing
`e*i*A = i*(e*A)` (`mul_left_comm`).

**SIZE.** 20 lines.

**SOURCE.** `EFF.WELDMASTER.25` (the F-4 annex: both displays verbatim; the corrected
consumption clause "the J-D block … may consume WM-FENCE only as the fixed-data (F-b)
character-triviality criterion … WM-FENCE supplies no freedom or existence theorem"; the
`F₅` witness with the spec's re-derivation: `ord(2) = 4 ∤ 1`, `χ₁ = 2⁻¹ = 3 ≠ 1`).

**FAITHFULNESS.** The criterion is transcribed; `PERIM-μ` — the LAW that the criterion's
condition holds on all claimed order-≥2 faces — is HYP.86, OUT of cone (§3 row 9). The two
must never be conflated; this node's docstring says so.

**TEETH.** Lean theorem; the `F₅` witness + both-prime instances fire at F.30.

**ENVIRONMENT.** ENV-F1 (+ `[Finite K]`).

---

### NODE F.24 [def] [fresh]

**STATEMENT.** *`WELD-M-PKG`, the anchored five-face transport package (chapter D's C7
anchor).* Transcribed from `EFF.WELDMASTER.22` (the C6 F-1 annex — the charge unit): for a
tower on the frozen S1 perimeter there exists ONE NAMED PACKAGE `𝐓 = (𝐓_{M0}, …, 𝐓_{M4})`
whose fields are exactly the frozen clauses (M0 division-chain identity; M1 `w_m = v_{m+1}`
+ the affine shear with its fences; M2 the per-slot read/operator character transport; M3
the multiplication transport to `K^c[ℤ/E]` on the scored stratum; M4 the representative/
lift covariance at W2-C3's accepted fenced scope). **"One" means one named five-field
package, not uniqueness and not a further common-map coherence theorem** — the RECORD-
ASSEMBLY LEMMA is the product constructor ("Choose the five cited witnesses and apply the
product/record constructor"), and the η-twist non-uniqueness witness (`∂(Ẽη) = ∂Ẽ`) is
F.25's content. Lean form: a `structure` with five `Prop` fields — the record IS the
theorem's honest content; **no cross-face compatibility field exists** (the F-1 lesson
honoured structurally; T1's own consumption at L13/L1074 honours exactly this scope).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- WELD-M-PKG (`EFF.WELDMASTER.22`): the five-face transport package as a record of five
Props. Existence-only; NO cross-face coherence field. Chapter D's (C7) consumption anchor;
the field contents are per-face site data (M3 = a `CarryCocycle` realization; M4 at W2-C3's
fenced scope via GC-13). -/
structure WeldMPkg (M0 M1 M2 M3 M4 : Prop) : Prop where
  m0 : M0
  m1 : M1
  m2 : M2
  m3 : M3
  m4 : M4
```

**DEPENDS.** F.07/F.08 (M3's shape), F.22 (M1's shear), F.21 (M4's covariance shape);
`EFF.GRTW2.29 [supplied-by: chapter C]` for M4's W2-C3 instance scope (GC-13(c)).

**PROOF.** definitional; the RECORD-ASSEMBLY LEMMA is the anonymous constructor — no
separate node.

**SIZE.** 14 lines.

**SOURCE.** `EFF.WELDMASTER.22` (the package display + RECORD-ASSEMBLY LEMMA + "No
compatibility beyond those displayed ties is asserted" + the seven-item consumer sweep with
its verified T1 cross-check); `EFF.WELDMASTER.03` (the superseded frozen S1 "ONE transport"
wording — NOT transcribed; the annex's package form governs).

**FAITHFULNESS.** The `Prop`-parameters form makes the record exactly the "product of five
propositions" the source says it is; typing the five faces concretely would assert the
cross-face tie the source explicitly declines. Chapter D cites this node for (C7) as "an
interface map and scope fence" — its GC-13 placeholder resolves here.

**TEETH.** the frozen face table's per-field batteries — RECORDED at WELDMASTER; the
package's Lean content is definitional.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.25 [lemma] [fresh]

**STATEMENT.** *The gauge-torsor lemma (the `H¹ = 0` uniqueness claim killed, structurally).*
From `EFF.WELDMASTER.23` (the C6 F-2 annex): for `F, G : ZMod E → Kˣ` with equal
coboundaries (`∂F = ∂G` where `(∂F) a b := F a * F b * (F (a+b))⁻¹`), the ratio `η := F/G`
is a group homomorphism `ZMod E → Kˣ`; conversely `∂(F·η) = ∂F` for every homomorphism `η`.
Hence gauges with a fixed coboundary form a torsor under `Hom(ZMod E, Kˣ) ≅ μ_E(K)` —
"rather than being unique". Minimal witness (gate F.29): `E = 2`, `K = F₅`,
`η(ν) = (−1)^ν` nontrivial since `−1 = 4 ∈ F₅ˣ` has order 2.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The 1-coboundary of a gauge (`EFF.WELDMASTER.23`). -/
def gaugeBdry {E : ℕ} [NeZero E] {K : Type*} [Field K] (F : ZMod E → Kˣ) :
    ZMod E → ZMod E → Kˣ := fun a b => F a * F b * (F (a + b))⁻¹

theorem gaugeBdry_eq_iff {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (F G : ZMod E → Kˣ) :
    gaugeBdry F = gaugeBdry G ↔
      ∀ a b, (F a * (G a)⁻¹) * (F b * (G b)⁻¹) = F (a + b) * (G (a + b))⁻¹
```

**DEPENDS.** none (mathlib commutative-group algebra).

**PROOF.** 1. (⟹) pointwise: divide the two coboundary identities; `Kˣ` is commutative so
the terms regroup — `field_simp`-style unit algebra. 2. (⟸) reverse the same regrouping.
3. The homomorphism reading (`η := F * G⁻¹` multiplicative) is definitional from the RHS.

**SIZE.** 24 lines.

**SOURCE.** `EFF.WELDMASTER.23` (the torsor derivation, whose every step the spec re-checked
— `H¹(ℤ/E, Kˣ) = Hom = μ_E(K)`, "need not vanish"; the withdrawn PE10 gloss NOT transcribed;
the F₅ witness); its CONDITIONALITY ("affects only the certification narrative, not
WM-CLASS's proved existence/class identity").

**FAITHFULNESS.** Stated as the iff between coboundary equality and the ratio being a
character — the torsor phrasing without importing group-cohomology carriers. Blocks any
future "canonical gauge by `H¹ = 0`" claim by giving the counterexample machinery a name.

**TEETH.** Lean theorem; the `μ₂(F₅)` witness at F.29.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.26 [interface-carrier] [fresh]

**STATEMENT.** *The `(DMULT-w)` tier — what W-9's chain rides, at its HEAD provenance.*
Verbatim shape from `EFF.GRTJC.69`: there is a unit `ω(λ, μ) ∈ K_mˣ`, **independent of `f`
and `g`** (line-only), with `𝑅_{λ+μ}(f·g) = ω(λ,μ) · y^{δ(λ,μ)} · 𝑅_λ(f) · 𝑅_μ(g)`,
`δ(λ,μ) ∈ {0,1}`. Status at HEAD (the five-layer CHAIN's terminal): **DERIVED from
[FGMN] Thm 4.2's rank-one freeness via LEMMA JC-RANKMULT (Annex #6); the "quoted product
identity" claim WITHDRAWN** — so the literature import underneath is the `(IN-3)` FGMN
graded package (`EFF.GRTJC.43`, PDF-VERIFIED at Annex #3), and **per Part V that exercised
cite is an owner gate-(b) item**: `[cite: FGMN Thm 4.2 (rank-one freeness), via
EFF.GRTJC.43's (IN-3) package]`, routed through chapter I's cite block. Consumer split
carried verbatim: "(COORD-B)(2), (MULT-B), JC-CARRY-m, W-8 and JC-BOX-4's corner closure
need only (DMULT-w)" — the mechanism being that the normalized coordinate `ρ_λ = 𝑅_λ/a_λ` is
invariant under ANY line-wise rescaling. `(DMULT-s)` (`ω ≡ 1`) is §3 row 5: OUT.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The (DMULT-w) tier (`EFF.GRTJC.69`): residual multiplicativity up to a line-only unit,
with the {0,1} wrap exponent. Carried; discharge rides the gate-(b) FGMN cite. -/
def DmultW {K : Type*} [Field K] {Λ : Type*} [Add Λ]
    (R : Λ → K[X] → K[X]) (y : K[X]) (δ : Λ → Λ → ℕ) : Prop :=
  ∀ lam mu : Λ, ∃ ω : Kˣ, ∀ f g : K[X],
    R (lam + mu) (f * g) = (ω : K) • (y ^ δ lam mu * R lam f * R mu g)
```

**DEPENDS.** F.07 (the δ shadow's shape). Cite provenance: `EFF.GRTJC.43` ((IN-3), the
CITE-SCOPE unit and chain home), `EFF.GRTJC.125` (Annex #3, FGMN cites PDF-VERIFIED),
`EFF.GRTJC.129` (Annex #6, JC-RANKMULT). Gate-(b) flag: **owner sign-off required for the
FGMN import** (Part V; chapter I's cite block aggregates).

**PROOF.** definitional (a carrier).

**SIZE.** 14 lines.

**SOURCE.** `EFF.GRTJC.69` (the two-tier display + the displayed (DMULT-w) derivation
`ω(λ,μ) = c_{λ+μ}/(c_λc_μ)` — "the 2-coboundary of the line-wise unit system; nothing gives
ω ≡ 1"; the consumer split; the weld-audit row verified: "the one reachable GRTJC face,
COROLLARY W-9, rides the CITABLE tier").

**FAITHFULNESS.** `∃ ω` is placed AFTER `(lam, mu)` and BEFORE `(f, g)` — ω depends only on
the lines, the exact content of "independent of f and g" (a quantifier-order trap the spec's
own text resolves; the stub stage must not commute it). The `•`-form keeps `ω` visibly a
unit.

**TEETH.** R1-DMULT 2,784/0 etc. measure the `ω ≡ 1` tier (OUT); (DMULT-w) "carries no
separate leg" (the spec's own disposition) — signed accordingly in §13.

**ENVIRONMENT.** ENV-F1.

---

## 8. §8 — THE WELD-ZERO PENDING ARC (no nodes; the recorded interface to a running unit)

**Status of record (verified at HEAD, 2026-08-15 — the honesty F-2 findings, restated as
this section's contract).** `HYP.149` (the GENHN-BOX-2 discharge route: gr(O_L) re-aim +
GENTOW5-A0/A1) is **IN-PROGRESS at clean-pass 1 of 2**. Arc so far: composed 2026-08-14
(commit `7aec45f1`) → r1 (one CRITICAL cured: WZ-3(ii)'s type-preservation claim withdrawn,
re-routed through a relabelling bijection; J-D0 removed from the fold's supplier list; one
GAP + eight minors cured) → the Opus-arm hostile pass (`runs/comp13/WZP2_output.log`,
0C + 0G + 6 minors — clean pass 1) → pass 2 of 2 REASSIGNED from gpt-5.6-sol to Fable-max
(append #56's pilot; its EOF line: "WELD-ZERO confirmation pass (pass 2 of 2) runs on
Fable-max now") — **LAUNCHED, IN FLIGHT, no landing commit in the tree** (checked through
append #61; `leanfinal/notes/` has no WELD-ZERO note; the unit note is
`lean/notes/openmath/WELDZERO_2026-08-14.md`, status line "composed, attempt 0/2, hostile
arc owed"). WELD-ZERO has **no effective spec** (`EXT:WELDZERO_2026-08-14.md`), so under
GC-10 this chapter cannot transcribe its content even if it wished to.

**What this chapter did and did not take from the arc.** Took: (i) the WZ-BOX-7 rule
(honesty F-3) — a *negative* finding about frozen GENHN/GENH4 text, machine-witnessed,
governing F's statement forms; (ii) the consumption-geography facts the GRTJC spec itself
verified against WELDZERO's citations (W-9 consumed at GENHN S6.1 L874 only; clause (iv)
not consumed) — these are facts about GENHN/GRTJC at HEAD, independently re-verified by the
0a compiler, not WZ results. Did NOT take: any WZ lemma (WZ-1/WZ-2/WZ-B), the gr(L) graded-
field frame, or the wrap-floor formula — those are the running unit's content.

**What a LANDED second pass changes, and under whose authority.** If the Fable-max pass
returns clean and the ledger books the arc (the 0b fold is the authority — a fleet agent or
chapter author may not re-disposition rows): per HYP.148/139's own v4 notes, `HYP.148`
(CARRY) retires and `HYP.139` (MATH) retires WITH it — "the replacement frame is gr(O_L),
not an FGMN object, so the W-1 transport would no longer be consumed." F-side consequence,
pre-authorized here so the later editor needs no fresh licence: a dated AMENDMENT block in
this section converting F.11 (`GenhnBox2`) and F.12 (`W1Transport`) from carried hypotheses
to DISCHARGE notes citing the WZ unit's landed statements, and re-checking F.26's FGMN cite
(the WZ route bypasses the FGMN frame at layer 1 — the cite may then be needed only by
GRTJC-internal mass, possibly lifting the gate-(b) item off the capstone path). Chapter I's
corresponding conjunct fields move in the same fold. **Until then: HYP.148 CARRY, HYP.139
MATH, both at full strength, and every §5 statement stands as written.**

---

## 9. §9 — THE CHAPTER-I HANDOFF PACKAGE

**Section contract.** The terminal supply, packaged the way chapter I's Display-A block
consumes it (the CHAP-E `LadderSupply`/`LadderObligations` pattern; noting, per the E
precedent's own care, that these are plain structures — no claim of mirroring H.95's
`def`-`Prop` kind).

### NODE F.27 [def] [fresh]

**STATEMENT.** *`WeldSupply` — the proved-supply record.* One structure bundling the data a
consuming chapter (D's gauge layer; H's landed count layer; I's assembly) instantiates to
use the weld layer's PROVED mathematics: a carry cocycle with its twisted algebra (F.07/
F.08, laws F.09/F.10/F.13), a ledger junction with its Σ-property package (F.14, F.17), and
the two criterion lemmas' inputs (F.23's `(z, A)` data; F.25's gauge pair). Everything in
this record is either proved in F or carried by a named field — no hidden hypothesis.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The weld layer's proved supply, as one record (chapter-I/D consumption surface). -/
structure WeldSupply (E : ℕ) [NeZero E] (K : Type*) [Field K] (ι α : Type*) where
  cc : CarryCocycle E K
  J : LedgerJunction K ι α
  -- [repaired: A-W.1/F-D1] field renamed `hΣ` → `hSigma` (illegal identifier at the pin). A
  -- FIELD name, so this is contract content: consumers write `W.hSigma`.
  hSigma : SigmaLedgerLaw J
```

**DEPENDS.** F.07, F.14, F.17.

**PROOF.** definitional.

**SIZE.** 10 lines.

**SOURCE.** assembly node (no corpus unit — the record packages §§5–7's named supply; the
CHAP-E §2 "terminal supply" pattern).

**FAITHFULNESS.** `hSigma` *[repaired: A-W.1/F-D1 — was `hΣ`]* is the one carried field (F.17's
C-side discharge pending GC-13); the rest instantiates from proved nodes.

**TEETH.** none (packaging); the members' teeth are their own.

**ENVIRONMENT.** ENV-F1.

---

### NODE F.28 [def] [fresh]

**STATEMENT.** *`WeldObligations` — the carried-hypothesis block handed to chapter I.* One
field per surviving Display-A weld obligation, at exactly ledger strength: (1) `jd0box2` —
F.04's perimeter for each consumed site (the seven-site family abstracted as an index type);
(2) `genhnBox2` — F.11's face for each `μ ≥ 3` carry site (chapter I indexes the conjunct by
`n ≥ 6`); (3) `w1` — F.12's transport for the FGMN-framed sites. Annotations carried
alongside (not Prop fields): the gate-(b) cite flag on F.26 (`[cite: FGMN Thm 4.2 via
(IN-3)]`, owner sign-off at I's cite block); the `AllOInterfaces[W/J, J-D0]` generality
conjuncts (HYP.126, HYP.129) — supplied STRUCTURALLY by F's statements being quantified over
every finite `K`/every `O`, both characteristics, but the ledger rows and their conjunct
fields remain chapter I's (F does not absorb them). **Per Part V, every field here
terminates in I as a discharge node or a gate-(b) literature cite — no third category; §8
names the one pending discharge route.**

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld

/-- The weld layer's carried obligations (chapter I's Display-A weld fields), at ledger
strength. -/
structure WeldObligations {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ]
    {Site CSite FSite : Type*}
    (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K) : Prop where
  jd0box2 : ∀ s, JD0Box2 (vsite s)
  genhnBox2 : ∀ s, GenhnBox2 (csite s)
  w1 : W1Transport Rh RG
```

**DEPENDS.** F.04, F.11, F.12; annotations reference F.26 and HYP.126/HYP.129.

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** Display A (the frozen v5 conjunct list: `JD0-BOX-2`, `(GENHN-BOX-2 if n≥6)`
carrying HYP.139, `AllOInterfaces[… W/J … J-D0 …]`); HYP.74/148/139/126/129 (the strengths).

**FAITHFULNESS.** `Prop`-valued structure (`: Prop where`) so it can sit inside I's
hypothesis block without size issues; the site index types are parameters because the
concrete site enumerations are other chapters' objects (GC-13). Nothing added, nothing
dropped: the reconciliation check in §3 (Display-A footprint = exactly these + the
generality rows) is this node's completeness certificate.

**TEETH.** signed non-applicability (a hypothesis block; H.09's rule — §13).

**ENVIRONMENT.** ENV-F1.

---

## 10. §10 — GATES (GC-11: `q = 2` AND `q = 3`; `e > 1 ∧ f > 1`; the degeneracy and
coincidence regimes exercised)

**Arena note (the chapter's own coincidence traps, from F.06 and SL-INVREC).** Two
degeneracies stalk this chapter's numerics: (i) over `F₂` the unit group is trivial — every
character check silently passes (F.06); (ii) on involution geographies (`ξ² = 1`) the
corrected Σ-map and the WRONG boxed map coincide — 468 sealed rows hid the defect that way.
The gates therefore run character content at `q = 2` on **F₄** (units of order 3 —
non-involution) and at `q = 3` on **F₉** (units of order 4/8 — non-involution) or `F₃`/`F₅`
where the check is order-2-safe, and include the explicit `F₂`-triviality and
involution-instance checks as NEGATIVE controls. `e > 1 ∧ f > 1`: `E = 2` (the coset group,
e-side) with `K = F₄` over `F₂` and `K = F₉` over `F₃` (f = 2 both).

**Field constructions — THE FALLBACK FIRED; the table-built fields are the form of record**
*[repaired: A-W.1/F-D6, executed 2026-08-16]*. ~~`F₄ := AdjoinRoot (X² + X + 1 : (ZMod 2)[X])`,
`F₉ := AdjoinRoot (X² + 1 : (ZMod 3)[X])`~~ carry **no** `DecidableEq`/`Fintype` instance
(`AdjoinRoot` is a quotient of a polynomial ring), so **no `decide` gate can fire on them at all**
— this is not a "resists" case, it is a hard absence. Under this section's own pre-authorization
the gate uses private **table-built** fields below the gate in the same file, and those are what
the fleet lands:

* `F4 := ZMod 2 × ZMod 2` with `θ² = θ + 1`, i.e. `(x₁,x₂)·(y₁,y₂) = (x₁y₁ + x₂y₂,
  x₁y₂ + x₂y₁ + x₂y₂)`; `CommRing` field-by-field `by decide`; `Field` on the explicit inverse
  `x⁻¹ = x^(q−2) = x²`. Generator `ω := θ = (0,1)`, order 3 (non-involution).
* `F9 := ZMod 3 × ZMod 3` with `θ² = −1`, i.e. `(x₁,x₂)·(y₁,y₂) = (x₁y₁ − x₂y₂,
  x₁y₂ + x₂y₁)`; same `CommRing`/`Field` pattern, `x⁻¹ = x⁷`. Generator `i := θ = (0,1)`,
  order 4 (non-involution).

`native_decide` appears NOWHERE (axiom census). The `AdjoinRoot` spellings stay recorded as the
mathematical identification of the two fields (and are what a *proof* about `F₄`/`F₉` would use);
they are not gate carriers.

**⚠ GATE-FORM RIDER (GC-11), STANDING FOR THIS CHAPTER** *[added: A-W.1/F-D5]*. Five §10 legs are
not `decide`-able as displayed. The substitution table below is **binding**: a gate agent lands the
right-hand form, and the pinned VALUES are unchanged (all were reproduced at the stage-0e gate).

| # | displayed form | why it fails at the pin | executed form (land this) |
|---|---|---|---|
| (i) | `Module.finrank K (TwistedAlgebra cc)`, `Nat.card (TwistedAlgebra cc)` | `finrank`/`Nat.card` are noncomputable | `show` through the def's own carrier `ZMod E → K`, then `simp` (finrank) resp. `rw [Nat.card_eq_fintype_card]; decide` |
| (ii) | `orderOf z = 4` | `orderOf` does not kernel-reduce | the power certificate `z ^ 4 = 1 ∧ z ^ 2 ≠ 1` (order ∣ 4, ≠ 1, ≠ 2 ⟹ 4) |
| (iii) | set-level images `slotScale u '' S = S`, `jbShear e h '' V = V'` | `Set` image equality is not decidable | pointwise on the named finite witnesses (the arithmetic content §10 pins) |
| (iv) | `(2 : ZMod 5)⁻¹ = 3` | mathlib's `Inv (ZMod n)` is `Nat.gcdA`-based (well-founded recursion) | the UNITS inverse `((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 3` **plus** the inverse-pair product `(2 : ZMod 5) * 3 = 1` |
| (v) | any `F₅` instance of a `[Field K]`-based node | `Field (ZMod 5)` needs `Fact (Nat.Prime 5)`, which mathlib does **not** register (only 2 and 3) | declare `instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩` beside the gate; every `F₅` example owes this line |

Item (iv) is the same reduction wall as F.08's `One` instance (F-D3): inverses that must reduce are
taken in `Kˣ`.

### NODE F.29 [gate] [fresh]

**STATEMENT.** *The twisted-algebra gate.* With the standard nontrivial 2-cocycle on
`ZMod 2` (`c 1 1 = ζ`, else `1`; `δ 1 1 = 1`, else `0`), check, by `decide`/`norm_num`:
1. the `CarryCocycle` fields hold — all 8 triples of the `Kˣ`-cocycle identity and all 8 of
   the integer identity — at `(K, ζ) = (F₄, ω)` (`ω` a generator, order 3 — nontrivial
   cocycle at `q = 2`) AND `(K, ζ) = (F₃, 2)` (`q = 3`);
2. `Nat.card (TwistedAlgebra cc) = 16` at `F₄` (`= 4²`) and `= 9` at `F₃` (`= 3²`) — F.13's
   identity, instance-level — **executed in gate form (i)**: `show` through the carrier
   `ZMod 2 → K`, `Fintype.card` by `decide`, then `Nat.card_eq_fintype_card`
   *[repaired: A-W.1/F-D5(i)]*;
3. `Module.finrank K (TwistedAlgebra cc) = 2` both — F.10(a) — **executed in gate form (i)**: a
   `show`-through-the-carrier `simp` leg, NOT `decide` (`finrank` is noncomputable)
   *[repaired: A-W.1/F-D5(i)]*;
4. `(single 1 1)² = ζ • single 0 1` both — F.10(b) with the orbit product
   `∏_{k=1}^{1} c(1,k) = c(1,1) = ζ`: expected `ω` at `F₄`, `2` at `F₃`; **executed pointwise**
   (`∀ t : ZMod 2, ((single 1 1)^2) t = ((ζ : K) • single 0 1) t`) so `decide` applies without
   `funext`, and this is the leg that forces F-D3's `Kˣ` inverse in `One`
   *[repaired: A-W.1/F-D5(i)+F-D3]*;
5. the `E = 3` integer-carry instance: the `{0,1}` table `δ a b = if a.val + b.val ≥ 3 then
   1 else 0` on `ZMod 3` satisfies the integer cocycle identity (27 triples, `decide`) —
   the carry shadow at odd `E`;
6. NEGATIVE control: at `K = F₂` every `CarryCocycle` has `c ≡ 1` (units trivial — F.06's
   regime), checked by `decide`.
`e > 1 ∧ f > 1` witness: instance 1's `F₄` leg (`E = 2`, `F₄/F₂`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld
-- one #eval/decide block per check, leancheck N3Cert idiom; expected values in comments,
-- e.g.  example : (twistGate_F4.pow2_value = genF4) := by decide
-- [repaired: A-W.1/F-D5] the executed shape: the two `CarryCocycle` gate instances carry
-- checks 1 as their PROOF FIELDS (`cocycle := by decide`, `δ_le_one := by decide`,
-- `δ_cocycle := by decide` — 3 fields × 2 primes = the 6 in-instance `decide`s), and every
-- other leg is an `example` in the substituted form of the §10 gate-form rider.
```

**DEPENDS.** F.07, F.08, F.10, F.13.

**PROOF.** `decide`/`norm_num` per check (stub stage (c) executes BEFORE axiom stubs sign —
GC-6.6), in the §10 rider's substituted forms where the displayed form is not decidable.

**SIZE.** ≤ 40 lines of checks **plus ~110 lines of table-built field helpers shared with F.30**
(the two fields with their `DecidableEq`/`Fintype`/`CommRing`/`Field` instances and generators)
*[repaired: A-W.1/F-D6 — the committed box said "the private field-table helper if needed"; it was
needed, and it is the bulk of the gate file]*.

**SOURCE.** GC-11; `EFF.GRTJC.89`'s JC7 battery shape (cocycle + carry + E-fold chain,
"two ways") — these are its smallest Lean-executable instances.

**TEETH.** Lean-executed gate; mirrored as `verification/chapF_gate_twisted.py` (§13).

**ENVIRONMENT.** ENV-F1 (concrete instances).

---

### NODE F.30 [gate] [fresh]

**STATEMENT.** *The character/fence/ledger gate.* By `decide`/`norm_num`, in the §10 gate-form
rider's substituted spellings *[repaired: A-W.1/F-D5 throughout this node]*:
1. **WM-FENCE instances (F.23):** the source's own `F₅` witness — `orderOf (2 : (ZMod 5)ˣ)
   = 4` **executed as the power certificate `z5 ^ 4 = 1 ∧ z5 ^ 2 ≠ 1` (+ `z5 ≠ 1`)**, form (ii);
   `¬((4 : ℤ) ∣ 1)`; and the character value `(2 : ZMod 5)⁻¹ = 3 ≠ 1` **executed as the units
   inverse `((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 3` plus the pair product `(2 : ZMod 5) * 3 = 1`**,
   form (iv). The witness needs the local `Fact (Nat.Prime 5)` instance, form (v). Then a `q = 2`
   pair at `F₄` (`z = ω`, order 3: fails at `A = 1`, holds at `A = 3`) and a `q = 3` pair at
   `F₃` (`z = 2 = −1`, order 2: fails at `A = 1`, holds at `A = 2`);
2. **`xiChar` instances (F.18):** `xiChar 1 0 (2 : (ZMod 5)ˣ) 2 1 = (2²)⁻¹ = 4` (the
   `ξ₂ = θ₂⁻¹` degeneration, concrete); a NON-involution instance at each prime — `q = 2`:
   `χ = ω, γ = 1, z = ω` over `F₄` (order-3 character; expected value computed at stub
   time and pinned in the file); `q = 3`: `χ = i, γ = 1, z = i` over `F₉` with `i² = −1`
   (order-4 character) — the separator-style instances SL-INVREC's lesson demands;
3. **slotScale counts (F.02):** over `Γ = Fin 1`, `K = F₃`: the stratum `S = {v | v 0 = 0}`
   satisfies `slotScale u '' S = S` for both units and `Nat.card ↥S = 1` — **executed pointwise**
   (`∀ u v, v 0 = 0 → slotScale u v 0 = 0`) plus `Fintype.card {v // v 0 = 0} = 1`, form (iii);
   NEGATIVE control (the JD0-T-NONCHAR failure mode): the additive shift `v ↦ v + 1` maps `S` to
   `{v | v 0 = 1} ≠ S` — executed as `((0 : Fin 1 → ZMod 3) + 1) 0 ≠ 0`, the perimeter boundary
   displayed executably;
4. **`F₂` degeneracy (F.06):** `slotScale u = id` for every `u` over `K = F₂`, `decide`;
5. **the torsor witness (F.25):** over `E = 2`, `K = F₅`: `η ν = (−1)^ν` is a nontrivial
   character (`η 1 = 4 ≠ 1`) and `gaugeBdry (fun _ => 1) = gaugeBdry η` — `μ₂(F₅)`
   nontrivial, uniqueness dead at the smallest interesting instance;
6. **JB shear (F.22):** `jbShear 2 1` maps the concrete harness vertex pair
   `{(0,0), (2,1)}` to `{(0,0), (2,4)}` — an `e = 2, h = 1` instance, plus a `q = 3`-side
   instance `jbShear 3 2` on the same pair (`{(0,0), (2,7)}`) — **executed as the four pointwise
   image values**, form (iii) (`jbShear 2 1 (0,0) = (0,0)`, `jbShear 2 1 (2,1) = (2,4)`, and the
   `e = 3, h = 2` pair), which is exactly the arithmetic this leg pins.
All six checks carry their expected values IN the file; a mismatch at stub stage is a
stop-the-line blueprint defect, not a thing to patch silently. **A gate-FORM substitution from
§10's rider is not a mismatch** *[added: A-W.1/F-D5]* — every value above was reproduced at the
stage-0e gate; what moved is the spelling that makes the kernel reduce.

**Additional executed legs, folded in at the stage-0e gate** *[added: A-W.1/F-D5]*: the
involution/non-involution SEPARATOR pair SL-INVREC's lesson demands, made executable — on `z² = 1`
the character and its inverse coincide (`((-1 : (ZMod 3)ˣ)^1)⁻¹ = (-1)^1`), while at order 3/4 they
separate (`(ω^1)⁻¹ ≠ ω^1` at `F₄`, `(i^1)⁻¹ ≠ i^1` at `F₉`); and the `xiChar` non-involution values
pinned at both primes (`xiChar ω 1 ω 1 2 = ω² = (1,1)` at `F₄`; `xiChar i 1 i 1 2 = i³ = (0,2)` at
`F₉`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Weld
-- decide/norm_num blocks; leancheck N3Cert idiom (expected values pinned in-file).
-- [added: A-W.1/F-D5(v)] the gate-local `instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩` and
-- the unit witness `def z5 : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩` sit here; the `F₄`/`F₉`
-- table-built fields are shared with F.29 (§10's construction block).
```

**DEPENDS.** F.02, F.06, F.18, F.22, F.23, F.25 (and F.22's `jbShear_injective` is NOT needed —
the leg is pointwise; see A-W.1/F-D4).

**PROOF.** `decide`/`norm_num` per check, in §10's substituted forms.

**SIZE.** ≤ 40 lines of checks (the shared field tables are counted at F.29)
*[repaired: A-W.1/F-D6]*.

**SOURCE.** GC-11; `EFF.WELDMASTER.25` (the F₅ witness, re-derived in the spec and here);
`EFF.SIGMALAW.02` (the ξ₂ = θ₂⁻¹ audit); `EFF.JD0.22` BOX-5 (the F₂ census) + the NONCHAR
tooth ("an additive slot shift … breaks … counts" — the failure-mode display).

**TEETH.** Lean-executed gate; mirrored as `verification/chapF_gate_chars.py` (§13).

**ENVIRONMENT.** ENV-F1 (concrete instances).

---

## 11. DAG ADDITIONS + FENCE ADJUDICATIONS

**Machine-readable edges:** `spec/DAG_BLUEPRINT_F.tsv` — **114 rows over the 30 nodes**,
computed mechanically from this file's DEPENDS fields (`proof-dep` rows; `BP.F.*` and
`BP.H.61`/`BP.H.87` targets) and SOURCE fields (`stmt-dep` rows against the merged,
contiguous `EFF.GRTJA/GRTJB/GRTJC/GRTW2/WELDMASTER/LIFTCORNER/SIGMALAW/JD0.*` IDs plus the
`HYP.*` ledger rows). **Every cited endpoint verified to exist in `spec/DAG_NODES.tsv` at
HEAD** (all seven weld notes have merged specs; no shard-local remap is needed for F —
GC-12 satisfied directly).

**The two adjudication rows (D-F1/D-F2, §7).** The TSV's last two rows install the DECIDED
statement-dependency directions `EFF.LIFTCORNER.72 → EFF.GRTW2.20` and
`EFF.LIFTCORNER.62 → EFF.GRTW2.35`. The complementary half of each ruling — re-classing the
harvest's REVERSE edges (`GRTW2 → LIFTCORNER`, the consumer-acknowledgment rows) out of the
dependency graph — is a `dag_build.py`/checker change on harvested rows, which is the
ORCHESTRATOR's (GC-12's division of labour); the checker's SCC 3–4 annotations should then
read ADJUDICATED-BY: CHAP-F D-F1/D-F2.

**dag_check status at composition (executed, then shared outputs restored to HEAD).**
`dag_build.py` + `dag_check.py` were run WITH this chapter's TSV merged: dangling-ID check
**PASS** (every F endpoint declared); cycle check — **F introduces ZERO new SCCs** (the
SCC list is byte-identical with and without `DAG_BLUEPRINT_F.tsv`; verified by diff). The
checker's overall verdict at HEAD is FAIL on **2 unadjudicated SCCs among `BP.C.*` nodes**
(`{BP.C.56, .84, .85, .87}` and `{BP.C.99, .100, .102, .104}`) — chapter C's in-progress
rows, flagged to the orchestrator and the C composer (§14 item 10), not F's to fix. The
committed `spec/dag_check_output.txt` is left at HEAD (the orchestrator's re-run commits
the merged outputs).

**Cross-chapter edges (the citation-rule ledger, GC-13):**
* **Into H (committed node IDs):** `BP.F.13 → BP.H.87`, `BP.F.13 → BP.H.61` — the two
  type-preservation-replacing theorems, cited as interfaces (honesty F-3). No other H node
  is touched (F consumes nothing of H §8 — that entry point is B/E's).
* **Into E (D-F3) — UPGRADED from committed node IDs to GC-13(a) LANDED NAMES** *[repaired:
  A-W.1, cross-chapter note 1, verified 2026-08-16]*: `BP.F.17 → BP.E.45`, `BP.F.17 → BP.E.46`
  now resolve to `Uniformity.Density.Ladder.ladderSigma` (`leanfinal/Uniformity/ChapE/E45.lean`)
  and `Uniformity.Density.Ladder.ladderSigma_degree` (`E46.lean`) — both LANDED. The edges stay
  annotation-only (D-F3: no F SIGNATURE references either name). **Orchestrator wiring item
  (already known, restated here because F's gate found it):** `ladderSigma_degree` is NOT in the
  `Uniformity` root import graph at HEAD — `E46.lean` is imported only by `E47.lean`, and
  `Uniformity/ChapE.lean` rolls up `E01, E07, E25, E26, E34, E45` only. `ladderSigma` IS reachable.
  Not an F defect and not F's to fix; it becomes one only if a later F node consumes the degree leg
  by import.
* **Into C (GC-13(c) placeholders — the orchestrator's resolution list):**
  `EFF.SIGMALAW.03 [supplied-by: chapter C]` (F.17 — the level-`m` residue-algebra
  carriers); `EFF.GRTW2.29 [supplied-by: chapter C]` (F.24 — M4's W2-C3 fenced-scope
  instance). Concrete `CarrySite`/`ValueDictSite` instances additionally arrive from H's
  landed count layer and C's composed stages (F.11's DEPENDS note) — placeholder-free
  because F carries them as type parameters.
* **Into D (GC-14):** no F node cites ϑ-orientation content (checked: no F statement
  mentions ϑ) — the GC-14 anchor obligation is vacuous for F; chapter D consumes F.24
  (WELD-M-PKG, its C7 anchor) and F.23 (WM-FENCE with the F-4 scoping) in the other
  direction.

**Fence adjudications (honesty F-10; BRIEF F trap (v)).** The global checker reports 82
fence-crossing edges; the weld notes' fence rows (per the checker's census: GRTW2 15,
WELDMASTER 15, LIFTCORNER 12, GRTJC 10, GRTJA 10, GRTJB 2) generate F's share. Adjudicated
one line each, at the level F's DEPENDS fields touch them:
1. `{GRTJA, GRTJB}` mutual cluster: GRTJA cites JB faces (JB-VTX/JB-DEV) and GRTJB cites
   JA-RES back (its DEV(iii)(RES) layer "is JA-RES at read level") — NOT a cycle at unit
   level: the citations land on disjoint units (`.08` vs `.89–.105`), same shape as the
   checker's HE6↔HE6R1 finding; F's rows keep them disjoint (F.19 vs F.22).
2. GRTJA fences (N-1 imports, JA-BOX-1..5): F consumes no fenced material — F.19/F.20
   transcribe the two preserved rows only; the JA-BOX-1 refuted display is fenced
   structurally (F.19's abscissa-linear exponent).
3. WELDMASTER's one-perimeter fence (WM-FENCE): every F edge into `EFF.WELDMASTER.25`
   carries the F-4 scoping in its evidence column ("fixed-data criterion, no freedom") —
   the spec's own instruction "A DAG edge into WM-FENCE must carry this scoping," executed.
4. GRTW2's dependency-line fence (`EFF.GRTW2.40`) and LIFTCORNER's fences (`.16/.17/.45/
   .71`): F touches neither notes' fenced imports; the two LIFTCORNER units F cites
   (`.62/.72`) are scope records, and their D-F1/D-F2 direction rulings are exactly fence-
   respecting (consumption declared by the consumer).
5. GRTJC's tautology fence (`.83`) and cyclic fence (`.93`): honoured by omission — no F
   node states the fenced forms; F.10's JC-BOX-5 scope note is the one contact point,
   handled in the node.

---

## 12. LEANSPEC STUB LIST (stage 0e)

> **STATUS: EXECUTED 2026-08-16** *[added: A-W.1]*. `leanspec/Leanspec/ChapF.lean` (commits
> `1905bb6b` / `3212150a`) is green: **41 signed declarations** (8 `structure` + 18 `def` real
> bodies + 15 `axiom` stubs at the exact signed types), F.08's 5 below-the-line instances, both §10
> gates EXECUTED at `q = 2` AND `q = 3` (50 `example`s + 6 in-instance `decide`s), zero `sorry`,
> zero `native_decide`, `autoImplicit`/`relaxedAutoImplicit` off, and three `Iff.rfl` PINS on the
> Display-A carriers' unfoldings (`JD0Box2`, `GenhnBox2`, `W1Transport`) — a standing gate that the
> carriers chapter I consumes cannot drift. Six defects (F-D1…F-D6) came back and are repaired in
> AMENDMENT A-W.1. The lists below are corrected to what landed; the counts in §2's declaration
> census are the authority.

Per GC-6.6: file `leanspec/Leanspec/ChapF.lean`, wrapped in `namespace LeanspecF` (never
re-declaring contract names in `Uniformity.*`; ChapG's retire-to-examples is the recorded
alternative). Gate order (CHAP-H §15 / GC-6.6(c)): (a) elaborate the FRAGILE signatures
first; (b) land the `def` bodies real; (c) EXECUTE the §10 numeric gates at `q = 2` AND
`q = 3` against this file's expected values; (d) only then sign the `axiom` stubs.

**(a) Fragile-signature list (elaborate first, in this order):**
1. F.08 `TwistedAlgebra` (the `Type _` wrapper + the twisted `Mul`/`AddCommGroup`/`Module`
   instances — instance leakage onto plain `ZMod E → K` is the failure mode to catch) **and
   F-D3's `One`/`Pow` pair, whose `One` body must invert in `Kˣ`** *[added: A-W.1/F-D3 — the
   committed list's four helpers do not carry F.10's `^`]*;
2. F.10 (`Module.finrank` through the def wrapper; the `single`/`•` spelling — the
   `single 0 1` normalization fence is a statement fence, not adjustable);
3. F.28 (`structure … : Prop where` — the Prop-valued structure syntax with three index
   types as parameters);
4. F.26 (`DmultW`'s quantifier order: `∃ ω` BETWEEN the line pair and `(f, g)` — a
   type-checked commute of the quantifiers is a blueprint defect, return BLOCKED);
5. F.29/F.30's concrete field instances — **RESOLVED: the table-built `F4`/`F9` of §10 are the
   form of record** *[repaired: A-W.1/F-D6]*. ~~`F₄ := AdjoinRoot (X² + X + 1)`,
   `F₉ := AdjoinRoot (X² + 1)`~~ carry no `DecidableEq`/`Fintype` at all, so the pre-authorized
   private table-built fields fired (`ZMod 2 × ZMod 2` with `θ² = θ + 1`; `ZMod 3 × ZMod 3` with
   `θ² = −1`; `CommRing` by `decide`, `Field` on `x⁻¹ = x^(q−2)`); `native_decide` FORBIDDEN and
   absent. Also owed at any `F₅` example: `instance : Fact (Nat.Prime 5)` (F-D5(v));
6. F.15 (the multiplied-form `δ_j` normalization — do not "simplify" to a division tower);
7. F.03 (`resTwist`'s `noncomputable` marker vs the gate's need for evaluable instances —
   gates use `eval`-level checks, not `decide` on `resTwist` itself, if it resists).

**(b) Def bodies (land real, topological order per the TSV):** F.01, F.07, F.14, F.05,
F.08, F.18 (def half), F.20, F.21 (needs F.03's def only), F.22, F.25 (def half), F.04,
F.11, F.12, F.26, F.24, F.17, F.27, F.28 — **plus the three the committed list dropped**
*[repaired: A-W.1 census correction, found by diffing this list against the 26 real bodies the
gate landed]*: **F.02's def half** (`slotScaleEquiv`, whose two `simp [slotScale]` proof fields
elaborate as signed), **F.03's def half** (`resTwist`, `noncomputable` — F.03 appeared only in (d),
and F.21's parenthetical "needs F.03's def only" was the sole trace of it), and **F.19**
(`JAResLaw`, absent from every §12 list). Total real bodies: **26** = 8 `structure` + 18 `def`
(§2's declaration census).

**(c) Numeric gates:** F.29, F.30 — all `decide`/`norm_num` **in §10's gate-form rider
spellings** *[repaired: A-W.1/F-D5]*; expected values pinned in this file (§10): card 16/9,
finrank 2, `v² = ζ•single 0 1` with ζ = ω resp. 2, the F₅ fence witness (`orderOf 2 = 4` as the
power certificate, `χ₁ = 3` as the units inverse + pair product), `ξ₂ = θ₂⁻¹ = 4` at F₅, the F₂
triviality control, the NONCHAR shift control, the μ₂(F₅) torsor witness, the two `jbShear`
images, and the involution/non-involution separator pair. **Standing rule:** a leg that lands in
the rider's substituted form has NOT weakened the gate; a leg that lands with a different VALUE is
stop-the-line.

**(d) Axiom stubs (15 theorem-shaped rows over 11 nodes):** F.02 (×1, `card_image_slotScale`),
F.03 (×3), F.06, F.09, F.10 (×2 — the split-mandated pair), F.13, F.15, F.16, F.18 (lemma half),
F.23 (×2), F.25 (lemma half) *[repaired: A-W.1 census correction — the multiplicities are now
displayed; the committed list read as 11 stubs]*. **Not stubbed, and not owed a stub:** F.22's
`jbShear_injective` (added at A-W.1/F-D4 after the gate ran, so the 0e diff for F.22 will show one
extra declaration at landing — expected, recorded here so it is not read as drift).

**BLOCKED-UNTIL-RESOLUTION (do NOT stub as provable):** the two GC-13 instance obligations
— F.17's C-side `SigmaLedgerLaw` discharge (`EFF.SIGMALAW.03 [supplied-by: chapter C]`) and
F.24's M4 instance (`EFF.GRTW2.29 [supplied-by: chapter C]`). The carrier DECLARATIONS
(F.17, F.24) elaborate and land in (b); only their instance nodes wait for the
orchestrator's resolution pass. F.11/F.12's site instances likewise wait on H/C landings but
create no stub obligation (they are type-parameterized). *[A-W.1: confirmed at the gate — both
carriers elaborate, neither instance is stubbed.]*

**RULES FOR THE STUB-LANDING AGENT (this chapter's, after the 0e gate)** *[added: A-W.1]*:

1. **No `Σ`, `Π` or `λ` in any identifier** (F-D1/F-D2). At Lean 4.31 `Σ` and `Π` are excluded
   from `isLetterLike` and `λ` is the lambda keyword; the ASCII spellings are the contract:
   `sigmaMap`, `hSigma`, `hSigmax`, `hSigmarho`, and `l` (or `lam`/`mu` in a line pair) for
   bound indices. Greek stays in prose and display mathematics. A landing agent that finds a
   Greek-token identifier anywhere in a chapter-F SIGNATURE has found a blueprint defect, not a
   licence to invent a spelling: the four cured names above are the sanctioned list.
2. **Inverses that a gate must reduce are taken in `Kˣ`** (F-D3/F-D5(iv)) — `Inv (ZMod n)` is
   well-founded-recursive and does not kernel-reduce.
3. **Gate legs land in §10's rider forms** (F-D5); `native_decide` is forbidden anywhere in the
   chapter (F-D6); the table-built `F4`/`F9` are the gate's fields.
4. **`One`/`Pow` on `TwistedAlgebra` are part of F.08's contract** (F-D3), and `Pow` must be
   `npowRec` — a later `Monoid` instance must agree, or F.10(b)'s statement moves.

---

## 13. UNIT-DISPOSITION CENSUS (all 567 SERIES units over 7 notes, + the 5 consumed JD0
units) + TEETH SUMMARY (GC-8)

### 13.1 Disposition vocabulary

Per GC-10/GC-8 (the CHAP-E §13 vocabulary): **NODE(→F.xx)** = transcribed into the named
node(s); **INSTANCE-ROW(→F.xx)** = supplier/stack content entered as a grade-annotated row
on a carrier's statement (citation form fixed at the node); **RECORDED** = process/
acceptance/round/pin content, or mathematics whose only consumers are out-of-cone (§3) —
preserved by the byte-frozen EFF spec, quoted at a constraining node where it constrains;
**FENCE-HONOURED** = a negative claim enforced structurally; **OUT(§3.n)** = the unit's
content is the out-of-cone package of §3 row n; **DECISION** = consumed by a D-F ruling.

### 13.2 EFF-GRTJA (36 units)

| units | disposition |
|---|---|
| .01–.03 | RECORDED (unit block, scope, base definitions — consumed inside GRTJA's own proofs) |
| .04 | RECORDED (JA-PIN: print-pin citations; supplier evidence for the class pin — no cone consumer distinct from the sites) |
| .05/.06 | RECORDED (JA-VAL preserved row; JA-EPS superseded by C2-1 — both site-internal) |
| .07 | NODE→F.20 (JA-GRID at C2-4's pinned scope) |
| .08 | NODE→F.19 (JA-RES) + F.03/F.04 provenance |
| .09 | RECORDED (JA-VDIND: forward proved at source, converse positively refuted by PE8's constructed escapes — quoted at F.19's gloss) |
| .10 | RECORDED (JA-MIN: "nothing downstream in this note consumes JA-MIN" — its own blast-radius clause) |
| .11 | NODE→F.21 (the (ξ,w) orbit action; chamber half OUT(§3.10)) |
| .12–.14 | RECORDED (imports at pinned commits) |
| .15–.18 | FENCE-HONOURED (JA-BOX-1's refuted slot-independent form fenced by F.19's abscissa-linear exponent; boxes 2–5 quoted where they scope F.19) |
| .19–.23 | RECORDED (machine brackets, run records, scope records) |
| .24 | RECORDED (the acceptance/grade record — the arc-1/2 grade consumed at F.04/F.19's annotations; honesty F-7) |
| .25–.36 | RECORDED (changes-records; .31's CRITICAL cure and .34's C2-4 scope-pin folded into F.20's statement) |

**GRTJA check:** 36 units — 3 NODE-mapped, 33 RECORDED/FENCE.

### 13.3 EFF-GRTJB (173 SERIES units)

| units | disposition |
|---|---|
| .01–.02 | RECORDED (scope records) |
| .03–.10 | RECORDED (SERIES S-STATUS, 8 members — grade chronology) |
| .11–.19 | RECORDED (definitions/hypotheses feeding the conditionality matrix) |
| .20 | RECORDED (THE CONDITIONALITY MATRIX — its rows 4/12 are §3 rows 1/3's mass; its JB-DEV/VTX rows are F.22's provenance) |
| .21–.30 | RECORDED (instrument/scope records; ⟨n1⟩–⟨n5⟩) |
| .31–.37 | RECORDED (grade surfaces) |
| .38–.42 | RECORDED (.39 CITE-SCOPE fence — cite hygiene preserved at the spec) |
| .43–.80 | RECORDED (repair rounds r1–r8; .77 the `u ≥ 0` chain terminal → OUT(§3.1/§3.3) via HYP.21/75) |
| .81–.88 | .86 NODE→F.22 (frames + shear); rest RECORDED |
| .89–.98 | .89 NODE→F.22 (JB-DEV(i)); .90–.95 INSTANCE-ROW→F.22 (clauses (ii)/(iii) at their per-layer perimeters; the (VD-m) reading fence .93 quoted); .96–.98 RECORDED |
| .99 | RECORDED (JB-AFF) |
| .100–.108 | .101/.102 NODE→F.22 (JB-VTX (a)/(b)); .103–.105 INSTANCE-ROW→F.22 ((c) at E-3's corrected run datum, (d) min ties, (e) window clause); .100/.106–.108 RECORDED |
| .109–.118 | RECORDED (JB-TREE: consumed by no cone note — J-D0's L4 leg is VTX/DEV only, HYP.75 re-verified) |
| .119–.133 | RECORDED (§5: the `u ≥ 0` lattice discharge .121/.122 and JB-CREAD/JB-EPS — their cone-facing mass is OUT(§3.1/§3.3); .126's unconditional ε-collapse noted at F.22's gloss) |
| .134–.140 | FENCE-HONOURED/RECORDED (JB-BOX-1..6; BOX-2's inherited-conditionality quantification quoted at F.22) |
| .141–.163 | RECORDED (sealed batteries, censuses, walker records) |
| .164 | RECORDED (SERIES post-freeze arc, 8 members) |
| .165 | RECORDED (ACCEPTED 2/2 — the grade consumed at F.22) |
| .166–.173 | RECORDED (fold/certifier annexes; .172 E-3 folded into F.22's statement; .173 the off-perimeter NOT-SUPPLIED reading preserved) |

**GRTJB check:** 173 units — 4 NODE-mapped, ~9 INSTANCE-ROW, 160 RECORDED/FENCE/OUT.

### 13.4 EFF-GRTJC (132 SERIES units)

| units | disposition |
|---|---|
| .01–.39 | RECORDED (instruments, batteries, S-STATUS series, repair rounds r1–r6; .31/.36's corrections folded where their terminals land below) |
| .40–.46 | RECORDED (conditionality stack head; (IN-1)/(IN-2)/(IN-4)/(IN-5) hypothesis rows — stack provenance on F.11) |
| .43 | NODE→F.26 ((IN-3), the FGMN CITE-SCOPE home — gate-(b)) |
| .47–.53 | RECORDED (harness definitions — the out-of-cone build declined, §3 preamble) |
| .54 | INSTANCE-ROW→F.11 (THEOREM W-6, stack citation) |
| .55–.61 | RECORDED (JC-DOM/JC-GAUGE/JC-PER/JC-FIB/JC-ANCHMON/JC-SCAL/JC-SPAN — W-9's proof machinery, carried by the stack citation) |
| .62/.63 | INSTANCE-ROW→F.11 (JC-LOAD, JC-PSIKER(iii) — the wild-decidedness warrant J-D0's BOX-6 routes) |
| .64–.68 | RECORDED ((COORD-B) repair layer) |
| .69 | NODE→F.26 ((DMULT) two tiers; (DMULT-s) OUT(§3.5)) + F.12 (the transport shape) |
| .70–.76 | RECORDED (.71 (MULT-B), .70 (COORD-B)(2) — ride (DMULT-w), carried via F.26) |
| .77 | INSTANCE-ROW→F.07 (JC-CARRY-m: the y-degree tie `deg A(a,b) = δ(a,b)` — instance content at the consuming site) |
| .78–.83 | RECORDED (.79 the J-B↔J-C germ interface; .83 tautology fence honoured by omission) |
| .84/.85 | INSTANCE-ROW→F.11 (THEOREM W-8 + its Annex-#4-cured proof — stack citation) |
| .86–.88 | RECORDED |
| .89 | NODE→F.07/F.09/F.10/F.11 (COROLLARY W-9, the special-care unit; clause (iv) NOT consumed — structurally absent from F.11) |
| .90 | NODE→F.09 (the proofs' associativity reading; kind inversion disclosed at F.07) |
| .91 | NODE→F.10 (JC-F1's power basis/cyclic presentation; JC-BOX-5's REVIEW-OWED presentation fence honoured by abstract-isomorphism scope) |
| .92–.104 | RECORDED/FENCE (JC-F2; (CYC)/JC-CYC; the eight boxes — JC-BOX-3's blast radius quoted at F.26) |
| .105–.121 | RECORDED (preregistrations, run records, grade tables; .121's named-consumer fence checked against F's consumption: F takes W-9 + (DMULT-w) + stack citations only) |
| .122–.132 | RECORDED (acceptance + post-acceptance annexes; the three survival clauses quoted at F.11; .125/.129 NODE→F.26 provenance) |

**GRTJC check:** 132 units — 7 NODE-mapped (.43, .69, .89, .90, .91, .125, .129), 6
INSTANCE-ROW, 119 RECORDED/FENCE/OUT.

### 13.5 EFF-GRTW2 (60 units)

| units | disposition |
|---|---|
| .01–.03 | RECORDED (changes-records, grade-arc series) |
| .04–.07 | RECORDED (the Object + three clauses; grade cap; literature fence; machine bracket — clause 3 is D-F1's dependency target via .20) |
| .08–.13 | RECORDED (.11 W2-L0, .12 W2-L1/TH-BASE, .13 W2-L2 — GRTW2-internal suppliers) |
| .14 | INSTANCE-ROW→F.19 (LEMMA W2-L3 = (VD-1): the m = 2 unconditional leg) |
| .15–.18 | RECORDED (.17 (C-coll) perimeter → OUT(§3.7); .18 W2-C2 value law → OUT(§3.4) mass) |
| .19 | NODE→F.21 (the (ξ,w) closed form) |
| .20 | DECISION D-F1 (content RECORDED: the covariance-generated-by-print-constant identification; the Σ-LAW's independent re-derivation noted) |
| .21 | NODE→F.21 (the non-uniqueness/support-stabilizer gloss + the invisible-twist genre) |
| .22–.28 | RECORDED (.23 W2-BOX-1 boundary witness; .24/.25 W2-C1 legs; .26 review-owed parametrization; .27/.28 transported type + mechanism) |
| .29 | GC-13→chapter C at F.24 (THEOREM W2-C3: M4's fenced scope) |
| .30–.32 | RECORDED (the honest re-scope; the converse's boundary counter-instance) |
| .33 | OUT(§3.10) (W2-OPEN-2/OPEN-2a — narrowed by the Σ-LAW annex; residue value-layer) |
| .34 | RECORDED (four-route derivability adjudication) |
| .35 | DECISION D-F2 + OUT(§3.4) (W2-OPEN-1 — the open value layer) |
| .36–.45 | RECORDED (W2-T3E; tables; round records; footer) |
| .46 | RECORDED (acceptance box — ACCEPTED at fenced scope; consumed at F.21/F.24's grade annotations) |
| .47–.49 | RECORDED (annex header; fold-carry closure; OPEN-2a narrowing) |
| .50 | RECORDED (ANNEX 3: Σ-LAW PROVED — the consumption record; the SIGMALAW units themselves govern §6) |
| .51–.60 | RECORDED (annex corrections, E5 adjudication; .56/.58's corrected theorems are value-layer/out-of-cone mass) |

**GRTW2 check:** 60 units — 2 NODE-mapped, 1 INSTANCE-ROW, 2 DECISION-consumed, 1 GC-13
placeholder, 54 RECORDED/OUT.

### 13.6 EFF-WELDMASTER (30 units)

| units | disposition |
|---|---|
| .01–.02 | RECORDED (title superseded by .22; convention) |
| .03 | RECORDED (the frozen "ONE transport" S1 theorem — SUPERSEDED, not transcribed; F.24 carries the annex form) |
| .04–.21 | RECORDED (definitions, faces M0–M4's frozen displays, fences, tables, acceptance — consumed only through the .22 package form; .10 WM-CLASS noted at F.25's blast-radius gloss) |
| .22 | NODE→F.24 (WELD-M-PKG, charge unit 1) |
| .23 | NODE→F.25 (the torsor correction, charge-adjacent) |
| .24 | RECORDED (F-3 RESOLVED-ALREADY) |
| .25 | NODE→F.23 (WM-FENCE criterion, charge unit 2; the PERIM-μ LAW stays OUT(§3.9)) |
| .26–.30 | RECORDED (remaining annexes/records) |

**WELDMASTER check:** 30 units — 3 NODE-mapped, 27 RECORDED.

### 13.7 EFF-LIFTCORNER (118 units)

| units | disposition |
|---|---|
| .01–.61 | RECORDED (conventions, machine-leg/repair-arc series, preregistrations, derivations, COR 1/COR 2 content — the ITER-LAW-LIFT discharge is ITERLAWN-facing; its interface conjunct is chapter I's HYP.125, and no F node states ITER-LAW content) |
| .62 | DECISION D-F2 + RECORDED (the withdrawn COR 2 = W2-OPEN-1 identification; obligations (a)/(b) STILL OWED at HEAD — value-layer, out-of-cone) |
| .63–.71 | RECORDED (CHAIN-P with AC-1/AC-4/AC-5 terminal; grade boxes; fences) |
| .72 | DECISION D-F1 + RECORDED (the W-2 consumption census; the "honest decoupling fact" — the COR 1 chain is W-2-free — quoted here as the census's load-bearing line) |
| .73–.77 | RECORDED (S5 consequence display with its three supersessions; the (RM-m) m ≥ 2 OPEN residual preserved) |
| .78–.118 | RECORDED (acceptance-box series, post-acceptance arc, certifier annexes — LIFTCORNER's ACCEPTED 2/2 grade is consumed at F.04's provenance as GRTW2's "corner cap") |

**LIFTCORNER check:** 118 units — 0 NODE-mapped, 2 DECISION-consumed, 116 RECORDED.

### 13.8 EFF-SIGMALAW (18 units)

| units | disposition |
|---|---|
| .01 | RECORDED (unit block; CERTIFIED grade → F.17) |
| .02 | NODE→F.17/F.18 (the corrected-map headline + the ξ₂ = θ₂⁻¹ audit) |
| .03 | NODE→F.18 + GC-13→C at F.17 (the §3.4 objects) |
| .04 | NODE→F.17 (SL-L1's gap clause; the recursions are C-side instance content) |
| .05 | NODE→F.14/F.17 (THEOREM SL-1) |
| .06 | NODE→F.17 (SL-L2 gauge-ratio law — instance content, simultaneous-induction note preserved) |
| .07 | NODE→F.17 ((EC-q), the hostile-pass-derived automorphism law) |
| .08 | NODE→F.15 (SL-C1) |
| .09 | NODE→F.16 (SL-C2; converse N-1 stays open, stated nowhere) |
| .10 | RECORDED (sealed battery; the E10 #4 leak-free corrections noted) |
| .11 | RECORDED (ACCEPTED 2/2, six commit pins verified — grade at F.17) |
| .12–.18 | RECORDED (E10 findings — #2's ξ₁ := 1 at F.18, #5's derivation at F.15; changes-records; ledger row) |

**SIGMALAW check:** 18 units — 8 NODE-mapped, 10 RECORDED.

### 13.9 EFF-JD0 (5 units consumed out-of-chapter, per BRIEF F product (1))

`.05` NODE→F.01/F.03 · `.06` NODE→F.02 (mechanism shadow only) · `.22` NODE→F.04/F.06
(BOX-2 verbatim; BOX-5) · `.24` RECORDED (consumers; the fence-bookkeeping clause quoted at
§3 rows 6–9) · `.25` RECORDED (the supplier stack — F.04's provenance table). The rest of
EFF-JD0 is chapter G's cut (G closed without it; only these five units are consumed here,
each named).

### 13.10 Census totals and the compression statement

567 SERIES units + 5 JD0 units consumed: **30 NODE-mapped units → 30 nodes; ~17
INSTANCE-ROW; 2 GC-13 placeholders; 4 DECISION-consumed; everything else RECORDED /
FENCE-HONOURED / OUT(§3)** — the 538-DAG-node chapter compresses to 30 nodes because the
capstone consumes exactly two weld faces plus their supplier interfaces, and the census
above accounts for every unit by ID range. (CHAP-E's 242→68 was the model; F's 567→30 is
steeper because the weld-face audit had already signed 9 of 10 chartered rows out.)

### 13.11 TEETH disposition summary (GC-8 table)

| disposition | count | items |
|---|---|---|
| **Lean theorem** | 13 nodes | F.02, F.03, F.06, F.09, F.10, F.13, F.15, F.16, F.18, F.23, F.25 + the executed gates F.29, F.30 |
| **executable regression retained** | 2 + 2 | NEW: `verification/chapF_gate_twisted.py`, `verification/chapF_gate_chars.py` (mirrors of F.29/F.30, created at stub stage (c)); RETAINED IN PLACE: `verification/openmath/jd0_checks.py` (the sealed J-D0 battery, 68,523/0) and `verification/openmath/sigmalaw_checks.py` (6,970 samples) — already in the tree, named here per GC-8 |
| **signed non-applicability / vacuity disclosures** | 9 rows | (1) `JD0-BOX-2` carried, HYP.74 (F.04); (2) `GENHN-BOX-2` carried, HYP.148 (F.11); (3) `W-1` MATH, HYP.139 (F.12); (4) F.17's C-side discharge pending (GC-13); (5) the GRTJA arc-1/2 grade cap on F.19/F.20 and F.04's residual leg (honesty F-7); (6) `(DMULT-w)` "carries no separate leg" — its discharge is the gate-(b) FGMN cite (F.26); (7) F.06's F₂ vacuity — disclosed AND proved (the strongest form); (8) F.28's obligations block (a hypothesis block has no teeth by design); (9) the involution-coincidence disclosure (SL-INVREC 218/218) carried at F.17/F.30 |
| **out-of-cone (no disposition owed)** | the §3 table | 13 rows, each with its BLOCKED string — per GC-8's rider (i), never silently promoted |

**Sanity check (H.09's rule):** the fields with no teeth are exactly the capstone's
conditionality — here `JD0-BOX-2`, `GENHN-BOX-2 (n ≥ 6)`, `W-1`, the `AllOInterfaces[W/J,
J-D0]` generality rows, and the two GC-13 instance obligations — precisely Display A's
surviving weld conjuncts plus the cross-chapter supply seams. Reconciles with §3's
Display-A footprint check. ✓

---

## 14. FLAGGED FOR THE CODEX CROSS-READ (and for the orchestrator)

1. **D-F1/D-F2** — the SCC direction principle ("a consumption/withdrawal record depends on
   the unit it consumes; an acknowledgment is provenance"). Attack the principle and both
   applications; the reverse-edge re-classing is an orchestrator item (§11).
2. **The 30-node count vs BRIEF F's 50–70 estimate** — §2's justification + §13's census.
   Verify no reachable clause was dropped: the candidates to re-check are GRTJB's JB-TREE
   faces (disposed RECORDED on HYP.75's re-verified geography) and GRTJC's harness
   definition layer (.47–.53, disposed RECORDED as declined out-of-cone build).
3. **F.07's kind inversion** (W-9's conclusions carried as structure FIELDS) — the
   chapter's central faithfulness call; check the FAITHFULNESS note's claim that
   instantiation preserves ledger strength.
4. **DECISION D-F3** (GC-4 satisfied by consuming E's `ladderSigma`; no σ-valued output in
   SIGMALAW) — re-read `EFF-SIGMALAW.md` for any σ-valued output this composition missed.
5. **F.04's residual-leg placement** — `JD0Box2` carries the slot + ledger legs; the
   residual leg rides F.19 (JA-RES at arc 1/2) so the grade cap stays visible. Check
   chapter I's block wires all three (F.28 carries F.04 only; F.19 reaches I through the
   §9 annotations).
6. **F.10's `single 0 1` normalization fence** (the unit of the twisted algebra is
   `single 0 (c 0 0)⁻¹`, not `single 0 1`) — verify the power-basis statement's `•`-form is
   the right contract and the stub stage does not normalize `cc`. *[A-W.1/F-D3: PARTLY ANSWERED —
   the gate did not normalize `cc`, the `•`-form elaborates and its `E = 2` value was reproduced at
   both primes, and the unit is now a signed `One` instance (inverse in `Kˣ`). What is still owed
   to the cross-read: whether the unit claim belongs in F.09's SIGNATURE rather than only in its
   prose.]*
7. **F.26's quantifier order** (`∃ ω` between the line pair and `(f, g)`) — the spec's own
   trap; also verify the gate-(b) cite tag (`FGMN Thm 4.2` via `(IN-3)`) is the right
   citation target at HEAD (Annex #6 re-based the derivation).
8. **The gate field constructions** (F₄/F₉ via `AdjoinRoot`; table fallback;
   `native_decide` forbidden) — and the involution/`F₂` negative controls' adequacy against
   honesty F-9. *[A-W.1/F-D6: ANSWERED on the construction half — `AdjoinRoot` carries no
   `DecidableEq`/`Fintype`, the pre-authorized table fallback fired, `native_decide` is absent, and
   the executed controls are the `F₂` unit-group triviality, the NONCHAR additive shift, and an
   involution/non-involution separator pair at `F₃`/`F₄`/`F₉`. The adequacy JUDGEMENT (are these the
   right controls?) is still the cross-read's.]*
9. **§8's pre-authorized WELD-ZERO amendment path** — verify it does not overstep the 0b
   fold's authority (the amendment fires only after the ledger books the arc).
10. **ORCHESTRATOR + C composer: the two `BP.C.*` SCCs at HEAD** (`{BP.C.56, .84, .85,
    .87}`, `{BP.C.99, .100, .102, .104}`) — found during F's dag_check run; they FAIL the
    checker and are not F's. F's own rows introduce zero new SCCs (verified by SCC-list
    diff, §11).
11. **HYP.126/HYP.129 "supplied structurally"** (F.28's annotation) — check chapter I's
    brief expects the generality rows to stay I-side (F quantifies over every finite `K`;
    the conjunct fields remain I's).
12. **GC-12 confirmation** — every F-cited EFF ID verified to exist contiguous in
    `DAG_NODES.tsv` at HEAD (§11); no evidence-column remap owed for F.
13. **F.03's `resTwist` normalization arithmetic** (the `C (ξ^deg)⁻¹` factor vs the
    source's `ξ^{−deg R}·R(ξ·y)`; monic-form death of the overall unit) — re-derive the
    leading-coefficient computation independently.
14. **The §2 kind census and file figure** (8/8/2/1/9/2 = 30; ≈ 31–33 files after the F.10
    split) — recount at stub time. *[A-W.1: DONE. The node kinds recount correctly (30); the
    DECLARATION census landed at **41** (8 structures + 18 defs + 15 theorem-shaped rows) and is now
    displayed at §2, and §12's lists were corrected against it — three real bodies (F.02's
    `slotScaleEquiv`, F.03's `resTwist`, F.19's `JAResLaw`) had been dropped from §12(b). File
    figure unchanged.]*
15. **ORCHESTRATOR — the E-side wiring, from F's gate** *[added: A-W.1, cross-chapter note]*:
    (a) F.17's DEPENDS is upgraded to the GC-13(a) landed names
    `Uniformity.Density.Ladder.ladderSigma` / `…ladderSigma_degree` (E.45/E.46 have landed);
    (b) `ladderSigma_degree` is outside the `Uniformity` root import graph at HEAD (`ChapE.lean`
    rolls up E01/E07/E25/E26/E34/E45 only; E46 is imported only by E47) — a known roll-up item,
    the orchestrator's, not F's, and harmless to F because D-F3 puts no E name in an F signature.

---

## FINAL STATE

All 30 nodes composed (§§4–10); the out-of-cone census (§3) disposes the value package row
by row; closing sections §§11–14 complete; `spec/DAG_BLUEPRINT_F.tsv` emitted (114 rows,
ACYCLIC, 6 layers, widths 12/8/6/1/2/1, critical path 5) and verified to add zero SCCs at
HEAD; the two GRTW2↔LIFTCORNER mutual-recon SCCs are DECIDED (D-F1/D-F2); WELD-ZERO status
of record: clean-pass 1 of 2, pass 2 Fable-max IN FLIGHT, nothing consumed from it.
CODEX CROSS-READ OWED (§14 is the queue).

**Stage-0e stub gate: RUN AND GREEN (2026-08-16)** *[added: A-W.1]* — 41 declarations, both §10
gates executed at `q = 2` AND `q = 3`, three Display-A carrier PINS, six defects F-D1…F-D6
repaired here by AMENDMENT A-W.1 (below).

<!-- RESUME: CHAPTER COMPLETE. Remaining external actions: (i) orchestrator dag_build re-run
(merges DAG_BLUEPRINT_F.tsv; re-classes the two adjudicated reverse edges; books the BP.C
SCC flag); (ii) cross-read per §14; (iii) leanspec stub stage per §12 — DONE at stage 0e
(2026-08-16, commits 1905bb6b/3212150a); its six defects are repaired in AMENDMENT A-W.1, and the
orchestrator still owes `import Leanspec.ChapF` in `leanspec/Leanspec.lean`; (iv) the §8 WELD-ZERO
amendment fires only after the ledger books the arc. -->

## AMENDMENT A-W.1 (2026-08-16, dated append) — THE STAGE-0e STUB-GATE DEFECT LIST, REPAIRED

**Provenance.** The chapter-F stub gate `leanspec/Leanspec/ChapF.lean` (commits `1905bb6b`
stage (a)/(b)/(d) + `3212150a` stage (c) and the carrier pins; `lake build Leanspec.ChapF` green:
41 signed declarations, 50 executed gate `example`s + 6 in-instance `decide`s at `q = 2` AND
`q = 3`, zero `sorry`, zero `native_decide`) recorded **six defects, F-D1…F-D6** in its header. Per
§12 / CHAP-H §15 rule 5, elaboration-level defects are cured minimally stub-side and repaired
blueprint-side here; **the stub's cures are ground truth for this amendment** — where the two could
differ, the landed spelling won.

**Series name.** `A-W.<n>`, "W" for weld — declared with its reason in the header banner
(`A-F.<n>` is chapter B's finisher series; a second `A-F.1` would collide in the fleet's grep).

**Landing provenance (recorded because it is not the usual one).** A-W.1's text landed in two
commits, not one: the body was swept into a concurrent unit's whole-tree commit `f97b81d9`
("BP:H.108: TEETH prose …") while this unit was composing its own commit message, and the commit
carrying the intended `BP-W: A-W.1 …` message is therefore this provenance note. Nothing was lost
and nothing else was touched; recorded so a later `git log -- blueprint/CHAP-F_weld_layer.md`
reader does not conclude the amendment was authored by the chapter-H unit.

**Convention of this block** (CHAP-E's A-E.1 convention, itself CHAP-H's A-H.1): node text IS
repaired in place, each repaired passage tagged `[repaired: A-W.1/F-D<n>]` or `[added: …]`;
superseded text stays visible as a strikethrough or a quoted original; this block records, per
defect, the finding, the defective ORIGINAL, the repair and the evidence. Nothing is deleted.

**Where the two files now differ.** At DECLARATION level, in exactly one place: F.22's
`jbShear_injective`, signed here at F-D4 *after* the gate ran, has no stub. Every identifier and
every gate spelling now agrees. Remaining differences are the stub's own declared conventions, not
drift: the stub drops the `namespace Uniformity.Density.Weld` headers (it wraps everything in
`LeanspecF`), abbreviates some docstrings, and line-breaks a few signatures differently — the
blueprint additionally carries F-D4/F-D5/F-D6 as *rules* where the stub carries them as *executed
code*.

### A-W.1/F-D1 — `Σmap` / `hΣ` / `hΣx` / `hΣρ` ARE NOT LEGAL LEAN IDENTIFIERS (hard parse error)

**The finding.** At the Lean 4.31 pin `Σ` (U+03A3) is explicitly EXCLUDED from `isLetterLike` (as
is `Π`) because it is the Sigma-type token. The gate's two probes:
`structure P (K) [Field K] where Σmap : K → K` → *"unexpected token 'Σ'; expected command"*;
`(hΣx : …)` → *"unexpected token 'Σ'; expected ')'"*. Five identifiers were affected, over five
nodes. *Class: illegal identifier — the same family as CHAP-E's E-D3 (`hλ`).*

**The defective originals** (committed SIGNATUREs, preserved):

    structure LedgerJunction (K : Type*) [Field K] (ι α : Type*) where
      Σmap : K → K                                              -- F.14, a FIELD
      …
      hledger : ∀ j a, Prnt j a = (u j : K) * Σmap (read j a)

    (hΣx : J.Σmap (J.read j C) ≠ 0) (hΣρ : J.Σmap (ρ : K) ≠ 0)  -- F.15, two BINDERS

    {Σmap : K → K} (hinj : Function.Injective Σmap) …            -- F.16, a BINDER

    Function.Injective J.Σmap ∧ J.Σmap 1 = 1 ∧ …                 -- F.17, three USES

    hΣ : SigmaLedgerLaw J                                        -- F.27, a FIELD

**The repair.** `Σmap → sigmaMap`, `hΣ → hSigma`, `hΣx → hSigmax`, `hΣρ → hSigmarho`, threaded at
F.14 (field + `hledger`), F.15 (signature + STATEMENT prose + PROOF), F.16 (binder + PROOF), F.17
(the three projections in `SigmaLedgerLaw`'s body) and F.27 (field + FAITHFULNESS).

**What is and is not contract content.** Two of the five are FIELD names —
`LedgerJunction.sigmaMap` and `WeldSupply.hSigma` — and field names are part of the type: every
consumer's projection changes, and **the signed spellings cannot be landed at all**. The other
three are binder names, which carry no type content (they matter only to named-argument call
sites). The source's `Σ` is untouched in prose and in the `(Σ-LEDGER)` display.

**Standing rule** (now §12's rule 1): no chapter-F identifier may carry `Σ`, `Π` or `λ`.

### A-W.1/F-D2 — F.12's `∀ λ, …` IS A HARD PARSE ERROR, AND THE CHAPTER WAS INTERNALLY INCONSISTENT

**The finding.** `W1Transport`'s bound variable was spelled `λ`, the lambda keyword:
*"unexpected token 'λ'; expected '(', '[', '_', '{', '⦃' or identifier"*. The chapter's own F.26
avoids the trap (`∀ lam mu : Λ`), so the two nodes disagreed. *Class: illegal identifier.*

**The defective original:** `∃ c : ι → Kˣ, ∀ λ, Rharness λ = (c λ : K) * RGMN λ`.

**The repair, and the convention choice recorded.** `∀ l` — the gate's executed form — with a
chapter-wide binder rule stated at F.12: Greek tokens never appear in identifiers; **`l`** for a
bare abstract index (F.12's `ι` is exactly that), **`lam`/`mu`** where the binders transliterate a
λ/μ *pair* from the source (F.26, which stays byte-unchanged). Both are legal, binder names are not
part of the type, so **the Display-A sub-residue carrier is unaffected** and a landing agent may
spell F.12's binder `lam` without being BLOCKED. The alternative — unifying on `lam` everywhere —
was rejected only because it would move a form the gate already executed and pinned by `Iff.rfl`.

### A-W.1/F-D3 — F.10's `^` HAD NO SIGNED INSTANCE; `One`/`Pow` ADDED, AND **THE INVERSE IS TAKEN IN `Kˣ`**

**The finding.** F.08 signed exactly four below-the-line helpers (`Mul`, `single`, `AddCommGroup`,
`Module K`). F.10's `pow_card_single` writes `(single 1 1 : TwistedAlgebra cc) ^ E`, which needs
`Pow (TwistedAlgebra cc) ℕ` and hence (via `npowRec`) a `One`. **The committed F.10 signature did
not elaborate.** *Class: missing declaration in a signed helper list.*

**The repair** (the gate's, adopted verbatim; bodies are F.09's own prose — "`single 0 (cc.c 0 0)⁻¹`
is a two-sided unit"):

    instance : One (TwistedAlgebra cc) := ⟨single 0 (((cc.c 0 0)⁻¹ : Kˣ) : K)⟩
    instance : Pow (TwistedAlgebra cc) ℕ := ⟨fun f n => npowRec n f⟩

**THE LOAD-BEARING SUBTLETY, RECORDED LOUDLY.** The inverse must be formed **in `Kˣ` and coerced**,
`(((cc.c 0 0)⁻¹ : Kˣ) : K)` — **never** `((cc.c 0 0 : K))⁻¹`. With the `K`-side spelling the
executed `q = 3` leg of F.29 check 4 (`(single 1 1)² = ζ • single 0 1` at `K = ZMod 3`) **does not
`decide`**: mathlib's `Inv (ZMod n)` is `Nat.gcdA`-based well-founded recursion and does not
kernel-reduce, whereas `Kˣ`'s `Inv` is projection to the stored `inv` field. This is the same wall
as F-D5(iv), and it is why the two look like a spelling choice and are not one: the `K`-side
spelling costs the chapter a gate leg at `q = 3` — i.e. GC-11 compliance.

**Content unchanged.** `npowRec` is the `npow` any later `Monoid` instance carries, so F.10(b)'s
statement means what it meant; the `single 0 1` normalization fence on the right-hand side is
untouched. **What the fleet owes:** these two instances, or a full `Monoid`/`Ring` instance (the
natural target once F.09 is proved) whose `one` inverts in `Kˣ` and whose `npow` is `npowRec`.

**Rider (E-D13-class, no repair).** F.09's STATEMENT asserts the two-sided-unit fact but its
SIGNATURE signs only `mul_assoc`; the unit claim is carried by the `One` instance, not by a
theorem. Recorded at F.09 as a SIGNATURE NOTE and flagged to the cross-read (§14 item 6); no
declaration added, because nothing in the chapter consumes `one_mul`/`mul_one`.

### A-W.1/F-D4 — F.22's INJECTIVITY HELPER WAS PROSE-ONLY; NOW SIGNED (machine-checked here)

**The finding.** "`jbShear` injectivity (`e ≠ 0`) is a below-the-line helper lemma the gate uses"
sat in F.22's PROOF field with no SIGNATURE block, so the stub stage had **no type to land** — the
gate signed nothing and ran F.30 leg 6 on pointwise image values instead (which is what §10's own
leg pins). *Class: unsigned helper.* Nothing was wrong mathematically; the contract was incomplete.

**The repair — a real SIGNATURE block at F.22, machine-checked at this amendment:**

    theorem jbShear_injective {e h : ℤ} (he : e ≠ 0) :
        Function.Injective (jbShear e h)

**Evidence (run at the pin, `lake env lean` against the leanspec environment, clean).** The
signature elaborates AND the statement is proved: `intro p q hpq`;
`simp only [jbShear, Prod.mk.injEq] at hpq` splits the goal into `p.1 = q.1` and
`e * p.2 + h * p.1 = e * q.2 + h * q.1`; rewriting the first into the second and `linarith` give
`e * p.2 = e * q.2`; `mul_left_cancel₀ he` and `Prod.ext` close it. **The hypothesis is necessary,
also machine-checked:** `¬ Function.Injective (jbShear 0 1)`, witnessed by
`jbShear 0 1 (0,0) = jbShear 0 1 (0,1)`. The corpus frames have `e = e_q ≥ 1`, so `e ≠ 0` is free
at every intended site.

**Bookkeeping.** This is the amendment's one blueprint-side ADDITION: the landed side will carry
one declaration more than the 0e stub for F.22 (recorded at §12(d) so the diff is not read as
drift). It stays below the contract line, so F.22 keeps its one-public-declaration status.

### A-W.1/F-D5 — FIVE §10 LEGS ARE NOT `decide`-ABLE AS DISPLAYED; THE GATE-FORM TABLE IS NOW BINDING

**The finding, and what it is not.** Every expected VALUE of §10 was reproduced at both primes;
what failed was the *spelling*. Five distinct reduction walls at our pin:

| # | displayed | wall | executed |
|---|---|---|---|
| (i) | `Module.finrank`, `Nat.card` on `TwistedAlgebra` | both noncomputable | `show` through the carrier `ZMod E → K`; `simp` for `finrank`, `Nat.card_eq_fintype_card` + `decide` for `Nat.card` |
| (ii) | `orderOf z = 4` | `orderOf` does not kernel-reduce | `z ^ 4 = 1 ∧ z ^ 2 ≠ 1` (order ∣ 4, ≠ 1, ≠ 2 ⟹ 4) |
| (iii) | `slotScale u '' S = S`, `jbShear e h '' V = V'` | `Set` image equality is not decidable | pointwise on the named finite witnesses |
| (iv) | `(2 : ZMod 5)⁻¹ = 3` | `Inv (ZMod n)` is `Nat.gcdA`-based (WF recursion) | `((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 3` **+** `(2 : ZMod 5) * 3 = 1` |
| (v) | any `F₅` instance at a `[Field K]` node | `Fact (Nat.Prime 5)` is unregistered in mathlib (only 2, 3) | declare `instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩` beside the gate |

**The repair.** The table is transcribed into §10 as a **standing GC-11 gate-form rider** (binding
on gate agents), the affected F.29/F.30 legs are re-displayed in their executed forms, and §12(c)
gains the rule that a rider-form substitution is not a mismatch while a VALUE change is
stop-the-line. *Class: gate-form — no statement of any node moved.* Note (iv)'s connection to
F-D3: inverses that must reduce are taken in `Kˣ`, and that is now a chapter rule (§12 rule 2).

### A-W.1/F-D6 — THE `AdjoinRoot` GATE FIELDS CANNOT CARRY A `decide`; THE PRE-AUTHORIZED TABLE FALLBACK IS NOW THE FORM OF RECORD

**The finding.** `F₄ := AdjoinRoot (X² + X + 1 : (ZMod 2)[X])` and
`F₉ := AdjoinRoot (X² + 1 : (ZMod 3)[X])` have **no** `DecidableEq`/`Fintype` instance (AdjoinRoot
is a quotient of a polynomial ring). §10's committed text said "*if* `DecidableEq`/`Fintype`
instances resist `decide`" — the truthful statement is that they are absent, so no `decide` gate
can fire on those carriers at all.

**The repair.** §10's own pre-authorization ("a private table-built field instance below the gate in
the same file") is promoted to the form of record and spelled out: `F4 = ZMod 2 × ZMod 2` with
`θ² = θ + 1`, `F9 = ZMod 3 × ZMod 3` with `θ² = −1`, each with `CommRing` proved field-by-field by
`decide` and `Field` built on the explicit inverse `x⁻¹ = x^(q−2)`; generators `ω = θ` (order 3) and
`i = θ` (order 4), both non-involutions, which is what the arena note's coincidence trap demands.
**`native_decide` appears nowhere in the gate file** (axiom census). The `AdjoinRoot` spellings stay
recorded as the mathematical identification of the two fields — a *proof* about `F₄`/`F₉` would use
them; a *gate* cannot. F.29's SIZE box is corrected (the shared field tables are ~110 lines, larger
than the check block they serve). *Class: gate-form; the fallback the blueprint itself authorized.*

### A-W.1 — CENSUS AND CROSS-CHAPTER BOOKKEEPING

**(1) The declaration census (new, at §2).** 41 signed declarations = 8 `structure` + 18 `def` + 15
theorem-shaped rows over 11 nodes, plus F.08's 5 below-the-line instances and (new) F.22's
`jbShear_injective`. §14 item 14 is thereby answered.

**(2) Three real bodies were missing from §12(b)** — `slotScaleEquiv` (F.02's def half), `resTwist`
(F.03's def half, whose only trace was F.21's parenthetical "needs F.03's def only") and `JAResLaw`
(F.19, absent from every §12 list). The gate landed all three, which is how the gap surfaced: the
committed list named 18 nodes carrying 23 declarations against 26 landed bodies. Corrected in place;
§12(d) now also displays the stub multiplicities (15 rows, not 11).

**(3) F.17's docstring** carried "stub as axiom with header per §12" while §12(b) lands the carrier
as a real `def` (as the gate did). Struck: the carrier is a `def`; the C-side INSTANCE is what is
blocked-until-resolution.

**(4) Cross-chapter note 1 — E.45/E.46 have LANDED, so F.17's DEPENDS upgrades to GC-13(a) names**
(`Uniformity.Density.Ladder.ladderSigma`, `…ladderSigma_degree`; E46 also lands
`ladderSigma_degree_eq_deg`). Recorded at F.17 and in §11's "Into E" bullet. Per **D-F3 no F
SIGNATURE references either name**, so this is a citation-form upgrade with no Lean dependency
created.

**(5) Cross-chapter note 2 — the ORCHESTRATOR's roll-up item (already known, restated).**
`ladderSigma_degree` is NOT reachable from `import Uniformity` at HEAD: `E46.lean` is imported only
by `E47.lean`, and `Uniformity/ChapE.lean` rolls up `E01, E07, E25, E26, E34, E45` only.
`ladderSigma` IS reachable (the gate's `#check` prints its type). Filed as §14 item 15; not an F
defect, and harmless to F under D-F3.

### A-W.1 — WHAT THIS AMENDMENT DID NOT TOUCH

* `leanspec/Leanspec/ChapF.lean` — the gate's file; not edited here (§12 rule / CHAP-H §15 rule 5).
  No cross-file edit of any kind was made; `leanfinal` and `leancheck` are untouched.
* **No node's mathematical strength.** F-D1/F-D2 are identifier spellings; F-D3 adds the instances a
  signed statement already presupposed (with `npowRec`, so the statement's content is fixed);
  F-D4 signs a helper whose statement was already asserted in prose and is now machine-proved;
  F-D5/F-D6 move gate spellings only, with every pinned value reproduced. **No hypothesis was added
  to or removed from any theorem-shaped row**, and no carrier's body moved by so much as a
  quantifier — the gate's three `Iff.rfl` pins on `JD0Box2`, `GenhnBox2` and `W1Transport` are the
  machine check of exactly that.
* The two GC-13 BLOCKED-UNTIL-RESOLUTION instance obligations (F.17's C-side discharge, F.24's M4
  instance) — still awaiting the orchestrator's resolution pass; A-W.1 stubs neither.
* §3's out-of-cone census, §7's DECISIONs D-F1/D-F2/D-F3, §8's WELD-ZERO status, §13's unit
  disposition census — unchanged (the disposition vocabulary and every row's verdict stand).
* The DAG (`spec/DAG_BLUEPRINT_F.tsv`): **no edge changes.** Every repair is intra-node; the one
  DEPENDS wording that moved (F.17's E-side citation form) is the same two edges `BP.F.17 → BP.E.45`
  / `BP.F.17 → BP.E.46` at GC-13(a) instead of GC-13(b) precision, and F.22's new helper is
  below-the-line (no node-level row). F still introduces zero SCCs.
* Chapter I's consumption surface: unchanged in content, but note that two FIELD names it will
  project are respelled (`LedgerJunction.sigmaMap`, `WeldSupply.hSigma`) — F-D1's one contract
  consequence.

<!-- SENTINEL: BP-F END OF FILE -->
