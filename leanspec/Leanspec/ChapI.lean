-- ⚠ THIS FILE DELIBERATELY DOES **NOT** `import Uniformity` — see defect I-D1 in the header.
-- The list below is `leanfinal/Uniformity.lean`'s own import list MINUS `Uniformity.ChapD`
-- (the roll-up), PLUS the two chapter-E modules chapter I's Display-A `ladder` field consumes.
-- Importing the roll-up and the E-side deep-twist branch TOGETHER is a hard Lean error at HEAD.
import Uniformity.Basic
import Uniformity.HenselFactorization
import Uniformity.MultiHensel
import Uniformity.StrongHensel
import Uniformity.Quarry
import Uniformity.Density.LocalData
import Uniformity.Density.CensusGen
import Uniformity.Density.Transport
import Uniformity.Density.TypeOf
import Uniformity.Density.TypePositivity
import Uniformity.Density.InertLeaf
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.TypeOfInvariance
import Uniformity.Density.ScaleExtraction
import Uniformity.Density.NormLeaves
import Uniformity.Density.GenuineDensity
import Uniformity.Density.CoveringMenus
import Uniformity.Density.QuadCert
import Uniformity.Density.AnisotropicForms
import Uniformity.Density.Statement
import Uniformity.Density.Gates
import Uniformity.Density.Drainage
import Uniformity.Density.DensityAPI
import Uniformity.Density.TypeOfFaithful
import Uniformity.Density.TypeOfFaithfulInert
import Uniformity.ChapG
import Uniformity.ChapG.G78
import Uniformity.ChapH
import Uniformity.ChapB
import Uniformity.ChapB.B86
import Uniformity.ChapE
import Uniformity.ChapE.E24
import Uniformity.ChapE.E63
import Uniformity.ChapC
import Uniformity.ChapF

/-!
# Chapter I — CAPSTONE AND CONDITIONALITY: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-I_capstone_conditionality.md` (25 nodes I.01–I.25 — the
Display-A hypothesis block, the conditionality ledger, and the assembly toward
`UniformityStatement`), landed in the isolated `leanspec` environment **before** the chapter-I
fleet fires, in the blueprint's node order.

**STATE: OPEN, AND ONE NODE IS SIGNED IN A STATE ITS OWN BLUEPRINT FORBIDS (defect I-D7).**
Chapter I has landed nothing in `leanfinal` (`grep` for `CapstoneHypotheses` /
`DecidedSliceAt` / `MenuLawAt` / `TypeOfFaithful` as a `Prop`-carrier over `leanfinal/Uniformity/`:
zero hits), so nothing here is in the retirement state of `Leanspec.lean`'s stub lifecycle.

**Wrapper choice, declared per GC-6.6:** wrapper `namespace LeanspecI`, which the blueprint's §11
instructs directly ("stubs wrap in `namespace LeanspecI`, one file `leanspec/Leanspec/ChapI.lean`
… whichever the stub agent picks, say so in the file header"). Consequently the blueprint's
`namespace Uniformity.Density` headers in the SIGNATURE blocks are DROPPED here and every
declaration is flat inside `LeanspecI`; the landed-side namespace assignment (GC-6.2 gives
chapter I **no** sub-namespace — every I declaration lands in `Uniformity.Density` directly) is
what the fleet must land.

**This file is never imported by `leanfinal` or `leancheck`.** It is an interface contract, not
mathematics. `sorry` and `native_decide` appear nowhere; the file elaborates with
`autoImplicit`/`relaxedAutoImplicit` **off**.

## HONESTY, CARRIED FROM THE BLUEPRINT'S §1 (read before consuming anything here)

* **I-1.** Nothing in this chapter proves the capstone. `uniformity_of_capstoneHypotheses`
  (I.17) is bookkeeping: it says `UniformityStatement` follows from the frozen Display-A block
  and nothing else. The honest headline stays *"proved unconditionally at `n = 1` and `n = 2`;
  at every `n ≥ 3` stated with its complete named conditionality."*
* **I-2 (the GENIND.B fence).** No node here composes `InductionPackage n` at `n ≥ 4`.
* **I-4.** `TotalMassOne` is the drainage leg in disguise — I.18 derives it from the `a2` fields
  through landed `totalMassOne_of_drainage`; it gets no field of its own.
* **I-7.** The WELD-ZERO arc licenses nothing: `HYP.148` stays CARRY and `HYP.139` stays MATH at
  full strength.
* **OM-9's `w1` note, carried (the charge's standing instruction).** F.12's landed `W1Transport`
  is the transport's **SIGNATURE**: `w1Transport_iff_zero_iff` (F12w) proves the carrier is
  equivalent to equality of vanishing loci, and `w1Transport_of_ne_zero` makes any instantiation
  at nonvanishing families FORMALLY TRIVIAL. **A typed `w1` field discharges NOTHING of HYP.139**
  (whose MATH content is TR-3′-GEN's compatible dictionary at general order). See defect I-D8:
  in I.10's signed field list there is no `w1` field for the note to ride on.

## THE `LB1 ∧ MP1` AND `(H-VARTHETA-RES) ∧ 𝒲` CONSUMPTION RULES (I.10's dated note, binding)

Two Display-A carriers were machine-refuted VACUOUS as committed and re-signed; this file
consumes the re-signed forms ONLY, against the LANDED declarations:

1. **`LB1 ∧ MP1`** at the **A-E.2 forms** — landed `Uniformity.Density.Ladder.LB1Carrier`
   (`ChapE/E39.lean`, concluding `Nonempty (BlockSuite I)` at E.39a's full S1.7A record) and
   `…MP1Carrier` (`ChapE/E40.lean`, concluding `Nonempty (MidPeelEmission B B')`), reached
   through E.24's `LadderSupply` and consumed **universe-polymorphically in `uW`** (honesty
   E-12: `uW` is the `(SEC-RANK)` rank carrier's universe, which occurs only inside the `Prop`).
   `CapstoneHypotheses` below is therefore universe-polymorphic — `CapstoneHypotheses.{uW, uG,
   uKt, uL}` — which is the only reading Lean admits (a `Prop` cannot quantify over universes).
   The voided shadows `OM4Shadow.LB1CarrierVoided`/`MP1CarrierVoided`/`LadderObligationsVoided`
   (`verification/om4_shadow_vacuity.lean`) are FENCED: nothing here cites them.
2. **`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}`** at the **A-D.2 form** — chapter D's SITEWISE
   `Uniformity.Density.Gauge.HVarthetaRes G K L N (v i) (ρ i) (q i)` against the level's GIVEN
   ambient residue datum, reached through E.61's typed socket `Ladder.VarthetaRes` inside E.24's
   `vartheta` field. The voided existential `HVarthetaResVoided` is FENCED. **The `𝒲` half has no
   field — defect I-D4**; the landed declaration that carries both halves at the typed sockets is
   E.63's `Ladder.DeepTwistConjunct`, elaborated in the §4 gate below but NOT signed into I.10
   (the field list is frozen).

## THE SIGN-OFF COROLLARY (CONVENTIONS Part V, carried)

Two owner gates only: (a) the main Lean statement; (b) every literature cite, signed per cite.
**Every hypothesis on the capstone path must terminate as a DISCHARGE NODE or a gate-(b)
LITERATURE CITE — no third category.** Gate-(b) state at composition, transcribed:

| cite | statement artifact | state |
|---|---|---|
| B.42 `[cite:GN15 Thm 2.3 + FGMN Thm 6.6]` | `LeanspecB.exists_slope_factorization` | **landed-signed** |
| C.66 `[cite:FGMN]` | `LeanspecC.FgmnResidualMulStatement` | **REDRAFTED (A-C.6, commit `958cc39b`), awaiting owner signature** |
| C.94 `[cite:AGNPRW Thm 5.6]` | `LeanspecC.NS7TerminationStatementR` over `DescentStepR` | **REDRAFTED (A-C.6), awaiting owner signature**; the A-C.1 draft is MACHINE-REFUTED (defect I-D6) |
| C.92 `[cite:FGMN-chain]` | — | **axiom RETIRED to hypothesis-form (A-C.6 DECISION option (1)); C.92 EXITS the gate-(b) queue** |

Consequences carried into this file: I.01's `ns7` field is **cite-conditional on the C.94
REDRAFT**, not on the struck A-C.1 draft (I-D6); and no I.10 field, and no I.24/I.25 registry
row, consumes C.92's withdrawn `fgmn_calculus_exists` (defect I-D11 records what that costs).

## Census (mechanical, over this file)

| kind | count | note |
|---|---:|---|
| `def` of blueprint declarations (real bodies, stage-0e rule 1) | **8** | `NS7Termination` (I.01), `DecidedSliceAt` (I.02), `MenuLawAt` (I.03), `WindowPinningAt` (I.05), `GenhnHEAt` (I.06), `GenhnTow1At` (I.07), `TypeOfFaithful` (I.21) — plus the `structure` below |
| `structure` (real body) | **1** | `CapstoneHypotheses` (I.10) — ⚠ signed in the state §11 forbids, defect I-D7 |
| `theorem` landed REAL (blueprint §11: "I.15–I.18 … land REAL, not axiom") | **4** | I.15–I.18 |
| `axiom` stubs | **0** | chapter I signs no theorem it cannot prove at stub time |
| gate `example`s / `#check` / `#print axioms`, ALL EXECUTED | **§4 gate 9 · §6 gate 3 · I.23 17 · I.24 22 · I.25 6** | |
| `[note]` nodes with no Lean file (blueprint §0.2) | **8** | I.04, I.11, I.12, I.13, I.14, I.19, I.20, I.22 — transcribed as docstring sections, nothing declared |

**13 signed blueprint declarations** (8 `def` + 1 `structure` + 4 `theorem`), matching the
blueprint's own file list (I01–I03, I05–I07, I10, I15–I18, I21, I23–I25 = 15 files; I.23–I.25 are
gate files carrying no declaration).

## Gate order (GC-6.6(c)) as actually run

(a) the fragile signatures first — I.10's `ladder` field (the six-universe E.24 application),
I.03's `A1Family` membership, I.02's literal-slice body, I.16's `exact`-closes-the-slice proof;
(b) the `def` bodies, real; (c) the §8 numeric gates EXECUTED at `q = 2` AND `q = 3`; (d) the
`axiom` stubs — none.

## THE DEFECT LIST (stage-0e gate, 2026-08-16)

Recorded here and in the 0e report; **NOT repaired in the blueprint** (CHAP-H §15 rule 5:
elaboration failures in a stub are blueprint defects, versioned by a dated append in the
blueprint, never patched in `leanspec`). Every stub-side adjustment made to get this file to
elaborate is listed; nothing was adjusted silently.

* **I-D1 — STOP-THE-LINE, a `leanfinal` DUPLICATE-DECLARATION defect: `Uniformity.Density.Gauge.Wle`
  and `…VarthetaWConjunct` are each declared by TWO modules, which therefore cannot be imported
  together.** `Uniformity/ChapD/D55.lean:103` (`Wle`) + `D63.lean:144` (`VarthetaWConjunct`)
  versus `Uniformity/ChapD/D62w.lean:369` + `:412` — D62w re-declares both "byte-matching the
  leanspec carrier" in its own module rather than importing them. `Uniformity/ChapD.lean` (the
  roll-up, hence `Uniformity`) carries **D62w**; every chapter-E deep-twist module (E.61, E.62,
  E.63, and E.24 through E.61) imports **D63 → D55**. So
  `import Uniformity` + `import Uniformity.ChapE.E24` is a hard error:
  `import Uniformity.ChapD.D55 failed, environment already contains 'Uniformity.Density.Gauge.Wle'
  from Uniformity.ChapD.D62w`. *Class: duplicate landed declaration (a `leanfinal` defect, not a
  blueprint one) — footprint-visible and stop-the-line under the repo's axiom/interface policy.*
  **Stub-side workaround (the import block at the top of this file):** `Uniformity.lean`'s list
  MINUS `Uniformity.ChapD`, PLUS `Uniformity.ChapE.E24`/`E63`. The fleet CANNOT land chapter I in
  `leanfinal` until this is cured (a `leanfinal` I-node importing `Uniformity` and the E-side
  carriers is impossible at HEAD). Cure: delete D62w's two duplicate `def`s and have it import
  D55/D63 — mechanical, but it is an owner-visible `leanfinal` edit.
* **I-D2 — the chapter-E and chapter-F roll-ups do not carry the Display-A carrier modules.**
  `Uniformity/ChapE.lean` omits **E24, E39, E39a, E40, E44, E61, E62, E63** — every module the
  `ladder` field consumes; `Uniformity/ChapF.lean` stops at F13, omitting **F14–F28** (so F.28's
  `Weld.WeldObligations`, the weld layer's own handoff record to chapter I, is unreachable).
  Machine-checked from `import Uniformity`: `Ladder.LadderSupply`, `LB1Carrier`, `MP1Carrier`,
  `BlockSuite`, `MidPeelEmission`, `VarthetaRes`, `WFrame`, `DeepTwistConjunct` and
  `Weld.WeldObligations` are all `unknownIdentifier`. *Class: roll-up gap (same class as CHAP-F's
  recorded `ladderSigma_degree` note, but load-bearing here).* Note the ChapE half **cannot be
  cured before I-D1 is**: adding E24 to the roll-up would import D55 into `Uniformity` and break
  the package.
* **I-D3 — I.10's `ladder` field is UNDERAPPLIED BY EIGHT ARGUMENTS (hard error).** The blueprint
  signs `Ladder.LadderSupply C B`; landed E.24 is
  `LadderSupply (C) (B) (G) [CommGroup G] (Kt) [Field Kt] (L) [Field L] [Algebra Kt L]
  (N : NormSection G) (v) (ρ) (q)`. Verbatim, Lean reports `type expected, got
  (Ladder.LadderSupply C B : (G : Type ?u) → …)`. *Class: signature/landed-declaration arity
  mismatch.* **Stub-side repair:** the level data `(G, Kt, L, N, v, ρ, q)` is universally
  quantified inside the field, and the six universes are spelled
  `LadderSupply.{0, 0, uW, uG, uKt, uL}` (E-12). **The repair is honest but the resulting field
  is UNDISCHARGEABLE, and that is a second, mathematical finding:** OM-8's ρ-defeat (machine-shown
  at real tower exponents, `verification/om8_vartheta_deep.py` LEG D2) says *"typing E.61's socket
  at anything but chapter C's canonical residue data leaves the conjunct undischargeable"* — and
  a `∀ (ρ : ∀ j, ker (v j) →* Lˣ)` binder is exactly "arbitrary `ρ`". The blueprint's own ⚠
  QUANTIFIER DISCLOSURE chose the strongest uniform reading without the level data in view. The
  honest cure is an owner-gate-(a) field-list change binding the level data to chapter C's
  canonical instantiation; recorded, not taken.
* **I-D4 — the `𝒲_{≤i}` half of Display A's `∀ i ≥ 3` conjunct (HYP.63) HAS NO FIELD.** I.10's
  STATEMENT says the `ladder` field packages "E.24's `LadderSupply`, which packages … the
  `∀ i ≥ 3` deep-twist carriers E.61/E.62". The LANDED E.24 packages **E.61 only**, and says so
  in its own docstring: *"E.62's `𝒲` leg is conjoined at chapter I, not here."* So as signed,
  chapter I carries `(H-VARTHETA-RES)_i` and silently DROPS `𝒲_{≤i}` — a Display-A conjunct with
  no carrier, which §12's rider-(iii) check ("nothing else on the frozen display lacks a
  carrier ✓") therefore mis-reports. *Class: missing field for a frozen conjunct.* No stub-side
  repair (field list frozen); the §4 gate elaborates landed `Ladder.DeepTwistConjunct` (E.63),
  which is the declaration that carries both halves at the typed sockets, so the fleet has the
  exact object to re-sign against.
* **I-D5 — I.03's `∀ C ∈ F` does not elaborate: `A1Family` is a plain `def`, not an `abbrev`.**
  H.93 lands `def A1Family (r : ℕ) : Type := List (A1Cell r)`; instance search does not unfold
  plain `def`s, so `failed to synthesize Membership ?m (Induction.A1Family r)`, cascading into
  `Invalid field notation … cannot resolve field 'σ'`. A `(F : List (Induction.A1Cell r))`
  ascription does **not** cure it (ascription is transparent; `inferType F` still returns
  `A1Family r`). *Class: missing instance / wrong reducibility on a landed declaration.*
  **Stub-side repair:** `∀ C ∈ @id (List (Induction.A1Cell r)) F, …` — type-identical, since the
  two types are definitionally equal. Root-cause cure for the fleet: make H.93's `A1Family` an
  `abbrev`, or land a `Membership (A1Cell r) (A1Family r)` instance.
* **I-D6 — I.01's resolution instruction (the 2026-08-16 A-C.1 addendum) is STALE AND UNSAFE.**
  The addendum states *"the typed body is exactly `Uniformity.Density.Tower.NS7TerminationStatement`'s
  matrix … the orchestrator's stub-resolution pass may now type I.01's body — either
  `NS7Termination := NS7TerminationStatement` … "*. That draft was **MACHINE-REFUTED** at A-C.6:
  `leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt` proves `NS7TerminationStatement → False`
  absolutely over `ℤ_[2]`, Lean-core and sorry-free. It is struck; the live artifact is
  `LeanspecC.NS7TerminationStatementR` over `DescentStepR` (commit `958cc39b`), still awaiting
  owner gate-(b) signature. Secondary: the name `Uniformity.Density.Tower.NS7TerminationStatement`
  **does not exist in `leanfinal` at HEAD** (only inside the `.lean.txt` refutation record and the
  `LeanspecC` draft), so the instruction is unexecutable as written as well as unsafe. *Class:
  stale blueprint instruction pointing at a refuted statement.* I.01 is landed here at its SIGNED
  `True` body, unresolved; **any fleet agent that follows the addendum lands `False`.**
* **I-D7 — I.10 is signed in a state its own blueprint FORBIDS, and the prohibition is now stale
  too.** §11's blocked table reads *"a signed I.10 stub with `True` fields is a false
  conditionality claim; forbidden"*, while I.10's own SIGNATURE block signs `jd0 : True` and
  `genhnBox2 : 6 ≤ n → True`. Since OM-9 (2026-08-16) the L-1/L-2 binding targets are LANDED —
  `Uniformity.Density.Weld.JD0Box2` (F.04), `.GenhnBox2` (F.11), `.W1Transport` (F.12) — so the
  placeholders are stale, not merely blocked. *Class: self-contradictory node state.*
  **This file lands the structure at the signed types as an ELABORATION GATE ONLY**, with the ⚠
  carried verbatim at the declaration and a gate-local `example` proving the L-1/L-2 typed shape
  elaborates against the landed carriers. **The stub is not a signature: no fleet agent may fire
  on I.10 until the owner re-signs the field list.**
* **I-D8 — the OM-9 `w1` honesty note has no field to attach to.** OM-9's instruction is that the
  `w1` conjunct field "should carry this note when bound". I.10's signed field list has **no `w1`
  field at all**: the W-1 sub-residue (HYP.139, MATH at full strength) rides inside the
  `genhnBox2 : 6 ≤ n → True` placeholder. F.28's landed `WeldObligations` carries three fields
  (`jd0box2`, `genhnBox2`, `w1`); I.10 carries one and a half. *Class: missing field for a carried
  ledger row.* The note is carried in this file's honesty block instead; no stub-side repair.
* **I-D9 — I.03's `(A1)`-admissibility clause is VACUOUS as signed (machine-checked here).**
  `MenuLawAt n` existentially quantifies `(r, F, S)` and constrains `F` by `∀ C ∈ F, C.σ ∈ S`
  ONLY — one-directional, so `r = 0, F = []` satisfies it for **every** `S`. The §4 gate proves
  the equivalence outright: `MenuLawAt n ↔ ∃ S, (∀ σ ∈ S, σ.degree = n) ∧ ∀ O, CoveringMenu O n S`
  — i.e. the `A1Family` existential adds no strength whatsoever, and the carrier is the bare menu
  clause. This is the OM-4 FINDING-0 genre (a trivially satisfiable conjunct tracks no
  conditionality) and it is NOT what I.03's own ⚠ SIGNATURE NOTE discloses — that note discloses
  only the missing WEIGHT-correctness tie. *Class: vacuous carrier.* **No stub-side repair**
  (statements frozen). The evident re-sign is the reverse inclusion (`∀ σ ∈ S, ∃ C ∈ F, C.σ = σ`)
  plus H.94's closure predicate; that is an owner-gate-(a) event.
* **I-D10 — `a0` is over-demanded at `n = 0`.** `UniformityStatementDecided` guards its body with
  `0 < n`; `CapstoneHypotheses n`'s `a0 : DecidedSliceAt n` does not, so `∀ n, CapstoneHypotheses n`
  demands the decided-value law at degree 0, which the target never asks for. (`a2`'s `DrainageAt 0`
  IS genuinely required — landed `ofDecided` takes `∀ n, DrainageAt n`.) The `Iff.rfl` pin in §6's
  gate makes the exact relationship machine-visible: `UniformityStatementDecided ↔ ∀ n, 0 < n →
  DecidedSliceAt n`. *Class: hypothesis-side over-demand (harmless to soundness, dishonest to the
  open surface — it makes the block look one law bigger than Display A).* No stub-side repair.
* **I-D11 — I.25's expected registry is out of date by one entry, in the safe direction.** The
  node's SOURCE names "C.66/C.92's FGMN axiom group (one or two entries per the orchestrator's
  subsumption choice, §9.3 O-4)". A-C.6 DECISION option (1) **retired C.92's axiom outright**
  (`fgmn_calculus_exists` withdrawn; the class kept as a hypothesis carrier; "C.92 EXITS the
  gate-(b) queue"), so orchestrator item **O-4 is moot** and the expected registry is
  {C.94's `agnprw_termination` (at the REDRAFT `NS7TerminationStatementR`), C.66's FGMN axiom (at
  the REDRAFT `FgmnResidualMulStatement`), B.42's `[GN15]+[FGMN]` axiom}, with the OM-4/OM-5
  candidates (`recentered_key_emission`, `bBox1_cite`) queued. Also unlisted at I.25: the axiom
  `Uniformity.Density.Ladder`-side has none, but the C.92 route now depends on INSTANCE SUPPLY,
  which `#print axioms` cannot see — the gate's clause (ii) ("the conditionality is IN the axiom
  dependency") does not reach hypothesis-form cites. *Class: stale gate registry + a gate blind
  spot, both recorded.*
* **I-D12 — six SIGNED bodies are the literal placeholder `True`.** I.01, I.05, I.06, I.07, I.21
  and (as fields) I.10's `jd0`/`genhnBox2`. Every one is the blueprint's own
  BLOCKED-UNTIL-RESOLUTION state, and all six are landed here verbatim so the NAME, INDEX and
  `Prop` KIND are gated — but a reader must not mistake the elaboration for content. Blocker
  status at HEAD, re-checked at this gate: I.01 **unblocked-but-unsafe** (I-D6); I.05 **narrowed**
  (OM-6 landed `ChapH/H89w.lean`, 17 declarations, but `hwin` itself is undischarged); I.06
  **owner-assigned** (OM-7 landed `ChapH/H73w.lean`, so I.06's docstring line "transcription owner
  UNASSIGNED (orchestrator O-1)" is stale and is carried here corrected-by-annotation, not
  edited); I.07 **partially typed** (C.93's clause (i) `Tower.tower_first_live` is landed and
  reachable — `#check`ed in the §4 gate); I.21 **still blocked** (the maximal-order carrier does
  not exist in the tree). *Class: signed placeholders — an accounting fact, not an elaboration
  failure.*

## What is real and what is a stub

Per stage-0e rule 1 the definitional layer lands as REAL BODIES (8 `def`s + 1 `structure`), and
per blueprint §11 the four assembly theorems I.15–I.18 land REAL as well — their proofs are
projections and one term application, all provable at stub time. **There is not one `axiom` in
this file**, which is the chapter's design point: every open input to `UniformityStatement` is a
HYPOTHESIS of I.17, never an axiom, so I.17's own footprint is Lean-core (printed at I.24).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace LeanspecI

open Uniformity Uniformity.Density Polynomial IsLocalRing

/-! E.12's three universes plus E.61's threaded tower universes, bound explicitly (A-E.1/E-D6,
honesty E-12): `uW` occurs only inside the `ladder` field's `Prop`, so `CapstoneHypotheses` must
name it. This IS the "consume the carrier universe-polymorphically" instruction of E.39/E.24 in
the only form Lean admits — a `Prop` cannot quantify over universes, so the structure carries
them as parameters and every consumer records its choice. -/
universe uW uG uKt uL

/-! ## §4 — THE DISPLAY-A CARRIERS AND THE CAPSTONE HYPOTHESIS STRUCTURE (I.01–I.10)

Section contract, transcribed: one field per Display-A conjunct, at exactly ledger strength,
degree-indexed where the display is (`if n ≥ 6`, `if n ≥ 8`). Under Part V gate (a) the field
list of I.10 is capstone-conditionality state: **any field change (add, remove, restate) is
owner-gated**, including the removal WELD-ZERO would license (I-7). Carrier `def`s are `Prop`s;
none is proved; non-vacuity is this file's elaboration check plus the `n ≤ 2` conclusion gates
(I.23), never a claimed instance — a `Prop` structure's instantiability IS the open mathematics.
-/

/-! ### NODE I.01 [def] — `NS7(O)`, the termination hypothesis at exactly HYP.15's strength.
Lands `Uniformity.Density.NS7Termination`. ENV-I1.

⚠ **BLOCKED-UNTIL-RESOLUTION, and the published resolution route is REFUTED (defect I-D6).** The
signed body is the literal `True` placeholder below; FROZEN are the name, the bundle quantifier
and the `Prop` kind. The A-C.1 addendum's instruction to type it as `NS7TerminationStatement` is
UNSAFE — that statement proves `False` (`ChapC/C94_REFUTATION.lean.txt`) and was struck at A-C.6.
The live target is `LeanspecC.NS7TerminationStatementR`, awaiting the owner's gate-(b) signature;
until then this field is carried, and on signature it becomes cite-conditional (visible to
`#print axioms`, gate I.25). -/

/-- `NS7(O)` (Display A line 1; ledger HYP.15, CARRY-as-CITE): OM descent terminates over every
complete DVR with finite residue field. Discharged by chapter C's gate-(b) cite C.94 ([AGNPRW]
**Thm 5.6**, published — the repo's "Thm 5.2" is the arXiv-v1 number, A-3 audit §3) once signed;
carried as a named `Prop` until then.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over chapter C's
descent-history type and asserts finiteness. FROZEN HERE: the name, the bundle quantifier, the
`Prop` kind. **Do not resolve it against `NS7TerminationStatement` (refuted) — see I-D6.** -/
def NS7Termination : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    True

/-! ### NODE I.02 [def] — `A0_n`, the decided-value law at degree `n` (HYP.25's Lean-facing
slice). Lands `Uniformity.Density.DecidedSliceAt`. ENV-I1.

The body is the LITERAL slice of the landed `UniformityStatementDecided` (copied, not re-typed),
which is what makes I.16's one-line `exact` proof close. The `Iff.rfl` pin in §6's gate is the
standing machine check on that copy: it fails the build if either body drifts. -/

/-- `A0_n` (Display A; ledger HYP.25): the degree-`n` decided-value law — the degree-`n` slice of
`UniformityStatementDecided`. FAITHFULNESS (honesty I-6): the corpus states `(A0)` on the
`disc ≠ 0` locus; `decidedDensity` counts the every-lift decided classes (GC-9, the strictly
stronger read) — divergence recorded, not silently strengthened. -/
def DecidedSliceAt (n : ℕ) : Prop :=
  ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-! ### NODE I.03 [def] — `A1_n`, the exact-core-menu law at degree `n` (HYP.26, at ledger
strength; COND:A1_n's resolution, I.13). Lands `Uniformity.Density.MenuLawAt`. ENV-I1.

Defect **I-D5** (`@id` repair on the `A1Family` membership) and defect **I-D9** (the
`(A1)`-admissibility clause is VACUOUS — machine-checked in the gate below) both live here. -/

/-- `A1_n` (Display A; ledger HYP.26; COND:A1_n's resolution — I.13): a q-independent
`(A1)`-admissible family list carrying a covering menu at degree `n`. The shape clause uses
chapter H's landed `A1Family`/`A1Cell` (H.93, with W-12 r4's σ-label field).

⚠ SIGNATURE NOTE (blueprint's own): the exact-weights clause of HYP.26 is carried by the
`A1Cell.coeff` field plus the count laws (C.114/H §7) — this carrier states menu + shape +
labels, and the WEIGHT-correctness tie stays OPEN-MATH (§3 rows HYP.23/32/35).
⚠ DEFECT I-D9, ADDED AT THE 0e GATE: the shape clause is ONE-DIRECTIONAL, so `r = 0, F = []`
satisfies it for every `S` and the `A1Family` existential is VACUOUS. The gate below proves it.
⚠ DEFECT I-D5: `∀ C ∈ F` is spelled `∀ C ∈ @id (List (Induction.A1Cell r)) F` because
`Induction.A1Family` is a plain `def` and instance search will not unfold it. Type-identical. -/
def MenuLawAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧ (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S

/-! ### NODE I.04 [note] — `A2_n` IS LANDED `DrainageAt n` (NO LEAN FILE)

`A2_n`'s formal carrier exists and is landed: `Uniformity.Density.DrainageAt`
(`Density/Statement.lean:118`), PROVED at `n = 1` (`drainage_one`) and `n = 2` (`drainage_two`),
open at `n ≥ 3`. Chapter I declares **no** parallel drainage `Prop` — that would double-count the
leg (honesty I-4). I.10's `a2` field binds the landed name directly; the `#check` is in the §4
gate. DAG rows only. -/

/-! ### NODE I.05 [def] — `(H-e)-window-pinning`, the pinning carrier (HYP.24's pinning half; the
third COND orphan, resolved at I.14). Lands `Uniformity.Density.WindowPinningAt`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12). Status NARROWED at HEAD, not discharged: OM-6 landed
`leanfinal/Uniformity/ChapH/H89w.lean` (CHAP-H amendment A-H.3, 17 declarations, sorry-free,
Lean-core) — `EFF.GENHN.29`'s (b)/(c) clauses at general `e₁`, (a)'s rider-corrected interior
criterion, the `[r2]`/CAP-GEN band census, and (d)'s update-map descent. That narrows the
SUPPLIER gap (honesty I-11(ii)); it does **not** discharge `hwin` (HYP.36, GC-5) and does not
formalize `GENHN-CAP-GEN`'s reader rule. I.05's body gains concrete clauses to bind to at the
resolution pass; it is not bound here. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `(H-e)-window-pinning` (Display A; ledger HYP.24's pinning half; COND resolution I.14).
Supplier re-sourcing per v4: `LEMMA GENHN-3` + GENIND-2's consulted-height bound — NOT the
off-route `(H-a)`/`(H-b)` leg. Discharged at `e₁ = 2` by H.89; general case = per-genre
`StageInterface.hwin`.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the degree-`n` stage
data (H.09's `StageInterface` instances) and asserts the `hwin` clause at every stage of every
genre of degree `n`. FROZEN HERE: name, degree index, `Prop` kind. -/
def WindowPinningAt (n : ℕ) : Prop :=
  True

/-! ### NODE I.06 [def] — `[GENHN-HE(μ ≥ 3)]`, the deep-leaf σ-decision carrier (HYP.81),
degree-indexed `n ≥ 6`. Lands `Uniformity.Density.GenhnHEAt`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12). **The docstring's signed line "transcription owner
UNASSIGNED (orchestrator O-1)" is STALE at HEAD** and is corrected by annotation here, not
edited: OM-7 (2026-08-16) booked the owner — `leanfinal/Uniformity/ChapH/H73w.lean`, CHAP-H
amendment A-H.4 (the HE3.A transport with its degree law, the five-type `μ = 3` dictionary with
degree conservation, five-type exhaustiveness, the `μ = 2` consistency theorem, HE3.B's
unconditionality arithmetic). The conjunct is UNCHANGED and stays on the open surface: `μ ≥ 4`
still rides HYP.143, and consumers still return `BLOCKED: HYP.81`. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `[GENHN-HE(μ ≥ 3)]` (Display A, `if n ≥ 6`; ledger HYP.81). `μ = 3` slice: THEOREM HE3.A,
unconditional in the corpus, transcription owner **H73w (OM-7, 2026-08-16)** — the signed
docstring's "UNASSIGNED (orchestrator O-1)" predates that unit. `μ ≥ 4`: open (HE3-BOX-6,
HYP.143). Consumers return `BLOCKED: HYP.81`, never assume.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): quantifies over degree-`n` stage leaves with
`μ ≥ 3` (H's `StageLeaf`/`GenreDatum` layer) asserting the σ-decision clause. -/
def GenhnHEAt (n : ℕ) : Prop :=
  True

/-! ### NODE I.07 [def] — `[GENHN-TOW-1]`, the deep-tower supplier carrier (HYP.82),
degree-indexed `n ≥ 8`. Lands `Uniformity.Density.GenhnTow1At`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12), PARTIALLY TYPEABLE at HEAD: C.93's clause (i) — the
threshold `n = D_r·μ_r ≥ 2^{r+1}` the whole HYP.82 census rests on — is LANDED and reachable as
`Uniformity.Density.Tower.tower_first_live` (`ChapC/C93.lean`), `#check`ed in the §4 gate. The
remaining census items are the `#check`-suite the resolution pass binds. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `[GENHN-TOW-1]` (Display A, `if n ≥ 8`; ledger HYP.82). Keyed to chapter C's census C.93: the
boxed remainder is the `n ≥ 8` open family (HYP.67–71/78–80/142/143/144-BOX-2).

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the census conjunction, typed against C.93's
`#check`-suite names at the resolution pass. -/
def GenhnTow1At (n : ℕ) : Prop :=
  True

/-! ### NODES I.08 / I.09 [def] [late-binding: chapter F] — NO LEAN FILE, AND THE TARGETS NOW EXIST

I.08 (`JD0-BOX-2`, HYP.74) and I.09 (`GENHN-BOX-2` + the W-1 sub-residue, HYP.148/HYP.139) are
signed as GC-13(c) placeholders that "type directly into I.10's fields at the F freeze", with no
file of their own. **At HEAD their binding targets are LANDED** (OM-9, 2026-08-16, CHAP-F
amendment A-W.2): `Uniformity.Density.Weld.JD0Box2` (F.04) with the strike ledger
`JD0SiteStrike` and the proved fold half `JD0SiteStrike.jd0Box2`; `Weld.GenhnBox2` (F.11, clause
(iv) structurally absent, the `μ ≥ 3` guard inside the `Prop`); `Weld.W1Transport` (F.12). The §4
gate below elaborates all three at chapter I's consumption shape — so §9's items **L-1 and L-2
are executable now**, which is exactly what makes I.10's `True` fields a defect (I-D7) rather
than a wait. The conjuncts themselves are UNCHANGED: CARRY, and the OM-9 `w1` note (a typed
instantiation discharges NOTHING of HYP.139) travels with them. -/

/-! ### NODE I.10 [structure] — **THE CAPSTONE HYPOTHESIS STRUCTURE** (Display A, made formal).
Lands `Uniformity.Density.CapstoneHypotheses`. ENV-I1.

⚠⚠ **THIS DECLARATION IS AN ELABORATION GATE, NOT A SIGNATURE — defect I-D7.** The blueprint's
§11 blocked table says, verbatim, *"a signed I.10 stub with `True` fields is a false
conditionality claim; forbidden"*, and I.10's own SIGNATURE block nevertheless signs
`jd0 : True` and `genhnBox2 : 6 ≤ n → True`. The structure is landed here at the SIGNED types so
that the eight non-placeholder fields are type-checked against the landed corpus (which is what
found I-D3, I-D4, I-D5 and I-D9); **no fleet agent may fire on I.10 until the owner re-signs the
field list.** Since OM-9 the two `True` fields have real binding targets (F.04/F.11/F.12) — the
gate below elaborates them — so the placeholders are STALE, not merely blocked.

⚠ **STUB-SIDE REPAIR ON THE `ladder` FIELD (defect I-D3).** The signed `Ladder.LadderSupply C B`
is underapplied by eight arguments against the landed E.24; the level data
`(G, Kt, L, N, v, ρ, q)` is quantified inside the field here and the six universes are spelled
explicitly (E-12). Recorded consequence: a `∀ ρ` binder is precisely OM-8's ρ-defeat regime, so
the field as repaired is **undischargeable**; the honest cure is a gate-(a) field-list change
binding chapter C's canonical residue data.

⚠ **QUANTIFIER DISCLOSURE, transcribed.** Display A assumes the ladder suite "uniformly in `O`";
E's carriers are instance-level. The field quantifies over ALL instantiations — the strongest
uniform reading. Weakening it to the instantiations arising from degree-`n` inputs weakens a
hypothesis, hence STRENGTHENS the theorem, and is still a gate-(a) event because the field list
IS the public conditionality.

⚠ **KIND NOTE [F7], transcribed.** H.95's `InductionPackage` is a `def`-Prop existential; this
carrier is a `structure` and does NOT claim to mirror H.95's kind. -/

/-- **Display A** (`spec/HYPOTHESIS_LEDGER.md`, FROZEN v5), one field per conjunct, at ledger
strength, degree-indexed where the display is. Field-list changes are owner gate-(a) events
(CONVENTIONS Part V).

Consumption rules in force (I.10's 2026-08-16 dated note): `ladder`'s `.lb1`/`.mp1` projections
are the **A-E.2** forms (`Nonempty (BlockSuite I)` / `Nonempty (MidPeelEmission B B')`), consumed
universe-polymorphically in `uW`; `.vartheta` is E.61's typed socket at chapter D's **A-D.2**
sitewise `HVarthetaRes`. The voided shadows (`OM4Shadow.*`, `HVarthetaResVoided`) are FENCED.

⚠ The `AllOInterfaces` conjunct is NOT a field — §4.3's signed reconciliation (honesty I-10).
⚠ The `𝒲_{≤i}` half of the `∀ i ≥ 3` conjunct has NO field (defect I-D4).
⚠ `jd0`/`genhnBox2` are the FORBIDDEN-TO-SIGN placeholders (defect I-D7); `w1` has no field at
all (defect I-D8). -/
structure CapstoneHypotheses (n : ℕ) : Prop where
  ns7 : NS7Termination
  ladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      -- ⚠ I-D3's stub-side repair: the level data E.24 actually takes, quantified here.
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q
  a0 : DecidedSliceAt n
  a1 : MenuLawAt n
  a2 : DrainageAt n
  jd0 : True                            -- ⚠ LATE-BINDING F (I.08); defect I-D7
  genhnBox2 : 6 ≤ n → True              -- ⚠ LATE-BINDING F (I.09); defects I-D7, I-D8
  windowPinning : WindowPinningAt n
  genhnHE : 6 ≤ n → GenhnHEAt n
  genhnTow1 : 8 ≤ n → GenhnTow1At n

/-! ## §4 GATE (executed; not blueprint declarations)

Nine checks. Each is something this section could get wrong silently, and three of them are the
machine evidence behind defects I-D4, I-D7 and I-D9. -/

section GateFour

-- (1) I.04: `A2_n`'s carrier is the LANDED `DrainageAt`, and I.10's `a2` field binds that name.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) : DrainageAt n := h.a2

-- (2) the A-E.2 `(LB1)` consumption pattern, universe-polymorphic in `uW`: from the `ladder`
-- field at a triggering interface, the FULL S1.7A block suite. Had `lb1` been left at the
-- machine-refuted shadow (product identity + degree sum only), this would not typecheck.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (I : Ladder.RungInterface.{0, 0, uW} C B) (hmulti : 1 < I.sides.card) :
    Nonempty (Ladder.BlockSuite I) :=
  (h.ladder ℤ K C B G Kt L N v ρ q).lb1 I (Or.inl hmulti)

-- (3) the A-E.2 `(MP1)` consumption pattern: at a legal recentering, the FULL items-2–5 record.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (Λ : Polynomial ℤ) (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree < C.D) (B' : Ladder.BlockData C)
    (hB' : B'.Φ = B.Φ - Λ) (hdvd : B'.Φ ∣ B.F) :
    Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B') :=
  (h.ladder ℤ K C B G Kt L N v ρ q).mp1 Λ hΛ hdeg B' hB' hdvd

-- (4) the A-D.2 `(H-VARTHETA-RES)_i` consumption pattern: chapter D's SITEWISE carrier at the
-- level-`i` data. Typing this against the voided existential would fail.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (i : ℕ) (hi : 3 ≤ i) :
    Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
  ((h.ladder ℤ K C B G Kt L N v ρ q).vartheta i hi).supplied

-- (5) **DEFECT I-D4, machine-exhibited.** The landed declaration that carries BOTH halves of the
-- `∀ i ≥ 3` conjunct at the typed sockets is E.63's `DeepTwistConjunct`; the `ladder` field
-- delivers only its first component, and the `𝒲` component has no field in I.10 at all. The
-- `#check` records the object the fleet must re-sign against.
#check @Uniformity.Density.Ladder.DeepTwistConjunct
example {G : Type uG} [CommGroup G] {K : Type uKt} [Field K] {L : Type uL} [Field L]
    [Algebra K L] {N : Gauge.NormSection G} (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ)
    (H : Ladder.DeepTwistConjunct v ρ q A R w) (i : ℕ) (hi : 3 ≤ i) :
    Gauge.HVarthetaRes G K L N (v i) (ρ i) (q i) ∧ Ladder.WFrame A q R w i :=
  ⟨(H i hi).1.supplied, (H i hi).2⟩

-- (6) **DEFECT I-D7 / items L-1 and L-2, machine-exhibited.** The `True` fields' binding targets
-- are landed and type at chapter I's consumption shape RIGHT NOW.
example : Prop :=
  ∀ (Γ K : Type) [AddCommGroup Γ] [Field K] (site : Weld.ValueDictSite Γ K), Weld.JD0Box2 site
example : Prop := ∀ (K : Type) [Field K] (s : Weld.CarrySite K), Weld.GenhnBox2 s
example : Prop := ∀ (K ι : Type) [Field K] (Rh RG : ι → K), Weld.W1Transport Rh RG

-- (7) **DEFECT I-D9, machine-PROVED: I.03's `(A1)`-admissibility clause is VACUOUS.** The shape
-- clause is one-directional, so `r = 0, F = []` satisfies it for every `S`, and `MenuLawAt` is
-- EQUAL to its bare menu clause. This is the OM-4 FINDING-0 genre and is NOT what I.03's own ⚠
-- SIGNATURE NOTE discloses.
example (n : ℕ) : MenuLawAt n ↔
    ∃ S : Finset FactorizationType, (∀ σ ∈ S, σ.degree = n) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        CoveringMenu O n S := by
  constructor
  · rintro ⟨_, _, S, _, hdeg, hmenu⟩
    exact ⟨S, hdeg, hmenu⟩
  · rintro ⟨S, hdeg, hmenu⟩
    exact ⟨0, ([] : List (Induction.A1Cell 0)), S, by intro C hC; simp at hC, hdeg, hmenu⟩

-- (8) I.07's partially-typed census leg: C.93 clause (i), the `n = D_r·μ_r ≥ 2^{r+1}` threshold
-- the whole HYP.82 census rests on, is LANDED and reachable.
#check @Uniformity.Density.Tower.tower_first_live

-- (9) the FENCE, stated as a type: `NS7Termination`'s signed body is the placeholder, and this
-- is the ONE machine-visible fact about it. Anything stronger would be a resolution, which
-- defect I-D6 forbids until the C.94 REDRAFT is signed.
example : NS7Termination := fun _ => trivial

end GateFour
