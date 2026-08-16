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
| `def` of blueprint declarations (real bodies, stage-0e rule 1) | **7** | `NS7Termination` (I.01), `DecidedSliceAt` (I.02), `MenuLawAt` (I.03), `WindowPinningAt` (I.05), `GenhnHEAt` (I.06), `GenhnTow1At` (I.07), `TypeOfFaithful` (I.21) |
| `structure` (real body) | **1** | `CapstoneHypotheses` (I.10) — ⚠ signed in the state §11 forbids, defect I-D7 |
| `theorem` landed REAL (blueprint §11: "I.15–I.18 … land REAL, not axiom") | **4** | I.15–I.18 |
| `axiom` stubs | **0** | chapter I signs no theorem it cannot prove at stub time; the file's ONE `axiom` is I.25's fenced, `private`, `True`-valued positive control for the AXCHK guard, consumed by nothing |
| gate `example`s / `#check`, ALL EXECUTED | **23 `example` + 7 `#check`** | §4 gate (9 checks) · §6 gate (the `Iff.rfl` slice pin + the I.19 package-route `#check`s) · I.23 (the `q = 2`/`q = 3` anchors, the `e·f = 2` non-applicability proof, the two `n = 2` non-vacuity witnesses) |
| `[note]` nodes with no Lean file (blueprint §0.2) | **8** | I.04, I.11, I.12, I.13, I.14, I.19, I.20, I.22 — transcribed as docstring sections, nothing declared |
| ENFORCED AXCHK guards (`#axiom_core`, I.24/I.25) | **67** | each one FAILS THE BUILD on a non-core footprint; two `elab` commands (`#axiom_core`, `#axiom_reg`) implement them |

**12 signed blueprint declarations** (7 `def` + 1 `structure` + 4 `theorem`), matching the
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

Per stage-0e rule 1 the definitional layer lands as REAL BODIES (7 `def`s + 1 `structure`), and
per blueprint §11 the four assembly theorems I.15–I.18 land REAL as well — their proofs are
projections and one term application, all provable at stub time. **There is not one `axiom` STUB
in this file**, which is the chapter's design point: every open input to `UniformityStatement` is
a HYPOTHESIS of I.17, never an axiom, so I.17's own footprint is Lean-core — *enforced*, not
merely printed, at I.24. (The single `private axiom axchkSelfTestAxiom : True` at I.25 is the
AXCHK guard's positive control: `True`-valued, so it cannot weaken anything, and consumed by
nothing outside its own two commented self-test lines.)
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

/-! ## §4.3 — NODE I.11 [note] — THE `AllOInterfaces` RECONCILIATION (NO LEAN FILE)

Honesty I-10: in Lean, all-`O` generality is not an assumption but the statement form itself, so
Display A's final conjunct is a **signed structural disposition**, not a field — "the informal
corpus's uses are characteristic-general" is not a statable `Prop`. The 14 names terminate as:
GENIND-1 (HYP.121) ∀`O`-free by form, H.93/H.94; RMG (122), GRB (124), ITER-LAW (125) out of cut
(`EXT:` notes, no import to generalize); ILN (123) consumers out of cone, residual rides
HYP.148's ∀`O` carrier; W/J (126), DU (127), W-10 (128) consumers out of cone / pricing-only;
J-D0 (129) the ∀`O` binder of F's carrier statement — **now landed and checkable**, see §4 gate
check (6); L2core (130), HUMAN_PROOF (131), local-integrals (132) quarry-side / Q7 route
exclusion; CONV (133) `leanfinal` is monic-native; GENHN-count (134) H §7's ∀`O` statements at
`μ = 2`. GC-8's rider-(iii) sanity check passes for these 14 — but see **defect I-D4**: the
rider-(iii) summary sentence in §12 ("nothing else on the frozen display lacks a carrier ✓") is
false as of this gate, because `𝒲_{≤i}` lacks one.

## §5 — THE COND RESOLUTIONS (I.12–I.14, all [note], NO LEAN FILES)

* **I.12 — `COND:A2_n` RESOLVED.** `A2_n` IS ledger row HYP.27's content and its carrier is
  LANDED: `Uniformity.Density.DrainageAt n`. `n = 1, 2` PROVED (`drainage_one`, `drainage_two`);
  `n = 3` open (HYP.08/09 frontier); `n ≥ 4` open via H.98 ⇐ `InductionPackage`. The 0c matcher
  missed it on a name-form technicality ("`A2` drainage", no `_n`).
* **I.13 — `COND:A1_n` RESOLVED.** `A1_n` IS HYP.26's content; its carrier is I.03 (`MenuLawAt`),
  typed against H.93's landed `A1Cell`/`A1Family`. ⚠ This resolution is weaker than it reads:
  defect I-D9 shows the `A1Family` leg of `MenuLawAt` is vacuous, so what I.13 actually resolves
  today is the MENU clause, not the `(A1)`-admissible SHAPE.
* **I.14 — `COND:H-e)-window-pinning` RESOLVED.** The conjunct IS HYP.24's pinning half (the v4
  SUPPLIER RE-SOURCED block is the authority: `LEMMA GENHN-3` + GENIND-2's consulted-height
  bound, NOT the off-route `(H-a)`/`(H-b)` leg). Carriers: I.05 + H.89 (`e₁ = 2`) +
  `StageInterface.hwin` (carried, per-genre). Supplier gap narrowed by OM-6's landed `H89w.lean`
  and NOT closed (`hwin` undischarged) — orchestrator item O-2 is DISCHARGED as an orchestration
  item, the mathematics is not.

## §6 — THE ASSEMBLY (I.15–I.20)

Section contract, transcribed: everything here is bookkeeping (honesty I-1) — projections of
I.10 and applications of landed `UniformityStatement.ofDecided` / `totalMassOne_of_drainage` and
committed `uniformity_of_package` (H.98). **No theorem in this section makes the capstone less
conditional; each makes the conditionality machine-readable.** Per blueprint §11 these four land
REAL, not as `axiom`s — their proofs are projections and one term application. -/

/-- **I.15** — the drainage projection. -/
theorem drainage_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : ∀ n, DrainageAt n :=
  fun n => (h n).a2

/-- **I.16** — the decided-target projection. The content: the `a0` fields ARE the degree-slices
of the decided target, so re-indexing is the whole proof. This is where the count layer's
openness is made visible — nobody can supply `∀ n, CapstoneHypotheses n` today precisely because
`a0`/`a1` are open at `n ≥ 3`.

The one-line `exact` closes because I.02's body was COPIED from the landed target's body rather
than re-typed; the `Iff.rfl` pin in the §6 gate is the standing regression on that copy. -/
theorem decided_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatementDecided := by
  intro n _hn σ hσ
  exact (h n).a0 σ hσ

/-- **I.17 — THE HONEST CAPSTONE ASSEMBLY.** `UniformityStatement` follows from the ledger's
frozen hypothesis block and nothing else. What remains open is exactly the block's fields: see
the chapter-I disposition table (§3, 36 OPEN-MATH rows + the gate-(b) cites).

**This proves no mathematics** (honesty I-1). Its value is the footprint: every open input is a
HYPOTHESIS, never an axiom, so this declaration's `#print axioms` is Lean-core — printed at
gate I.24. -/
theorem uniformity_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatement :=
  UniformityStatement.ofDecided (drainage_of_capstoneHypotheses h)
    (decided_of_capstoneHypotheses h)

/-- **I.18** — `TotalMassOne`, not double-counted: from the same structure, via the `a2` fields
and landed `totalMassOne_of_drainage` ONLY (honesty I-4 — the mass law is the drainage leg
wearing a different hat and gets no field of its own). -/
theorem totalMassOne_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : TotalMassOne :=
  totalMassOne_of_drainage (drainage_of_capstoneHypotheses h)

/-! ### §6 GATE (executed) -/

section GateSix

-- (1) **THE LITERAL-SLICE PIN (I.02 ⟷ the landed target).** `UniformityStatementDecided` IS
-- `∀ n, 0 < n → DecidedSliceAt n`, on the nose. This `Iff.rfl` fails the build the moment either
-- body drifts by so much as an instance order — the standing regression behind I.16's `exact`.
example : UniformityStatementDecided ↔ ∀ n : ℕ, 0 < n → DecidedSliceAt n := Iff.rfl

-- (2) **DEFECT I-D10, machine-visible in the same pin.** The landed target guards its body with
-- `0 < n`; `CapstoneHypotheses n`'s `a0` does not, so `∀ n, CapstoneHypotheses n` demands
-- `DecidedSliceAt 0` — a law the capstone never asks for. (`a2`'s `DrainageAt 0` IS required:
-- landed `ofDecided` takes `∀ n, DrainageAt n`, as the `#check` records.)
#check @Uniformity.Density.UniformityStatement.ofDecided

-- (3) **NODE I.19 [note] — THE PACKAGE ROUTE, consumed by name and NOT re-exported.** CHAP-H's
-- committed pair is landed; the one-public-declaration discipline forbids a verbatim re-export
-- (that adds a name, not content), so the note is a `#check`. `package_two` is UNCONDITIONAL
-- (H.96, a chapter-G payoff); `package_three_of_rate` is H.97's ADOPTED form —
-- `package_three_of_drainage` is DECLARED UNPROVABLE by H.97's own ⚠ and must not be assigned.
-- ⚠ THE GENIND.B FENCE APPLIES IN FULL (honesty I-2): no node here or anywhere composes
-- `InductionPackage n` for `n ≥ 4`.
#check @Uniformity.Density.drainage_of_package
#check @Uniformity.Density.uniformity_of_package
#check @Uniformity.Density.package_two
#check @Uniformity.Density.package_three_of_rate

end GateSix

/-! ### NODE I.20 [note] — THE STAGE DISPLAY (NO LEAN FILE)

The honest "capstone modulo …" statement at each stage, for the record and for §12's teeth.

| stage | fires | modulo (named) |
|---|---|---|
| **S0 — today, landed** | `n = 1` drainage + total mass; `n = 2` drainage, total mass, the exact densities, THE CAPSTONE SLICE; the `q = 2, 3` instances | nothing — unconditional, Lean-core |
| **S1 — chapters B–H land** | leaf layer, schema, rate calculus, `package_two`, the σ-μ2 chain, order-1 count laws | the gate-(b) cites where consumed (B.42 signed; C.66/C.94 REDRAFTED, unsigned; C.92 RETIRED) |
| **S2 — the `n = 3` frontier closes** | `DrainageAt 3` (H.97 + H.98), cubic total mass unconditionally | `hrate₃` (HYP.08) + the cubic value layer (HYP.11/28/29) |
| **S3 — the open surface** | `UniformityStatement` via I.17 | **exactly the §4 field list** — i.e. §3's 36 OPEN-MATH rows + the CITEs, and nothing else |

**No stage claims more than its row.** ⚠ The S3 row's "and nothing else" claim is checkable and
this gate finds it SHORT by one conjunct: `𝒲_{≤i}` (HYP.63) is on the display and has no field
(defect I-D4), so "exactly the §4 field list" is at present a smaller set than Display A. The
sentence a report may use must therefore be qualified until the field list is re-signed.

## §7 — THE `typeOf` FAITHFULNESS BRIDGE AND THE CORE-SET AUDIT LEDGER (I.21–I.22)

### NODE I.21 [def] — `TypeOfFaithful`, the trust-boundary bridge statement.
Lands `Uniformity.Density.TypeOfFaithful`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12), and STILL BLOCKED at HEAD: typing the body needs the
factor-field valuation-ring carrier — the object B.56's OPTIONAL repair route would build — and
it does not exist in the tree. OM-5 §3.1 sharpens why: at every `d ≥ 2` leaf the order
`AdjoinRoot g` has residue field of degree `m < m·d`, hence is never a DVR, so that region lies
entirely OFF the monogenic-maximal locus the landed `Density/TypeOfFaithful.lean` reaches. -/

-- The signed body is the bare `True` placeholder (the node is BLOCKED-UNTIL-RESOLUTION);
-- nothing about the two APIs is asserted, which is the point of GC-3's KEPT-APART rule.
/-- **THE TRUST BOUNDARY, NAMED** (ledger HYP.01 [CORE-SET] + HYP.105; GC-3's kept-apart rule):
`typeOf`'s gcd multiset (over the ORDER `AdjoinRoot g`) agrees on the `disc ≠ 0` locus with the
ideal-theoretic `(e, f)` multiset (over the maximal order/DVR), in the primed rank-form
generation. **NO chapter may silently identify the two APIs** (GC-3); a node needing the
identification hypothesizes THIS name or returns `BLOCKED: HYP.01`.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the bundle and monic
`f` with `disc f ≠ 0`, and equates `(typeOf f).data` with the maximal-order multiset via
`Ideal.ramificationIdx'`/`inertiaDeg'`. FROZEN HERE: name, locus, both APIs by name. -/
def TypeOfFaithful : Prop :=
  True

/-! ### NODE I.22 [note] — THE CORE-SET AUDIT LEDGER A-1 … A-7 (NO LEAN FILE)

Under Part V item 2, cite/def-faithfulness rows stay gate-(b)-adjacent HUMAN reads; the rest are
absorbed into the standing fresh-eyes cadence. **No audit row is a fleet node.**

| id | row(s) | object | class | when |
|---|---|---|---|---|
| A-1 | HYP.01, HYP.105 | `typeOf` faithfulness — review I.21's statement against the classical `(e,f)` multiset | gate-(b)-adjacent, human | before any node hypothesizes `TypeOfFaithful` |
| A-2 | HYP.12 | `(e,f)` ordering/multiset normalization vs the classical convention | rides A-4 | with A-4 |
| A-3 | HYP.17 | [AGNPRW]/[GN15]/[FGMN]/Kuhlmann publisher numbering | gate-(b)-adjacent (cite) | **DONE for all three C-side cites** (A-C.1/A-C.6); residual print-reads are the owner's closing checks |
| A-4 | HYP.98 | the core set: the types, `UniformityStatement`, the two densities, the cites, changed-definition faithfulness paragraphs | RECURRING fresh-eyes | at chapter milestones; **next at this gate's findings** |
| A-5 | HYP.111 (def half) | what `decidedDensity` counts | rides A-4 | with A-4 |
| A-6 | (I.10) | the field list of `CapstoneHypotheses` vs frozen Display A — one-to-one, nothing added, nothing dropped | fresh-eyes, decorrelated arm | **FIRES NOW: this gate finds it NOT one-to-one — I-D4 (`𝒲` dropped), I-D7/I-D8 (`jd0`/`genhnBox2` placeholders, no `w1`), I-D9 (`a1` vacuous), I-D10 (`a0` over-demanded at n = 0)** |
| A-7 | HYP.91 | OB-a…OB-d representation vs CHAP-H's committed text | bounded, one pass | at the H stub stage |
-/

/-! ## §8 — THE GATES (I.23–I.25), EXECUTED

**Arena note.** Chapter I owns no mathematics, so its gates are the teeth (GC-8's own
battery-inheritance row: "I: no batteries — its teeth are the gate nodes"). Three of them: the
unconditional `n ≤ 2` re-fire (I.23), the maintained AXCHK census (I.24), and the cite-footprint
gate (I.25). GC-11 compliance for I.23: **two primes ✓** (`q = 2` and `q = 3`); the
`e > 1 ∧ f > 1` witness clause is **signed non-applicable at `n = 2`** and the reason is
executed below rather than asserted (a degree-2 type has `e·f = 2`).

**The AXCHK guard is EXECUTED, not eyeballed.** `#print axioms` prints a line a human must read;
this file installs `#axiom_core`, which *fails the build* when a constant's footprint leaves
`{propext, Classical.choice, Quot.sound}`. That turns REVISION 2's "maintained, diffable census"
into a maintained, self-enforcing one: a footprint regression anywhere on the capstone-facing
surface is a red build here, which is what the repo's stop-the-line rule wants. -/

section Gates

open Lean Elab Command in
/-- **The AXCHK primitive (I.24/I.25).** `#axiom_core foo` fails the build unless `foo`'s axiom
footprint is EXACTLY Lean core `{propext, Classical.choice, Quot.sound}`. With the gate-(b)
registry currently EMPTY (no cite axiom is landed in `leanfinal`; B.42 is signed but unlanded,
C.66/C.94 are REDRAFTED and unsigned, C.92's axiom is RETIRED), "Lean core exactly" IS I.25's
clause (i) AND its clause (iii) forbidden-list check — `AX_cellRecursion`, `Lean.ofReduceBool`
and every unsigned axiom are excluded by the same test. When a cite lands, its consumers move to
`#axiom_reg` below. -/
elab "#axiom_core " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ax ← liftCoreM <| collectAxioms n
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AXCHK FAIL (I.25 clause (i)/(iii)): {n} depends on non-core axioms {bad.toList}"

open Lean Elab Command in
/-- **I.25 clause (ii), the cite-conditional form.** `#axiom_reg foo [a, b]` fails the build
unless `foo`'s footprint is Lean core PLUS a subset of the named registry — the honest carrier
the ledger wants ("the conditionality is IN the axiom dependency", C.67's pattern). The registry
at composition time is **empty**, so no declaration uses this form yet; expected first entries
are C.94's `agnprw_termination` (at the A-C.6 REDRAFT `NS7TerminationStatementR`) and C.66's FGMN
axiom (at the REDRAFT `FgmnResidualMulStatement`), plus B.42's `[GN15]+[FGMN]` axiom on landing.
⚠ Defect I-D11: this gate is BLIND to C.92's route, which A-C.6 converted from an axiom to
hypothesis-form — an unsupplied `[FGMNCalculus …]` instance is invisible to `collectAxioms`. -/
elab "#axiom_reg " id:ident " [" reg:ident,* "] " : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ax ← liftCoreM <| collectAxioms n
  let mut allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for r in reg.getElems do
    allowed := allowed.push (← liftCoreM <| realizeGlobalConstNoOverload r)
  let bad := ax.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AXCHK FAIL (I.25 clause (ii)): {n} depends on unregistered axioms {bad.toList}"

/-! ### NODE I.23 [gate] — THE UNCONDITIONAL-SLICE GATE (`q = 2` AND `q = 3`)

(i) footprints of the landed unconditional set; (ii) chapter G's landed `n = 2` values re-fired
as regression anchors, with the expected numbers EXECUTED rather than commented; (iii)
non-vacuity witnesses for I.02's and I.03's `n = 2` instances. -/

-- (i) the landed unconditional set: every one Lean-core, enforced.
#axiom_core Uniformity.Density.drainage_one
#axiom_core Uniformity.Density.totalMass_one
#axiom_core Uniformity.Density.drainage_two
#axiom_core Uniformity.Density.totalMass_two
#axiom_core Uniformity.Density.coveringMenu_two
#axiom_core Uniformity.Density.coveringMenu_three
#axiom_core Uniformity.Density.genuineDensity_two_exact
#axiom_core Uniformity.Density.uniformityStatement_two
#axiom_core Uniformity.Density.gate_two_padic_two_exact
#axiom_core Uniformity.Density.gate_two_padic_three_exact

-- (ii) the `q = 2` anchor triple `(1/3, 1/3, 1/3)`.
example : genuineDensity ℤ_[2] 2 splitType = 1 / 3 := gate_two_padic_two_exact.1
example : genuineDensity ℤ_[2] 2 inertType = 1 / 3 := gate_two_padic_two_exact.2.1
example : genuineDensity ℤ_[2] 2 ramType = 1 / 3 := gate_two_padic_two_exact.2.2
-- the `q = 3` anchor triple `(3/8, 3/8, 1/4)` — a NON-uniform triple, so the two primes really
-- separate (had the gate run at `q = 2` alone, a "all types equally likely" bug would survive).
example : genuineDensity ℤ_[3] 2 splitType = 3 / 8 := gate_two_padic_three_exact.1
example : genuineDensity ℤ_[3] 2 inertType = 3 / 8 := gate_two_padic_three_exact.2.1
example : genuineDensity ℤ_[3] 2 ramType = 1 / 4 := gate_two_padic_three_exact.2.2
-- the exact `n = 2` drainage law `undecidedCount O 2 N = q^N` (G.36), at both primes and at the
-- blueprint's three spot values `(q, N) = (2,1) ↦ 2`, `(2,3) ↦ 8`, `(3,2) ↦ 9`.
example : undecidedCount ℤ_[2] 2 1 = 2 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]
example : undecidedCount ℤ_[2] 2 3 = 8 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]
example : undecidedCount ℤ_[3] 2 2 = 9 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]

-- GC-11's `e > 1 ∧ f > 1` witness clause: SIGNED NON-APPLICABLE at `n = 2`, and the reason is
-- executed rather than asserted. The meaningful witnesses live in B/C/E's gates (e.g. B.85),
-- whose footprints I.24 re-prints on landing.
example : ∀ e f : ℕ, e * f = 2 → ¬ (1 < e ∧ 1 < f) := by
  rintro e f hef ⟨he, hf⟩
  have h4 : 2 * 2 ≤ e * f := Nat.mul_le_mul he hf
  rw [hef] at h4
  omega

-- (iii) NON-VACUITY of the `a0` field at `n = 2`: `DecidedSliceAt 2` is PROVED outright, from
-- chapter G's landed `uniformityStatement_two` through the landed `n = 2` drainage tie
-- `genuineDensity_eq_decidedDensity_two`. This is the field's witness that it says something.
example : DecidedSliceAt 2 := by
  intro σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := uniformityStatement_two σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, by rw [← genuineDensity_eq_decidedDensity_two]; exact h2⟩

-- NON-VACUITY of the `a1` field at `n = 2`: `MenuLawAt 2` is PROVED from `coveringMenu_two`.
-- ⚠ READ WITH DEFECT I-D9: the `A1Family` component of this witness is the EMPTY list, which is
-- exactly why the witness is cheap — the shape clause carries no content. The menu clause is
-- what is really certified here.
example : MenuLawAt 2 := by
  refine ⟨0, ([] : List (Induction.A1Cell 0)), {splitType, inertType, ramType}, ?_, ?_, ?_⟩
  · intro C hC
    simp at hC
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    exacts [splitType_degree, inertType_degree, ramType_degree]
  · intro O _ _ _ _ _
    exact coveringMenu_two

/-! ### NODE I.24 [gate] — **AXCHK: THE MAINTAINED INTERFACE CENSUS**

REVISION 2's planned artifact, composed here as an ENFORCED census: every exported
capstone-facing interface of `leanfinal`, guarded Lean-core.

**Location decision, recorded and CHANGED at this gate.** The blueprint proposes
`leanfinal/AXCHK.lean` with a pointer at `spec/`. That is not composable at HEAD: defect I-D1
means a `leanfinal` module cannot import both `Uniformity` and the chapter-E Display-A carriers,
so a `leanfinal`-side census cannot cover the `ladder` field's supply. The census therefore
lives HERE (in `leanspec`, which is allowed to pick its import set) until I-D1 is cured; the
committed diffable OUTPUT still belongs under `spec/` and remains the orchestrator's to emit.

**Maintenance rule (unchanged).** Every chapter's stub-gate agent APPENDS its chapter's terminal
names on landing — this block is the one place the whole trusted surface is greppable. -/

-- the `Statement.lean` API: both CAP targets and every cross-implication
#axiom_core Uniformity.Density.UniformityStatement
#axiom_core Uniformity.Density.UniformityStatementDecided
#axiom_core Uniformity.Density.UniformityStatementPadic
#axiom_core Uniformity.Density.UniformityStatement.ofDecided
#axiom_core Uniformity.Density.UniformityStatement.toDecided
#axiom_core Uniformity.Density.UniformityStatement.toPadic
#axiom_core Uniformity.Density.DrainageAt
#axiom_core Uniformity.Density.TotalMassOne
#axiom_core Uniformity.Density.totalMassOne_of_drainage
-- the density / drainage layer
#axiom_core Uniformity.Density.genuineDensity
#axiom_core Uniformity.Density.decidedDensity
#axiom_core Uniformity.Density.CoveringMenu
#axiom_core Uniformity.Density.genuineDensity_eq_of_drainage
#axiom_core Uniformity.Density.sum_genuineDensity_eq_one_of_drainage
#axiom_core Uniformity.Density.one_le_sum_genuineDensity
#axiom_core Uniformity.Density.typeOf
-- chapter G's terminal supplies (the rest are re-fired at I.23)
#axiom_core Uniformity.Density.undecidedCount_two_eq
#axiom_core Uniformity.Density.undecidedSeq_two_eq
#axiom_core Uniformity.Density.totalMass_three_of_drainage
#axiom_core Uniformity.Density.one_le_sum_three
#axiom_core Uniformity.Density.card_le_undecidedCount_three
-- chapter H's terminal supplies (the assembly spine + the `(A1)` schema)
#axiom_core Uniformity.Density.InductionPackage
#axiom_core Uniformity.Density.package_two
#axiom_core Uniformity.Density.package_three_of_rate
#axiom_core Uniformity.Density.drainage_of_package
#axiom_core Uniformity.Density.uniformity_of_package
#axiom_core Uniformity.Density.Induction.A1Cell
#axiom_core Uniformity.Density.Induction.A1Family
-- chapter E's Display-A carriers (the `ladder` field's supply, at the A-E.2/A-D.2 forms)
#axiom_core Uniformity.Density.Ladder.LadderSupply
#axiom_core Uniformity.Density.Ladder.LB1Carrier
#axiom_core Uniformity.Density.Ladder.MP1Carrier
#axiom_core Uniformity.Density.Ladder.VarthetaRes
#axiom_core Uniformity.Density.Ladder.WFrame
#axiom_core Uniformity.Density.Ladder.DeepTwistConjunct
#axiom_core Uniformity.Density.Gauge.HVarthetaRes
-- chapter F's Display-A carriers (I.08/I.09's L-1/L-2 targets)
#axiom_core Uniformity.Density.Weld.JD0Box2
#axiom_core Uniformity.Density.Weld.GenhnBox2
#axiom_core Uniformity.Density.Weld.W1Transport
-- chapter C's landed census leg
#axiom_core Uniformity.Density.Tower.tower_first_live
-- the landed discharge set named in the §3 disposition table
#axiom_core Uniformity.Hensel.strongHensel
#axiom_core Uniformity.Hensel.exists_monic_factorization_finset
#axiom_core Uniformity.Density.typeOf_shift
#axiom_core Uniformity.Density.typeOf_scaleRoots
#axiom_core Uniformity.Density.typeOf_scale
#axiom_core Uniformity.Density.exists_anisotropic
-- **THIS CHAPTER'S OWN TERMINAL SUPPLIES (I.15–I.18).** I.17's Lean-core footprint IS the design
-- point (I.17's TEETH row): every open input is a HYPOTHESIS, never an axiom, so the capstone
-- assembly adds nothing to the trusted base.
#axiom_core LeanspecI.drainage_of_capstoneHypotheses
#axiom_core LeanspecI.decided_of_capstoneHypotheses
#axiom_core LeanspecI.uniformity_of_capstoneHypotheses
#axiom_core LeanspecI.totalMassOne_of_capstoneHypotheses
-- and this chapter's carriers, so a later resolution pass cannot smuggle an axiom into a `Prop`
#axiom_core LeanspecI.NS7Termination
#axiom_core LeanspecI.DecidedSliceAt
#axiom_core LeanspecI.MenuLawAt
#axiom_core LeanspecI.WindowPinningAt
#axiom_core LeanspecI.GenhnHEAt
#axiom_core LeanspecI.GenhnTow1At
#axiom_core LeanspecI.CapstoneHypotheses
#axiom_core LeanspecI.TypeOfFaithful

/-! ### NODE I.25 [gate] — THE CITE-FOOTPRINT GATE

Axiom hygiene under Part V: Lean core plus exactly the signed cites, nowhere else.

* **clause (i)** — every declaration NOT downstream of a gate-(b) import prints exactly Lean
  core. Enforced: that is what all 67 `#axiom_core` lines above assert, and the guard THROWS
  rather than prints.
* **clause (ii)** — every cite-conditional declaration prints Lean core plus exactly its signed
  cite axioms. The `#axiom_reg` form above is the enforcement shape; **the signed registry at
  composition time is EMPTY**, so it has no call sites yet. Expected first entries: C.94's
  `agnprw_termination` at the A-C.6 REDRAFT, C.66's FGMN axiom at the A-C.6 REDRAFT, B.42's
  `[GN15 Thm 2.3 + FGMN Thm 6.6]` axiom. ⚠ **Defect I-D11**: C.92's route left the axiom world
  at A-C.6 (option (1): `fgmn_calculus_exists` RETIRED, the class kept as a hypothesis carrier,
  "C.92 EXITS the gate-(b) queue"), so orchestrator item **O-4 is MOOT** — and the sixteen
  `[FGMNCalculus …]`-conditional §10 theorems are now conditional in a way `collectAxioms`
  cannot see. A hypothesis-form cite is invisible to this gate BY CONSTRUCTION; the honest
  compensating control is the instance-supply census, not the axiom census.
* **clause (iii)** — the FORBIDDEN list (`AX_cellRecursion`-family, quarry-quarantined under Q7;
  `Lean.ofReduceBool`, i.e. `native_decide`, stop-the-line per H.99's precedent; and any axiom
  not in the signed registry) is enforced by the SAME test, since with an empty registry
  "Lean core exactly" excludes all of them. The self-test below shows the guard has teeth. -/

-- The guard's own self-test: a deliberately non-core constant must be REJECTED. It is declared
-- and immediately fenced — nothing in this file or any other consumes it, and it is the only
-- `axiom` chapter I writes anywhere.
private axiom axchkSelfTestAxiom : True
private theorem axchkSelfTestConsumer : True := axchkSelfTestAxiom
-- If `#axiom_core LeanspecI.axchkSelfTestConsumer` is uncommented the build FAILS with
-- "AXCHK FAIL (I.25 clause (i)/(iii)): … depends on non-core axioms [axchkSelfTestAxiom]".
-- That is the gate's positive control, verified at composition (2026-08-16) and left commented
-- so the file stays green:
-- #axiom_core LeanspecI.axchkSelfTestConsumer
-- The registry form's behaviour on the same constant, also verified and left commented:
-- #axiom_reg LeanspecI.axchkSelfTestConsumer [axchkSelfTestAxiom]   -- PASSES (registered)
-- #axiom_reg LeanspecI.axchkSelfTestConsumer []                     -- FAILS  (unregistered)

end Gates

end LeanspecI

/-!
## RESUME

**LSPEC-I stage 0e COMPLETE (2026-08-16).** All 25 blueprint nodes are landed here: **12 signed
declarations** (7 `def` + 1 `structure` real bodies + 4 `theorem`s landed REAL per §11), **zero
`axiom` stubs** (chapter I signs no theorem it cannot prove at stub time — the one `axiom` in the
file is I.25's fenced positive control), zero `sorry`, zero `native_decide`, `autoImplicit` off,
and the §8 gates EXECUTED at `q = 2` AND `q = 3` (the `(1/3, 1/3, 1/3)` and `(3/8, 3/8, 1/4)`
triples, the three `undecidedCount` spot values, the `e > 1 ∧ f > 1` non-applicability proof, and
the two `n = 2` non-vacuity witnesses `DecidedSliceAt 2` / `MenuLawAt 2` PROVED), plus an
**enforced** AXCHK census of 67 capstone-facing constants — all Lean-core.
Build: `lake build Leanspec.ChapI`.

**The four load-bearing type-diffs this gate performed** (the reason it exists): the Display-A
`ladder` field types against LANDED `Ladder.LadderSupply` with `.lb1`/`.mp1` at the **A-E.2**
forms (`Nonempty (BlockSuite I)` / `Nonempty (MidPeelEmission B B')`) universe-polymorphically in
`uW`, and `.vartheta` at chapter D's **A-D.2** sitewise `HVarthetaRes`; the `a0` field is
`Iff.rfl`-pinned to the landed `UniformityStatementDecided`; the `a2` field binds landed
`DrainageAt`; and I.17 fires through landed `UniformityStatement.ofDecided`.

**Defects for the blueprint's dated-append queue (NOT patched there by this unit):** twelve,
I-D1 … I-D12, listed in full in the header. The three the orchestrator should read first:

1. **I-D1 (stop-the-line, `leanfinal`)** — `Uniformity.Density.Gauge.Wle` and
   `…VarthetaWConjunct` are DECLARED TWICE (ChapD/D55 + D63 vs ChapD/D62w), so the ChapD roll-up
   and the chapter-E deep-twist branch are mutually un-importable. **Chapter I cannot be landed
   in `leanfinal` at all until this is cured.**
2. **I-D6 (unsafe instruction)** — the A-C.1 addendum tells the resolution pass to type I.01
   against `NS7TerminationStatement`, which is MACHINE-REFUTED (proves `False`). Any agent that
   follows it lands an inconsistency.
3. **I-D9 (vacuous carrier)** — I.03's `(A1)`-admissibility clause is provably content-free
   (proved in the §4 gate), so `COND:A1_n`'s resolution today certifies the MENU only. Same
   genre as OM-4 FINDING 0, and it needs the same treatment: a re-sign, owner-gated.

**Remaining external actions:** (i) `import Leanspec.ChapI` is wired into
`leanspec/Leanspec.lean` **as a COMMENTED line with its reason** — wiring it live breaks
`lake build Leanspec` outright, because the root imports `Uniformity` (the D62w branch) and this
file must reach the E-side carriers (the D63 → D55 branch); machine-checked at this gate. One
uncommenting restores the standing gate the moment I-D1 is cured; (ii) I-D1's `leanfinal` cure, then
the ChapE/ChapF roll-up repairs of I-D2, then this file's import block reverts to the one-line
`import Uniformity` every other chapter uses; (iii) the owner re-signs I.10's field list (I-D3,
I-D4, I-D7, I-D8, I-D9, I-D10 are all field-list or carrier-strength events); (iv) the gate-(b)
signatures for the C.66/C.94 REDRAFTS, after which their consumers move from `#axiom_core` to
`#axiom_reg`; (v) as chapter I lands in `leanfinal`, retire each stub to the
`example : <type> := <name>` diff form per `Leanspec.lean`'s stub lifecycle.
-/
