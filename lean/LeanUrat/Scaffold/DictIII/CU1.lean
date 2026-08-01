/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Scaffold.DictIII.GMNReader
import LeanUrat.Scaffold.DictIII.Locality
import LeanUrat.Scaffold.DictIII.O2aOrder1
import LeanUrat.HC2.Defs
import LeanUrat.HC2.HK57
import LeanUrat.MovesT.V9_irrSat
import LeanUrat.MovesT.V3_accKeyDeg
import LeanUrat.MovesD.R7_runRealizer

/-!
# Scaffold/DictIII/CU1 — Theorem CU-1 (BP_III §1.8)

E-phase target file for units III-U1..U8 (module §1.8, Theorem CU-1 +
Corollary CU-1-LVL).  Source of record: CU1 §2 Thm CU-1.

Status at hand-off (unit III-U5, 2026-08-01): BLOCKED — see the record
below.  No declaration is landed; the verbatim blueprint statement is
preserved in the commented block (transcribing it weakened, or with invented
placeholder carriers for other units' owned definitions, would be a statement
change).  [III-U5 re-attempted at HEAD later this date (prover III-U5): the
blocker census is now down to the SINGLE unknown identifier `CU1Pins`
(III-H3, fenced) — exact compiler error reproduced against a freshly rebuilt
olean; refreshed record at the unit block.  Statement-side, everything else
elaborates; proof-side, III-U4 additionally remains unlanded.]

Status at hand-off (unit III-U7, re-run 2026-08-01, prover III-U7): LANDED
as a flagged rendering — `cu1_spanTotal` (per-site SPAN totality: EVERY
interior GMN child at the site extends the chain, via the III-U3c harvest
builder applied to the child's data plus the new dressing/tower-slot
assignment `EHist.harvestExtend`, to an `EWF` + `InteriorChain` + `ConsF`
chain — exactly `cu1`'s displayed per-instance rows at the extension), with
the supporting datum `InteriorChildAt` and the three extension legs, all
PROVED, no sorry, expected Lean-core footprint.  Ground 2 of the original
BLOCKED record (III-U3c construction unlanded) was CURED at the III-U3c
hand-off; ground 1 (elided §1.8 display) STANDS — the statements are this
unit's rendering from CU1 rev-5 §4 Corollary CU-1-ADEQ, flagged for
division-lead ratification (record at the unit section).  The ADEQ
realization clause ("Theorem CU-1 realizes it") is NOT claimed: it is
III-U5's conclusion vocabulary (`cu1`, BLOCKED), and the unit row's deps
line (III-U3c only) scopes it out — this unit produces the chain on which
`cu1` fires.  No [M]-row (GRB/FRESH/CU1Pins/OL6/OL1) is consumed anywhere
in the unit, so the III-U8 vacuity verdict does not touch it.

Status at hand-off (unit III-U1, 2026-08-01): PARTIAL — `machineProj` (the
§1.8 signature + docstring, VERBATIM) LANDS with the CU1 §2 π field mapping:
the Node → ENodeData re-key `nodeToE` with per-field lemmas, the root-datum
split (machine root read → (ψ̂₀, a₀); forced by W2, note at the unit
section), the σ.K/nextField dressing tower, and an `EWF` certificate proved
in full EXCEPT the W3 row, which carries this unit's ONE honest sorry:
W3 (interior μ ≥ 2 + a₀ ≥ 2) is NOT derivable from `HistoryCoherent` — the
interior discipline is the machine's HALTING/decision layer (O-1thr §1.4,
IrrHalts ⟺ μ_last = 1), not coherence, and a coherent countermodel shape is
on record at the proof site (trivial recentering-shaped successor reads;
cf. `HK25.H₂rec`).  REV2 finding 17 ("returns an EWF-certified subtype"
from coherence alone) over-promises at exactly that row; cure = architect
ruling (decision-layer hypothesis on `machineProj`, or W3 re-scoped).
PROVED: W1a/W1b/W2/W5, W4-dress, all four tower rows — the two cardinal
degree laws through a proved finite-field adjoin-root cardinality kernel
(`card_adjoin_root`).  This cures the III-A5 statement-site blocker and the
third of III-U5's four missing identifiers (census note at the U5 block).

Status at hand-off (unit III-U2, 2026-08-01): LANDED — `InteriorChain` (the
§1.8 signature, verbatim) with fieldwise access lemmas, + the CU-1 base case
k = 0 (`cu1_base_rootTrack`, `cu1_base_reductionFactor`), proved, Lean-core
footprint.  Source of record: `CU1_phaseB_verifybrief_rev5.md` §2 (clause
(i)'s k = 0 reading; V27 finding 3a — REALIZED is NOT asserted at the empty
history) and §3 "Base k = 0".  Dep: unit III-C9 (`ConsF`,
`DictIII/GMNReader.lean`).  This lands the FIRST of the four missing
identifiers recorded in the III-U5 block below; `CU1Pins`/`machineProj`/
`StateBinding` remain open there.

Rendering note for III-U2 (division-lead review; the III-C3 precedent in
Carriers.lean): BP_III §1.8 displays for this unit only the def SIGNATURE
`def InteriorChain (H : EHist p F) : Prop` with its docstring ("all nodes
continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2"), and NO Lean statement for the
base case (unit-table row 805 describes it in words).  The def BODY and the
two base-case theorems are therefore this unit's renderings — flagged, not
fenced.  Body sources: "continuing" = `sel ≠ none` (the (C1) docstring's
`sel = none` ⇔ terminal); "non-complete" = μ ≥ 2 at the selected pair (CU1
rev-5 §2: "EVERY node non-complete: μ_i ≥ 2 for all 1 ≤ i ≤ k"); `2 ≤ H.a0`
verbatim from the docstring.  ord_{ψ̂₀}(f̄) is carried at the §1.2
ι-interface as the (c0) read — `ConsF`'s first conjunct `R.rootOrd = H.a0`
with `R.rootOrd_spec : R.rootOrd = D.rootOrder`; the scaffold constructs no
GMN objects (§1.2 header), so the base clause is stated against the reader.

Status at hand-off (unit III-U3a, 2026-08-01): LANDED — `StateBinding` (the
clause-(ii) Prop over (M, H, lift); the §1.8 `cu1` display fixes its exact
signature through the conclusion clause `… ∧ StateBinding M H hlift`), with
the two [F.0] stage-data EQUALITY field pairs of the unit row (key = Lift,
width = μ_k), each split root/node per clause (ii)'s k = 0 / k ≥ 1 cases.
Source of record: `CU1_phaseB_verifybrief_rev5.md` §2 Thm CU-1 clause (ii).
Deps: III-H6 (`LiftFn`, landed in Hyps.lean); III-U1 is wave-ordering only
(the def reads no `machineProj`).  This lands the SECOND of the four missing
identifiers recorded in the III-U5 block below; `CU1Pins`/`machineProj`
remain open there.  Rendering notes at the unit section (division-lead
review requested, per the III-A1/III-U2 convention).

Status at hand-off (unit III-U3b, 2026-08-01): LANDED — the induction step's
candidate-pair identification (`CandidatePairAt` + the two order legs
`cu1_stepPair_le1`/`cu1_stepPair_ge2`, the assembly `cu1_stepPair`, the GD-2
instance display, and the positive gate at the landed `ol6Gate` world), all
PROVED, no sorry.  Source of record: `CU1_phaseB_verifybrief_rev5.md` §3,
base-k=1 items 1–2 and step items 1–3(d) — from Cons_f's (c1)/(c2) the read at
each continuing node identifies THE candidate pair (window principal face S,
dressing ψ̂) that III-U3c's harvest realizes.  Deps: III-A6 (reader interface,
`laws_pin_fields`, the `ol6Gate` world), III-G21 (`gd3_min`, the order-≤1
OL3min warrant — cited, graded carrier not consumed, per the III-A6a
precedent), III-H1/III-H2 (`GRB`/`FRESH`, FIRED in the ≥ 2 leg).  Rendering
notes at the unit section (division-lead review requested — BP_III §1.8
displays no III-U3b signature; the III-A1/III-U2/III-U3a convention).
HONESTY CROSS-REFERENCE: by the III-U8 gate verdict below
(`U8.grb_uninhabited`/`U8.fresh_uninhabited`), the ≥ 2 leg's hypothesis rows
are uninhabited AS DISPLAYED, so that leg is currently VACUOUS at every
(p, F); it is landed as the blueprint-specified consumption shape (the proof
fires the rows where CU1 §3 cites them and survives the pending §1.3 scope
repair verbatim).  The unit's non-vacuous face is the order-≤1 leg, gated
positively at `cu1_stepPair_gate` (Lean-core footprint).

Status at hand-off (unit III-U3c, 2026-08-01): PARTIAL — the unit's displayed
harvest CONSTRUCTION (`harvestNode`, the §4 node-builder formulas that the
III-U7 record below binds its own unblock order to), the creation-first
harvest kernel at the ι-interface consuming III-U3b's landed output carrier
(`identified_side_laws`, `harvestNode_matches`, `harvest_sel_reads` — step
item 3(d)'s 𝔈-face over `CandidatePairAt`, each field firing its named
source), the ASSEMBLED step shape `cu1_stepHarvest` (III-U3b's `cu1_stepPair`
∘ the harvest — what III-U5's `List.rec` consumes; rides `hGRB`/`hFRESH`,
so it inherits the III-U8 vacuity, per the U3b honesty note), and the
construction gate `harvestNode_gate` (builder reproduces the `ol6Gate`
world's node, machine-checked) are LANDED and PROVED, no sorry, Lean-core
footprint.  The unit's machine-side realization legs (item 3(c)'s (M6a)
harvest firing, item 4's REALIZED with the (M6c)(i) beyond-window clause,
the `machineProj`/M_𝐇·ν̂ tie) are BLOCKED — record at the unit section.
This cures the FIRST item of the III-U7 record's unblock order (the
node-builder vocabulary); the `MovesD.R7_runRealizer` import pins the
unit's §3.1 quarry (anchors at the unit section).
[UPDATE (re-run, 2026-08-01, after the III-U1 `machineProj` landing):
ground 2 of the blocked record ADVANCED at the carrier level — the
machine-side creation target `historySnoc` (M_𝐇·ν̂, the corpus face the
record anticipated) and its π-tie lemmas (`machineEHist_historySnoc_base/
a0/psi0/nodes/getElem?_of_lt/lastSlot`) plus the composed machine face
`harvestNode_machineFace` (harvest of THE identified pair = the machine
record's emitted 𝔈-face, REALIZED-free) are LANDED and PROVED, Lean-core
(footprint audit extended).  Grounds 1, 3, 4 (the (M6a)-row ruling, the
§1.3 GRB/FRESH scope repair, the (M6c)(i) prose pin) STAND — the unit
stays PARTIAL.]

Status at hand-off (unit III-U4, 2026-08-01): LANDED — the clause-(ii)
transport through the harvested step (CU1 rev-5 §3 step item 5), all PROVED,
no sorry: the transport kernel `stateBinding_of_lastRecord` ("frame recursion
= stage recursion" — both recursions are one-step-local, so the binding at
k + 1 needs exactly the new record's produced-key and width laws, no
clause-(ii) IH), the step faces `stateBinding_snoc` and
`stateBinding_historySnoc` (the latter at III-U3c's landed creation-target
carrier — the shape III-U5 consumes next to the `machineEHist_historySnoc_*`
π-ties), the assembled leg `cu1_stepBinding` (consumes III-U3c's
`cu1_stepHarvest` — "transport the state produced by U3c" — and DERIVES the
∀-`sel` width leg from the matched μ_{k+1}; rides `hGRB`/`hFRESH`, so the
III-U8 vacuity note applies to it verbatim), and the positive gate
`u4Gate_stateBinding` — the FIRST compiled inhabitant of III-U3a's
`StateBinding` (machine side ν₀gate + the PROVED `HK57.sideReads0_landing`
landing-key witness; the new `HC2.HK57` import pins the unit row's §3.3
quarry class).  THREE division-lead adjudication items at the unit section:
(1) the unit row's "(OL-6 … fire)" parenthetical is STALE against rev 5
(V27 finding 2b DELETED the OL-6 consumption — "OL-6 appears nowhere";
`OL6` is not consumed, dep III-H7c = wave-ordering only); (2) III-H3
(`CU1Pins`) is BLOCKED, so the (P-KEY)/(FR≡) pin OUTPUT is taken as the
named binders `hkeyPin`/`hwidthPin` at the pins' exact consumption slots —
III-U5 discharges them from `hpins` once III-H3 lands, nothing discharged
by fiat; (3) the valuation/shear/residue-tower leg's carrier awaits the
III-H3 repair (the III-U3a scoping note verbatim).

Status at hand-off (unit III-A5, re-run 2026-08-01 after III-U1): BLOCKED —
record at the end of the file, REFRESHED at this re-run.  The `MovesT`
imports pin that unit's quarry (`V9_irrSat`/`V3_accKeyDeg`, landed and green
— this file's compile gate certifies they resolve at HEAD).  Ground 2 of the
original record (statement site unlanded) is CURED: III-U1's `machineProj` +
fieldwise lemmas are landed above.  Ground 1 STANDS ALONE and is decisive:
BP_III.md at HEAD (1011 lines, unchanged) displays no III-A5 signature, and
the landed projection shows the re-key is NOT canonical (root-datum split:
machine node 0 ↦ (ψ̂₀, a₀), projected list = tail — the (accE, accF) product
and the saturation leg each split into a length-1 corner keyed at `a0` and a
length ≥ 2 leg keyed at the last projected node's `sel`), so statement
election is architect work, not transcription.

Status at hand-off (unit III-U6, 2026-08-01, RE-RUN same day): BLOCKED —
record below (between the III-U5 and III-U7 blocks; the same elision class
as III-U7, plus a statement defect inherited from the III-T14 seam).  The
re-run re-measured both grounds (verbatim `…` transcription error unchanged;
`cu1`/`realEquiv_of_m6` still unknown identifiers) and refreshed the census:
III-T10 `read_locality` LANDED since the first pass.  TWO support lemmas are
now landed and PROVED: `nstarMaj_readCeil_le` (the (N\*-MAJ) consumption leg
over the landed III-H4 row, Lean-core footprint) and
`readsOf_transfer_at_nstar_level` (the row's ONE `read_locality` top-site
application, sorry-free in body; footprint inherits `sorryAx` from the
honest BLOCKED(III-T10) row-supply sorry inside `read_locality`, tracked at
Locality.lean) — the `Locality` import pins both cites; the III-T14 census
stands as prose (the `Window` import was DROPPED at the III-U3c hand-off:
the cross-module `devCoeff` clash, compiled obstruction record at the
III-U3c section).

Status at hand-off (unit III-U8, 2026-08-01): BLOCKED, with the obstruction
COMPILED — record at the end of the file.  Ground 1: dep III-U5 (`cu1`) is
BLOCKED (record below).  Ground 2 (THE GATE VERDICT, wave-blocking, NOT
curable by landing the Wave-4 chain): the §1.3 rows `GRB p F` and `FRESH p F`
(Hyps.lean, III-H1/III-H2) are UNINHABITED as displayed —
`U8.grb_uninhabited` / `U8.fresh_uninhabited` /
`U8.u8Gate_hypStack_unsat_p2`, all PROVED, Lean-core footprint — so the
displayed `cu1` is VACUOUS and no positive gate can ever pass until the §1.3
rows receive a blueprint-level scope repair.  §4 line 930 ("U8 remains
mandatory before closure") therefore reads STOP-THE-LINE for Wave-4 closure.
-/

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Unit III-U1 — `machineProj` def + fieldwise lemmas (BP_III §1.8,
signature VERBATIM; src CU1 §2 π; Node → ENodeData re-key)

Unit row (BP_III §2 Wave 4, line 804): "`machineProj` def + fieldwise lemmas
| Node → ENodeData re-key | III-C2a, corpus MovesC | EASY | CU1 §2 π";
REV2 finding 17: "`machineProj` requires `HistoryCoherent` and returns an
`EWF`-certified subtype".  The §1.8 display fixes the SIGNATURE and docstring
verbatim (lines 556–559); the def BODY is this unit's rendering from the
source of record — `CU1_phaseB_verifybrief_rev5.md` §0′ "Machine dressings
and the projection π":

> "π(M) is the dressed 𝔈-history whose i-th node is the [F.1]/[F.2] emitted
> record of ν̂_i's harvest — explicitly: e := ê, h := ĥ, ℓ := ŵSide/ê (the
> side degree: the number of e-strides, = deg of the residual polynomial),
> (s, u) := the emitted initial-point pair, sel := (deg ψ̂, μ̂), inc := 1 iff
> the species is increment (⟺ ê·deg ψ̂ ≥ 2, the §1.2 species law = W2's
> value), dressing := ψ̂"

Rendering notes (division-lead review requested, per the III-A1/III-U2/
III-U3a convention):

* **Display adjustment (the Carriers.lean III-C1 class):** the `machineProj`
  def carries the `noncomputable` keyword (its value holds `Polynomial`/
  `Subfield.closure` data); no other token differs from the §1.8 display,
  docstring included.
* **Root datum vs. node records.**  A corpus `MovesC.History` opens with THE
  root read (`root_iff`: node 0 is species `root`, first and only first),
  while the 𝔈-carrier separates the root datum (ψ̂₀, a₀) from the node list.
  The re-key therefore maps machine node 0 to the root datum — base := its
  frame field σ.K, ψ̂₀ := its harvested residual ψ (monic irreducible by the
  node's own rows), a₀ := its multiplicity μ̂₀ — and machine nodes 1.. to
  𝔈-nodes via `nodeToE`.  This split is FORCED by W2: a root read may have
  e·g ≥ 2 with species `root` ≠ `increment`, so keying `inc` by the species
  law on the root record would refute W2; on the tail, species ∈
  {increment, recentering} (root_iff) and W1a/W1b/W2 are THEOREMS below.
* **The (s, u) pair.**  `s := ŝ₀` (the side's initial slot).  For `u`, the
  node records the RIGHT-endpoint height `ustar : ℚ` and the integer total
  side weight `gam` (γ-tie, `HistoryCoherent` clause 3: e·(STR·u\*) =
  γ − (s₀+wSide)·h).  The initial-point height on the STRETCHED integer
  lattice is (γ − s₀·h)/e = STR·u\* + ℓ·h — an exact integer division under
  the γ-tie — so `u := ((gam − s₀·h)/e).toNat`, the unique ℕ-valued
  emitted-height candidate on the recorded data ((C1) REV 2 declares domains
  ℤ≥0).  The def itself consumes NO coherence (π is defined for an ARBITRARY
  machine history, rev-4 re-cite P2 F-7); off the coherent domain `toNat`
  clips junk.
* **Dressing tower.**  `fld i` := the frame field σ.K of machine node i+1
  (= F_{i+1}, the field its dressing ψ̂_i lives over); beyond the recorded
  reads it continues with the LAST read's created field
  `σ.nextField zbar` (D.6), keeping every tower row honest at the seam.
  `psihat i` := node (i+1)'s residual ψ in range; junk dressing X − C 1
  off-range (monic, irreducible, ≠ X over any subfield).
* **EWF certificate.**  W1a/W1b/W2/W5, the W4 dressing row, and ALL FOUR
  tower rows are PROVED — the two cardinal degree laws via a finite-field
  adjoin-root cardinality lemma (`card_adjoin_root` below: |K(z̄)| =
  |K|^{deg ψ} for z̄ a unit root of the monic irreducible ψ, through
  `IntermediateField.adjoin`/`minpoly`/`Module.natCard_eq_pow_finrank`),
  fed by coherence's two transition legs (`TransitionCoreL.base.child_field`
  + `RegradeOf.nextField_eq`; `IsRecenteringCore.base`'s K-equality).
  **W3 is the unit's ONE honest sorry** — BLOCKED record at the proof site:
  it is not derivable from `HistoryCoherent`, and REV2 finding 17
  over-promises there.

NOT claimed: W3 (sorried, see the record), any III-A5 re-key content (its
own unit), the III-U5 assembly. -/

section UnitIIIU1

/-- III-U1 support (the tower cardinal degree laws' kernel): adjoining a root
    `z` of a monic irreducible `ψ` over a subfield `K` of a finite field
    grows cardinality by exactly `|K|^{deg ψ}` — `Subfield.closure`-face of
    `IntermediateField.adjoin.finrank` + `Module.natCard_eq_pow_finrank`. -/
private theorem card_adjoin_root {K : Subfield F} {ψ : Polynomial ↥K}
    (hmon : ψ.Monic) (hirr : Irreducible ψ) {z : F}
    (hz : Polynomial.eval₂ K.subtype z ψ = 0) :
    Nat.card ↥(Subfield.closure (↑K ∪ {z})) = Nat.card ↥K ^ ψ.natDegree := by
  have haev : (Polynomial.aeval z) ψ = 0 := by
    rwa [Polynomial.aeval_def]
  have hint : IsIntegral ↥K z := ⟨ψ, hmon, haev⟩
  have hmin : minpoly ↥K z = ψ :=
    (minpoly.eq_of_irreducible_of_monic hirr haev hmon).symm
  have hfin : Module.finrank ↥K ↥(IntermediateField.adjoin ↥K {z})
      = ψ.natDegree := by
    rw [← hmin]
    exact IntermediateField.adjoin.finrank hint
  have hcard : Nat.card ↥(IntermediateField.adjoin ↥K {z})
      = Nat.card ↥K ^ ψ.natDegree := by
    rw [← hfin]
    exact Module.natCard_eq_pow_finrank
  have hrange : Set.range ⇑(algebraMap ↥K F) = (↑K : Set F) := Subtype.range_coe
  rw [← hcard]
  refine Nat.card_congr (Equiv.setCongr ?_)
  rw [← IntermediateField.coe_toSubfield, IntermediateField.adjoin_toSubfield,
    hrange]

/-- Coefficients of the anchored residual, read off the recorded pattern
    (`hRanch`): `Ranch.coeff N = pat N` inside the window, `0` beyond. -/
private lemma node_ranch_coeff (m : MovesC.Node p F) (N : ℕ) :
    m.Ranch.coeff N = if N < m.wSide / m.e + 1 then m.pat N else 0 := by
  rw [m.hRanch]
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m.wSide / m.e + 1)) N m.pat]
  simp

private lemma node_ranch_ne_zero (m : MovesC.Node p F) : m.Ranch ≠ 0 := by
  intro h0
  have hc := node_ranch_coeff m (m.wSide / m.e)
  rw [h0, Polynomial.coeff_zero, if_pos (by omega)] at hc
  exact m.hpatTop hc.symm

private lemma node_ranch_natDegree_le (m : MovesC.Node p F) :
    m.Ranch.natDegree ≤ m.wSide / m.e := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [node_ranch_coeff, if_neg (by omega)]

/-- III-U1 fieldwise support, the re-key degree law (`hsel`'s window bound):
    `μ̂·deg ψ̂ ≤ ℓ = ŵSide/ê`, from `ψ^μ ∥ Ranch` (`hOrd`) and the pattern's
    exact top digit (`hpatTop`). -/
theorem node_mu_mul_g_le_ell (m : MovesC.Node p F) :
    m.μ * m.g ≤ m.wSide / m.e := by
  have hdeg := Polynomial.natDegree_le_of_dvd m.hOrd.1 (node_ranch_ne_zero m)
  rw [Polynomial.natDegree_pow, m.hψdeg] at hdeg
  exact hdeg.trans (node_ranch_natDegree_le m)

/-- III-U1 fieldwise support, side-degree positivity (`hl`): `1 ≤ ℓ`. -/
theorem node_one_le_ell (m : MovesC.Node p F) : 1 ≤ m.wSide / m.e :=
  (Nat.mul_pos m.hμ m.hg).trans_le (node_mu_mul_g_le_ell m)

/-- III-U1 fieldwise support, the dressing-fence law: a recorded residual is
    never the bare variable `X` (its selected residue root `z̄` is a UNIT of
    `F`, and `X`'s only root is 0). -/
theorem node_psi_ne_X (m : MovesC.Node p F) : m.ψ ≠ Polynomial.X := by
  intro hX
  have h0 := m.hzbarRoot
  rw [hX, Polynomial.eval₂_X] at h0
  exact Units.ne_zero m.zbar h0

/-- **Unit III-U1, the Node → ENodeData re-key** (CU1 §2 π, displayed field
    by field in the section header): the [F.1]/[F.2] emitted record of one
    machine read.  Law rows discharged from the node's own carrier rows +
    the degree lemmas above; NO coherence consumed (π is total on machine
    histories). -/
def nodeToE (m : MovesC.Node p F) : ENodeData where
  e := m.e
  h := m.h
  ℓ := m.wSide / m.e
  s := m.s0
  u := ((m.gam - (m.s0 : ℤ) * (m.h : ℤ)) / (m.e : ℤ)).toNat
  sel := some (m.g, m.μ)
  inc := decide (m.species = MovesC.ReadSpecies.increment)
  he := m.he
  hh := m.hh
  hcop := m.hcop
  hl := node_one_le_ell m
  hsel := by
    rintro gμ hgμ
    rw [Option.mem_def, Option.some.injEq] at hgμ
    subst hgμ
    exact ⟨m.hg, m.hμ, node_mu_mul_g_le_ell m⟩

/-! Fieldwise lemmas (the unit deliverable): each emitted 𝔈-field against its
recorded machine source, definitional. -/

@[simp] theorem nodeToE_e (m : MovesC.Node p F) : (nodeToE m).e = m.e := rfl
@[simp] theorem nodeToE_h (m : MovesC.Node p F) : (nodeToE m).h = m.h := rfl
@[simp] theorem nodeToE_ell (m : MovesC.Node p F) :
    (nodeToE m).ℓ = m.wSide / m.e := rfl
@[simp] theorem nodeToE_s (m : MovesC.Node p F) : (nodeToE m).s = m.s0 := rfl
@[simp] theorem nodeToE_u (m : MovesC.Node p F) :
    (nodeToE m).u = ((m.gam - (m.s0 : ℤ) * (m.h : ℤ)) / (m.e : ℤ)).toNat := rfl
@[simp] theorem nodeToE_sel (m : MovesC.Node p F) :
    (nodeToE m).sel = some (m.g, m.μ) := rfl
@[simp] theorem nodeToE_inc (m : MovesC.Node p F) :
    (nodeToE m).inc = decide (m.species = MovesC.ReadSpecies.increment) := rfl

/-- III-U1 tower carrier: level field of the projected history — the frame
    field of machine node i+1 in range; the LAST read's created D.6 field
    `σ.nextField z̄` beyond (so the tower rows stay honest at the seam). -/
def projFld (last : MovesC.Node p F) :
    Option (MovesC.Node p F) → Subfield F
  | some m => m.σ.K
  | none => last.σ.nextField last.zbar

/-- III-U1 tower dressing: node (i+1)'s residual ψ̂ in range ("dressing :=
    ψ̂", CU1 §2 π); junk monic irreducible `X − C 1` off-range (the (C1)
    convention "junk off-range"). -/
noncomputable def projPsihat (last : MovesC.Node p F) :
    (o : Option (MovesC.Node p F)) → Polynomial ↥(projFld last o)
  | some m => m.ψ
  | none => Polynomial.X - Polynomial.C 1

theorem projPsihat_monic (last : MovesC.Node p F)
    (o : Option (MovesC.Node p F)) : (projPsihat last o).Monic := by
  cases o with
  | some m => exact m.hψmonic
  | none => exact Polynomial.monic_X_sub_C 1

theorem projPsihat_irreducible (last : MovesC.Node p F)
    (o : Option (MovesC.Node p F)) : Irreducible (projPsihat last o) := by
  cases o with
  | some m => exact m.hψirr
  | none => exact Polynomial.irreducible_X_sub_C 1

theorem projPsihat_ne_X (last : MovesC.Node p F)
    (o : Option (MovesC.Node p F)) : projPsihat last o ≠ Polynomial.X := by
  cases o with
  | some m => exact node_psi_ne_X m
  | none =>
    show Polynomial.X - Polynomial.C 1 ≠ Polynomial.X
    intro heq
    have h0 := congrArg (fun q => Polynomial.coeff q 0) heq
    simp at h0

/-- W4-dress data at an in-range slot, in the generalized-scrutinee form the
    dependent match consumes (`subst` on the option). -/
private lemma projPsihat_dress (last m : MovesC.Node p F)
    (o : Option (MovesC.Node p F)) (ho : o = some m) :
    (projPsihat last o).Monic ∧ Irreducible (projPsihat last o) ∧
      (projPsihat last o).natDegree = m.g ∧ projPsihat last o ≠ Polynomial.X := by
  subst ho
  exact ⟨m.hψmonic, m.hψirr, m.hψdeg, node_psi_ne_X m⟩

/-- **Unit III-U1, the projected 𝔈-history** (the `machineProj` value): root
    datum from the root read (machine node 0), 𝔈-nodes = the tail re-keyed by
    `nodeToE`, tower = the recorded frame fields continued by the last read's
    D.6 field.  Consumes NO coherence — every structure row is a node-carrier
    fact (positivity, coprimality, dressing). -/
noncomputable def machineEHist (M : MovesC.History p F) : EHist p F where
  base := (M.nodes.head M.nonempty).σ.K
  psi0 := (M.nodes.head M.nonempty).ψ
  hpsi0 := ⟨(M.nodes.head M.nonempty).hψmonic, (M.nodes.head M.nonempty).hψirr⟩
  a0 := (M.nodes.head M.nonempty).μ
  ha0 := (M.nodes.head M.nonempty).hμ
  nodes := M.nodes.tail.map nodeToE
  fld := fun i => projFld (M.nodes.getLast M.nonempty) M.nodes[i + 1]?
  psihat := fun i => projPsihat (M.nodes.getLast M.nonempty) M.nodes[i + 1]?
  hpsihat := fun _ =>
    ⟨projPsihat_monic _ _, projPsihat_irreducible _ _, projPsihat_ne_X _ _⟩

/-! Fieldwise lemmas at the history level (root datum, node list, tower). -/

theorem machineEHist_base (M : MovesC.History p F) :
    (machineEHist M).base = (M.nodes.head M.nonempty).σ.K := rfl

theorem machineEHist_psi0 (M : MovesC.History p F) :
    (machineEHist M).psi0 = (M.nodes.head M.nonempty).ψ := rfl

theorem machineEHist_a0 (M : MovesC.History p F) :
    (machineEHist M).a0 = (M.nodes.head M.nonempty).μ := rfl

theorem machineEHist_nodes (M : MovesC.History p F) :
    (machineEHist M).nodes = M.nodes.tail.map nodeToE := rfl

theorem machineEHist_nodes_length (M : MovesC.History p F) :
    (machineEHist M).nodes.length = M.nodes.length - 1 := by
  show (M.nodes.tail.map nodeToE).length = _
  rw [List.length_map, List.length_tail]

/-- Indexwise re-key: 𝔈-node i of the projection is machine node i+1's
    emitted record (the `?`-total form). -/
theorem machineEHist_nodes_getElem? (M : MovesC.History p F) (i : ℕ) :
    (machineEHist M).nodes[i]? = Option.map nodeToE M.nodes[i + 1]? := by
  show (M.nodes.tail.map nodeToE)[i]? = _
  rw [List.getElem?_map, List.getElem?_tail]

/-- Indexwise re-key, inverse direction: a projected node comes from a
    machine node one slot up. -/
theorem machineEHist_node_inv {M : MovesC.History p F} {i : ℕ}
    {ν : ENodeData} (h : (machineEHist M).nodes[i]? = some ν) :
    ∃ hi : i + 1 < M.nodes.length, nodeToE (M.nodes[i + 1]'hi) = ν := by
  rw [machineEHist_nodes_getElem?] at h
  cases hm : M.nodes[i + 1]? with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
    rw [hm, Option.map_some, Option.some.injEq] at h
    obtain ⟨hi, hgm⟩ := List.getElem?_eq_some_iff.mp hm
    exact ⟨hi, by rw [hgm]; exact h⟩

theorem machineEHist_fld_of_lt (M : MovesC.History p F) {i : ℕ}
    (hi : i + 1 < M.nodes.length) :
    (machineEHist M).fld i = (M.nodes[i + 1]'hi).σ.K := by
  show projFld (M.nodes.getLast M.nonempty) M.nodes[i + 1]? = _
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem machineEHist_fld_of_ge (M : MovesC.History p F) {i : ℕ}
    (hi : M.nodes.length ≤ i + 1) :
    (machineEHist M).fld i
      = (M.nodes.getLast M.nonempty).σ.nextField
          (M.nodes.getLast M.nonempty).zbar := by
  show projFld (M.nodes.getLast M.nonempty) M.nodes[i + 1]? = _
  rw [List.getElem?_eq_none hi]
  rfl

/-- Tail nodes are never root reads (`root_iff`), so their species is
    increment or recentering — the split every W-row proof below cases on. -/
private lemma tail_species (M : MovesC.History p F) {i : ℕ}
    (hi : i + 1 < M.nodes.length) :
    (M.nodes[i + 1]'hi).species = MovesC.ReadSpecies.increment ∨
      (M.nodes[i + 1]'hi).species = MovesC.ReadSpecies.recentering := by
  cases hsp : (M.nodes[i + 1]'hi).species with
  | root => exact absurd ((M.root_iff (i + 1) hi).mp hsp) (by omega)
  | increment => exact Or.inl rfl
  | recentering => exact Or.inr rfl

/-- The D.6 residue-growth cardinality law at one recorded read:
    `|K(z̄)| = |K|^{deg ψ}` (the node's `hψmonic`/`hψirr`/`hzbarRoot` rows
    feed `card_adjoin_root`). -/
theorem node_card_nextField (m : MovesC.Node p F) :
    Nat.card ↥(m.σ.nextField m.zbar) = Nat.card ↥m.σ.K ^ m.ψ.natDegree :=
  card_adjoin_root m.hψmonic m.hψirr m.hzbarRoot

/-- Coherence's field step, both transition legs folded: the child frame
    field is the parent's D.6 created field (non-recentering leg:
    `TransitionCoreL.base.child_field` + `RegradeOf.nextField_eq`), or is
    UNCHANGED with `g = 1` (recentering leg: `IsRecenteringCore.base`'s
    K-equality + `hspecRec`). -/
private lemma coherent_step_K {M : MovesC.History p F}
    (hM : MovesC.HistoryCoherent M) {i : ℕ} (hi : i + 1 < M.nodes.length) :
    (M.nodes[i + 1]'hi).σ.K
        = (M.nodes[i]'(by omega)).σ.nextField (M.nodes[i]'(by omega)).zbar ∨
      ((M.nodes[i + 1]'hi).σ.K = (M.nodes[i]'(by omega)).σ.K ∧
        (M.nodes[i]'(by omega)).g = 1) := by
  obtain ⟨-, -, -, hstep⟩ := hM
  obtain ⟨hrec, hnonrec, -, -, -, -, -⟩ := hstep i hi
  by_cases hsp :
      (M.nodes[i]'(by omega)).species = MovesC.ReadSpecies.recentering
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hK, -, -, -⟩ := (hrec hsp).base
    exact Or.inr ⟨hK, ((M.nodes[i]'(by omega)).hspecRec hsp).2⟩
  · obtain ⟨-, σV, hreg, -, hcore⟩ := hnonrec hsp
    exact Or.inl (hcore.base.child_field.trans (hreg.nextField_eq _))

/-- **Unit III-U1, the EWF certificate** of the projection.  PROVED:
    W1a/W1b/W2 (species laws, from `hspecInc`/`hspecRec` + `root_iff` +
    the degree lemmas), W5 (every emitted record is continuing), the W4
    dressing row, and all four tower rows (inclusions + both cardinal degree
    laws, fed by `coherent_step_K` and `node_card_nextField`).  W3 is the
    unit's ONE honest sorry — BLOCKED record at the proof site. -/
theorem machineEWF (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) : EWF (machineEHist M) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- W1a: ℓ = 1, e ≥ 2 ⟹ inc (a steep one-stride read is an increment).
  · intro i ν hν _ _ he2
    obtain ⟨hi1, rfl⟩ := machineEHist_node_inv hν
    rw [nodeToE_inc, decide_eq_true_eq]
    rcases tail_species M hi1 with hsp | hsp
    · exact hsp
    · exfalso
      rw [nodeToE_e] at he2
      have he1 := ((M.nodes[i + 1]'hi1).hspecRec hsp).1
      omega
  -- W1b: ℓ = 1, e = 1 ⟹ ¬inc (an increment needs e·g ≥ 2, but μg ≤ ℓ).
  · intro i ν hν _ hl he1
    obtain ⟨hi1, rfl⟩ := machineEHist_node_inv hν
    rw [nodeToE_inc, decide_eq_false_iff_not]
    intro hsp
    have hgrow := (M.nodes[i + 1]'hi1).hspecInc hsp
    rw [nodeToE_e] at he1
    rw [nodeToE_ell] at hl
    rw [he1, one_mul] at hgrow
    have hle : (M.nodes[i + 1]'hi1).g
        ≤ (M.nodes[i + 1]'hi1).μ * (M.nodes[i + 1]'hi1).g :=
      Nat.le_mul_of_pos_left _ (M.nodes[i + 1]'hi1).hμ
    have hll := node_mu_mul_g_le_ell (M.nodes[i + 1]'hi1)
    rw [hl] at hll
    have hg1 : (M.nodes[i + 1]'hi1).g ≤ 1 := hle.trans hll
    omega
  -- W2: inc ⟺ e·g ≥ 2 (the §1.2 species law, both directions).
  · intro i ν g μ hν hsel
    obtain ⟨hi1, rfl⟩ := machineEHist_node_inv hν
    rw [nodeToE_sel, Option.some.injEq, Prod.mk.injEq] at hsel
    obtain ⟨hg, -⟩ := hsel
    rw [nodeToE_inc, nodeToE_e]
    constructor
    · intro hinc
      rw [decide_eq_true_eq] at hinc
      have hgrow := (M.nodes[i + 1]'hi1).hspecInc hinc
      rw [hg] at hgrow
      exact hgrow
    · intro hge
      rw [decide_eq_true_eq]
      rcases tail_species M hi1 with hsp | hsp
      · exact hsp
      · exfalso
        obtain ⟨he1, hg1⟩ := (M.nodes[i + 1]'hi1).hspecRec hsp
        rw [he1, one_mul, ← hg, hg1] at hge
        omega
  -- W3: NOT derivable from HistoryCoherent — the unit's one honest sorry.
  --
  -- BLOCKED(III-U1): W3 (interior μ ≥ 2; a₀ ≥ 2 at nonempty node lists)
  -- cannot be proved from `hM : HistoryCoherent M`.  Coherence's only
  -- μ-law is window containment (νᵢ₊₁.s0 + νᵢ₊₁.wSide ≤ νᵢ.μ), and a
  -- successor read with (e, g, μ, s0, wSide) = (1, 1, 1, 0, 1) — the
  -- recentering-shaped trivial read, IsRecenteringCore-transitionable —
  -- bounds νᵢ.μ ≥ 1 only.  Countermodel shape: a root read with μ̂₀ = 1
  -- followed by such trivial recenterings (cf. the compiled coherent
  -- recentering-ended history `HK25.H₂rec`, HC2/HK25_recGate.lean, whose
  -- ν₁rec already has μ = 1).  The interior discipline is the machine's
  -- HALTING layer — O-1thr §1.4, IrrHalts ⟺ μ_last = 1 (CU1 rev-5 row 18)
  -- — i.e. ReadsOf/decision content, NOT coherence; the 𝔈-side carries it
  -- as `InteriorChain` (III-U2), a SEPARATE hypothesis in `cu1`.  REV2
  -- finding 17 ("returns an EWF-certified subtype" from coherence alone)
  -- over-promises at exactly this row.  Cure = architect ruling: add the
  -- decision-layer hypothesis to `machineProj`'s displayed signature, or
  -- re-scope W3 out of the certificate (statement change, fenced above
  -- unit authority).  Honest sorry per the unit charge; every other EWF
  -- row is proved.
  · sorry
  -- W5: every emitted record is continuing (sel := some (deg ψ̂, μ̂)).
  · intro i ν _ hν
    obtain ⟨hi1, rfl⟩ := machineEHist_node_inv hν
    simp [nodeToE_sel]
  -- W4-dress: the level-i dressing IS node (i+1)'s residual, with its rows.
  · intro i ν g μ hν hsel
    obtain ⟨hi1, hto⟩ := machineEHist_node_inv hν
    have hg : g = (M.nodes[i + 1]'hi1).g := by
      rw [← hto, nodeToE_sel, Option.some.injEq, Prod.mk.injEq] at hsel
      exact hsel.1.symm
    subst hg
    exact projPsihat_dress (M.nodes.getLast M.nonempty) (M.nodes[i + 1]'hi1)
      M.nodes[i + 1]? (List.getElem?_eq_getElem hi1)
  -- towerBase: F_q = σ₀.K ≤ fld 0.
  · rcases Nat.lt_or_ge 1 M.nodes.length with h2 | h2
    · show (M.nodes.head M.nonempty).σ.K ≤ (machineEHist M).fld 0
      rw [machineEHist_fld_of_lt M (i := 0) h2, List.head_eq_getElem]
      rcases coherent_step_K hM (i := 0) h2 with hL | hR
      · rw [hL]
        exact Moves.Stage.le_nextField _ _
      · rw [hR.1]
    · have hpos : 0 < M.nodes.length := List.length_pos_of_ne_nil M.nonempty
      show (M.nodes.head M.nonempty).σ.K ≤ (machineEHist M).fld 0
      rw [machineEHist_fld_of_ge M (i := 0) (by omega)]
      have hlh : M.nodes.getLast M.nonempty = M.nodes.head M.nonempty := by
        rw [List.getLast_eq_getElem, List.head_eq_getElem]
        congr 1
        omega
      rw [hlh]
      exact Moves.Stage.le_nextField _ _
  -- towerStep: fld i ≤ fld (i+1) (transition legs; nextField at the seam).
  · intro i
    rcases Nat.lt_or_ge (i + 1) M.nodes.length with hi | hi
    · rcases Nat.lt_or_ge (i + 2) M.nodes.length with hi2 | hi2
      · rw [machineEHist_fld_of_lt M hi,
          machineEHist_fld_of_lt M (i := i + 1) hi2]
        rcases coherent_step_K hM (i := i + 1) hi2 with hL | hR
        · rw [hL]
          exact Moves.Stage.le_nextField _ _
        · rw [hR.1]
      · rw [machineEHist_fld_of_lt M hi,
          machineEHist_fld_of_ge M (i := i + 1) hi2]
        have hlast : M.nodes.getLast M.nonempty = M.nodes[i + 1]'hi := by
          rw [List.getLast_eq_getElem]
          congr 1
          omega
        rw [hlast]
        exact Moves.Stage.le_nextField _ _
    · rw [machineEHist_fld_of_ge M hi,
        machineEHist_fld_of_ge M (i := i + 1) (by omega)]
  -- towerBaseDegree: |F₁| = |F_q|^{deg ψ̂₀} (D.6 at the root read).
  · rcases Nat.lt_or_ge 1 M.nodes.length with h2 | h2
    · have hψn : (machineEHist M).psi0.natDegree
          = (M.nodes[0]'(by omega)).ψ.natDegree := by
        show (M.nodes.head M.nonempty).ψ.natDegree = _
        rw [List.head_eq_getElem]
      have hbase : Nat.card ↥(machineEHist M).base
          = Nat.card ↥(M.nodes[0]'(by omega)).σ.K := by
        show Nat.card ↥(M.nodes.head M.nonempty).σ.K = _
        rw [List.head_eq_getElem]
      rw [machineEHist_fld_of_lt M (i := 0) h2, hψn, hbase]
      rcases coherent_step_K hM (i := 0) h2 with hL | hR
      · rw [hL]
        exact node_card_nextField _
      · rw [hR.1, (M.nodes[0]'(by omega)).hψdeg, hR.2, pow_one]
    · have hpos : 0 < M.nodes.length := List.length_pos_of_ne_nil M.nonempty
      rw [machineEHist_fld_of_ge M (i := 0) (by omega)]
      have hlh : M.nodes.getLast M.nonempty = M.nodes.head M.nonempty := by
        rw [List.getLast_eq_getElem, List.head_eq_getElem]
        congr 1
        omega
      rw [hlh]
      exact node_card_nextField _
  -- towerStepDegree: |F_{i+2}| = |F_{i+1}|^{gᵢ₊₁} (D.6 at each read).
  · intro i ν g μ hν hsel
    obtain ⟨hi1, hto⟩ := machineEHist_node_inv hν
    have hg : g = (M.nodes[i + 1]'hi1).g := by
      rw [← hto, nodeToE_sel, Option.some.injEq, Prod.mk.injEq] at hsel
      exact hsel.1.symm
    subst hg
    rw [machineEHist_fld_of_lt M hi1]
    rcases Nat.lt_or_ge (i + 2) M.nodes.length with hi2 | hi2
    · rw [machineEHist_fld_of_lt M (i := i + 1) hi2]
      rcases coherent_step_K hM (i := i + 1) hi2 with hL | hR
      · rw [hL, ← (M.nodes[i + 1]'hi1).hψdeg]
        exact node_card_nextField _
      · have hg1 : (M.nodes[i + 1]'hi1).g = 1 := hR.2
        rw [hR.1, hg1, pow_one]
    · rw [machineEHist_fld_of_ge M (i := i + 1) hi2]
      have hlast : M.nodes.getLast M.nonempty = M.nodes[i + 1]'hi1 := by
        rw [List.getLast_eq_getElem]
        congr 1
        omega
      rw [hlast, ← (M.nodes[i + 1]'hi1).hψdeg]
      exact node_card_nextField _

/-- The projection requires exactly the corpus coherence evidence from which its
    positivity, coprimality, and dressing proofs are obtained. -/
noncomputable def machineProj (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) : {H : EHist p F // EWF H} :=
  ⟨machineEHist M, machineEWF M hM⟩

/-! Fieldwise lemmas at the `machineProj` interface (what III-A5/III-U5
consume): the value is `machineEHist M`, so every fieldwise lemma above
transports along `machineProj_val`. -/

@[simp] theorem machineProj_val (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1 = machineEHist M := rfl

theorem machineProj_base (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1.base = (M.nodes.head M.nonempty).σ.K := rfl

theorem machineProj_psi0 (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1.psi0 = (M.nodes.head M.nonempty).ψ := rfl

theorem machineProj_a0 (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1.a0 = (M.nodes.head M.nonempty).μ := rfl

theorem machineProj_nodes (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1.nodes = M.nodes.tail.map nodeToE := rfl

theorem machineProj_nodes_getElem? (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) (i : ℕ) :
    (machineProj M hM).1.nodes[i]? = Option.map nodeToE M.nodes[i + 1]? :=
  machineEHist_nodes_getElem? M i

theorem machineProj_nodes_length (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) :
    (machineProj M hM).1.nodes.length = M.nodes.length - 1 :=
  machineEHist_nodes_length M

end UnitIIIU1

/-! ## Unit III-U2, def half — the interior scoping (BP_III §1.8, signature verbatim) -/

/-- Interior scoping: all nodes continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2. -/
def InteriorChain (H : EHist p F) : Prop :=
  2 ≤ H.a0 ∧
    ∀ (i : ℕ) ν, H.nodes[i]? = some ν →
      ν.sel ≠ none ∧ ∀ gμ ∈ ν.sel, 2 ≤ gμ.2

/-- Fieldwise access, a₀-clause: an interior chain has a₀ ≥ 2 (CU1 rev-5 §2's
    standing hypothesis; at nonempty chains this is also W3's second leg). -/
theorem InteriorChain.a0_ge_two {H : EHist p F} (h : InteriorChain H) :
    2 ≤ H.a0 :=
  h.1

/-- Fieldwise access, continuing-clause: every node of an interior chain is
    continuing (`sel ≠ none`; terminal records are CU-2t's seam, excluded by
    the scoping — CU1 rev-5 §2 scope note (2)). -/
theorem InteriorChain.sel_ne_none {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν) :
    ν.sel ≠ none :=
  (h.2 i ν hν).1

/-- Fieldwise access, non-complete-clause: every selected multiplicity of an
    interior chain has μ ≥ 2 (complete last nodes, μ_k = 1, are the leaf seam
    routed by CU1 rev-5 §4's split — excluded here). -/
theorem InteriorChain.mu_ge_two {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ)) :
    2 ≤ μ :=
  (h.2 i ν hν).2 (g, μ) hsel

/-- Fieldwise access, selected-pair form of the continuing-clause: every node
    of an interior chain carries a selected pair, with μ ≥ 2 (the ∃-form the
    induction step consumes). -/
theorem InteriorChain.exists_sel {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν) :
    ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ := by
  cases hsel : ν.sel with
  | none => exact absurd hsel (h.sel_ne_none hν)
  | some gμ => exact ⟨gμ.1, gμ.2, rfl, h.mu_ge_two hν hsel⟩

/-! ## Unit III-U2, base half — CU-1 base case k = 0 (CU1 rev-5 §2/§3 "Base k = 0")

The brief's clause (i) at k = 0 reads (V27 finding 3a — REALIZED is not
defined at the empty history, so NO REALIZED claim is made): "the track root
state o_𝐇 of ψ̂₀ exists on f, i.e. ord_{ψ̂₀}(f̄) = a₀ ≥ 2, with reduction
factor ψ̂₀^{a₀}".  At the ι-interface the displayed equation is the (c0)
read.  Consumed: (c0) + the interior scoping's a₀ ≥ 2 — the brief's
"[Consumed: (c0); …]" list restricted to this unit's clause; ROOT-M is NOT
yet needed here, per the same list. -/

/-- CU-1 base case k = 0, clause (i) (CU1 rev-5 §3 "Base k = 0"): the root
    track of ψ̂₀ exists on f — the (c0)-read root order (ord_{ψ̂₀}(f̄) read
    through the ι-interface) equals a₀ and is ≥ 2.  No `H.nodes = []`
    hypothesis is consumed: (c0) is `ConsF`'s level-free first conjunct, so
    the k = 0 instance is the literal statement, and the root clause stays
    available along the whole chain (the assembly III-U5 uses it at its
    `List.rec` base). -/
theorem cu1_base_rootTrack {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hint : InteriorChain H) (hcons : ConsF f H D R) :
    R.rootOrd = H.a0 ∧ D.rootOrder = H.a0 ∧ 2 ≤ D.rootOrder := by
  have h1 : R.rootOrd = H.a0 := hcons.1
  have h2 : D.rootOrder = H.a0 := R.rootOrd_spec.symm.trans h1
  exact ⟨h1, h2, hint.a0_ge_two.trans_eq h2.symm⟩

/-- CU-1 base case k = 0, the reduction factor (CU1 rev-5 §3 "Base k = 0":
    "f̄ has the repeated irreducible factor ψ̂₀^{a₀} (a₀ ≥ 2), so the track
    of ψ̂₀ exists with root state o_𝐇, reduction factor ψ̂₀^{a₀}"): at the
    ι-interface the reduction factor's exponent is the (c0)-read root order —
    ψ̂₀^{ord_{ψ̂₀}(f̄)} = ψ̂₀^{a₀}, with exponent ≥ 2 (repeated, so the track
    exists).  The polynomial lives over the carrier's root level `H.base`;
    monicity and irreducibility of ψ̂₀ itself are `H.hpsi0`. -/
theorem cu1_base_reductionFactor {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hint : InteriorChain H) (hcons : ConsF f H D R) :
    H.psi0 ^ D.rootOrder = H.psi0 ^ H.a0 ∧ 2 ≤ D.rootOrder := by
  obtain ⟨-, h2, h3⟩ := cu1_base_rootTrack hint hcons
  exact ⟨by rw [h2], h3⟩

/-! ## Unit III-U3a — `StateBinding` (CU1 rev-5 §2 clause (ii); BP §1.8)

BP_III §1.8 displays NO standalone `def StateBinding` line; the definition's
exact SIGNATURE is fixed by the displayed `cu1` conclusion
(`… ∧ MovesJ.ReadsOf p F n f M ∧ StateBinding M H hlift`, §1.8 line 579) —
`StateBinding : MovesC.History p F → EHist p F → LiftFn p F → Prop` — and its
content by the unit row (line 806: "clause (ii)'s content as a Prop over
(M, H, lift) — [F.0] stage-data equality fields (key = Lift, width = μ_k)").
As with III-A1 (`recoverEHist`, O2aOrder1.lean) and III-U2 above, the unit is
a DEFINITION whose body is rendered from the source display — CU1 rev-5 §2,
Theorem CU-1 clause (ii):

> "(ii) (state binding — the old F5, carried as a clause.)  The state o_𝐇
> (the root state at k = 0; the state of M_𝐇 at k ≥ 1) has frame equal to
> the [F.0] stage frame over (f, Θ(𝐇)): its key is Φ_{o_𝐇} = Lift_k(Θ(𝐇));
> its valuation, shear, and residue tower are the §1.1 recursion over M_𝐇's
> records and 𝒫 ((M4)), which under (P-KEY)/(FR≡) are the stage's [F.0] data
> over Θ(𝐇); and its window width is W_{o_𝐇} = a₀ (k = 0) resp. μ_k (k ≥ 1)
> — §1.4's definition instantiated at the matched records."

The unit row scopes the Prop's fields to exactly the two EQUALITY legs (key,
width): the valuation/shear/residue-tower leg is the §1.1 recursion over M's
own records — machine-side definitional content whose [F.0] identification is
(P-KEY)/(FR≡) pin content, consumed by unit III-U4, never a field here.
Rendering notes (division-lead review requested, per the III-A1 convention):

* **The state after M, in corpus vocabulary.**  A corpus history records the
  frame σ AT each read; the state o_𝐇 REACHED after the last read carries no
  recorded `Stage`.  Its produced key is exactly what the corpus law
  `MovesC.LandingKey` pins to the recorded data of the final read ("supplies
  the FINAL read's landing key", MovesC/Defs.lean blocker 56 — for interior
  nodes the same produced key is the NEXT frame's `σ.Φ` via coherence's
  `IsNodeLift` clause, so `LandingKey` is the uniform final-state idiom), and
  its standing window vertex is the final read's recorded `μ` (coherence and
  `TransitionAdmissible` compare every appended read against `νp.μ`).  So the
  key legs read `LandingKey (M.nodes.getLast M.nonempty) (…)` and the width
  legs read `(M.nodes.getLast M.nonempty).μ = …`.
* **Lift indexing = the landed OL1/pROOT slot convention** (Hyps.lean,
  III-H6): the `LiftFn` level argument is the 0-based Lean dressing slot —
  display Lift_j (j ≥ 1) applied to ψ̂_j is `lift (j−1) (c.psihat (j−1))`
  (OL1's `lift i (c.psihat i)`, i < slopes.length ⟷ j = i+1 ≥ 1), and
  display Lift₀(ψ̂₀) is `lift 0 c.psi0` (the §1.3 pROOT display).  Hence at
  k = 0 (`H.nodes = []`) the key leg reads `hlift 0 H.psi0`, and at
  `H.nodes.length = k + 1` it reads `hlift k (H.psihat k)` — display
  Lift_{k+1}(Θ(𝐇)) at the top dressing.  `Theta` carries `psi0`/`psihat`
  UNCHANGED from `H` (III-C6b), so the fields read them off `H` directly;
  the coefficientwise tower inclusion is III-H6's `CoeHead` bridge, exactly
  as in OL1.
* **Guards.**  The k = 0 legs are guarded by `H.nodes = []`, the k ≥ 1 legs
  by `H.nodes.length = k + 1` (+ the last node's selected pair read through
  `∀ gμ ∈ ν.sel`, the W4/`hsel` membership idiom).  On a terminal last node
  (`sel = none`) the width leg is vacuous — clause (ii) is stated at INTERIOR
  chains (`cu1`'s `InteriorChain` hypothesis, III-U2 above, forces
  `sel ≠ none`); the Prop itself stays total over (M, H, lift), as the
  blueprint signature requires. -/

/-- **Unit III-U3a** (BP_III §2 Wave 4 row 806; src CU1 rev-5 §2 clause (ii)):
    CU-1's state-binding clause as a Prop over `(M, H, lift)` — the [F.0]
    stage-data EQUALITY fields for the state reached after `M`, against the
    stage frame over `(f, Θ(H))`:

    * **key = Lift** (`key_root`/`key_node`): the FINAL read's landing key —
      `MovesC.LandingKey` at `M`'s last recorded node — is Lift_k(Θ(𝐇)):
      `hlift 0 H.psi0` at k = 0, resp. `hlift k (H.psihat k)` at
      `H.nodes.length = k + 1` (the landed OL1/pROOT slot convention).
    * **width = μ_k** (`width_root`/`width_node`): the standing window vertex
      after the final read — `M`'s last node's recorded `μ` — is `H.a0` at
      k = 0, resp. the last 𝔈-node's selected μ_k at k ≥ 1.

    Clause (ii)'s valuation/shear/residue-tower leg is the §1.1 recursion over
    `M`'s own records; its [F.0] identification is (P-KEY)/(FR≡) pin content,
    consumed by unit III-U4 — not a field here (unit-row scoping). -/
structure StateBinding (M : MovesC.History p F) (H : EHist p F)
    (hlift : LiftFn p F) : Prop where
  key_root : H.nodes = [] →
    MovesC.LandingKey (M.nodes.getLast M.nonempty) (hlift 0 H.psi0)
  key_node : ∀ (k : ℕ), H.nodes.length = k + 1 →
    MovesC.LandingKey (M.nodes.getLast M.nonempty) (hlift k (H.psihat k))
  width_root : H.nodes = [] → (M.nodes.getLast M.nonempty).μ = H.a0
  width_node : ∀ (k : ℕ) (ν : ENodeData), H.nodes.length = k + 1 →
    H.nodes[k]? = some ν → ∀ gμ ∈ ν.sel,
      (M.nodes.getLast M.nonempty).μ = gμ.2

/-! ## Unit III-U3b — induction step, candidate-pair identification
(BP_III §2 Wave 4 row 807; src CU1 rev-5 §3 step)

Unit row: "induction step, candidate-pair identification (order ≤ 1 outright
via A6/G-layer; ≥ 2 fires hGRB + hFRESH) | (c1)/(c2) → window principal face
+ ψ̂; GD-2/GD-3 instances | III-A6, III-G21, III-H1, III-H2 | HARD |
CU1 §3 step".

**Transcription-rule adjudication (division-lead review flag, per the
III-A1/III-A6a/III-U2/III-U3a precedents):** BP_III §1.8 displays NO Lean
signature for III-U3b (its block displays `machineProj`/`InteriorChain`/`cu1`
only — units III-U1/U2/U5).  The rendering below is this unit's, designed
from the source of record — CU1 rev-5 §3, base-k=1 items 1–2 and step items
1–3(d): Cons_f's clause (c1) (the side of slope −h/e with d(S) = ℓ and the
recorded initial point) and clause (c2) (ord_{ψ̂}(R_λ(f)) = μ) identify, at
each continuing node, THE candidate pair (S, ψ̂) that unit III-U3c's harvest
realizes — flagged, not fenced.  Design notes:

* **`CandidatePairAt` renders "(S, ψ̂) is a candidate pair at o_𝐇"** (brief
  §3 base item 2 / step item 2) at the §1.2 semantic-data layer: S is a
  window principal face (`S ∈ D.principalSides i`) carrying the chain's
  requested slope; its `(e, h, ℓ, s, u)` match the node's ((c1)'s lowest-terms
  slope, degree, and positional clauses); the residual degree reads off `S.ℓ`
  (the GD-3 law); and the selected ψ̂'s multiplicity is the residual order
  ((c2) through `resOrd_spec`).  It is reader-free DATA — the pair is a
  polygon/residual object; the identification theorems bind it to the read
  `R.side i`.  The dressing itself is the chain's ψ̂_i by the CHOICE of pair
  (brief §3 step 3(d) "dressing equal by choice"); its degree/monicity laws
  are the carrier's W4 row (`EWF_dress`), consumed by III-U3c/III-U4, not
  re-stated here.
* **Index convention** (the III-A1 note): Lean read/node index `i` (0-based)
  ↔ the display's level i+1.  **The order split follows the landed (H1)
  row's own guard** (`GRB`, Hyps.lean: clauses keyed `2 ≤ i` on the same
  index that keys `D.principalSides i`): the ≤ 1 leg is the unit's "order
  ≤ 1 outright" face, the ≥ 2 leg fires the rows at `2 ≤ i` VERBATIM.  SEAM
  NOTE for the division lead: should (H1)'s `2 ≤ i` be re-keyed to display
  order (= Lean index + 1), this unit's split re-keys with it — the legs'
  union covers every index either way, so `cu1_stepPair` is stable.
* **The ≤ 1 leg consumes only the III-A6 reader-law interface**
  (`side_spec`/`side_unique`/`resOrd_spec`/`resDeg_eq_sideDeg`): at order
  ≤ 1 these are PROVED for the III-A6b builder `gmnReaderOrder1` from the
  polygon API rows, `OL3min`'s semantic warrant being the landed III-G21
  G-layer theorem `gd3_min` (`Devid.lean`; graded carrier not consumed here,
  per the III-A6a precedent note).  The guard `_hi : i ≤ 1` displays the
  leg's claimed perimeter; the term is index-uniform because the scaffold
  reader carries those laws at every level BY TYPE (D-R2's honesty lives in
  A6's `c.slopes.length ≤ 1` construction restriction, not here).
* **The ≥ 2 leg genuinely FIRES the named rows** where the brief's step
  cites them: `hFRESH.childDetermined` supplies THE-ness of the read (the
  uniqueness leg routes through the (H2) row's ∃!, keyed to `H.nodes` by the
  interior scoping's continuing clause — `InteriorChain`, unit III-U2
  above), and `hGRB.residualNormalForm` supplies the GD-3 residual-degree
  law (its granted reader tied to `R` by the III-A6b reader-uniqueness
  lemma `GMNReader.laws_pin_fields`, O2aOrder1.lean).  The rows stay NAMED
  [M]-hypotheses — consumed as arguments, never discharged.  HONESTY (the
  III-U8 verdict below): as displayed the rows are UNINHABITED
  (`U8.grb_uninhabited`/`U8.fresh_uninhabited`), so this leg is currently
  VACUOUS at every (p, F); the proof is the blueprint-specified consumption
  shape and survives the pending §1.3 scope repair verbatim.
* **GD-2/GD-3 instances** (the row's proof-sketch column): the identified
  pair yields the GD-2 instance `D.principalSides i ≠ []` at the step's
  level (`cu1_stepPair_gd2_instance`); the GD-3 instance is
  `CandidatePairAt`'s residual-degree/multiplicity legs, displayed
  concretely by the gate.
* **Positive gate** (III-A6c/`ol6Gate` discipline): the identification fired
  at the landed one-node run world (`ol6GateHist`/`ol6GateData`/
  `ol6GateReader`/`ol6Gate_consF`, unit III-A9, O2aOrder1.lean) — THE pair
  at level 0 is `o2aGateSide`, machine-checked, on the ≤ 1 leg (which
  consumes no [M]-row; `ol6GateHist` is NOT interior — a₀ = 1, μ = 1 — and
  need not be: the identification predates the harvest's interior scoping).
  Satisfiability certificate ONLY (D-R2/D-R3 caveat, as at the precedents).

NOT claimed here: the harvest realization (III-U3c), state binding through
the step (III-U4), `cu1` itself (III-U5), and any inhabitation of the
consumed rows (III-U8's verdict stands). -/

/-- CU1 rev-5 §3 (base item 2 / step item 2): "(S, ψ̂) is a **candidate
    pair** at o_𝐇" — the level-`i` read's semantic content, at the §1.2
    data layer.  Legs, in order: window principal face; requested slope
    ((c1)'s side-of-slope); the (c1) fieldwise match; the GD-3
    residual-degree law; the ψ̂ multiplicity read ((c2)). -/
def CandidatePairAt (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (i : ℕ) (ν : ENodeData) (S : SideDatum) : Prop :=
  S ∈ D.principalSides i ∧
  HasRequestedSlope (Theta H) i S ∧
  (S.e, S.h, S.ℓ, S.s, S.u) = (ν.e, ν.h, ν.ℓ, ν.s, ν.u) ∧
  D.residualDegree i = S.ℓ ∧
  ∀ g μ, ν.sel = some (g, μ) → D.residualOrder i = μ

/-- THE-ness of the candidate pair, reader-law face ("a polygon has at most
    one side of a given slope", CU1 rev-5 §3 step 3(d)): any two candidate
    pairs at the same level coincide, by the GD-5 uniqueness row
    `side_unique` of any reader on the data. -/
theorem CandidatePairAt.unique {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {i : ℕ} {ν : ENodeData} {S T : SideDatum}
    (hS : CandidatePairAt f H D i ν S) (R : GMNReader f (Theta H) D)
    (hT : CandidatePairAt f H D i ν T) : S = T :=
  R.side_unique i S T hS.1 hT.1 hS.2.1 hT.2.1

/-- **Unit III-U3b, order-≤1 leg (outright via the A6/G-layer).**  At a read
    level `i ≤ 1`, Cons_f's clauses (c1)/(c2) at the continuing node `ν`
    identify THE candidate pair: the reader returns a side `S`; `S` is a
    window principal face at the requested slope, matching `ν` fieldwise,
    with the GD-3/ψ̂ residual data; and EVERY candidate pair is `S`.
    Consumed: `ConsF` (III-C9) + the III-A6 reader-law interface only — no
    [M]-row fires (section-header note on `_hi` and on III-G21's warrant
    role). -/
theorem cu1_stepPair_le1 {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hcons : ConsF f H D R) {i : ℕ} {ν : ENodeData}
    (hν : H.continuingPart.nodes[i]? = some ν) (_hi : i ≤ 1) :
    ∃ S, R.side i = some S ∧ CandidatePairAt f H D i ν S ∧
      ∀ T, CandidatePairAt f H D i ν T → T = S := by
  obtain ⟨-, hbind⟩ := (hcons : _ ∧ _)
  obtain ⟨S, hS, hfields, hsel⟩ := hbind i ν hν
  obtain ⟨hmem, hslope⟩ := (R.side_spec i S).mp hS
  have hpair : CandidatePairAt f H D i ν S :=
    ⟨hmem, hslope, hfields, R.resDeg_eq_sideDeg i S hS,
     fun g μ hgμ => (R.resOrd_spec i).symm.trans (hsel g μ hgμ)⟩
  exact ⟨S, hS, hpair, fun T hT => hT.unique R hpair⟩

/-- Interior scoping, list face (support for the ≥ 2 leg): on an interior
    chain every node is continuing, so the continuing part is ALL of `H` —
    `ConsF`'s per-node lookups and the (H2) row's `H.nodes` lookups
    coincide. -/
theorem InteriorChain.continuingPart_nodes {H : EHist p F}
    (hint : InteriorChain H) : H.continuingPart.nodes = H.nodes := by
  refine List.takeWhile_eq_self_iff.mpr ?_
  intro x hx
  obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
  exact Option.isSome_iff_ne_none.mpr
    (hint.sel_ne_none (List.getElem?_eq_some_iff.mpr ⟨hj, hxj⟩))

/-- **Unit III-U3b, orders-≥2 leg (fires hGRB + hFRESH).**  The same
    identification at a read level `2 ≤ i`, with the named [M]-rows consumed
    exactly where CU1 rev-5 §3 step items 1–3 cite them: the (H2) row
    `FRESH.childDetermined` supplies THE-ness of the read (uniqueness routed
    through its ∃!, keyed to `H.nodes` via the interior scoping), and the
    (H1) row `GRB.residualNormalForm` supplies the GD-3 residual-degree law
    (its granted reader tied to `R` by `laws_pin_fields`).  The rows stay
    NAMED hypothesis rows — consumed, never discharged.  HONESTY: currently
    vacuous at every (p, F) by the III-U8 verdict (section-header note). -/
theorem cu1_stepPair_ge2 {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hGRB : GRB p F) (hFRESH : FRESH p F)
    (hint : InteriorChain H)
    (hcons : ConsF f H D R) {i : ℕ} {ν : ENodeData}
    (hν : H.continuingPart.nodes[i]? = some ν) (hi : 2 ≤ i) :
    ∃ S, R.side i = some S ∧ CandidatePairAt f H D i ν S ∧
      ∀ T, CandidatePairAt f H D i ν T → T = S := by
  -- (c1)/(c2) supply the pair (Cons_f's clause at the node).
  have hbind := (hcons : _ ∧ _).2
  obtain ⟨S, hS, hfields, hsel⟩ := hbind i ν hν
  obtain ⟨hmem, hslope⟩ := (R.side_spec i S).mp hS
  -- Interior scoping: the continuing part is all of H.
  rw [hint.continuingPart_nodes] at hν
  -- (H2) FIRES: THE read at the child level (FRESH.childDetermined).
  have hex : ∃! T, R.side i = some T := hFRESH.childDetermined hcons hν
  -- (H1) FIRES: the GD-3 residual-degree law at orders ≥ 2
  -- (GRB.residualNormalForm's granted reader, tied to R by laws_pin_fields).
  obtain ⟨R', hR'⟩ :=
    hGRB.residualNormalForm (f := f) (c := Theta H) (D := D) i hi
  have hpin : R'.side = R.side := (R'.laws_pin_fields R).1
  have hresdeg : D.residualDegree i = S.ℓ := hR' S (by rw [hpin]; exact hS)
  have hpair : CandidatePairAt f H D i ν S :=
    ⟨hmem, hslope, hfields, hresdeg,
     fun g μ hgμ => (R.resOrd_spec i).symm.trans (hsel g μ hgμ)⟩
  refine ⟨S, hS, hpair, fun T hT => ?_⟩
  exact hex.unique ((R.side_spec i T).mpr ⟨hT.1, hT.2.1⟩) hS

/-- **Unit III-U3b, assembled step identification** (the shape III-U3c's
    harvest and III-U5's `List.rec` consume): at EVERY read level of an
    interior Cons_f chain, under the displayed rows, the clauses (c1)/(c2)
    identify THE candidate pair — order ≤ 1 by the outright leg, orders ≥ 2
    by firing the rows.  Hypotheses match `cu1`'s §1.8 signature (the rows
    ride as arguments through the whole induction). -/
theorem cu1_stepPair {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hGRB : GRB p F) (hFRESH : FRESH p F)
    (hint : InteriorChain H)
    (hcons : ConsF f H D R) {i : ℕ} {ν : ENodeData}
    (hν : H.continuingPart.nodes[i]? = some ν) :
    ∃ S, R.side i = some S ∧ CandidatePairAt f H D i ν S ∧
      ∀ T, CandidatePairAt f H D i ν T → T = S := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · exact cu1_stepPair_le1 hcons hν (by omega)
  · exact cu1_stepPair_ge2 hGRB hFRESH hint hcons hν hi

/-- GD-2 instance at the step's level (the unit row's proof-sketch column):
    the identified window principal face inhabits the principal-side list,
    so the polygon is non-empty at every continuing-node level — `OL2min`'s
    clause fired pointwise from the identification. -/
theorem cu1_stepPair_gd2_instance {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hGRB : GRB p F) (hFRESH : FRESH p F)
    (hint : InteriorChain H)
    (hcons : ConsF f H D R) {i : ℕ} {ν : ENodeData}
    (hν : H.continuingPart.nodes[i]? = some ν) :
    D.principalSides i ≠ [] := by
  obtain ⟨S, -, hpair, -⟩ := cu1_stepPair hGRB hFRESH hint hcons hν
  exact List.ne_nil_of_mem hpair.1

/-! ### Unit III-U3b positive gate (III-A6c/`ol6Gate` discipline):
the identification FIRED at the landed one-node run world —
satisfiability certificate only. -/

/-- Gate display, GD-3 face: `o2aGateSide` IS a candidate pair at the
    `ol6Gate` world's single continuing node — every leg of
    `CandidatePairAt` (membership, slope, fields, residual degree, ψ̂
    multiplicity) holds by computation on the concrete data. -/
theorem cu1_stepPair_gate_side :
    CandidatePairAt (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist ol6GateData
      0 ol6GateNode o2aGateSide := by
  refine ⟨by simp [ol6GateData], rfl, rfl, rfl, ?_⟩
  intro g μ hgμ
  have h : some ((1 : ℕ), (1 : ℕ)) = some (g, μ) := hgμ
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- Unit III-U3b gate, FIRED: the order-≤1 leg at the compiled `ol6Gate`
    binding (`ol6Gate_consF`, unit III-A9) — the ∃ is inhabited,
    machine-checked; no hypothesis of the fired leg is vacuous. -/
theorem cu1_stepPair_gate :
    ∃ S, ol6GateReader.side 0 = some S ∧
      CandidatePairAt (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist
        ol6GateData 0 ol6GateNode S ∧
      ∀ T, CandidatePairAt (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist
        ol6GateData 0 ol6GateNode T → T = S :=
  cu1_stepPair_le1 ol6Gate_consF rfl (Nat.zero_le 1)

/-- Gate display, THE-ness face: the gate's identified pair is UNIQUELY
    `o2aGateSide` — the ∀-clause of the identification fires on a genuine
    witness. -/
theorem cu1_stepPair_gate_unique :
    ∀ T, CandidatePairAt (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist
      ol6GateData 0 ol6GateNode T → T = o2aGateSide :=
  fun _ hT => hT.unique ol6GateReader cu1_stepPair_gate_side

/-! ## Unit III-U3c — induction step, harvest realizes ν̂_{i+1} (creation-first;
construction displayed): PARTIAL — construction + ι-face harvest kernel LANDED
below; the machine-side realization legs BLOCKED (record, 2026-08-01)

Unit row (BP_III §2 Wave 4, line 808): "induction step, harvest realizes
ν̂_{i+1} (creation-first; construction displayed) | harvest of THE identified
pair; (M6c)(i) beyond-window | deps III-U3b, III-T11 | HARD | CU1 §3 step".
Source of record: CU-1 rev 5 §3 Step (k → k+1)
(`lean/notes/openmath/CU1_phaseB_verifybrief_rev5.md` lines 435–519: this unit
= item 3(c)'s harvest-creation, item 3(d)'s fieldwise match, and item 4's
"(R1) beyond the window by (M6c)(i) at o_𝐇" leg) and §4's displayed
construction formulas (lines 528–535: "Lemma R's recovery formulas USED AS
DEFINITIONS — the construction precedes and replaces any appeal to recovery").

STATEMENT-PROVENANCE RECORD (the Window.lean III-T11a/T12 convention; the
III-A1/III-U2/III-U3a/III-U3b rendering-flag precedents of this file):

* BP_III §1.8 (lines 555–587) displays NO Lean statement for this unit — not
  even an elided `theorem …` slot (the block types `machineProj`/
  `InteriorChain`/`cu1` and elides `cu1_lvl`/`cu1_spanTotal`; the
  induction-step legs U3b/U3c/U4 are proof-internal to `cu1`'s assembly, "U5:
  List.rec on nodes; U2 base, U3b/c+U4 step", row 810).  There is nothing to
  transcribe and hence no exact compiler error to report; the failure class is
  III-T11b's (missing display), not III-T14m's (failing display).
* What IS display-pinned, and therefore landed per the DictIII completion
  convention (Devid.lean III-G18; Window.lean III-T12; this file's III-U2/
  III-U3a/III-U3b rendering notes): the unit row's own words "construction
  displayed"; the §4 display of the construction formulas; the peer III-U7
  record below, whose unblock order binds to "III-U3c's construction … it
  fixes the node-builder vocabulary this statement binds"; and the landed
  III-U3b output carrier `CandidatePairAt` (THE identified pair — this unit's
  charged input, "harvest of THE identified pair").  Landed, in order:
  - `harvestNode` — the §4 node-builder formulas VERBATIM on the landed
    carriers (`SideDatum` → `ENodeData`); the dressing coordinate "ψ̂ := ψ"
    has NO `ENodeData` face — it rides the `EHist.psihat` tower slot, whose
    assignment belongs to the chain-extension legs (III-U4/III-U7), per the
    landed carrier split;
  - `identified_side_laws` — the builder's seven law binders all HOLD at the
    identified pair (the §4 well-formedness checks, read off the (c1) tuple +
    the node's own carrier rows), so consumers instantiate with zero input;
  - `harvestNode_matches` — the creation-first FIELDWISE MATCH, step item
    3(d)'s 𝔈-face ("the construction precedes any recovery talk, and each
    𝔈-field is matched with a named source"; V27 finding 2a): the (c1)
    5-tuple [`CandidatePairAt`'s tuple leg], sel = (g, μ) by the choice of
    pair, inc = [e·g ≥ 2] on both sides [`EWF.w2`, the species law / W2];
    Lemma R is NOWHERE invoked;
  - `harvest_sel_reads` — the (c2)/dressing ties: μ IS the datum's residual
    order, g IS deg ψ̂_i [`EWF.w4dress`];
  - `cu1_stepHarvest` — the ASSEMBLED step shape for III-U5's `List.rec`:
    at every level of an interior Cons_f chain, under `cu1`'s displayed rows,
    THE identified pair exists (III-U3b's `cu1_stepPair`) and its harvest
    IS ν̂_{i+1} — creation first, then the match.  HONESTY: rides III-U3b's
    `hGRB`/`hFRESH` binders, so it inherits the III-U8 vacuity at every
    (p, F) until the §1.3 scope repair (the U3b honesty note verbatim); the
    row-free kernel legs above are its non-vacuous face;
  - `harvestNode_gate` — the construction gate: the builder REPRODUCES the
    `ol6Gate` world's node from its identified pair (`o2aGateSide`, g = μ =
    1), machine-checked.  The matcher's `EWF` hypothesis cannot fire at this
    world (a₀ = 1 — the gate world is deliberately NOT interior, per the U3b
    gate note), so the gate certifies the BUILDER's formulas only.
  Flagged for division-lead ratification as statements (nothing to be
  verbatim to).

-- BLOCKED(III-U3c): the REALIZATION half — the unit's machine-side legs — on
grounds each verified at this pin (2026-08-01):

1. Item 3(c)'s firing row, "(M6a) (harvest totality): o_𝐇 is REALIZED and
   non-halted, so (M6a) harvests ALL candidate pairs", has NO landed Lean
   rendering: the displayed `cu1` consumes `hGRB`/`hFRESH`/`hpins : CU1Pins`/
   `hOL6`/`hOL1`, of which `CU1Pins` (III-H3) is BLOCKED (`Hyps.lean`: `frEQ`
   row, `HC1.ReadFrame` arity defect, fenced), and `Window.lean`'s `M6ABHyps`
   (whose `m6a` row is REAL≡'s DIFFERENT (M6a): ReadsOf → CanRealizes) is
   BLOCKED on the `CanRealizes` arity defect.  Which row carries harvest
   totality is an architect ruling, fenced above this unit.
2. The creation target M_{𝐇′} := M_𝐇·ν̂_{k+1} (corpus face: `History.snoc`
   at a `MovesC.Node` carrying frame σ, i.e. the machine-side record whose
   𝔈-face `harvestNode` builds) and the tie π(M_{𝐇′}) = 𝐇′ need
   `machineProj` (III-U1, UNLANDED — the III-U5 census below) and the
   machine-side IH (REALIZED(f, M_𝐇), clause (ii) at k) — `cu1`'s own
   conclusion vocabulary, unlanded with it.
   [UPDATE (prover III-U3c re-run, 2026-08-01): ADVANCED at the carrier
   level after the III-U1 `machineProj` landing — the creation target
   (`historySnoc`) and its π-tie (`machineEHist_historySnoc_*`: root datum
   preserved, 𝔈-nodes = snoc of emitted records, prefix slots stable, the
   created slot = `nodeToE ν̂`) plus the composed face
   `harvestNode_machineFace` (harvest of THE identified pair = `nodeToE` of
   the machine node one slot up) are LANDED and PROVED below the kernel
   legs, Lean-core (they read `machineEHist`, NOT the W3-sorry'd
   certificate).  STILL blocked in this ground: coherence preservation
   across the snoc and the REALIZED IH — `cu1`'s conclusion vocabulary,
   unlanded with it.]
3. The ≥ 2-order supply of the step ("≥ 2 fires hGRB + hFRESH", row 807) is
   COMPILED-VACUOUS at this pin: the III-U8 gate verdict below proves
   `GRB p F`/`FRESH p F` uninhabited as displayed — stop-the-line for any
   machine-side statement consuming them, pending the §1.3 scope repair.  The
   kernel legs landed below consume NEITHER (only `CandidatePairAt` + the
   per-instance `EWF H` rows, which the verdict does not touch); only the
   assembled `cu1_stepHarvest` rides them, flagged above.
4. Item 4's "(R1) beyond the window by (M6c)(i) at o_𝐇": the supply is
   III-T11a's `m6c_beyondWindow_e1` (LANDED, `Window.lean`, at the EXPLICIT
   `e′ = 1` perimeter with the carried trio hσL/hsteep/species displayed —
   prose pin; see the obstruction note below for why the compiled anchor
   cannot live in THIS file) with the general form III-T11b BLOCKED (elided
   display); the
   leg itself fires inside REALIZED — blocked with grounds 1–2.  Fence
   carried forward: the HK-52 e′-stretch seam (BP §3.3 line 882) must NOT be
   silently crossed — an adjudicated machine-side statement displays
   `e′ = 1` + trio or waits on III-T11b.

UNBLOCK ORDER (BP §4 line 929 at the current census): III-U1 (`machineProj`)
+ the (M6a)-row ruling + the III-H3 repair + the §1.3 GRB/FRESH scope repair
(U8 verdict) → the machine-side III-U3c statement (its ι-face kernel below is
ready to consume, and III-U3b's identification already supplies its pair) →
III-U4 → III-U5. -/

section UnitIIIU3c

/-! CROSS-MODULE OBSTRUCTION, surfaced by this unit's gate (2026-08-01;
division-lead item, gate-blocking beyond this unit):
`LeanUrat.Scaffold.DictIII.devCoeff` is DOUBLY DECLARED — `GDOrder1.lean:50`
("Dependency def for unit III-G2") and `Devid.lean:72` ("Unit III-G1
(forward-provided dependency)"), token-identical bodies modulo binder names,
BOTH claiming unit-table row III-G1.  Consequence: any module importing both
chains fails AT IMPORT TIME —
    `import LeanUrat.Scaffold.DictIII.Devid failed, environment already
     contains 'LeanUrat.Scaffold.DictIII.devCoeff.match_1' from
     LeanUrat.Scaffold.DictIII.GDOrder1`
— here via `Locality` (→ `GDOrder1`) + `Window` (→ `Devid`); the clash was
masked until now by a stale pre-Devid `Window.olean` (rebuilt green this
date).  This file NEEDS `Locality` (the landed III-U6 `readCeil` support), so
the `Window` import is DROPPED and the (M6c)(i) supply is a prose pin:
`m6c_beyondWindow_e1`, `Window.lean` (III-T11a), gated green by that file's
own compile (`lake build LeanUrat.Scaffold.DictIII.Window`, this date).  The
dedup (delete one copy, re-point its consumers — the "dedup rule" that
Window.lean's §T13 header already cites for exactly this cluster) is G-track
territory: an architect/division-lead ruling, not performed here.  NOTE for
the wave plan: the future III-U5 assembly consumes BOTH chains (`readCeil`
via III-U6, the M6/REAL≡ seams via III-T14), so this dedup gates Wave-4
closure INDEPENDENTLY of the III-U8 verdict below. -/

/-! Compiled anchors for the III-U3c record: the §3.1 R7 run-start/
interior-node quarry (BP line 858) that the blocked machine-side legs will
consume.  ((M6c)(i): prose pin above, per the obstruction note.) -/

#check @LeanUrat.MovesD.interior_node_e_eq_one
#check @LeanUrat.MovesD.exists_run_start

/-- III-U3c support — extensionality of the landed 𝔈-node carrier on its DATA
fields: the five (c1) coordinates + sel + inc determine the record (the law
fields are propositional; proof irrelevance closes them).  Support lemma in
the T12 `lastRead_of_readsOf_snoc` class — no carrier redeclared. -/
theorem ENodeData.ext' {ν₁ ν₂ : ENodeData}
    (h1 : ν₁.e = ν₂.e) (h2 : ν₁.h = ν₂.h) (h3 : ν₁.ℓ = ν₂.ℓ)
    (h4 : ν₁.s = ν₂.s) (h5 : ν₁.u = ν₂.u)
    (h6 : ν₁.sel = ν₂.sel) (h7 : ν₁.inc = ν₂.inc) : ν₁ = ν₂ := by
  cases ν₁; cases ν₂
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- III-U3c support — node lookups transport from the continuing part to the
full history (`takeWhile` is a prefix; the `EWF.of_prefix` bookkeeping
reversed, done once — no interior hypothesis needed, unlike
`InteriorChain.continuingPart_nodes`): the W2/W4 rows fire at the
`ConsF`-indexed nodes. -/
theorem getElem?_of_continuingPart {H : EHist p F} {i : ℕ} {ν : ENodeData}
    (hν : H.continuingPart.nodes[i]? = some ν) :
    H.nodes[i]? = some ν := by
  have hpre : H.continuingPart.nodes <+: H.nodes := List.takeWhile_prefix _
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hν
  obtain ⟨t, ht⟩ := hpre
  rw [← ht, List.getElem?_append_left hi]
  exact hν

/-- **Unit III-U3c, the displayed harvest construction** (CU-1 rev-5 §4, the
node-builder formulas "USED AS DEFINITIONS", creation-first; the vocabulary
the III-U7 record binds to).  Field for field, the §4 display:

    (e, h) := the lowest-terms pair of −λ (the side's recorded slope pair);
    ℓ := d(S);   (s, u) := the initial point of S;
    sel := (deg ψ, μ);   inc := 1 iff e·deg ψ ≥ 2

on the landed carriers `SideDatum → ENodeData`.  The dressing "ψ̂ := ψ" rides
the `EHist.psihat` tower slot (chain-extension legs III-U4/III-U7), not this
record.  The law binders are `ENodeData`'s own rows read off the §4
well-formedness checks (lowest terms; d(S) ≥ 1; μ·deg ψ ≤ ℓ); at THE
identified pair they all hold — `identified_side_laws` below discharges
them. -/
def harvestNode (S : SideDatum) (g μ : ℕ)
    (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h) (hScop : Nat.gcd S.e S.h = 1)
    (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g) (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ) :
    ENodeData where
  e := S.e
  h := S.h
  ℓ := S.ℓ
  s := S.s
  u := S.u
  sel := some (g, μ)
  inc := decide (2 ≤ S.e * g)
  he := hSe
  hh := hSh
  hcop := hScop
  hl := hSl
  hsel := by
    rintro gμ hgμ
    rw [Option.mem_def, Option.some.injEq] at hgμ
    subst hgμ
    exact ⟨hg, hμ, hμg⟩

/-- The construction's species law, displayed for consumers: the harvested
`inc` bit is set exactly by "e·deg ψ ≥ 2" (the §4 formula's W2/species
face). -/
theorem harvestNode_inc_iff (S : SideDatum) (g μ : ℕ)
    (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h) (hScop : Nat.gcd S.e S.h = 1)
    (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g) (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ) :
    (harvestNode S g μ hSe hSh hScop hSl hg hμ hμg).inc = true ↔
      2 ≤ S.e * g :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- **Unit III-U3c, laws at THE identified pair**: the builder's seven law
binders all hold at a `CandidatePairAt` datum with selected pair (g, μ) —
the (c1) 5-tuple ties the side's fields to the node's own carrier rows
(`he`/`hh`/`hcop`/`hl`), and the node's `hsel` row supplies the (deg ψ, μ)
positivity and the μ·g ≤ ℓ window bound (the §4 checks "μ·g ≤ ℓ since
μ·deg ψ ≤ …").  Consumers instantiate `harvestNode` with zero extra input. -/
theorem identified_side_laws {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {i : ℕ} {ν : ENodeData} {S : SideDatum}
    (hpair : CandidatePairAt f H D i ν S)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ)) :
    1 ≤ S.e ∧ 1 ≤ S.h ∧ Nat.gcd S.e S.h = 1 ∧ 1 ≤ S.ℓ ∧
      1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ S.ℓ := by
  have hfields := hpair.2.2.1
  simp only [Prod.mk.injEq] at hfields
  obtain ⟨hfe, hfh, hfl, hfs, hfu⟩ := hfields
  have hlaws := ν.hsel (g, μ) hsel
  refine ⟨?_, ?_, ?_, ?_, hlaws.1, hlaws.2.1, ?_⟩
  · rw [hfe]; exact ν.he
  · rw [hfh]; exact ν.hh
  · rw [hfe, hfh]; exact ν.hcop
  · rw [hfl]; exact ν.hl
  · rw [hfl]; exact hlaws.2.2

/-- **Unit III-U3c, the creation-first fieldwise match** (CU-1 rev-5 §3 step
item 3(d)'s 𝔈-face: "the construction precedes any recovery talk, and each
𝔈-field is matched with a named source" — V27 finding 2a's requested
display): the harvest of THE identified pair IS the chain's node ν̂_{i+1}.
Named source per field, firing in order: (e, h, ℓ, s, u) = the side's
recorded data [(c1), `CandidatePairAt`'s tuple leg]; sel = (g, μ) by the
choice of pair; inc — the species law [`EWF.w2` at the transported node].
Lemma R is NOWHERE invoked (the match is fieldwise, per the source display).
The machine-side reading of "realizes" (REALIZED(f, M_𝐇·ν̂), (M6c)(i)
beyond-window) is the BLOCKED half — record above. -/
theorem harvestNode_matches {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} (hwf : EWF H)
    {i : ℕ} {ν : ENodeData} (hν : H.continuingPart.nodes[i]? = some ν)
    {S : SideDatum} (hpair : CandidatePairAt f H D i ν S)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ))
    (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h) (hScop : Nat.gcd S.e S.h = 1)
    (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g) (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ) :
    harvestNode S g μ hSe hSh hScop hSl hg hμ hμg = ν := by
  have hfields := hpair.2.2.1
  simp only [Prod.mk.injEq] at hfields
  obtain ⟨hfe, hfh, hfl, hfs, hfu⟩ := hfields
  refine ENodeData.ext' hfe hfh hfl hfs hfu hsel.symm ?_
  -- inc: the species law W2 at the node, transported to the full history
  have hget : H.nodes[i]? = some ν := getElem?_of_continuingPart hν
  have hiff := hwf.w2 i ν g μ hget hsel
  show decide (2 ≤ S.e * g) = ν.inc
  rw [hfe]
  cases hb : ν.inc
  · rw [hb] at hiff
    simp only [Bool.false_eq_true, false_iff, not_le] at hiff
    exact decide_eq_false (by omega)
  · rw [hb] at hiff
    simp only [true_iff] at hiff
    exact decide_eq_true hiff

/-- **Unit III-U3c, the harvested selection's semantic reads** (step item
3(d)'s (c2)/dressing ties: "sel: the factor is ψ̂_{k+1} by the choice of
pair, with machine multiplicity = ord_{ψ̂_{k+1}}(R_{λ_{k+1}}(f)) = μ_{k+1}
[(c2)], and g = deg ψ̂_{k+1}"): the harvested pair (g, μ) IS
(deg ψ̂_i, the datum's residual order at i) — μ by `CandidatePairAt`'s
multiplicity leg, g by the W4 dressing law. -/
theorem harvest_sel_reads {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} (hwf : EWF H)
    {i : ℕ} {ν : ENodeData} (hν : H.continuingPart.nodes[i]? = some ν)
    {S : SideDatum} (hpair : CandidatePairAt f H D i ν S)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ)) :
    D.residualOrder i = μ ∧ (H.psihat i).natDegree = g := by
  have hget : H.nodes[i]? = some ν := getElem?_of_continuingPart hν
  exact ⟨hpair.2.2.2.2 g μ hsel, (hwf.w4dress i ν g μ hget hsel).2.2.1⟩

/-- **Unit III-U3c, the assembled step shape** (what III-U5's `List.rec`
consumes at each step, joint with III-U3b): at every read level of an
interior Cons_f chain, under `cu1`'s displayed rows, THE identified pair
exists (`cu1_stepPair`, III-U3b) and its harvest — built by the displayed
constructor, creation-first — IS the chain's node ν̂_{i+1}.  HONESTY: rides
III-U3b's `hGRB`/`hFRESH` binders, hence inherits the III-U8 vacuity at
every (p, F) until the §1.3 scope repair (the U3b note verbatim); the
row-free kernel above is the unit's non-vacuous face. -/
theorem cu1_stepHarvest {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hwf : EWF H) (hGRB : GRB p F) (hFRESH : FRESH p F)
    (hint : InteriorChain H) (hcons : ConsF f H D R)
    {i : ℕ} {ν : ENodeData} (hν : H.continuingPart.nodes[i]? = some ν)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ)) :
    ∃ (S : SideDatum) (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h)
      (hScop : Nat.gcd S.e S.h = 1) (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g)
      (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ),
      R.side i = some S ∧ CandidatePairAt f H D i ν S ∧
      harvestNode S g μ hSe hSh hScop hSl hg hμ hμg = ν := by
  obtain ⟨S, hS, hpair, -⟩ := cu1_stepPair hGRB hFRESH hint hcons hν
  obtain ⟨hSe, hSh, hScop, hSl, hg, hμ, hμg⟩ := identified_side_laws hpair hsel
  exact ⟨S, hSe, hSh, hScop, hSl, hg, hμ, hμg, hS, hpair,
    harvestNode_matches hwf hν hpair hsel hSe hSh hScop hSl hg hμ hμg⟩

/-- Unit III-U3c construction gate (the `ol6Gate`/III-A6c discipline): the
builder REPRODUCES the gate world's node from its identified pair
(`o2aGateSide` with (g, μ) = (1, 1), the pair `cu1_stepPair_gate` returns) —
machine-checked, fields and species bit alike.  The matcher's `EWF`
hypothesis cannot fire at this world (a₀ = 1 — the gate world is
deliberately NOT interior, per the U3b gate note), so this gate certifies
the CONSTRUCTION's formulas; satisfiability certificate only. -/
theorem harvestNode_gate :
    harvestNode o2aGateSide 1 1 le_rfl le_rfl (Nat.gcd_self 1) le_rfl
      le_rfl le_rfl le_rfl = ol6GateNode := by
  refine ENodeData.ext' rfl rfl rfl rfl rfl rfl ?_
  decide

/-! ### Machine-side creation target (BLOCKED-record ground 2, ADVANCED
2026-08-01 after the III-U1 `machineProj` landing): the corpus face `M_𝐇·ν̂`
and its π-tie at the Lean-core `machineEHist` level.  The record above
anticipated exactly this carrier ("corpus face: `History.snoc` at a
`MovesC.Node`"); `machineEHist` consumes NO coherence (its header note), so
every tie below is sorryAx-FREE even while `machineProj`'s W3 certificate row
carries the III-U1 honest sorry.  What still rides the fenced rulings:
coherence preservation across the snoc (the machine-side IH / REALIZED
vocabulary, unlanded with `cu1`), and the (M6a)/(M6c)(i) firing legs —
grounds 1, 3, 4 of the record STAND. -/

/-- **Unit III-U3c, the machine-side creation target** `M_𝐇·ν̂_{k+1}` (CU-1
rev-5 §3 step item 3(c)'s creation, at the corpus carrier): the machine
history extended by one non-root record.  Scaffold-local name per the
`nodeToE` convention (the corpus declares no `History.snoc`); the `root_iff`
law is re-certified across the append — the new slot is non-root by the
`hm` binder, and slot 0 stays in the old prefix.  No coherence consumed. -/
def historySnoc (M : MovesC.History p F) (m : MovesC.Node p F)
    (hm : m.species ≠ MovesC.ReadSpecies.root) : MovesC.History p F where
  nodes := M.nodes ++ [m]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hjlt : j < M.nodes.length + 1 := by
      simpa using hj
    rcases Nat.lt_or_ge j M.nodes.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      exact M.root_iff j hlt
    · have hj' : j = M.nodes.length := by omega
      subst hj'
      simp only [List.getElem_concat_length]
      constructor
      · exact fun h => absurd h hm
      · intro h0
        exact absurd (List.eq_nil_of_length_eq_zero h0) M.nonempty

@[simp] theorem historySnoc_nodes (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (historySnoc M m hm).nodes = M.nodes ++ [m] := rfl

/-- The creation target keeps the machine root read: head transports across
the append (so the projected root datum below is UNCHANGED — clause (ii)'s
root leg at the carrier level). -/
theorem historySnoc_head (M : MovesC.History p F) (m : MovesC.Node p F)
    (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (historySnoc M m hm).nodes.head (historySnoc M m hm).nonempty
      = M.nodes.head M.nonempty := by
  show (M.nodes ++ [m]).head _ = _
  rw [List.head_append_left M.nonempty]

/-- π-tie, root datum (base field): π(M·ν̂) reads the SAME root frame. -/
theorem machineEHist_historySnoc_base (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (machineEHist (historySnoc M m hm)).base = (machineEHist M).base := by
  rw [machineEHist_base, machineEHist_base, historySnoc_head]

/-- π-tie, root datum (a₀ = root multiplicity): unchanged across creation. -/
theorem machineEHist_historySnoc_a0 (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (machineEHist (historySnoc M m hm)).a0 = (machineEHist M).a0 := by
  rw [machineEHist_a0, machineEHist_a0, historySnoc_head]

/-- π-tie, root datum (ψ̂₀): unchanged across creation.  `HEq` because
`psi0`'s type depends on the base field — propositionally equal by the base
tie, not definitionally (head-of-append does not reduce on an opaque node
list). -/
theorem machineEHist_historySnoc_psi0 (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    HEq (machineEHist (historySnoc M m hm)).psi0 (machineEHist M).psi0 := by
  show HEq ((historySnoc M m hm).nodes.head (historySnoc M m hm).nonempty).ψ
    ((M.nodes.head M.nonempty).ψ)
  rw [historySnoc_head]

/-- **π-tie, the creation itself** (the BLOCKED record's "tie π(M_{𝐇′}) =
𝐇′" at the node-list face): the projected 𝔈-nodes of M·ν̂ are the projected
𝔈-nodes of M with the emitted record `nodeToE ν̂` appended — the machine-side
snoc IS an 𝔈-side snoc, slot for slot. -/
theorem machineEHist_historySnoc_nodes (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (machineEHist (historySnoc M m hm)).nodes
      = (machineEHist M).nodes ++ [nodeToE m] := by
  rw [machineEHist_nodes, machineEHist_nodes, historySnoc_nodes,
    List.tail_append_of_ne_nil M.nonempty, List.map_append]
  rfl

/-- π-tie, prefix stability: every already-projected slot is untouched by
the creation (what III-U4's state transport reads at levels ≤ k). -/
theorem machineEHist_historySnoc_getElem?_of_lt (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root)
    {i : ℕ} (hi : i < (machineEHist M).nodes.length) :
    (machineEHist (historySnoc M m hm)).nodes[i]?
      = (machineEHist M).nodes[i]? := by
  rw [machineEHist_historySnoc_nodes, List.getElem?_append_left hi]

/-- π-tie, the created slot: the ONE new 𝔈-slot of π(M·ν̂) carries exactly
the emitted record of ν̂ — creation lands where the step needs it. -/
theorem machineEHist_historySnoc_lastSlot (M : MovesC.History p F)
    (m : MovesC.Node p F) (hm : m.species ≠ MovesC.ReadSpecies.root) :
    (machineEHist (historySnoc M m hm)).nodes[(machineEHist M).nodes.length]?
      = some (nodeToE m) := by
  rw [machineEHist_historySnoc_nodes]
  exact List.getElem?_concat_length

/-- **Unit III-U3c, harvest = the machine record's emitted 𝔈-face** (item
3(c)/(d)'s machine-side reading at the carrier level, REALIZED-free): at a
projected history, the harvest of THE identified pair IS `nodeToE` of the
machine node one slot up — `harvestNode_matches` composed with the
projection's indexwise re-key `machineEHist_node_inv`.  The
REALIZED/(M6a)/(M6c)(i) firing of this face stays BLOCKED per the record
(grounds 1, 3, 4). -/
theorem harvestNode_machineFace {f : Polynomial ℤ_[p]}
    {M : MovesC.History p F} {D : GMNData f (Theta (machineEHist M))}
    (hwf : EWF (machineEHist M)) {i : ℕ} {ν : ENodeData}
    (hν : (machineEHist M).continuingPart.nodes[i]? = some ν)
    {S : SideDatum} (hpair : CandidatePairAt f (machineEHist M) D i ν S)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ))
    (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h) (hScop : Nat.gcd S.e S.h = 1)
    (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g) (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ) :
    ∃ hi : i + 1 < M.nodes.length,
      harvestNode S g μ hSe hSh hScop hSl hg hμ hμg
        = nodeToE (M.nodes[i + 1]'hi) := by
  obtain ⟨hi, hface⟩ := machineEHist_node_inv (getElem?_of_continuingPart hν)
  refine ⟨hi, ?_⟩
  rw [harvestNode_matches hwf hν hpair hsel hSe hSh hScop hSl hg hμ hμg]
  exact hface.symm

end UnitIIIU3c

/-! ## Unit III-U4 — state binding through the harvested induction step
(BP_III §2 Wave 4 row 809; src CU1 rev-5 §3 step item 5)

Unit row: "state binding through the harvested induction step (OL-6 +
(P-KEY)/(FR≡) fire) | transport the state produced by U3c; frame recursion =
stage recursion | III-U3a, III-U3c, III-H3, III-H7c | MED | CU1 §3 (ii) leg".

STATEMENT-PROVENANCE RECORD (the III-U3b/III-U3c convention): BP_III §1.8
displays NO Lean statement for III-U4 — the induction-step legs U3b/U3c/U4
are proof-internal to `cu1`'s assembly ("U5: List.rec on nodes; U2 base,
U3b/c+U4 step", row 810).  There is nothing to transcribe and hence no exact
compiler error to report; the failure class is the missing-display one
(III-U3b's), not a failing display.  The rendering below is this unit's,
designed from the source of record — CU1 rev-5 §3, step item 5 (and base
item 6 for the k = 1 shape), `lean/notes/openmath/CU1_phaseB_verifybrief_rev5.md`:

> "5. *Clause (ii) at k + 1.* The state o_{𝐇′}'s key is ν̂_{k+1}'s produced
> key ((R4), (M4)); by (P-KEY) and step 3(d)'s formal fields it equals
> Lift_{k+1}(Θ(𝐇′)). Valuation/shear/tower: the §1.1 recursion over
> M_{𝐇′}'s records ((M4)) — the [F.0] stage data over Θ(𝐇′) under (FR≡)'s
> frame clause. Window width = μ_{k+1} (§1.4's definition at the last
> read's multiplicity, = the matched μ_{k+1}). NO run-decomposition lemma
> is consumed: OL-6 appears nowhere (V27 finding 2b — rev 1's 'OL-2a-6(b)
> at level k + 2' is deleted, not relocated). ∎"

Flagged for division-lead ratification, with THREE adjudication items:

* **OL-6 (III-H7c) discrepancy — the unit row's parenthetical is STALE
  against the source of record.**  The row reads "(OL-6 + (P-KEY)/(FR≡)
  fire)", but rev 5's step item 5 (quoted above) explicitly DELETED the
  OL-6 consumption (V27 finding 2b: "the state-level pins (FR≡)/(P-KEY)
  are the content OL-6's stage-birth proof route supplies, declared
  instead"; OL-6's consumer remains O-2a Theorem 2(D) = CU-2).  The
  rendering follows the source of record: `OL6` is NOT consumed below,
  and the dep III-H7c reads as wave-ordering only (the landed `OL6` row
  is untouched).  Should the division lead rule the ROW authoritative
  over the brief, an `hOL6` binder rides through `cu1_stepBinding`
  unchanged — additive, no statement weakened.
* **The pins CANNOT fire as the structure row: III-H3 (`CU1Pins`) is
  BLOCKED** (Hyps.lean §III-H3: row `frEQ`'s `HC1.ReadFrame` arity/sort
  defect, fenced above unit authority — the structure exists only inside
  a commented block, so it is not an available declaration).  Rendering:
  the pins' OUTPUT at exactly this unit's two consumption sites — the
  produced-key identification `LandingKey m (Lift_{k+1}(Θ(𝐇′)))` ((P-KEY)
  + step 3(d), under (FR≡)'s frame clause) and the machine width at the
  matched record (§1.4 at the matched μ_{k+1}) — is taken as the NAMED
  hypothesis binders `hkeyPin`/`hwidthPin`, at the slots `CU1Pins`'
  repaired rows will fill.  When III-H3 lands, III-U5 discharges these
  binders from its `hpins` argument; nothing is discharged by fiat here,
  and no pin content is invented (the binders are the §1.8 `cu1`
  conclusion's own `StateBinding` field shapes, landed at III-U3a).
* **Unit-row scoping carried from III-U3a:** clause (ii)'s
  valuation/shear/residue-tower leg has NO `StateBinding` field (the
  III-U3a rendering note: it is machine-side definitional content whose
  [F.0] identification is the (FR≡)-frame pin).  Its transport is
  therefore the `hkeyPin` binder's charge, not a proof obligation below;
  the Lean carrier for that leg awaits the III-H3 repair.

Landed, in order (all PROVED, no sorry):
  - `stateBinding_of_lastRecord` — THE TRANSPORT KERNEL ("frame recursion =
    stage recursion"): both the machine §1.1 frame recursion and the [F.0]
    stage recursion are ONE-STEP-LOCAL — the state after M′ reads only the
    final record — so clause (ii) at k + 1 needs exactly the new record's
    two laws (produced key at the top dressing slot; width at the matched
    multiplicity), and NO clause-(ii) IH: the binding transports through
    the step because the two recursions have the same one-step shape.
  - `stateBinding_snoc` — the step face M_{𝐇′} = M_𝐇·ν̂_{k+1},
    𝐇′ = 𝐇·ν_{k+1} (list-append rendering of the §3 step's creation
    target), reduced to the kernel.
  - `stateBinding_historySnoc` — the same face AT the landed creation-target
    carrier `historySnoc` (III-U3c's machine-side block above): the shape
    III-U5's step consumes next to the `machineEHist_historySnoc_*` π-tie
    family (π-ties = clause (i)'s projection at k + 1; this = clause (ii)).
  - `cu1_stepBinding` — the ASSEMBLED (ii) leg for III-U5's `List.rec`,
    joint with III-U3b/U3c: at the top level of an interior Cons_f chain,
    under `cu1`'s displayed rows, THE identified pair exists and its
    harvest IS ν_{k+1} (`cu1_stepHarvest`, III-U3c — "transport the state
    produced by U3c") AND the extended machine history binds the extended
    chain.  The §1.4 width leg is DERIVED here: the matched record's
    selected pair forces every `sel` member, so the machine width law
    reduces to the single matched μ_{k+1}.  HONESTY: rides III-U3b's
    `hGRB`/`hFRESH` binders, hence inherits the III-U8 vacuity at every
    (p, F) until the §1.3 scope repair (the U3b note verbatim); the
    row-free kernel above and the gate below are the unit's non-vacuous
    face.
  - `u4GateLift`/`u4GateMachine`/`u4GateHist`/`u4Gate_stateBinding` — the
    positive gate (`ol6Gate`/III-A6c discipline): the kernel FIRED at a
    compiled one-read world — machine side the HC2 gate node `ν₀gate`
    with its PROVED landing-key witness `HK57.sideReads0_landing`
    (LandingKey ν₀gate U31.fq, Lean-core; the §3.3 quarry class), 𝔈-side a
    one-node chain over F4 re-using `ol6GateNode`, lift = the constant
    U31.fq function.  This is the FIRST compiled inhabitant of
    `StateBinding` (unit III-U3a's Prop, landed there without a
    satisfiability certificate) — the binding's ∀-legs genuinely fire at
    k = 0+1.  Satisfiability certificate ONLY (D-R2/D-R3 caveat): the
    gate world is one read deep and NOT tied to any Cons_f data.

NOT claimed here: the machine-side realization legs (III-U3c's BLOCKED
half — (M6a) harvest firing, REALIZED, the `machineProj` tie), `cu1` itself
(III-U5), any inhabitation of `GRB`/`FRESH` (III-U8's verdict stands), and
the (FR≡)-frame valuation/shear/tower carrier (III-H3, adjudication item
above). -/

section UnitIIIU4

/-- **Unit III-U4, the transport kernel** (CU1 rev-5 §3 step item 5; "frame
recursion = stage recursion"): the state after `M′` reads ONLY the final
record — both the machine §1.1 frame recursion and the [F.0] stage recursion
are one-step-local — so the state binding at k + 1 follows from the new
record's two laws alone: `hkeyPin`, the produced key at the top dressing
slot (the (P-KEY)/(FR≡)-pin output, named binder per the section header —
III-H3 is BLOCKED), and `hwidthPin`, the §1.4 width at the matched record.
No clause-(ii) IH is consumed: the k-level binding rides through untouched,
which IS the recursion identification. -/
theorem stateBinding_of_lastRecord {M' : MovesC.History p F} {H' : EHist p F}
    {hlift : LiftFn p F} {m : MovesC.Node p F} {ν : ENodeData} {k : ℕ}
    (hlen : H'.nodes.length = k + 1)
    (hν : H'.nodes[k]? = some ν)
    (hlast : M'.nodes.getLast M'.nonempty = m)
    (hkeyPin : MovesC.LandingKey m (hlift k (H'.psihat k)))
    (hwidthPin : ∀ gμ ∈ ν.sel, m.μ = gμ.2) :
    StateBinding M' H' hlift := by
  have hne : H'.nodes ≠ [] := by
    intro h
    rw [h] at hlen
    exact absurd hlen (by simp)
  refine ⟨fun h => absurd h hne, ?_, fun h => absurd h hne, ?_⟩
  · intro k' hk'
    obtain rfl : k' = k := by omega
    rw [hlast]
    exact hkeyPin
  · intro k' ν' hk' hν'
    obtain rfl : k' = k := by omega
    rw [hν] at hν'
    obtain rfl : ν = ν' := Option.some.inj hν'
    rw [hlast]
    exact hwidthPin

/-- **Unit III-U4, the step face** (CU1 rev-5 §3 step 3(c)'s creation target
M_{𝐇′} := M_𝐇·ν̂_{k+1} and the chain extension 𝐇′ = 𝐇·ν_{k+1}, list-append
rendering): binding transports through the snoc — the appended machine
record is the final one and the appended 𝔈-node is the top one, so the
kernel applies at slot k = `H.nodes.length` (the landed OL1/pROOT 0-based
slot convention, III-U3a note).  The dressing tower slot `H'.psihat` is
`H'`'s own field (the III-U3c note: ψ̂ rides the tower, not the node
record). -/
theorem stateBinding_snoc {M M' : MovesC.History p F} {H H' : EHist p F}
    {hlift : LiftFn p F} {m : MovesC.Node p F} {ν : ENodeData}
    (hM' : M'.nodes = M.nodes ++ [m])
    (hH' : H'.nodes = H.nodes ++ [ν])
    (hkeyPin : MovesC.LandingKey m
      (hlift H.nodes.length (H'.psihat H.nodes.length)))
    (hwidthPin : ∀ gμ ∈ ν.sel, m.μ = gμ.2) :
    StateBinding M' H' hlift := by
  refine stateBinding_of_lastRecord (k := H.nodes.length) ?_ ?_ ?_
    hkeyPin hwidthPin
  · rw [hH']; simp
  · rw [hH']; simp
  · simp [hM']

/-- **Unit III-U4 at the landed creation target** (III-U3c's machine-side
carrier `historySnoc` = M_𝐇·ν̂_{k+1}, landed at the U3c machine-face block
above): the state after the CREATED machine history binds the extended
chain — `stateBinding_snoc` instantiated at `historySnoc_nodes`.  This is
the shape III-U5's step will consume next to `machineEHist_historySnoc_*`
(the π-tie family): π-ties give clause (i)'s projection at k + 1, this
gives clause (ii). -/
theorem stateBinding_historySnoc {M : MovesC.History p F} {H H' : EHist p F}
    {hlift : LiftFn p F} {m : MovesC.Node p F} {ν : ENodeData}
    (hm : m.species ≠ MovesC.ReadSpecies.root)
    (hH' : H'.nodes = H.nodes ++ [ν])
    (hkeyPin : MovesC.LandingKey m
      (hlift H.nodes.length (H'.psihat H.nodes.length)))
    (hwidthPin : ∀ gμ ∈ ν.sel, m.μ = gμ.2) :
    StateBinding (historySnoc M m hm) H' hlift :=
  stateBinding_snoc (historySnoc_nodes M m hm) hH' hkeyPin hwidthPin

/-- **Unit III-U4, the assembled (ii) leg** (what III-U5's `List.rec`
consumes jointly with III-U3b/U3c — "transport the state produced by U3c"):
at the top read level of an interior Cons_f chain, under `cu1`'s displayed
rows, THE identified pair exists and its harvest IS the top node ν_{k+1}
(`cu1_stepHarvest`, III-U3c), AND the extended machine history binds the
extended chain — the produced-key law at the top dressing slot (`hkeyPin`,
the (P-KEY)/(FR≡) pin output; section-header adjudication item) plus the
machine width at THE matched record (`hwidthPin` at the single matched
μ_{k+1}; the ∀-`sel` width leg is DERIVED from the match — §1.4's
"definition at the last read's multiplicity, = the matched μ_{k+1}").
HONESTY: rides `hGRB`/`hFRESH`, hence the III-U8 vacuity note
(section header) applies; the kernel and gate are the non-vacuous face. -/
theorem cu1_stepBinding {f : Polynomial ℤ_[p]} {H' : EHist p F}
    {D : GMNData f (Theta H')} {R : GMNReader f (Theta H') D}
    (hwf : EWF H') (hGRB : GRB p F) (hFRESH : FRESH p F)
    (hint : InteriorChain H') (hcons : ConsF f H' D R)
    {k : ℕ} (hlen : H'.nodes.length = k + 1)
    {ν : ENodeData} (hν : H'.nodes[k]? = some ν)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ))
    {M' : MovesC.History p F} {m : MovesC.Node p F} {hlift : LiftFn p F}
    (hlast : M'.nodes.getLast M'.nonempty = m)
    (hkeyPin : MovesC.LandingKey m (hlift k (H'.psihat k)))
    (hwidthPin : m.μ = μ) :
    (∃ (S : SideDatum) (hSe : 1 ≤ S.e) (hSh : 1 ≤ S.h)
      (hScop : Nat.gcd S.e S.h = 1) (hSl : 1 ≤ S.ℓ) (hg : 1 ≤ g)
      (hμ : 1 ≤ μ) (hμg : μ * g ≤ S.ℓ),
      R.side k = some S ∧ CandidatePairAt f H' D k ν S ∧
      harvestNode S g μ hSe hSh hScop hSl hg hμ hμg = ν) ∧
    StateBinding M' H' hlift := by
  have hνc : H'.continuingPart.nodes[k]? = some ν := by
    rw [hint.continuingPart_nodes]; exact hν
  refine ⟨cu1_stepHarvest hwf hGRB hFRESH hint hcons hνc hsel, ?_⟩
  refine stateBinding_of_lastRecord hlen hν hlast hkeyPin ?_
  intro gμ hgμ
  rw [hsel, Option.mem_def, Option.some.injEq] at hgμ
  subst hgμ
  exact hwidthPin

/-! ### Unit III-U4 positive gate (`ol6Gate`/III-A6c discipline): the kernel
FIRED at a compiled one-read world — the first inhabitant of `StateBinding`.
Machine side: the HC2 gate node `ν₀gate` (root species, μ = 1) with its
PROVED landing-key witness `HK57.sideReads0_landing : LandingKey ν₀gate
U31.fq` (the §3.3 quarry class this unit's row cites).  𝔈-side: a one-node
chain over F4 re-using the F-free node record `ol6GateNode` (sel = (1, 1),
matching ν₀gate.μ = 1), root datum (X, 1), constant dressing X − 1 (monic,
irreducible, ≠ X over ↥(⊤ : Subfield F4)).  Lift: constantly U31.fq, so the
top-slot produced key IS the witnessed landing key.  Satisfiability
certificate ONLY (D-R2/D-R3): one read deep, no Cons_f data attached. -/

/-- III-U4 gate lift: constantly `U31.fq` — the gate world's produced key at
    every slot. -/
noncomputable def u4GateLift : LiftFn 2 MovesJ.F4 :=
  ⟨fun _ _ => MovesJ.U31.fq⟩

/-- III-U4 gate, machine side: the one-read history `[ν₀gate]` (root read
    first and only first — ν₀gate is root species). -/
noncomputable def u4GateMachine : MovesC.History 2 MovesJ.F4 where
  nodes := [MovesJ.HK18.ν₀gate]
  nonempty := by simp
  root_iff := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- III-U4 gate, 𝔈-side: the one-node chain over F4 — node record
    `ol6GateNode` (F-free data, re-used from the III-A9 gate world), root
    datum (X, a₀ = 1), constant dressing X − 1. -/
noncomputable def u4GateHist : EHist 2 MovesJ.F4 where
  base := ⊤
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 1
  ha0 := le_rfl
  nodes := [ol6GateNode]
  fld := fun _ => ⊤
  psihat := fun _ => Polynomial.X - Polynomial.C 1
  hpsihat := fun _ =>
    ⟨Polynomial.monic_X_sub_C 1, Polynomial.irreducible_X_sub_C 1,
     fun h => one_ne_zero (Polynomial.C_eq_zero.mp (sub_eq_self.mp h))⟩

/-- Unit III-U4 gate, FIRED: the transport kernel produces a compiled
    `StateBinding` instance — the ∀-legs of unit III-U3a's Prop genuinely
    fire (key leg = the PROVED `HK57.sideReads0_landing` witness at the
    constant-lift top slot; width leg = ν₀gate.μ = 1 = the matched selected
    multiplicity), machine-checked.  First inhabitant of `StateBinding`. -/
theorem u4Gate_stateBinding :
    StateBinding u4GateMachine u4GateHist u4GateLift := by
  refine stateBinding_of_lastRecord (k := 0) (ν := ol6GateNode)
    rfl rfl rfl ?_ ?_
  · exact MovesJ.HK57.sideReads0_landing
  · rintro gμ hgμ
    have h : some ((1 : ℕ), (1 : ℕ)) = some gμ := hgμ
    obtain rfl : ((1 : ℕ), (1 : ℕ)) = gμ := Option.some.inj h
    rfl

end UnitIIIU4

/-! ## Unit III-U5 — `cu1` (BP_III §1.8): BLOCKED — the verbatim statement
does not elaborate; sole remaining unknown identifier `CU1Pins` (III-H3, fenced)

The verbatim blueprint statement is preserved in the commented block below; it
is NOT weakened or partially landed.  Status at this unit's own attempt
(prover III-U5, 2026-08-01, fresh census superseding the four-identifier
census of the earlier hand-off):

* -- BLOCKED(III-U5): transcribed VERBATIM into a scratch module importing
  this file (only the standing `variable {p} [Fact p.Prime] {F} [Field F]
  [Finite F]` line supplying the ambient binders, body `sorry`), rebuilt
  olean at HEAD (`lake build LeanUrat.Scaffold.DictIII.CU1`, green, this
  date), `lake env lean` reports exactly ONE error, at the binder
  `(hpins : CU1Pins p F)`:
      error: Function expected at
        CU1Pins
      but this term has type
        ?m.1
      Note: Expected a function because this term is being applied to the
      argument p
      Hint: The identifier `CU1Pins` is unknown ...
  `CU1Pins` is unit III-H3's owned declaration, itself BLOCKED (Hyps.lean
  §III-H3: statement defect in row `frEQ` — `HC1.ReadFrame p F` arity/sort
  mismatch, fenced above unit authority); the structure exists only inside
  Hyps.lean's commented block, so it is not an available declaration.
  Landing it here (or dropping/retyping the binder) would be another unit's
  owned declaration invented, resp. a statement change — both forbidden.
* CURED since the earlier census (verified by the same probe — NO other
  error is reported): `InteriorChain` (III-U2), `machineProj` (III-U1,
  its `EWF` certificate carrying the ONE honest W3 sorry, record at the
  unit section), `StateBinding` (III-U3a) — all landed in this file; all
  other vocabulary resolves (`EHist`/`EWF`/`Theta` from Carriers,
  `GMNData`/`GMNReader`/`ConsF` from GMNReader, `GRB`/`FRESH`/`LiftFn`/
  `OL1`/`OL6` from Hyps, `MovesC.History`/`MovesC.HistoryCoherent`/
  `MovesJ.ReadsOf` from the corpus).
* Beyond statement elaboration, the assembly proof this unit owns ("List.rec
  on nodes; U2 base, U3b/c + U4 step") also awaits unit III-U4 (state
  binding through the harvested step — grep over `LeanUrat/`: no III-U4
  declarations; its deps III-H3/III-H7c partly fenced), while the U2 base
  (`cu1_base_rootTrack`/`cu1_base_reductionFactor`) and the U3b/c step
  carriers (`cu1_stepPair`, `cu1_stepHarvest`) ARE landed above.  And the
  III-U8 verdict below stands: `GRB`/`FRESH` are uninhabited as displayed,
  so even a landed `cu1` would be VACUOUS pending the §1.3 scope repair.
  [UPDATE (prover III-U4, 2026-08-01): the U4 step leg is now LANDED above
  (`stateBinding_of_lastRecord`/`stateBinding_snoc`/`stateBinding_historySnoc`/
  `cu1_stepBinding`, all Lean-core) — the List.rec step's clause-(ii)
  supply exists.  Its `hkeyPin`/`hwidthPin` binders are the (P-KEY)/(FR≡)
  pin OUTPUT slots (III-H3 BLOCKED, unit-U4 section header): once `hpins`
  types, this unit discharges them from it.]
* Unblock order at this census: the III-H3 `frEQ` blueprint repair (types
  the `hpins` binder) → III-U5 re-runs as the List.rec assembly
  its row describes (+ the §1.3 GRB/FRESH scope repair for non-vacuity).

```
/-- THEOREM CU-1 (N-free realization + state binding), over the displayed rows:
    order-≤1 instances of GD-2/GD-3(min)/GD-6 outright; orders ≥ 2 via hGRB; plus
    hFRESH, the pins, OL6. Conclusion (i): a machine history M with
    machineProj M = 𝐇 and ReadsOf f M; (ii): the state frame after M equals the
    [F.0] stage data over Theta 𝐇 (key = Lift, width = μ_k). -/
theorem cu1 {n : ℕ} {f : Polynomial ℤ_[p]} (H : EHist p F) (hwf : EWF H)
    (hint : InteriorChain H)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (hcons : ConsF f H D R)
    (hGRB : GRB p F) (hFRESH : FRESH p F) (hpins : CU1Pins p F)
    (hOL6 : OL6 f (Theta H) D R)
    (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
    ∃ M : MovesC.History p F,
      ∃ hM : MovesC.HistoryCoherent M,
        (machineProj M hM).1 = H ∧
        MovesJ.ReadsOf p F n f M ∧ StateBinding M H hlift
```
-/

/-! ## Unit III-U6 — `cu1_lvl` (Corollary CU-1-LVL, the working-level
transfer; BP_III §1.8): BLOCKED — elided display; the consumed theorems are
unlanded, one on a statement defect the corollary's own conclusion inherits

STATEMENT-PROVENANCE RECORD (same discipline as the III-U7 record below and
the Window.lean §1.7 records):

* -- BLOCKED(III-U6): BP_III §1.8 displays this unit's theorem ONLY as the
  ellipsis
  ```
  /-- Corollary CU-1-LVL: the working-level transfer — consumes read_locality ONCE at
      the top site + realEquiv_of_m6 (⟸) + the NstarMaj row. -/
  theorem cu1_lvl … (hmaj : NstarMaj Nstar readCeil dress) …
  ```
  (blueprint lines 581–583) — there is NO verbatim blueprint statement to
  transcribe (REV2 finding 1's elision class, exactly as the III-U7 record
  below).  Exact compiler error at verbatim transcription into a scratch
  module (Lean 4.31, this pin, 2026-08-01): `error: expected token` at the
  first `…`.  Unit row (line 811): proof sketch = "ONE `read_locality`
  application at the top site + `realEquiv_of_m6`(⟸) + `NstarMaj`", deps =
  III-U5/III-T10/III-T14/III-H4, src = CU1 §2 CU-1-LVL.  The row has NO
  stmt/proof pre-split (contrast III-T12's "T12a stmt (EASY) / T12b proof" —
  the delegated-statement situation Window.lean's III-T12 record documents),
  so completing the statement from the source of record is fenced above this
  unit's authority; it is NOT weakened or partially landed here.

* Dependency census (`#check` probes in a scratch module at this pin,
  2026-08-01, imports `Hyps` + `Locality` + `Window`):
  - III-U5 `cu1`: `Unknown identifier `cu1`` — BLOCKED, record above (its
    four-identifier census, of which the III-U2 landing above cures exactly
    one, `InteriorChain`).
  - III-T10 `read_locality`: NOW LANDED (re-measured at the 2026-08-01
    re-run pass, which found the earlier census line stale on exactly this
    entry): `Locality.lean` holds the per-clause transfers (III-T7/T8/T9)
    AND the assembled Theorem 1 (D-14) at its verbatim §1.6 signature
    (`Locality.lean` §III-T10; `#check @read_locality` anchor below
    compiles).  CONDITIONALITY carried at the dep, not here: its proof
    discharges the assembled transfer through `read_locality_rows`
    (sorry-free) but supplies the `SiteLawRows` bundle by the honest
    BLOCKED(III-T10) sorry recorded at that proof site — so any consumer's
    axiom footprint includes `sorryAx` until the row supply is cured
    (architect escalation recorded there).  The §4 wave plan's "Checkpoint
    after T10: `read_locality` is CU-1-LVL's gate" (line 926) is thus
    passed at statement level; the consumption leg is compiled below.
  - III-T14 `realEquiv_of_m6`: `Unknown identifier `realEquiv_of_m6`` —
    units III-T14a/T14b are BLOCKED on the §1.7 display's own-conclusion
    defect at `MovesD.CanRealizes p F n f H` (Window.lean records; exact
    error on file there: `Application type mismatch: The argument p has
    type ℕ but is expected to have type MovesC.Node ?m.19 ?m.21 in the
    application MovesD.CanRealizes p`), NOT curable by dependency landing.
    CU-1-LVL's conclusion — the walk's visit on f_N, obtained from REAL≡
    (⟸) with REALIZED(f_N, M_𝐇) established FIRST (V27 finding 3f) —
    consumes exactly that defective side, so the SAME architect ruling (a
    typed history-level realizability predicate of arity (p F n f H)) gates
    this unit's eventual STATEMENT, not just its proof.
  - III-H4 `NstarMaj`: LANDED (`Hyps.lean`).  The display's one non-elided
    binder group `(hmaj : NstarMaj Nstar readCeil dress)` elaborates
    VERBATIM once its elided binders (`Nstar`, `dress`) are supplied —
    compiled anchor below.

* Statement content of record, for the eventual elaboration (source: CU1
  rev-5 brief `lean/notes/openmath/CU1_phaseB_verifybrief_rev5.md` §2,
  "Corollary CU-1-LVL"): 𝐇 interior with Cons_f(𝐇), k ≥ 1, and N ≥ L(M_𝐇) —
  in particular any N ≥ N\*(𝐇), by (N\*-MAJ); f_N := the decode of f's
  level-N box (MONIC of degree n, f ≡ f_N (mod p^N) by the §1 box display);
  then REALIZED(f_N, M_𝐇) holds, and the execution walk on f_N (the
  DEFINITION of "the canonical run of the machine on f at working level N")
  visits o_𝐇.  At k = 0 (any N ≥ 1): the walk starts at the root states of
  all tracks of f̄_N = f̄, among them o_𝐇.  Proof shape on record: ONE
  `read_locality` application at the top site transfers REALIZED(f, M_𝐇)
  (from `cu1` clause (i)) to REALIZED(f_N, M_𝐇) — one application suffices
  because `readCeil` is the max of all per-read ceilings (Lemma CEIL's audit
  is over ALL i < k); then `realEquiv_of_m6` (⟸) on f_N.  The (N\*-MAJ)
  reduction leg is landed below, PROVED from the III-H4 row alone.

* Unblock order: the T14m/T14a/T14b arity ruling (it types this unit's
  conclusion) → the III-U5 chain lands (III-T10 landed 2026-08-01, row
  supply pending at its own record) → architect displays the completed
  `cu1_lvl` statement → this unit re-runs as the three-cite assembly its
  row describes.

* RE-VERIFIED by the 2026-08-01 re-run pass (fresh scratch probes at this
  pin, per the trust boundary — comments are not ground truth): (a) the
  verbatim transcription of the §1.8 display still fails with the identical
  `error: expected token` at the first `…` (measured at the display's
  column 16, the character after `theorem cu1_lvl `); (b) `cu1` and
  `realEquiv_of_m6` are still `Unknown identifier`s at HEAD (both occur
  only inside commented BLOCKED records — this file's III-U5 block and
  Window.lean's III-T14a/T14b blocks respectively); (c) `NstarMaj`,
  `readCeil`, and now `read_locality` resolve (anchors below).  Verdict
  unchanged: BLOCKED on the elided display + the T14 own-conclusion arity
  defect; what IS newly compilable is the row's first cite, landed as the
  support theorem `readsOf_transfer_at_nstar_level` below. -/

/-! Compiled anchors for the III-U6 record: the landed III-H4 row, the read
ceiling it majorizes, and (since the 2026-08-01 re-run) the landed III-T10
transfer; the display's one non-elided binder group elaborates verbatim once
its elided binders are supplied. -/

#check @NstarMaj
#check @readCeil
#check @read_locality

example (Nstar : EHist p F → ℕ) (dress : EHist p F → MovesC.History p F)
    (_hmaj : NstarMaj Nstar readCeil dress) : True := trivial

/-- **III-U6 support (PROVED — the (N\*-MAJ) consumption leg of Corollary
CU-1-LVL).**  CU1 rev-5 §2 admits working levels "N ≥ L(M_𝐇) — in particular
any N ≥ N\*(𝐇), by (N\*-MAJ)": the corollary's SINGLE consumption of the
decision level reduces its `N ≥ N\*(𝐇)` entry point to the `readCeil`-form
bound that the ONE `read_locality` application (III-T10) will consume at the
top site.  Stated over the landed III-H4 row verbatim; any level function
satisfying (N\*-MAJ) may be substituted, per that row's docstring. -/
theorem nstarMaj_readCeil_le {Nstar : EHist p F → ℕ}
    {dress : EHist p F → MovesC.History p F}
    (hmaj : NstarMaj Nstar readCeil dress)
    (H : EHist p F) {N : ℕ} (hN : Nstar H ≤ N) :
    readCeil (dress H) ≤ N :=
  le_trans (hmaj H) hN

/-- **III-U6 support (the ONE `read_locality` application at the top site —
the row's first cite, compiled).**  CU1 rev-5 §2's transfer leg: at the
machine M_𝐇 = `dress H` and any working level `N ≥ N*(𝐇)`, a read of `f`
transfers to any `f' ≡ f (mod p^N)` (monic, degree n) — the level-N
congruence feeds the `readCeil`-level congruence that `read_locality`
(III-T10, landed) consumes, via `nstarMaj_readCeil_le` (the (N\*-MAJ) leg
above) and ideal-power antitonicity.  This is NOT `cu1_lvl` (that statement
is still elided in BP_III §1.8 and its conclusion is gated on the T14 arity
ruling — record above); it is the corollary's read_locality cite in
isolation, stated over landed vocabulary only.  Footprint honesty: consumes
`read_locality`, whose proof carries the honest BLOCKED(III-T10) row-supply
sorry — so this theorem's axiom audit shows `sorryAx` until III-T10's
`SiteLawRows` supply is cured (tracked at that record, not here). -/
theorem readsOf_transfer_at_nstar_level {n : ℕ} {f f' : Polynomial ℤ_[p]}
    {Nstar : EHist p F → ℕ} {dress : EHist p F → MovesC.History p F}
    (hmaj : NstarMaj Nstar readCeil dress)
    (H : EHist p F) (hcoh : MovesC.HistoryCoherent (dress H))
    {N : ℕ} (hN : Nstar H ≤ N)
    (hcong : ∀ k, (f - f').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ N)
    (hm' : f'.Monic) (hd' : f'.natDegree = n)
    (h : MovesJ.ReadsOf p F n f (dress H)) :
    MovesJ.ReadsOf p F n f' (dress H) :=
  read_locality hcoh
    (fun k => Ideal.pow_le_pow_right (nstarMaj_readCeil_le hmaj H hN) (hcong k))
    hm' hd' h

/-! ## Unit III-U7 — `cu1_spanTotal` (interior adequacy, per-site SPAN
totality — the ADEQ interior half; BP_III §2 Wave 4 row 812): LANDED as a
flagged rendering (re-run 2026-08-01, prover III-U7; supersedes the BLOCKED
record of the same date, whose census is preserved inside this record)

Unit row: "`cu1_spanTotal` (interior adequacy, per-site SPAN) | per-site
totality from the same harvest construction | deps III-U3c | MED | CU1 §4".
Source of record: CU1 rev-5 §4, Corollary CU-1-ADEQ
(`lean/notes/openmath/CU1_phaseB_verifybrief_rev5.md` lines 521–559).

STATEMENT-PROVENANCE RECORD (the III-U2/III-U3a/III-U3b/III-U3c convention):

* GROUND 1 OF THE ORIGINAL BLOCKED RECORD STANDS: BP_III §1.8 (lines
  585–586) displays this unit's theorem ONLY as the ellipsis
  `theorem cu1_spanTotal …` — there is NO verbatim blueprint statement to
  transcribe (REV2 finding 1; the verbatim transcription still fails with
  `error: expected token` at the `…`).  Every declaration below is
  therefore this unit's RENDERING from the §4 source, flagged for
  division-lead ratification as statements (nothing to be verbatim to) —
  the completion convention this file already used for III-U2's body,
  III-U3a, III-U3b, and III-U3c's kernel, NOT a verbatim landing.
* GROUND 2 OF THE ORIGINAL RECORD IS CURED (why the unit re-ran): III-U3c's
  harvest construction is LANDED above (`harvestNode` + kernel).  The
  original unblock order — "III-U3c's construction lands first (it fixes
  the node-builder vocabulary this statement binds); then this unit states
  totality over it" — is executed here literally: the harvested node below
  IS `harvestNode` applied to the child's data (`InteriorChildAt.node` is a
  wrapper application, no builder redeclared), and the extension assigns
  the dressing slot ψ̂_k := ψ that the III-U3c carrier-split note routes to
  the chain-extension legs (III-U4/III-U7).
* SCOPE (what is and is NOT claimed):
  - CLAIMED (the row's own words: "per-site totality from the same harvest
    construction"): for a well-formed (`EWF`) all-continuing non-complete
    (`InteriorChain`) Cons_f chain 𝐇 and EVERY interior GMN child at the
    site — rendered reader-free at the §1.2 semantic-data layer as
    `InteriorChildAt` (the `CandidatePairAt` convention): a principal side
    `S ∈ D.principalSides H.nodes.length` at the site's own level slot,
    a dressing ψ, and a residual multiplicity μ ≥ 2 (INTERIOR), with the
    §4 well-formedness reads as per-instance law rows — the harvest
    extension (nodes ++ [ν(S, ψ)], dressing slot ψ̂_k := ψ) is again
    `EWF` + `InteriorChain` + Cons_f: exactly `cu1`'s displayed
    per-instance rows at the extended chain.  The §4 checks are
    DISCHARGED, not hypothesized: W1a/W1b at the new node (the ℓ = 1,
    e = 1 case is VACUOUS under μ ≥ 2 — the rev-5 minor-note disposition,
    landed as a real contradiction from the window bound), W2/W5 by
    construction, W3 from the interior scoping, W4 at the updated dressing
    slot (untouched slots ride), the tower rows (`fld` unchanged; the new
    step-degree law is the child's `tower` row), and Cons_f ((c0)
    untouched; (c1)/(c2) at i < k by slope-list stability, at the site by
    construction — "the hypothesis IS the data").
  - NOT CLAIMED: the ADEQ realization clause ("Theorem CU-1 realizes it …
    the walk on f_N visits its state") — that is `cu1`/`cu1_lvl`
    conclusion vocabulary (III-U5/III-U6, both BLOCKED at their records),
    and the unit row's deps line (III-U3c ONLY, not III-U5) scopes it out
    of this unit: `cu1_spanTotal` produces the chain on which `cu1` fires.
    No leaf clause (μ = 1 is O5triple's, routed by the §4 split); no
    terminal clause (CU-2t's seam); no claim that the extension's semantic
    data (D', R') EXIST — the scaffold constructs no GMN objects (§1.2
    header), so they ride as hypotheses with three displayed compatibility
    rows (polygon/residual stability at levels ≤ k + the root order: the
    OL-1/(C4) well-definedness face at the abstract interface).
* Per-instance hypothesis rows, NOT [M]-rows: this unit consumes NO
  GRB/FRESH/CU1Pins/OL6/OL1 row anywhere — the III-U8 vacuity verdict does
  not touch it.  `InteriorChildAt`'s law fields render §4's consumed facts
  ((L2) domains: ℕ by carrier; the (L3)/Def-2.21 window bound
  μ·deg ψ ≤ d(S) = ℓ; the (L3) y-nondivisibility read ψ ≠ X; the
  tower-degree supply at the carrier's own next slot — the REV2-finding-4
  cardinal law's face; the scaffold constructs no field extensions).  Each
  is semantic content about f that the abstract §1.2 interface cannot
  derive — carried per-instance, exactly as `CandidatePairAt` carries
  (c1)/(c2). -/

section UnitIIIU7

/-- **Unit III-U7, the chain-extension builder** (the dressing/tower-slot
assignment that the III-U3c carrier-split note routes to the chain-extension
legs): append one node and assign the dressing slot ψ̂_{|nodes|} := ψ.
`base`/`psi0`/`a0`/`fld` ride unchanged — the tower-degree supply for the
new node is the carrier's OWN next slot, hypothesized per-instance in
`InteriorChildAt.tower`. -/
def EHist.harvestExtend (H : EHist p F) (ν : ENodeData)
    (ψ : Polynomial ↥(H.fld H.nodes.length))
    (hψ : ψ.Monic ∧ Irreducible ψ ∧ ψ ≠ Polynomial.X) : EHist p F :=
  { H with
    nodes := H.nodes ++ [ν]
    psihat := Function.update H.psihat H.nodes.length ψ
    hpsihat := by
      intro i
      rcases eq_or_ne i H.nodes.length with rfl | hne
      · rw [Function.update_self]
        exact hψ
      · rw [Function.update_of_ne hne]
        exact H.hpsihat i }

/-- Θ's slope list on an interior chain: all nodes continuing, so the
continuing part is everything (`InteriorChain.continuingPart_nodes` at the
`Theta` projection). -/
theorem theta_slopes_of_interior {H : EHist p F} (hint : InteriorChain H) :
    (Theta H).slopes = H.nodes.map fun ν => (ν.e, ν.h) := by
  have h : (Theta H).slopes
      = H.continuingPart.nodes.map fun ν => (ν.e, ν.h) := rfl
  rw [h, hint.continuingPart_nodes]

/-- **Unit III-U7, the interior-child datum at the site** (CU1 rev-5 §4,
Corollary CU-1-ADEQ's hypothesis, reader-free at the §1.2 semantic-data
layer — the `CandidatePairAt` convention): a GMN child (S, ψ) of ι(Θ(𝐇))
at the site level k := `H.nodes.length` — S a window principal face from
the data's own site-level slot, ψ the dressing with residual multiplicity
μ — that is INTERIOR (μ ≥ 2), with the §4 well-formedness reads as
per-instance law rows: the (c1) lowest-terms/positivity laws of the side,
the (L3)/Def-2.21 window bound μ·deg ψ ≤ d(S) = ℓ, the W4 dressing laws
(monic, irreducible, ≠ X — the (L3) y-nondivisibility read), and the
tower-degree supply at the carrier's next slot. -/
structure InteriorChildAt (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (S : SideDatum)
    (ψ : Polynomial ↥(H.fld H.nodes.length)) (μ : ℕ) : Prop where
  side_mem : S ∈ D.principalSides H.nodes.length
  resOrd_eq : D.residualOrder H.nodes.length = μ
  interior : 2 ≤ μ
  hSe : 1 ≤ S.e
  hSh : 1 ≤ S.h
  hScop : Nat.gcd S.e S.h = 1
  hSl : 1 ≤ S.ℓ
  window : μ * ψ.natDegree ≤ S.ℓ
  monic : ψ.Monic
  irr : Irreducible ψ
  ne_X : ψ ≠ Polynomial.X
  tower : Nat.card ↥(H.fld (H.nodes.length + 1)) =
    Nat.card ↥(H.fld H.nodes.length) ^ ψ.natDegree

variable {f : Polynomial ℤ_[p]} {H : EHist p F} {D : GMNData f (Theta H)}
  {S : SideDatum} {ψ : Polynomial ↥(H.fld H.nodes.length)} {μ : ℕ}

/-- The dressing has a genuine degree: g := deg ψ ≥ 1 (monic + irreducible —
a degree-0 monic is 1, a unit). -/
theorem InteriorChildAt.deg_pos (hc : InteriorChildAt f H D S ψ μ) :
    1 ≤ ψ.natDegree := by
  rcases Nat.eq_zero_or_pos ψ.natDegree with h0 | h1
  · exfalso
    refine hc.irr.not_isUnit ?_
    rw [hc.monic.natDegree_eq_zero.mp h0]
    exact isUnit_one
  · exact h1

/-- Interior ⟹ selected multiplicity is positive. -/
theorem InteriorChildAt.mu_pos (hc : InteriorChildAt f H D S ψ μ) :
    1 ≤ μ :=
  le_trans one_le_two hc.interior

/-- **Unit III-U7, the harvested node of the child** — LITERALLY the
III-U3c builder applied to the child's data (the row's "per-site totality
from the SAME harvest construction"): all seven law binders are the
datum's own rows; nothing is redeclared. -/
def InteriorChildAt.node (hc : InteriorChildAt f H D S ψ μ) : ENodeData :=
  harvestNode S ψ.natDegree μ hc.hSe hc.hSh hc.hScop hc.hSl hc.deg_pos
    hc.mu_pos hc.window

theorem InteriorChildAt.node_sel (hc : InteriorChildAt f H D S ψ μ) :
    hc.node.sel = some (ψ.natDegree, μ) :=
  rfl

/-- **Unit III-U7, the extension**: nodes ++ [ν(S, ψ)] with the dressing
slot ψ̂_k := ψ (the §4 display's "dressing ψ̂ := ψ"). -/
def InteriorChildAt.extend (hc : InteriorChildAt f H D S ψ μ) : EHist p F :=
  H.harvestExtend hc.node ψ ⟨hc.monic, hc.irr, hc.ne_X⟩

theorem InteriorChildAt.extend_nodes (hc : InteriorChildAt f H D S ψ μ) :
    hc.extend.nodes = H.nodes ++ [hc.node] :=
  rfl

theorem InteriorChildAt.extend_psihat_site
    (hc : InteriorChildAt f H D S ψ μ) :
    hc.extend.psihat H.nodes.length = ψ :=
  Function.update_self _ _ _

theorem InteriorChildAt.extend_psihat_of_ne
    (hc : InteriorChildAt f H D S ψ μ) {i : ℕ}
    (hne : i ≠ H.nodes.length) :
    hc.extend.psihat i = H.psihat i :=
  Function.update_of_ne hne _ _

/-- Node lookups in the extension: an indexed node is an old node (below
the site) or THE harvested node (at the site) — the case split every W-row
consumes. -/
theorem InteriorChildAt.extend_cases (hc : InteriorChildAt f H D S ψ μ)
    {i : ℕ} {ν' : ENodeData}
    (h : hc.extend.nodes[i]? = some ν') :
    (i < H.nodes.length ∧ H.nodes[i]? = some ν') ∨
      (i = H.nodes.length ∧ ν' = hc.node) := by
  have h' : (H.nodes ++ [hc.node])[i]? = some ν' := h
  rcases Nat.lt_or_ge i H.nodes.length with hi | hi
  · rw [List.getElem?_append_left hi] at h'
    exact Or.inl ⟨hi, h'⟩
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h'
    have hlt' : i < H.nodes.length + 1 := by simpa using hlt
    have hieq : i = H.nodes.length := by omega
    subst hieq
    rw [List.getElem?_concat_length] at h'
    injection h' with h''
    exact Or.inr ⟨rfl, h''.symm⟩

/-- **Unit III-U7, leg 1 — the extension is all-continuing non-complete**
(the §4 conclusion's interior scoping: prior nodes by hypothesis;
non-completeness of the LAST node IS the interiority hypothesis μ ≥ 2). -/
theorem InteriorChildAt.extend_interior (hc : InteriorChildAt f H D S ψ μ)
    (hint : InteriorChain H) : InteriorChain hc.extend := by
  refine ⟨hint.a0_ge_two, ?_⟩
  intro i ν' hν'
  rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
  · exact hint.2 i ν' hold
  · refine ⟨Option.some_ne_none _, ?_⟩
    intro gμ hgμ
    rw [Option.mem_def] at hgμ
    have h : (some (ψ.natDegree, μ) : Option (ℕ × ℕ)) = some gμ := hgμ
    injection h with h'
    rw [← h']
    exact hc.interior

/-- Θ of the extension: the slope list grows by the side's recorded slope
pair — the (c1) stability face the i < k Cons_f clauses ride. -/
theorem InteriorChildAt.extend_theta_slopes
    (hc : InteriorChildAt f H D S ψ μ) (hint : InteriorChain H) :
    (Theta hc.extend).slopes =
      (H.nodes.map fun ν => (ν.e, ν.h)) ++ [(S.e, S.h)] := by
  rw [theta_slopes_of_interior (hc.extend_interior hint)]
  have h : hc.extend.nodes = H.nodes ++ [hc.node] := rfl
  rw [h, List.map_append]
  rfl

/-- Requested-slope stability below the site. -/
theorem InteriorChildAt.extend_requestedSlope_lt
    (hc : InteriorChildAt f H D S ψ μ) (hint : InteriorChain H)
    {i : ℕ} (hi : i < H.nodes.length) :
    requestedSlope (Theta hc.extend) i = requestedSlope (Theta H) i := by
  show (Theta hc.extend).slopes[i]? = (Theta H).slopes[i]?
  rw [hc.extend_theta_slopes hint, theta_slopes_of_interior hint,
    List.getElem?_append_left (by rw [List.length_map]; exact hi)]

/-- The requested slope AT the site is the harvested side's pair. -/
theorem InteriorChildAt.extend_requestedSlope_site
    (hc : InteriorChildAt f H D S ψ μ) (hint : InteriorChain H) :
    requestedSlope (Theta hc.extend) H.nodes.length = some (S.e, S.h) := by
  show (Theta hc.extend).slopes[H.nodes.length]? = some (S.e, S.h)
  rw [hc.extend_theta_slopes hint]
  have hlen : H.nodes.length = (H.nodes.map fun ν => (ν.e, ν.h)).length := by
    rw [List.length_map]
  rw [hlen, List.getElem?_concat_length]

/-- **Unit III-U7, leg 2 — the extension is well-formed** (the §4 checks,
clause by clause; see the section record for the check-by-check map). -/
theorem InteriorChildAt.extend_wf (hc : InteriorChildAt f H D S ψ μ)
    (hwf : EWF H) (hint : InteriorChain H) : EWF hc.extend := by
  have hintE := hc.extend_interior hint
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- W1a: ℓ = 1, e ≥ 2 ⟹ inc — at the new node from e·g ≥ 2·1.
  · intro i ν' hν' hsel hℓ he2
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · exact hwf.w1a i ν' hold hsel hℓ he2
    · have he2' : 2 ≤ S.e := he2
      have hmul : 2 * 1 ≤ S.e * ψ.natDegree :=
        Nat.mul_le_mul he2' hc.deg_pos
      show decide (2 ≤ S.e * ψ.natDegree) = true
      exact decide_eq_true (by omega)
  -- W1b: ℓ = 1, e = 1 — VACUOUS at an interior child (μ ≥ 2 and g ≥ 1
  -- force μ·g ≥ 2 > 1 = ℓ against the window bound; the rev-5
  -- minor-note disposition of ADEQ's W1 e = 1 case).
  · intro i ν' hν' hsel hℓ he1
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · exact hwf.w1b i ν' hold hsel hℓ he1
    · have hℓ' : S.ℓ = 1 := hℓ
      have hmul : 2 * 1 ≤ μ * ψ.natDegree :=
        Nat.mul_le_mul hc.interior hc.deg_pos
      have hle : μ * ψ.natDegree ≤ 1 := hℓ' ▸ hc.window
      exact absurd hle (by omega)
  -- W2: species law — by construction at the new node.
  · intro i ν' g μ'' hν' hsel
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · exact hwf.w2 i ν' g μ'' hold hsel
    · have h : (some (ψ.natDegree, μ) : Option (ℕ × ℕ)) = some (g, μ'') :=
        hsel
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact ⟨of_decide_eq_true, decide_eq_true⟩
  -- W3: interior nodes are 𝐇's (interior scoping covers ALL nodes) + a₀.
  · exact ⟨fun i ν' _ hν' gμ hgμ => (hintE.2 i ν' hν').2 gμ hgμ,
      fun _ => hint.a0_ge_two⟩
  -- W5: every non-last node continuing — from the interior scoping.
  · exact fun i ν' _ hν' => (hintE.2 i ν' hν').1
  -- W4: dressing laws — old slots ride, the site slot is ψ's own rows.
  · intro i ν' g μ'' hν' hsel
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · rw [hc.extend_psihat_of_ne (Nat.ne_of_lt hi)]
      exact hwf.w4dress i ν' g μ'' hold hsel
    · rw [hc.extend_psihat_site]
      have h : (some (ψ.natDegree, μ) : Option (ℕ × ℕ)) = some (g, μ'') :=
        hsel
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact ⟨hc.monic, hc.irr, rfl, hc.ne_X⟩
  -- Tower rows: `fld` unchanged; the new step degree is the child's row.
  · exact hwf.towerBase
  · exact hwf.towerStep
  · exact hwf.towerBaseDegree
  · intro i ν' g μ'' hν' hsel
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · exact hwf.towerStepDegree i ν' g μ'' hold hsel
    · have h : (some (ψ.natDegree, μ) : Option (ℕ × ℕ)) = some (g, μ'') :=
        hsel
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact hc.tower

/-- **Unit III-U7, leg 3 — the extension is Cons_f** over its supplied
semantic data: (c0) untouched; (c1)/(c2) below the site by the displayed
stability rows; at the site by construction ("the hypothesis IS the
data"). -/
theorem InteriorChildAt.extend_consF (hc : InteriorChildAt f H D S ψ μ)
    {R : GMNReader f (Theta H) D}
    (hint : InteriorChain H) (hcons : ConsF f H D R)
    (D' : GMNData f (Theta hc.extend))
    (R' : GMNReader f (Theta hc.extend) D')
    (hroot' : D'.rootOrder = D.rootOrder)
    (hsides' : ∀ i, i ≤ H.nodes.length →
      D'.principalSides i = D.principalSides i)
    (hord' : ∀ i, i ≤ H.nodes.length →
      D'.residualOrder i = D.residualOrder i) :
    ConsF f hc.extend D' R' := by
  have hintE := hc.extend_interior hint
  refine ⟨?_, ?_⟩
  · -- (c0): the root read is level-free and rides the compatibility rows.
    show R'.rootOrd = hc.extend.a0
    rw [R'.rootOrd_spec, hroot', ← R.rootOrd_spec]
    exact hcons.1
  · intro i ν' hν'
    rw [hintE.continuingPart_nodes] at hν'
    rcases hc.extend_cases hν' with ⟨hi, hold⟩ | ⟨rfl, rfl⟩
    · -- Below the site: the old (c1)/(c2), transported by stability.
      have hold' : H.continuingPart.nodes[i]? = some ν' := by
        rw [hint.continuingPart_nodes]
        exact hold
      obtain ⟨Si, hSi, hfields, hsel⟩ := hcons.2 i ν' hold'
      obtain ⟨hmem, hslope⟩ := (R.side_spec i Si).mp hSi
      refine ⟨Si, (R'.side_spec i Si).mpr ⟨?_, ?_⟩, hfields, ?_⟩
      · rw [hsides' i (le_of_lt hi)]
        exact hmem
      · show requestedSlope (Theta hc.extend) i = some (Si.e, Si.h)
        rw [hc.extend_requestedSlope_lt hint hi]
        exact hslope
      · intro g μ'' hgμ
        rw [R'.resOrd_spec, hord' i (le_of_lt hi), ← R.resOrd_spec]
        exact hsel g μ'' hgμ
    · -- At the site: S is the read side, fields match by construction.
      refine ⟨S, (R'.side_spec _ S).mpr ⟨?_, ?_⟩, rfl, ?_⟩
      · rw [hsides' _ le_rfl]
        exact hc.side_mem
      · show requestedSlope (Theta hc.extend) H.nodes.length
          = some (S.e, S.h)
        exact hc.extend_requestedSlope_site hint
      · intro g μ'' hgμ
        have h : (some (ψ.natDegree, μ) : Option (ℕ × ℕ)) = some (g, μ'') :=
          hgμ
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [R'.resOrd_spec, hord' _ le_rfl, hc.resOrd_eq]
        exact h.2

/-- **Unit III-U7 — `cu1_spanTotal` (interior adequacy, per-site SPAN
totality; the ADEQ interior half).**  CU1 rev-5 §4, Corollary CU-1-ADEQ's
chain-extension conclusion, quantified over EVERY interior child at the
site (the ∀-(S, ψ) totality — S, ψ, μ and the datum ride as binders): the
harvest extension of 𝐇 by ν(S, ψ) — the III-U3c builder's node, dressing
slot ψ̂_k := ψ — is a well-formed (`EWF`) all-continuing non-complete
(`InteriorChain`) Cons_f chain.  These are exactly `cu1`'s displayed
per-instance hypotheses at the extension, so Theorem CU-1 (III-U5, its own
unit) realizes the extended chain by ONE application once it lands; the
realization clause is NOT claimed here (deps line: III-U3c only).  The
extension's semantic data (D', R') ride as hypotheses with the three
displayed stability rows — the scaffold constructs no GMN objects.  See
the section record for the full scope fence and rendering flags. -/
theorem cu1_spanTotal {R : GMNReader f (Theta H) D}
    (hwf : EWF H) (hint : InteriorChain H) (hcons : ConsF f H D R)
    (hchild : InteriorChildAt f H D S ψ μ)
    (D' : GMNData f (Theta hchild.extend))
    (R' : GMNReader f (Theta hchild.extend) D')
    (hroot' : D'.rootOrder = D.rootOrder)
    (hsides' : ∀ i, i ≤ H.nodes.length →
      D'.principalSides i = D.principalSides i)
    (hord' : ∀ i, i ≤ H.nodes.length →
      D'.residualOrder i = D.residualOrder i) :
    hchild.extend.nodes = H.nodes ++ [hchild.node] ∧
      EWF hchild.extend ∧ InteriorChain hchild.extend ∧
      ConsF f hchild.extend D' R' :=
  ⟨rfl, hchild.extend_wf hwf hint, hchild.extend_interior hint,
    hchild.extend_consF hint hcons D' R' hroot' hsides' hord'⟩

end UnitIIIU7

/-! ## Unit III-A5 — the `(accE, accF)` tie + saturation ⇔ ω = 1 at coherent
`machineProj` (BP_III §2 row 768, MOVED TO WAVE 4 after III-U1): BLOCKED

RE-RUN 2026-08-01, scheduled slot (after III-U1, per REV2 finding 12): the
record below is REFRESHED at HEAD.  Original ground 2 (statement site
unlanded) is CURED — III-U1's `machineProj` and its fieldwise lemmas are
landed above — but ground 1 (no blueprint display of the re-keyed
signature) STANDS ALONE and remains decisive; BP_III.md is byte-identical
to the original probe (1011 lines, commit 0494ce1).  See the CURED note
replacing ground 2 and the refreshed cure paragraph at the end.

Charge (BP_III §2, line 768): "`(accE, accF)` tie + saturation ⇔ ω = 1 at
coherent `machineProj` | corpus telescope `V9_irrSat` + `V3_accKeyDeg`;
quarry only, not a verbatim alias | deps III-U1, corpus MovesT | EASY |
O2a §5 (B); ROOT Step 7".  Probed 2026-08-01 (BP_III.md at HEAD, 1011
lines; Lean 4.31, this pin).  No declaration is landed, on the grounds
below, per the BLOCKED(III-A4/A7/A8) precedent (`O2aOrder1.lean`) and the
III-U5/III-U7 records above:

1. NO Lean statement exists in the blueprint for this unit, so there is
   nothing to transcribe, and statement invention is forbidden.  Grep audit
   over BP_III.md: `III-A5`/`A5` hit the §2 Wave-2 prose row (line 768),
   the §3.2 corpus-reuse row (line 871: "the (accE,accF) tie is largely
   PROVED — re-key, don't re-prove"), the §4 wave-plan prose (lines 921,
   928: "U1→A5"), and the REVISION-2 rows 12 and 26 (lines 993, 1007) —
   all prose, none a signature.  The §1.8 block for THIS module (lines
   553–587) displays `machineProj`, `InteriorChain`, `cu1`, `cu1_lvl`,
   `cu1_spanTotal` only — no III-A5 display; no other §1 block mentions
   the unit.  REVISION-2 finding 26 pins the unit as "quarry-only, not a
   verbatim alias", so re-exporting the corpus theorems verbatim is ALSO
   out of scope by the blueprint's own ruling: the unit's content is a
   RE-KEY of the quarry at `machineProj`, and no display of the re-keyed
   signature exists (the III-U7 record's failure class, not III-T11a's).

2. CURED at the 2026-08-01 re-run (original ground, kept for the ledger:
   "the sole Lean dependency, III-U1's `machineProj`, is UNLANDED at
   HEAD").  III-U1 has since landed `machineProj` (§1.8 signature
   verbatim, PARTIAL: the one honest W3 sorry in the `machineEWF`
   certificate — any III-A5 statement THROUGH `machineProj` would inherit
   that sorryAx via the def, per the footprint-audit note at the end of
   the file) together with the fieldwise vocabulary a re-key would consume
   (`machineProj_val`, `_base`, `_psi0`, `_a0`, `_nodes`,
   `_nodes_getElem?`, `_nodes_length`).  The cure SHARPENS ground 1 rather
   than weakening it: the landed projection's root-datum split (machine
   node 0 ↦ the root datum (ψ̂₀, a₀); projected node list = `M.nodes.tail
   .map nodeToE`, so `machineProj_nodes_length` = machine length − 1)
   makes the re-keyed statement NON-canonical — the quarry's
   `accE M * accF M` runs over ALL machine nodes (node 0's (e, g)
   included) while the projected list drops node 0, and the saturation leg
   `MovesT.irr_iff_mu_one` (keyed at the LAST machine node's μ) lands at
   `(machineProj M hM).1.a0` when `M.nodes.length = 1` (empty projected
   list) but at the last projected node's `sel` (via `nodeToE_sel`) when
   `2 ≤ M.nodes.length`.  At least two inequivalent renderings exist
   (two-case split vs. a nonempty-tail hypothesis; root factor carried on
   the `a0`/`psi0.natDegree` side vs. restated over the machine carrier),
   so electing one is the architect's statement work, not transcription —
   the III-U7 record's failure class, exactly as ruled at the original
   probe.

Quarry status (pinned by this file's `MovesT` imports, so the compile gate
certifies it resolves at HEAD): the corpus telescope IS landed and green,
on the `MovesC.History p F` carrier —
  * `MovesT.acc_childWidth` (`MovesT/V9_irrSat.lean`): under
    `HistLawful p n H` and `H.nodes ≠ []`,
    `accE H * accF H = (H.nodes.getLast?).elim 1 fun ν => ν.childWidth`
    — the `(accE, accF)` tie (Dwidth-chain telescope);
  * `MovesT.irr_iff_mu_one` (same file): under `HistLawful p n H` at
    `H.nodes.getLast? = some ν`, `IrrHalts H ↔ ν.μ = 1` — the saturation
    ⇔ ω = 1 leg (the row's ω is the note's μ; MOVES 7078–7080
    parenthetical, per that file's header);
  * `MovesT.accEF_keyDeg` (`MovesT/V3_accKeyDeg.lean`): the E·F =
    key-degree species leg.
The re-key target carrier is `EHist p F` (`H.nodes : List ENodeData`),
while `MovesT.accE`/`accF` have domain `MovesC.History p F` — the exact
carrier seam already on record at BLOCKED(III-A7) ground (a)
(`O2aOrder1.lean`: application type mismatch, `H.nodes : List ENodeData`
where `MovesC.History ?p ?F` is expected; no coercion exists).
`machineProj` is the blueprint's sanctioned bridge across that seam —
REVISION-2 finding 12 moved this unit after III-U1 for exactly this
reason.

Cure (refreshed at the 2026-08-01 re-run; step 1 of the original order is
DONE): the ONE remaining step is the architect displaying the III-A5
re-keyed signature in a §1 block for this module — the tie + saturation
⇔ ω = 1 stated through `(machineProj M hM).1`, consuming the quarry rows
above, with the root-datum election of ground 2's CURED note (length-1
corner at `a0` vs. last projected node's `sel`; where node 0's (e, g)
factor rides) DECIDED in the display.  Then III-A5 re-runs as a re-key,
NOT a re-proof (BP §3.2 row 871); its footprint will inherit III-U1's W3
sorryAx through `machineProj` until the W3 adjudication (footprint-audit
note at the end of the file). -/

/-! ## Unit III-U8 — the CU-1 positive gate (BP_III §2 row 813): BLOCKED as
specified, and THE OBSTRUCTION IS COMPILED — the gate REFUSES: `cu1`'s
hypothesis stack is unsatisfiable at EVERY (p, F)

Charge (BP_III §2, line 813): "positive gate: 2-node interior chain at p = 2
runs through `cu1`'s statement (non-vacuity) | corpus gate style
(`HK23_twoNodeGatePos` template) | deps III-U5 | MED | CU1 §7.1's gate
discipline"; §4 wave plan (line 930): "U8 remains mandatory before closure".
Gate units carry NO verbatim blueprint statement (corpus style: a compiled
instance packaged as one ∃-theorem, per `HC2/HK23_twoNodeGatePos.lean`).
Probed 2026-08-01 (BP_III.md at HEAD; Lean 4.31, this pin).

* -- BLOCKED(III-U8), ground 1 (dependency): the gate must apply `cu1` to a
  compiled 2-node interior instance, and `cu1` is UNLANDED — unit III-U5 is
  BLOCKED above (statement census at hand-off: `CU1Pins` fenced at III-H3,
  `machineProj` = unlanded III-U1; `InteriorChain`/`StateBinding` since cured
  by III-U2/III-U3a above).  Any gate statement would bind `cu1` and its
  conclusion vocabulary; exact error class on any attempt: "Unknown
  identifier `cu1`".

* -- BLOCKED(III-U8), ground 2 (THE GATE VERDICT — independent of ground 1
  and NOT curable by landing the Wave-4 chain): the displayed `cu1`'s
  hypothesis stack is UNSATISFIABLE, at the row's p = 2 and at every other
  (p, F).  Compiled below, Lean-core:
    - `U8.grb_uninhabited : ¬ GRB p F` — `GRB.properness` (Hyps.lean,
      III-H1) universally quantifies its implicit `{D : GMNData f c}` over
      ARBITRARY carriers (`GMNData` is law-free data); the all-empty
      `principalSides` datum `U8.dataEmpty` refutes it at i = 2.
    - `U8.fresh_uninhabited : ¬ FRESH p F` — `FRESH.parentSeparated`
      (Hyps.lean, III-H2) universally quantifies its implicit
      `{H : EHist p F}` over ARBITRARY carriers, and `EHist` imposes no
      nodup law on `nodes`; the duplicate-node history `U8.histDup`
      (`nodes = [ν, ν]`) refutes it at (i, j) = (0, 1).
    - `U8.u8Gate_hypStack_unsat_p2` packages the verdict at the gate's
      displayed prime: `¬ (GRB 2 (ZMod 2) ∧ FRESH 2 (ZMod 2))`.
  CONSEQUENCE for the wave: every theorem consuming `hGRB : GRB p F` or
  `hFRESH : FRESH p F` — the displayed `cu1` included — is VACUOUS (its
  hypothesis row is contradictory), and NO positive gate can ever be built.
  This is the transcription-overreach class the gate discipline exists to
  catch: the ROOT §3.1 (H1)/(H2) math rows speak of ENGINE-ARISING residue
  data, while the §1.3 verbatim transcription's implicit carrier quantifiers
  range over all of `GMNData`/`EHist`, degenerate instances included.  (Same
  smell, flagged not compiled: `GRB.slotBijection`'s map `fun j => j` is the
  identity — that clause is trivially TRUE and carries no content.)  The
  §1.3 rows need a blueprint-level scope repair (e.g. guard the clauses by
  the OL-family conformance rows, or move the carriers to per-instance
  hypothesis position) — fenced above this unit's authority, the III-H3
  `frEQ` precedent exactly.

* Witness style: corpus negative-gate precedent (`HK22.twoNodeGate_isEmpty`;
  `HC2/U1_negWitness.lean`; `HC2/HK52_stretchGate.lean` — compiled
  obstructions).  The degenerate carriers below are gate ARTIFACTS, scoped in
  namespace `U8`: they assert nothing about engine-arising data and must NOT
  be quarried as project carriers.

* Unblock order: §1.3 `GRB`/`FRESH` scope repair (division-lead + architect
  ruling) → III-H3/III-U1/III-U3b/III-U3c/III-U4/III-U5 land → THEN this
  unit re-runs as the positive 2-node instance its row describes. -/

namespace U8

/-- Gate artifact (III-U8 verdict witness): the minimal terminal node record
    (e = h = ℓ = 1, `sel = none`).  Exists only to witness that `ENodeData`
    admits equal entries at distinct history indices. -/
def nodeDup : ENodeData where
  e := 1
  h := 1
  ℓ := 1
  s := 0
  u := 0
  sel := none
  inc := false
  he := le_rfl
  hh := le_rfl
  hcop := Nat.gcd_self 1
  hl := le_rfl
  hsel := by intro gμ hgμ; simp at hgμ

/-- Gate artifact: `X − 1` is not `X` (their constant coefficients differ) —
    the `hpsihat` obligation `psihat i ≠ X` for the degenerate dressings. -/
theorem X_sub_C_one_ne_X {K : Type*} [Field K] :
    (Polynomial.X - Polynomial.C 1 : Polynomial K) ≠ Polynomial.X := by
  intro h
  have h0 := congrArg (fun q => Polynomial.coeff q 0) h
  simp at h0

/-- Gate artifact (III-U8 verdict witness): a well-typed `EHist` whose node
    list repeats ONE record — `EHist` (the §1.1 carrier, verbatim) imposes no
    nodup law, so `nodes[0]? = nodes[1]?` with `0 ≠ 1`, refuting
    `FRESH.parentSeparated`'s universal `{H}`. -/
noncomputable def histDup : EHist p F where
  base := ⊥
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 1
  ha0 := le_rfl
  nodes := [nodeDup, nodeDup]
  fld := fun _ => ⊥
  psihat := fun _ => Polynomial.X - Polynomial.C 1
  hpsihat := fun _ =>
    ⟨Polynomial.monic_X_sub_C 1, Polynomial.irreducible_X_sub_C 1, X_sub_C_one_ne_X⟩

/-- **III-U8 GATE VERDICT, leg 2 of 2**: the §1.3 row `FRESH p F` is
    uninhabited — its `parentSeparated` clause fails at the duplicate-node
    history `histDup`.  Every consumer of `hFRESH : FRESH p F` (the displayed
    `cu1` included) is vacuous until the row is scope-repaired. -/
theorem fresh_uninhabited : ¬ FRESH p F := fun hF =>
  hF.parentSeparated (H := histDup) (i := 0) (j := 1)
    (by simp [histDup]) (by simp [histDup]) (by omega) rfl

/-- Gate artifact (III-U8 verdict witness): the empty formal chain (`ChainData`
    carries NO admissibility, per its §1.1 docstring), carrier for the
    degenerate `GMNData` below. -/
noncomputable def chainEmpty : ChainData p F where
  base := ⊥
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  slopes := []
  hcop := by intro eh heh; simp at heh
  fld := fun _ => ⊥
  psihat := fun _ => Polynomial.X
  hdress := by intro i hi; simp at hi

/-- Gate artifact (III-U8 verdict witness): the all-empty semantic datum —
    `GMNData` is law-free data (§1.2), so `principalSides := fun _ => []` is
    well-typed, refuting `GRB.properness`'s universal `{D}`. -/
noncomputable def dataEmpty :
    GMNData (Polynomial.X : Polynomial ℤ_[p]) (chainEmpty (p := p) (F := F)) where
  principalSides := fun _ => []
  residualOrder := fun _ => 0
  residualDegree := fun _ => 0
  rootOrder := 0

/-- **III-U8 GATE VERDICT, leg 1 of 2**: the §1.3 row `GRB p F` is
    uninhabited — its `properness` clause fails at the all-empty datum
    `dataEmpty` (level 2).  Every consumer of `hGRB : GRB p F` (the displayed
    `cu1` included) is vacuous until the row is scope-repaired. -/
theorem grb_uninhabited : ¬ GRB p F := fun hG =>
  hG.properness (f := Polynomial.X) (c := chainEmpty) (D := dataEmpty) 2 le_rfl rfl

/-- **III-U8 GATE VERDICT, packaged at the row's displayed prime p = 2**: the
    hypothesis stack `(hGRB, hFRESH)` of the displayed `cu1` is unsatisfiable
    — no 2-node interior chain (nor ANY instance) can run through `cu1`'s
    statement while the §1.3 rows stand as transcribed.  The III-U8 positive
    gate is therefore impossible as specified; wave closure is gated on the
    blueprint-level scope repair recorded above. -/
theorem u8Gate_hypStack_unsat_p2 :
    ¬ (GRB 2 (ZMod 2) ∧ FRESH 2 (ZMod 2)) := fun ⟨hG, _⟩ =>
  grb_uninhabited hG

end U8

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-U1, proved perimeter): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.node_mu_mul_g_le_ell
#print axioms LeanUrat.Scaffold.DictIII.node_psi_ne_X
#print axioms LeanUrat.Scaffold.DictIII.node_card_nextField
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_node_inv
-- Footprint audit (unit III-U1, certificate): expect sorryAx — the ONE
-- honest W3 sorry (BLOCKED record at the proof site); everything else in
-- the certificate is proved.  Statements MENTIONING `machineProj` (e.g.
-- `machineProj_nodes_length`) inherit the sorryAx through the def until
-- the W3 adjudication, even where their own proof terms are clean.
#print axioms LeanUrat.Scaffold.DictIII.machineEWF
#print axioms LeanUrat.Scaffold.DictIII.machineProj
#print axioms LeanUrat.Scaffold.DictIII.machineProj_nodes_length

-- Footprint audit (unit III-U2 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.cu1_base_rootTrack
#print axioms LeanUrat.Scaffold.DictIII.cu1_base_reductionFactor

-- Footprint audit (unit III-U8 gate verdict): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.U8.grb_uninhabited
#print axioms LeanUrat.Scaffold.DictIII.U8.fresh_uninhabited
#print axioms LeanUrat.Scaffold.DictIII.U8.u8Gate_hypStack_unsat_p2

-- Footprint audit (unit III-U6 support gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.nstarMaj_readCeil_le
-- Footprint audit (unit III-U6 support, read_locality leg): expect sorryAx —
-- inherited from the honest BLOCKED(III-T10) row-supply sorry inside
-- `read_locality`'s proof (Locality.lean), NOT from this declaration's body.
#print axioms LeanUrat.Scaffold.DictIII.readsOf_transfer_at_nstar_level

-- Footprint audit (unit III-U3b): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair_le1
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair_ge2
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair_gd2_instance
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair_gate
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepPair_gate_unique

-- Footprint audit (unit III-U3c, landed half): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.harvestNode_matches
#print axioms LeanUrat.Scaffold.DictIII.harvest_sel_reads
#print axioms LeanUrat.Scaffold.DictIII.identified_side_laws
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepHarvest
#print axioms LeanUrat.Scaffold.DictIII.harvestNode_gate
-- Footprint audit (unit III-U3c, machine-side creation-target ties): expect
-- Lean core only — the ties live at `machineEHist` (no coherence, no W3
-- certificate), so NO sorryAx despite `machineProj`'s honest W3 sorry.
#print axioms LeanUrat.Scaffold.DictIII.historySnoc
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_base
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_a0
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_psi0
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_nodes
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_getElem?_of_lt
#print axioms LeanUrat.Scaffold.DictIII.machineEHist_historySnoc_lastSlot
#print axioms LeanUrat.Scaffold.DictIII.harvestNode_machineFace

-- Footprint audit (unit III-U4): expect Lean core only — the kernel, both
-- step faces, the assembled leg, and the gate (incl. the imported
-- `HK57.sideReads0_landing` witness) are all proved with no sorry.
#print axioms LeanUrat.Scaffold.DictIII.stateBinding_of_lastRecord
#print axioms LeanUrat.Scaffold.DictIII.stateBinding_snoc
#print axioms LeanUrat.Scaffold.DictIII.stateBinding_historySnoc
#print axioms LeanUrat.Scaffold.DictIII.cu1_stepBinding
#print axioms LeanUrat.Scaffold.DictIII.u4Gate_stateBinding

-- Footprint audit (unit III-U7): expect Lean core only — the extension
-- builder, the interior-child legs, and the assembled `cu1_spanTotal` are
-- all proved with no sorry (no [M]-row consumed; per-instance rows only).
#print axioms LeanUrat.Scaffold.DictIII.EHist.harvestExtend
#print axioms LeanUrat.Scaffold.DictIII.InteriorChildAt.extend_interior
#print axioms LeanUrat.Scaffold.DictIII.InteriorChildAt.extend_wf
#print axioms LeanUrat.Scaffold.DictIII.InteriorChildAt.extend_consF
#print axioms LeanUrat.Scaffold.DictIII.cu1_spanTotal
