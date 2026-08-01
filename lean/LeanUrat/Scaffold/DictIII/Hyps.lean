/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Carriers
import LeanUrat.Scaffold.DictIII.GMNReader
import LeanUrat.MovesC.Defs
import LeanUrat.HC2.Defs
import LeanUrat.HC1.DefsV

/-!
# Scaffold/DictIII/Hyps — THE NAMED HYPOTHESIS ROWS (BP_III §1.3)

E-phase transcription of `lean/blueprints/BP_III.md` §1.3.  This file currently
holds units III-H1 (`GRB`) and III-H2 (`FRESH`), transcribed VERBATIM.  Every [M]/pin row Movement III
consumes enters here as a displayed Prop structure with its clause list — NO
axioms, NO `True` placeholders; each row's docstring pins its ROOT §3.1 row and
printed-source loci.  Sources of record: GD23 r4 §7.2; ROOT §3.1 (H1).
Unit III-H8 adds the §1.3 literature Props (`MacLaneV1Pkg`, `KeyPkg`) —
displayed hypothesis Props, NOT axioms; the policy loop decides their eventual
status.  Sources: O1thr §2.5 (V1)/(V2); GD23 §1.3; MacLane 1936 Def 4.1 + Thm 4.2.
Unit III-H9 adds the remaining §1.3 literature Props: `Lit3Hensel` (landed
verbatim; REV2 finding 19 shape) — `GMNCor120_38` is BLOCKED, see the record at
the bottom of this file.  Sources: CUC §9.3(ii); O2a §5.
-/

namespace LeanUrat.Scaffold.DictIII

/-- (H1) = (GR-B), ROOT §3.1: the anchored-march residue-structure package at OM
    orders ≥ 2 — GD-3 FULL form: R^nrm = c·R_λ(f) with slot-wise residue-field
    bijections, per GD23 rev-4 §7.2's TWO printed FGMN Thm-4.2 pairings, with the
    properness proviso. Pinned: FGMN Thm 4.2, Cor 4.4/4.8/4.9/5.6, Prop 5.14/Cor
    5.15; MacLane Thm 10.2, Lem 10.1/11.1–11.2, Thm 12.1/Cor 12.2. HYPOTHESIS, not
    axiom. -/
structure GRB (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  residualNormalForm : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i → ∃ R : GMNReader f c D,
      ∀ S, R.side i = some S →
        D.residualDegree i = S.ℓ
  slotBijection : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      Function.Bijective fun j : Fin (D.residualDegree i + 1) => j
  properness : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      D.principalSides i ≠ []

/-- Interior scoping: all nodes continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2.
    (Unit III-U2 def half; signature VERBATIM BP_III §1.8.  MOVED here from
    `DictIII/CU1.lean` at H2-U10b, 2026-08-01 — the restated (H2) row below
    consumes it as its guard; the fieldwise-access lemmas stay in CU1.lean.) -/
def InteriorChain {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : EHist p F) : Prop :=
  2 ≤ H.a0 ∧
    ∀ (i : ℕ) ν, H.nodes[i]? = some ν →
      ν.sel ≠ none ∧ ∀ gμ ∈ ν.sel, 2 ≤ gμ.2

/-- (H2) = (FRESH), with every object locally quantified.

Unit III-H2, transcribed from BP_III §1.3 (sources: ROOT §3.1 (H2);
CU1 §5 — the O-9/CU-1 vertex-law clause + clause (c)).  Display adjustment
(same sanctioned convention as the Carriers.lean header note): the §1.3 display
writes node lookups `H.nodes.get? i`, but `List.get?` was REMOVED from the
pinned Lean-4.31/Mathlib environment — the surviving spelling of the SAME
function is `H.nodes[i]?` (`getElem?`).  HYPOTHESIS row, not axiom.

**`childDetermined` RESTATED at H2-U10b (2026-08-01; Asvin's standing
statement-change authority).**  The §1.3 verbatim form (`ConsF →
H.nodes[i]? = some ν → ∃! S, R.side i = some S`) is REFUTED at terminal
indices: over an all-terminal history `Theta H` has no slopes, `side_spec`
forces `side ≡ none` while `ConsF` holds vacuously — compiled as PROBE F-4,
`probe_restated_childDetermined_refuted` (HDischarge/H2/DictIIIProbes.lean).
The landed consumption (`cu1_stepPair_ge2`, CU1.lean — the ONLY firing site)
is interior-only, so the honest scope is the guard `InteriorChain H`: every
node continuing, so a slope EXISTS at every recorded index and the clause
asserts the unique-side law NON-VACUOUSLY — THE read at each level is THE
unique principal side carrying the requested slope.  Compiled non-vacuity
witness: `interior_childDetermined_gate` (DictIIIProbes.lean), a one-node
interior chain with an actual slope realizing the ∃! at an actual side.
HONEST PRICING (the ledger dichotomy, on record): under the guard the clause
is derivable from `ConsF` + the reader laws (`side_spec` existence + `Option`
injectivity), so this row prices CITATION STRUCTURE, not content — the
genuine (FRESH) freshness content is priced at (TRANS-DEEP)/(VTX-DEEP),
gated H2-U9 (HDISCHARGE_H2.md §5).  TERMINAL-index reads are NOT this row's
content: they are terminal-seam material, routed to (T-READ)/(H6) — see
`TerminalSeamHyps` (BP_III §1.3) and the H6 discharge group.
`parentSeparated` stands as transcribed and remains REFUTED at duplicate
histories (PROBE F-2 / `U8.fresh_uninhabited`, CU1.lean): the whole-row
inhabitation is the §1.3 scope repair, still open — NOT executed here. -/
structure FRESH (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  childDetermined : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    {i : ℕ} {ν : ENodeData}, InteriorChain H → ConsF f H D R →
      H.nodes[i]? = some ν →
      ∃! S, R.side i = some S ∧ S ∈ D.principalSides i ∧
        HasRequestedSlope (Theta H) i S
  parentSeparated : ∀ {H : EHist p F} {i j : ℕ},
    i < H.nodes.length → j < H.nodes.length → i ≠ j →
    H.nodes[i]? ≠ H.nodes[j]?
  junctionPin : ∀ {H : EHist p F} {i : ℕ},
    i + 1 < H.nodes.length → (H.nodes[i]?).isSome

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- III-H6 carrier (O-2a (C2) Lift/ι): the once-and-for-all pinned lift function —
    level-indexed, valued in `O[x] = ℤ_[p][x]`.  Level 0 is the coefficientwise
    canonical lift of ψ̂₀; each `Lift_i`, `i ≥ 1`, is an ARBITRARY BUT FIXED
    function of the level-`i` dressing (the note pins it to the project engine's
    standard lift).  The carrier imposes NO laws: that each output is a Def-2.12
    representative of its type is exactly the named row `OL1` below.  Tower-level
    inputs are read in the ambient field `F` via the coefficientwise inclusion
    (the `Coe` instance below), matching the corpus Subfield-tower style. -/
structure LiftFn (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  toFun : ℕ → Polynomial F → Polynomial ℤ_[p]

instance : CoeFun (LiftFn p F) (fun _ => ℕ → Polynomial F → Polynomial ℤ_[p]) :=
  ⟨LiftFn.toFun⟩

/-- Coefficientwise inclusion of a tower-level polynomial into the ambient field,
    so applications read exactly as displayed in BP_III §1.3
    (`lift i (c.psihat i)`, `lift 0 c.psi0`). -/
noncomputable instance {K : Subfield F} : CoeHead (Polynomial ↥K) (Polynomial F) :=
  ⟨Polynomial.map K.subtype⟩

/-- OL-2a-1..6 = GD-1..GD-6 (O-2a rev-5 §4), each its own named Prop. OL1 is the
    ι-granting row (Lift_j outputs are Def-2.12 representatives, j ≥ 1); OL2/OL3's
    ≥2 content routes through GRB; OL4/OL5/OL6 are the engine-conformance family
    (OL6 = run decomposition + chain binding, consumed by CU-1(ii)). -/
def OL1 (c : ChainData p F) (lift : LiftFn p F) : Prop :=
  ∀ i, i < c.slopes.length →
    (lift i (c.psihat i)).Monic ∧
    (lift i (c.psihat i)).natDegree = (c.psihat i).natDegree

/-- OL-2 minimal form (GD-2, O-2a rev-5 §4): every requested level carries a
    non-empty principal-side list.  Unit III-H7a; the ≥2 content routes through
    `GRB.properness`. -/
def OL2min (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i, i < c.slopes.length → D.principalSides i ≠ []

/-- OL-3 minimal form (GD-3, O-2a rev-5 §4): the residual degree reads off any
    principal side's ℓ.  Unit III-H7a; the ≥2 content routes through `GRB`. -/
def OL3min (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i S, S ∈ D.principalSides i → D.residualDegree i = S.ℓ

/-- OL-4 (GD-4, O-2a rev-5 §4): a principal side exists at every requested
    level — engine conformance, existence leg.  Unit III-H7b. -/
def OL4 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i, i < c.slopes.length → ∃ S, S ∈ D.principalSides i

/-- OL-5 (GD-5, O-2a rev-5 §4): at most one principal side carries the
    requested slope — engine conformance, uniqueness leg.  Unit III-H7b. -/
def OL5 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i S T, S ∈ D.principalSides i → T ∈ D.principalSides i →
    HasRequestedSlope c i S → HasRequestedSlope c i T → S = T

/-- OL-6 (GD-6, O-2a rev-5 §4): run decomposition + chain binding — the reader
    returns a principal side at every requested level (consumed by CU-1(ii)).
    Unit III-H7c. -/
def OL6 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) (R : GMNReader f c D) : Prop :=
  ∀ i, i < c.slopes.length →
    ∃ S, R.side i = some S ∧ S ∈ D.principalSides i

/-! ## Unit III-H3 — `CU1Pins` (BP_III §1.3): BLOCKED on a statement defect in row `frEQ`

The verbatim blueprint statement is preserved in the commented block below; it is NOT
weakened or partially landed (dropping a row would be a statement change).  Status at
hand-off (2026-08-01):

* `pROOT`/`pKEY` elaborate VERBATIM against the landed III-H6 carrier (checked in a
  scratch module with primed names: with the coefficientwise-inclusion bridge in its
  surviving `CoeTC` + `noncomputable` spelling, both rows compile exactly as displayed).
* -- BLOCKED(III-H3): row `frEQ`'s conclusion `HC1.ReadFrame p F` cannot compile as
  written.  BP_III §3's corpus map pins `HC1.ReadFrame` to `LeanUrat.HC1.ReadFrame`
  (`HC1/DefsV.lean:115`), whose signature is
  `ReadFrame {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
    (σ : Moves.Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u`
  — `p`,`F` are IMPLICIT, the explicit slots are (σ, e★, h★, s★, t★), and the result
  is `Type u`, not `Prop`.  Exact compiler error at the displayed row:
    `Application type mismatch: The argument p has type ℕ but is expected to have
     type Moves.Stage ?m ?m in the application HC1.ReadFrame p`.
  The row needs a blueprint-level repair — which frame indices (σ, e★, h★, s★, t★)
  the pin quantifies over, and Prop-valued packaging (e.g. `Nonempty`) — which is
  fenced above this unit's authority.

```
/-- CU-1's three declared pins (CU1 rev-5 §0′), as one row structure. -/
structure CU1Pins (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  pROOT : ∀ (c : ChainData p F) (lift₁ lift₂ : LiftFn p F),
    OL1 c lift₁ → OL1 c lift₂ → lift₁ 0 c.psi0 = lift₂ 0 c.psi0
  pKEY : ∀ (c : ChainData p F) (lift₁ lift₂ : LiftFn p F),
    OL1 c lift₁ → OL1 c lift₂ →
    ∀ i ψ, lift₁ i ψ = lift₂ i ψ
  frEQ : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {M : MovesC.History p F},
    MovesC.HistoryCoherent M → MovesJ.ReadsOf p F n f M →
    ∀ i, i < M.nodes.length → HC1.ReadFrame p F
```
-/

section
-- BP_III §1 standing variables.
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- (N*-MAJ), CU1 rev-5 §1: N*(𝐇) ≥ L(M_𝐇) — the SINGLE consumed property of the
    decision level. Any level function satisfying it may be substituted. -/
def NstarMaj (Nstar : EHist p F → ℕ) (L : MovesC.History p F → ℕ)
    (dress : EHist p F → MovesC.History p F) : Prop :=
  ∀ H, L (dress H) ≤ Nstar H

end

/-! ## Unit III-H8 — the §1.3 literature Props (BP_III §1.3, verbatim)

Displayed hypothesis Props, NOT axioms — the policy loop decides their eventual
status.  `p` is the file-ambient prime (the `variable` line above), exactly as
in the blueprint block. -/

/-- MacLane 1936 Def 4.1 + Thm 4.2 at the (V1) frame-semantics pin (LITUNIT §4,
    MATCH): the augmented value of a genuine key chain is a valuation. -/
structure MacLaneV1Pkg
    (w : ℕ → Polynomial ℤ_[p] → WithTop ℤ)
    (keys : ℕ → Polynomial ℤ_[p]) : Prop where
  zero : ∀ i, w i 0 = ⊤
  one : ∀ i, w i 1 = 0
  mul : ∀ i A B, w i (A * B) = w i A + w i B
  add : ∀ i A B, min (w i A) (w i B) ≤ w i (A + B)
  keyMonic : ∀ i, (keys i).Monic

/-- (V2) key package at a single level (O1thr §2.5 (V2); GD23 §1.3): Φ is a
    genuine MacLane key for w — monic, positive degree, initial-form prime
    (KPa), and no lower-degree block attains w Φ.  HYPOTHESIS row, not axiom. -/
structure KeyPkg (w : Polynomial ℤ_[p] → WithTop ℤ)
    (Φ : Polynomial ℤ_[p]) : Prop where
  monic : Φ.Monic
  positiveDegree : 1 ≤ Φ.natDegree
  initialPrime : ∀ A B, w (A * B) = w Φ →
    w A = w Φ ∨ w B = w Φ
  lowerDegreeBlock : ∀ B, B.natDegree < Φ.natDegree →
    B ≠ 0 → w B ≠ w Φ

/-! ## Unit III-H9 — the remaining §1.3 literature Props (BP_III §1.3)

`Lit3Hensel` is transcribed VERBATIM below.  Its sibling `GMNCor120_38` is
BLOCKED — record at the end of this block. -/

/-- Hensel/Gauss lifting of a monic coprime factorization over a domain modulo
    a maximal ideal (CUC §9.3(ii) literature row; O2a §5; REV2 finding 19: the
    ring, ideal, polynomials, monicity, maximality, coprimality, reduction
    equality, and lifted factorization are all exposed as binders).  Displayed
    hypothesis Prop, NOT an axiom — the policy loop decides its eventual
    status. -/
structure Lit3Hensel (p : ℕ) [Fact p.Prime] : Prop where
  lift : ∀ {R : Type*} [CommRing R] [IsDomain R]
    (f g₀ h₀ : Polynomial R) (I : Ideal R),
    f.Monic → g₀.Monic → h₀.Monic →
    Ideal.IsMaximal I → IsCoprime g₀ h₀ →
    Polynomial.map (Ideal.Quotient.mk I) f =
      Polynomial.map (Ideal.Quotient.mk I) (g₀ * h₀) →
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h

/- BLOCKED(III-H9): `GMNCor120_38` (BP_III §1.3, displayed verbatim below) does
NOT elaborate as written, on two independent grounds — statement changes are
fenced, so the row is NOT landed:

(1) NOT curable by dependency landing: both clauses apply the corpus functions
    `MovesT.accE`/`MovesT.accF : MovesC.History p F → ℕ` (pinned as-is by the
    BP_III §1 preamble and the §3 corpus map) to `H.nodes : List ENodeData`.
    Exact error (Lean 4.31, this pin, 2026-08-01):
      Application type mismatch: The argument
        H.nodes
      has type
        List ENodeData
      but is expected to have type
        MovesC.History ?p ?F
      in the application
        MovesT.accE H.nodes
    (and the same at `MovesT.accF H.nodes`).  No coercion exists; a
    list-domain overload or an `ENodeData → MovesC.Node` dressing would be a
    NEW definition changing the row's meaning — needs an architect ruling.

(2) Curable when unit III-S1a lands: `DecIrr` (owned by §1.9 / III-S1a,
    `CU2t.lean`) is not yet in the corpus — "Unknown identifier `DecIrr`".
    (`ConsF` resolves since III-C9 landed in `GMNReader.lean`.)

The blocked display, for the record (BP_III §1.3):

  structure GMNCor120_38 (p : ℕ) [Fact p.Prime]
      (F : Type*) [Field F] [Finite F] : Prop where
    irrationalBranch : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
      {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
      DecIrr H → ConsF f H D R →
      MovesT.accE H.nodes * MovesT.accF H.nodes = f.natDegree
    positiveResidualDegree : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
      {D : GMNData f (Theta H)}, DecIrr H →
      ∀ i, i < H.nodes.length → 1 ≤ D.residualDegree i
-/

end LeanUrat.Scaffold.DictIII
