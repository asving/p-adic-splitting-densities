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
holds unit III-H1 (`GRB`), transcribed VERBATIM.  Every [M]/pin row Movement III
consumes enters here as a displayed Prop structure with its clause list — NO
axioms, NO `True` placeholders; each row's docstring pins its ROOT §3.1 row and
printed-source loci.  Sources of record: GD23 r4 §7.2; ROOT §3.1 (H1).
Unit III-H8 adds the §1.3 literature Props (`MacLaneV1Pkg`, `KeyPkg`) —
displayed hypothesis Props, NOT axioms; the policy loop decides their eventual
status.  Sources: O1thr §2.5 (V1)/(V2); GD23 §1.3; MacLane 1936 Def 4.1 + Thm 4.2.
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
instance {K : Subfield F} : Coe (Polynomial ↥K) (Polynomial F) :=
  ⟨Polynomial.map K.subtype⟩

/-- OL-2a-1..6 = GD-1..GD-6 (O-2a rev-5 §4), each its own named Prop. OL1 is the
    ι-granting row (Lift_j outputs are Def-2.12 representatives, j ≥ 1); OL2/OL3's
    ≥2 content routes through GRB; OL4/OL5/OL6 are the engine-conformance family
    (OL6 = run decomposition + chain binding, consumed by CU-1(ii)). -/
def OL1 (c : ChainData p F) (lift : LiftFn p F) : Prop :=
  ∀ i, i < c.slopes.length →
    (lift i (c.psihat i)).Monic ∧
    (lift i (c.psihat i)).natDegree = (c.psihat i).natDegree

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

end LeanUrat.Scaffold.DictIII
