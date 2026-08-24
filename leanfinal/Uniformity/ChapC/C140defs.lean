/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C43
import Uniformity.ChapC.C44
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapC.C140defs — transcription batch DT1: definitional twins, no proof content

**Transcription unit DT1.** Four small signed DEFINITIONAL declarations from
`leanspec/Leanspec/ChapC.lean` (structures / an inductive / defs, carrying no proof content),
landed here as BYTE-FAITHFUL twins of the signed leanspec text. Deviations: none, beyond the
namespace/import adjustments the parent `CLAUDE.md` statement-fence explicitly allows, and (for
`Phi1`/`Phi2`/`Phi3` alone) carrying their three necessary auxiliary defs `pmul`/`padd`/`psmul`
verbatim from the same leanspec lines — without them the two composite defs do not elaborate.

* `ComposedLabel` — leanspec `ChapC.lean:2221–2235` (NODE C.62's booked hypothesis bundle: the
  Tier-1-iterated composed singleton over a `TowerDatum`).
* `ClassSizeSupplyData` — leanspec `ChapC.lean:2343–2356` (NODE C.69, the class-size/block-length
  TERMINAL SUPPLY bundle — `Prop`-valued, clause 1 = C.63, clause 2 = C.64, clause 3 = C.67).
* `Mu2TwoCase` — leanspec `ChapC.lean:3499–3504` (NODE C.79's five-case decision tag for the
  `μ₂* = 2` table).
* `pmul`, `padd`, `psmul`, `Phi1`, `Phi2`, `Phi3` — leanspec `ChapC.lean:4292–4307` (C.97's
  numeric-gate witness polynomials over `List ℤ` at `q = 2`; C.97 itself carries no signature,
  defect D1 — these are the audit script's own defs, not blueprint declarations).

**Not landed in this file** (see `runs/wave-b/verdict_DT1.md` for the full verdict):
`DescentStep` and `NS7TerminationStatement` (leanspec `ChapC.lean:1726–1759`) are the A-C.1
draft, machine-REFUTED and explicitly struck in leanspec itself — *"kept for the record and MUST
NOT BE CONSUMED"* (leanspec `ChapC.lean:1761–1780`). The A-C.6 redraft that supersedes them,
`DescentStepR` / `NS7TerminationStatementR`, is already landed in `Uniformity.ChapC.C94`; landing
the struck names here would create a dead/trap twin, so both are SKIPPED.

## Status

Sorry-free, axiom-free, `unsafe`-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### NODE C.62 [theorem] — Tier 1 iterated: `ComposedLabel` + the composed singleton
[signed: A-C.1; the hypothesis bundle IS the booked `ComposedLabel` structure] -/

structure ComposedLabel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (g : Polynomial O) : Type _ where
  u₃ : ℕ
  ℓ₃ : ℕ
  r₂ : Polynomial (AdjoinRoot (towerLabel T))
  hℓ₃ : 0 < ℓ₃
  hcop : Nat.Coprime u₃ ℓ₃
  hfloor : ℓ₃ * T.E₂ < u₃
  hr₂ : r₂.Monic ∧ Irreducible r₂ ∧ 0 < r₂.natDegree ∧ r₂.coeff 0 ≠ 0
  hgmonic : g.Monic
  hgdeg : g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree)
  hpure1 : IsDvPure F g T.u₂ T.e₂
  hxpure : IsPure Polynomial.X g F.h F.e₁
  hne₂ : (dv2SideSet (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃).Nonempty
  hres₂ : dv2ResPoly (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃ hne₂ = r₂

/-! ### NODE C.69 [theorem] — THE SUPPLY BUNDLE [signed: A-C.1 as a Prop-structure with the
three clause fields quoting the suppliers' statements — "the NAME is the contract"] -/

-- the per-clause `hπ`/adic-completeness binders quote the suppliers' own signatures (C.63/
-- C.64/C.67) verbatim; each is threaded but not used in the clause body, exactly as signed.
set_option linter.unusedVariables false in
/-- the bundled class-size/block-length supply (clause 1 = C.63, clause 2 = C.64, clause 3 =
C.67), packaged so downstream chapters cite ONE name with per-clause hypotheses readable. -/
structure ClassSizeSupplyData {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : Prop where
  separable_side : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : Finite (ResidueField O))
    {g : Polynomial O}, g.Monic → IsDvPure F g L.u L.ℓ →
    IsPure Polynomial.X g F.h F.e₁ →
    ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      (dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp).Separable →
      ∃ (s : Finset (Polynomial (F.stageField H₀ hpin)))
        (Fac : Polynomial (F.stageField H₀ hpin) → Polynomial O),
        g = ∏ r ∈ s, Fac r ∧
        ∀ r ∈ s, (Fac r).Monic ∧ (Fac r).natDegree = (F.e₁ * F.f₁) * L.ℓ * r.natDegree ∧
          ((∀ g' ∈ monicFactors (Fac r), (F.f₁ * r.natDegree) ∣ inertiaDegOf g') →
            typeOf (Fac r) = ⟨{(F.e₁ * L.ℓ, F.f₁ * r.natDegree)}⟩ ∧ Irreducible (Fac r))
  read_form : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    {f : Polynomial O}, BlockContext L f →
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
  mixed_tie : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    {f : Polynomial O}, BlockContext L f → ∀ {m : ℕ}, 0 < m →
    (∀ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
      L.r ^ m ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp ∧
      ¬ L.r ^ (m + 1) ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp) →
    mult₂ L f = m

/-! ### NODE C.79 [theorem] — the `μ₂* = 2` decision table [signed: A-C.1; the five rows as
an inductive case tag (GC-4's domain licence), σ per case, boxes inside] -/

inductive Mu2TwoCase where
  | twoSides : Mu2TwoCase
  | halfInteger : Mu2TwoCase
  | inertQuadratic : Mu2TwoCase
  | split : Mu2TwoCase
  | doubleRoot : Mu2TwoCase

/-! ### C.97's numeric-gate witness polynomials (no signature, D1) — verbatim `List ℤ` audit
defs, carried with their two prerequisite arithmetic helpers `pmul`/`padd`/`psmul` (leanspec
`ChapC.lean:4292–4307`; `v2`/`isPure2` and the later `#eval`/`#guard` rows are NOT part of this
batch — only `Phi1`/`Phi2`/`Phi3` and what they need to elaborate). -/

def pmul (a b : List ℤ) : List ℤ :=
  (List.range (a.length + b.length - 1)).map (fun k =>
    ((List.range (k + 1)).map (fun i => (a.getD i 0) * (b.getD (k - i) 0))).sum)

def padd (a b : List ℤ) : List ℤ :=
  (List.range (max a.length b.length)).map (fun k => a.getD k 0 + b.getD k 0)

def psmul (c : ℤ) (a : List ℤ) : List ℤ := a.map (fun x => c * x)

def Phi1 : List ℤ := [-2, 0, 1]                                 -- Φ′ = x² − 2
def Phi2 : List ℤ := padd (pmul Phi1 Phi1) [0, -4]              -- Φ₂ = Φ′² − 4x
def Phi3 : List ℤ := padd (pmul Phi2 Phi2) (psmul (-16) Phi1)   -- Φ₃ = Φ₂² − 16Φ′

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ComposedLabel
#print axioms Uniformity.Density.Tower.ClassSizeSupplyData
#print axioms Uniformity.Density.Tower.Mu2TwoCase
#print axioms Uniformity.Density.Tower.pmul
#print axioms Uniformity.Density.Tower.padd
#print axioms Uniformity.Density.Tower.psmul
#print axioms Uniformity.Density.Tower.Phi1
#print axioms Uniformity.Density.Tower.Phi2
#print axioms Uniformity.Density.Tower.Phi3

end AxCheck
