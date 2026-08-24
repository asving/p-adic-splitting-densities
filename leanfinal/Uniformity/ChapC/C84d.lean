/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C42
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C84d — `TowerDatum.deepTower`: the concrete depth-2 chain, CONSTRUCTED

**Chapter C, §10 preamble** [def+theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §10, the
GENTOW2 supply layer's preamble constants; twin `leanspec/Leanspec/ChapC.lean` ~L2420, where both
declarations are stub-carried as AXIOM CONSTANTS with the recorded gloss *"def-kind with
theorem-grade fields; stub-carried as an axiom constant + data clauses, the C.45/C.97 rule"*).
**ENV-C1.**  Unit TDW.

The shared infrastructure whose absence blocked even STATING the C.100–C.103 GENTOW2 twins
(flagged independently at `C84.lean:110`, `C99gt.lean`, `C102gt.lean`): the promotion of a
depth-2 `TowerDatum` (C.42) to a `DeepTower F H₀ hpin 2` (C.83), i.e. the concrete two-rung
chain every §10 statement is typed at.  Following the C.45 precedent (`towerLabelEquiv`,
stub-carried as an axiom constant, landed as a real `noncomputable def`), both leanspec axiom
constants are REALIZED here — `deepTower` as a definition, `deepTower_data` as a theorem —
with **signatures byte-identical to the stubs'** (modulo `axiom` → `noncomputable def` /
`theorem`).

## The construction (the two-rung telescope)

C.83's GC-7 fallback carrier asks for abstract level fields `fld i` tied to the `AdjoinRoot`
iterate by `RingEquiv` witnesses.  At depth 2 the honest telescope is:

* `fld 1 := F.stageField H₀ hpin` — rung 1 IS the frame's stage field `K₁` (C.03), with
  `base := RingEquiv.refl _`;
* `fld 2 := AdjoinRoot T.ψ₂` — rung 2 is the `ψ₂`-iterate itself, `K₂ = K₁(β₂)`, with the live
  residual `ψ 1 := T.ψ₂` and `step 1 := RingEquiv.refl _` (the iterate witness is definitional,
  not merely up-to-isomorphism);
* stage data `(e, f, u)` at rung 1 = the frame's `(e₁, f₁, h)`, at rung 2 = the datum's
  `(e₂, f₂, u₂)`.

Every constraint field of `DeepTower` is discharged from the corresponding `TowerDatum` field:
properness at rung 2 is `T.hcomp`, coprimality is `T.hcop`, the floor chain at the single live
rung is `T.hfloor` re-associated (`e₂·(e₁f₁)·h < u₂  ⇒  e₂·((e₁f₁)·h) < u₂`), and `hψ` at the
single live residual is the conjunction of `T.hψmonic / hψirr / hψdeg / hψ0` verbatim.  The
`Field` data: `fld 1` is a field because the frame residual is irreducible (`F.hresirr`, C.03's
note — the same `instFieldResField isKey_X` + `Fact` route as C.97's `s2StageFieldInst`, here at
the abstract frame); `fld 2` is a field because `ψ₂` is irreducible over it (`T.hψirr`,
`AdjoinRoot.instField`).  Both instances are `@[reducible]` so the `CommRing` they induce is
the ambient `AdjoinRoot` one (C.97's discipline).

## Junk conventions (C.83's off-range discipline, applied)

`e/f/u/fld/ψ` are TOTAL (`ℕ`-indexed); off the live range `1 … 2` no lemma may read them.  The
junk values chosen: `e/f/u` constant-extend (`i = 0` and `i ≥ 3` return the rung-2 numerals),
`fld 0` is a junk copy of the stage field, `fld i (i ≥ 3)` a junk copy of `AdjoinRoot T.ψ₂`, and
the junk residuals are `Polynomial.X` (never read: `hψ` quantifies exactly `1 ≤ i < 2`).

## The carried hypothesis `hπ`

`hπ : Irreducible π` is the signed signature's and is kept byte-for-byte; **it is not consumed**
— every obligation is discharged from `T`'s own fields (`hresirr` is a `KeyFrame` field, so the
stage-field instance needs no `hπ` either).  It is the §10 consumers (`levelDatum`-side reads)
that consume `hπ`, not the chain object.  Flagged rather than dropped: the C.97 "two carried
hypotheses" precedent, applied to the stub signature.

**⚠ Mandatory, trust-boundary definition.**  `deepTower` realizes a stub-carried axiom constant
as a construction; the telescope reading above (rungs definitionally the iterate, junk
conventions as listed) is the substantive content.  **Flagged for human review** (parent
CLAUDE.md trust boundary).

**DEPENDS.** C.83 (`DeepTower`, the carrier) · C.42 (`TowerDatum`, the datum consumed) · C.03
(`stageField`, `frameRes`) · C.14a (`KeyFrame.Pin`, the signed pin binder) · B.25
(`instFieldResField`) — imported.  By committed node ID: C.97 (the construction template —
`s2StageFieldInst`'s reducible-instance discipline) · C.130s2 (the S2 bridge these general
lemmas mirror; NOT imported — no concrete numeral is consumed here).

**PROOF.** Definitional throughout; the two non-`rfl` legs are the floor re-association
(`mul_assoc`) and the `Finset.Icc 1 2` product unfolding in the `Dcum` companion.

**SOURCE.** leanspec `ChapC.lean` §10 preamble (the two stub axioms, verbatim);
`EFF.GENTOW5.14`–`.16` via C.83 (the telescope the depth-2 instance instantiates).

**TEETH.** Not dischargeable at these binders (abstract frame, no numerals — C.15's D7 rider).
The local substitutes are the companions: `deepTower_data`'s four clauses (the signed data
pins), `deepTower_Dcum` / `deepTower_Econst` (the bookkeeping ties `Dcum 2 = D₂`,
`Econst 2 = E₂` against C.42's independent definitions — an `e₂ ↔ f₂` swap or a dropped frame
factor breaks a compile), and `deepTower_psi_one` (the live-residual pin, whose elaboration is
itself the type-level bridge, as at CC-2's `s2Bridge_ψ`).

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  Both leanspec §10 preamble constants realized;
the C.100–C.103 signatures become statable against this file.
-/

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The `Field` data of the two rungs -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- The `Field` structure on the frame's stage field `K₁ = stageField` at ANY frame, from the
frame's own `hresirr` (C.03's note: `AdjoinRoot (frameRes …)` is a field exactly because the
frame residual is irreducible).  This is C.97's `s2StageFieldInst` at the abstract frame.
Reducible so that the `CommRing` it induces is the ambient `AdjoinRoot` one. -/
@[reducible] noncomputable def KeyFrame.stageFieldInst (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- The `Field` structure on the rung-2 carrier `K₂ = AdjoinRoot ψ₂`, from the datum's own
`hψirr`.  Reducible for the same reason as `stageFieldInst`. -/
@[reducible] noncomputable def TowerDatum.adjoinPsi₂FieldInst {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) : Field (AdjoinRoot T.ψ₂) :=
  letI : Field (F.stageField H₀ hpin) := F.stageFieldInst H₀ hpin
  haveI : Fact (Irreducible T.ψ₂) := ⟨T.hψirr⟩
  AdjoinRoot.instField

/-! ## The two-rung field telescope -/

/-- The depth-2 field telescope: `fld 1 = K₁` (the frame's stage field, C.03),
`fld 2 = K₂ = AdjoinRoot ψ₂` (the `ψ₂`-iterate); junk copies off the live range
(`fld 0 = K₁`, `fld (i+3) = K₂` — nothing reads them, C.83's off-range discipline). -/
noncomputable def TowerDatum.deepFld {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : ℕ → Type _
  | 0 => F.stageField H₀ hpin
  | 1 => F.stageField H₀ hpin
  | _ + 2 => AdjoinRoot T.ψ₂

/-- The telescope's `Field` data, rung by rung (`stageFieldInst` at `0`/`1`,
`adjoinPsi₂FieldInst` at `≥ 2`). -/
@[reducible] noncomputable def TowerDatum.deepFldField {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) : ∀ i, Field (T.deepFld i)
  | 0 => F.stageFieldInst H₀ hpin
  | 1 => F.stageFieldInst H₀ hpin
  | _ + 2 => T.adjoinPsi₂FieldInst

/-! ## The signed declarations (leanspec §10 preamble, `axiom` → `def`/`theorem`) -/

-- `hπ` is the signed signature's and is unused by the construction; see the module
-- docstring's carried-hypothesis section (the C.97 precedent).
set_option linter.unusedVariables false in
/-- **The depth-2 chain of a tower datum** (leanspec §10 preamble, stub-carried as an axiom
constant, REALIZED per the C.45/C.97 rule): the two-rung `DeepTower` whose rung 1 is the frame
and whose rung 2 is the datum's inner stage `(e₂, f₂, u₂, ψ₂)`, on the telescope
`fld 1 = K₁`, `fld 2 = AdjoinRoot ψ₂` with DEFINITIONAL iterate witnesses
(`base = step = RingEquiv.refl`).  Every theorem-grade field is discharged from `T`'s own
fields; see the module docstring. -/
noncomputable def TowerDatum.deepTower {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : DeepTower F H₀ hpin 2 :=
  letI : Field (F.stageField H₀ hpin) := F.stageFieldInst H₀ hpin
  letI : Field (AdjoinRoot T.ψ₂) := T.adjoinPsi₂FieldInst
  letI : ∀ i, Field (T.deepFld i) := T.deepFldField
  { e := fun i => match i with | 1 => F.e₁ | _ => T.e₂
    f := fun i => match i with | 1 => F.f₁ | _ => T.f₂
    u := fun i => match i with | 1 => F.h | _ => T.u₂
    fld := T.deepFld
    fldField := T.deepFldField
    ψ := fun i => match i with
      | 0 => Polynomial.X
      | 1 => T.ψ₂
      | _ + 2 => Polynomial.X
    he1 := rfl
    hf1 := rfl
    hu1 := rfl
    he := fun i h1 h2 => by
      interval_cases i
      · exact F.he₁
      · exact T.he₂
    hf := fun i h1 h2 => by
      interval_cases i
      · exact F.hf₁
      · exact T.hf₂
    hproper := fun i h1 h2 => by
      interval_cases i
      exact T.hcomp
    hcop := fun i h1 h2 => by
      interval_cases i
      exact T.hcop
    hfloor := fun i h1 h2 => by
      interval_cases i
      have h := T.hfloor
      rw [mul_assoc] at h
      exact h
    hψ := fun i h1 h2 => by
      interval_cases i
      exact ⟨T.hψmonic, T.hψirr, T.hψdeg, T.hψ0⟩
    base := RingEquiv.refl _
    step := fun i h1 h2 =>
      match i, h1, h2 with
      | 1, _, _ => RingEquiv.refl _
      | 0, h1, _ => absurd h1 (by decide)
      | _ + 2, _, h2 => absurd h2 (by omega) }

/-- **The chain's data clauses** (leanspec §10 preamble, stub-carried as an axiom constant,
PROVED): the rung-2 data of `T.deepTower hπ` is the datum's `(e₂, f₂, u₂)`, and the rung-2
carrier is the `ψ₂`-iterate.  All four clauses are definitional at the construction — the
`Nonempty` witness is `RingEquiv.refl`, since `fld 2` IS `AdjoinRoot ψ₂`. -/
theorem TowerDatum.deepTower_data {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).e 2 = T.e₂ ∧ (T.deepTower hπ).f 2 = T.f₂ ∧
    (T.deepTower hπ).u 2 = T.u₂ ∧
    Nonempty ((T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂) :=
  ⟨rfl, rfl, rfl, ⟨RingEquiv.refl _⟩⟩

/-! ## Companions — the anti-drift pins (this node's teeth substitutes) -/

/-- Rung-1 data = the frame's, definitionally (C.83's `he1/hf1/hu1`, read back off the
construction). -/
theorem TowerDatum.deepTower_stage1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).e 1 = F.e₁ ∧ (T.deepTower hπ).f 1 = F.f₁ ∧
      (T.deepTower hπ).u 1 = F.h :=
  ⟨rfl, rfl, rfl⟩

/-- The rung-1 carrier IS the frame's stage field (a type equality, definitional). -/
theorem TowerDatum.deepTower_fld_one {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).fld 1 = F.stageField H₀ hpin := rfl

/-- The rung-2 carrier IS `AdjoinRoot ψ₂` (a type equality, definitional) — the strong form of
`deepTower_data`'s `Nonempty` clause. -/
theorem TowerDatum.deepTower_fld_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).fld 2 = AdjoinRoot T.ψ₂ := rfl

/-- The live residual IS the datum's `ψ₂` (that this equality ELABORATES — `fld 1` is
definitionally the stage field — is itself the type-level bridge, as at CC-2's
`s2Bridge_ψ`). -/
theorem TowerDatum.deepTower_psi_one {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).ψ 1 = T.ψ₂ := rfl

/-- The bookkeeping tie `Dcum 2 = D₂`: the chain's cumulative degree at the top rung is C.42's
independently-defined composed degree `D₂ = (e₁f₁)(e₂f₂)` (the degree of C.43's `Φ₂`). -/
theorem TowerDatum.deepTower_Dcum {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).Dcum 2 = T.D₂ := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

/-- The bookkeeping tie `Econst 2 = E₂`: the chain's rung-2 side constant is C.42's
independently-defined `E₂ = e₂f₂u₂` (definitional). -/
theorem TowerDatum.deepTower_Econst {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).Econst 2 = T.E₂ := rfl

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageFieldInst
#print axioms Uniformity.Density.Tower.TowerDatum.adjoinPsi₂FieldInst
#print axioms Uniformity.Density.Tower.TowerDatum.deepFld
#print axioms Uniformity.Density.Tower.TowerDatum.deepFldField
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_data
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_stage1
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_fld_one
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_fld_two
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_psi_one
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_Dcum
#print axioms Uniformity.Density.Tower.TowerDatum.deepTower_Econst

end AxCheck
