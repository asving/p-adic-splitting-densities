/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03
import Uniformity.ChapB.B26

/-!
# Uniformity.ChapC.C04 — `card_stageField`: the stage residue field is `F_{Q^{f₁}}`

**Chapter C, NODE C.04** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C3 (`[Finite (ResidueField O)]`,
`hπ` explicit). One signed public declaration; the field / finiteness / `finrank` clauses of the
blueprint STATEMENT are carried by private companions in this file, exactly as the SIGNATURE
block prescribes (*"with the `Field`/`Finite`/`finrank` clauses as instance/companion statements
in the same file (private helpers below the public declaration; the public name is
`card_stageField`)"*).

*The stage residue field is a finite field of the predicted size.* For a frame `F` (C.01) with a
correct pin `H₀` (C.03), the stage field `K = stageField F H₀ hpin = AdjoinRoot ψ` — where
`ψ = frameRes F H₀ hpin` is the frame residual — satisfies

  `Nat.card K = residueCard O ^ F.f₁`

i.e. `|K| = Q^{f₁} = stageCard F` (C.03), which is the numeral half of `EFF.HE6.08`'s
`K := F_Q(η_θ) ≅ F_{Q^{f₁}}`. C.03 deliberately left the carrier and the number as formally
independent objects; this node is the identity that joins them, and it is the identity chapter E
and chapter D consume whenever they count residues at a tower level.

## The two-step count, and why it does not go through `card_resField`

The count is a TOWER count, run over the order-0 residual field rather than over
`ResidueField O`:

1. `Module.finrank (resField X) (stageField F H₀ hpin) = F.f₁` — the power basis
   `AdjoinRoot.powerBasis` of `ψ` has dimension `ψ.natDegree`, and `ψ.natDegree = F.f₁` is the
   second component of the frame's own `hresirr` field (C.01). This is B.26(a)'s route one level
   up.
2. `Nat.card (resField X) = residueCard O` — the order-0 residual field is the residue field
   itself, since `X.map (residue O) = X` has degree `1`.

`Module.natCard_eq_pow_finrank` then gives `Nat.card K = (Nat.card (resField X)) ^ f₁`.

Step 2 is **re-proved here rather than cited from B.26(c)** (`card_resField`). The reason is an
environment mismatch, not a mathematical one: `card_resField` sits in B.26's `ENVC` section and
its elaborated signature carries `[IsAdicComplete (maximalIdeal O) O]`, which C.04's A-C.1-signed
signature does not bind (ENV-C3 = ENV-C1 + residue finiteness, no completeness). The signature is
frozen, so the completeness-free two-line re-derivation `card_resField_X` is the only route that
lands on the signed type. Its proof is B.26(c)'s proof with `φ := X`, minus the section
hypothesis it never used.

## D9 — `IsKey X`, the missing base-field fact

`AdjoinRoot.powerBasis` needs a `Field` structure on the BASE `resField X`, and B.25(b)'s
`instFieldResField` is keyed on `IsKey φ` — a hypothesis no landed node discharges at the order-0
key. Defect **D9** of the stub gate (`leanspec/Leanspec/ChapC.lean`) records this and exhibits the
cure; the cure is landed here as the private `isKey_X` (`X` is monic, of degree `1 > 0`, and
`X.map (residue O) = X` is irreducible over the residue field). It is `private` because it is a
stub-side helper, NOT a blueprint node: the public D9 cure belongs to whichever node the amendment
set assigns it, and a private copy cannot collide with that.

Note the contrast recorded at C.01: `IsKey F.key` is FALSE for a frame with `1 ≤ F.h`. `isKey_X`
is about the order-0 key `X`, which is the base of the whole tower, not about the frame's key.

## `hπ`

`hπ : Irreducible π` is bound by ENV-C3 and by the signed signature, and the proof does not use
it: the count is a dimension count over `resField X`, and `π` enters only through `frameRes`'s
digit reduction, whose output irreducibility and degree are supplied wholesale by `F.hresirr`. The
binder is kept (the signature is frozen) and the unused-variable linter is silenced for that
declaration with this as the reason.

**DEPENDS.** C.01 (`KeyFrame`, `hresirr`) · C.03 (`frameRes`, `stageField`, `stageCard`) ·
B.01 (`IsKey`) · B.25 (`resField`, `instFieldResField`) · B.26 (the level-1 templates
(a) `finrank_resField`, (b) `instFiniteResField`, (c) `card_resField` — used as PATTERNS; see the
environment note above for why (c) is re-proved rather than applied) · landed `residueCard`
(`Uniformity/Density/LocalData.lean`) — all by committed node ID (GC-13(b)). The imports are
`Uniformity.ChapC.C03` and `Uniformity.ChapB.B26`.

**PROOF.** As the blueprint's three steps, with step 3's base count run at `resField X` instead of
at `ResidueField O` (same value, and it keeps the tower shape that C.12 iterates):
1. `F.hresirr H₀ hpin` gives `Irreducible ψ` and `ψ.natDegree = f₁`; `AdjoinRoot` of a nonzero
   polynomial over a field has a power basis, and `Fact (Irreducible ψ)` upgrades it to a field.
2. `finrank = ψ.natDegree = f₁` via `PowerBasis.finrank` + `AdjoinRoot.powerBasis_dim`.
3. `Nat.card = (Nat.card (resField X)) ^ f₁` by `Module.natCard_eq_pow_finrank`, and
   `Nat.card (resField X) = residueCard O ^ 1` by the same route at `φ = X`.

SOURCE: `EFF.HE6.08` (`K ≅ F_{Q^{f₁}}`); GC-7 (the statement-shape mandate: card/finrank
bookkeeping at every `AdjoinRoot` iterate).

**TEETH.** `HE6R1` frame audit `K₂ = F_{p²}` (`EFF.HE6R1.18`, arithmetic-audit row
"`[K₂:K] = d_r = 2` and `K = F_p` (since `f₁ = 1`), so `K₂ = F_{p²}` ✓") → **Lean theorem**, this
node at the C.12 iterate; the numeric leg re-fires at blueprint §13.

ENVIRONMENT: ENV-C3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers (stub-gate defect **D9**, and the completeness-free base count) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense — monic, of positive
degree, with irreducible reduction (`X.map (residue O) = X`). Nothing in `leanfinal` said so, and
B.25(b)'s `Field (resField φ)` is keyed on exactly this. `private`: a stub-side helper, not a
blueprint node. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- The order-0 residual field is the residue field, as a count: `|resField X| = Q`.
B.26(c)'s proof at `φ = X`, without the `[IsAdicComplete …]` section hypothesis that B.26's
elaborated signature carries and C.04's signed signature does not bind. -/
private theorem card_resField_X :
    Nat.card (resField (Polynomial.X : Polynomial O)) = residueCard O := by
  have hne : ((Polynomial.X : Polynomial O).map (residue O)) ≠ 0 :=
    (isKey_X (O := O)).irred.ne_zero
  haveI : Module.Finite (ResidueField O) (resField (Polynomial.X : Polynomial O)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfr : Module.finrank (ResidueField O) (resField (Polynomial.X : Polynomial O)) = 1 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne]
    simp
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O), hfr, pow_one]
  rfl

/-- The order-0 residual field is finite. B.26(b)'s route at `φ = X`, likewise
completeness-free. -/
private theorem finite_resField_X [Finite (ResidueField O)] :
    Finite (resField (Polynomial.X : Polynomial O)) := by
  haveI : Module.Finite (ResidueField O) (resField (Polynomial.X : Polynomial O)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (isKey_X (O := O)).irred.ne_zero).basis
  exact Module.finite_of_finite (ResidueField O)

/-- **The `Field` clause of C.04's STATEMENT.** `Fact (Irreducible ψ)` comes from the frame's
`hresirr`, the base `Field` from D9's `isKey_X`. A `@[reducible] noncomputable def`, not an
`instance`, for B.25(b)'s reason (an `instance` with the explicit non-class hypotheses `F`/`hpin`
is rejected at our pin); consumers write `letI := fieldStageField F H₀ hpin`. -/
@[reducible] private noncomputable def fieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- **The `finrank` clause of C.04's STATEMENT.** `[K : resField X] = f₁` — the power basis of
`ψ` has dimension `ψ.natDegree`, and the frame pins `ψ.natDegree = f₁`. -/
private theorem finrank_stageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Module.finrank (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) = F.f₁ := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨hirr, hdeg⟩ := F.hresirr H₀ hpin
  have hψ0 : F.frameRes H₀ hpin ≠ 0 := hirr.ne_zero
  rw [(AdjoinRoot.powerBasis hψ0).finrank, AdjoinRoot.powerBasis_dim hψ0]
  exact hdeg

/-- **The `Finite` clause of C.04's STATEMENT.** `K` is a finite-dimensional space over the
finite field `resField X`. -/
private theorem finite_stageField (F : KeyFrame O π) [Finite (ResidueField O)] (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Finite (F.stageField H₀ hpin) := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI := finite_resField_X (O := O)
  have hψ0 : F.frameRes H₀ hpin ≠ 0 := (F.hresirr H₀ hpin).1.ne_zero
  haveI : Module.Finite (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hψ0).basis
  exact Module.finite_of_finite (resField (Polynomial.X : Polynomial O))

/-! ### The signed declaration -/

-- `hπ` is bound by ENV-C3 and by the A-C.1-signed signature; the count never reads it (`π`
-- enters only inside `frameRes`, whose irreducibility and degree the frame supplies wholesale).
-- The binder cannot be dropped — the signature is frozen.
set_option linter.unusedVariables false in
/-- **C.04 — the stage residue field has `Q^{f₁}` elements.** `|K| = |F_Q|^{f₁} = stageCard F`,
i.e. the numeral half of `EFF.HE6.08`'s `K ≅ F_{Q^{f₁}}`. -/
theorem KeyFrame.card_stageField (F : KeyFrame O π) [Finite (ResidueField O)]
    (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Nat.card (F.stageField H₀ hpin) = residueCard O ^ F.f₁ := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  have hψ0 : F.frameRes H₀ hpin ≠ 0 := (F.hresirr H₀ hpin).1.ne_zero
  haveI : Module.Finite (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hψ0).basis
  rw [Module.natCard_eq_pow_finrank (K := resField (Polynomial.X : Polynomial O)),
    finrank_stageField F H₀ hpin, card_resField_X]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.card_stageField

end AxCheck
