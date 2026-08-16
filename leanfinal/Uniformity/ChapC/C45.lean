/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C12
import Uniformity.ChapC.C44

/-!
# Uniformity.ChapC.C45 — `towerLabelEquiv`: HETOW-1(b), the field form `K(β) = K(η₂)`

**Chapter C, NODE C.45** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys
and the tower bridges; the A-C.1 amendment set governs). **ENV-C1**. One signed declaration.

HETOW-1(b). Over a frame `F` (C.01) pinned at `H₀` (C.03) with a tower datum `T` (C.42), the two
level-2 carriers coincide:

`towerLabelEquiv T hπ : AdjoinRoot (towerLabel T) ≃ₐ[K] AdjoinRoot T.ψ₂`,

with `K = F.stageField H₀ hpin`.

The left-hand carrier is C.12's `level2Field (T.levelDatum hπ)` — `K(β)`, the field the whole
§5 dictionary reads at, since C.44's `TowerDatum.levelDatum` fills the `r`-field with
`towerLabel T`. The right-hand carrier is `K(η₂)`, the inner residual's own root field. The
isomorphism is the corpus's pointwise affine substitution `β_{x₀} = η_{x₀}^{−Q}·η₂(x₀)` recast as
a map of quotients: **the root equivalence is the `K`-affine substitution `Z ↦ η^{Q}Z`**.

## What is actually constructed (and why it is not `algEquivOfEq`)

Write `η = F.stageLetter H₀ hpin` (C.19), `Q = F.twistExp T.u₂` (C.15), and

`a := η^Q`,  `c := (η⁻¹)^{Q·f₂}`,  so that (C.44, by `rfl`)

`towerLabel T = C c * ψ₂.comp (C a * X)`.

The two carriers are quotients of `K[Z]` by *different* ideals — `span {towerLabel T}` and
`span {ψ₂}` — so no `AdjoinRoot.algEquivOfEq`/`algEquivOfAssociated` applies: the polynomials are
not associated, they are related by an automorphism of `K[Z]`. The construction is therefore the
pair of `AdjoinRoot.liftAlgHom`s that send each root to the substituted other root,

`β = root (towerLabel T) ↦ a⁻¹ · η₂`,   `η₂ = root T.ψ₂ ↦ a · β`,

glued by `AlgEquiv.ofAlgHom`. Both root images are legitimate because of the two `aeval` clauses
proved inline:

* `aeval (a⁻¹·η₂) (towerLabel T) = c · ψ₂(a·a⁻¹·η₂) = c · ψ₂(η₂) = 0` — the forward leg;
* `0 = (towerLabel T)(β) = c · ψ₂(a·β)`, and `c` is a **unit** of `K`, so `ψ₂(a·β) = 0` — the
  backward leg. The unitness is used through `algebraMap c⁻¹ * (algebraMap c * y) = y`; no
  injectivity of `K → AdjoinRoot (towerLabel T)` is needed, hence no nontriviality side condition.

Both round trips collapse by `a·a⁻¹ = 1` in `K`, checked on the generator via
`AdjoinRoot.algHom_ext` (an `AlgHom` out of `AdjoinRoot p` is determined by its value at
`root p`).

`a ≠ 0` and `c ≠ 0` are `pow_ne_zero` off C.19's `stageLetter_ne_zero` — **the only place `hπ` is
consumed**, exactly as at C.44: the letter's unitness is what makes `Z ↦ η^Q Z` invertible, and
without it the substitution is not an automorphism and the node is false.

## Divergences carried from the gate-verified twin

* **the pin binder.** `KeyFrame.Pin` is C.14a's abbreviation and C.14a has not landed, so the pin
  hypothesis is written out in full, exactly as C.03/C.09/C.42/C.44 already do (the A-C.1/D4
  convention). Same proposition, spelled.
* **the twin's `axiom` is DISCHARGED.** `leanspec/Leanspec/ChapC.lean` stub-carries this node as
  an `axiom towerLabelEquiv`; the blueprint's SIGNATURE field says in so many words that "the
  fleet lands the `AdjoinRoot`-equiv construction". It is landed here as a genuine
  `noncomputable def`, Lean-core axioms only. No axiom is added to the corpus.
* **`isKey_X` re-declared `private`.** C.04/C.12/C.19/C.44 each carry their own private copy
  (defect D9's cure) because private declarations are not importable; this file needs it to name
  the base `Field (resField X)`, from which — with `Fact (Irreducible (F.frameRes H₀ hpin))` —
  instance search produces the `Field K` that gives `K` its `Inv` (the D9 rider on C.44's
  `towerLabel`: `stageField` has no `Inv` without the two `letI`s). When C.14a lands a public
  `isKey_X`, all five retire to it — a RE-PLAN item, not a silent addition here.
* **`aeval_C_mul_comp` is a stub-side helper, not a node.** A three-line generic `CommRing`
  identity (`aeval x (C c * p.comp (C a * X)) = c · p(a·x)`), stated over abstract `K`/`A` so that
  it can be applied at BOTH carriers without dragging the frame's instance stack through it.
* **the `level2Field` identification is CHECKED, not asserted.** The blueprint's STATEMENT names
  the left carrier `level2Field (T.levelDatum)` where the SIGNATURE writes
  `AdjoinRoot (towerLabel T)`; C.12 is therefore imported (its only role here) and the anonymous
  `example` at the foot of the file elaborates `towerLabelEquiv T hπ` at the blueprint's type. It
  is an `example`, so no second name is added and GC-6.5 holds.

## Faithfulness

**Interface-only.** This node asserts an isomorphism of carriers and nothing numeric; the blueprint
records its TEETH as *signed non-applicable* ("an interface iso; guarded through C.46's residue
values"), so no §13 regression row attaches here. The trust-boundary reading is the direction of
the substitution: `EFF.HETOW.15`(b)/`EFF.HETOW.16`(b) give `β = η^{−Q}·η₂`, i.e. the map sending
the label root to `a⁻¹·η₂` with `a = η^{Q}` — that is `towerLabelEquiv`'s FORWARD leg, and the
`symm` direction is the one that sends `η₂ ↦ η^{Q}·β`. Composing the two in the wrong order is the
classic sign slip here, and the two round-trip proofs are precisely what rules it out.

The corpus flags this substitution **POINTWISE, hence wrap-free**: only the single height `u₂` is
normalized, so `Q = twistExp u₂` occurs alone and never as a product of normalizers. C.43's
`composedKey`, by contrast, DOES carry the wrap `W(t)`; the two must not be conflated.

**DEPENDS.** C.12 (`level2Field` — the carrier this equivalence is *about*; the left side of the
statement is `level2Field (T.levelDatum hπ)` after C.44) · C.44 (`towerLabel`, and its `rfl`-grade
explicit form) · C.42 (`TowerDatum`) · C.19 (`stageLetter`, `stageLetter_ne_zero`) · C.15
(`twistExp`) · C.01/C.03 (the frame, `frameRes`, `stageField`) · B.25 (`resField`,
`instFieldResField`) — by committed node ID (GC-13(b)). Mathlib: `AdjoinRoot.liftAlgHom`,
`AdjoinRoot.liftAlgHom_root`, `AdjoinRoot.algHom_ext`, `AdjoinRoot.aeval_eq`,
`AdjoinRoot.mk_self`, `AlgEquiv.ofAlgHom`, `AlgHom.commutes`, `Polynomial.aeval_comp`.

**PROOF.** The substitution `Z ↦ η^Q·Z` maps `towerLabel T` to a unit multiple of `ψ₂`; the two
quotients are therefore canonically isomorphic, realized by the `liftAlgHom` pair above.

SOURCE: `EFF.HETOW.15`(b)/`EFF.HETOW.16`(b) (the two-factor split + "POINTWISE, hence wrap-free:
only the single height `u₂` is normalized — no product of normalizers occurs").

**TEETH.** signed non-applicable (an interface iso; guarded through C.46's residue values).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers (stub-gate defect **D9**, and one generic `aeval` identity) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense. C.04/C.44's private
copy, re-declared because private declarations are not importable. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- **Stub-side helper, not a blueprint node.** The affine-substitution evaluation law
`aeval x (C c * p.comp (C a * X)) = c · p(a·x)`, over an arbitrary base — the one computation both
legs of C.45 run, at two different carriers. -/
private theorem aeval_C_mul_comp {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (c a : K) (p : Polynomial K) (x : A) :
    Polynomial.aeval x (Polynomial.C c * p.comp (Polynomial.C a * Polynomial.X))
      = algebraMap K A c * Polynomial.aeval (algebraMap K A a * x) p := by
  simp [Polynomial.aeval_comp]

/-! ### The signed declaration -/

/-- **C.45 — HETOW-1(b), field form: `K(β) = K(η₂)`.** The algebra isomorphism induced by the
affine substitution `β ↦ η^{−Q}·η₂` (`EFF.HETOW.15`(b)), realized as the `AdjoinRoot`-equivalence
`root (towerLabel T) ↦ (η^Q)⁻¹ · root ψ₂` with inverse `root ψ₂ ↦ η^Q · root (towerLabel T)`.
The twin carries this as an axiom; it is CONSTRUCTED here. `hπ` is consumed exactly once, through
C.19's `stageLetter_ne_zero` (the letter's unitness is what makes `Z ↦ η^Q Z` invertible).
[A-C.1/D4: the pin binder is written out, as at C.03/C.09/C.42/C.44.] -/
noncomputable def towerLabelEquiv {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    AdjoinRoot (towerLabel T) ≃ₐ[F.stageField H₀ hpin] AdjoinRoot T.ψ₂ := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  have hη : F.stageLetter H₀ hpin ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  set a : F.stageField H₀ hpin := (F.stageLetter H₀ hpin) ^ F.twistExp T.u₂ with ha_def
  set c : F.stageField H₀ hpin := (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂) with hc_def
  have ha : a ≠ 0 := pow_ne_zero _ hη
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero hη)
  -- C.44's explicit form, definitionally
  have hEq : towerLabel T = Polynomial.C c * T.ψ₂.comp (Polynomial.C a * Polynomial.X) := rfl
  -- the forward root image `a⁻¹·η₂` is a root of the translated label
  have h₁ : Polynomial.aeval
      (algebraMap (F.stageField H₀ hpin) (AdjoinRoot T.ψ₂) a⁻¹ * AdjoinRoot.root T.ψ₂)
      (towerLabel T) = 0 := by
    rw [hEq, aeval_C_mul_comp, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, mul_zero]
  -- the backward root image `a·β` is a root of `ψ₂`: cancel the unit scalar `c`
  have h₂ : Polynomial.aeval
      (algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) a
        * AdjoinRoot.root (towerLabel T)) T.ψ₂ = 0 := by
    have h₀ : algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) c
        * Polynomial.aeval
            (algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) a
              * AdjoinRoot.root (towerLabel T)) T.ψ₂ = 0 := by
      rw [← aeval_C_mul_comp, ← hEq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have h₃ : algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) c⁻¹
        * (algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) c
          * Polynomial.aeval
            (algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) a
              * AdjoinRoot.root (towerLabel T)) T.ψ₂) = 0 := by
      rw [h₀, mul_zero]
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h₃
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (towerLabel T)
      (Algebra.ofId (F.stageField H₀ hpin) (AdjoinRoot T.ψ₂))
      (algebraMap (F.stageField H₀ hpin) (AdjoinRoot T.ψ₂) a⁻¹ * AdjoinRoot.root T.ψ₂) h₁)
    (AdjoinRoot.liftAlgHom T.ψ₂
      (Algebra.ofId (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)))
      (algebraMap (F.stageField H₀ hpin) (AdjoinRoot (towerLabel T)) a
        * AdjoinRoot.root (towerLabel T)) h₂) ?_ ?_
  · -- `η₂ ↦ a·β ↦ a·a⁻¹·η₂ = η₂`
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, map_mul, AlgHom.commutes,
      AdjoinRoot.liftAlgHom_root, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul,
      AlgHom.id_apply]
  · -- `β ↦ a⁻¹·η₂ ↦ a⁻¹·a·β = β`
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, map_mul, AlgHom.commutes,
      AdjoinRoot.liftAlgHom_root, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul,
      AlgHom.id_apply]

/-! ### Interface check: the left carrier IS C.12's `level2Field` -/

/-- The blueprint's STATEMENT names the left-hand carrier `level2Field (T.levelDatum hπ)` — the
field `K(β)` the whole §5 dictionary reads at — while the signed SIGNATURE writes
`AdjoinRoot (towerLabel T)`. The two are the same type **definitionally** (`level2Field` is C.12's
`abbrev` for `AdjoinRoot L.r`, kept transparent for exactly this reason, and C.44's `levelDatum`
fills `r` with `towerLabel T`), so `towerLabelEquiv` inhabits the blueprint's type on the nose.
Checked here rather than asserted in prose; this is the node's only claim beyond the SIGNATURE. -/
noncomputable example {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    level2Field (T.levelDatum hπ) ≃ₐ[F.stageField H₀ hpin] AdjoinRoot T.ψ₂ :=
  towerLabelEquiv T hπ

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerLabelEquiv

end AxCheck
