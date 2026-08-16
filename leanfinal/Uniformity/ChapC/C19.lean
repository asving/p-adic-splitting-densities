/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03
import Uniformity.ChapB.B25
import Uniformity.ChapB.B30
import Uniformity.ChapB.B35b

/-!
# Uniformity.ChapC.C19 — `stageLetter`: the letter `η`, and `η ≠ 0`

**Chapter C, NODE C.19** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge
layer; the A-C.1 amendment set governs). **ENV-C1** (`hπ` explicit on the lemma). Two signed
declarations.

* `KeyFrame.stageLetter F H₀ hpin` — `EFF.HE6.08`'s `η_θ = res(θ^{e₁}π^{−h})`, recast as the
  canonical residual root `AdjoinRoot.root ψ` of the frame residual `ψ = F.frameRes H₀ hpin`
  (C.03) inside the stage field `K = F.stageField H₀ hpin = AdjoinRoot ψ` (C.03). Definitional.
* `KeyFrame.stageLetter_ne_zero F hπ H₀ hpin` — the letter is a **unit**: `η ≠ 0`. This is the
  clause the whole §4 gauge layer rests on, because C.22's `twistRead` divides by `η^{q(k)}`.

## Why `η ≠ 0` is not formal

It is not a consequence of `Irreducible ψ` alone: `ψ = T` is irreducible over any field and has
`AdjoinRoot.root T = 0`. The content is that the frame residual has **nonzero constant term**,
which is B.30(b) (`natDegree_resPoly`, second conjunct) applied at the frame's own side
`(u, ℓ) = (F.h, F.e₁)` over the order-0 key `X`. Concretely: if `η = 0` then `ψ ∣ X` in
`(resField X)[T]`; taking constant terms and using `ψ(0) ≠ 0` forces the cofactor `q` to have
`q(0) = 0`, i.e. `X ∣ q`; cancelling `X` (a nonzerodivisor) then exhibits `ψ` as a unit,
contradicting `Irreducible ψ` — which the frame supplies as `F.hresirr H₀ hpin`.

Feeding B.30(b) needs its two side conditions at the frame. `(sideSet X F.key F.h F.e₁).Nonempty`
is the structure field `F.hne`. Finiteness `suppVal X F.key F.h F.e₁ ≠ ⊤` is B.35b's
`suppVal_of_pure` at the structure field `F.hpure : IsPure X F.key F.h F.e₁` (with
`F.key.natDegree = (e₁f₁)·natDegree X` from `F.hdeg`), which evaluates the support value to the
numeral `F.h * (F.e₁ * F.f₁)`. Both are private helpers below.

## The `Field (resField X)` instance (defect **D9**, again)

The cancellation step needs `resField X` to have no zero divisors, and `resField X` is a `Field`
only through B.25(b)'s `instFieldResField`, which is keyed on `IsKey X` — a fact nothing in
`leanfinal` states, since no node proves `IsKey Polynomial.X`. C.04 already carries the cure as a
`private theorem isKey_X`; it is `private`, hence not in scope here, so the same three-line proof
is repeated below (likewise `private`, likewise not a blueprint node). The A-C.1(m) record adopts
`isKey_X` as a blueprint declaration; when C.14a lands it, both copies should be retired to it.

## What does NOT land here (frozen-signature discipline, the C.16 precedent)

The blueprint's SIGNATURE block adds, after the two signed declarations, *"with the power-basis
statement (`AdjoinRoot.powerBasis` at `Irreducible ψ`) as a companion in the same file"* — the
(T2)-role carrier `{1, η, …, η^{f₁−1}}` of `EFF.HE6.15`. **No signature is given for it**, and the
gate-verified twin `leanspec/Leanspec/ChapC.lean` (authoritative on divergence) signs exactly the
two declarations below. Signatures are frozen and a node may not grow one, so the companion does
not land — the same disposition C.16 recorded for its unsigned clauses (iv)/(v).

Nothing is lost, and consumers should not re-derive it from scratch. The companion is one term:

```lean
AdjoinRoot.powerBasis (F.hresirr H₀ hpin).1.ne_zero
  : PowerBasis (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
```

under `letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X`, with
`dim = ψ.natDegree = F.f₁` by `AdjoinRoot.powerBasis_dim` and `(F.hresirr H₀ hpin).2`. That is
verbatim what C.04's `private finrank_stageField` already does, and it is what **C.21** (the
`η^t`-indexed slot residue) and **C.23** (nonvanishing at an attained height) should write inline
at their own nodes.

**DEPENDS.** C.03 (`frameRes`, `stageField`) · C.01 (`KeyFrame.hresirr`, `hpure`, `hne`, `hdeg`,
`he₁`, `hcop`, `hmonic`) · B.30 (`natDegree_resPoly` — `resPoly` has nonzero constant term) ·
B.35b (`suppVal_of_pure`) · B.25 (`instFieldResField`) — by committed node ID (GC-13(b)). The
imports are `Uniformity.ChapC.C03` (which pulls C.01 and the B chain), `Uniformity.ChapB.B25`,
`Uniformity.ChapB.B30`, `Uniformity.ChapB.B35b`.

**PROOF.** 1. definitional. 2. the blueprint's `η = 0 → ψ(0) = 0` argument, executed through
divisibility as described above (the direct route "`ψ(0) = 0`" needs injectivity of
`AdjoinRoot.of`, which costs the same `Field` instance and one more lemma).

SOURCE: `EFF.HE6.08` (`η_θ`, `K = F_Q(η_θ)`); `EFF.HE6.15` (the (T2) role:
`{1, η, …, η^{f₁−1}}` `F_Q`-independent — here the `AdjoinRoot` power basis, see above).

**TEETH.** Signed non-applicable.

ENVIRONMENT: ENV-C1 (`hπ` explicit — B.30's residual reads consume it).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers (stub-gate defect **D9**, and B.30's two side conditions at the frame) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense. C.04 carries the same
helper `private`; repeated here because `private` does not export. `private`: a stub-side helper,
not a blueprint node. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- B.30's finiteness side condition at the frame: the frame's key is `(F.h, F.e₁)`-pure of full
degree over `X`, so B.35b evaluates its cleared support value to the numeral `h·e₁f₁`. -/
private theorem suppVal_key_ne_top (F : KeyFrame O π) :
    suppVal Polynomial.X F.key F.h F.e₁ ≠ ⊤ := by
  rw [suppVal_of_pure (n := F.e₁ * F.f₁) Polynomial.monic_X (by simp) F.hmonic
    (by simp [F.hdeg]) F.hpure]
  exact ENat.coe_ne_top _

/-- **B.30(b) at the frame:** the frame residual `ψ` has nonzero constant term.  This — not
irreducibility — is what makes the letter a unit. -/
private theorem frameRes_coeff_zero_ne_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    (F.frameRes H₀ hpin).coeff 0 ≠ 0 :=
  (natDegree_resPoly hπ isKey_X F.he₁ F.hcop (suppVal_key_ne_top F) F.hne hpin).2

/-! ### The signed declarations -/

/-- **C.19 (a) — the stage letter `η`.**  `EFF.HE6.08`'s `η_θ = res(θ^{e₁}π^{−h})`, recast as the
canonical residual root of the frame residual `ψ` inside `K = AdjoinRoot ψ` (C.03). -/
noncomputable def KeyFrame.stageLetter (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    F.stageField H₀ hpin :=
  AdjoinRoot.root (F.frameRes H₀ hpin)

/-- **C.19 (b) — the letter is a unit.**  `η ≠ 0`, because the frame residual has nonzero
constant term (B.30(b)); irreducibility alone would not do it (`ψ = T` is a counterexample). -/
theorem KeyFrame.stageLetter_ne_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    F.stageLetter H₀ hpin ≠ 0 := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  intro h0
  -- `η = 0` says exactly that `ψ` divides `T` in `(resField X)[T]`.
  have hdvd : F.frameRes H₀ hpin ∣
      (Polynomial.X : Polynomial (resField (Polynomial.X : Polynomial O))) := by
    rw [KeyFrame.stageLetter, ← AdjoinRoot.mk_X, AdjoinRoot.mk_eq_zero] at h0
    exact h0
  obtain ⟨q, hq⟩ := hdvd
  -- constant terms: `0 = ψ(0)·q(0)`, and `ψ(0) ≠ 0`, so `q(0) = 0`.
  have hc0 : (F.frameRes H₀ hpin).coeff 0 * q.coeff 0 = 0 := by
    have h := congrArg (fun p : Polynomial (resField (Polynomial.X : Polynomial O)) =>
      p.coeff 0) hq
    simp only [Polynomial.coeff_X_zero, Polynomial.mul_coeff_zero] at h
    exact h.symm
  have hq0 : q.coeff 0 = 0 :=
    (mul_eq_zero.mp hc0).resolve_left (frameRes_coeff_zero_ne_zero F hπ H₀ hpin)
  obtain ⟨q', hq'⟩ := Polynomial.X_dvd_iff.mpr hq0
  -- cancelling `T` exhibits `ψ` as a unit.
  have hcan : (Polynomial.X : Polynomial (resField (Polynomial.X : Polynomial O))) * 1
      = Polynomial.X * (F.frameRes H₀ hpin * q') := by
    rw [mul_one]
    calc (Polynomial.X : Polynomial (resField (Polynomial.X : Polynomial O)))
        = F.frameRes H₀ hpin * q := hq
      _ = F.frameRes H₀ hpin * (Polynomial.X * q') := by rw [hq']
      _ = Polynomial.X * (F.frameRes H₀ hpin * q') := by ring
  exact (F.hresirr H₀ hpin).1.not_isUnit
    (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ Polynomial.X_ne_zero hcan).symm)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageLetter
#print axioms Uniformity.Density.Tower.KeyFrame.stageLetter_ne_zero

end AxCheck
