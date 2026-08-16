/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F18 — `xiChar`: the formula character and its `q = 2` degeneration

**Chapter F, NODE F.18** [def+lemma] (`blueprint/CHAP-F_weld_layer.md` §6), ENV-F1 +
`[Field K]`. The §3.4 formula character `ξ_q = χ_{q−1}^{γ_q} · z_{q−1}^{−e_{q−1}A_{q−1}}`
(`EFF.SIGMALAW.02/.03`), with integer exponents (hence `zpow`), together with the spec's own
arithmetic audit of its base level: at `χ = 1`,

`xiChar 1 γ z e A = (z ^ (e * A))⁻¹`,

i.e. `ξ₂ = θ₂⁻¹` where `θ₂ = z₁^{e₁A₁}` is the BOXED interior twist — **at `q = 2` the true
map is exactly the inverse of the boxed one**, and at `q ≥ 3` it differs further by the
χ-chain factor `χ_{q−1}^{γ_q}`. That divergence is what the two machine-witnessed
non-involution separators witness, and why the boxed map survived 468 sealed rows
(involution geographies hide it).

Statement fence carried from F.17: `Σ_m` is NEVER the bare interior twist `z_q ↦ θ_q z_q`;
the corrected ξ-composite is the only sanctioned definition. `ξ₁ := 1` (the E10 #2
supplement) is base-instance content, RECORDED at `EFF.SIGMALAW.13`, and is not a claim of
this node. The tower indexing — which `χ`, `z`, `γ`, `e`, `A` at which level — is chapter
C's instance data.

The lemma half was an `axiom` stub at stage 0e; PROVED here (2026-08-16). Signatures
byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`, LeanspecF).
-/

namespace Uniformity.Density.Weld

/-- The §3.4 formula character `ξ = χ^γ · z^{−eA}` (`EFF.SIGMALAW.03`). -/
def xiChar {K : Type*} [Field K] (χ : Kˣ) (γ : ℤ) (z : Kˣ) (e A : ℤ) : Kˣ :=
  χ ^ γ * z ^ (-(e * A))

theorem xiChar_base {K : Type*} [Field K] (γ : ℤ) (z : Kˣ) (e A : ℤ) :
    xiChar 1 γ z e A = (z ^ (e * A))⁻¹ := by
  rw [xiChar, one_zpow, one_mul, zpow_neg]

end Uniformity.Density.Weld
