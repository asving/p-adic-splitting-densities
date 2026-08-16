/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapE.E25 — seam exponent integrality

**Chapter E, NODE E.25** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §5, the slot-seam
evaluation layer), ENV-E1 (the arithmetic arena: no `O`, pure exponent bookkeeping).

The corrected `(GAMMA)`/`(HE6-SEAM)` display of `EFF.T2.06` reads

`γ_k(A) = Σ_{t ≥ 0, i + e₁t < D′} res(a_{i+e₁t} · π^{−(k − (i+e₁t)h)/e₁}) · η^t`,

so every summand carries the coefficient normalizer `π^{−(k − (i+e₁t)h)/e₁}`. This node is the
exponent half of that display: the two arithmetic facts that make those normalizers well posed.

* `seam_exp_dvd` — on the seam's own residue class (`k ≡ i·h [MOD e]`) and above the slot's
  floor (`(i + e·t)·h ≤ k`), the numerator `k − (i + e·t)·h` is divisible by `e`, so the
  exponent `(k − (i + e·t)·h)/e` is an honest natural, not a truncated quotient.
* `seam_exp_step` — moving one slot up the class (`t ↦ t + 1`) drops that exponent by exactly
  `h`. In particular `t ↦ (k − (i + e·t)·h)/e` is strictly antitone on the range where the
  floor condition holds (`h ≥ 1`), which is what bounds the seam sum's length.

Both are stated for arbitrary `t`; the second needs no divisibility hypothesis at all, because
the two numerators differ by exactly `e·h` and `Nat.add_mul_div_left` is exact.

DEPENDS: none beyond mathlib (`Nat.modEq_iff_dvd'`, `Nat.add_mul_mod_self_left`,
`Nat.add_mul_div_left`). The blueprint's DEPENDS field cites H.51 (`class_sep`) as the
"congruence engine"; H.51 is the *injectivity* of `i ↦ i·h % e` under coprimality, which is
what selects the class `i` that a height `k` can be fed from — it is not needed to run the
arithmetic *inside* one fixed class, which is all this node states. The frozen signature's
`hcop` and `hi` are therefore carried but unconsumed (see the `linter.unusedVariables` notes);
no strength is lost, the landed statements are the signed ones verbatim.

**PROOF.** `seam_exp_dvd`: `(i + e·t)·h = i·h + e·(t·h) ≡ i·h ≡ k [MOD e]`
(`Nat.add_mul_mod_self_left`, then `hk`), and `Nat.modEq_iff_dvd'` turns a `ModEq` under
`(i + e·t)·h ≤ k` into the divisibility of the natural difference.
`seam_exp_step`: `(i + e·(t+1))·h = (i + e·t)·h + e·h` (`ring`), so under the guard
`(i + e·(t+1))·h ≤ k` the two truncated differences satisfy
`k − (i + e·t)·h = (k − (i + e·(t+1))·h) + e·h` (`omega`, on the three products as atoms);
divide by `e > 0` with `Nat.add_mul_div_left`.

**⚠ HYP.150/151 DISCIPLINE.** The bare pre-A3 `HE6-SLOT-SEAM` display — the *unnormalized*
coefficient-residue sum — is affirmatively FALSE for `k > (D′−1)h`, where every bare summand
vanishes while the true residue is a unit. Nothing in this file states or licenses the bare
form: the normalizer exponent is exactly what is being proved integral here.

SOURCE: `EFF.T2.06` (the boxed `(GAMMA)`: "The coefficient normalizers inside `γ_k(A)` … are
mandatory"); `EFF.HE7.19` (LEMMA HE7-L1's proof: "the slot `i` contributes at height `k` iff
`e₁v(a_i) = k − ih ≥ 0` … which forces `i ≡ i₀ (mod e₁)` and `k ≥ ih`").

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Ladder

-- The signed hypotheses `hcop : Nat.Coprime h e` and `hi : i < e` are kept (frozen signature)
-- but are not consumed: within one fixed residue class the congruence `hk` already pins the
-- numerator's class, and `e = 0` is ruled out vacuously by `hi` rather than used. Coprimality
-- is what *selects* the class (H.51); it plays no role once the class is given.
set_option linter.unusedVariables false in
/-- **E.25 (a) — seam exponent integrality.** On the seam class `k ≡ i·h [MOD e]`, above the
slot floor `(i + e·t)·h ≤ k`, the `(GAMMA)` numerator is divisible by `e`; hence the normalizer
exponent `(k − (i + e·t)·h)/e` is an honest natural. -/
theorem seam_exp_dvd {e h i k t : ℕ} (hcop : Nat.Coprime h e) (hi : i < e)
    (hk : k % e = (i * h) % e) (ht : (i + e * t) * h ≤ k) :
    e ∣ k - (i + e * t) * h := by
  have hmod : (i + e * t) * h % e = k % e := by
    rw [hk, add_mul, mul_assoc, Nat.add_mul_mod_self_left]
  exact (Nat.modEq_iff_dvd' ht).mp hmod

/-- **E.25 (b) — the seam exponent drops by `h` per unit `t`.** Stepping one slot up the class
lowers the `(GAMMA)` normalizer exponent by exactly `h`. -/
theorem seam_exp_step {e h i k t : ℕ} (hi : i < e)
    (ht : (i + e * (t + 1)) * h ≤ k) :
    (k - (i + e * t) * h) / e = (k - (i + e * (t + 1)) * h) / e + h := by
  have he : 0 < e := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have key : (i + e * (t + 1)) * h = (i + e * t) * h + e * h := by ring
  have hsub : k - (i + e * t) * h = (k - (i + e * (t + 1)) * h) + e * h := by omega
  rw [hsub, Nat.add_mul_div_left _ _ he]

section AxCheck
#print axioms Uniformity.Density.Ladder.seam_exp_dvd
#print axioms Uniformity.Density.Ladder.seam_exp_step
end AxCheck

end Uniformity.Density.Ladder
