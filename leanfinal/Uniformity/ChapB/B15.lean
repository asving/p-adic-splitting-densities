/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B08
import Uniformity.ChapB.B14

/-!
# Uniformity.ChapB.B15 — `φ = X`: the `φ`-adic layer is the ordinary Newton polygon

**Chapter B, NODE B.15** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A′ (= ENV-A with `hπ : Irreducible π`, carried in the signature).

At the key `φ = X` the whole development/polygon layer collapses to the ordinary coefficient
picture: the development coefficients are the constants `C (f.coeff j)`, the heights are the
coefficient valuations, and the cleared support inequality at slope `−M` is exactly the
divisibility hypothesis of the landed `Uniformity.Density.exists_monic_scaleRoots`
(`Uniformity/Density/ScaleExtraction.lean`).

**⚠ THIS NODE IS DECISION D-1's CRITERION-C8 CERTIFICATE.** `ScaleExtraction.lean` states,
verbatim, that CN-12's divisibility hypothesis *is* the polygon condition "written without any
polygon representation". `suppVal_X_iff` proves that the representation chosen by D-1
reproduces that condition exactly, so the DECISION extends `leanfinal`'s existing polygon read
rather than forking it.

Three public declarations, as signed: `dev_X` and `npHgt_X` are the `φ = X` dictionary every
later specialisation needs (B.83's gate, and chapters C/H's ordinary Newton polygon), and
`suppVal_X_iff` is the compatibility certificate itself.

DEPENDS: B.02 (`dev`) · B.08 (`gaussVal`, via B.11) · B.11 (`npHgt`) · B.14 (`suppVal`) ·
landed `Uniformity.Hensel.pow_dvd_iff_le_addVal` (`Uniformity/StrongHensel.lean`) · mathlib
`Polynomial.modByMonic_X`, `Polynomial.divX_mul_X_add`, `Polynomial.coeff_divX`,
`ENat.add_le_add_iff_right`.

**PROOF.**

1. The pinned mathlib has `modByMonic_X : p %ₘ X = C (p.eval 0)` but no `divByMonic_X`, so the
   private helper `divByMonic_X_eq_divX : f /ₘ X = f.divX` is proved from the two division
   identities `modByMonic_add_div f X : f %ₘ X + X * (f /ₘ X) = f` and
   `divX_mul_X_add f : f.divX * X + C (f.coeff 0) = f`, cancelling `X` (a nonzerodivisor:
   `O` is a domain).
2. `dev_X` by induction on `j` generalising `f`: at `j = 0` it is `modByMonic_X` plus
   `coeff_zero_eq_eval_zero`; at `j+1`, `dev X f (j+1) = dev X (f /ₘ X) j` by `rfl`, then
   step 1 and `coeff_divX : (divX p).coeff n = p.coeff (n+1)`.
3. `npHgt_X`: `gaussVal (C a) = addVal O a`, because `(C a).natDegree = 0`, so the `inf` runs
   over `range 1 = {0}` and its single value is `addVal O ((C a).coeff 0) = addVal O a`.
4. `suppVal_X_iff` (→): `Finset.le_inf_iff` gives, for each `i ≤ n := f.natDegree`,
   `M*n ≤ addVal O (f.coeff i) + M*i` in `ℕ∞` (the `1 •` is `one_smul`). For `i < n` write the
   *natural number* `M*n` as `M*(n-i) + M*i` and cancel the finite summand `M*i` on the right
   (`ENat.add_le_add_iff_right`, `(M*i : ℕ∞) ≠ ⊤`); `pow_dvd_iff_le_addVal hπ` turns
   `M*(n-i) ≤ addVal O (f.coeff i)` into the divisibility.
5. (←): `Finset.le_inf`. For `i < n` run step 4 backwards (`add_le_add_right` after the same
   `M*n = M*(n-i) + M*i` split). For `i = n` no hypothesis is needed at all: the term is
   `addVal O (f.coeff n) + M*n ≥ M*n` by `le_add_self`, since `ℕ∞` is canonically ordered.
   (This is where the blueprint's route used monicity to compute `addVal O (f.coeff n) = 0`;
   the inequality direction makes the computation unnecessary, so `hf` and `hn` are kept for
   the frozen signature but not consumed. The statement is *not* weakened — the hypotheses
   remain in place.)

SOURCE: `EFF.W12.23`; `spec/CERTAIN_NODES_2026-08-14.md` CN-12 and REJECTED R1.

TEETH: signed non-applicable as a battery item (a compatibility identity), but this node is
the chapter's internal decision gate for D-1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The pinned mathlib has `modByMonic_X` but no `divByMonic_X`: division by `X` is `divX`.
Proved by cancelling `X` between `modByMonic_add_div` and `divX_mul_X_add`. -/
private theorem divByMonic_X_eq_divX (f : Polynomial O) : f /ₘ X = f.divX := by
  have h1 : f %ₘ X + X * (f /ₘ X) = f := modByMonic_add_div f X
  rw [modByMonic_X, ← coeff_zero_eq_eval_zero] at h1
  have h2 : f.divX * X + C (f.coeff 0) = f := divX_mul_X_add f
  have hX : X * (f /ₘ X) = X * f.divX := by linear_combination h1 - h2
  exact mul_left_cancel₀ X_ne_zero hX

/-- At `φ = X` the development coefficients are the constants `C (f.coeff j)`. -/
theorem dev_X (f : Polynomial O) (j : ℕ) : dev X f j = Polynomial.C (f.coeff j) := by
  induction j generalizing f with
  | zero =>
    rw [show dev X f 0 = f %ₘ X from rfl, modByMonic_X, coeff_zero_eq_eval_zero]
  | succ j ih =>
    rw [show dev X f (j + 1) = dev X (f /ₘ X) j from rfl, divByMonic_X_eq_divX, ih, coeff_divX]

/-- At `φ = X` the polygon heights are the coefficient valuations: the `X`-adic polygon is the
ordinary Newton polygon. -/
theorem npHgt_X (f : Polynomial O) (j : ℕ) :
    npHgt X f j = IsDiscreteValuationRing.addVal O (f.coeff j) := by
  rw [npHgt, dev_X, gaussVal]
  simp

-- `hf` and `hn` are signed hypotheses of the frozen statement; the proof of the `i = n` slot
-- goes through `le_add_self` instead of `addVal O (f.coeff n) = 0`, so neither is consumed.
set_option linter.unusedVariables false in
/-- **DECISION D-1's compatibility certificate.** The cleared support inequality of `f`'s
`X`-adic polygon at slope `−M` is verbatim the divisibility hypothesis of the landed
`Uniformity.Density.exists_monic_scaleRoots`. -/
theorem suppVal_X_iff (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) (M : ℕ) :
    ((M * f.natDegree : ℕ) : ℕ∞) ≤ suppVal X f M 1 ↔
      ∀ i < f.natDegree, π ^ (M * (f.natDegree - i)) ∣ f.coeff i := by
  have hsplit : ∀ i ≤ f.natDegree, M * f.natDegree = M * (f.natDegree - i) + M * i := by
    intro i hi
    have h : f.natDegree - i + i = f.natDegree := by omega
    calc M * f.natDegree = M * (f.natDegree - i + i) := by rw [h]
      _ = M * (f.natDegree - i) + M * i := by ring
  simp only [suppVal, Finset.le_inf_iff, Finset.mem_range, one_smul, npHgt_X]
  constructor
  · intro h i hi
    rw [Uniformity.Hensel.pow_dvd_iff_le_addVal hπ]
    have hle := h i (by omega)
    rw [hsplit i (by omega), Nat.cast_add] at hle
    exact (ENat.add_le_add_iff_right (ENat.coe_ne_top (M * i))).1 hle
  · intro h i hi
    rcases lt_or_ge i f.natDegree with hlt | hge
    · rw [hsplit i (by omega), Nat.cast_add]
      gcongr
      exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 (h i hlt)
    · have hieq : i = f.natDegree := by omega
      subst hieq
      exact le_add_self

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_X
#print axioms Uniformity.Density.Leaf.npHgt_X
#print axioms Uniformity.Density.Leaf.suppVal_X_iff
end AxCheck

end Uniformity.Density.Leaf
