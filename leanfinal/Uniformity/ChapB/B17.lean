/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B16

/-!
# Uniformity.ChapB.B17 — the `ℓ`-spacing of a side

**Chapter B, NODE B.17** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

*The `ℓ`-spacing of a side.*  Let `0 < ℓ`, `Nat.Coprime u ℓ`, and let `j, j'` both be on the
`(u,ℓ)`-side with `suppVal φ f u ℓ ≠ ⊤`.  Then `j ≡ j' [MOD ℓ]`.

This is the combinatorial heart of the side: the abscissae carried by a side of slope `−u/ℓ`
**in lowest terms** form a single residue class mod `ℓ`, so they are the lattice points
`j₀ + ℓ·k` of `EFF.HE3.14`.  B.20 turns the spacing into the side's residual degree
`sideDeg = sideLen / ℓ`, and B.28/B.30 read the residual coefficients off those lattice points.

Three declarations.  The two auxiliaries are the blueprint's mandated SPLIT CANDIDATE
(*"extract it as a private helper `onSide_nat_eq` returning the `ℕ`-equality of step 2, which
B.20 and B.28 also want"*), here split once more into the finiteness step and the equality
step.  **Deviation from the blueprint's word `private`:** they are public, because B.19's
DEPENDS line names `onSide_nat_eq` explicitly and B.19 is a different file, where a
`private` declaration would be invisible.  Neither auxiliary is a signed node statement.

* `npHgt_ne_top_of_onSide` — step 1: an on-side abscissa of a finite side has finite height;
* `onSide_nat_eq` — step 2: with the two heights named as naturals, the two `OnSide`
  equations become the single `ℕ`-equation `ℓ * H + u * j = ℓ * H' + u * j'`;
* `onSide_modEq` — the node, by steps 3–4 (transport to `ℤ`, then coprimality).

DEPENDS: B.11 (`npHgt`) · B.14 (`suppVal`) · B.16 (`OnSide`) · mathlib
`WithTop.ne_top_iff_exists`, `Nat.isCoprime_iff_coprime`, `IsCoprime.dvd_of_dvd_mul_left`,
`Nat.modEq_iff_dvd`.

**PROOF.**
1. From `htop` and `hj`, `ℓ • npHgt φ f j ≠ ⊤`, so `npHgt φ f j ≠ ⊤` (as `0 < ℓ`, using
   `ℓ • ⊤ = ⊤` in `ℕ∞`); write `npHgt φ f j = (H : ℕ∞)`, and likewise `H'` at `j'`.
2. The two `OnSide` equalities give, after `Nat.cast_injective` on `ℕ∞`, the `ℕ`-equality
   `ℓ * H + u * j = ℓ * H' + u * j'`.
3. Pass to `ℤ`: `ℓ * (H − H') = u * (j' − j)`, hence `(ℓ : ℤ) ∣ u * (j' − j)`.
4. `Nat.Coprime u ℓ` gives `IsCoprime (ℓ : ℤ) (u : ℤ)`, so `(ℓ : ℤ) ∣ (j' − j)`, which is
   `j ≡ j' [MOD ℓ]`.

## Minimum-hypothesis note (blueprint, verbatim in force)

`Nat.Coprime u ℓ` **is load-bearing and cannot be weakened to `0 < u`**: at `u = ℓ = 2` the
spacing is `1`, not `2`, and the corpus tooth `HE6-T-BADKEY` (`EFF.HE6.52`) fired on exactly
this ("`gcd(u,ℓ) = 1` hypothesis is load-bearing (`κ = 6/2` gives 2 factors, different
residues)").  `htop` cannot be dropped (without it both sides may be `⊤` and every `j` is
vacuously "on side"); `0 < ℓ` cannot be dropped (at `ℓ = 0` step 1 fails).

SOURCE: `EFF.HE3.14` verbatim (*"lattice abscissas `j₀ + ℓk` (`k = 0, …, d_λ`)"*);
`EFF.HE6.52` (the tooth); `EFF.HE3.13` (*"slope `λ = u/ℓ` **in lowest terms**"*).

TEETH: `HE6-T-BADKEY` (`EFF.HE6.52`) → Lean theorem (`onSide_modEq` is the sufficiency half;
the tooth's necessity half is the counterexample recorded above).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.17 step 1 — an on-side abscissa of a finite side has finite height.**  If the cleared
support value at the slope `−u/ℓ` is finite and `j` attains it, then `npHgt φ f j ≠ ⊤`; here
`0 < ℓ` is what makes `ℓ • ⊤ = ⊤`. -/
theorem npHgt_ne_top_of_onSide {ℓ u : ℕ} (hℓ : 0 < ℓ) {φ f : Polynomial O} {j : ℕ}
    (htop : suppVal φ f u ℓ ≠ ⊤) (hj : OnSide φ f u ℓ j) : npHgt φ f j ≠ ⊤ := by
  intro h
  have hj' : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hj
  refine htop ?_
  rw [← hj', h]
  simp [nsmul_eq_mul, hℓ.ne']

/-- **B.17 step 2 — the two `OnSide` equations, in `ℕ`.**  Once the two heights are named as
naturals `H`, `H'`, the equality of the two cleared support values is a plain `ℕ`-equation.
No hypothesis on `ℓ` or `u` is needed here.  (B.19 and B.20 consume this form.) -/
theorem onSide_nat_eq {ℓ u : ℕ} {φ f : Polynomial O} {j j' H H' : ℕ}
    (hH : npHgt φ f j = (H : ℕ∞)) (hH' : npHgt φ f j' = (H' : ℕ∞))
    (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have hja : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hj
  have hjb : ℓ • npHgt φ f j' + ((u * j' : ℕ) : ℕ∞) = suppVal φ f u ℓ := hj'
  have e : ℓ • (H : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ℓ • (H' : ℕ∞) + ((u * j' : ℕ) : ℕ∞) := by
    rw [← hH, ← hH', hja, hjb]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞) = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

/-- **B.17 — the `ℓ`-spacing of a side.**  On a side of finite cleared support value and slope
`−u/ℓ` in lowest terms, any two on-side abscissae are congruent mod `ℓ`. -/
theorem onSide_modEq {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    {j j' : ℕ}
    (htop : suppVal φ f u ℓ ≠ ⊤) (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j') :
    j ≡ j' [MOD ℓ] := by
  obtain ⟨H, hH⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hj)
  obtain ⟨H', hH'⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hj')
  have key : ℓ * H + u * j = ℓ * H' + u * j' := onSide_nat_eq hH.symm hH'.symm hj hj'
  have keyZ : (ℓ : ℤ) * (H : ℤ) + (u : ℤ) * (j : ℤ) = (ℓ : ℤ) * (H' : ℤ) + (u : ℤ) * (j' : ℤ) :=
    by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have hdvd : (ℓ : ℤ) ∣ (u : ℤ) * ((j' : ℤ) - (j : ℤ)) := ⟨(H : ℤ) - (H' : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_ne_top_of_onSide
#print axioms Uniformity.Density.Leaf.onSide_nat_eq
#print axioms Uniformity.Density.Leaf.onSide_modEq
end AxCheck

end Uniformity.Density.Leaf
