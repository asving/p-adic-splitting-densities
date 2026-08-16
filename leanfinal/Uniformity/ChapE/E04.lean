/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E01
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Uniformity.ChapE.E04 — the cocycle exponent lies in `{0, ℓ}`, and the carry identity

**Chapter E, NODE E.04** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §3), ENV-E1 (the arithmetic
arena: exponent bookkeeping, no local base `O`).

ANNEX-LEMMA R1-a(ii)'s **arithmetic half** (`EFF.HE7.108`). Fix a rung `R = (ℓ, g, u, T)` (E.01)
and read `s`/`m` through E.03's Bézout decomposition: `s(k) < ℓ` and `ℓ·m(k) + s(k)·u = k`. Then
for `a, b : ℤ`

* `cocycle_exp_mem` — the slot exponent is only *almost* additive, and the defect is exact:
  `s(a) + s(b) − s(a+b) ∈ {0, ℓ}`, i.e. the carry `c := (s(a) + s(b) − s(a+b))/ℓ` is `0` or `1`;
* `cocycle_carry` — the carry is paid by the height exponent:
  `m(a) + m(b) = m(a+b) − c·u`.

That is the exponent bookkeeping behind the cocycle recursion
`τ_{i+1}(a,b) = Λ_i^c · τ_i(m(a), m(b)) · τ_i(m(a)+m(b), c·u)` (`EFF.T2.07`'s `(COC)`). The
letter-monomial RESIDUE of that display is carrier content — E.33 states its exponent law, the
residue law itself is a §4 field/chapter-C placeholder — and nothing about `τ`, `Λ`, a field or a
valuation appears here. At the **base** rung the level-1 cocycle is trivial (`τ₁ ≡ 1`, because
`k ↦ ϖ^k` is a homomorphism — R1-a(ii), "THE point of the re-based system"); that is a carrier
statement, not this node's.

## Why the signature takes `s`/`m` as arguments

Per E.03's own instruction (the H.54 `stageLift'` lesson) the consumers of the Bézout
decomposition do NOT take the `Exists.choose` projections `RungDatum.sExp`/`mExp`: they take
`s`/`m` as explicit arguments carrying their defining equations as hypotheses. So both theorems
here are stated on raw `(sa, ma)`, `(sb, mb)`, `(sab, mab)` with the pair
`s < ℓ ∧ ℓ*m + s*u = k` as a conjunction hypothesis; a consumer holding `sExp`/`mExp` supplies
`(normExp_exists_unique R k).choose_spec`, and E.03's UNIQUENESS half is what makes those
arguments the corpus's `s`/`m` and not merely *some* decomposition. This is why the DEPENDS line
names E.03 while the import list does not: the divisibility step below re-derives its `mod ℓ`
congruence from `R.hcop` directly (exactly the step E.03's docstring describes as "the
coprimality step E.04's cocycle range argument re-runs one letter over"), so no declaration of
E.03 is used and the file stays at E.01 + mathlib.

The `< ℓ` conjuncts are load-bearing in `cocycle_exp_mem` (they are the whole range argument) and
carried unused-in-the-proof in `cocycle_carry`, where the signature keeps them so the two
theorems are fired from one and the same hypothesis triple at every use site.

DEPENDS: E.01 (`RungDatum`), E.03 (uniqueness — semantically, see above) · mathlib
`Nat.Coprime.isCoprime`, `IsCoprime.dvd_of_dvd_mul_right`.

PROOF (blueprint's, verbatim in structure): add the first two defining equations and subtract the
third, giving `ℓ·(ma + mb − mab) + (sa + sb − sab)·u = 0`; hence `ℓ ∣ (sa + sb − sab)·u`, and
coprimality gives `ℓ ∣ sa + sb − sab`. The three `< ℓ` bounds put that multiple in the open range
`(−ℓ, 2ℓ)`, which leaves `0` and `ℓ`. For the carry identity, substitute `sa + sb − sab = c·ℓ`
into the same combination and cancel `ℓ ≠ 0`.

SOURCE: `EFF.HE7.108` (R1-a(ii), verbatim: "`s_i(a) + s_i(b) − s_i(a+b)` lies in `(−ℓ_i, 2ℓ_i)`
and is `≡ 0 mod ℓ_i`, so it is 0 or `ℓ_i`, i.e. `c ∈ {0,1}`; applying `ℓ_i·(·) + u_i·(s-identity)
= 0` gives `m_i(a) + m_i(b) = m_i(a+b) − c·u_i`"); `EFF.T2.07` (`(COC)`, the cocycle identity this
bookkeeping feeds); `EFF.HE7.08` (the level-2 instance `c := (s(k) + s(k′) − s(k+k′))/ℓ ∈ ℤ`,
sharpened to `{0,1}` by R1-a).

TEETH: `he7rannex_supp.py` (the `Λ₂Λ₁`-monomial twist arithmetic, 102 slot instances; the
exponent value identity held on every computed monomial) — the exponent half is a Lean theorem
here.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **The cocycle exponent is `0` or `ℓ`** (`EFF.HE7.108`, R1-a(ii)'s range argument). For
Bézout decompositions `ℓ*ma + sa*u = a`, `ℓ*mb + sb*u = b`, `ℓ*mab + sab*u = a + b` with all
three slot exponents `< ℓ`, the defect `sa + sb − sab` is `0` or `ℓ` — i.e. the carry
`c = (sa + sb − sab)/ℓ` lies in `{0, 1}`. -/
theorem cocycle_exp_mem (R : RungDatum) (a b : ℤ)
    (sa sb sab : ℕ) (ma mb mab : ℤ)
    (ha : sa < R.ℓ ∧ (R.ℓ : ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ : ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ : ℤ) * mab + sab * R.u = a + b) :
    (sa + sb - sab : ℤ) = 0 ∨ (sa + sb - sab : ℤ) = R.ℓ := by
  have hℓpos : (0 : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast R.hℓ
  have hcop : IsCoprime (R.u : ℤ) (R.ℓ : ℤ) := R.hcop.isCoprime
  -- the three defining equations, combined: `ℓ·(ma+mb−mab) + (sa+sb−sab)·u = 0`
  have hcomb : (R.ℓ : ℤ) * (ma + mb - mab)
      + ((sa : ℤ) + (sb : ℤ) - (sab : ℤ)) * (R.u : ℤ) = 0 := by
    linear_combination ha.2 + hb.2 - hab.2
  -- so `ℓ` divides the defect, coprimality stripping the `u`
  have hdvd : (R.ℓ : ℤ) ∣ ((sa : ℤ) + (sb : ℤ) - (sab : ℤ)) * (R.u : ℤ) :=
    ⟨-(ma + mb - mab), by linear_combination hcomb⟩
  obtain ⟨c, hc⟩ := hcop.symm.dvd_of_dvd_mul_right hdvd
  -- the range `(−ℓ, 2ℓ)` from the three `< ℓ` bounds leaves `c = 0` and `c = 1`
  have hsa : (sa : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast ha.1
  have hsb : (sb : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast hb.1
  have hsab : (sab : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast hab.1
  have hsa0 : (0 : ℤ) ≤ (sa : ℤ) := Int.natCast_nonneg sa
  have hsb0 : (0 : ℤ) ≤ (sb : ℤ) := Int.natCast_nonneg sb
  have hsab0 : (0 : ℤ) ≤ (sab : ℤ) := Int.natCast_nonneg sab
  have hlow : (-1 : ℤ) < c := by nlinarith
  have hhigh : c < 2 := by nlinarith
  have hc01 : c = 0 ∨ c = 1 := by
    rcases lt_or_ge c 1 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rcases hc01 with rfl | rfl
  · exact Or.inl (by simpa using hc)
  · exact Or.inr (by simpa using hc)

/-- **The carry identity** (`EFF.HE7.108`, R1-a(ii)): with the carry `c` read off the defect
(`sa + sb − sab = c·ℓ`), the height exponents satisfy `ma + mb = mab − c*u`. Together with
`cocycle_exp_mem` (`c ∈ {0,1}`) this is the exponent content of `(COC)`. -/
theorem cocycle_carry (R : RungDatum) {a b : ℤ} {sa sb sab : ℕ} {ma mb mab : ℤ}
    (ha : sa < R.ℓ ∧ (R.ℓ : ℤ) * ma + sa * R.u = a)
    (hb : sb < R.ℓ ∧ (R.ℓ : ℤ) * mb + sb * R.u = b)
    (hab : sab < R.ℓ ∧ (R.ℓ : ℤ) * mab + sab * R.u = a + b)
    {c : ℤ} (hc : (sa + sb - sab : ℤ) = c * R.ℓ) :
    ma + mb = mab - c * R.u := by
  have hℓne : (R.ℓ : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast R.hℓ
    exact ne_of_gt this
  refine mul_left_cancel₀ hℓne ?_
  linear_combination ha.2 + hb.2 - hab.2 - (R.u : ℤ) * hc

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.cocycle_exp_mem
#print axioms Uniformity.Density.Ladder.cocycle_carry

end AxCheck
