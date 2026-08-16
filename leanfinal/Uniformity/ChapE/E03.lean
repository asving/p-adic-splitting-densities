/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E01
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E03 — the normalizer exponents: Bézout at the rung

**Chapter E, NODE E.03** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §3), ENV-E1 (the arithmetic
arena: exponent bookkeeping, no local base `O`).

For a rung datum `R = (ℓ, g, u, T)` (E.01) and every `k : ℤ` there is exactly one pair
`(m, s) ∈ ℤ × ℕ` with

  `s < ℓ`  and  `ℓ * m + s * u = k`.

This is `EFF.HE7.06`'s clause verbatim — "`ℓ·m(k) + s(k)·u = k` with `0 ≤ s(k) < ℓ` — possible
and unique because `gcd(u, ℓ) = 1`" — and it is the exponent content of the normalizer recursion
`n_{i+1}(k) := n_i(m_i(k)) · Φ_i^{s_i(k)}` (`EFF.HE7.107`, ANNEX-DEF HE7-2′). The normalizer
POLYNOMIAL itself is carrier content (§4 / chapter C); this node is its exponent bookkeeping
only, so nothing here mentions `Φ`, a field, or a valuation.

Both halves of the corpus's clause are load-bearing downstream and both are proved here:

* **existence** rides Bézout for `gcd(u, ℓ) = 1` (`Nat.Coprime.isCoprime` into `ℤ`, then reduce
  the Bézout multiplier mod `ℓ` with `Int.emod`); the `0 ≤ s` half of `0 ≤ s(k) < ℓ` is carried
  by the type (`s : ℕ`), which is why the signed pair is `ℤ × ℕ` and not `ℤ × ℤ`;
* **uniqueness** is the coprimality step E.04's cocycle range argument re-runs one letter over:
  `ℓ ∣ (s − s′)·u` and `gcd(u, ℓ) = 1` force `ℓ ∣ s − s′`, and `s, s′ < ℓ` then force `s = s′`
  (the `|s − s′| < ℓ` squeeze), after which `ℓ ≠ 0` cancels to `m = m′`.

`sExp`/`mExp` are the `Exists.choose` projections of that unique pair — `noncomputable` because
`ExistsUnique` is an existence statement, not an algorithm (a computable spelling would fix a
particular `emod` normal form and is not what the corpus names). Their defining property is
`(normExp_exists_unique R k).choose_spec`. Per the blueprint's own instruction (the H.54
`stageLift'` lesson), the consumers E.04 and E.33 do NOT take these projections: they take
`s`/`m` as explicit arguments with the defining equation as a hypothesis, and use
`normExp_exists_unique` only to know such arguments exist and are unique. Nothing beyond the
three signed declarations is landed here.

DEPENDS: E.01 · mathlib `Nat.Coprime.isCoprime`, `IsCoprime.dvd_of_dvd_mul_right`,
`Int.mul_ediv_add_emod`, `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`.

SOURCE: `EFF.HE7.06` (the `n₂(k)` display and its Bézout clause); `EFF.HE7.107` (the recursion's
`ℓ_i·m_i(k) + s_i(k)·u_i = k`, `0 ≤ s_i(k) < ℓ_i`, "possible and unique because
`gcd(u_i, ℓ_i) = 1`").

TEETH: Q2 / HE7-SLOT2 (12,632 exactness identities ride this bookkeeping) — the arithmetic half
is a Lean theorem here, no longer a convention.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. All three declarations report exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}`: `Classical.choice` enters `normExp_exists_unique`
through `linarith`'s proof terms, and the two projections through `Exists.choose`, which is the
body the blueprint signs. No project axiom is touched (in particular not B.42).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **The normalizer exponents exist and are unique** (Bézout at the rung, `EFF.HE7.06`):
for every `k : ℤ` there is exactly one `(m, s) : ℤ × ℕ` with `s < ℓ` and `ℓ * m + s * u = k`. -/
theorem normExp_exists_unique (R : RungDatum) (k : ℤ) :
    ∃! p : ℤ × ℕ, p.2 < R.ℓ ∧ (R.ℓ : ℤ) * p.1 + (p.2 : ℤ) * (R.u : ℤ) = k := by
  have hℓpos : (0 : ℤ) < (R.ℓ : ℤ) := by exact_mod_cast R.hℓ
  have hℓne : (R.ℓ : ℤ) ≠ 0 := ne_of_gt hℓpos
  have hcop : IsCoprime (R.u : ℤ) (R.ℓ : ℤ) := R.hcop.isCoprime
  -- uniqueness: coprimality kills the slot exponent, cancellation kills the carry
  have huniq : ∀ (m m' : ℤ) (s s' : ℕ), s < R.ℓ → s' < R.ℓ →
      (R.ℓ : ℤ) * m + (s : ℤ) * (R.u : ℤ) = k →
      (R.ℓ : ℤ) * m' + (s' : ℤ) * (R.u : ℤ) = k → m = m' ∧ s = s' := by
    intro m m' s s' hs hs' h h'
    have hdvd : (R.ℓ : ℤ) ∣ ((s : ℤ) - (s' : ℤ)) * (R.u : ℤ) := ⟨m' - m, by linarith⟩
    have hd : (R.ℓ : ℤ) ∣ ((s : ℤ) - (s' : ℤ)) := hcop.symm.dvd_of_dvd_mul_right hdvd
    have hss : (s : ℤ) - (s' : ℤ) = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by omega)
    have hseq : s = s' := by omega
    subst hseq
    refine ⟨mul_left_cancel₀ hℓne ?_, rfl⟩
    linarith
  -- existence: reduce a Bézout multiplier modulo `ℓ`
  obtain ⟨m, s, hslt, hks⟩ :
      ∃ (m : ℤ) (s : ℕ), s < R.ℓ ∧ (R.ℓ : ℤ) * m + (s : ℤ) * (R.u : ℤ) = k := by
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨s, hs0, hslt, c, hc⟩ :
        ∃ s : ℤ, 0 ≤ s ∧ s < (R.ℓ : ℤ) ∧ ∃ c : ℤ, k * a = (R.ℓ : ℤ) * c + s :=
      ⟨(k * a) % (R.ℓ : ℤ), Int.emod_nonneg _ hℓne, Int.emod_lt_of_pos _ hℓpos,
        (k * a) / (R.ℓ : ℤ), (Int.mul_ediv_add_emod (k * a) (R.ℓ : ℤ)).symm⟩
    refine ⟨c * (R.u : ℤ) + k * b, s.toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg hs0]
    have hring : (R.ℓ : ℤ) * (c * (R.u : ℤ) + k * b) + s * (R.u : ℤ)
        = ((R.ℓ : ℤ) * c + s) * (R.u : ℤ) + (R.ℓ : ℤ) * (k * b) := by ring
    rw [hring, ← hc]
    calc k * a * (R.u : ℤ) + (R.ℓ : ℤ) * (k * b)
        = k * (a * (R.u : ℤ) + b * (R.ℓ : ℤ)) := by ring
      _ = k := by rw [hab, mul_one]
  refine ⟨(m, s), ⟨hslt, hks⟩, ?_⟩
  rintro ⟨m', s'⟩ ⟨hs'lt, hks'⟩
  obtain ⟨h1, h2⟩ := huniq m' m s' s hs'lt hslt hks' hks
  rw [h1, h2]

/-- The slot exponent `s(k)`: the unique `s < ℓ` with `s·u ≡ k (mod ℓ)`. -/
noncomputable def RungDatum.sExp (R : RungDatum) (k : ℤ) : ℕ :=
  (normExp_exists_unique R k).choose.2

/-- The carry exponent `m(k)`: `(k − s(k)·u)/ℓ`. -/
noncomputable def RungDatum.mExp (R : RungDatum) (k : ℤ) : ℤ :=
  (normExp_exists_unique R k).choose.1

end Uniformity.Density.Ladder

/-! ## Axiom footprint

`normExp_exists_unique` is Lean-core only. The two projections are `Exists.choose` applications
— the bodies the blueprint signs — so `Classical.choice` is expected and is the whole of the
extra footprint. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.normExp_exists_unique
#print axioms Uniformity.Density.Ladder.RungDatum.sExp
#print axioms Uniformity.Density.Ladder.RungDatum.mExp

end AxCheck
