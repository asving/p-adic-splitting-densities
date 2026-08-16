/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E33 — the twist cocycle `τ`, its `(COC)` identity, and twist-unit telescoping

**Chapter E, NODE E.33** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §5), ENV-E1 (the abstract
arena: one commutative group `G` and one function `n : ℤ → G`; no ring, no field, no carrier).

R1-a(iii)'s exponent engine, in the only generality it needs. Fix a commutative group `G` and a
**normalizer system** `n : ℤ → G` — at the instances, `n k` is the level-`i` normalizer of height
`k` (`EFF.HE7.05`'s `ϖ`-powers at level 1, a monomial in the preceding residual letters above).
One definition and three identities, all group-theoretic:

* **`coc`** — the twist cocycle `τ(a, b) := n(a)·n(b)·n(a+b)⁻¹` (`(COC-DEF)`, `EFF.T2.07`). It
  measures the failure of `n` to be a homomorphism, and it is exactly the unit that the residue
  coordinates pick up when a slot value is re-based from one height to another.
* **`coc_cocycle`** — the `(COC)` identity `τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)`: the four-factor
  cancellation of `EFF.T2.07`. Both sides equal `n(a)·n(b)·n(c)·n(a+b+c)⁻¹`; the only content is
  that the two bracketings of `a + b + c` agree.
* **`theta_telescope`** — the telescoping identity of `EFF.HE7.110` Step 3: for
  `θ_t := n(m₀ − t·u)·n(u)^t·n(m₀)⁻¹`,
  `θ_t = ∏_{j < t} τ(m₀ − (j+1)u, u)`, because *"each factor is
  `n_i(m₀−(j+1)u_i)·n_i(u_i)/n_i(m₀−j·u_i)`; the product collapses"*.
* **`coc_of_hom`** — the level-1 degeneration: if `n` is a homomorphism then `τ ≡ 1` (hence every
  `θ_t = 1`). This is `EFF.HE7.108`(ii)'s *"τ₁ ≡ 1 because `k ↦ ϖ^k` is a homomorphism — THE
  point of the re-based system"*, and `EFF.HE7.110`'s *"At i = 1 every θ_t = 1 (ϖ-powers
  multiply)"*. It is why E.29's twist inputs are `ϑ ≡ 1` at the base rung, and why the twisted
  displays reduce to `(SLOT₂)`/`(LIFT₂)` byte-for-byte there.

## Reading notes

**`θ_t = 1` is a corollary, not a fifth declaration.** The blueprint's STATEMENT (ii) says "`τ ≡ 1`
and every `θ_t = 1`", and the signed SIGNATURE has four declarations, the last being `coc_of_hom`
alone. The `θ`-half is `theta_telescope` composed with `coc_of_hom` (a product of `1`s), so it
costs a one-line `rw`; adding a fifth signed name would be inventing signature.

**The exponent/group half only.** `EFF.HE7.108`'s residue evaluation
`res(τ_i(a,b)(ξ)) = ι(Π β_j^{e_j})` — the letter-monomial VALUE of the cocycle at a point — is
carrier content and is instance-supplied (chapter C); nothing here evaluates `n` anywhere. That
is exactly the split the node's TEETH field prescribes ("**Lean theorem** for the exponent/group
half; the residue evaluation stays instance content").

**⚠ GC-14 (the ϑ ORIENTATION), carried, not adjudicated.** The letters `ϑ_s`/`Θ_s` obey
`EFF.T2.08`'s `Θ_s = ϑ_s^{−1}` and `(THETA-EVAL)`'s direction. The FOUR-WAY orientation
reconciliation (GENTOW2's `ϑ` vs T1's `Θ` vs T3's `ϑ_{G2}` vs GENTOW5's reciprocal `ϑ_t`) is
**chapter D's canonical table** (`EFF.GENTOW2 orientation records [supplied-by: chapter D, the
GC-14 table]`); per honesty E-5 no chapter-E node restates or adjudicates that correspondence,
and this file does not: `coc` and `θ_t` here are T2/HE7-internal letters, used only through the
displays quoted above. A consumer that needs an orientation reads chapter D's table, never this
file.

**Why `n : ℤ → G` and not `ℕ → G`.** Heights are `ℤ`-valued (DECISION D-E1; `EFF.HE7.05`'s raw
normalizers really do have negative exponents), and the telescoping runs downwards from `m₀` in
steps of `u`, so `m₀ − t·u` must be allowed to go negative. Nothing in the three identities uses
positivity.

DEPENDS: none in Lean (E.04's `{0, ℓ}` exponent law pairs with this at the instances, but is not
consumed here) · mathlib `Finset.prod_range_succ`, `Mathlib.Tactic.Ring` (the `ℤ`-arithmetic step
`m₀ − (t+1)u + u = m₀ − tu`) and the commutative-group AC simp set
(`mul_comm`/`mul_assoc`/`mul_left_comm`; the blueprint's suggested `group` tactic normalizes FREE
group words and does not use commutativity, so it leaves both cancellations open here).

SOURCE: `EFF.T2.07` (`(COC-DEF)`/`(COC)` boxed; the four-factor cancellation derivation);
`EFF.HE7.110` (Step 3's telescoping, verbatim); `EFF.HE7.108` (R1-a(ii)'s `τ₁ ≡ 1` + (R1.1)'s
recursion — whose EXPONENT content is E.04; the letter-monomial RESIDUE value is carrier
content, instance-supplied); `EFF.T2.08` (`(THETA-EVAL)`, `Θ_s = ϑ_s^{−1}`, `(BETA)`
`τ(k,k′) = β^c` — "It is not replaced by 1. At deeper levels the same construction gives a
monomial in all preceding residual letters").

TEETH: `he7rannex_supp.py` (the exponent-vector value identity on every computed `n₃`-monomial)
→ **Lean theorem** for the exponent/group half, discharged here.

ENVIRONMENT: ENV-E1 (abstract group).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.33 `(COC-DEF)`** — the twist cocycle of a normalizer system `n : ℤ → G`:
`τ(a, b) = n(a)·n(b)·n(a+b)⁻¹` (`EFF.T2.07`). -/
def coc {G : Type*} [CommGroup G] (n : ℤ → G) (a b : ℤ) : G :=
  n a * n b * (n (a + b))⁻¹

/-- **E.33 (iii) — the `(COC)` identity** (`EFF.T2.07`): `τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)`.
Both sides collapse to `n(a)·n(b)·n(c)·n(a+b+c)⁻¹` — the four-factor cancellation. -/
theorem coc_cocycle {G : Type*} [CommGroup G] (n : ℤ → G) (a b c : ℤ) :
    coc n a b * coc n (a + b) c = coc n b c * coc n a (b + c) := by
  -- `add_assoc` is the whole content: it makes the two `n`-arguments `a + b + c` and
  -- `a + (b + c)` the same term; the rest is AC-cancellation in the commutative group.
  simp only [coc, add_assoc]
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- **E.33 (i) — twist-unit telescoping** (`EFF.HE7.110` Step 3): for
`θ_t = n(m₀ − t·u)·n(u)^t·n(m₀)⁻¹`, `θ_t = ∏_{j < t} τ(m₀ − (j+1)u, u)`. Each factor is
`n(m₀−(j+1)u)·n(u)·n(m₀−ju)⁻¹`, and the product collapses. -/
theorem theta_telescope {G : Type*} [CommGroup G] (n : ℤ → G) (m₀ u : ℤ) (t : ℕ) :
    n (m₀ - t * u) * (n u) ^ t * (n m₀)⁻¹
      = ∏ j ∈ Finset.range t, coc n (m₀ - (j + 1) * u) u := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.prod_range_succ, ← ih]
      -- the new factor is `n(m₀−(t+1)u)·n(u)·n(m₀−tu)⁻¹`: its tail cancels the old head
      have hstep : m₀ - ((t : ℤ) + 1) * u + u = m₀ - (t : ℤ) * u := by ring
      simp only [coc, hstep, Nat.cast_succ, pow_succ]
      simp [mul_comm, mul_assoc, mul_left_comm]

/-- **E.33 (ii) — the level-1 degeneration** (`EFF.HE7.108`(ii)): at a homomorphism the cocycle
is trivial. Composed with `theta_telescope` this gives `θ_t = 1` for every `t` — the reason
E.29's twist inputs are `ϑ ≡ 1` at the base rung. -/
theorem coc_of_hom {G : Type*} [CommGroup G] (n : ℤ → G)
    (hn : ∀ a b, n (a + b) = n a * n b) (a b : ℤ) : coc n a b = 1 := by
  simp [coc, hn]

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.coc
#print axioms Uniformity.Density.Ladder.coc_cocycle
#print axioms Uniformity.Density.Ladder.theta_telescope
#print axioms Uniformity.Density.Ladder.coc_of_hom

end AxCheck
