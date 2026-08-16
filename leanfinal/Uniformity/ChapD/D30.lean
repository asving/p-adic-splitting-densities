/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Uniformity.ChapD.D30 — the corrected key polynomial and its degree/monicity

**Chapter D, NODE D.30** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5; amendments
A-1 and A-D.1 govern — neither touches this node, so the SIGNATURE below is the one signed at
composition and re-stubbed at stage 0e in `leanspec/Leanspec/ChapD.lean`, whose `correctedKey`
body is reused here byte-for-byte). ENV-D3, stated over a bare `CommRing S` (consumed at `S = O`
and at chapter C's level rings). Two signed declarations: the definition and its monicity/degree
lemma.

*The corrected key polynomial and its degree/monicity.* For a commutative ring `S`, a monic
`Φ : S[x]` with `d := Φ.natDegree ≥ 1`, `e f ≥ 1`, and coefficients `k̂ : Fin f → S[x]` with
`∀ t, (k̂ t).natDegree < d` — that hypothesis is `(C3-corrected-coefficient-bound)`, the consumed
form of `(C3-lift-coefficient-space)` — the **corrected key**

`correctedKey Φ e f k̂ := Φ^(e·f) − Σ_t k̂ t · Φ^(e·t)`

is monic of degree `e·f·d`. "The coefficient degree bound makes every lower term's degree
strictly below the monic leading term, **including `e_{i+1} = 1`, `t = f_{i+1}−1`**"
(`EFF.T1.12`'s derivation, the boundary case named): at `e = 1, t = f−1` the extremal lower term
has degree at most `(d−1) + (f−1)d = fd − 1`, which is still strictly below `fd`. That boundary
is the only place the bound is tight, and it is the reason the coefficient bound must be STRICT.

DEPENDS: mathlib only — `Polynomial.Monic.pow`, `Polynomial.natDegree_pow'`,
`Polynomial.natDegree_mul_le`, `Polynomial.natDegree_sum_le_of_forall_le`,
`Polynomial.Monic.sub_of_left`, `Polynomial.natDegree_sub_eq_left_of_natDegree_lt`.
(The blueprint DEPENDS field names `Polynomial.natDegree_sum_le`, which exists but bounds by a
`Finset.fold max`; the strict bound is taken through its `_of_forall_le` companion instead. It
also names the `Monic.natDegree_mul`-cluster; over a bare `CommRing` the product degree is only
an inequality, and `natDegree_mul_le` plus the monic power degree `natDegree_pow'` is what the
argument actually needs — no `NoZeroDivisors` assumption is introduced.)

**PROOF.**
1. Each lower term: `natDegree (k̂ t · Φ^{et}) ≤ (natDegree (k̂ t)) + e·t·d < d + e·t·d
   ≤ e·d + e·t·d = e·(t+1)·d ≤ e·f·d`, using `t + 1 ≤ f`, `1 ≤ e` and the strict coefficient
   bound. (`Φ^m` has degree exactly `m·d` because `Φ` is monic and `S` is nontrivial:
   `leadingCoeff Φ ^ m = 1 ≠ 0`.)
2. Hence the whole sum has degree `< e·f·d = natDegree (Φ^{ef})`, and a monic polynomial minus a
   strictly-lower-degree polynomial is monic of the same degree (`Monic.sub_of_left` plus
   `natDegree_sub_eq_left_of_natDegree_lt`).

SOURCE: `EFF.T1.12` (the boxed `(C3-key)` and the degree derivation). The height clause
`(C3-common-height)` — `dv_i(k̂_t Φ_i^{e_{i+1}t}) = f_{i+1}u_{i+1}` for `c_t ≠ 0`, i.e. the
arithmetic `(f−t)u + tu = fu` on the typed heights of `EFF.T1.02` — is NOT a declaration here:
the level-`i` valuation carrier that would type it is chapter C's, and at level 1 it is D.25's
exact-height clause. `(C3-corrected-lift)`'s lift-contract clauses (`(C3-lift-residue/height/zero)`)
are level-carrier statements too: at level 1 they are D.24–D.26, at level `i ≥ 2` they are
`EFF.T1.02` hypothesis data `[supplied-by: chapter C]`.

**TEETH.** T1 §4.2 checks 7–10 → the level-1 instance (D.28) + gates; the degree lemma is a
**Lean theorem** here, and it is T1 §4.2 check 7's ("coefficient-space bound") Lean leg per §13.

ENVIRONMENT: ENV-D3 (over `CommRing S`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.30 (def) — the corrected key.** `correctedKey Φ e f k̂ = Φ^{e·f} − Σ_{t<f} k̂ t · Φ^{e·t}`
(`EFF.T1.12`'s `(C3-key)`). No hypothesis is imposed at the definition: the monicity and degree
facts live in `correctedKey_monic`. -/
noncomputable def correctedKey {S : Type*} [CommRing S] (Φ : Polynomial S) (e f : ℕ)
    (khat : Fin f → Polynomial S) : Polynomial S :=
  Φ ^ (e * f) - ∑ t : Fin f, khat t * Φ ^ (e * (t : ℕ))

/-- **D.30 (lemma) — the corrected key is monic of degree `e·f·d`.** With `Φ` monic of degree
`d ≥ 1`, `e, f ≥ 1` and every coefficient `k̂ t` of degree strictly below `d`, the corrected key
`Φ^{e·f} − Σ_t k̂ t · Φ^{e·t}` is monic with `natDegree = e·f·d`. The boundary case `e = 1`,
`t = f−1` is covered: there the extremal lower term has degree at most `f·d − 1`. -/
theorem correctedKey_monic {S : Type*} [CommRing S] [Nontrivial S] {Φ : Polynomial S}
    (hΦ : Φ.Monic) (hd : 0 < Φ.natDegree) {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    {khat : Fin f → Polynomial S} (hdeg : ∀ t, (khat t).natDegree < Φ.natDegree) :
    (correctedKey Φ e f khat).Monic
    ∧ (correctedKey Φ e f khat).natDegree = e * f * Φ.natDegree := by
  set d := Φ.natDegree with hdd
  -- Monicity of `Φ` gives every power an exact degree, over a bare nontrivial `CommRing`.
  have hlead : ∀ m : ℕ, Φ.leadingCoeff ^ m ≠ 0 := by
    intro m
    rw [hΦ.leadingCoeff, one_pow]
    exact one_ne_zero
  have hpow : (Φ ^ (e * f)).Monic := hΦ.pow _
  have hpowdeg : (Φ ^ (e * f)).natDegree = e * f * d := by
    rw [Polynomial.natDegree_pow' (hlead _)]
  -- Step 1: every lower term sits strictly below the leading degree — the boundary case
  -- `e = 1`, `t = f − 1` included, via `d ≤ e * d` and `t + 1 ≤ f`.
  have hterm : ∀ t : Fin f, (khat t * Φ ^ (e * (t : ℕ))).natDegree < e * f * d := by
    intro t
    have h1 : (khat t * Φ ^ (e * (t : ℕ))).natDegree
        ≤ (khat t).natDegree + (Φ ^ (e * (t : ℕ))).natDegree :=
      Polynomial.natDegree_mul_le
    have h2 : (Φ ^ (e * (t : ℕ))).natDegree = e * (t : ℕ) * d := by
      rw [Polynomial.natDegree_pow' (hlead _)]
    have h3 : (khat t).natDegree < d := hdeg t
    have ht : (t : ℕ) + 1 ≤ f := t.isLt
    have h4 : e * ((t : ℕ) + 1) * d ≤ e * f * d :=
      Nat.mul_le_mul_right d (Nat.mul_le_mul_left e ht)
    have h5 : d ≤ e * d := Nat.le_mul_of_pos_left d he
    have h6 : e * ((t : ℕ) + 1) * d = e * (t : ℕ) * d + e * d := by ring
    omega
  have hpos : 0 < e * f * d := Nat.mul_pos (Nat.mul_pos he hf) hd
  -- Step 2: hence the whole correction sits strictly below the leading degree.
  have hsum : (∑ t : Fin f, khat t * Φ ^ (e * (t : ℕ))).natDegree < e * f * d := by
    have hle := Polynomial.natDegree_sum_le_of_forall_le (n := e * f * d - 1) Finset.univ
      (fun t : Fin f => khat t * Φ ^ (e * (t : ℕ))) (fun t _ => by have := hterm t; omega)
    omega
  have hlt : (∑ t : Fin f, khat t * Φ ^ (e * (t : ℕ))).degree < (Φ ^ (e * f)).degree :=
    Polynomial.degree_lt_degree (by rw [hpowdeg]; exact hsum)
  refine ⟨hpow.sub_of_left hlt, ?_⟩
  rw [correctedKey, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [hpowdeg]; exact hsum),
    hpowdeg]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.correctedKey
#print axioms Uniformity.Density.Gauge.correctedKey_monic

end AxCheck
