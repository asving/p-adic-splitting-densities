/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapH.H76 — the `(e, f)`-forcing chain

**Chapter H, NODE H.76** (`blueprint/CHAP-H_general_induction.md` §12, sources `EFF.GENHN.15`,
`EFF.GENHN.21`, `EFF.GENHN.38`, `EFF.GENHN.42`(i)). Let `g` be monic of degree `e * f` whose
splitting type is a singleton `{p}` (one irreducible monic factor). If `e ∣ p.1` and `f ∣ p.2`,
then `p = (e, f)`.

DEPENDS: landed `typeOf`, `efPair_pos_of_mem`, `efPair_mul_le_natDegree`
(`Density/TypePositivity.lean`).

**The divisibility hypotheses are the geometric input and are NOT proved here.** The source's two
transported facts — `(T1) v(θ) = h/e₁` with `gcd(h, e₁) = 1` forces `e₁ ∣ e(L)`, and
`(T2) η = res(θ^{e₁} π^{−h})` generating `F_{Q^{f₁}} ⊆ k_L` forces `f₁ ∣ f(L)` — are statements
about the leaf field resting on the carrier (ERRATUM E3). Chapter H takes them as the hypotheses
`hpe` / `hpf`; what is proved here is that **once the two divisibilities are granted, the degree
bound forces the pair**, and that is where `efPair_mul_le_natDegree` does the work.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- **The `(e, f)`-forcing chain.** A monic `g` of degree `e * f` with a single irreducible
factor, whose pair `p` is divisible componentwise by `(e, f)`, has `p = (e, f)`: writing
`p = (e * s, f * t)`, the degree bound `p.1 * p.2 ≤ deg g = e * f` reads `e * f * (s * t) ≤ e * f`,
and positivity of `e`, `f`, `s`, `t` collapses it to `s = t = 1`. -/
theorem efPair_forced_of_dvd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {g : Polynomial O} (hg : g.Monic) {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f)
    (hdeg : g.natDegree = e * f) {p : ℕ × ℕ} (hp : (typeOf g).data = {p})
    (hpe : e ∣ p.1) (hpf : f ∣ p.2) : p = (e, f) := by
  -- Step 1: `p` really is a member pair, so it is positive and its product is bounded.
  have hmem : p ∈ (typeOf g).data := by
    rw [hp]; exact Multiset.mem_singleton_self p
  obtain ⟨hp1, hp2⟩ := efPair_pos_of_mem hg hmem
  have hle : p.1 * p.2 ≤ e * f := by
    have := efPair_mul_le_natDegree hg hmem
    rwa [hdeg] at this
  -- Step 2: the divisibilities, with positive cofactors.
  obtain ⟨s, hs⟩ := hpe
  obtain ⟨t, ht⟩ := hpf
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [hs, h0, Nat.mul_zero] at hp1; exact absurd hp1 (lt_irrefl 0)
    · exact h0
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [ht, h0, Nat.mul_zero] at hp2; exact absurd hp2 (lt_irrefl 0)
    · exact h0
  -- Step 3: `e * f * (s * t) ≤ e * f * 1` forces `s * t ≤ 1`, hence `s = t = 1`.
  have hef : 0 < e * f := Nat.mul_pos he hf
  have hmul : e * f * (s * t) ≤ e * f * 1 := by
    rw [Nat.mul_one]
    calc e * f * (s * t) = (e * s) * (f * t) := by ring
      _ = p.1 * p.2 := by rw [← hs, ← ht]
      _ ≤ e * f := hle
  have hst : s * t ≤ 1 := Nat.le_of_mul_le_mul_left hmul hef
  have hsone : s = 1 := by
    have : s ≤ s * t := Nat.le_mul_of_pos_right s ht1
    omega
  have htone : t = 1 := by
    have : t ≤ s * t := Nat.le_mul_of_pos_left t hs1
    omega
  -- Step 4: read off both components.
  have e1 : p.1 = e := by rw [hs, hsone, Nat.mul_one]
  have e2 : p.2 = f := by rw [ht, htone, Nat.mul_one]
  exact Prod.ext e1 e2

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.efPair_forced_of_dvd

end AxCheck
