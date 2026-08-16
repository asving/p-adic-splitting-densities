/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B18
import Uniformity.ChapB.B30
import Uniformity.ChapB.B33
import Uniformity.ChapB.B35b

/-!
# Uniformity.ChapB.B35c — `resPoly` is multiplicative on pure factors

**Chapter B, NODE B.35, part (c) of the mandated 4-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′ + `[Finite (ResidueField O)]`. This file carries the
**second signed contract theorem of B.35**, `resPoly_mul_of_pure` (the blueprint's PROOF steps
4–6), together with the normal-form facts about the *product* that B35d's `suppVal_mul_of_pure`
consumes:

* `suppVal_mul_eq_of_pure` — the support values add (B.33's inequality against B.18's terminal-point
  bound: for full-degree pure factors both are `u·n`, so the sandwich is an equality);
* `npHgt_mul_of_pure` — the product's height at abscissa `0` is `H₀f + H₀g`. This is the one place
  the master identity of B35b is genuinely *needed* rather than convenient: `≥` is free from the two
  bounds above, and `≤` says that the product's leading digit does not vanish, which is B35b's
  identity at `k = 0` plus `resField φ` being a domain (B.25/B.30);
* `isPure_mul_of_pure`, `sideDeg_mul_of_pure` — hence the product is pure with `sideDeg` adding.

`resPoly_mul_of_pure` is then coefficientwise: `resPoly`'s `k`-th coefficient of a full-degree pure
polynomial is `resMk π φ (H₀ − u·k) (dev φ f (ℓ·k))` at *every* `k` (`resPoly_coeff_of_pure` —
above the side both sides vanish, since the development does), and `Polynomial.coeff_mul` over
`Finset.Nat.antidiagonal` is exactly the shape of B35b's `resMk_dev_mul`. Above `d_f + d_g` both
sides vanish by degree (B.30's `natDegree_resPoly`).

The A-F.6 hypotheses do real work here: `hfd`/`hgd` (`φ.natDegree ∣ f.natDegree`) are what make
`IsPure`'s right endpoint the polygon's terminal point, so that `f.natDegree = ℓ·d_f·m` and
`H₀f = u·d_f`; `hu : 0 < u` is inherited by B35b's carry estimate. Without them the statement is
false (amendment A-F.6's two machine-checked counterexamples).

DEPENDS: B.13 (`npHgt_top`) · B.18 (`suppVal_ne_top`) · B.20 · B.25 (`resMk`, `instFieldResField`) ·
B.28/B.29 (`resCoeff`, `resPoly`) · B.30 (`natDegree_resPoly`) · B.33
(`suppVal_add_le_suppVal_mul`) · B.36 (`resMk_ne_zero`) · B35a · B35b (`resMk_dev_mul`) ·
mathlib `Polynomial.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`,
`Polynomial.natDegree_mul_le`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

private theorem weight_cast (ℓ u H j : ℕ) :
    ℓ • ((H : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
  push_cast
  simp [nsmul_eq_mul]

/-! ### The left height of a full-degree pure polygon -/

/-- **`H₀ = u · d`.** On a `(u,ℓ)`-pure polygon of full degree the left height is `u` times the
residual degree: the side runs from `(0, u·d)` to `(ℓ·d, 0)`. -/
theorem height_eq_of_pure {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {n u ℓ : ℕ} (hdeg : f.natDegree = n * φ.natDegree)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsPure φ f u ℓ)
    (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ} (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞)) :
    H₀ = u * sideDeg φ f u ℓ h := by
  have hn : ℓ * sideDeg φ f u ℓ h = n := sideDeg_of_pure hφ hd hf hdeg hℓ hcop hpure h
  have hon : ℓ • npHgt φ f 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ f u ℓ := hpure.1
  rw [hH₀, suppVal_of_pure hφ hd hf hdeg hpure, weight_cast] at hon
  have hnat : ℓ * H₀ + u * 0 = u * n := by exact_mod_cast hon
  have hcalc : ℓ * H₀ = ℓ * (u * sideDeg φ f u ℓ h) := by
    calc ℓ * H₀ = u * n := by omega
      _ = u * (ℓ * sideDeg φ f u ℓ h) := by rw [hn]
      _ = ℓ * (u * sideDeg φ f u ℓ h) := by ring
  exact Nat.eq_of_mul_eq_mul_left hℓ hcalc

/-- **The coefficients of `resPoly` on a full-degree pure polygon.** At *every* `k` (not only
`k ≤ d`) the `k`-th coefficient is the digit `resMk π φ (H₀ − u·k) (dev φ f (ℓ·k))`: above the side
both sides vanish, because the development does. -/
theorem resPoly_coeff_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {f : Polynomial O} (hf : f.Monic) {n u ℓ : ℕ}
    (hdeg : f.natDegree = n * φ.natDegree) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hpure : IsPure φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty) (H₀ k : ℕ) :
    (resPoly π φ f u ℓ h H₀).coeff k = resMk π φ (H₀ - u * k) (dev φ f (ℓ * k)) := by
  classical
  have hcoeff : (resPoly π φ f u ℓ h H₀).coeff k
      = if k < sideDeg φ f u ℓ h + 1 then resCoeff π φ f u ℓ h H₀ k else 0 := by
    rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  rw [hcoeff]
  by_cases hk : k < sideDeg φ f u ℓ h + 1
  · rw [if_pos hk, resCoeff, sideMin_of_pure hpure h, Nat.zero_add]
  · rw [if_neg hk]
    have hn : ℓ * sideDeg φ f u ℓ h = n := sideDeg_of_pure hφ hd hf hdeg hℓ hcop hpure h
    have hz : dev φ f (ℓ * k) = 0 := by
      refine dev_eq_zero_of_lt hφ hd f (ℓ * k) ?_
      rw [hdeg]
      refine mul_lt_mul_of_pos_right ?_ hd
      have hlt : sideDeg φ f u ℓ h < k := by omega
      calc n = ℓ * sideDeg φ f u ℓ h := hn.symm
        _ < ℓ * k := mul_lt_mul_of_pos_left hlt hℓ
    rw [hz, resMk_of_zero hπ]

/-! ### The product's normal form -/

section Product

/-- **The support values add** (B.35, clause 1). For full-degree pure factors, B.33's
superadditivity and B.18's terminal-point bound `≤ u·(n_f+n_g)` sandwich the product. -/
theorem suppVal_mul_eq_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) {nf ng : ℕ}
    (hfdeg : f.natDegree = nf * φ.natDegree) (hgdeg : g.natDegree = ng * φ.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) :
    suppVal φ (f * g) u ℓ = ((u * (nf + ng) : ℕ) : ℕ∞) := by
  have hfg : (f * g).natDegree = (nf + ng) * φ.natDegree := by
    rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero, hfdeg, hgdeg]; ring
  have hub : suppVal φ (f * g) u ℓ ≤ ((u * (nf + ng) : ℕ) : ℕ∞) :=
    suppVal_ne_top hφ.monic hφ.pos (hf.mul hg) hfg u ℓ
  have hlb : suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ :=
    suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u f g
  rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg hfp,
    suppVal_of_pure hφ.monic hφ.pos hg hgdeg hgp] at hlb
  refine le_antisymm hub ?_
  calc ((u * (nf + ng) : ℕ) : ℕ∞) = ((u * nf : ℕ) : ℕ∞) + ((u * ng : ℕ) : ℕ∞) := by
        push_cast; ring
    _ ≤ suppVal φ (f * g) u ℓ := hlb

/-- **The product's left height is `H₀f + H₀g`.** `≥` is the two support-value bounds; `≤` is
B35b's master identity at `k = 0` — the product of the two nonzero leading digits is nonzero in the
field `resField φ`, so the product's digit at that height does not vanish. -/
theorem npHgt_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O} (hf : f.Monic)
    (hg : g.Monic) {df dg : ℕ} (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hdf : H₀f = u * df) (hdg : H₀g = u * dg) :
    npHgt φ (f * g) 0 = ((H₀f + H₀g : ℕ) : ℕ∞) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have hsupp : suppVal φ (f * g) u ℓ = ((u * (ℓ * df + ℓ * dg) : ℕ) : ℕ∞) :=
    suppVal_mul_eq_of_pure hπ hφ hℓ hf hg hfdeg hgdeg hfp hgp
  -- `≥` : the terminal-point bound forces the height at `0` up
  have hge : ((H₀f + H₀g : ℕ) : ℕ∞) ≤ npHgt φ (f * g) 0 := by
    have hw := suppVal_le_weight hφ.monic hφ.pos hℓ u (f * g) 0
    rw [hsupp] at hw
    rcases eq_or_ne (npHgt φ (f * g) 0) ⊤ with hT | hT
    · rw [hT]; exact le_top
    obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
    rw [← hV] at hw ⊢
    rw [weight_cast] at hw
    have hnat : u * (ℓ * df + ℓ * dg) ≤ ℓ * V + u * 0 := by exact_mod_cast hw
    have hcalc : ℓ * (H₀f + H₀g) ≤ ℓ * V := by
      calc ℓ * (H₀f + H₀g) = u * (ℓ * df + ℓ * dg) := by rw [hdf, hdg]; ring
        _ ≤ ℓ * V + u * 0 := hnat
        _ = ℓ * V := by ring
    exact_mod_cast Nat.le_of_mul_le_mul_left hcalc hℓ
  -- `≤` : the master identity at `k = 0`
  have hmaster := resMk_dev_mul hπ hφ.monic hφ.pos hu hℓ hcop hf hg hfdeg hgdeg hfp hgp
    (k := 0) (Nat.zero_le _)
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_zero, Nat.mul_zero] at hmaster
  have hfne : resMk π φ H₀f (dev φ f 0) ≠ 0 := by
    refine resMk_ne_zero hπ hφ (degree_dev_lt hφ.monic hφ.pos f 0) ?_ hHf
    intro hz
    rw [npHgt_eq_top_iff.2 hz] at hHf
    exact (ENat.coe_ne_top H₀f) hHf.symm
  have hgne : resMk π φ H₀g (dev φ g 0) ≠ 0 := by
    refine resMk_ne_zero hπ hφ (degree_dev_lt hφ.monic hφ.pos g 0) ?_ hHg
    intro hz
    rw [npHgt_eq_top_iff.2 hz] at hHg
    exact (ENat.coe_ne_top H₀g) hHg.symm
  have hne0 : resMk π φ (H₀f + H₀g) (dev φ (f * g) 0) ≠ 0 := by
    have harith : u * (df + dg) = H₀f + H₀g := by rw [hdf, hdg]; ring
    rw [← harith, hmaster, ← hdf, ← hdg]
    exact mul_ne_zero hfne hgne
  rcases lt_or_ge ((H₀f + H₀g : ℕ) : ℕ∞) (npHgt φ (f * g) 0) with hlt | hle
  · exfalso
    refine hne0 (resMk_eq_zero_of_lt hπ ?_)
    have hstep : ((H₀f + H₀g : ℕ) : ℕ∞) + 1 ≤ npHgt φ (f * g) 0 := Order.add_one_le_of_lt hlt
    have hcast : ((H₀f + H₀g + 1 : ℕ) : ℕ∞) = ((H₀f + H₀g : ℕ) : ℕ∞) + 1 := by push_cast; ring
    rw [hcast]
    exact hstep
  · exact le_antisymm hle hge

/-- **The product of two full-degree pure polynomials is pure** (B.35, clause 2). -/
theorem isPure_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O} (hf : f.Monic)
    (hg : g.Monic) {df dg : ℕ} (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hdf : H₀f = u * df) (hdg : H₀g = u * dg) : IsPure φ (f * g) u ℓ := by
  have hfgdeg : (f * g).natDegree = (ℓ * df + ℓ * dg) * φ.natDegree := by
    rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero, hfdeg, hgdeg]; ring
  have hsupp : suppVal φ (f * g) u ℓ = ((u * (ℓ * df + ℓ * dg) : ℕ) : ℕ∞) :=
    suppVal_mul_eq_of_pure hπ hφ hℓ hf hg hfdeg hgdeg hfp hgp
  have hH := npHgt_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf hHg hdf hdg
  constructor
  · show ℓ • npHgt φ (f * g) 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ (f * g) u ℓ
    rw [hH, weight_cast, hsupp]
    congr 1
    rw [hdf, hdg]
    ring
  · have hn : (f * g).natDegree / φ.natDegree = ℓ * df + ℓ * dg := by
      rw [hfgdeg]; exact Nat.mul_div_cancel _ hφ.pos
    rw [hn]
    show ℓ • npHgt φ (f * g) (ℓ * df + ℓ * dg) + ((u * (ℓ * df + ℓ * dg) : ℕ) : ℕ∞)
      = suppVal φ (f * g) u ℓ
    rw [npHgt_top hφ.monic hφ.pos (hf.mul hg) hfgdeg, hsupp]
    simp

/-- **The residual degrees add** (B.35, clause 4). -/
theorem sideDeg_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O} (hf : f.Monic)
    (hg : g.Monic) {df dg : ℕ} (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hdf : H₀f = u * df) (hdg : H₀g = u * dg) (h : (sideSet φ (f * g) u ℓ).Nonempty) :
    sideDeg φ (f * g) u ℓ h = df + dg := by
  have hfgdeg : (f * g).natDegree = (ℓ * df + ℓ * dg) * φ.natDegree := by
    rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero, hfdeg, hgdeg]; ring
  have hfgp : IsPure φ (f * g) u ℓ :=
    isPure_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf hHg hdf hdg
  have hn : ℓ * sideDeg φ (f * g) u ℓ h = ℓ * df + ℓ * dg :=
    sideDeg_of_pure hφ.monic hφ.pos (hf.mul hg) hfgdeg hℓ hcop hfgp h
  refine Nat.eq_of_mul_eq_mul_left hℓ ?_
  rw [hn]
  ring

/-! ### The signed contract: `resPoly` is multiplicative -/

/-- **B.35 (b) — `resPoly` is multiplicative on pure factors** (the signed contract theorem;
signature frozen at the A-F.6 form). For `φ` an order-1 key, `0 < u`, `0 < ℓ`, `u` coprime to `ℓ`,
and `f`, `g` monic and `(u,ℓ)`-pure whose degrees are divisible by `φ.natDegree`:

```
resPoly π φ (f*g) u ℓ hfg' (H₀f + H₀g) = resPoly π φ f u ℓ hf' H₀f * resPoly π φ g u ℓ hg' H₀g.
```

Both A-F.6 hypotheses are necessary: at `u = 0` (`f = g = X²+X+1` over `ℤ₃`, `φ = X²+1`) the carry
corrupts the digit and the identity fails by exactly one monomial; without the divisibilities
`IsPure`'s truncated right endpoint does not pin the polygon. -/
theorem resPoly_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic)
    (hfd : φ.natDegree ∣ f.natDegree) (hgd : φ.natDegree ∣ g.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hf' : (sideSet φ f u ℓ).Nonempty) (hg' : (sideSet φ g u ℓ).Nonempty)
    (hfg' : (sideSet φ (f * g) u ℓ).Nonempty) :
    resPoly π φ (f * g) u ℓ hfg' (H₀f + H₀g)
      = resPoly π φ f u ℓ hf' H₀f * resPoly π φ g u ℓ hg' H₀g := by
  classical
  -- Normalisation: the divisibilities make the degrees exact, so `n = ℓ·d` and `H₀ = u·d`.
  have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hfd).symm
  have hgdeg0 : g.natDegree = (g.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hgd).symm
  have hnf : ℓ * sideDeg φ f u ℓ hf' = f.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hfp hf'
  have hng : ℓ * sideDeg φ g u ℓ hg' = g.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hg hgdeg0 hℓ hcop hgp hg'
  have hfdeg : f.natDegree = ℓ * sideDeg φ f u ℓ hf' * φ.natDegree := by
    rw [hnf]; exact hfdeg0
  have hgdeg : g.natDegree = ℓ * sideDeg φ g u ℓ hg' * φ.natDegree := by
    rw [hng]; exact hgdeg0
  have hdf : H₀f = u * sideDeg φ f u ℓ hf' :=
    height_eq_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hfp hf' hHf
  have hdg : H₀g = u * sideDeg φ g u ℓ hg' :=
    height_eq_of_pure hφ.monic hφ.pos hg hgdeg0 hℓ hcop hgp hg' hHg
  set df := sideDeg φ f u ℓ hf' with hdfdef
  set dg := sideDeg φ g u ℓ hg' with hdgdef
  -- the product's normal form
  have hfgdeg : (f * g).natDegree = (ℓ * df + ℓ * dg) * φ.natDegree := by
    rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero, hfdeg, hgdeg]; ring
  have hfgp : IsPure φ (f * g) u ℓ :=
    isPure_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf hHg hdf hdg
  have hH₀fg : npHgt φ (f * g) 0 = ((H₀f + H₀g : ℕ) : ℕ∞) :=
    npHgt_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf hHg hdf hdg
  have hsdfg : sideDeg φ (f * g) u ℓ hfg' = df + dg :=
    sideDeg_mul_of_pure hπ hφ hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hHf hHg hdf hdg hfg'
  refine Polynomial.ext fun k => ?_
  rcases Nat.lt_or_ge (df + dg) k with hk | hk
  · -- above the product's side: both sides vanish
    have hL : (resPoly π φ (f * g) u ℓ hfg' (H₀f + H₀g)).coeff k = 0 := by
      rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos (hf.mul hg) hfgdeg hℓ hcop hfgp hfg']
      have hz : dev φ (f * g) (ℓ * k) = 0 := by
        refine dev_eq_zero_of_lt hφ.monic hφ.pos (f * g) (ℓ * k) ?_
        rw [hfgdeg]
        refine mul_lt_mul_of_pos_right ?_ hφ.pos
        calc ℓ * df + ℓ * dg = ℓ * (df + dg) := by ring
          _ < ℓ * k := mul_lt_mul_of_pos_left hk hℓ
      rw [hz, resMk_of_zero hπ]
    have hRf : (resPoly π φ f u ℓ hf' H₀f).natDegree = df := by
      have htop : suppVal φ f u ℓ ≠ ⊤ := by
        rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hfp]; exact ENat.coe_ne_top _
      have hH : npHgt φ f (sideMin φ f u ℓ hf') = (H₀f : ℕ∞) := by
        rw [sideMin_of_pure hfp hf']; exact hHf
      exact (natDegree_resPoly hπ hφ hℓ hcop htop hf' hH).1
    have hRg : (resPoly π φ g u ℓ hg' H₀g).natDegree = dg := by
      have htop : suppVal φ g u ℓ ≠ ⊤ := by
        rw [suppVal_of_pure hφ.monic hφ.pos hg hgdeg0 hgp]; exact ENat.coe_ne_top _
      have hH : npHgt φ g (sideMin φ g u ℓ hg') = (H₀g : ℕ∞) := by
        rw [sideMin_of_pure hgp hg']; exact hHg
      exact (natDegree_resPoly hπ hφ hℓ hcop htop hg' hH).1
    have hR : (resPoly π φ f u ℓ hf' H₀f * resPoly π φ g u ℓ hg' H₀g).coeff k = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      refine lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
      rw [hRf, hRg]
      exact hk
    rw [hL, hR]
  · -- inside the product's side: B35b's master identity
    rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos (hf.mul hg) hfgdeg hℓ hcop hfgp hfg',
      Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterms : ∀ k₁ ∈ Finset.range (k + 1),
        (resPoly π φ f u ℓ hf' H₀f).coeff k₁ * (resPoly π φ g u ℓ hg' H₀g).coeff (k - k₁)
          = resMk π φ (H₀f - u * k₁) (dev φ f (ℓ * k₁))
              * resMk π φ (H₀g - u * (k - k₁)) (dev φ g (ℓ * (k - k₁))) := by
      intro k₁ _
      rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos hf hfdeg hℓ hcop hfp hf',
        resPoly_coeff_of_pure hπ hφ.monic hφ.pos hg hgdeg hℓ hcop hgp hg']
    rw [Finset.sum_congr rfl hterms, hdf, hdg, ← Nat.mul_add]
    exact resMk_dev_mul hπ hφ.monic hφ.pos hu hℓ hcop hf hg hfdeg hgdeg hfp hgp hk

end Product

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.height_eq_of_pure
#print axioms Uniformity.Density.Leaf.resPoly_coeff_of_pure
#print axioms Uniformity.Density.Leaf.suppVal_mul_eq_of_pure
#print axioms Uniformity.Density.Leaf.npHgt_mul_of_pure
#print axioms Uniformity.Density.Leaf.isPure_mul_of_pure
#print axioms Uniformity.Density.Leaf.sideDeg_mul_of_pure
#print axioms Uniformity.Density.Leaf.resPoly_mul_of_pure
end AxCheck
