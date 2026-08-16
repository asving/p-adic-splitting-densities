/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B26
import Uniformity.ChapB.B27
import Uniformity.ChapB.B35b
import Uniformity.ChapB.B42
import Uniformity.ChapB.B66

/-!
# Uniformity.ChapB.B72 — degree conservation for the order-1 datum

**Chapter B, NODE B.72** [lemma] [fresh] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C. One
signed declaration, `degree_order1Type`, plus one private arithmetic helper.

*Degree conservation.* For an order-1 key `φ` (`m = φ.natDegree`) and a monic block `g` with
`ḡ = φ̄ ^ μ`, `0 < μ`, a nonzero zeroth development coefficient (`h0`) and separable residuals
(`hsep`), the order-1 datum accounts for the whole degree:

```
(order1Type π φ g).degree = g.natDegree.
```

This is the **arithmetic** form of degree conservation, which B.66 explicitly could *not* state
(its own docstring: *"The arithmetic form `(order1Type π φ f).degree = f.natDegree` is NOT
provable at this node … it needs B.42's dissection welded to B.45's residual degree law"*).
B.66 shipped only the structural form `order1Type_degree`, i.e. the double sum
`Σ_S Σ_ψ ℓ_S · (m · deg ψ)` over the two canonical index `Finset`s. This node performs the weld.

**SIGNATURE.** Verbatim from the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.72**, re-signed
through A-F.10): binder names, order, implicitness and the two expanded clauses unchanged —
`(hsep : …)` is the `B-D10` expansion of B.63's `hsep` clause at `(φ, g)` (§12 item 4(b)) and
`(h0 : dev φ g 0 ≠ 0)` is the `A-F.9` repair (the A-F.6-era form is refuted at `g = φ`, where
`slopeFinset π φ φ = ∅` and the left side is `0 ≠ m`). `h0` is exactly what B.42 needs, and is
free at the consumers (B.80's per-block `hvis` via B.76(ii); B.81's `hnz`).

## Proof

Write `m = φ.natDegree` and let `s`, `F` be B.42's slope dissection of `g` (this is where `h0`
and `hμ` are consumed).

1. **The degree pin.** `g.natDegree = μ * m`, since the residue map preserves the degree of a
   monic polynomial and `(φ̄)^μ` has degree `μ * m`.
2. **`slopeFinset π φ g = s`.** B.66a's `mem_slopeFinset` (at the degree pin) characterises the
   left side as the coprime slopes carrying a two-point side; B.42's clause 5 characterises `s`
   by exactly that condition, and B.42's clause 1 supplies `0 < ℓ` and coprimality for members
   of `s`. (Nothing here needs `0 < u`, B.42's extra clause-1 conjunct.)
3. **Per slope `p ∈ s`, the residual sum is the side degree.** The stub's `hsep` makes the
   pinned residual polynomial `R_p := resPoly π φ g p.1 p.2 hne H₀` separable, hence squarefree
   (B.27), hence with `Nodup` normalized factors; `resFactorFinset π φ g p` is precisely the set
   of monic irreducible divisors of `R_p` (B.66a's `mem_resFactorFinset`, at the same `sideMin`
   pin — the two readings are identified by definitional proof irrelevance for the `Nonempty`
   witness plus injectivity of `ℕ → ℕ∞` for `H₀`), so
   `Σ_{ψ ∈ resFactorFinset π φ g p} deg ψ = deg R_p = sideDeg φ g p.1 p.2 hne` (B.30(b)).
4. **The length identity `ℓ_p · sideDeg_p · m = deg F_p`.** B.42's clause 6 ties `R_p` to the
   slope factor's own residual polynomial up to a unit constant, so the two side degrees agree
   (B.30(b) again, on both sides); `F p` is `(p.1,p.2)`-pure of degree divisible by `m`, so
   B.35b's `sideDeg_of_pure` gives `p.2 * sideDeg φ (F p) p.1 p.2 = (F p).natDegree / m`.
5. **Summing.** `Σ_{p ∈ s} (F p).natDegree = (∏_{p ∈ s} F p).natDegree = g.natDegree` (B.42's
   clause 4, `Polynomial.natDegree_prod` over the domain `O`).

Steps 4–5 are the blueprint's step 3 — the polygon's length identity `Σ_S ℓ_S d_S = μ` — obtained,
per the node's ⚠, as a corollary of B.42's factorization (a degree count over `O`) rather than as
an independent length argument. Note that the identity is never divided by `m` here: the goal is
assembled directly at the level of `deg F_p`.

## The B.45 route, and why the helper is not a private copy of it

The blueprint's DEPENDS lists B.45 (`exists_residual_factorization`) for step 3. B.45's signature
requires `R.Monic`, and the pinned residual polynomial `resPoly` is **not** monic (B.30(b) pins
its degree and its nonzero constant term, not its leading coefficient), so B.45 does not apply on
the nose. The private helper `sum_natDegree_monic_irreducible_divisors` below is therefore stated
for a nonzero, not necessarily monic, separable `R`, and is proved from the same mathlib API B.45
and B.66a are both built from (`Polynomial.mem_normalizedFactors_iff`,
`Polynomial.leadingCoeff_mul_prod_normalizedFactors`, `squarefree_iff_nodup_normalizedFactors`)
plus `Polynomial.natDegree_multiset_prod_of_monic`. It is a new statement (a *degree* count over
the divisor `Finset`), not a copy of B.45's existence-and-coprimality statement; §0.2's
private-copy ban is not engaged. **Flagged for the orchestrator** in case the roll-up prefers it
booked as a shared supplier.

DEPENDS: B.13 (the degree pin, inlined as a three-line `have` — B.61's `natDegree_of_map_residue_eq_pow`
is `private` there and not importable) · B.18 (`sideSet_nonempty`, `suppVal_ne_top`) ·
B.17 (`npHgt_ne_top_of_onSide`) · B.20 (`sideDeg`, `onSide_of_mem_sideSet`) · B.26
(`instFiniteResField`) · B.27 (`separable_iff_squarefree`) · B.30 (`natDegree_resPoly`) ·
B.35b (`sideDeg_of_pure`) · **B.42 (`exists_slope_factorization`, the signed literature axiom)** ·
B.66 (`order1Type`, `order1Type_degree`) · B.66a (`mem_slopeFinset`, `mem_resFactorFinset`) ·
mathlib `Polynomial.natDegree_prod`, `Polynomial.natDegree_multiset_prod_of_monic`,
`Polynomial.natDegree_C_mul`, `Polynomial.mem_normalizedFactors_iff`,
`Polynomial.leadingCoeff_mul_prod_normalizedFactors`,
`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`.

**SIZE.** blueprint 26 lines; landed 2 declarations.

**TEETH.** `HE6-SEP` (`EFF.HE6.49`, 4,232 rows) → **executable regression** retained (not
discharged here), per the node's TEETH field.

SOURCE: `EFF.HE6.30`(a) as completed by `EFF.HE6.59`; `EFF.HE3.13`; landed `typeOf_degree`.

## Status

Sorry-free. **Axiom footprint: Lean core + `exists_slope_factorization`** — B.42 is the signed
2026-08-16 literature import (`[cite:GN15 Thm 2.3 + FGMN Thm 6.6]`, gate (b)), consumed at step 2
and step 4, and every downstream `#print axioms` will and should display it.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The arithmetic helper -/

/-- **Private helper.** Over a finite field, the monic irreducible divisors of a nonzero
separable `R` have degrees summing to `deg R`. Separability is what makes the *set* of divisors
(rather than a multiset with multiplicities) already account for the whole degree. -/
private theorem sum_natDegree_monic_irreducible_divisors {K : Type*} [Field K] [Finite K]
    {R : Polynomial K} (hR0 : R ≠ 0) (hsepR : R.Separable) {T : Finset (Polynomial K)}
    (hT : ∀ ψ : Polynomial K, ψ ∈ T ↔ (ψ.Monic ∧ Irreducible ψ ∧ ψ ∣ R)) :
    ∑ ψ ∈ T, ψ.natDegree = R.natDegree := by
  classical
  set Fs : Multiset (Polynomial K) := UniqueFactorizationMonoid.normalizedFactors R with hFs
  have hmem : ∀ ψ : Polynomial K, ψ ∈ Fs ↔ (ψ.Monic ∧ Irreducible ψ ∧ ψ ∣ R) := by
    intro ψ
    rw [hFs, Polynomial.mem_normalizedFactors_iff hR0]
    tauto
  have hTF : T = Fs.toFinset := by
    ext ψ
    rw [hT ψ, Multiset.mem_toFinset, hmem ψ]
  have hnodup : Fs.Nodup := by
    rw [hFs]
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hR0).mp
      ((separable_iff_squarefree hR0).mp hsepR)
  have hval : Fs.toFinset.val = Fs := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hmonic : ∀ ψ ∈ Fs, ψ.Monic := fun ψ hψ => ((hmem ψ).mp hψ).1
  have hlc : (Polynomial.C R.leadingCoeff * Fs.prod) = R := by
    rw [hFs]; exact Polynomial.leadingCoeff_mul_prod_normalizedFactors R
  have hdeg : R.natDegree = Fs.prod.natDegree := by
    rw [← hlc, Polynomial.natDegree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hR0)]
  calc ∑ ψ ∈ T, ψ.natDegree
      = (Fs.map Polynomial.natDegree).sum := by
        rw [hTF, Finset.sum_eq_multiset_sum, hval]
    _ = Fs.prod.natDegree := (Polynomial.natDegree_multiset_prod_of_monic _ hmonic).symm
    _ = R.natDegree := hdeg.symm

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness. Completeness enters through
-- B.42, residue finiteness through B.26/B.27 (the separable-to-squarefree bridge).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.72 — degree conservation.** For an order-1 key `φ` and a monic block `g` with
`ḡ = φ̄ ^ μ`, `0 < μ`, `dev φ g 0 ≠ 0` and separable residuals, the order-1 datum's degree is
`g.natDegree`: no degree is lost between the polygon-and-residual index and the block. -/
theorem degree_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ g 0 ≠ 0)
    (hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ g u ℓ).Nonempty,
      1 < (sideSet φ g u ℓ).card → ∀ H₀ : ℕ, npHgt φ g (sideMin φ g u ℓ h) = (H₀ : ℕ∞) →
        (resPoly π φ g u ℓ h H₀).Separable) :
    (order1Type π φ g).degree = g.natDegree := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  haveI : Finite (resField φ) := instFiniteResField hφ
  have hm : 0 < φ.natDegree := hφ.pos
  -- Step 1: the degree pin.
  have hdeg : g.natDegree = μ * φ.natDegree := by
    have h1 : (g.map (IsLocalRing.residue O)).natDegree = g.natDegree :=
      hg.natDegree_map (IsLocalRing.residue O)
    have h2 : ((φ.map (IsLocalRing.residue O)) ^ μ).natDegree = μ * φ.natDegree := by
      rw [Polynomial.natDegree_pow, hφ.monic.natDegree_map (IsLocalRing.residue O)]
    rw [← h1, hres, h2]
  -- B.42: the slope dissection.
  obtain ⟨s, F, hs1, -, hs3, hs4, hs5, hs6⟩ :=
    exists_slope_factorization hπ hφ hg hμ hres h0
  -- Step 2: the canonical slope `Finset` is B.42's index set.
  have hslope : slopeFinset π φ g = s := by
    ext p
    rw [mem_slopeFinset hφ hg hdeg]
    constructor
    · rintro ⟨hℓ, hcop, hcard⟩
      exact (hs5 p.1 p.2 hℓ hcop).mp hcard
    · intro hp
      obtain ⟨-, hℓ, hcop⟩ := hs1 p hp
      exact ⟨hℓ, hcop, (hs5 p.1 p.2 hℓ hcop).mpr hp⟩
  -- Steps 3 and 4: per slope, the inner sum is the slope factor's degree.
  have key : ∀ p ∈ s, (∑ ψ ∈ resFactorFinset π φ g p, p.2 * (φ.natDegree * ψ.natDegree))
      = (F p).natDegree := by
    intro p hp
    obtain ⟨-, hℓ, hcop⟩ := hs1 p hp
    obtain ⟨hFmon, hFpure, hFdvd, -, -⟩ := hs3 p hp
    have hcard : 1 < (sideSet φ g p.1 p.2).card := (hs5 p.1 p.2 hℓ hcop).mpr hp
    -- the `g`-side reading, at the A-F.1 `sideMin` pin
    have htop : suppVal φ g p.1 p.2 ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hm hg hdeg p.1 p.2)
    have hne : (sideSet φ g p.1 p.2).Nonempty := sideSet_nonempty hφ.monic hm hg hdeg p.1 p.2
    have hmin : sideMin φ g p.1 p.2 hne ∈ sideSet φ g p.1 p.2 := Finset.min'_mem _ _
    obtain ⟨H₀, hH₀⟩ := WithTop.ne_top_iff_exists.mp
      (npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hmin))
    -- the slope factor's own reading
    obtain ⟨nF, hnF⟩ := hFdvd
    have hdegF : (F p).natDegree = nF * φ.natDegree := by rw [hnF]; ring
    have htopF : suppVal φ (F p) p.1 p.2 ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hm hFmon hdegF p.1 p.2)
    have hneF : (sideSet φ (F p) p.1 p.2).Nonempty :=
      sideSet_nonempty hφ.monic hm hFmon hdegF p.1 p.2
    have hminF : sideMin φ (F p) p.1 p.2 hneF ∈ sideSet φ (F p) p.1 p.2 := Finset.min'_mem _ _
    obtain ⟨H₀', hH₀'⟩ := WithTop.ne_top_iff_exists.mp
      (npHgt_ne_top_of_onSide hℓ htopF (onSide_of_mem_sideSet hminF))
    -- B.30(b) on both sides, and B.42's clause 6 between them
    have hdegR : (resPoly π φ g p.1 p.2 hne H₀).natDegree = sideDeg φ g p.1 p.2 hne :=
      (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀.symm).1
    have hdegRF : (resPoly π φ (F p) p.1 p.2 hneF H₀').natDegree
        = sideDeg φ (F p) p.1 p.2 hneF :=
      (natDegree_resPoly hπ hφ hℓ hcop htopF hneF hH₀'.symm).1
    obtain ⟨c, hc⟩ := hs6 p hp hne hneF H₀ H₀' hH₀.symm hH₀'.symm
    have hsd : sideDeg φ g p.1 p.2 hne = sideDeg φ (F p) p.1 p.2 hneF := by
      rw [← hdegR, ← hdegRF, hc, Polynomial.natDegree_C_mul (Units.ne_zero c)]
    -- Step 3: the residual sum
    have hR0 : resPoly π φ g p.1 p.2 hne H₀ ≠ 0 := by
      intro hz
      have hcz := (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀.symm).2
      rw [hz] at hcz
      exact hcz (Polynomial.coeff_zero 0)
    have hsum : (∑ ψ ∈ resFactorFinset π φ g p, ψ.natDegree) = sideDeg φ g p.1 p.2 hne := by
      rw [← hdegR]
      refine sum_natDegree_monic_irreducible_divisors hR0
        (hsep p.1 p.2 hℓ hcop hne hcard H₀ hH₀.symm) ?_
      intro ψ
      rw [mem_resFactorFinset hπ hφ hg hdeg hℓ hcop]
      refine ⟨fun h => ⟨h.1, h.2.1, h.2.2 hne H₀ hH₀.symm⟩, fun h => ⟨h.1, h.2.1, ?_⟩⟩
      intro hne' H₀'' hH₀''
      -- `hne' = hne` by definitional proof irrelevance, so `H₀'' = H₀` by injectivity of the cast
      have hcast : ((H₀'' : ℕ) : ℕ∞) = ((H₀ : ℕ) : ℕ∞) := hH₀''.symm.trans hH₀.symm
      obtain rfl : H₀'' = H₀ := by exact_mod_cast hcast
      exact h.2.2
    -- Step 4: the length identity at this slope
    have hlen : p.2 * sideDeg φ (F p) p.1 p.2 hneF = nF :=
      sideDeg_of_pure hφ.monic hm hFmon hdegF hℓ hcop hFpure hneF
    calc (∑ ψ ∈ resFactorFinset π φ g p, p.2 * (φ.natDegree * ψ.natDegree))
        = p.2 * (φ.natDegree * ∑ ψ ∈ resFactorFinset π φ g p, ψ.natDegree) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = p.2 * (φ.natDegree * sideDeg φ g p.1 p.2 hne) := by rw [hsum]
      _ = φ.natDegree * (p.2 * sideDeg φ (F p) p.1 p.2 hneF) := by rw [hsd]; ring
      _ = φ.natDegree * nF := by rw [hlen]
      _ = (F p).natDegree := hnF.symm
  -- Step 5: sum over the slopes.
  have hFne : ∀ p ∈ s, F p ≠ 0 := fun p hp => (hs3 p hp).1.ne_zero
  calc (order1Type π φ g).degree
      = ∑ p ∈ slopeFinset π φ g, ∑ ψ ∈ resFactorFinset π φ g p,
          p.2 * (φ.natDegree * ψ.natDegree) := order1Type_degree π φ g
    _ = ∑ p ∈ s, ∑ ψ ∈ resFactorFinset π φ g p, p.2 * (φ.natDegree * ψ.natDegree) := by
        rw [hslope]
    _ = ∑ p ∈ s, (F p).natDegree := Finset.sum_congr rfl key
    _ = (∏ p ∈ s, F p).natDegree := (Polynomial.natDegree_prod _ _ hFne).symm
    _ = g.natDegree := by rw [← hs4]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.degree_order1Type
end AxCheck
