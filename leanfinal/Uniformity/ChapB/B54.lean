/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B08
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B17
import Uniformity.ChapB.B18
import Uniformity.ChapB.B20
import Uniformity.ChapB.B34
import Uniformity.ChapB.B53c
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapB.B54 — the residue-degree upper bound

**Chapter B, NODE B.54** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer),
ENV-C.

*The residue-degree upper bound.* Let `φ` be an order-1 key with `m = φ.natDegree`, let
`0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `g` be monic of positive degree, `(u,ℓ)`-pure
(B.34) with `d = sideDeg φ g u ℓ > 0` and `ḡ = φ̄ ^ (ℓ*d)`. Then

```
inertiaDegOf g ∣ m * d.
```

Together with B.52's `m ∣ inertiaDegOf g` this is the bracket `m ∣ f(g) ∣ m·d` that B.55
conjoins and collapses at `d = 1`.

The mechanism is the **norm bracket**: two independent elements of `AdjoinRoot g` whose norms
have computable valuations, and the gcd definition of `inertiaDegOf` (landed
`Density/TypeOf.lean`) which divides both.

* `φ(α)`, `α = AdjoinRoot.root g`: B.53's `addVal_norm_key_eval` gives
  `addVal (norm (φ α)) = m * gaussVal (dev φ g 0)`, and purity evaluates the left height as
  `gaussVal (dev φ g 0) = u*d` (step 1 below). So `m*u*d ∈ normValues g`.
* `π` itself: landed `natDegree_mem_normValues` gives `g.natDegree ∈ normValues g` (the norm of
  `algebraMap O _ π` is `π ^ deg g`), and `deg g = m*ℓ*d`. So `m*ℓ*d ∈ normValues g`.

`inertiaDegOf g` divides both, hence divides `Nat.gcd (m*d*u) (m*d*ℓ) = m*d*Nat.gcd u ℓ = m*d`.

DEPENDS: B.13b (`npHgt_top`) · B.14 (`suppVal`) · B.16 (`OnSide`, `sideSet`) · B.17
(`npHgt_ne_top_of_onSide`, `onSide_nat_eq`) · B.18 (`suppVal_ne_top`) · B.20 (`sideDeg`) · B.34
(`IsPure`) · B.53 (`addVal_norm_key_eval`) · landed `Density/TypeOf.lean`
(`normValues`, `inertiaDegOf_dvd`, `natDegree_mem_normValues`, `normValues_nonempty`) · mathlib
`Polynomial.natDegree_pow`, `Polynomial.Monic.natDegree_map`, `Algebra.norm_zero`,
`IsDiscreteValuationRing.addVal_eq_top_iff`, `Nat.gcd_mul_left`.

**PROOF.**
0. **The degree pin.** `hres` reduces to a degree identity: `g` is monic so
   `(g.map (residue O)).natDegree = g.natDegree`, while the right-hand side has degree
   `(ℓ*d) * m`. Hence `g.natDegree = (ℓ*d) * m`; in particular `m ∣ g.natDegree` and
   `g.natDegree / m = ℓ*d`.
1. **The left height.** `suppVal φ g u ℓ ≠ ⊤` (B.18 (a) with the step-0 pin). B.13b at the
   abscissa `μ = ℓ*d` gives `npHgt φ g μ = 0`, and `IsPure`'s right clause — which is `OnSide`
   at `g.natDegree / m`, i.e. at `μ` by step 0 — puts `μ` on the side. `IsPure`'s left clause
   puts `0` on the side, with finite height `H₀` (B.17 step 1). B.17 step 2 on the pair
   `(0, μ)` then reads `ℓ*H₀ + u*0 = ℓ*0 + u*(ℓ*d)`, so `H₀ = u*d` after cancelling `ℓ > 0`;
   that is, `gaussVal (dev φ g 0) = u*d`, and in particular `dev φ g 0 ≠ 0`.
2. **The two norm valuations.** B.53 with step 1: `addVal (norm (φ α)) = m*(u*d)`. Landed
   `natDegree_mem_normValues`: `g.natDegree = (ℓ*d)*m` is itself a norm-valuation.
3. **Both are in `normValues g`.** Positivity is `0 < m, u, d, ℓ`; the witness `φ α` is nonzero
   because its norm is (a finite `addVal` forbids `0` by `addVal_eq_top_iff`, and
   `Algebra.norm_zero` on the free finite nontrivial `O`-algebra `AdjoinRoot g`).
4. **The gcd.** `inertiaDegOf_dvd` twice, then
   `Nat.gcd ((m*d)*u) ((m*d)*ℓ) = (m*d) * Nat.gcd u ℓ = m*d` by `Nat.gcd_mul_left` and `hcop`.

## ⚠ `Nat.Coprime u ℓ` is consumed here and nowhere else in §7

Step 4 is the payoff. It is the same hypothesis whose necessity `EFF.HE6.52`'s tooth
`HE6-T-BADKEY` established by counterexample (`κ = 6/2` gives two factors with different
residues): without coprimality the gcd of the two norm-valuations is `m*d*gcd(u,ℓ)`, a proper
multiple of `m*d`, and the bracket does not close.

## Minimum-hypothesis note — `hres` is NOT redundant (correction to the blueprint)

The blueprint's node text says *"`hres` is needed only to make `AdjoinRoot g` local for B.53's
step 2 — actually B.53 does not need `hres` at all, so `hres` is over-strong in this node's
signature and should be dropped"* (flagged there as §14 item 8). **That is wrong for this
route, and the reason is a genuine gap, not a proof-engineering artifact.** `hres` is what pins
`g.natDegree = (ℓ*d) * m` — step 0 — and *nothing else in the signature does*:

* `IsPure φ g u ℓ` places `OnSide` at the abscissa `g.natDegree / φ.natDegree`, a **truncated**
  division. Purity is therefore compatible with `m ∤ g.natDegree`: e.g. `φ = X² + 1` over
  `ℤ_[3]` and `g = X` give `g.natDegree / m = 0`, `npHgt φ g 0 = 0`, `suppVal φ g 1 1 = 0`, so
  `IsPure φ g 1 1` holds while `m ∤ g.natDegree`.
* Both consumers of the pin need it as an *equation*: B.13b's `npHgt_top` (the polygon's
  terminal height is `0`) has the hypothesis `f.natDegree = μ * φ.natDegree` verbatim, and
  step 2's second norm-valuation is `g.natDegree`, which must be recognised as `m*ℓ*d` to
  contribute `ℓ` to the gcd.

So the minimum-hypothesis item resolves the other way: `hres` stays, and B.55 sharing it with
B.52 is a convenience on top of a load-bearing hypothesis, not the only reason to carry it. The
weakest replacement that would do is `g.natDegree = φ.natDegree * (ℓ * sideDeg φ g u ℓ hne)`;
`hres` implies it and is what the caller (B.42/B.48's dissection) actually has. **Recorded for
the cross-read (§14 item 8), which should mark the item CLOSED-AGAINST.**

## Environment note (0e type diff)

The elaborated signature carries ENV-C's `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]`, which the stub's `axiom` form drops because the *statement* names
neither. They reappear here through B.53's `addVal_norm_key_eval`, which binds both. Exactly the
artifact recorded at B.52; the mismatch is the blueprint's own declared ENV-C hypotheses
reappearing, not a weakening introduced here.

## Faithfulness

`docs/GMN_citations.md` Cor 1.20, the `m*d` half. `EFF.HE3.22` (`LEMMA HE3-1′`,
`dv(B₀) = min_j(dv(A_j) + jκ)`) is step 1: on a pure polygon the left height is the support
value, and `κ = u/ℓ` cleared by `ℓ` makes it `u*d`. `EFF.HE3.26` (`COROLLARY HE3-0′`) is the
bracket this half feeds.

SOURCE: `docs/GMN_citations.md` Cor 1.20; `EFF.HE3.22` (`LEMMA HE3-1′`); `EFF.HE3.26`.

**TEETH.** `HE-PSI` (`EFF.HE3.51`, 43,528 identities, 0 violations, guarding `EFF.HE3.22`) →
**Lean theorem** (step 1 is `LEMMA HE3-1′`'s identity in the pure case).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Both instances enter the
-- signature through B.53's `addVal_norm_key_eval` (see the environment note above).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.54 — the residue-degree upper bound.** For an order-1 key `φ`, a slope `−u/ℓ` in lowest
terms with `0 < u`, and a monic `g` of positive degree that is `(u,ℓ)`-pure with residual degree
`d > 0` and reduction `φ̄ ^ (ℓ*d)`, the residue degree of `g` divides `φ.natDegree * d`.

The norm bracket: `addVal (norm (φ α)) = m*u*d` (B.53 plus the purity height computation) and
`addVal (norm (algebraMap O _ π)) = deg g = m*ℓ*d`; the gcd of the two is `m*d` because
`gcd u ℓ = 1`. -/
theorem inertiaDegOf_dvd_key_mul_resDeg (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)) :
    inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne := by
  classical
  set d := sideDeg φ g u ℓ hne with hd_def
  -- Step 0: `hres` pins the degree — `deg g = (ℓ*d) * m`.
  have hdeg : g.natDegree = (ℓ * d) * φ.natDegree := by
    have h1 : (g.map (IsLocalRing.residue O)).natDegree = g.natDegree := hg.natDegree_map _
    have h2 : ((φ.map (IsLocalRing.residue O)) ^ (ℓ * d)).natDegree = (ℓ * d) * φ.natDegree := by
      rw [Polynomial.natDegree_pow, hφ.monic.natDegree_map]
    rw [← h1, hres, h2]
  -- Step 1: the support value is finite, and both endpoints of the polygon are on the side.
  have htop : suppVal φ g u ℓ ≠ ⊤ := by
    intro h
    have hle := suppVal_ne_top hφ.monic hφ.pos hg hdeg u ℓ
    rw [h, top_le_iff] at hle
    exact (ENat.coe_ne_top _) hle
  have hquot : g.natDegree / φ.natDegree = ℓ * d := by
    rw [hdeg]; exact Nat.mul_div_cancel _ hφ.pos
  have hend : OnSide φ g u ℓ (ℓ * d) := hquot ▸ hpure.2
  have hstart : OnSide φ g u ℓ 0 := hpure.1
  obtain ⟨H₀, hH₀⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hstart)
  have htopH : npHgt φ g (ℓ * d) = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_top hφ.monic hφ.pos hg hdeg]; simp
  -- the two on-side equations, read in `ℕ`: `ℓ*H₀ + u*0 = ℓ*0 + u*(ℓ*d)`
  have hnat : ℓ * H₀ + u * 0 = ℓ * 0 + u * (ℓ * d) :=
    onSide_nat_eq hH₀.symm htopH hstart hend
  have hH₀val : H₀ = u * d := by
    have hmul : ℓ * H₀ = ℓ * (u * d) := by
      have : ℓ * H₀ = u * (ℓ * d) := by omega
      rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_left hℓ hmul
  have hgv : gaussVal (dev φ g 0) = ((u * d : ℕ) : ℕ∞) := by
    have h : npHgt φ g 0 = ((u * d : ℕ) : ℕ∞) := by
      rw [← hH₀, hH₀val]
      rfl
    exact h
  have h0 : dev φ g 0 ≠ 0 := by
    intro hz
    rw [gaussVal_eq_top_iff.mpr hz] at hgv
    exact (ENat.coe_ne_top _) hgv.symm
  -- Step 2: the norm of `φ(α)`.
  have hnorm : IsDiscreteValuationRing.addVal O
      (Algebra.norm O (Polynomial.aeval (AdjoinRoot.root g) φ))
      = ((φ.natDegree * (u * d) : ℕ) : ℕ∞) := by
    rw [addVal_norm_key_eval hπ hφ hg hd h0, hgv]
    push_cast
    ring
  -- Step 3: both valuations are elements of `normValues g`.
  haveI hfin : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI hfree : Module.Free O (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI hntr : Nontrivial (AdjoinRoot g) := by
    have hdegne : g.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hdegne).nontrivial
  have hxne : (Polynomial.aeval (AdjoinRoot.root g) φ : AdjoinRoot g) ≠ 0 := by
    intro hz
    rw [hz, Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero] at hnorm
    exact (ENat.coe_ne_top _) hnorm.symm
  have hmem₁ : φ.natDegree * (u * d) ∈ normValues g :=
    ⟨Nat.mul_pos hφ.pos (Nat.mul_pos hu hdd), _, hxne, hnorm⟩
  have hmem₂ : g.natDegree ∈ normValues g := natDegree_mem_normValues hg hd hπ
  have hnv : (normValues g).Nonempty := normValues_nonempty hg hd
  -- Step 4: the gcd.
  have hdvd₁ : inertiaDegOf g ∣ (φ.natDegree * d) * u := by
    have := inertiaDegOf_dvd hnv hmem₁
    calc inertiaDegOf g ∣ φ.natDegree * (u * d) := this
      _ = (φ.natDegree * d) * u := by ring
  have hdvd₂ : inertiaDegOf g ∣ (φ.natDegree * d) * ℓ := by
    have := inertiaDegOf_dvd hnv hmem₂
    calc inertiaDegOf g ∣ g.natDegree := this
      _ = (φ.natDegree * d) * ℓ := by rw [hdeg]; ring
  have hgcd : Nat.gcd ((φ.natDegree * d) * u) ((φ.natDegree * d) * ℓ) = φ.natDegree * d := by
    rw [Nat.gcd_mul_left, hcop, Nat.mul_one]
  calc inertiaDegOf g ∣ Nat.gcd ((φ.natDegree * d) * u) ((φ.natDegree * d) * ℓ) :=
        Nat.dvd_gcd hdvd₁ hdvd₂
    _ = φ.natDegree * d := hgcd

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.inertiaDegOf_dvd_key_mul_resDeg
end AxCheck
