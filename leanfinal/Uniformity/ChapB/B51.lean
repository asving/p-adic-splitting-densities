/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B50
import Mathlib.RingTheory.LocalRing.Length

/-!
# Uniformity.ChapB.B51 — length multiplies by the residue degree

**Chapter B, NODE B.51** (`blueprint/CHAP-B_leaf_layer.md` §7). *Length multiplies by the residue
degree.* Let `A` be a local `O`-algebra, free and module-finite over the discrete valuation ring
`O`, whose residue field has `ResidueField O`-dimension `s`. Then for every `z : A`,

`s ∣ addVal O (Algebra.norm O z)`

whenever that valuation is finite (i.e. equals `(k : ℕ∞)`).

**DEFECT B-D6 IS CARRIED, NOT REPAIRED.** The node's first signed block,
`residueDeg_dvd_sum_of_local`, ends in the literal placeholder `s ∣ (Nat.find (…) : ℕ)` and is not
a signable statement; per the blueprint's own instruction it is RETIRED from the SIGNATURE and its
content (the extraction of the elementary-divisor sum, and the locality bookkeeping) is absorbed
into the proof below. The **sole** declaration of this node — "the contract the fleet must land" —
is `residueDeg_dvd_addVal_norm`, landed here verbatim from the signed block.

DEPENDS: B.50 (`exists_smith_of_norm`) · mathlib `IsLocalRing.length_restrictScalars`
(`Mathlib/RingTheory/LocalRing/Length.lean`), `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`,
`Module.length_pi_of_fintype`, `Module.length_eq_finrank`, `DirectSum.linearEquivFunOnFintype`.
ENVIRONMENT: ENV-A′ (ENV-A plus the explicit `hπ : Irreducible π`).

**API RISK RESOLVED — THE FALLBACK IS NOT NEEDED.** The blueprint called this "the second API
risk", warning that `Module.length` and a composition-series API might be missing from the pin and
that the route would then have to be replaced by a 110-line strong induction on `k` modelled on
landed `natDegree_dvd_addVal_norm` (`InertLeaf.lean:128`, the `s = g.natDegree`, `A ⧸ 𝔪A` a field
instance of exactly this node). At our pin (mathlib `v4.31.0`) both halves of the primary route are
present *as single lemmas*, so neither a hand-rolled composition series nor the induction is used:

* `IsLocalRing.length_restrictScalars O A M : length O M = length A M * length κ(O) κ(A)`
  — for `M` a module over the local ring `A` and `O → A` a local homomorphism. This is steps 2–3 of
  the blueprint's primary route (every simple `A`-module is `κ(A)`, of `O`-length `s`; `O`-length is
  additive along a composition series) in one citation.
* `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n : length O (O ⧸ 𝔪ᵒⁿ) = n` — the
  `O`-length of each elementary-divisor block.

The `IsLocalHom (algebraMap O A)` side condition of the first is supplied *by instance search* from
`IsLocalRing A` and `Module.Finite O A` (integrality), which is also the instance path by which the
signed hypothesis `hs`'s `Module (ResidueField O) (ResidueField A)` elaborates
(`IsLocalRing.ResidueField.instModule`) — so `hs` and the tower formula speak about the same
`κ(O)`-structure on `κ(A)`, with no diamond.

**PROOF.**
1. `hk` forces `Algebra.norm O z ≠ 0` (`addVal` of `0` is `⊤`, which is not a coercion of `k`), and
   `A` is nontrivial (it is local) and free module-finite over `O`, so `0 < finrank O A`. Feed both
   to B.50: it returns exponents `e : Fin (finrank O A) → ℕ` with
   `A ⧸ zA ≃ₗ[O] ⨁ i, O ⧸ (π ^ e i)` and `addVal O (norm z) = Σ i, e i`.
2. `O`-length of the left side: transport along that equivalence, replace `⨁` by `Π`
   (`DirectSum.linearEquivFunOnFintype`), split the product (`Module.length_pi_of_fintype`), and
   evaluate each block by `Ideal.span {π ^ n} = 𝔪ᵒⁿ` (`Irreducible.maximalIdeal_eq` plus
   `Ideal.span_singleton_pow`) and `length_quotient_pow_maximalIdeal`. Hence
   `length O (A ⧸ zA) = Σ i, e i = k`.
3. `A ⧸ (Ideal.span {z}).restrictScalars O` and `A ⧸ Ideal.span {z}` are the *same type* — the
   quotient only sees the carrier — so the `A`-module structure on the target of step 2 is available
   definitionally, and `IsLocalRing.length_restrictScalars` gives
   `(k : ℕ∞) = length A (A ⧸ zA) * length κ(O) κ(A)`, with the second factor `= s` by
   `Module.length_eq_finrank` and `hs`.
4. Descend to `ℕ`. If `s = 0` the product is `0` (in `ℕ∞`, `t * 0 = 0` even at `t = ⊤`), so `k = 0`
   and `s ∣ k`. If `s ≠ 0` then `length A (A ⧸ zA) ≠ ⊤` (otherwise the product would be `⊤ ≠ k`), so
   it is some `(m : ℕ∞)` and `k = m * s`.

**NOTE ON THE `k = 1`, `s = natDegree` CASE.** Landed `natDegree_dvd_addVal_norm`
(`Uniformity.Density.InertLeaf`) is this node when `A ⧸ 𝔪A` is a field of degree `g.natDegree`; it
is left untouched — this node does not subsume it in the corpus, it generalises it.

**SOURCE.** classical; landed `InertLeaf.lean:128` as the `k = 1` instance; `EFF.HE3.10` (the order
vs maximal-order distinction that makes this the right general form).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.51.** *Length multiplies by the residue degree.* For `A` a local `O`-algebra, free and
module-finite over the discrete valuation ring `O`, whose residue field has
`ResidueField O`-dimension `s`, the residue degree `s` divides `addVal O (Algebra.norm O z)` for
every `z : A` of finite norm-valuation `k`. -/
theorem residueDeg_dvd_addVal_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [IsLocalRing A]
    [Algebra O A] [Module.Free O A] [Module.Finite O A] {s : ℕ}
    (hs : Module.finrank (ResidueField O) (IsLocalRing.ResidueField A) = s)
    {z : A} {k : ℕ} (hk : IsDiscreteValuationRing.addVal O (Algebra.norm O z) = (k : ℕ∞)) :
    s ∣ k := by
  classical
  -- Step 1: the norm is nonzero, the rank is positive, and B.50 fires.
  have hnz : Algebra.norm O z ≠ 0 := by
    intro h
    rw [h, IsDiscreteValuationRing.addVal_zero] at hk
    exact (ENat.coe_ne_top k) hk.symm
  have hrank : 0 < Module.finrank O A := Module.finrank_pos
  obtain ⟨e, ⟨eqv⟩, hsum⟩ := exists_smith_of_norm hπ hrank hnz
  -- Step 2: the `O`-length of each elementary-divisor block.
  have hpow : ∀ n : ℕ, Module.length O (O ⧸ Ideal.span {π ^ n}) = (n : ℕ∞) := by
    intro n
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n
  have hlen : Module.length O (A ⧸ (Ideal.span {z}).restrictScalars O) = (k : ℕ∞) := by
    rw [eqv.length_eq, (DirectSum.linearEquivFunOnFintype O _
      (fun i => O ⧸ Ideal.span {π ^ e i})).length_eq, Module.length_pi_of_fintype]
    simp only [hpow]
    rw [← Nat.cast_sum, ← hsum, hk]
  -- Step 3: the same length read through the tower `O → A`.
  have hlen' : Module.length O (A ⧸ Ideal.span {z}) = (k : ℕ∞) := hlen
  have hres : Module.length (ResidueField O) (IsLocalRing.ResidueField A) = (s : ℕ∞) := by
    rw [Module.length_eq_finrank, hs]
  have htower := IsLocalRing.length_restrictScalars O A (A ⧸ Ideal.span {z})
  rw [hlen', hres] at htower
  -- Step 4: descend to `ℕ`.
  set L := Module.length A (A ⧸ Ideal.span {z}) with hL
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    simpa using htower
  · have hLne : L ≠ ⊤ := by
      intro hLtop
      rw [hLtop, ENat.top_mul (by exact_mod_cast hs0.ne')] at htower
      exact (ENat.coe_ne_top k) htower
    lift L to ℕ using hLne with m hm
    refine ⟨m, ?_⟩
    have : ((k : ℕ∞)) = ((s * m : ℕ) : ℕ∞) := by
      rw [htower, Nat.cast_mul]
      ring
    exact_mod_cast this

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.residueDeg_dvd_addVal_norm
end AxCheck
