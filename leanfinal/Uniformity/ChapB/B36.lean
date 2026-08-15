/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B24
import Uniformity.ChapB.B25

/-!
# Uniformity.ChapB.B36 — the slot lemma at order 1 over the base

**Chapter B, NODE B.36** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §5, the product law),
ENV-A′.

*The slot lemma at order 1 over the base.*  Let `φ` be an order-1 key with `m = φ.natDegree`,
and let `p ∈ (ResidueField O)[y]` with `p.degree < m`.  Then
`AdjoinRoot.mk (φ.map (residue O)) p = 0 ↔ p = 0`.  Consequently, for `a ∈ O[X]` with
`a.degree < φ.degree` and any `k`, `resMk π φ k a = 0 ↔ digPoly π k a = 0`; and if `a ≠ 0`
with `gaussVal a = (k : ℕ∞)` then `resMk π φ k a ≠ 0`.

The content is that `F[y]_{<m} → F[y]/(φ̄)` is injective: below the degree of the modulus the
quotient map loses nothing, so the residual coefficient read off a vertex is nonzero exactly
when the vertex is genuinely there.  This is the seam every later residual-polynomial
statement passes through (B.30 consumes it as *the slot lemma*).

DEPENDS: B.01 (`IsKey`) · B.23 (`digPoly`) · B.24 (`degree_digPoly_le`, `digPoly_eq_zero_iff`)
· B.25 (`resField`, `resMk`) · mathlib `AdjoinRoot.mk_eq_zero`, `Polynomial.Monic.degree_map`,
`Polynomial.degree_eq_natDegree`, `Polynomial.eq_zero_of_dvd_of_degree_lt`.

**PROOF.**
1. `mk_eq_zero_iff_of_degree_lt`, (→): `AdjoinRoot.mk_eq_zero` gives `φ̄ ∣ p`; `φ̄` has degree
   `m` (`Monic.degree_map hφ.monic`, the target being the nontrivial ring `ResidueField O`)
   and `p.degree < m`, so `p = 0` (`eq_zero_of_dvd_of_degree_lt`).
2. (←): `map_zero`.
3. `resMk_eq_zero_iff`: `resMk π φ k a = AdjoinRoot.mk φ̄ (digPoly π k a)` by definition, and
   `(digPoly π k a).degree ≤ a.degree < φ.degree = m` by B.24's `degree_digPoly_le`; apply
   step 1.  *[repaired: A-F.5]* `degree_digPoly_le` takes `(hπ : Irreducible π)` since A-F.5 —
   supplied by this clause's own `hπ`, already in the signature; **call-site free, SIGNATURE
   byte-unchanged.**
4. `resMk_ne_zero`: by step 3 it suffices that `digPoly π k a ≠ 0`, which is B.24's
   `digPoly_eq_zero_iff` — its hypothesis `(k : ℕ∞) ≤ gaussVal a` is `hk` with `le_refl`, and
   its conclusion `(k+1 : ℕ∞) ≤ gaussVal a = (k : ℕ∞)` is false.

## Minimum-hypothesis note

`(ha0 : a ≠ 0)` in `resMk_ne_zero` is **redundant** — it follows from `hk` (`gaussVal a = k`
is not `⊤`, and B.08's `gaussVal_eq_top_iff` says `⊤` is exactly `a = 0`).  It is carried
because the SIGNATURE is frozen; `linter.unusedVariables` is disabled locally at that
declaration for exactly this reason and no other.  The hypotheses that *are* load-bearing:
`ha` (without the degree bound the map is not injective — `resMk π φ k φ = 0` while
`digPoly π k φ ≠ 0` at `k = 0`), `hφ.monic` (it is what makes `deg φ̄ = deg φ`; over a
non-monic `φ` the reduction can drop degree and the bound is lost), and `hπ`.

## ⚠ THIS NODE IS `EFF.HE6.15` (T2 PIN `HE6-SLOT-SEAM`, 48 T2 citations) AT `e₁ = 1`

The pin's statement is *"`dv(A(ξ)) = min_i(e₁v(a_i) + ih)` **EXACTLY**, and the residue of the
attaining class, read after division by `ϖ(ξ)^{dv(A)}`, is `ι_ξ(γ)·η_ξ^{−q}`"*, as corrected
by `EFF.HE6.58` (A3 F-1, which replaced a **vacuous bare `γ`** by
`γ_k(A) := Σ_{t≥0, i+e₁t<D′} res(a_{i+e₁t}π^{−(k−(i+e₁t)h)/e₁}) η_θ^t`).  At `e₁ = 1, h = 0`:
the exactness clause `dv(A(ξ)) = min_i v(a_i)` **is** `gaussVal a`, the twist `η_ξ^{−q(k)}` is
trivial (`q(k) = 0`), and `γ_k(A)` collapses to `Σ_{t<m} res(a_t π^{−k}) η_θ^t`, which is
precisely the class of `digPoly π k a` in `F[y]/(φ̄)` under `y ↦ η_θ`.  So **`resMk π φ k a`
is `γ_k(A)`** and `resMk_ne_zero` is the exactness clause.  **The `ξ` is gone**: the corpus
states the lemma at a point `ξ` of `K̄₀` satisfying `(T1)/(T2)`, this chapter states it as the
injectivity of `F[y]_{<m} → F[y]/(φ̄)`, which is the same fact with the ambient closure
removed.  **That removal is §14 item 4 and it is the chapter's most consequential
transcription choice.**  `EFF.HE6.30`'s OPEN-CALL 2 flags exactly this pin as one whose A3
correction "sits **outside** every T2 pin span" and calls it "the most consequential item in
this compilation" — so the corrected form `EFF.HE6.58`, not the pin span `EFF.HE6.15` alone,
is what is transcribed here.  **Flagged for human review.**

SOURCE: `EFF.HE6.15` (`[PIN HE6-SLOT-SEAM]`, LEMMA HE6-0″) **as corrected by** `EFF.HE6.58`
(A3 F-1); `EFF.HE3.03` (`LEMMA GENHN-2`, the SLOT LEMMA, whose over-consumption at non-root
points `EFF.HE6.15` exists to cure); `EFF.HE3.71` (R8-5: cite HE6-0″, not GENHN-2).

TEETH: `HE6R1-SLOT2` (`EFF.HE6R1.26`, 0 violations / 1,512) → executable regression retained
at the level-2 analogue (not discharged here); `HE-NORM` (`EFF.HE3.50`, 72,134 identities) →
Lean theorem, the level-1 exactness clause being `resMk_ne_zero`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena.  ENV-A′ adds `(hπ : Irreducible π)` per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.36 (a) — the slot lemma, over the residue field.**  Below the degree of the modulus
`φ̄`, the quotient map `F[y] → F[y]/(φ̄)` is injective. -/
theorem mk_eq_zero_iff_of_degree_lt {φ : Polynomial O} (hφ : IsKey φ)
    {p : Polynomial (ResidueField O)} (hp : p.degree < (φ.natDegree : WithBot ℕ)) :
    AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) p = 0 ↔ p = 0 := by
  have hdeg : (φ.map (IsLocalRing.residue O)).degree = (φ.natDegree : WithBot ℕ) := by
    rw [hφ.monic.degree_map, Polynomial.degree_eq_natDegree hφ.monic.ne_zero]
  constructor
  · intro h
    have hlt : p.degree < (φ.map (IsLocalRing.residue O)).degree := by rw [hdeg]; exact hp
    exact Polynomial.eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_zero.mp h) hlt
  · rintro rfl
    exact map_zero _

/-- **B.36 (b) — the slot lemma, as a criterion on `resMk`.**  For `a` of degree below the
key's, the residual reduction vanishes exactly when the digit polynomial does. -/
theorem resMk_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) :
    resMk π φ k a = 0 ↔ digPoly π k a = 0 := by
  have hφdeg : φ.degree = (φ.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hφ.monic.ne_zero
  have hdeg : (digPoly π k a).degree < (φ.natDegree : WithBot ℕ) :=
    lt_of_le_of_lt (degree_digPoly_le hπ k a) (hφdeg ▸ ha)
  exact mk_eq_zero_iff_of_degree_lt hφ hdeg

set_option linter.unusedVariables false in
/-- **B.36 (c) — the exactness clause.**  At a vertex — `gaussVal a` exactly `k` — the
residual reduction of `a` at height `k` is nonzero.  This is `EFF.HE6.15`'s "EXACTLY" at
`e₁ = 1`.

`(ha0 : a ≠ 0)` is carried from the frozen SIGNATURE and is redundant (it follows from `hk`
via B.08's `gaussVal_eq_top_iff`); the linter is disabled for that binder alone. -/
theorem resMk_ne_zero (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) (ha0 : a ≠ 0)
    (hk : gaussVal a = (k : ℕ∞)) : resMk π φ k a ≠ 0 := by
  rw [Ne, resMk_eq_zero_iff hπ hφ ha, digPoly_eq_zero_iff hπ hk.ge, hk]
  simp only [Nat.cast_add, Nat.cast_one, not_le]
  exact_mod_cast Nat.lt_succ_self k

section AxCheck
#print axioms Uniformity.Density.Leaf.mk_eq_zero_iff_of_degree_lt
#print axioms Uniformity.Density.Leaf.resMk_eq_zero_iff
#print axioms Uniformity.Density.Leaf.resMk_ne_zero
end AxCheck

end Uniformity.Density.Leaf
