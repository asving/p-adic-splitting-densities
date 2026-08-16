/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B12
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B17
import Uniformity.ChapB.B18
import Uniformity.ChapB.B20
import Uniformity.ChapB.B34
import Uniformity.ChapB.B39a

/-!
# Uniformity.ChapB.B42a — pure ⟹ one-sided: the dictionary lemma

**Chapter B, NODE B.42a** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §6, amendment A-F.10),
ENV-A. One signed declaration. **This is a THEOREM — no axiom, no `sorry`, Lean-core
footprint.**

*The statement.* A monic `f` of degree `μ · m` (`m = φ.natDegree`) that is `(w,t)`-pure has a
**one-point** side at every genuinely different slope `(u,ℓ)`: `IsPure` forces a single-sided
polygon.

## Why this node exists (three jobs, all recorded at A-F.10)

1. **It is the obstruction that retired NODE B.42's proof route.** B.42's signed route applies
   B.41 to `f` itself at the steepest slope, and B.41's frozen signature carries
   `(hpure : IsPure φ f u ℓ)`. This lemma says purity is incompatible with the multi-side
   inductive case, so that hypothesis is unavailable exactly where the induction needs it. The
   full machine-checked record — including the corollary `b42_route_blocked` and the
   independent degree-arithmetic defect — is the committed evidence file
   `leanfinal/Uniformity/ChapB/B42_ROUTE_BLOCKED.lean.txt` (kept as `.lean.txt`, outside the
   build, per the `B39_REFUTATION` / `B59_REFUTATION` convention).
2. **It is the base-case-exhaustiveness lemma of any future retirement proof of B.42** (the
   converse direction of the pure ⟺ one-sided dictionary: B.42's step 3 needs the disjunction
   "at most one slope with a two-point side ⟹ `f` is pure" to be exhaustive).
3. **It is the in-repo coherence corroboration of the B.42 literature cite** (`B42.lean`): the
   imported theorem's clause 3 asserts each factor `F p` is `IsPure φ (F p) p.1 p.2`, and this
   lemma is the machine-checked consequence that such a factor then has one-point sides at
   every other slope — the dictionary the cite's clause-mapping bullet appeals to.

## Provenance

Verbatim from the committed proof in `leanfinal/Uniformity/ChapB/B42_ROUTE_BLOCKED.lean.txt`
(compiled at the pin, sorry-free, Lean-core `#print axioms`), landed unchanged as a node file
at the B.42 axiom landing (2026-08-16). The evidence file's second declaration
`b42_route_blocked` is NOT landed here: it is a statement about a retired proof route, not a
blueprint node, and stays in the evidence file.

DEPENDS: B.04 (`dev_eq_zero_of_lt`) · B.12 (`npHgt_eq_top_iff`) · B.13b (`npHgt_top`) ·
B.17 (`npHgt_ne_top_of_onSide`) · B.18 (`suppVal_ne_top`) · B.20 (`onSide_of_mem_sideSet`) ·
B.34 (`IsPure`, in the signature) · B.39a (`suppVal_eq_of_onSide`, `le_weight_gen`).

**PROOF.** Four lines of weight arithmetic per case. Purity pins the chord: `t·H₀ = w·μ`,
where `H₀ = npHgt φ f 0` and `npHgt φ f μ = 0`. Suppose the `(u,ℓ)`-side had two points
`j < j'`. Multiply the on-side identity at that point by `t`, the purity bound by `ℓ`, add,
cancel the common `ℓ·t·H` monomial, and divide by the positive abscissa gap — the steeper case
(`w·ℓ < u·t`) is decided at the RIGHT on-side point (`0 < j'`), the shallower case at the LEFT
one (`j < μ`, via `μ = j + d`). `hslope : u * t ≠ w * ℓ` is what makes the gap strict.

Note what is *not* assumed: no `hπ`, no coprimality of `(u,ℓ)` or `(w,t)`, no completeness, no
residue finiteness — this is an ENV-A statement.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- An abscissa of finite height of a monic `f` of degree `μ * m` is at most `μ`. -/
private theorem le_of_npHgt_ne_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) {j : ℕ}
    (hfin : npHgt φ f j ≠ ⊤) : j ≤ μ := by
  by_contra hj
  refine hfin (npHgt_eq_top_iff.2 (dev_eq_zero_of_lt hφ hd f j ?_))
  rw [hdeg]
  exact mul_lt_mul_of_pos_right (by omega) hd

/-- **B.42a — the pure ⟹ one-sided dictionary.** A monic `f` of degree `μ · m` that is
`(w,t)`-pure has a **one-point** side at every other slope: `IsPure` forces a single-sided
polygon. -/
theorem card_sideSet_le_one_of_isPure {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {w t : ℕ} (ht : 0 < t) (hpure : IsPure φ f w t)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hslope : u * t ≠ w * ℓ) :
    (sideSet φ f u ℓ).card ≤ 1 := by
  classical
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have htopwt : suppVal φ f w t ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg w t)
  have hμindex : f.natDegree / φ.natDegree = μ := by
    rw [hdeg]; exact Nat.mul_div_cancel _ hφ.pos
  have hp0 : OnSide φ f w t 0 := hpure.1
  have hpμ : OnSide φ f w t μ := by rw [← hμindex]; exact hpure.2
  obtain ⟨H₀, hH₀⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide ht htopwt hp0)
  have hHμ : npHgt φ f μ = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_top hφ.monic hφ.pos hf hdeg]; rfl
  have hSwt : suppVal φ f w t = ((t * H₀ : ℕ) : ℕ∞) := by
    have h := suppVal_eq_of_onSide (u := w) (ℓ := t) hH₀.symm hp0
    simpa using h
  have hSwtμ : suppVal φ f w t = ((w * μ : ℕ) : ℕ∞) := by
    have h := suppVal_eq_of_onSide (u := w) (ℓ := t) hHμ hpμ
    simpa using h
  have hchord : t * H₀ = w * μ := by
    have h : ((t * H₀ : ℕ) : ℕ∞) = ((w * μ : ℕ) : ℕ∞) := hSwt.symm.trans hSwtμ
    exact_mod_cast h
  -- the three inequalities available at an on-side abscissa
  have hfacts : ∀ k ∈ sideSet φ f u ℓ, ∀ Hk : ℕ, npHgt φ f k = (Hk : ℕ∞) →
      t * H₀ ≤ t * Hk + w * k ∧ ℓ * Hk + u * k ≤ ℓ * H₀ ∧ ℓ * Hk + u * k ≤ u * μ ∧ k ≤ μ := by
    intro k hk Hk hHk
    have hon : OnSide φ f u ℓ k := onSide_of_mem_sideSet hk
    have hV : suppVal φ f u ℓ = ((ℓ * Hk + u * k : ℕ) : ℕ∞) := suppVal_eq_of_onSide hHk hon
    refine ⟨le_weight_gen (u := w) (ℓ := t) hφ.monic hφ.pos ht hSwt hHk, ?_, ?_, ?_⟩
    · have := le_weight_gen (u := u) (ℓ := ℓ) hφ.monic hφ.pos hℓ hV hH₀.symm
      simpa using this
    · have := le_weight_gen (u := u) (ℓ := ℓ) hφ.monic hφ.pos hℓ hV hHμ
      simpa using this
    · exact le_of_npHgt_ne_top hφ.monic hφ.pos hdeg (by rw [hHk]; exact ENat.coe_ne_top _)
  by_contra hcard
  rw [Nat.not_le] at hcard
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard
  obtain ⟨j, hj, j', hj', hjj'⟩ :
      ∃ j ∈ sideSet φ f u ℓ, ∃ j' ∈ sideSet φ f u ℓ, j < j' := by
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, hx, y, hy, h⟩
    · exact ⟨y, hy, x, hx, by omega⟩
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1
    (npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hj))
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1
    (npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hj'))
  obtain ⟨hjpure, hj0, hjμ, hjle⟩ := hfacts j hj A hA.symm
  obtain ⟨hj'pure, hj'0, hj'μ, hj'le⟩ := hfacts j' hj' B hB.symm
  rcases lt_trichotomy (u * t) (w * ℓ) with hlt | heq | hgt
  · -- the shallower case: use the LEFT point `j < μ`
    obtain ⟨d, hdpos, hμd⟩ : ∃ d, 0 < d ∧ μ = j + d := ⟨μ - j, by omega, by omega⟩
    have e1 : t * (ℓ * A + u * j) ≤ t * (u * μ) := Nat.mul_le_mul_left t hjμ
    have e2 : ℓ * (t * H₀) ≤ ℓ * (t * A + w * j) := Nat.mul_le_mul_left ℓ hjpure
    rw [hchord] at e2
    rw [hμd] at e1 e2
    have e3 : u * t * d < w * ℓ * d := mul_lt_mul_of_pos_right hlt hdpos
    linarith
  · exact hslope heq
  · -- the steeper case: use the RIGHT point `0 < j'`
    have hj'pos : 0 < j' := by omega
    have e1 : t * (ℓ * B + u * j') ≤ t * (ℓ * H₀) := Nat.mul_le_mul_left t hj'0
    have e2 : ℓ * (t * H₀) ≤ ℓ * (t * B + w * j') := Nat.mul_le_mul_left ℓ hj'pure
    have e3 : w * ℓ * j' < u * t * j' := mul_lt_mul_of_pos_right hgt hj'pos
    linarith

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.card_sideSet_le_one_of_isPure
end AxCheck
