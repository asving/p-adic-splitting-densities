/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Basic

/-!
# Uniformity.ChapC.C30 — the descent trichotomy

**Chapter C, NODE C.30** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §5, the descent
grammar; the A-C.1 amendment set governs). ENV-C5 — the arithmetic arena: no `O`, no
polynomials, `ℕ` only. One signed declaration.

*The descent trichotomy* (COROLLARY HE6.B `[r1]`'s case split, re-derived from the proof's own
display). For a side `(u, ℓ)` (`0 < ℓ`, coprime) and a monic irreducible factor `r` of the side
residual with multiplicity `m_r ≥ 1` and `d_r := deg r ≥ 1`, exactly one of:

* **(a)** `m_r = 1` — the separable-at-`r` case (decided by the blueprint's §7 layer);
* **(b)** `m_r ≥ 2 ∧ ℓ = 1 ∧ d_r = 1` — a repeated `K`-rational linear factor at an integer
  slope: the α-refine case, where descent stays at the current level (chapter B's order-1
  recentering at the degenerate frame, `EFF.HE6.19`'s "HE3 stage-α" branch);
* **(c)** `m_r ≥ 2 ∧ 2 ≤ ℓ·d_r` — the **level jump** (LEMMA HE6R1-1's widened condition: "a node
  requires a level jump exactly when its side carries a repeated irreducible residual factor
  with `ℓ_i·deg r_i ≥ 2`").

The three cases are pairwise disjoint and exhaustive, decidably in `(m_r, ℓ, d_r)`. Disjointness
is carried inside the statement: each disjunct asserts the negation of the other cells' defining
conjunctions, so the disjunction is an exclusive one and a consumer never has to re-derive the
exclusions.

**Only the numerals appear.** The node is deliberately stated over `(mr, ℓ, dr) : ℕ` rather than
over a residual factor: the side residual, its irreducible factors and their multiplicities are
chapter B's landed objects (`resPoly`, `Squarefree`/multiplicity reads), and every §5/§7 consumer
of this trichotomy already holds `mr`, `ℓ`, `dr` as numerals extracted from them. Keeping the
node in ENV-C5 is what makes it reusable at every level of the tower — level 1 (chapter B's
side) and level 2 (the `dv`-carrier side) instantiate the same lemma.

The blueprint permits packaging the three cells as an `inductive` case tag (GC-4 allows inductive
DOMAIN types; the σ carrier is unaffected). That option is **not** exercised here: the signed
signature is the disjunction, and signatures are frozen.

DEPENDS: none (arithmetic).

**PROOF.** The one nonlinear step is `ℓ = 1 ∧ dr = 1 ↔ ℓ*dr = 1 ↔ ¬(2 ≤ ℓ*dr)` given
positivity, and it is done by hand: if `2 ≤ ℓ` then `2 = 2*1 ≤ ℓ*dr`, and symmetrically for
`dr`, so `ℓ*dr = 1` forces both factors to be `1`. Everything else is `omega` on
`(mr, ℓ, dr, ℓ*dr)` with the product as an atom.

SOURCE: `EFF.HE6R1.10` (the proof's own three-way split, verbatim: "HE6.A decides a separable
residual at every ℓ; HE3's stage-α decides a repeated K-rational linear factor at an integer
slope; the complement is exactly a repeated irreducible `r` with `ℓ·deg r ≥ 2`");
`EFF.HE6.19` (COROLLARY HE6.B `[r1]`, the honest scope + "the excluded set is now EXACTLY the
complement of the union of the two surviving node hypotheses"); `EFF.HE6R1.05` (the §S2 four-case
enumeration — the four cells `(ℓ ≥ 2?) × (d ≥ 2?)` of case (c)∪(b) refine this trichotomy; per
GC-10's re-derive rule the PROOF-consumed split is the one transcribed).

**TEETH.** `HE6-T-CASEB` + `HE6R1-T-CRACK` (both branches of (c) machine-certified genuinely
undecided by outer data — three distinct PARI σ on identical outer data) → **executable
regressions** retained; they guard the NECESSITY of the case split, which no Lean theorem states
(a Lean theorem cannot say "no outer-data-only argument decides this").

ENVIRONMENT: ENV-C5.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

/-- **C.30 — the descent trichotomy.** With `mr` the multiplicity of an irreducible residual
factor `r` of a side `(u, ℓ)` and `dr = deg r`, exactly one of: (a) `mr = 1` (separable at `r`);
(b) `mr ≥ 2`, `ℓ = 1`, `dr = 1` (the α-refine case, descent stays at the level); (c) `mr ≥ 2`
and `2 ≤ ℓ * dr` (the level jump). Each disjunct carries the negations that make the split
exclusive. -/
theorem descent_trichotomy (mr ℓ dr : ℕ) (hm : 1 ≤ mr) (hℓ : 0 < ℓ) (hd : 1 ≤ dr) :
    (mr = 1 ∧ ¬(mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1) ∧ ¬(mr ≥ 2 ∧ 2 ≤ ℓ * dr)) ∨
    (mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1 ∧ ¬(2 ≤ ℓ * dr) ∧ mr ≠ 1) ∨
    (mr ≥ 2 ∧ 2 ≤ ℓ * dr ∧ ¬(ℓ = 1 ∧ dr = 1) ∧ mr ≠ 1) := by
  -- The product of two positive naturals is `1` only when both factors are.
  have hone : ℓ * dr = 1 → ℓ = 1 ∧ dr = 1 := by
    intro hprod
    refine ⟨?_, ?_⟩
    · by_contra hne
      have h2 : 2 * 1 ≤ ℓ * dr := Nat.mul_le_mul (by omega) hd
      omega
    · by_contra hne
      have h2 : 1 * 2 ≤ ℓ * dr := Nat.mul_le_mul hℓ (by omega)
      omega
  rcases Nat.lt_or_ge mr 2 with hm2 | hm2
  · -- case (a): `mr = 1`, and both jump conditions fail on their `mr ≥ 2` conjunct.
    exact Or.inl ⟨by omega, by rintro ⟨h, -⟩; omega, by rintro ⟨h, -⟩; omega⟩
  · rcases Nat.lt_or_ge (ℓ * dr) 2 with hlt | hge
    · -- case (b): `ℓ * dr = 1`, so the slope denominator and the residual degree are both `1`.
      have hpos : 1 ≤ ℓ * dr := Nat.mul_le_mul hℓ hd
      obtain ⟨hl1, hd1⟩ := hone (by omega)
      exact Or.inr (Or.inl ⟨hm2, hl1, hd1, by omega, by omega⟩)
    · -- case (c): the level jump; `ℓ = 1 ∧ dr = 1` would contradict `2 ≤ ℓ * dr`.
      refine Or.inr (Or.inr ⟨hm2, hge, ?_, by omega⟩)
      rintro ⟨hl1, hd1⟩
      subst hl1; subst hd1
      omega

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.descent_trichotomy

end AxCheck
