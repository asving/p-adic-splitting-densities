/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H102
import Uniformity.Density.GenuineDensity
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapH.H103 — σ-additive assembly of decided classes (the ⟸ direction ONLY)

**Chapter H, NODE H.103** (`blueprint/CHAP-H_general_induction.md` §17.1, the dated extension of
2026-08-16, unit T-1 / provenance OM-2). The fourth node of **N-1, the level-0 class transport**.

Decided factor classes assemble. If, inside a coprime level-0 product stratum, `c₁` is decided at
the factorization type `σ₁` and `c₂` at `σ₂`, then the product class is decided at the **multiset
sum** `⟨σ₁.data + σ₂.data⟩`:

* `decidedAt_mulClass : DecidedAt O n₁ σ₁ N c₁ → DecidedAt O n₂ σ₂ N c₂ →
  DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N (mulClass c₁ c₂)`.

## ⚠ THE F-1 FENCE (blueprint §17.0, standing fence F-1) — this node is an IMPLICATION

**The per-type ⟹ direction is FALSE and must never be added here.** Distinct factor-type pairs
collide in the frame type: with `split = ⟨{(1,1),(1,1)}⟩` and `inert = ⟨{(1,2)}⟩`, both of degree
`2`,

  `split.data + inert.data  =  inert.data + split.data`,

so four factor-type combinations produce only three frame types (battery `P4 F-1 exhibit`). The
multiset sum therefore does NOT determine the summands, and no iff can hold at the σ level. A
transcription strengthening this node to
`DecidedAt ⟨σ₁.data + σ₂.data⟩ (mulClass c₁ c₂) ↔ DecidedAt σ₁ c₁ ∧ DecidedAt σ₂ c₂` is
**REFUTED** on those collision witnesses. The *predicate*-level iff — decided/undecided rather
than per-type — is a different statement and is H.104's, where `Multiset.add_right_cancel` (the
CC-1 leg) is available because only one side varies.

§2 below records the collision as machine-checked Lean, so the fence is not a comment: it is a
proof that the σ-level `⟹` is unavailable.

## Proof shape

`DecidedAt` quantifies over *all* monic lifts of the product class, so the work is: given an
arbitrary lift `b` of `mulClass c₁ c₂`, identify `typeOf (monicPoly b)`.

1. `mulClass c₁ c₂` lies in the product stratum (H.102's MapsTo half), so `b`'s reduction is
   `g₁ * g₂` and landed `Hensel.exists_monic_factorization` splits `monicPoly b = f₁ * f₂` along
   `(g₁, g₂)`.
2. The factor classes of that split ARE `(c₁, c₂)` — **this is where H.102's no-precision-loss
   clause `eq_of_mulClass_eq` is consumed**: the split's classes multiply to `mulClass c₁ c₂`,
   and so does `(c₁, c₂)`, and both pairs lie in the factor strata.
3. Hence `h₁`/`h₂` apply *at the split's own factors*, giving `typeOf f₁ = σ₁`, `typeOf f₂ = σ₂`.
4. Landed `typeOf_mul` adds the two `.data`s; `FactorizationType.ext` closes.

Step 2 is the reason the node needs the whole of H.102 and not just its MapsTo half: without
injectivity at full precision the split could a priori produce factor classes *different* from
`(c₁, c₂)`, at which point `h₁`/`h₂` say nothing about `f₁`/`f₂`.

DEPENDS: H.100 (`levelZeroStratum`, `mem_levelZeroStratum_iff`, `proj_surjective'`) · H.101
(`mulClass`, `mulClass_proj`) · H.102 (`mulClass_mem_levelZeroStratum`, `eq_of_mulClass_eq`) ·
landed `Uniformity.Density.DecidedAt`, `typeOf_mul`, `typeOf_data`, `FactorizationType.ext`,
`exists_monicPoly_eq`, `monicPoly_coeff_lt`, `Uniformity.Hensel.exists_monic_factorization`.

**ENVIRONMENT — ENV-H17 + `[IsAdicComplete (maximalIdeal O) O]`** (blueprint §17.0): all binders
inline, no section variables, **no `Finite (ResidueField O)`**.

**TEETH** (`verification/openmath/OM2_genindb_battery.py`, RESULTS run 2026-08-16, 612/612):
`P2(iv) oracle σ-tie on reader-DECIDED` (12 tie checks, 0 mismatches, PARI `factorpadic` at
`ℤ_2`/`ℤ_3` — the reader's composed σ agrees with the oracle's true type on every class the reader
calls decided) and `P4 F-1 exhibit` (`coll and len(combos) == 4 and len(frame_types) == 3`, the
fence's witness). GC-8 disposition: **Lean theorem here** for the assembly (`decidedAt_mulClass`
is the composed-σ claim, universally quantified and with the `q ∈ {2,3}` scope removed);
**executable regression retained** for the oracle tie, which is a statement about PARI and cannot
be a Lean theorem. The `P4 F-1 exhibit` is reproduced exactly in §2, as six kernel `#guard`s and
as the theorem `f1_fence`.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`). The B.42
axiom does not enter §17 before H.123.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The node -/

/-- **H.103. σ-additive assembly, the ⟸ direction.** Decided factor classes of a coprime level-0
product stratum assemble: the product class is decided at the multiset sum of the two types.

**No iff is stated, and none is available** — see the F-1 fence in the module docstring and its
machine-checked witness in §2. -/
theorem decidedAt_mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (hc₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (hc₂ : c₂ ∈ levelZeroStratum O n₂ N g₂)
    {σ₁ σ₂ : FactorizationType}
    (h₁ : DecidedAt O n₁ σ₁ N c₁) (h₂ : DecidedAt O n₂ σ₂ N c₂) :
    DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N (mulClass c₁ c₂) := by
  intro b hb
  -- 1. an arbitrary lift of the product class reduces to `g₁ * g₂`, so Hensel splits it
  have hres : (monicPoly b).map (residue O) = g₁ * g₂ :=
    mulClass_mem_levelZeroStratum hN hc₁ hc₂ b hb
  obtain ⟨f₁, f₂, hf₁, hf₂, hfb, hr₁, hr₂, hdf₁, hdf₂⟩ :=
    Uniformity.Hensel.exists_monic_factorization (monicPoly_monic b) hg₁ hg₂ hcop hres
  obtain ⟨b₁, hb₁⟩ := exists_monicPoly_eq hf₁ (by rw [hdf₁, hd₁])
  obtain ⟨b₂, hb₂⟩ := exists_monicPoly_eq hf₂ (by rw [hdf₂, hd₂])
  -- 2. the split's factor classes lie in the factor strata and multiply to the same class …
  have hm₁ : proj O n₁ N b₁ ∈ levelZeroStratum O n₁ N g₁ :=
    (mem_levelZeroStratum_iff hN _ _).2 ⟨b₁, rfl, by rw [hb₁, hr₁]⟩
  have hm₂ : proj O n₂ N b₂ ∈ levelZeroStratum O n₂ N g₂ :=
    (mem_levelZeroStratum_iff hN _ _).2 ⟨b₂, rfl, by rw [hb₂, hr₂]⟩
  have hmul : mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) = mulClass c₁ c₂ := by
    rw [← mulClass_proj b₁ b₂, hb₁, hb₂, ← hfb,
      show (fun i : Fin (n₁ + n₂) => (monicPoly b).coeff (i : ℕ)) = b from
        funext fun i => monicPoly_coeff_lt b i.isLt, hb]
  -- … so they ARE `(c₁, c₂)`: H.102's no-precision-loss clause
  obtain ⟨e₁, e₂⟩ := eq_of_mulClass_eq hN hg₁ hg₂ hcop hm₁ hc₁ hm₂ hc₂ hmul
  -- 3. the decidedness hypotheses now apply at the split's own factors
  have ht₁ : typeOf f₁ = σ₁ := by rw [← hb₁]; exact h₁ b₁ e₁
  have ht₂ : typeOf f₂ = σ₂ := by rw [← hb₂]; exact h₂ b₂ e₂
  -- 4. `typeOf_mul` adds the `.data`s
  refine FactorizationType.ext ?_
  rw [hfb, typeOf_mul hf₁ hf₂, ht₁, ht₂]

end Uniformity.Density.Induction

/-! ## 2. THE F-1 FENCE, machine-checked — why no iff is stated

Battery `P4 F-1 exhibit` (`OM2_genindb_battery.py:1124`) reads

```python
split2 = ((1, 1), (1, 1)); inert2 = ((1, 2),)
coll = (tuple(sorted(split2 + inert2)) == tuple(sorted(inert2 + split2)))
combos = {(a, b) for a in (split2, inert2) for b in (split2, inert2)}
frame_types = {tuple(sorted(a + b)) for (a, b) in combos}
check("P4 F-1 exhibit: 4 combinations, 3 frame types (per-type census NOT free)",
      coll and len(combos) == 4 and len(frame_types) == 3)
```

Transcribed below verbatim on `Multiset (ℕ × ℕ)` (Python's `tuple(sorted(...))` is the multiset
normal form). The consequence, stated as `f1_fence` and proved from the exhibit: the multiset sum
does not determine its summands even among types of the SAME degree, so no per-type `⟹` — hence
no iff — can be attached to `decidedAt_mulClass`. -/

namespace Uniformity.Density.Induction

section Fence

/-- The degree-2 split type `⟨{(1,1),(1,1)}⟩`, as the battery's `split2`. -/
private def split2 : Multiset (ℕ × ℕ) := {(1, 1), (1, 1)}

/-- The degree-2 inert type `⟨{(1,2)}⟩`, as the battery's `inert2`. -/
private def inert2 : Multiset (ℕ × ℕ) := {(1, 2)}

/-- The battery's four combinations, in order. -/
private def combos : List (Multiset (ℕ × ℕ) × Multiset (ℕ × ℕ)) :=
  [(split2, split2), (split2, inert2), (inert2, split2), (inert2, inert2)]

-- `coll`: the collision itself — `split ⊎ inert = inert ⊎ split`
#guard split2 + inert2 = inert2 + split2
-- the two colliding factor types are distinct …
#guard split2 ≠ inert2
-- … and of the same degree `2`, so the collision is not a degree artefact
#guard (⟨split2⟩ : FactorizationType).degree = 2
#guard (⟨inert2⟩ : FactorizationType).degree = 2
-- `len(combos) == 4` and `len(frame_types) == 3`
#guard combos.length = 4
#guard ((combos.map fun p => p.1 + p.2).dedup).length = 3

/-- **The F-1 fence, as a Lean statement.** Two DISTINCT ordered pairs of factorization types, of
matching degrees factorwise, share one frame type. Any per-type `⟹` for `decidedAt_mulClass`
would have to recover `(σ₁, σ₂)` from `⟨σ₁.data + σ₂.data⟩`, which this refutes. -/
theorem f1_fence : ∃ σ₁ σ₂ τ₁ τ₂ : FactorizationType,
    σ₁.data + σ₂.data = τ₁.data + τ₂.data ∧ (σ₁, σ₂) ≠ (τ₁, τ₂) ∧
      σ₁.degree = τ₁.degree ∧ σ₂.degree = τ₂.degree := by
  refine ⟨⟨split2⟩, ⟨inert2⟩, ⟨inert2⟩, ⟨split2⟩, by decide, ?_, by decide, by decide⟩
  intro h
  have : split2 = inert2 := congrArg (fun p => p.1.data) h
  exact absurd this (by decide)

end Fence

end Uniformity.Density.Induction

/-! ## 3. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.decidedAt_mulClass
#print axioms Uniformity.Density.Induction.f1_fence

end AxCheck
