/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C16
import Uniformity.ChapC.C17
import Uniformity.ChapC.C19

/-!
# Uniformity.ChapC.C21 — `KeyFrame.slotRes`: the normalized slot residue `γ_k`

**Chapter C, NODE C.21** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1**. One signed declaration, definitional.

`γ_k(A)` is A3 F-1's **TERMINAL** display (`EFF.HE6.58`), the `n(k)`-read of `A ∈ O[X]` at height
`k`, valued in the stage field `K = F.stageField H₀ hpin` (C.03):

`γ_k(A) = Σ_{t ∈ T(k)} res(a_{i+e₁t} · π^{−(k−(i+e₁t)h)/e₁}) · η^t`,  `i := slotIdx F k`.

Three landed objects carry the three parts. The slot index `i = i(k)` is C.15's `slotIdx`; the
sum range `T(k)` is C.17's `slotWindow`; the letter `η` is C.19's `stageLetter`. The normalizer
`π^{−(k−jh)/e₁}` and the "pin strictly above height `k` contributes zero" clause are **one landed
object**, B.24's digit read `digAt π m x` (`res(x·π^{−m})` when `π^m ∣ x`, junk `0` otherwise):
`digAt` returns `0` exactly when the coefficient's own pin is too high to reach height `k`, which
is `EFF.HE6.58`'s vanishing clause, and returns the normalized residue otherwise.

## Why the window is the right range (the TEETH lemma, landed private)

Slots outside `T(k)` would need a **negative** digit index: `T(k) = {t < f₁ : (i + e₁t)h ≤ k}`
(C.17), so off the window `k − (i+e₁t)h` would be negative — in `ℕ` it truncates to `0` and
`digAt π 0` is the bare residue, which is exactly the DEAD bare-`γ` display. Restricting to the
window is therefore not a convenience: it is what makes the exponent the corpus's exponent.

On the window the exponent is moreover an **exact** `ℕ`-division. C.16(i) gives
`i·h ≡ k (mod e₁)`, and `(i + e₁t)·h ≡ i·h (mod e₁)`, so `e₁ ∣ k − (i+e₁t)h` there. The two
private lemmas below are the blueprint's TEETH entry (*"the divisibility sanity `(k − jh)/e₁ ∈ ℕ`
on the window (exact division by C.16's congruence) → Lean theorem (a private lemma in this
file)"*):

* `e₁_dvd_sub_slotCost` — the divisibility itself;
* `slotDigit_index_spec` — its consumable form `e₁·m + (i + e₁t)h = k` for `m` the digit index,
  i.e. the digit index really is the corpus's normalizer exponent `(k − jh)/e₁`.

They are `private`: GC-6.5 (one public declaration per node), and no landed node names them.

## Divergence carried from the twin (D8), and the FAITHFULNESS block

**D8.** The blueprint writes `algebraMap … (digAt π … )`, which asks for an
`Algebra (ResidueField O) (F.stageField H₀ hpin)` instance that does not exist — mathlib composes
no `Algebra` chains, and the stage field is a *two-step* `AdjoinRoot` tower (residue field →
`resField X` → `stageField`). The gate-verified twin writes the composite of the two landed
quotient maps out; that two-step form is the signed text and is what is transcribed here.

**⚠ FAITHFULNESS (trust-boundary definition — the chapter's most consequential recast).** Carried
verbatim from the blueprint, three clauses. (i) This is the **n(k)-read** (`res(A(θ)/n(k)(θ))`),
per `EFF.HE6.58`'s derivation `res(A(ξ)/n(k)(ξ)) = ι_ξ(γ_k(A))`; the ϖ-read is C.22's `twistRead`,
which multiplies this by `η^{−q(k)}`. (ii) The TERMINAL-form discipline (C-H8): the frozen
`HE6-SLOT-SEAM` display's bare `γ = Σ res(a_{i₀+e₁t})·η^t` is **vacuous** (its tying coefficients
have positive valuation), and this definition is the corrected `γ_k`; **any node or stub matching
the bare form is a defect**. (iii) The per-point embedding `ι_ξ` is eliminated: `γ_k(A)` is
`K`-valued data, and transport to factors happens through `addVal ∘ norm` statements (C.27), never
through embeddings into a closure (GC-7). Flagged to §16 for the cross-read against `EFF.HE6.58`'s
six displays.

**DEPENDS.** C.02 (`stageHeight` — the height this residue is read *at*; not consumed by the
body) · C.03 (`stageField`, through C.19) · C.15 (`slotIdx`) · C.16 (`slotIdx_spec`, for the TEETH
lemma) · C.17 (`slotWindow`) · C.19 (`stageLetter`) · B.21/B.24 (`digAt`) · B.25 (`resField`) — by
committed node ID (GC-13(b)). Imports: `Uniformity.ChapC.C16` (pulls C.15 and H.51),
`Uniformity.ChapC.C17`, `Uniformity.ChapC.C19` (pulls C.03 and the B chain).

**PROOF.** definitional (the node); the two private TEETH lemmas by C.16(i) plus
`Nat.modEq_iff_dvd'` at the window's `≤`.

SOURCE: `EFF.HE6.58` (A3 F-1, the six-display correction, verbatim); `EFF.HE6.15` (LEMMA HE6-0″,
whose consumed residue this is); `EFF.HE6.11` (`R_λ`'s coefficient reads, which C.25 builds from
this).

**TEETH.** the divisibility sanity → the two private Lean theorems above (discharged, not
deferred). `EFF.HE6.58`'s exponent-identity audit → re-derived at C.27's proof step 2, not here.

ENVIRONMENT: ENV-C1 (`hπ` enters through `digAt`, which takes `π` as data; no `Irreducible π`
hypothesis is needed to *state* the read — B.22's `digAt_eq` family supplies `hπ` at the consumers
that compute with it).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The TEETH lemmas: on the window the digit index is an exact `ℕ`-division -/

/-- **C.21 TEETH (private), part 1.** On the slot window the normalizer exponent is a genuine
`ℕ`-division: `e₁ ∣ k − (i(k) + e₁t)·h`. The congruence is C.16(i) (`i(k)·h ≡ k mod e₁`) pushed
along `(i + e₁t)·h ≡ i·h (mod e₁)`; the `≤` is the window's own defining inequality (C.17). -/
private theorem e₁_dvd_sub_slotCost (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ ∣ k - (F.slotIdx k + F.e₁ * t) * F.h := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact this.2
  refine (Nat.modEq_iff_dvd' hle).mp ?_
  calc (F.slotIdx k + F.e₁ * t) * F.h
      = F.slotIdx k * F.h + F.e₁ * (t * F.h) := by ring
    _ ≡ F.slotIdx k * F.h + 0 [MOD F.e₁] :=
        Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr ⟨t * F.h, rfl⟩)
    _ = F.slotIdx k * F.h := by ring
    _ ≡ k [MOD F.e₁] := (F.slotIdx_spec k).2

/-- **C.21 TEETH (private), part 2 — the consumable form.** The digit index used in the body,
`m = (k − (i(k) + e₁t)h) / e₁`, satisfies `e₁·m + (i(k) + e₁t)·h = k` exactly: it *is* the
corpus's normalizer exponent, with no `ℕ`-truncation anywhere. -/
private theorem slotDigit_index_spec (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + (F.slotIdx k + F.e₁ * t) * F.h = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact this.2
  rw [Nat.mul_div_cancel' (e₁_dvd_sub_slotCost F k t ht), Nat.sub_add_cancel hle]

/-! ### The signed declaration -/

/-- A3 F-1's normalized slot residue
`γ_k(A) = Σ_t res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})·η^t` (`EFF.HE6.58`, TERMINAL layer of the
`HE6-SLOT-SEAM` chain — the frozen bare-`γ` display is DEAD, C-H8).

**D8 (cured, from the gate-verified twin).** The composite of the two landed quotient maps
`ResidueField O → resField X → stageField` is written out: mathlib composes no `Algebra` chains,
so the blueprint's single `algebraMap _ _` does not elaborate. -/
noncomputable def KeyFrame.slotRes (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) (A : Polynomial O) : F.stageField H₀ hpin :=
  (F.slotWindow k).sum fun t =>
    algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
            (A.coeff (F.slotIdx k + F.e₁ * t))))
      * (F.stageLetter H₀ hpin) ^ t

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotRes

end AxCheck
