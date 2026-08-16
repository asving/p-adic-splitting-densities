/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E27

/-!
# Uniformity.ChapE.E32 — `realizedSet`: the realized residues at a height

**Chapter E, NODE E.32** [def+lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6, the reach/realize
layer), ENV-E3 (the stage arena `F ⊆ K'`, generator `η : K'`).

At a height with reach set `T ⊆ Fin f₁`, the residues actually realized are the `w`-translates
of the *nonzero* elements of the `F`-span of `{η^t : t ∈ T}`:

`realizedSet η w T = { w · seamSum γ η : γ supported on T, γ ≠ 0 }`.

`w : K'ˣ` is the external twist `η_θ^{−q(k)}` — a **DATUM** here, whose value is instance
content (`EFF.T2.50`'s `(Q-DEF)` reconciliation fixes it; nothing in this file depends on
which unit it is, only that it *is* a unit).

The signed lemma is the **full-reach clause (ii)**: at `T = Finset.univ`, and with `η` a
generator in the minimal-polynomial sense (`(minpoly F η).natDegree = [K' : F] = f₁`), the
realized set is *all* of `K' ∖ {0}` — "at full `T(k)` the coset is still ALL of `K^×`".

## The two directions, and where each hypothesis is spent

* `⊆` is the seam kill: a nonzero coefficient vector cannot assemble to `0`. This is E.27 at
  the untwisted specialization `ϑ ≡ 1` (`seamSum γ η = seamSumT γ 1 η`, a `simp`), and `w`
  being a unit finishes. Note this direction alone already needs `hgen`/`hf`: without the
  generator hypothesis `seamSum` can vanish on a nonzero `γ` and the realized set meets `0`.
* `⊇` is spanning: `hgen` + `hf` make `t ↦ η^t` an `F`-basis of `K'`
  (`basisOfLinearIndependentOfCardEqFinrank` fed by H.53's `eta_independent`), so `w⁻¹ · x`
  has a coordinate vector, which is nonzero exactly when `x` is.

`f₁ > 0` is *derived*, not assumed: `minpoly.natDegree_pos` at an integral element plus
`hgen`/`hf`. That is what supplies the `Nonempty (Fin f₁)` the basis constructor wants, and it
is also the reason the statement is not vacuous — see the instantiation gate below.

## The properness rider (i) is NOT signed here — fence

ANNEX R's R5 rider reads "a proper subgroup-coset of `K₂`" as "the nonzero elements of a
proper `F_Q`-linear subspace (a punctured proper subspace)", and the composed object above is
literally of that shape: `w` is the coset half, the braces the subspace half. **The properness
claim at `T ≠ univ` is deliberately not a theorem of this file.** It is false for the bare
signature — with `f₁ = 2` but `[K' : F] = 1`, the reach `T = {0}` already realizes everything
nonzero — and becomes true only under the same `hgen`/`hf` package that clause (ii) uses. Any
consumer wanting properness must carry those hypotheses and state it; the sub-threshold proper
case is E.30(iii)+(i) composed with this node's set, not this node.

DEPENDS: E.26 (`seamSum`), E.27 (`seamSumT_ne_zero`, the kill) · mathlib
`basisOfLinearIndependentOfCardEqFinrank`, `Fintype.linearIndependent_iff`,
`minpoly.natDegree_pos`.

**Flagged for human review as a new definition** (parent CLAUDE.md trust boundary):
`realizedSet` is the composed corrected form and is the whole content of the node's def half.
Its body is the stage-0e gate-verified one from `leanspec/Leanspec/ChapE.lean`, reused verbatim.

SOURCE: `EFF.HE7.19` (the frozen realized-set display + the dated EFFECTIVE READING:
"`η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ))`, realized set = `η_θ^{−q(k)} · {Σ_{t∈T(k)} c_t·η_θ^t :
c_t ∈ F_Q, not all 0}`"); `EFF.HE7.22` (sharpness + ANNEX R R5's rider, quoted above — the Lean
object IS the composed corrected form, discharging OPEN-CALL 2's wording question at the formal
level); `EFF.T2.50` (`(Q-DEF)`: "the two agree on q(k) with no sign convention left free").

TEETH: HE7-T-LIFT2SHARP (exact sets by enumeration, ten frames; "every k above the closed-form
threshold IS surjective, and some k below it is NOT") → **Lean theorem** for the full case;
E.66/E.68 add the `q(k) ≠ 0` numeric witness the sealed teeth lacked (`EFF.HE7.19`'s disclosed
limitation).

ENVIRONMENT: ENV-E3.

## Status

Sorry-free. Footprint `[propext, Classical.choice, Quot.sound]` — Lean core only (no chapter
axiom; `Classical.choice` enters through mathlib's basis/`minpoly` route and H.53).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.32** [def] *The realized set at a height* (corrected, punctured-subspace-coset form):
the `w`-translate of the nonzero elements of the `F`-span of `{η^t : t ∈ T}`, assembled by
E.26's `seamSum`. `T` is the reach set, `w` the external twist unit (a datum). -/
def realizedSet {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    {f₁ : ℕ} (η : K') (w : K'ˣ) (T : Finset (Fin f₁)) : Set K' :=
  { x | ∃ γ : Fin f₁ → F, (∀ t ∉ T, γ t = 0) ∧ (∃ t, γ t ≠ 0) ∧
        x = (w : K') * seamSum γ η }

/-- **E.32** [lemma], clause (ii): *at full reach the realized set is everything nonzero.*
With `η` a generator in the minimal-polynomial sense and `f₁ = [K' : F]`, the reach set
`T = univ` realizes exactly `K' ∖ {0}` — the `w`-translate of everything nonzero is everything
nonzero. -/
theorem realizedSet_full {F K' : Type*} [Field F] [Field K'] [Algebra F K'] {f₁ : ℕ}
    {η : K'} (hgen : (minpoly F η).natDegree = Module.finrank F K')
    (hint : IsIntegral F η) (hf : f₁ = Module.finrank F K') (w : K'ˣ) :
    realizedSet (F := F) η w (Finset.univ : Finset (Fin f₁)) = {x : K' | x ≠ 0} := by
  classical
  -- `f₁ > 0` is derived: a minimal polynomial of an integral element has positive degree.
  have hpos : 0 < f₁ := by
    rw [hf, ← hgen]
    exact minpoly.natDegree_pos hint
  haveI : Nonempty (Fin f₁) := ⟨⟨0, hpos⟩⟩
  -- The power family is `F`-independent — H.53's `eta_independent`, repackaged.
  have hli : LinearIndependent F (fun t : Fin f₁ => η ^ (t : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro l hl t
    refine Induction.eta_independent hgen hint hf l ?_ t
    simpa [Algebra.smul_def] using hl
  have hcard : Fintype.card (Fin f₁) = Module.finrank F K' := by simp [hf]
  -- …hence a basis, by the dimension count `f₁ = [K' : F]`.
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard with hB
  have hBapply : ∀ t : Fin f₁, B t = η ^ (t : ℕ) := by
    intro t
    rw [hB, coe_basisOfLinearIndependentOfCardEqFinrank]
  ext x
  simp only [Set.mem_setOf_eq, realizedSet]
  constructor
  · -- `⊆`: the seam kill (E.27 at `ϑ ≡ 1`) plus `w` a unit.
    rintro ⟨γ, -, hγ, rfl⟩
    have h1 : seamSum γ η = seamSumT γ (fun _ => (1 : F)) η := by
      simp [seamSum, seamSumT]
    have h2 : seamSumT γ (fun _ => (1 : F)) η ≠ 0 :=
      seamSumT_ne_zero hgen hint hf γ _ hγ (fun _ => one_ne_zero)
    exact mul_ne_zero (Units.ne_zero w) (h1 ▸ h2)
  · -- `⊇`: coordinates of `w⁻¹ · x` in the power basis; nonzero `x` gives a nonzero vector.
    intro hx
    refine ⟨fun t => B.repr ((w⁻¹ : K'ˣ) * x) t, by simp, ?_, ?_⟩
    · by_contra hcon
      have hzero : B.repr (((w⁻¹ : K'ˣ) : K') * x) = 0 := by
        ext t
        simpa using not_exists.mp hcon t
      have hy : ((w⁻¹ : K'ˣ) : K') * x = 0 :=
        (LinearEquiv.map_eq_zero_iff B.repr).mp hzero
      exact hx (by simpa using (Units.mul_right_eq_zero w⁻¹).mp hy)
    · have hsum : seamSum (fun t => B.repr ((w⁻¹ : K'ˣ) * x) t) η
          = ((w⁻¹ : K'ˣ) : K') * x := by
        rw [seamSum]
        calc ∑ t : Fin f₁, algebraMap F K' (B.repr ((w⁻¹ : K'ˣ) * x) t) * η ^ (t : ℕ)
            = ∑ t : Fin f₁, B.repr ((w⁻¹ : K'ˣ) * x) t • B t := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hBapply t, Algebra.smul_def]
          _ = ((w⁻¹ : K'ˣ) : K') * x := B.sum_repr _
      rw [hsum, ← mul_assoc, Units.mul_inv, one_mul]

end Uniformity.Density.Ladder

/-! ## Gate

`realizedSet` is `Set`-valued over abstract fields, so it is not `decide`-able. Four checks
instead: two structural sanity laws on the reach parameter, a **non-vacuity instantiation** of
the signed theorem at a real (if minimal) stage extension, and the full-reach clause executed
as an enumeration over `ZMod 5` — the shape the sealed teeth (HE7-T-LIFT2SHARP) test. -/

section Gate

open Uniformity.Density.Ladder

/-- Empty reach realizes nothing: `γ` must vanish everywhere *and* somewhere be nonzero. -/
example {F K' : Type*} [Field F] [Field K'] [Algebra F K'] {f₁ : ℕ} (η : K') (w : K'ˣ) :
    realizedSet (F := F) (f₁ := f₁) η w ∅ = ∅ := by
  ext x
  simp only [realizedSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨γ, hsupp, ⟨t, ht⟩, -⟩
  exact ht (hsupp t (by simp))

/-- Growing the reach can only realize more (the reach set enters as a support constraint). -/
example {F K' : Type*} [Field F] [Field K'] [Algebra F K'] {f₁ : ℕ} (η : K') (w : K'ˣ)
    {T T' : Finset (Fin f₁)} (hTT : T ⊆ T') :
    realizedSet (F := F) η w T ⊆ realizedSet (F := F) η w T' := by
  rintro x ⟨γ, hsupp, hγ, hx⟩
  exact ⟨γ, fun t ht => hsupp t fun h => ht (hTT h), hγ, hx⟩

-- NON-VACUITY: the signed theorem's hypotheses are satisfiable, and it fires. At `F = K' = ℚ`
-- with `η = 0` the minimal polynomial is `X` (degree 1 = `[ℚ : ℚ]`), so `f₁ = 1` and the
-- realized set at full reach is all of `ℚ ∖ {0}` — an actual, non-empty conclusion.
example (w : ℚˣ) :
    realizedSet (F := ℚ) (f₁ := 1) (0 : ℚ) w Finset.univ = {x : ℚ | x ≠ 0} :=
  realizedSet_full (F := ℚ) (K' := ℚ)
    (by rw [minpoly.eq_X_sub_C']; simp)
    (isIntegral_algebraMap (x := (0 : ℚ)))
    (by simp) w

/-- At seam length `1` the realized set is the `w`-translate of the nonzero base scalars
(`η ^ 0 = 1`) — the shape the enumeration gate below executes. -/
example {F K' : Type*} [Field F] [Field K'] [Algebra F K'] (η : K') (w : K'ˣ) :
    realizedSet (F := F) (f₁ := 1) η w Finset.univ
      = {x : K' | ∃ c : F, c ≠ 0 ∧ x = (w : K') * algebraMap F K' c} := by
  ext x
  simp only [realizedSet, Set.mem_setOf_eq, seamSum]
  constructor
  · rintro ⟨γ, -, ⟨t, ht⟩, rfl⟩
    exact ⟨γ 0, by simpa [Fin.fin_one_eq_zero t] using ht, by simp⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun _ => c, by simp, ⟨0, hc⟩, by simp⟩

/-- All of `ZMod 5`, as a list. -/
private def zmod5 : List (ZMod 5) := (List.range 5).map (fun i => (i : ZMod 5))

#guard zmod5.length == 5

-- The full-reach clause EXECUTED at `f₁ = 1` over `F = K' = ZMod 5` with twist `w = 2`: the
-- realized residues `{2 · c : c ≠ 0}` are (a) all nonzero and (b) exhaust the nonzero
-- elements. That is exactly `realizedSet _ w univ = {x | x ≠ 0}`, enumerated.
private def realized5 : List (ZMod 5) := (zmod5.filter (fun c => c != 0)).map (fun c => 2 * c)

#guard realized5.all (fun x => x != 0)
#guard zmod5.all (fun x => x == 0 || realized5.contains x)

-- NEGATIVE control, same frame: drop the twist's invertibility (take `w = 0`, not a unit) and
-- the conclusion FAILS — every "realized" residue collapses to `0`. So `w : K'ˣ` is
-- load-bearing in the signature, not decoration.
#guard ((zmod5.filter (fun c => c != 0)).map (fun c => 0 * c)).all (fun x => x == 0)

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.realizedSet
#print axioms Uniformity.Density.Ladder.realizedSet_full

end AxCheck
