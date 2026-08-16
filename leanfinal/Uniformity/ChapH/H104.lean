/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H103
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H104 — the drain/decidedness composition on the PREDICATE (N-1b)

**Chapter H, NODE H.104** (`blueprint/CHAP-H_general_induction.md` §17.1 — the T-1 completion
layer, dated extension 2026-08-16; provenance OM-2 §3.1 `N-1b`, source `EFF.GENIND.54` and the
`CC-1` infeasibility record).  Fifth node of **N-1**, the level-0 class transport.

Within a coprime product stratum, the product class is (semantically) UNDECIDED **iff some
factor class is**:

* `undecidedAt_mulClass_iff : UndecidedAt (mulClass c₁ c₂) ↔ UndecidedAt c₁ ∨ UndecidedAt c₂`.

`EFF.GENIND.54`'s sentence "drains compose by *some factor drains*", in its safe (predicate)
form.

## The two directions are of completely different weight

* **`⟸` is `CC-1`'s one-line mechanism, and it is UNCONDITIONAL.** If `c₁` has two lifts of
  distinct types `τ ≠ τ'`, multiply both by ONE fixed lift `f₂` of `c₂`: the products are two
  lifts of `mulClass c₁ c₂` (H.101's `mulClass_proj`) whose types have `.data` equal to
  `τ.data + (typeOf f₂).data` and `τ'.data + (typeOf f₂).data`, and `Multiset` is cancellative,
  so they still differ.  Two lifts of distinct types is exactly `UndecidedAt`.  This is what
  `CC-1` recorded: *"the future Lean node is one `Multiset.add_right_cancel` application,
  PROVIDED all combinations are realized, which is N-1a's bijection"*.
  The two exported halves `undecidedAt_mulClass_of_left` / `..._of_right` carry **no stratum,
  no coprimality, no completeness hypothesis** — they are strictly more general than the
  blueprint's binder list, which is why they are exported rather than inlined.  (The
  right-hand half cancels on the other side, `add_left_cancel`.)
* **`⟹` is the whole Hensel layer.**  Contrapositively: both factors decided ⟹ product
  decided, which is H.103's σ-additive assembly — and H.103 rides H.102's bijection, whose
  `InjOn` half is the no-precision-loss clause.  Every hypothesis in the frozen signature
  (`hN`, `hg₁`, `hg₂`, `hd₁`, `hd₂`, `hcop`, `hc₁`, `hc₂`, `[IsAdicComplete]`) is consumed
  HERE and nowhere else.

## The F-1 fence is not touched

H.103's ⟹ direction at the σ level is REFUTED (`split ⊎ inert = inert ⊎ split`; battery PART 4's
collision exhibit), and nothing here weakens that: this node's iff is at the level of the
UNDECIDED *predicate*, which forgets which type is decided.  The predicate-level iff is exactly
the strengthening that survives the collision, and it is the one N-1c consumes.

DEPENDS: H.103 (`decidedAt_mulClass`) · H.102 (through H.103) · H.101 (`mulClass`,
`mulClass_proj`) · H.100 (`proj_surjective'`) · landed `UndecidedAt`, `DecidedAt`, `typeOf_mul`,
`FactorizationType.ext`, `exists_monicPoly_eq`, `monicPoly_monic`, `monicPoly_natDegree`,
`monicPoly_coeff_lt` · mathlib `add_right_cancel`, `add_left_cancel` (the `Multiset`
cancellation `CC-1` names).

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete (maximalIdeal O) O]`, every binder INLINE (B.42).
No `[Finite (ResidueField O)]`: this node counts nothing (H.105 does).

## TEETH (GC-8)

`verification/openmath/OM2_genindb_battery.py` PART 4, check
`P4 CC-1: no defeat of decided-composition (deg ≤ 3 exhaustive)` — an exhaustive search for a
multiset-cancellation defeat (a pair of distinct factor types whose sums with a common cofactor
type coincide), which found **zero solutions**; and PART 2's `P2(iii)`, whose per-stratum
undecided count is only correct if this iff holds cellwise.  GC-8 disposition: the CC-1 scan's
content is a `Multiset` statement, so it is a **Lean theorem** here — §4's two `example`s are the
defeat scan's negation, proved in general (`deg ≤ 3` was the battery's reach; cancellation needs
no degree bound at all) — and §5's `#guard`s re-run the battery's own two-element `(e, f)`-pair
search on the nose, over `31` types and all `31 ^ 3 = 29791` triples, finding zero defeats.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. Presenting a product of monic lifts as a lift of the product class -/

/-- **The product lift.** For lifts `a₁, a₂` of two classes, `monicPoly a₁ * monicPoly a₂` is
`monicPoly b` for a vector `b` that lifts `mulClass`.  (H.102's `mulClass_mem_levelZeroStratum`
performs the same presentation inline; it is factored out here because H.104 needs it twice, at
two different left factors.) -/
theorem exists_lift_mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    ∃ b : Fin (n₁ + n₂) → O, monicPoly b = monicPoly a₁ * monicPoly a₂ ∧
      proj O (n₁ + n₂) N b = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) := by
  obtain ⟨b, hb⟩ := exists_monicPoly_eq ((monicPoly_monic a₁).mul (monicPoly_monic a₂))
    (by rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂), monicPoly_natDegree,
      monicPoly_natDegree])
  refine ⟨b, hb, ?_⟩
  have hfe : b = fun i : Fin (n₁ + n₂) => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ) := by
    funext i
    rw [← hb, monicPoly_coeff_lt b i.isLt]
  rw [hfe, mulClass_proj]

/-- Two lifts of distinct types make a class undecided (the unfolding of `UndecidedAt` that both
`CC-1` legs end on). -/
theorem undecidedAt_of_two_types {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} {c : Coeff O n N} {b b' : Fin n → O}
    (hb : proj O n N b = c) (hb' : proj O n N b' = c)
    (hne : typeOf (monicPoly b) ≠ typeOf (monicPoly b')) : UndecidedAt O n N c := by
  intro σ hσ
  exact hne ((hσ b hb).trans (hσ b' hb').symm)

/-- A class that is not undecided is decided at some type. -/
theorem exists_decidedAt_of_not_undecidedAt {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} {c : Coeff O n N} (h : ¬ UndecidedAt O n N c) :
    ∃ σ : FactorizationType, DecidedAt O n σ N c := by
  simp only [UndecidedAt, not_forall, not_not] at h
  exact h

/-! ## 2. The `CC-1` legs — unconditional, no Hensel -/

/-- **The `CC-1` leg, left factor.** If `c₁` is undecided then so is `mulClass c₁ c₂`: fix ONE
lift of `c₂` and multiply both of `c₁`'s type-distinguishing lifts by it;
`Multiset` cancellation on the right keeps the two product types apart.

**No stratum, coprimality or completeness hypothesis is used** — the blueprint's binders belong
to the other direction. -/
theorem undecidedAt_mulClass_of_left {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n₁ n₂ N : ℕ} {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (h : UndecidedAt O n₁ N c₁) : UndecidedAt O (n₁ + n₂) N (mulClass c₁ c₂) := by
  classical
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  have hnd := h (typeOf (monicPoly a₁))
  simp only [DecidedAt, not_forall] at hnd
  obtain ⟨a₁', ha₁', hne⟩ := hnd
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  obtain ⟨b, hb, hbp⟩ := exists_lift_mulClass (N := N) a₁ a₂
  obtain ⟨b', hb', hbp'⟩ := exists_lift_mulClass (N := N) a₁' a₂
  rw [ha₁, ha₂] at hbp
  rw [ha₁', ha₂] at hbp'
  refine undecidedAt_of_two_types hbp hbp' ?_
  intro hEq
  apply hne
  have h1 : (typeOf (monicPoly b)).data
      = (typeOf (monicPoly a₁)).data + (typeOf (monicPoly a₂)).data := by
    rw [hb]; exact typeOf_mul (monicPoly_monic a₁) (monicPoly_monic a₂)
  have h2 : (typeOf (monicPoly b')).data
      = (typeOf (monicPoly a₁')).data + (typeOf (monicPoly a₂)).data := by
    rw [hb']; exact typeOf_mul (monicPoly_monic a₁') (monicPoly_monic a₂)
  exact (FactorizationType.ext (add_right_cancel (h1.symm.trans (hEq ▸ h2)))).symm

/-- **The `CC-1` leg, right factor.** The mirror of `undecidedAt_mulClass_of_left`, cancelling
on the other side (`add_left_cancel`).  Same freedom from hypotheses. -/
theorem undecidedAt_mulClass_of_right {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n₁ n₂ N : ℕ} {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (h : UndecidedAt O n₂ N c₂) : UndecidedAt O (n₁ + n₂) N (mulClass c₁ c₂) := by
  classical
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  have hnd := h (typeOf (monicPoly a₂))
  simp only [DecidedAt, not_forall] at hnd
  obtain ⟨a₂', ha₂', hne⟩ := hnd
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨b, hb, hbp⟩ := exists_lift_mulClass (N := N) a₁ a₂
  obtain ⟨b', hb', hbp'⟩ := exists_lift_mulClass (N := N) a₁ a₂'
  rw [ha₁, ha₂] at hbp
  rw [ha₁, ha₂'] at hbp'
  refine undecidedAt_of_two_types hbp hbp' ?_
  intro hEq
  apply hne
  have h1 : (typeOf (monicPoly b)).data
      = (typeOf (monicPoly a₁)).data + (typeOf (monicPoly a₂)).data := by
    rw [hb]; exact typeOf_mul (monicPoly_monic a₁) (monicPoly_monic a₂)
  have h2 : (typeOf (monicPoly b')).data
      = (typeOf (monicPoly a₁)).data + (typeOf (monicPoly a₂')).data := by
    rw [hb']; exact typeOf_mul (monicPoly_monic a₁) (monicPoly_monic a₂')
  exact (FactorizationType.ext (add_left_cancel (h1.symm.trans (hEq ▸ h2)))).symm

/-! ## 3. The node -/

/-- **H.104.** The drain/decidedness composition on the PREDICATE: within a coprime product
stratum, the product class is undecided iff SOME factor class is.

`⟸` is `CC-1`'s multiset cancellation (§2, unconditional); `⟹` is H.103's σ-additive assembly
read contrapositively, and that is where every hypothesis of the signature is spent. -/
theorem undecidedAt_mulClass_iff {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (hc₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (hc₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) :
    UndecidedAt O (n₁ + n₂) N (mulClass c₁ c₂)
      ↔ UndecidedAt O n₁ N c₁ ∨ UndecidedAt O n₂ N c₂ := by
  constructor
  · -- (⟹) contrapositive: both factors decided, so H.103 decides the product
    intro hu
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨σ₁, hσ₁⟩ := exists_decidedAt_of_not_undecidedAt h1
    obtain ⟨σ₂, hσ₂⟩ := exists_decidedAt_of_not_undecidedAt h2
    exact hu _ (decidedAt_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop hc₁ hc₂ hσ₁ hσ₂)
  · -- (⟸) the CC-1 legs
    rintro (h | h)
    · exact undecidedAt_mulClass_of_left h
    · exact undecidedAt_mulClass_of_right h

end Uniformity.Density.Induction

/-! ## 4. TEETH, Lean half — the `CC-1` defeat scan, proved in general

Battery PART 4 searches exhaustively (`deg ≤ 3`) for a **defeat of decided-composition**: a pair
of DISTINCT factor types `τ ≠ τ'` and a cofactor type `κ` with `τ ⊎ κ = τ' ⊎ κ`, which would let
two differently-typed factor lifts produce identically-typed products and so break the `⟸` leg.
It found none.  The scan's content is pure `Multiset` cancellation, so it is provable with no
degree bound whatsoever — the theorem below is the battery's check with its `deg ≤ 3` reach
removed. -/

section Teeth

open Uniformity Uniformity.Density

/-- TEETH — the CC-1 defeat scan, in general: no cofactor type can merge two distinct factor
types.  (The battery certified this for `deg ≤ 3`; cancellation gives it for all degrees.) -/
example (τ τ' κ : FactorizationType) (hne : τ ≠ τ')
    (h : (⟨τ.data + κ.data⟩ : FactorizationType) = ⟨τ'.data + κ.data⟩) : False := by
  have hd : τ.data + κ.data = τ'.data + κ.data := congrArg FactorizationType.data h
  exact hne (FactorizationType.ext (add_right_cancel hd))

/-- TEETH — the same on the other side (the `_of_right` leg's cancellation). -/
example (τ τ' κ : FactorizationType) (hne : τ ≠ τ')
    (h : (⟨κ.data + τ.data⟩ : FactorizationType) = ⟨κ.data + τ'.data⟩) : False := by
  have hd : κ.data + τ.data = κ.data + τ'.data := congrArg FactorizationType.data h
  exact hne (FactorizationType.ext (add_left_cancel hd))

end Teeth

/-! ## 5. TEETH, numeric half — the battery's two-element `(e, f)`-pair search

PART 4 ranges over multisets of `(e, f)` pairs of total degree `≤ 3` (the recorded restriction
argument reduces the scan to 2-element pairs).  The guards below re-run exactly that search on
`Multiset (ℕ × ℕ)` and confirm the count of defeats is `0`, with the population searched pinned
so the check cannot go vacuous. -/

section NumericGate

/-- The `(e, f)` pairs of degree `≤ 3` — the battery's alphabet. -/
private def efPairs : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (1, 3), (2, 1), (3, 1)]

/-- Types as multisets of `(e, f)` pairs, built from at most two letters. -/
private def smallTypes : List (Multiset (ℕ × ℕ)) :=
  (0 : Multiset (ℕ × ℕ)) :: efPairs.map (fun p => {p}) ++
    efPairs.flatMap fun p => efPairs.map fun r => (p ::ₘ {r})

/-- A DEFEAT: distinct `τ, τ'` merged by some cofactor `κ`. -/
private def defeats : List (Multiset (ℕ × ℕ) × Multiset (ℕ × ℕ) × Multiset (ℕ × ℕ)) :=
  (smallTypes.flatMap fun t => smallTypes.flatMap fun t' => smallTypes.map fun k => (t, t', k)).filter
    fun x => decide (x.1 ≠ x.2.1 ∧ x.1 + x.2.2 = x.2.1 + x.2.2)

-- the scan is non-vacuous: 31 types, 29791 triples searched
#guard smallTypes.length == 31
#guard (smallTypes.flatMap fun t => smallTypes.flatMap fun t' =>
  smallTypes.map fun k => (t, t', k)).length == 29791

-- and it finds nothing, exactly as PART 4 reports
#guard defeats.length == 0

-- the search WOULD find something if cancellation failed: distinct types with a common
-- cofactor really are distinct after adding it (the positive control)
#guard decide (({(1, 1)} : Multiset (ℕ × ℕ)) + {(2, 1)} ≠ ({(1, 2)} : Multiset (ℕ × ℕ)) + {(2, 1)})

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.exists_lift_mulClass
#print axioms Uniformity.Density.Induction.undecidedAt_of_two_types
#print axioms Uniformity.Density.Induction.exists_decidedAt_of_not_undecidedAt
#print axioms Uniformity.Density.Induction.undecidedAt_mulClass_of_left
#print axioms Uniformity.Density.Induction.undecidedAt_mulClass_of_right
#print axioms Uniformity.Density.Induction.undecidedAt_mulClass_iff

end AxCheck
