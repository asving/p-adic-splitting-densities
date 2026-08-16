/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H107 — the windowed (conservative) valuation on `Res O N`

**Chapter H, NODE H.107** (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1 completion
layer, dated extension 2026-08-16; provenance OM-2 §3.2's reader carrier, source
`EFF.GENIND.07`).  Second node of **N-2**, the cluster event grammar over `O`.

`resOrd x`, for `x : Res O N`, is the largest `k ≤ N` with `x` in the image of `𝔪 ^ k`.  It is
the **CONSERVATIVE** valuation of the S-1 reader: `resOrd x = N` means the coefficient is
INVISIBLE in the window (`x = 0` there), *never* "the valuation is exactly `N`".  Nothing below
consults a lift's true valuation; every clause is a statement about the class.

* `resOrd_ge_iff` (clause i) — representative transport: for `k ≤ N`,
  `k ≤ resOrd (mk a) ↔ π ^ k ∣ a`;
* `resOrd_eq_iff` (clause ii) — invisibility: `resOrd x = N ↔ x = 0`.

Three auxiliaries are exported because the rest of §17 reads them constantly (H.108's capped
content needs `resOrd_le` together with clause (ii) to get its `≤ N − 1` on non-drain states):

* `resOrd_spec` — `resOrd x` is itself a member of the defining set (`Nat.sSup_mem`);
* `resOrd_le` — `resOrd x ≤ N`, the window cap;
* `le_resOrd_iff` — the class-level form of clause (i): for `k ≤ N`,
  `k ≤ resOrd x ↔ x ∈ image (𝔪 ^ k)`;
* `mk_mem_map_pow_iff` — the representative transport of the image ideal itself.

**Why the divisibility characterization is re-derived here.**  The landed
`mem_maximalIdeal_pow_iff_dvd` (`Uniformity/Density/Drainage.lean:635`) proves exactly
`a ∈ 𝔪 ^ k ↔ π ^ k ∣ a`, but its binder list carries `[Finite (ResidueField O)]` (section
auto-inclusion of an instance whose type mentions `O`, not a mathematical need — its proof is
three ideal rewrites).  H.107's SIGNATURE is frozen WITHOUT that instance, and adding it would
weaken the node, so `mem_maximalIdeal_pow_iff_dvd_of_irr` below reproves the same statement in
the frozen environment with the landed proof verbatim.  The `example` at the end of §1 pins the
two statements together: it discharges the re-derived proposition *by the landed lemma* under
the extra instance, so any future drift in either shape becomes a build error.

DEPENDS: landed `Res` (`Uniformity/Density/LocalData.lean`), `mem_maximalIdeal_pow_iff_dvd`
(`Uniformity/Density/Drainage.lean`, statement-pinned; see above) · mathlib `Nat.sSup_mem`,
`le_csSup`, `Ideal.mem_map_iff_of_surjective`, `Ideal.map_quotient_self`,
`Irreducible.maximalIdeal_eq`.

## TEETH (GC-8)

The node's TEETH are *implicit* in every PART-1 check of
`verification/openmath/OM2_genindb_battery.py`: `RB.val` capped at the window is the battery's
own reader carrier, and every bucket read of every cell consumes it, so there is no separate
numeric cell to reproduce as a `#guard` (contrast H.106, whose TEETH are the cell inventories
themselves).  What the battery certifies about it is the *class-determinedness* that makes
CC-2(iv)'s both-ring equality possible; the Lean statements of that determinedness are exactly
clauses (i) and (ii) here, both now proved.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The image ideals `𝔪 ^ k / 𝔪 ^ N`, and divisibility -/

/-- **Representative transport for the image ideal.** For `k ≤ N`, the class of `a` lies in the
image of `𝔪 ^ k` exactly when `a` does.  (Forward: a witness `b ∈ 𝔪 ^ k` with `mk b = mk a`
only gives `b − a ∈ 𝔪 ^ N`, and `𝔪 ^ N ≤ 𝔪 ^ k` closes it — this is where `k ≤ N` is used, and
it is the reason `resOrd` is capped at the window.) -/
theorem mk_mem_map_pow_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N k : ℕ} (hk : k ≤ N) (a : O) :
    (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) ∈
        ((maximalIdeal O) ^ k).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      ↔ a ∈ (maximalIdeal O) ^ k := by
  constructor
  · intro hmem
    obtain ⟨b, hb, hba⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
    have hd : b - a ∈ (maximalIdeal O) ^ N := Ideal.Quotient.eq.1 hba
    have hrw : a = b - (b - a) := by ring
    rw [hrw]
    exact Ideal.sub_mem _ hb (Ideal.pow_le_pow_right hk hd)
  · intro ha
    exact Ideal.mem_map_of_mem _ ha

/-- **`a ∈ 𝔪 ^ k ↔ π ^ k ∣ a`**, in H.107's frozen environment (no `[Finite]`); the landed
`mem_maximalIdeal_pow_iff_dvd`'s proof, verbatim.  See the file header for why it is reproved
rather than cited. -/
theorem mem_maximalIdeal_pow_iff_dvd_of_irr {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) (k : ℕ) (a : O) :
    a ∈ (maximalIdeal O) ^ k ↔ π ^ k ∣ a := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- **The statement pin.** Under the landed lemma's extra `[Finite (ResidueField O)]` the
re-derived proposition IS the landed one — discharged by it, so a drift in either shape breaks
the build. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) (k : ℕ) (a : O) :
    a ∈ (maximalIdeal O) ^ k ↔ π ^ k ∣ a :=
  mem_maximalIdeal_pow_iff_dvd hπ k a

/-! ## 2. The windowed valuation -/

/-- **H.107 (def half). The windowed (conservative) valuation** of a truncated element: the
largest `k ≤ N` with `x` in the image of `𝔪 ^ k`.  `resOrd x = N` means INVISIBLE (`x = 0` in
the window), never "valuation `= N`". -/
noncomputable def resOrd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) : ℕ :=
  sSup {k | k ≤ N ∧ x ∈ ((maximalIdeal O) ^ k).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}

/-- **The `sSup` is attained.** The defining set contains `0` (the image of `𝔪 ^ 0 = ⊤` is
everything) and is bounded by `N`, so `Nat.sSup_mem` puts `resOrd x` in it. -/
theorem resOrd_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) :
    resOrd x ≤ N ∧
      x ∈ ((maximalIdeal O) ^ (resOrd x)).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  exact Nat.sSup_mem
    (s := {k | k ≤ N ∧
      x ∈ ((maximalIdeal O) ^ k).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))})
    ⟨0, Nat.zero_le N, by simp [Ideal.one_eq_top, Ideal.map_top]⟩
    ⟨N, fun k hk => hk.1⟩

/-- **The window cap.** `resOrd` never exceeds `N`: the reader sees `N` digits and no more. -/
theorem resOrd_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) : resOrd x ≤ N :=
  (resOrd_spec x).1

/-- **The class-level form of clause (i).** For `k ≤ N`, `k ≤ resOrd x` is membership of the
image ideal at `k` — the defining set is downward closed because `𝔪 ^ k' ≤ 𝔪 ^ k` for
`k ≤ k'`. -/
theorem le_resOrd_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N k : ℕ} (hk : k ≤ N) (x : Res O N) :
    k ≤ resOrd x ↔
      x ∈ ((maximalIdeal O) ^ k).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  constructor
  · intro h
    exact Ideal.map_mono (Ideal.pow_le_pow_right h) (resOrd_spec x).2
  · intro hx
    exact le_csSup ⟨N, fun j hj => hj.1⟩ ⟨hk, hx⟩

/-! ## 3. The two clauses -/

/-- **H.107 (lemma half, clause i). Representative transport.** For `k ≤ N`,
`k ≤ resOrd (mk a) ↔ π ^ k ∣ a`. -/
theorem resOrd_ge_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k ≤ N) (a : O) :
    k ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) ↔ π ^ k ∣ a := by
  rw [le_resOrd_iff hk, mk_mem_map_pow_iff hk, mem_maximalIdeal_pow_iff_dvd_of_irr hπ]

/-- **H.107 (lemma half, clause ii). Invisibility.** `resOrd x = N ↔ x = 0`: the top value of
the windowed valuation is the reader's "I see nothing here", not a valuation claim. -/
theorem resOrd_eq_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) : resOrd x = N ↔ x = 0 := by
  constructor
  · intro h
    have hx : x ∈ ((maximalIdeal O) ^ N).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) :=
      (le_resOrd_iff le_rfl x).1 (le_of_eq h.symm)
    rw [Ideal.map_quotient_self] at hx
    simpa using hx
  · rintro rfl
    exact le_antisymm (resOrd_le _) ((le_resOrd_iff le_rfl (0 : Res O N)).2 (Ideal.zero_mem _))

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.mk_mem_map_pow_iff
#print axioms Uniformity.Density.Induction.mem_maximalIdeal_pow_iff_dvd_of_irr
#print axioms Uniformity.Density.Induction.resOrd_spec
#print axioms Uniformity.Density.Induction.resOrd_le
#print axioms Uniformity.Density.Induction.le_resOrd_iff
#print axioms Uniformity.Density.Induction.resOrd_ge_iff
#print axioms Uniformity.Density.Induction.resOrd_eq_iff

end AxCheck
