/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C53 — GENTOW-1(b): the fibration and the CLIPPED free count

**Chapter C, NODE C.53** [theorem] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §6, ~line 3361). ENV-C1. Two signed declarations,
transcribed BYTE-FROZEN from `leanspec/Leanspec/ChapC.lean`:

* `towerFreeCount T μ₂ N = ∑_{j<μ₂} ∑_{a<D′} ∑_{b<e₂f₂} (N − budgetFloor T μ₂ j a b)` — the
  **CLIP**, `ℕ`-subtraction being `max(0, ·)` definitionally (the R2a replacement; the sealed
  unclipped `Σ (N − floor)` is DEAD);
* `towerLocus_fibration` — the count of level-`N` coefficient classes that lift into the
  tower-entry locus `𝒯 = towerLocus T μ₂` (C.51) is `q ^ towerFreeCount T μ₂ N`.

## Landing status (honest)

* `towerFreeCount`: **LANDED**, byte-frozen.
* the CLIP arithmetic and the whole **box-count half** of the fibration: **LANDED** as
  `card_budgetBox` — the clipped product law at the three-index slot grid, Lean-core.
* `towerLocus_fibration`: **BLOCKED** — see `C53_BLOCKED_2026-08-20.md`. Its content is
  reduced, here and Lean-core, to the single frontier Prop `BudgetBoxRead` below: the
  statement that "lifts into `𝒯`" and "lifts into the budget box in the RAW coefficient
  coordinates" cut out the same set of level-`N` classes. That is C.52's
  `towerLocus_iff_budget` (BLOCKED, `C52_BLOCKED_2026-08-18.md`) composed with C.52 Step 3's
  triangular/unipotent digit dictionary (also unlanded — obstruction 4 of that record names
  this very file as the missing supplier).

## Overlap with the recent landings (checked before transcription)

* `C128.lean` / `C128b1.lean` / `C128b2.lean` (LAW B-S2, the P-BINOM cascade) carry
  `composedKey_trinomial` and the pinned-parameter attainment identities. NONE of them is the
  general two-key triangular dictionary, and none mentions `Coeff`, `proj`, `monicPoly` or
  `Nat.card`: no lemma there is consumable here, and nothing here re-proves anything there.
* `C52.lean` supplies `budgetFloor` (consumed by NAME, not re-declared) and
  `budgetFloor_le_iff`, `dev_pow_self` (the two landed step legs). The four legs C.52 records
  as BLOCKED are exactly the suppliers of the frontier below; this unit does not re-attempt
  them (route already documented dead at the dv-graded product law).
* `C110.lean`'s `ht_conservative_card` is the level-1 twin of `card_budgetBox` — but its
  floor function is hard-wired to the conservative shape `(a − i/d)·k + 1`, so it cannot be
  instantiated at `budgetFloor`. Its three valuation-counting helpers
  (`card_res_ge_of_le`, `card_res_ge_of_ge`, `card_res_ge`) ARE what this file needs and are
  `private` there, hence not importable. **Disclosure:** they are reproduced verbatim below as
  `private` lemmas of this file rather than by editing another unit's landed file. RE-PLAN
  candidate for the orchestrator: promote the cluster to `Uniformity/Density/LocalData.lean`
  and have both C.110 and C.53 consume it.

## MANDATORY A-C.7 five-instance vacuity audit — VERDICT: NO INSTANCE

Audited before any proof work, against the five-instance registry (C.111 `hnode` unpinned
carrier · C.94 self-loop · C.113 unconditional `hne` · C.118 clause-1 one-sided `≠ ⊤` guard ·
C.118 clause-2 unguarded consulted side data), plus A-C.8.4's low-degree-purity row.

**`towerFreeCount` (a def, no hypotheses).** The only degenerate strata are `μ₂ = 0` (empty
outer sum → count `0`) and the `N ≤ floor` slots (`ℕ`-subtraction → summand `0`). Both are
INTENDED and both are the R2a correction itself: the CLIP must be active, and `card_budgetBox`
below proves the count law holds on exactly those strata too (`residueCard ^ 0 = 1`, the single
zero class). The three ranges `Finset.range μ₂`, `range (F.e₁ * F.f₁)`, `range (T.e₂ * T.f₂)`
are inhabited whenever `0 < μ₂`, since `F.he₁`, `F.hf₁`, `T.he₂`, `T.hf₂` are structure fields
(and `T.hcomp : 2 ≤ T.e₂ * T.f₂` is strictly stronger for the inner one).

**`towerLocus_fibration`'s hypotheses.**

* **`hμ₂ : 0 < μ₂`** — excludes the degree-`0` stratum. It is NOT an implication guard, and
  the identity is in fact true at `μ₂ = 0` as well (both sides are `1`: the unique element of
  `Coeff O 0 N` lifts to `monicPoly` of the empty vector `= 1`, and `towerFreeCount T 0 N = 0`);
  so the hypothesis restricts, it does not rescue.
* **`hπ : Irreducible π`** — consumed by the valuation-count leg (`card_res_ge`); not inert.
* **`hh : 1 ≤ F.h`** — a regime hypothesis of §6 (the wrap-corrected composed key needs a
  nondegenerate frame); inherited from C.52's signature, not a guard.
* **`[IsAdicComplete …]`, `[Finite (ResidueField O)]`** — the second is *needed for the
  statement to typecheck at all* (`Coeff`, `residueCard`); the first is the scope hypothesis of
  the §6 chain. Neither is a one-sided guard.
* **the counted subtype** — the risk site, since `towerLocus` membership contains the
  ∀-quantified pin block `∀ (hne) (M₀) (hp), dvResPoly … = towerLabel ^ μ₂`, an A-C.113-shaped
  pattern. It BINDS on-locus: `IsDvPure F f T.u₂ T.e₂` is a CONJUNCT of the same membership and
  its first component is `0 ∈ dvSideSet F f T.u₂ T.e₂`, which inhabits `hne`; `DvOnSide`'s
  second component `dvHgt ≠ ⊤` then supplies a finite pin at `dvSideMin`, inhabiting `M₀`/`hp`.
  So the residual equation is never vacuously satisfied by an empty witness domain. (This is
  the identical verdict C.51's and C.52's headers record for the same block, reached
  independently here.)
* **the frontier `BudgetBoxRead`** — audited as a refutation target in its own right, per the
  standing lesson. It is an iff between two `∃`-statements over the SAME class `c`, so there is
  no one-sided guard; it cannot be satisfied vacuously by an empty domain (`proj` is surjective,
  `proj_surjective`, so every class has lifts); and it is not trivially true, since the RHS is a
  product box in the raw coordinates while the LHS is a polygon condition — the two agree only
  through the unipotent digit dictionary, which is precisely the unlanded content.

**DEPENDS.** C.42 (`TowerDatum`, `D₂`, `E₂`) · C.43 (`composedKey`) · C.50 (`slotOffset`) ·
C.51 (`towerLocus`) · C.52 (`budgetFloor`) — imported. `Uniformity/Density/LocalData.lean`
(`Coeff`, `Res`, `proj`, `monicPoly`, `residueCard`, `card_res`).

## Status

Sorry-free. Axiom footprint of every declaration below: Lean core
`{propext, Classical.choice, Quot.sound}` (AxCheck footer). No cite is inherited.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed definition (BYTE-FROZEN from `leanspec/Leanspec/ChapC.lean`) -/

/-- **NODE C.53's count — the CLIP.**  `∑_{j,a,b} max(0, N − budgetFloor T μ₂ j a b)`, the
`max(0, ·)` being `ℕ`-subtraction definitionally (`EFF.GENTOW1.16`'s R2a replacement; the
sealed unclipped exponent is false whenever `N < floor` at some slot and is DEAD). -/
noncomputable def towerFreeCount {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range μ₂, ∑ a ∈ Finset.range (F.e₁ * F.f₁),
    ∑ b ∈ Finset.range (T.e₂ * T.f₂), (N - budgetFloor T μ₂ j a b)

/-! ### Valuation bookkeeping in one coordinate

**Disclosure (see the header's overlap section):** the three lemmas of this subsection are a
verbatim reproduction of `C110.lean`'s `private` cluster `card_res_ge_of_le` /
`card_res_ge_of_ge` / `card_res_ge`.  They are `private` there, so they cannot be imported;
they are reproduced rather than promoted because promoting them means editing another unit's
landed file.  RE-PLAN candidate: move the cluster to `Uniformity/Density/LocalData.lean`. -/

private theorem le_addVal_iff_pow_dvd' (hπ : Irreducible π) (m : ℕ) (x : O) :
    ((m : ℕ) : ℕ∞) ≤ addVal O x ↔ π ^ m ∣ x := by
  rw [← hπ.addVal_pow m]
  exact addVal_le_iff_dvd

private theorem mem_pow_maximalIdeal_iff' (hπ : Irreducible π) (m : ℕ) (x : O) :
    x ∈ (IsLocalRing.maximalIdeal O) ^ m ↔ π ^ m ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- the CLIP branch: the bound lies at or beyond the window, so only the zero class survives. -/
private theorem card_res_ge_of_le' (hπ : Irreducible π) {N m : ℕ} (h : N ≤ m) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  have hzero : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r = 0 := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_maximalIdeal_iff' hπ]
      exact dvd_trans (pow_dvd_pow _ h) ((le_addVal_iff_pow_dvd' hπ m x).1 hx)
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  have hone : Nat.card {r : Res O N // r = 0} = 1 := by simp
  rw [Nat.sub_eq_zero_of_le h, pow_zero, ← hone]
  exact Nat.card_congr (Equiv.subtypeEquivRight hzero)

/-- the free branch: the classes with a lift of valuation `≥ m` are the range of
`x ↦ [x·π ^ m]`, whose kernel is `𝔪 ^ (N−m)`. -/
private theorem card_res_ge_of_ge' [Finite (ResidueField O)] (hπ : Irreducible π) {N m : ℕ}
    (h : m ≤ N) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  classical
  set μ : O →+ Res O N :=
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)).toAddMonoidHom.comp
      (AddMonoidHom.mulRight (π ^ m)) with hμ
  have hμ_apply : ∀ x : O, μ x = Ideal.Quotient.mk _ (x * π ^ m) := fun _ => rfl
  have hrange : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r ∈ Set.range μ := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      obtain ⟨y, rfl⟩ := (le_addVal_iff_pow_dvd' hπ m x).1 hx
      exact ⟨y, by rw [hμ_apply]; ring_nf⟩
    · rintro ⟨y, rfl⟩
      refine ⟨y * π ^ m, rfl, ?_⟩
      exact (le_addVal_iff_pow_dvd' hπ m _).2 ⟨y, by ring⟩
  have hker : μ.ker = ((IsLocalRing.maximalIdeal O) ^ (N - m)).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, hμ_apply, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_toAddSubgroup]
    rw [mem_pow_maximalIdeal_iff' hπ, mem_pow_maximalIdeal_iff' hπ]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hid : π ^ (N - m) * c * π ^ m = π ^ N * c := by
        rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]
      have hsplit : x * π ^ m = (π ^ (N - m) * c) * π ^ m := by rw [hid]; exact hc
      exact mul_right_cancel₀ (pow_ne_zero m hπ.ne_zero) hsplit
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]⟩
  have hcard : Nat.card (Set.range μ) = Nat.card (O ⧸ μ.ker) :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange μ).toEquiv).symm
  have hq : Nat.card (O ⧸ μ.ker) = residueCard O ^ (N - m) := by
    rw [hker]
    exact card_res (O := O) (N - m)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hrange), hcard, hq]

/-- **One coordinate, both branches.**  `#{r : O ⧸ 𝔪 ^ N | r lifts to valuation ≥ m}
= q ^ (N − m)`, the subtraction being the `ℕ`-CLIP. -/
private theorem card_res_ge' [Finite (ResidueField O)] (hπ : Irreducible π) (N m : ℕ) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  rcases le_total m N with h | h
  · exact card_res_ge_of_ge' hπ h
  · exact card_res_ge_of_le' hπ h

/-! ### The three-index slot grid

`n = μ₂·D₂` with `D₂ = D′·(e₂f₂)` (C.42), so the `n` scalar coefficient coordinates are in
bijection with the slot triples `(j, a, b)`, `j < μ₂`, `a < D′`, `b < e₂f₂`.  `slotDecode` is
that bijection, written as the division/remainder cascade, and `budgetSlot` is `budgetFloor`
read through it. -/

/-- the slot floor at the raw coefficient index `i`: decode `i = j·D₂ + b·D′ + a` and read
`budgetFloor` there. -/
def budgetSlot {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ i : ℕ) : ℕ :=
  budgetFloor T μ₂ (i / T.D₂) (i % T.D₂ % (F.e₁ * F.f₁)) (i % T.D₂ / (F.e₁ * F.f₁))

/-- `∑_{i < a·d} g (i / d) (i % d) = ∑_{j < a} ∑_{s < d} g j s` — the two-index regrouping of a
flat range, `C110.lean`'s `sum_range_mul_div` with the remainder kept. -/
private theorem sum_range_div_mod {d : ℕ} (hd : 0 < d) (g : ℕ → ℕ → ℕ) (a : ℕ) :
    ∑ i ∈ Finset.range (a * d), g (i / d) (i % d)
      = ∑ j ∈ Finset.range a, ∑ s ∈ Finset.range d, g j s := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hsplit : (a + 1) * d = a * d + d := by ring
    rw [hsplit, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < d := Finset.mem_range.1 hi
    have hdiv : (a * d + i) / d = a := by
      rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hi', Nat.add_zero]
    have hmod : (a * d + i) % d = i := by
      rw [Nat.mul_comm a d, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
    rw [hdiv, hmod]

/-- **The slot exponent IS `towerFreeCount`.**  Flattening the three-index sum over the slot
grid along `i ↦ (i / D₂, i % D₂ % D′, i % D₂ / D′)` reproduces the signed count. -/
theorem sum_budgetSlot {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) :
    ∑ i ∈ Finset.range (μ₂ * T.D₂), (N - budgetSlot T μ₂ i) = towerFreeCount T μ₂ N := by
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hE : 0 < T.e₂ * T.f₂ := Nat.mul_pos T.he₂ T.hf₂
  have hD₂ : 0 < T.D₂ := by
    rw [TowerDatum.D₂]; exact Nat.mul_pos hD hE
  -- outer split: `i ↦ (i / D₂, i % D₂)`
  have h1 : ∑ i ∈ Finset.range (μ₂ * T.D₂), (N - budgetSlot T μ₂ i)
      = ∑ j ∈ Finset.range μ₂, ∑ s ∈ Finset.range T.D₂,
          (N - budgetFloor T μ₂ j (s % (F.e₁ * F.f₁)) (s / (F.e₁ * F.f₁))) :=
    sum_range_div_mod hD₂
      (fun j s => N - budgetFloor T μ₂ j (s % (F.e₁ * F.f₁)) (s / (F.e₁ * F.f₁))) μ₂
  -- inner split: `s ↦ (s / D′, s % D′)` on `range ((e₂f₂)·D′)`
  have hcomm : T.D₂ = (T.e₂ * T.f₂) * (F.e₁ * F.f₁) := by
    rw [TowerDatum.D₂]; ring
  have h2 : ∀ j : ℕ, ∑ s ∈ Finset.range T.D₂,
        (N - budgetFloor T μ₂ j (s % (F.e₁ * F.f₁)) (s / (F.e₁ * F.f₁)))
      = ∑ b ∈ Finset.range (T.e₂ * T.f₂), ∑ a ∈ Finset.range (F.e₁ * F.f₁),
          (N - budgetFloor T μ₂ j a b) := by
    intro j
    rw [hcomm]
    exact sum_range_div_mod hD (fun b a => N - budgetFloor T μ₂ j a b) (T.e₂ * T.f₂)
  rw [h1, towerFreeCount]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 j]
  exact (Finset.sum_comm).symm

/-! ### The clipped box count -/

/-- **The box count law — the whole counting half of NODE C.53, LANDED.**

The level-`N` coefficient classes admitting an integral lift whose slot-`i` entry has valuation
at least `budgetSlot T μ₂ i` number exactly `q ^ towerFreeCount T μ₂ N`.  The exponent's
`ℕ`-subtraction is the R2a CLIP and it is definitionally active: the identity holds at EVERY
finite window `N`, including windows below some slot's floor, where that slot contributes the
single zero class (`q ^ 0 = 1`) rather than a negative exponent.

Three moves, as at C.110 clause 1: the lift may be chosen coordinatewise
(`Equiv.subtypePiEquivPi`), one coordinate counts `q ^ (N − floor)` (`card_res_ge'`), and the
product regroups along the slot grid (`sum_budgetSlot`). -/
theorem card_budgetBox [Finite (ResidueField O)] (hπ : Irreducible π)
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
          ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (a i)}
      = residueCard O ^ towerFreeCount T μ₂ N := by
  classical
  set R : Fin (μ₂ * T.D₂) → Res O N → Prop := fun i r =>
    ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O x with hR
  have hiff : ∀ c : Coeff O (μ₂ * T.D₂) N,
      (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
          ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (a i))
        ↔ ∀ i : Fin (μ₂ * T.D₂), R i (c i) := by
    intro c
    constructor
    · rintro ⟨a, ha, hval⟩ i
      exact ⟨a i, congrFun ha i, hval i⟩
    · intro h
      choose x hx hval using h
      exact ⟨x, funext hx, hval⟩
  have e2 : {c : Coeff O (μ₂ * T.D₂) N // ∀ i, R i (c i)}
      ≃ (∀ i : Fin (μ₂ * T.D₂), {r : Res O N // R i r}) := Equiv.subtypePiEquivPi
  have hstep : Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
          ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (a i)}
      = ∏ i : Fin (μ₂ * T.D₂), residueCard O ^ (N - budgetSlot T μ₂ i.1) := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans e2), Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => card_res_ge' hπ N (budgetSlot T μ₂ i.1)
  rw [hstep, Finset.prod_pow_eq_pow_sum, ← sum_budgetSlot T μ₂ N]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => N - budgetSlot T μ₂ i) (μ₂ * T.D₂)

/-! ### The frontier, isolated -/

/-- **`BudgetBoxRead T μ₂ N` — the exact remaining content of `towerLocus_fibration`.**

"Lifting into the tower-entry locus `𝒯`" and "lifting into the budget box in the RAW
coefficient coordinates" cut out the SAME level-`N` classes.  This Prop is the composite of

1. C.52's `towerLocus_iff_budget` (`f ∈ 𝒯 ↔ per-slot floors on the two-key development digits
   `(dev F.key (dev (composedKey T) f j) b).coeff a`) — BLOCKED, `C52_BLOCKED_2026-08-18.md`;
2. C.52 Step 3's triangular/unipotent dictionary (those digit bounds ↔ the same bounds on the
   raw coefficient vector at the decoded slot `j·D₂ + b·D′ + a`, the map being unipotent in the
   x-degree filtration hence measure-preserving mod `π ^ N`) — unlanded; obstruction 4 of the
   C.52 record names this file as its intended supplier.

Nothing weaker suffices: the count law `card_budgetBox` above is already sharp, so the whole
residual content of the signed theorem is this set equality. -/
def BudgetBoxRead [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) : Prop :=
  ∀ c : Coeff O (μ₂ * T.D₂) N,
    (∃ a : Fin (μ₂ * T.D₂) → O,
        proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂)
      ↔ (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
          ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (a i))

/-- **Leg 1 of the frontier — C.52's signed characterization**, as a Prop to be threaded (the
leanspec stub `towerLocus_iff_budget`, BLOCKED at `C52_BLOCKED_2026-08-18.md`): membership in
`𝒯` is the conjunction of per-slot `addVal` floors on the TWO-KEY development digits
`(dev F.key (dev (composedKey T) f j) b).coeff a`. -/
def TowerBudgetIff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) : Prop :=
  ∀ f : Polynomial O, f.Monic → f.natDegree = μ₂ * T.D₂ →
    (f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a))

/-- **Leg 2 of the frontier — C.52 Step 3's unipotent digit dictionary**, as a Prop: at a fixed
window `N`, having a lift whose TWO-KEY digits clear the floors is the same as having a lift
whose RAW coefficients clear the same floors at the decoded slots.  This is the only place where
"triangular-unimodular" is used, and it is used exactly as a measure-preservation statement:
`c_{j,a,b}` is the coefficient at degree `j·D₂ + b·D′ + a` plus an `O`-combination of strictly
higher-degree coefficients, so the change of coordinates is unipotent in the x-degree filtration
and therefore a bijection of the level-`N` box onto itself. UNLANDED (obstruction 4 of
`C52_BLOCKED_2026-08-18.md`). -/
def TriangularDigitRead [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) : Prop :=
  ∀ c : Coeff O (μ₂ * T.D₂) N,
    (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
        ∀ j a' b : ℕ, j < μ₂ → a' < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a' b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) (monicPoly a) j) b).coeff a'))
      ↔ (∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
          ∀ i : Fin (μ₂ * T.D₂), ((budgetSlot T μ₂ i.1 : ℕ) : ℕ∞) ≤ addVal O (a i))

/-- **The frontier splits into exactly those two legs.**  `monicPoly` supplies C.52's two side
conditions for free (`monicPoly_monic`, `monicPoly_natDegree`), so leg 1 rewrites the locus
membership into digit floors class by class and leg 2 transports them to the raw coordinates. -/
theorem budgetBoxRead_of_legs [Finite (ResidueField O)] {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ)
    (h1 : TowerBudgetIff T μ₂) (h2 : TriangularDigitRead T μ₂ N) :
    BudgetBoxRead T μ₂ N := by
  intro c
  refine Iff.trans ?_ (h2 c)
  constructor
  · rintro ⟨a, ha, hmem⟩
    exact ⟨a, ha, (h1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).1 hmem⟩
  · rintro ⟨a, ha, hbud⟩
    exact ⟨a, ha, (h1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).2 hbud⟩

/-- **NODE C.53, from the frontier alone (Lean-core).**  The full signed conclusion of
`towerLocus_fibration` follows from `BudgetBoxRead` and the landed `card_budgetBox`; so the
missing content of the signed theorem is EXACTLY the frontier Prop.  The signed hypotheses
`hh` and `hμ₂` are not consumed by the reduction — the count law is uniform in them, which is
itself part of the R2a finding (the clip, not a positivity side condition, is what makes the
formula correct at small `N`). -/
theorem towerLocus_fibration_of_frontier [Finite (ResidueField O)] (hπ : Irreducible π)
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ)
    (hfr : BudgetBoxRead T μ₂ N) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O,
          proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂}
      = residueCard O ^ towerFreeCount T μ₂ N := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfr)]
  exact card_budgetBox hπ T μ₂ N

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerFreeCount
#print axioms Uniformity.Density.Tower.budgetSlot
#print axioms Uniformity.Density.Tower.sum_budgetSlot
#print axioms Uniformity.Density.Tower.card_budgetBox
#print axioms Uniformity.Density.Tower.BudgetBoxRead
#print axioms Uniformity.Density.Tower.TowerBudgetIff
#print axioms Uniformity.Density.Tower.TriangularDigitRead
#print axioms Uniformity.Density.Tower.budgetBoxRead_of_legs
#print axioms Uniformity.Density.Tower.towerLocus_fibration_of_frontier

end AxCheck
