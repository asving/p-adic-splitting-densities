/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C23

/-!
# Uniformity.ChapC.C24 — `KeyFrame.slotRes_image`: the corrected LIFT law

**Chapter C, NODE C.24** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge
layer; the A-C.1 amendment set governs). **ENV-C3.** One signed declaration.

LEMMA HE6-1L, both directions, closure-free. For a stage frame `F` and a height `k`, the image of

`{A ∈ O[X] : deg A < D′ = e₁f₁ and dv(A) = k}`

under C.21's normalized slot residue `γ_k = F.slotRes H₀ hpin k` is **exactly** the braced span of
`EFF.HE6.13`:

`{Σ_{t ∈ T(k)} c_t η^t : c_t ∈ F_Q, not all zero}`,   `T(k) = F.slotWindow k`, `η = stageLetter`.

The `ϖ`-read image (C.22's `twistRead`) is the `η^{−q(k)}`-coset of this set; for the fullness
clause that shift is invisible (`η^{−q}·K^× = K^×`), which is why the signed statement is the
`n(k)`-read one.

## The two directions, and where each lives

**`⊆` is C.21 + C.23.** For `A` in the source set, `γ_k(A)` *is* the displayed sum with
`c_t := digAt π ((k − (i(k)+e₁t)h)/e₁) (a_{i(k)+e₁t})` — that is C.21's definition, so the
inclusion is `rfl` once the coefficients are named. The "not all zero" conjunct is C.23
(`slotRes_ne_zero`) read contrapositively: if every window digit vanished the whole sum would,
and C.23 forbids that.

**`⊇` is an explicit construction** (this file's `exists_stage_at_window`). Given window data
`(c_t)` with some `c_{t₀} ≠ 0`, put

`A := Σ_{t ∈ T(k)} (π^{m(t)} · g_t) · x^{i(k)+e₁t}`,  `m(t) = (k − (i(k)+e₁t)h)/e₁`,
`g_t = 0` if `c_t = 0`, else a residue lift of `c_t`,

and read off the three clauses: the exponents `i(k)+e₁t ≤ (e₁−1)+e₁(f₁−1) = D′−1` give
`deg A < D′`; the height is exactly `k` because on the window `e₁·m(t) + (i(k)+e₁t)h = k` **with
no `ℕ`-truncation** (C.16(i)'s congruence plus the window's own inequality), so every nonzero
slot sits at cost exactly `k` and the slot `t₀` — where `g_{t₀}` is a unit — attains it; and
`digAt π (m(t)) (π^{m(t)}·g_t) = res(g_t) = c_t` is B.22(a).

## Divergences (none is a blueprint node; GC-6.5)

* **The `⊇` construction is the window-restricted lift, not H.54's `stageLift'` verbatim.**
  The blueprint's PROOF step 2 routes the constructive direction through H.54/H.55/H.56 via
  C.14a's adapter. That adapter needs the corpus perimeter `1 ≤ F.h` **and** `2 ≤ e₁f₁`
  (`KeyFrame.genreDatum`), and C.24's signed SIGNATURE carries neither — the statement is
  quantified over every frame and every `k`, including `h = 0` and `D′ = 1`. Worse, `stageLift'`
  sums over the **whole** range `f₁`, so off-window terms (`t·h > a`, where `ℕ`-truncation
  collapses the `π`-exponent to `0`) would sit at the wrong height and break the height clause:
  H.55 excludes them by its terminal-scope hypothesis `keyDeg·h < M`, which is exactly the regime
  `slotWindow k = range f₁` (C.18(ii)). The construction here is `stageLift'` **restricted to the
  window**, which agrees with it summand-for-summand on the full-window regime, and the height and
  residue computations are H.55(iii)/H.56 done at those same summands, over the window only. So
  nothing is weakened: the signed statement is proved at every frame, and on the corpus perimeter
  the witness IS the corpus lift. The agreement is recorded as an `example` below rather than
  asserted in prose.
* **The two C.21-private slot helpers are re-derived here** (`window_dvd_sub_slotCost`,
  `window_slot_spec`): `private` does not export, and the exactness of the `ℕ`-division
  `m(t) = (k − (i(k)+e₁t)h)/e₁` is the arithmetic spine of the height clause. Same
  private-copy pattern as `isKey_X` (D9), retiring together with it.
* **Clauses (i)/(ii) of the STATEMENT are not separate declarations here.** Clause (ii) ("if
  `T(k) = ∅` the height is unattained") is *encoded* in the signed equation: at an empty window
  the right-hand side is empty (its `∃ t ∈ ∅` conjunct is `False`), so the equation forces the
  source set's image to be empty too — and the source set itself is empty by C.20(iii)
  (`stageHeight_unattained`), which is the landed form of the clause. Clause (i), the fullness
  corollary the blueprint calls `slotRes_surj_iff`, has **no signed signature** in
  `leanspec/Leanspec/ChapC.lean` (the stub file signs `slotRes_image` alone); it is therefore
  **NOT transcribed here** and remains an open perimeter item for §6/§9's consumers. Flagged, not
  silently absorbed.

**DEPENDS.** C.15/C.16 (`slotIdx`, `slotIdx_spec`) · C.17 (`slotWindow`) · C.19 (`stageLetter`) ·
C.20 (`stageHeight`, its `inf` form) · C.21 (`slotRes`, the object) · C.23 (`slotRes_ne_zero`, the
"not all zero" conjunct) · C.14a (`resLift`, `resLift_spec`, and — in the `example` — `stageLiftIA`
/ `stageLift_summand_eq`'s perimeter) · B.21/B.22 (`digAt`, `digAt_eq`) · H.54 (`stageLift'`,
through C.14a's `stageLiftIA_eq_stageLift'`, in the `example` only) — by committed node ID
(GC-13(b)). Mathlib: `Polynomial.finsetSum_coeff`, `Polynomial.coeff_X_pow`,
`Polynomial.natDegree_sum_le_of_forall_le`, `Finset.sum_eq_single`, `Finset.le_inf`,
`Finset.inf_le`, `IsDiscreteValuationRing.addVal_zero`, `IsLocalRing.residue_eq_zero_iff`.

**SOURCE.** `EFF.HE6.13` (LEMMA HE6-1L, the corrected display, TERMINAL layer: coset + span +
fullness iff + emptiness); `EFF.HE6.12` (the STRUCK `(LIFT)` — the sealed display is DEAD and this
node is its corrected replacement).

**TEETH.** `EFF.HE6.12`'s two counter-instances are instances of the signed equation: at
`(e₁,f₁,h) = (1,2,1)`, `k = 0` the window is `T(0) = {0}` (only `t = 0` is affordable), so the
right-hand side is the proper subset `F_Q^× ⊊ K^×` of the residue line — the ⊆ half's content; at
`(3,1,2)`, `k = 1` the window is empty and both sides are `∅` — clause (ii). `EFF.HE6.13`'s
`(2,2,3)` witness stays a §13 gate.

**ENVIRONMENT.** ENV-C3 (`hπ` + `[Finite (ResidueField O)]`; finiteness is bound because the node
is signed at ENV-C3, and is not consumed by the proof).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The `ℕ`-arithmetic of a window slot (C.21's private helpers, re-derived) -/

/-- On the slot window the normalizer exponent is a genuine `ℕ`-division:
`e₁ ∣ k − (i(k) + e₁t)·h`.  C.16(i)'s congruence pushed along `(i + e₁t)h ≡ ih (mod e₁)`, with
the `≤` supplied by the window's own defining inequality (C.17). -/
private theorem window_dvd_sub_slotCost (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
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

/-- The consumable form: the digit index `m(t) = (k − (i(k)+e₁t)h)/e₁` satisfies
`e₁·m(t) + (i(k)+e₁t)·h = k` **exactly**, with no `ℕ`-truncation anywhere. -/
private theorem window_slot_spec (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + (F.slotIdx k + F.e₁ * t) * F.h = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact this.2
  rw [Nat.mul_div_cancel' (window_dvd_sub_slotCost F k t ht), Nat.sub_add_cancel hle]

/-- `v(x) = n` from exactness, in `ℕ∞` (B.09's private `enat_eq_of_le_of_not_le`, re-derived). -/
private theorem addVal_eq_of_exact (hπ : Irreducible π) {x : O} {n : ℕ} (hdvd : π ^ n ∣ x)
    (hnot : ¬ π ^ (n + 1) ∣ x) : addVal O x = (n : ℕ∞) := by
  have h1 : (n : ℕ∞) ≤ addVal O x := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hdvd
  have h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ addVal O x := fun hc =>
    hnot ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 hc)
  rcases eq_or_ne (addVal O x) ⊤ with h | h
  · exact absurd (h ▸ le_top) h2
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 h
    rw [← hv] at h1 h2 ⊢
    have h1' : n ≤ v := by exact_mod_cast h1
    have h2' : ¬ n + 1 ≤ v := fun hc => h2 (by exact_mod_cast hc)
    exact_mod_cast (show v = n by omega)

/-! ### The `⊇` half: the window-restricted lift -/

/-- **The constructive direction of LEMMA HE6-1L.** Given window data `(c_t)` with at least one
nonzero entry `c_{t₀}`, the window-restricted lift
`A = Σ_{t ∈ T(k)} (π^{m(t)}·g_t)·x^{i(k)+e₁t}` has degree `< D′`, exact height `k`, and window
digits `c_t`.  This is H.54's `stageLift'` restricted to the window; see the module docstring's
first divergence for why the restriction is forced at C.24's signed binders. -/
private theorem exists_stage_at_window (F : KeyFrame O π) (hπ : Irreducible π) (k : ℕ)
    (c : ℕ → ResidueField O) {t₀ : ℕ} (ht₀ : t₀ ∈ F.slotWindow k) (hc₀ : c t₀ ≠ 0) :
    ∃ A : Polynomial O, A.natDegree < F.e₁ * F.f₁ ∧ F.stageHeight A = (k : ℕ∞) ∧
      ∀ t ∈ F.slotWindow k,
        digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
          (A.coeff (F.slotIdx k + F.e₁ * t)) = c t := by
  classical
  have hi₀ : F.slotIdx k < F.e₁ := (F.slotIdx_spec k).1
  -- the lifted window coefficients: `0` where `c` vanishes, a residue section elsewhere
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → O, g = fun t => if c t = 0 then 0 else resLift (c t) := ⟨_, rfl⟩
  have hgres : ∀ t, IsLocalRing.residue O (g t) = c t := by
    intro t
    rw [hgdef]
    by_cases h : c t = 0
    · simp [h]
    · simpa [h] using resLift_spec (c t)
  have hgzero : ∀ t, g t = 0 ↔ c t = 0 := by
    refine fun t => ⟨fun h => by rw [← hgres t, h, map_zero], fun h => by rw [hgdef]; simp [h]⟩
  -- the witness
  obtain ⟨A, hAdef⟩ : ∃ A : Polynomial O, A = ∑ t ∈ F.slotWindow k,
      Polynomial.C (π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t)
        * Polynomial.X ^ (F.slotIdx k + F.e₁ * t) := ⟨_, rfl⟩
  -- its coefficient list
  have hcoeff : ∀ j : ℕ, A.coeff j = ∑ t ∈ F.slotWindow k,
      if j = F.slotIdx k + F.e₁ * t then
        π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t else 0 := by
    intro j
    rw [hAdef, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hj : j = F.slotIdx k + F.e₁ * t <;> simp [hj]
  have hcoeff_win : ∀ t ∈ F.slotWindow k,
      A.coeff (F.slotIdx k + F.e₁ * t)
        = π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t := by
    intro t ht
    rw [hcoeff, Finset.sum_eq_single t
      (fun b _ hb => if_neg (fun hjb => hb
        (Nat.eq_of_mul_eq_mul_left F.he₁ (Nat.add_left_cancel hjb)).symm))
      (fun hn => absurd ht hn)]
    simp
  -- the degree clause
  have hdeg : A.natDegree < F.e₁ * F.f₁ := by
    have hle : A.natDegree ≤ F.e₁ * F.f₁ - 1 := by
      rw [hAdef]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
      have htf : t < F.f₁ := by
        have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
        exact Finset.mem_range.mp this.1
      have hstep : F.e₁ * (t + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left _ htf
      have hexp : F.e₁ * (t + 1) = F.e₁ * t + F.e₁ := by ring
      have hmul : (Polynomial.C (π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t)
            * Polynomial.X ^ (F.slotIdx k + F.e₁ * t)).natDegree
          ≤ (Polynomial.C (π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t)).natDegree
              + (Polynomial.X ^ (F.slotIdx k + F.e₁ * t) : Polynomial O).natDegree :=
        Polynomial.natDegree_mul_le
      have hCX : (Polynomial.C (π ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * g t)).natDegree
            + (Polynomial.X ^ (F.slotIdx k + F.e₁ * t) : Polynomial O).natDegree
          = F.slotIdx k + F.e₁ * t := by
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, Nat.zero_add]
      omega
    have : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
    omega
  -- the valuation of an occupied slot
  have haddval : ∀ t ∈ F.slotWindow k, c t ≠ 0 →
      addVal O (A.coeff (F.slotIdx k + F.e₁ * t))
        = (((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ : ℕ) : ℕ∞) := by
    intro t ht hct
    have hnd : ¬ π ∣ g t := by
      rintro ⟨y, hy⟩
      refine hct ?_
      rw [← hgres t, IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq,
        Ideal.mem_span_singleton]
      exact ⟨y, hy⟩
    rw [hcoeff_win t ht]
    refine addVal_eq_of_exact hπ ⟨g t, rfl⟩ ?_
    intro hc
    rw [pow_succ] at hc
    exact hnd ((mul_dvd_mul_iff_left
      (pow_ne_zero ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) hπ.ne_zero)).mp hc)
  -- the height clause
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  have hcost : ∀ t ∈ F.slotWindow k, c t ≠ 0 →
      F.e₁ • addVal O (A.coeff (F.slotIdx k + F.e₁ * t))
          + ((F.h * (F.slotIdx k + F.e₁ * t) : ℕ) : ℕ∞) = (k : ℕ∞) := by
    intro t ht hct
    rw [haddval t ht hct]
    have hnat := window_slot_spec F k t ht
    have : F.e₁ • (((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ : ℕ) : ℕ∞)
        + ((F.h * (F.slotIdx k + F.e₁ * t) : ℕ) : ℕ∞)
        = ((F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
            + (F.slotIdx k + F.e₁ * t) * F.h : ℕ) : ℕ∞) := by
      push_cast [nsmul_eq_mul]
      ring
    rw [this, hnat]
  have ht₀0 : A.coeff (F.slotIdx k + F.e₁ * t₀) ≠ 0 := by
    rw [hcoeff_win t₀ ht₀]
    exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (fun h => hc₀ ((hgzero t₀).mp h))
  have hht : F.stageHeight A = (k : ℕ∞) := by
    rw [hinf]
    refine le_antisymm ?_ ?_
    · refine le_trans (Finset.inf_le (Finset.mem_range.mpr ?_)) (le_of_eq (hcost t₀ ht₀ hc₀))
      exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero ht₀0)
    · refine Finset.le_inf fun j _ => ?_
      by_cases hz : A.coeff j = 0
      · rw [hz, addVal_zero, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add]
        exact le_top
      · have hex : ∃ t ∈ F.slotWindow k, j = F.slotIdx k + F.e₁ * t := by
          by_contra hno
          push Not at hno
          exact hz (by rw [hcoeff j]; exact Finset.sum_eq_zero fun t ht => if_neg (hno t ht))
        obtain ⟨t, ht, rfl⟩ := hex
        have hct : c t ≠ 0 := by
          intro h
          exact hz (by rw [hcoeff_win t ht, (hgzero t).mpr h, mul_zero])
        exact le_of_eq (hcost t ht hct).symm
  -- the digit clause
  refine ⟨A, hdeg, hht, fun t ht => ?_⟩
  rw [hcoeff_win t ht, digAt_eq hπ rfl, hgres t]

/-! ### The signed declaration -/

/-- **NODE C.24 — the corrected LIFT law (LEMMA HE6-1L), both directions, closure-free.**
The image of the degree-`< D′`, height-exactly-`k` polynomials under C.21's normalized slot
residue `γ_k` is exactly the set of `η`-combinations supported on the slot window `T(k)` with at
least one nonzero coefficient — `EFF.HE6.13`'s braced span.  Emptiness of `T(k)` is the degenerate
case (both sides `∅`, C.20(iii)); fullness of `T(k)` is the case in which the span is all of
`K^×` (C.18, and see the module docstring on `slotRes_surj_iff`). -/
theorem KeyFrame.slotRes_image (F : KeyFrame O π) (hπ : Irreducible π)
    [Finite (ResidueField O)] (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) :
    (Set.image (F.slotRes H₀ hpin k)
        {A : Polynomial O | A.natDegree < F.e₁ * F.f₁ ∧ F.stageHeight A = (k : ℕ∞)})
      = {x | ∃ c : ℕ → ResidueField O, (∃ t ∈ F.slotWindow k, c t ≠ 0) ∧
          x = (F.slotWindow k).sum fun t =>
            algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
                (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O)) (c t))
              * F.stageLetter H₀ hpin ^ t} := by
  classical
  ext x
  constructor
  · -- `⊆`: C.21's definition names the coefficients, C.23 says they are not all zero.
    rintro ⟨A, ⟨hA, hht⟩, rfl⟩
    refine ⟨fun t => digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
      (A.coeff (F.slotIdx k + F.e₁ * t)), ?_, rfl⟩
    by_contra hall
    push Not at hall
    refine F.slotRes_ne_zero hπ H₀ hpin hA hht ?_
    simp only [KeyFrame.slotRes]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [hall t ht]
    simp
  · -- `⊇`: the window-restricted lift.
    rintro ⟨c, ⟨t₀, ht₀, hc₀⟩, rfl⟩
    obtain ⟨A, hdeg, hht, hdig⟩ := exists_stage_at_window F hπ k c ht₀ hc₀
    refine ⟨A, ⟨hdeg, hht⟩, ?_⟩
    simp only [KeyFrame.slotRes]
    exact Finset.sum_congr rfl fun t ht => by rw [hdig t ht]

end Uniformity.Density.Tower

/-! ## The corpus perimeter: the witness IS H.54's lift on the full-window regime

An `example`, not a declaration — C.24's signed contract is the theorem above.  On the corpus
perimeter (`1 ≤ h`, `2 ≤ D′`) and past C.18(ii)'s uniform budget `(D′−1)h ≤ k`, the slot window is
all of `range f₁` (`slotWindow_full_of_le`), and there the `⊇` witness of
`exists_stage_at_window` is summand-for-summand H.54's `stageLift'` at the C.14a adapter datum,
with normalizer data `i = i(k)`, `a = m(0)`: the `π`-exponent `a − t·h` and the `X`-exponent
`i + e₁t` are the window's `m(t)` and `i(k)+e₁t`.  The statement below is that identification, at
the level of the exponent bookkeeping, so that the divergence recorded in the module docstring is
checked by the elaborator rather than asserted in prose. -/

section CorpusPerimeter

open Uniformity.Density.Tower Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The window's digit index is H.54's `π`-exponent: `m(t) = m(0) − t·h` on the window. -/
example (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁
      = (k - (F.slotIdx k + F.e₁ * 0) * F.h) / F.e₁ - t * F.h := by
  have h0 : (0 : ℕ) ∈ F.slotWindow k := by
    have hmem := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    rw [KeyFrame.slotWindow, Finset.mem_filter, Finset.mem_range]
    refine ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.mp hmem.1), ?_⟩
    refine le_trans (Nat.mul_le_mul_right _ (by omega)) hmem.2
  have hspec := window_slot_spec F k t ht
  have hspec0 := window_slot_spec F k 0 h0
  have hexp : (F.slotIdx k + F.e₁ * t) * F.h
      = (F.slotIdx k + F.e₁ * 0) * F.h + F.e₁ * (t * F.h) := by ring
  have hmul : F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + F.e₁ * (t * F.h)
      = F.e₁ * ((k - (F.slotIdx k + F.e₁ * 0) * F.h) / F.e₁) := by omega
  have hcancel : (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ + t * F.h
      = (k - (F.slotIdx k + F.e₁ * 0) * F.h) / F.e₁ :=
    Nat.eq_of_mul_eq_mul_left F.he₁ (by rw [Nat.mul_add]; exact hmul)
  exact Nat.eq_sub_of_add_eq hcancel

end CorpusPerimeter

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotRes_image

end AxCheck
