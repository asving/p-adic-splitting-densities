/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.ResidualPolynomial

/-!
# Order0Hull — the γ1 flat-hull gate (HNODE0_BLUEPRINT §1)

**Target (γ1).** For a support `S : Finset (ℕ × ℕ)` containing `(0, 0)` and `(n, 0)` with every
abscissa `≤ n` (and `0 < n`), the Newton-polygon side list is the single flat side:
`npSides S hS = [⟨0, n, 0, 0⟩]`. This is the hull computation backing
`classify p n N f = sepShape n λ(f̄)` on the generic (unit-constant-coefficient) stratum: the
valuation support of such an `f` is flat, so the polygon has exactly one side, the flat one.

Proof route (each node a lemma, all against the BANKED `LeanUrat.OM.NewtonPolygon` primitives):
1. `npHeight_flat` — the chord `((0,0), (n,0))` is a valid supporting line (all dot heights are
   `ℕ`-casts, hence `≥ 0`), so the breakpoint lemma `npHeight_eq_pairLine_of_validLine` pins
   `npHeight ≡ 0` on `Icc 0 n`.
2. `hullDots_flat` — the on-hull dots are exactly the height-`0` dots.
3. `zero_mem_hullAbscissae` / `n_mem_hullAbscissae` / `mem_hullAbscissae_bound` — `0` and `n` are
   hull abscissae and every hull abscissa is `≤ n`; combined with sortedness
   (`Finset.pairwise_sort`) the abscissa list starts at `0` and ends at `n`
   (`head_zero_of_pairwise`, `getLastD_of_pairwise` — stated via `List.Pairwise (· ≤ ·)` and
   `List.getLastD`, since this mathlib pin exposes `Finset.sort` sortedness as `Pairwise`).
4. `npVerticesFull_flat` — the full vertex list is the abscissa list plotted at height `0`.
5. `dropCollinear_flat` (KEY combinatorial lemma) — `dropCollinear` collapses any all-height-`0`
   list to its two endpoints: any three height-`0` lattice points have vanishing integer cross
   product (`collinear₃_of_flat`), so every interior point is dropped.
6. `npVertices_of_flat` / `npSides_of_flat` — assemble; `npSides` on the 2-vertex list is a
   literal computation.

Also banked: the flat-side arithmetic the downstream γ3 residual-identification needs
(`flatSide_slope`, `flatSide_e`, `flatSide_h`, `flatSide_length`, `flatSide_residualDeg`).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.Order0

open scoped Classical
open NewtonPolygon

/-! ## List-level helpers (self-contained) -/

/-- `getLastD` commutes with plotting-at-height-0 (specialization of `List.getLastD_map`,
with the default value pre-beta-reduced so it can be used as a `rw` rule). -/
lemma getLastD_map_pair (l : List ℕ) (b : ℕ) :
    (l.map (fun i => (i, (0 : ℕ)))).getLastD (b, 0) = (l.getLastD b, 0) :=
  List.getLastD_map

/-- A `(· ≤ ·)`-pairwise `ℕ`-list containing `0` starts with `0`. -/
lemma head_zero_of_pairwise {l : List ℕ} (hp : l.Pairwise (· ≤ ·)) (h0 : 0 ∈ l) :
    ∃ t, l = 0 :: t := by
  cases l with
  | nil => simp at h0
  | cons a t =>
    rcases List.mem_cons.mp h0 with h | h
    · exact ⟨t, by rw [← h]⟩
    · have ha : a = 0 := Nat.le_zero.mp ((List.pairwise_cons.mp hp).1 0 h)
      exact ⟨t, by rw [ha]⟩
/-- In a `(· ≤ ·)`-pairwise `ℕ`-list, a member that dominates every member is the last entry
(phrased via `getLastD`, any default). -/
lemma getLastD_of_pairwise :
    ∀ (l : List ℕ) (m : ℕ), l.Pairwise (· ≤ ·) → m ∈ l → (∀ i ∈ l, i ≤ m) →
      ∀ d, l.getLastD d = m
  | [], m, _, hm, _, _ => by simp at hm
  | [a], m, _, hm, _, d => by
    rw [List.getLastD_cons, List.getLastD_nil]
    rcases List.mem_cons.mp hm with h | h
    · exact h.symm
    · simp at h
  | a :: b :: t, m, hp, hm, hb, d => by
    rw [List.getLastD_cons]
    have hp' : (b :: t).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hp).2
    have hm' : m ∈ b :: t := by
      rcases List.mem_cons.mp hm with h | h
      · have hmb : m ≤ b := by
          rw [h]; exact (List.pairwise_cons.mp hp).1 b (by simp)
        have hbm : b ≤ m := hb b (by simp)
        rw [← le_antisymm hbm hmb]
        simp
      · exact h
    exact getLastD_of_pairwise (b :: t) m hp' hm'
      (fun i hi => hb i (List.mem_cons_of_mem a hi)) a

/-! ## The key combinatorial lemma: `dropCollinear` on an all-height-0 list -/

/-- Any three height-`0` lattice points are `collinear₃`: the integer cross product has both
factors' second coordinates equal to `0`, so both sides vanish. -/
lemma collinear₃_of_flat {A B C : ℕ × ℕ} (hA : A.2 = 0) (hB : B.2 = 0) (hC : C.2 = 0) :
    collinear₃ A B C = true := by
  simp [collinear₃, hA, hB, hC]

/-- **KEY (blueprint γ1, step 5).** `dropCollinear` collapses a list of lattice points with ALL
second components `0` (length ≥ 2, headed form) to its two endpoints. -/
lemma dropCollinear_flat :
    ∀ (l : List (ℕ × ℕ)) (a b : ℕ × ℕ), (∀ P ∈ a :: b :: l, P.2 = 0) →
      dropCollinear (a :: b :: l) = [a, l.getLastD b]
  | [], a, b, _ => rfl
  | c :: rest, a, b, h => by
    have htail : dropCollinear (b :: c :: rest) = [b, rest.getLastD c] :=
      dropCollinear_flat rest b c (fun P hP => h P (List.mem_cons_of_mem a hP))
    have hmemL : rest.getLastD c ∈ a :: b :: c :: rest :=
      List.mem_cons_of_mem a (List.mem_cons_of_mem b List.getLastD_mem_cons)
    have hcol : collinear₃ a b (rest.getLastD c) = true :=
      collinear₃_of_flat (h a (by simp)) (h b (by simp)) (h _ hmemL)
    rw [dropCollinear_cons3, htail]
    simp only [hcol, if_true]
    rw [List.getLastD_cons]

/-! ## Step 1: the flat chord is valid and pins `npHeight ≡ 0` on `[0, n]` -/

/-- The chord through `(0, 0)` and `(n, 0)` is a valid supporting line of any support containing
both dots: it is identically `0` and every dot height is a `ℕ`-cast, hence `≥ 0`. -/
lemma flat_pair_mem_validLines (S : Finset (ℕ × ℕ)) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) :
    ((((0 : ℕ), (0 : ℕ)) : ℕ × ℕ), (((n : ℕ), (0 : ℕ)) : ℕ × ℕ)) ∈ validLines S := by
  rw [validLines, Finset.mem_filter]
  refine ⟨Finset.mem_product.2 ⟨h0, hnmem⟩, ?_⟩
  intro Q hQ
  have hz : pairLine ((0 : ℕ), (0 : ℕ)) ((n : ℕ), (0 : ℕ)) ((Q.1 : ℕ) : ℚ) = 0 :=
    pairLine_of_heights_zero rfl rfl _
  show pairLine ((0 : ℕ), (0 : ℕ)) ((n : ℕ), (0 : ℕ)) ((Q.1 : ℕ) : ℚ) ≤ ((Q.2 : ℕ) : ℚ)
  rw [hz]
  exact Nat.cast_nonneg _

/-- **Step 1 (blueprint γ1).** On a flat support the lower Newton height vanishes identically on
`[0, n]`: the flat chord is a valid line, so the breakpoint lemma
`npHeight_eq_pairLine_of_validLine` evaluates `npHeight` to the (zero) chord. -/
theorem npHeight_flat (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) :
    ∀ x ∈ Set.Icc (0 : ℚ) (n : ℚ), npHeight S hS x = 0 := by
  intro x hx
  have hval := flat_pair_mem_validLines S n h0 hnmem
  have hIcc : x ∈ Set.Icc (((0 : ℕ) : ℚ)) (((n : ℕ) : ℚ)) := by simpa using hx
  rw [npHeight_eq_pairLine_of_validLine S hS hval hIcc]
  exact pairLine_of_heights_zero rfl rfl x

/-! ## Step 2: the hull dots are the height-0 dots -/

/-- **Step 2 (blueprint γ1).** On a flat support the on-hull dots are exactly the height-`0`
dots. -/
theorem hullDots_flat (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) (hbound : ∀ P ∈ S, P.1 ≤ n) :
    hullDots S hS = S.filter (fun P => P.2 = 0) := by
  rw [hullDots]
  refine Finset.filter_congr fun P hP => ?_
  have hx : ((P.1 : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (n : ℚ) :=
    Set.mem_Icc.mpr ⟨by simp, by exact_mod_cast hbound P hP⟩
  unfold OnHull
  rw [npHeight_flat S hS n h0 hnmem _ hx]
  exact Nat.cast_eq_zero

/-! ## Step 3: the hull abscissae contain `0` and `n`, and are bounded by `n` -/

/-- `0` is a hull abscissa (witnessed by the on-hull dot `(0, 0)`). -/
lemma zero_mem_hullAbscissae (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) :
    (0 : ℕ) ∈ hullAbscissae S hS := by
  rw [mem_hullAbscissae_iff]
  refine ⟨0, h0, ?_⟩
  have hx : ((0 : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (n : ℚ) := Set.mem_Icc.mpr ⟨by simp, by simp⟩
  rw [npHeight_flat S hS n h0 hnmem _ hx]
  simp

/-- `n` is a hull abscissa (witnessed by the on-hull dot `(n, 0)`). -/
lemma n_mem_hullAbscissae (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) :
    n ∈ hullAbscissae S hS := by
  rw [mem_hullAbscissae_iff]
  refine ⟨0, hnmem, ?_⟩
  have hx : ((n : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (n : ℚ) := Set.mem_Icc.mpr ⟨by simp, le_refl _⟩
  rw [npHeight_flat S hS n h0 hnmem _ hx]
  simp

/-- Every hull abscissa is the abscissa of a support dot, hence `≤ n`. -/
lemma mem_hullAbscissae_bound (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (hbound : ∀ P ∈ S, P.1 ≤ n) {i : ℕ} (hi : i ∈ hullAbscissae S hS) : i ≤ n := by
  rw [mem_hullAbscissae_iff] at hi
  obtain ⟨v, hmem, -⟩ := hi
  exact hbound (i, v) hmem

/-! ## Step 4: the full vertex list is the abscissa list plotted at height 0 -/

/-- **Step 4 (blueprint γ1).** On a flat support, `npVerticesFull` is the hull-abscissa list
plotted at height `0` (`hullHeightAt = ⌊npHeight⌋.toNat = 0` everywhere on `[0, n]`). -/
theorem npVerticesFull_flat (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) (hbound : ∀ P ∈ S, P.1 ≤ n) :
    npVerticesFull S hS = (hullAbscissae S hS).map (fun i => (i, (0 : ℕ))) := by
  unfold npVerticesFull
  refine List.map_congr_left fun i hi => ?_
  have hin : i ≤ n := mem_hullAbscissae_bound S hS n hbound hi
  have hx : ((i : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (n : ℚ) :=
    Set.mem_Icc.mpr ⟨by simp, by exact_mod_cast hin⟩
  unfold hullDotAt hullHeightAt
  rw [npHeight_flat S hS n h0 hnmem _ hx]
  simp

/-! ## Step 6: assembly — the vertex and side lists of a flat support -/

/-- **γ1 vertex form** (blueprint `npVertices_of_flat`). The genuine vertex list of a flat
support is exactly the two endpoints `[(0, 0), (n, 0)]`. -/
theorem npVertices_of_flat (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ) (hn : 0 < n)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) (hbound : ∀ P ∈ S, P.1 ≤ n) :
    npVertices S hS = [((0 : ℕ), (0 : ℕ)), (n, (0 : ℕ))] := by
  have hpw : (hullAbscissae S hS).Pairwise (· ≤ ·) := by
    unfold hullAbscissae
    exact Finset.pairwise_sort _ _
  have h0m : (0 : ℕ) ∈ hullAbscissae S hS := zero_mem_hullAbscissae S hS n h0 hnmem
  have hnm : n ∈ hullAbscissae S hS := n_mem_hullAbscissae S hS n h0 hnmem
  have hbnd : ∀ i ∈ hullAbscissae S hS, i ≤ n :=
    fun i hi => mem_hullAbscissae_bound S hS n hbound hi
  have hlast : (hullAbscissae S hS).getLastD 0 = n :=
    getLastD_of_pairwise _ n hpw hnm hbnd 0
  obtain ⟨t, ht⟩ := head_zero_of_pairwise hpw h0m
  cases t with
  | nil =>
    rw [ht] at hnm
    simp at hnm
    omega
  | cons b t' =>
    rw [ht, List.getLastD_cons, List.getLastD_cons] at hlast
    unfold npVertices
    rw [npVerticesFull_flat S hS n h0 hnmem hbound, ht, List.map_cons, List.map_cons]
    have hflat : ∀ P ∈ ((0 : ℕ), (0 : ℕ)) :: (b, (0 : ℕ)) :: t'.map (fun i => (i, (0 : ℕ))),
        P.2 = 0 := by
      intro P hP
      rcases List.mem_cons.mp hP with hP0 | hP
      · rw [hP0]
      rcases List.mem_cons.mp hP with hP0 | hP
      · rw [hP0]
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hP
        rfl
    rw [dropCollinear_flat _ _ _ hflat, getLastD_map_pair, hlast]

/-- **γ1 (the flat-hull gate, HNODE0_BLUEPRINT §1).** A support containing `(0, 0)` and `(n, 0)`
with all abscissae `≤ n` has the single flat Newton-polygon side `⟨0, n, 0, 0⟩`. -/
theorem npSides_of_flat (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) (n : ℕ) (hn : 0 < n)
    (h0 : (0, 0) ∈ S) (hnmem : (n, 0) ∈ S) (hbound : ∀ P ∈ S, P.1 ≤ n) :
    NewtonPolygon.npSides S hS = [⟨0, n, 0, 0⟩] := by
  unfold NewtonPolygon.npSides
  rw [npVertices_of_flat S hS n hn h0 hnmem hbound]
  rfl

/-! ## Flat-side arithmetic (blueprint γ3 consumers)

The side data of `⟨0, n, 0, 0⟩` in the exact form the residual-identification node reads it:
slope `0`, ramification denominator `e = 1`, numerator `h = 0`, length `n`, residual degree `n`.
(None of these need `0 < n`: for `n = 0` the slope is the junk `0/0 = 0`, so they hold literally.) -/

/-- The flat side has slope `0`. -/
theorem flatSide_slope (n : ℕ) : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).slope = 0 := by
  simp [NewtonPolygon.Side.slope]

/-- The flat side has ramification denominator `e = Rat.den 0 = 1`. -/
theorem flatSide_e (n : ℕ) : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).e = 1 := by
  unfold NewtonPolygon.Side.e
  rw [flatSide_slope]
  exact Rat.den_zero

/-- The flat side has slope numerator `h = Rat.num 0 = 0`. -/
theorem flatSide_h (n : ℕ) : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).h = 0 := by
  unfold NewtonPolygon.Side.h
  rw [flatSide_slope]
  exact Rat.num_zero

/-- The flat side has horizontal length `n`. -/
theorem flatSide_length (n : ℕ) : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).length = n := by
  simp [NewtonPolygon.Side.length]

/-- The flat side has residual degree `ℓ/e = n/1 = n`. -/
theorem flatSide_residualDeg (n : ℕ) :
    M4.residualDeg (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) = n := by
  unfold M4.residualDeg
  rw [flatSide_length, flatSide_e, Nat.div_one]

end LeanUrat.OM.Order0
