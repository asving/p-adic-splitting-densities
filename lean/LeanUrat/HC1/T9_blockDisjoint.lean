/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L0_FactB_unique

/-!
# HC1.T9_blockDisjoint — (ii.3), TWO legs (audit G-5)

moves_ref: MOVES 2175–2188 ("distinct development slots have disjoint leaf subtrees
(the development is a coordinate partition) … the two forced slot classes t_k·γ*,
t_k·γ′* differ (t_k invertible mod e_k) … induction bottoms at distinct p-adic
heights — disjoint addresses"). deps: DefsCar, T12; Moves `L0_FactB_unique` (clean —
development uniqueness = the partition). Leg (a) is the ledger-facing locus
disjointness; leg (b) is THE CONTENT (audit G-5): the mixed-radix leaf-address
injectivity — "no two equations of one system pin the same digit coordinate", the
injectivity S17's `L6_ledgerCount` consumption rests on. difficulty: medium.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-! ## Generic mixed-radix uniqueness (over `ℕ`, tower-independent)

`D r` is the `r`-th place value, `c r` the `r`-th digit bound. The single structural
hypothesis is `hstep : c r · D r ≤ D (r+1)` (the ratio-floor inequality, `Nat.div_mul_le_self`):
each digit's maximal contribution stays below the next place value. With `hD : 1 ≤ D r`
this forces every prefix `∑_{r<n} a r · D r` to stay `< D n`, which is exactly the
carrying-free property that makes the positional representation unique. -/

/-- Prefix bound: the base-`D` value of the first `n` digits (each `a r < c r`) is `< D n`. -/
private lemma mr_prefix_lt (D c a : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r < D n := by
  intro n
  induction n with
  | zero =>
      intro _ _
      simp only [Finset.range_zero, Finset.sum_empty]
      exact hD 0
  | succ m ih =>
      intro hb hstep
      rw [Finset.sum_range_succ]
      have hpre : ∑ r ∈ Finset.range m, a r * D r < D m :=
        ih (fun r hr => hb r (Nat.lt_succ_of_lt hr)) (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have ham : a m + 1 ≤ c m := hb m (Nat.lt_succ_self m)
      calc ∑ r ∈ Finset.range m, a r * D r + a m * D m
          < D m + a m * D m := by omega
        _ = (a m + 1) * D m := by ring
        _ ≤ c m * D m := by gcongr
        _ ≤ D (m + 1) := hstep m (Nat.lt_succ_self m)

/-- Injectivity on a fully-bounded prefix: two digit strings of length `n`, each digit
`< c r`, with equal base-`D` value, agree on every position `< n`. -/
private lemma mr_inj_prefix (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → b r < c r) →
      (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r = ∑ r ∈ Finset.range n, b r * D r →
      ∀ r, r < n → a r = b r := by
  intro n
  induction n with
  | zero => intro _ _ _ _ r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ m ih =>
      intro ha hb hstep hsum r hr
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
      have hpa : ∑ r ∈ Finset.range m, a r * D r < D m :=
        mr_prefix_lt D c a hD m (fun r hr => ha r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have hpb : ∑ r ∈ Finset.range m, b r * D r < D m :=
        mr_prefix_lt D c b hD m (fun r hr => hb r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      set Pa := ∑ r ∈ Finset.range m, a r * D r with hPadef
      set Pb := ∑ r ∈ Finset.range m, b r * D r with hPbdef
      have hDm : 0 < D m := hD m
      have hPaeq : (Pa + a m * D m) % D m = Pa := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
      have hPbeq : (Pb + b m * D m) % D m = Pb := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
      have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
      have hamm : a m * D m = b m * D m := by omega
      have ham : a m = b m := Nat.eq_of_mul_eq_mul_right hDm hamm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · exact ih (fun r hr => ha r (Nat.lt_succ_of_lt hr))
              (fun r hr => hb r (Nat.lt_succ_of_lt hr))
              (fun r hr => hstep r (Nat.lt_succ_of_lt hr)) hmod r hlt
      · subst heq; exact ham

/-- Top-peel injectivity: positions `0..n-1` bounded (`< c r`), position `n` free;
equal base-`D` value forces agreement on all of `0..n`. This is the shape T9(b) needs
(the top development slot is unbounded — recorded decision (2)). -/
private lemma mr_inj_top (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) (n : ℕ)
    (ha : ∀ r, r < n → a r < c r) (hb : ∀ r, r < n → b r < c r)
    (hstep : ∀ r, r < n → c r * D r ≤ D (r + 1))
    (hsum : ∑ r ∈ Finset.range (n + 1), a r * D r = ∑ r ∈ Finset.range (n + 1), b r * D r) :
    ∀ r, r ≤ n → a r = b r := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
  have hpa : ∑ r ∈ Finset.range n, a r * D r < D n := mr_prefix_lt D c a hD n ha hstep
  have hpb : ∑ r ∈ Finset.range n, b r * D r < D n := mr_prefix_lt D c b hD n hb hstep
  set Pa := ∑ r ∈ Finset.range n, a r * D r with hPadef
  set Pb := ∑ r ∈ Finset.range n, b r * D r with hPbdef
  have hDn : 0 < D n := hD n
  have hPaeq : (Pa + a n * D n) % D n = Pa := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
  have hPbeq : (Pb + b n * D n) % D n = Pb := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
  have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
  have hamm : a n * D n = b n * D n := by omega
  have han : a n = b n := Nat.eq_of_mul_eq_mul_right hDn hamm
  intro r hr
  rcases hr.lt_or_eq with hlt | heq
  · exact mr_inj_prefix D c a b hD n ha hb hstep hmod r hlt
  · subst heq; exact han

/-- Unit T9: (a) distinct (block, height) pins constrain disjoint loci;
(b) the mixed-radix address map `c ↦ (Σ_r slot_r·deg Φ_r, l)` is injective on
coordinates (the slot vector is the mixed-radix representation of the base index
in the degree-ratio radices — slot_lt = exactly the digit bounds). -/
theorem T9_blockDisjoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) :
    (∀ (b b' : ℕ) (γ γ' : ℚ), (b, γ) ≠ (b', γ') →
      Disjoint (T.levelSet b γ) (T.levelSet b' γ')) ∧
    Function.Injective (fun c : T.Coord => (T.baseIdx c, c.l)) := by
  refine ⟨?_, ?_⟩
  · -- Leg (a): `blk`/`ht` are functions, so distinct `(b,γ)` pins name disjoint loci.
    intro b b' γ γ' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨hb, hγ⟩ := hx
    obtain ⟨hb', hγ'⟩ := hx'
    exact hne (by rw [Prod.mk.injEq]; exact ⟨hb.symm.trans hb', hγ.symm.trans hγ'⟩)
  · -- Leg (b): mixed-radix injectivity of the leaf-address map.
    intro c c' hcc
    simp only [Prod.mk.injEq] at hcc
    obtain ⟨hbase, hl⟩ := hcc
    -- place values `D r = deg Φ_r` and digit bounds `cc r = slotBound r`, extended to `ℕ`
    set D : ℕ → ℕ := fun r => if h : r < T.K + 1 then (T.stg ⟨r, h⟩).Φ.natDegree else 1
      with hDdef
    set cc : ℕ → ℕ := fun r => if h : r < T.K then T.slotBound ⟨r, h⟩ else 1 with hccdef
    -- every place value is `≥ 1` (each key polynomial has positive degree)
    have hD : ∀ r, 1 ≤ D r := by
      intro r
      simp only [hDdef]
      by_cases h : r < T.K + 1
      · rw [dif_pos h]; exact (T.stg ⟨r, h⟩).hdeg
      · rw [dif_neg h]
    -- the ratio-floor inequality `slotBound r · deg Φ_r ≤ deg Φ_{r+1}`
    have hstep : ∀ r, r < T.K → cc r * D r ≤ D (r + 1) := by
      intro r hr
      have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
      have hr2 : r + 1 < T.K + 1 := by omega
      simp only [hccdef, hDdef, dif_pos hr, dif_pos hr1, dif_pos hr2]
      have hcs : (⟨r, hr⟩ : Fin T.K).castSucc = (⟨r, hr1⟩ : Fin (T.K + 1)) := by
        rfl
      have hsc : (⟨r, hr⟩ : Fin T.K).succ = (⟨r + 1, hr2⟩ : Fin (T.K + 1)) := by
        rfl
      unfold Tower.slotBound
      rw [hcs, hsc]
      exact Nat.div_mul_le_self _ _
    -- rewrite each base index as an `ℕ`-indexed mixed-radix sum
    have hconv : ∀ d : T.Coord, T.baseIdx d
        = ∑ r ∈ Finset.range (T.K + 1),
            (if h : r < T.K + 1 then d.slot ⟨r, h⟩ else 0) * D r := by
      intro d
      have hterm : (∑ i : Fin (T.K + 1), d.slot i * (T.stg i).Φ.natDegree)
          = ∑ r ∈ Finset.range (T.K + 1),
              (if h : r < T.K + 1 then d.slot ⟨r, h⟩ else 0) * D r := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun r => (if h : r < T.K + 1 then d.slot ⟨r, h⟩ else 0) * D r) (T.K + 1)]
        apply Finset.sum_congr rfl
        intro i _
        have hi : (i : ℕ) < T.K + 1 := i.2
        have hslot_eval :
            (if h : (i : ℕ) < T.K + 1 then d.slot ⟨(i : ℕ), h⟩ else 0) = d.slot i := by
          rw [dif_pos hi]
        have hD_eval : D (i : ℕ) = (T.stg i).Φ.natDegree := by
          simp only [hDdef]; rw [dif_pos hi]
        change d.slot i * (T.stg i).Φ.natDegree
            = (if h : (i : ℕ) < T.K + 1 then d.slot ⟨(i : ℕ), h⟩ else 0) * D (i : ℕ)
        rw [hslot_eval, hD_eval]
      change (∑ i : Fin (T.K + 1), d.slot i * (T.stg i).Φ.natDegree) = _
      exact hterm
    -- digit bounds transported from `slot_lt`
    have haC : ∀ r, r < T.K →
        (if h : r < T.K + 1 then c.slot ⟨r, h⟩ else 0) < cc r := by
      intro r hr
      have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
      simp only [hccdef, dif_pos hr, dif_pos hr1]
      have hcs : (⟨r, hr⟩ : Fin T.K).castSucc = (⟨r, hr1⟩ : Fin (T.K + 1)) := by
        rfl
      have := c.slot_lt ⟨r, hr⟩
      rwa [hcs] at this
    have haC' : ∀ r, r < T.K →
        (if h : r < T.K + 1 then c'.slot ⟨r, h⟩ else 0) < cc r := by
      intro r hr
      have hr1 : r < T.K + 1 := Nat.lt_succ_of_lt hr
      simp only [hccdef, dif_pos hr, dif_pos hr1]
      have hcs : (⟨r, hr⟩ : Fin T.K).castSucc = (⟨r, hr1⟩ : Fin (T.K + 1)) := by
        rfl
      have := c'.slot_lt ⟨r, hr⟩
      rwa [hcs] at this
    rw [hconv c, hconv c'] at hbase
    have hslots := mr_inj_top D cc
      (fun r => if h : r < T.K + 1 then c.slot ⟨r, h⟩ else 0)
      (fun r => if h : r < T.K + 1 then c'.slot ⟨r, h⟩ else 0)
      hD T.K haC haC' hstep hbase
    -- conclude equality of the whole slot vectors
    have hslot : c.slot = c'.slot := by
      funext i
      have hi : (i : ℕ) < T.K + 1 := i.2
      have hle : (i : ℕ) ≤ T.K := Nat.lt_succ_iff.mp hi
      have hik := hslots (i : ℕ) hle
      rw [dif_pos hi, dif_pos hi] at hik
      exact hik
    -- assemble `Coord` equality (proof field irrelevant)
    obtain ⟨l, s, hs⟩ := c
    obtain ⟨l', s', hs'⟩ := c'
    replace hl : l = l' := hl
    replace hslot : s = s' := hslot
    subst hl
    subst hslot
    rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T9_blockDisjoint
