/-
BP_I §1.4 — Splitting types (MeasureFloor).
Unit I-D1: `IsType` def + the positivity-guard note.
Unit I-D3 (C0): the graded type monoid (⊎ = Multiset add on `data`):
`Add FactorizationType`, `degree_add`, `add_comm'`/`add_assoc'`/
`add_left_cancel'`, `typeEmpty` + `degree_empty`.
Reuses the corpus type `LeanUrat.FactorizationType` (Interface.lean:152 —
`data : Multiset (ℕ × ℕ)` with `degree = Σ e·f`).
-/
import Mathlib
import LeanUrat.Interface

namespace LeanUrat.Scaffold

/-! ## I-D1: σ ∈ Σ_n

NOTE (displayed): bare `FactorizationType` admits (0,k) parts of degree 0, so
"degree n" alone is NOT finite — the positivity guard is part of `IsType`
(brief (3): pairs in ℤ_{≥1} × ℤ_{≥1}). -/

/-- σ ∈ Σ_n (brief (3)): degree n and every part positive. -/
def IsType (n : ℕ) (σ : FactorizationType) : Prop :=
  σ.degree = n ∧ ∀ ef ∈ σ.data, 1 ≤ ef.1 ∧ 1 ≤ ef.2

/-! ## I-D2: Lemma FIN (Df §1.3)

Proof shape (BP row I-D2): each part of an admissible `data` lies in
`(range (n+1)) ×ˢ (range (n+1))` and `data.card ≤ n`, so `data` is a
sub-multiset of the fixed multiset `n • ((range (n+1)) ×ˢ (range (n+1))).val`;
powerset finiteness + injectivity of `FactorizationType.mk` conclude. -/

/-- Lemma FIN: Σ_n is finite. -/
theorem isType_finite (n : ℕ) : {σ : FactorizationType | IsType n σ}.Finite := by
  -- the fixed dominating multiset
  set T : Multiset (ℕ × ℕ) :=
    n • ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).val with hT
  have hsub : {σ : FactorizationType | IsType n σ} ⊆
      FactorizationType.mk '' {s : Multiset (ℕ × ℕ) | s ∈ T.powerset} := by
    rintro ⟨s⟩ ⟨hdeg, hpos⟩
    refine ⟨s, ?_, rfl⟩
    rw [Set.mem_setOf_eq, Multiset.mem_powerset]
    have hsum : (s.map (fun ef => ef.1 * ef.2)).sum = n := hdeg
    -- card bound: every part contributes ≥ 1 to the degree sum
    have hcard : Multiset.card s ≤ n := by
      have h1 : ∀ x ∈ s.map (fun ef => ef.1 * ef.2), 1 ≤ x := by
        intro x hx
        obtain ⟨ef, hef, rfl⟩ := Multiset.mem_map.mp hx
        obtain ⟨he, hf⟩ := hpos ef hef
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h2 := Multiset.card_nsmul_le_sum h1
      simpa [hsum] using h2
    -- coordinate bound: each pair sits in range (n+1) × range (n+1)
    have hmem : ∀ ef ∈ s, ef ∈ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) := by
      intro ef hef
      obtain ⟨he, hf⟩ := hpos ef hef
      have hle : ef.1 * ef.2 ≤ n := by
        have hx : ef.1 * ef.2 ∈ s.map (fun p => p.1 * p.2) :=
          Multiset.mem_map_of_mem _ hef
        have := Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hx
        omega
      have he' : ef.1 ≤ n :=
        le_trans (by simpa using Nat.mul_le_mul (le_refl ef.1) hf) hle
      have hf' : ef.2 ≤ n :=
        le_trans (by simpa using Nat.mul_le_mul he (le_refl ef.2)) hle
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    -- multiplicity comparison
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ s
    · have h1 : s.count a ≤ n := (Multiset.count_le_card a s).trans hcard
      have h2 : T.count a = n := by
        rw [hT, Multiset.count_nsmul,
          Multiset.count_eq_one_of_mem (Finset.nodup _) (Finset.mem_val.mpr (hmem a ha)),
          mul_one]
      omega
    · simp [Multiset.count_eq_zero.mpr ha]
  exact Set.Finite.subset (Set.Finite.image _ T.powerset.finite_toSet) hsub

/-- The Finset carrier of Σ_n used by SUM-ONE (choice-free consumption). -/
noncomputable def typesFinset (n : ℕ) : Finset FactorizationType :=
  (isType_finite n).toFinset

theorem mem_typesFinset {n σ} : σ ∈ typesFinset n ↔ IsType n σ :=
  Set.Finite.mem_toFinset _

/-! ## I-D3: (C0) the graded type monoid (brief §6.2): ⊎ = Multiset add on `data` -/

instance : Add FactorizationType :=
  ⟨fun σ₁ σ₂ => ⟨σ₁.data + σ₂.data⟩⟩

@[simp] theorem add_data (σ₁ σ₂ : FactorizationType) :
    (σ₁ + σ₂).data = σ₁.data + σ₂.data := rfl

theorem degree_add (σ₁ σ₂ : FactorizationType) :
    (σ₁ + σ₂).degree = σ₁.degree + σ₂.degree := by
  simp [FactorizationType.degree, Multiset.map_add]

theorem add_comm' (σ₁ σ₂ : FactorizationType) : σ₁ + σ₂ = σ₂ + σ₁ :=
  congrArg FactorizationType.mk (add_comm σ₁.data σ₂.data)

theorem add_assoc' (σ₁ σ₂ σ₃ : FactorizationType) :
    σ₁ + σ₂ + σ₃ = σ₁ + (σ₂ + σ₃) :=
  congrArg FactorizationType.mk (add_assoc σ₁.data σ₂.data σ₃.data)

theorem add_left_cancel' (σ σ₁ σ₂ : FactorizationType)
    (h : σ + σ₁ = σ + σ₂) : σ₁ = σ₂ := by
  have hd : σ₁.data = σ₂.data :=
    add_left_cancel (congrArg FactorizationType.data h)
  cases σ₁; cases σ₂; exact congrArg FactorizationType.mk hd

/-- The unit ∅ of the graded type monoid. -/
def typeEmpty : FactorizationType := ⟨0⟩

@[simp] theorem degree_empty : typeEmpty.degree = 0 := rfl

/-! ## I-D4: degree-1 multiset analysis (Df §6.1 BASE-1(a)) -/

theorem isType_one_iff (σ) : IsType 1 σ ↔ σ = ⟨{(1, 1)}⟩          -- BASE-1(a)
  := by
  constructor
  · rintro ⟨hdeg, hpos⟩
    obtain ⟨data⟩ := σ
    simp only [FactorizationType.degree] at hdeg
    induction data using Multiset.induction_on with
    | empty => simp at hdeg
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons] at hdeg
      obtain ⟨ha1, ha2⟩ := hpos a (Multiset.mem_cons_self a t)
      have haprod : 1 ≤ a.1 * a.2 := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hta : t = 0 := by
        rcases eq_or_ne t 0 with h | h
        · exact h
        · exfalso
          obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero h
          obtain ⟨hb1, hb2⟩ := hpos b (Multiset.mem_cons_of_mem hb)
          have hble : b.1 * b.2 ≤ (Multiset.map (fun p => p.1 * p.2) t).sum :=
            Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
              (Multiset.mem_map_of_mem _ hb)
          have hbprod : 1 ≤ b.1 * b.2 := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega))
          omega
      subst hta
      have hprod : a.1 * a.2 = 1 := by simpa using hdeg
      obtain ⟨h1, h2⟩ := (mul_eq_one_iff_of_one_le ha1 ha2).mp hprod
      have ha : a = (1, 1) := Prod.ext h1 h2
      subst ha
      rfl
  · rintro rfl
    refine ⟨by simp [FactorizationType.degree], ?_⟩
    intro ef hef
    simp only [Multiset.mem_singleton] at hef
    simp [hef]

/-! ## I-D5 (`isType_zero_iff`, BASE-0(a)): every part contributes ≥ 1

(`typeEmpty`/`degree_empty` deduped: I-D3's monoid block above carries them.) -/

theorem isType_zero_iff (σ) : IsType 0 σ ↔ σ = typeEmpty          -- BASE-0(a)
  := by
  constructor
  · rintro ⟨hdeg, hpos⟩
    -- degree 0 forces the part multiset empty: each part contributes
    -- e·f ≥ 1 to the degree sum.
    have hdata : σ.data = 0 := by
      by_contra h
      obtain ⟨ef, hef⟩ := Multiset.exists_mem_of_ne_zero h
      obtain ⟨he, hf⟩ := hpos ef hef
      have hef1 : 1 ≤ ef.1 * ef.2 := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hle : ef.1 * ef.2 ≤ σ.degree :=
        Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
          (Multiset.mem_map_of_mem _ hef)
      omega
    obtain ⟨data⟩ := σ
    simpa [typeEmpty] using hdata
  · rintro rfl
    exact ⟨degree_empty, fun ef hef => absurd hef (by simp [typeEmpty])⟩

end LeanUrat.Scaffold
