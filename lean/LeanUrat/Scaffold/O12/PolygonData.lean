/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/O12/PolygonData — face-kind sequences [unit II-P1]

E-phase transcription of `lean/blueprints/BP_II.md` §1.6, unit II-P1: the
`FaceKind` structure (verbatim) and the `FaceKind.x` / `FaceKind.d`
definitions (signatures verbatim; bodies realize the docstring's defining
clauses `x_1 = 0, x_{j+1} = x_j + L_j` and `d_j = L_j / b_j`).
Math source of record: `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§3 (the L6 setting). Later units II-P2..II-P8 (`SlopeTuple`, `heights`,
L6b, L4(ii) arithmetic) extend this file.

Indexing convention (recorded for downstream units): faces are 0-indexed in
Lean (`j = 0` is the blueprint's `j = 1`), so `x 0 = 0` and
`x (j+1) = x j + L_j` for `j < k`; `x` saturates at `e` for `j ≥ k`, and
`d j = 0` out of range. The defining equations are certified below
(`x_zero`, `x_succ_of_lt`, `x_length`, `d_of_lt`).
-/

set_option linter.style.longLine false

namespace LeanUrat.Scaffold

variable {e : ℕ}

/-- A face-kind sequence κ = (L_j, b_j)_{j=1..k} on width e (brief §3, L6): L_j ≥ 1,
Σ L_j = e, b_j ∣ L_j, b_k ≥ 2. d_j := L_j/b_j; x_1 = 0, x_{j+1} = x_j + L_j. -/
structure FaceKind (e : ℕ) where
  faces    : List (ℕ+ × ℕ+)                    -- (L_j, b_j), left to right
  hsum     : (faces.map (·.1.val)).sum = e
  hdvd     : ∀ f ∈ faces, (f.2 : ℕ) ∣ (f.1 : ℕ)
  hlast    : ∀ h : faces ≠ [], 2 ≤ ((faces.getLast h).2 : ℕ)

/-- Vertex abscissas: `x j = L_0 + ⋯ + L_{j-1}` (so `x 0 = 0`,
`x (j+1) = x j + L_j` while `j < k`, saturating at `e` for `j ≥ k`). -/
def FaceKind.x (κ : FaceKind e) (j : ℕ) : ℕ :=
  ((κ.faces.take j).map (·.1.val)).sum

/-- Residual degrees `d_j = L_j / b_j` (an exact division by `hdvd`);
`0` out of range. -/
def FaceKind.d (κ : FaceKind e) (j : ℕ) : ℕ :=
  match κ.faces[j]? with
  | some f => (f.1 : ℕ) / (f.2 : ℕ)
  | none   => 0

namespace FaceKind

@[simp] theorem x_zero (κ : FaceKind e) : κ.x 0 = 0 := rfl

/-- The defining recurrence `x_{j+1} = x_j + L_j` (0-indexed, in range). -/
theorem x_succ_of_lt (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.x (j + 1) = κ.x j + (κ.faces[j].1 : ℕ) := by
  simp only [FaceKind.x, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The rightmost vertex abscissa is the full width `e`. -/
theorem x_length (κ : FaceKind e) : κ.x κ.faces.length = e := by
  simpa [FaceKind.x] using κ.hsum

/-- The defining clause `d_j = L_j / b_j` (0-indexed, in range). -/
theorem d_of_lt (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.d j = (κ.faces[j].1 : ℕ) / ((κ.faces[j].2 : ℕ)) := by
  simp [FaceKind.d, List.getElem?_eq_getElem hj]

end FaceKind

/-! ## Unit II-P2: `SlopeTuple`, `heights`, `vertexHeight_int`

Blueprint §1.6 pseudo-notation realized: `slope j := (a j : ℚ) / (b j : ℚ)` is
inlined at its two use sites (`hdesc`, `hlt1`); `last` is the index
`κ.faces.length - 1` (well-defined under `h : κ.faces ≠ []`). -/

/-- An admissible slope tuple: numerators a_j ≥ 1, gcd(a_j, b_j) = 1, s_1 > ⋯ > s_k,
s_k ∈ (0,1) (i.e. a_k < b_k). -/
structure SlopeTuple (κ : FaceKind e) where
  a       : Fin κ.faces.length → ℕ+
  hcop    : ∀ j, Nat.Coprime (a j) (κ.faces.get j).2
  hdesc   : ∀ j j' : Fin κ.faces.length, j < j' →
    ((a j' : ℕ) : ℚ) / (((κ.faces.get j').2 : ℕ) : ℚ) <
      ((a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ)
  hlt1    : ∀ h : κ.faces ≠ [],
    ((a ⟨κ.faces.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil h) Nat.one_pos⟩ : ℕ) : ℚ) /
      (((κ.faces.getLast h).2 : ℕ) : ℚ) < 1

/-- Heights h_i := P(i) ∈ ℚ (right-anchored: h_e = 0); vertex heights are integers
h_{x_j} = Σ_{j′≥j} a_{j′}·d_{j′} (each face drops a_j·d_j ∈ ℤ).

Realization: h_i sums, over each face j, the slope a_j/b_j times the width of the
part of face j lying to the right of the abscissa i (so `heights` is the
piecewise-linear polygon read right-anchored from h_e = 0). -/
noncomputable def heights (κ : FaceKind e) (s : SlopeTuple κ) (i : ℕ) : ℚ :=
  ∑ j : Fin κ.faces.length,
    ((s.a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) *
      ((max (κ.x ((j : ℕ) + 1)) i - max (κ.x (j : ℕ)) i : ℕ) : ℚ)

/-- Vertex heights are integers: h_{x_j} = ((Σ_{j′ ≥ j} a_{j′}·d_{j′} : ℕ) : ℚ) —
each face drops a_j·d_j ∈ ℤ. -/
theorem vertexHeight_int (κ : FaceKind e) (s : SlopeTuple κ) (j : ℕ) :
    heights κ s (κ.x j) =
      ((∑ j' ∈ Finset.univ.filter (fun j' : Fin κ.faces.length => j ≤ (j' : ℕ)),
          (s.a j' : ℕ) * κ.d (j' : ℕ) : ℕ) : ℚ) := by
  have hmono : Monotone κ.x := by
    apply monotone_nat_of_le_succ
    intro m
    by_cases hm : m < κ.faces.length
    · rw [κ.x_succ_of_lt hm]; omega
    · unfold FaceKind.x
      rw [List.take_of_length_le (Nat.le_of_not_lt hm),
        List.take_of_length_le (by omega)]
  rw [heights, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j' _ => ?_
  by_cases hj : j ≤ (j' : ℕ)
  · rw [if_pos hj]
    have h1 : κ.x j ≤ κ.x (j' : ℕ) := hmono hj
    have h2 : κ.x j ≤ κ.x ((j' : ℕ) + 1) := hmono (by omega)
    rw [max_eq_left h2, max_eq_left h1, κ.x_succ_of_lt j'.isLt,
      Nat.add_sub_cancel_left, κ.d_of_lt j'.isLt]
    have hdvd : ((κ.faces.get j').2 : ℕ) ∣ ((κ.faces.get j').1 : ℕ) :=
      κ.hdvd _ (κ.faces.get_mem j')
    have hb : (((κ.faces.get j').2 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (κ.faces.get j').2.ne_zero
    simp only [List.get_eq_getElem] at hdvd hb ⊢
    rw [Nat.cast_mul, Nat.cast_div hdvd hb]
    field_simp
  · rw [if_neg hj]
    have h1 : κ.x ((j' : ℕ) + 1) ≤ κ.x j := hmono (by omega)
    have h2 : κ.x (j' : ℕ) ≤ κ.x j := hmono (by omega)
    rw [max_eq_right h1, max_eq_right h2]
    simp

/-! ## Unit II-P7: `singleFace_finite`

Realization: with a single face, `hlt1` bounds the unique numerator strictly by
the last denominator `b`, giving an injection `SlopeTuple κ ↪ Fin b`. -/

/-- L6b(ii), k = 1: a single-face kind has NO unbounded parameter (finitely many
admissible tuples: a_k ∈ {1,…,b_k−1}). -/
theorem singleFace_finite (κ : FaceKind e) (h : κ.faces.length = 1) :
    Finite (SlopeTuple κ) := by
  have hne : κ.faces ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hzero : (0 : ℕ) < κ.faces.length := by omega
  have hbound : ∀ s : SlopeTuple κ,
      (s.a ⟨0, hzero⟩ : ℕ) < ((κ.faces.getLast hne).2 : ℕ) := by
    intro s
    have hlt := s.hlt1 hne
    have hidx : (⟨κ.faces.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos⟩ :
          Fin κ.faces.length) = ⟨0, hzero⟩ := by
      ext; omega
    rw [hidx] at hlt
    have hbpos : (0 : ℚ) < (((κ.faces.getLast hne).2 : ℕ) : ℚ) := by
      exact_mod_cast (κ.faces.getLast hne).2.pos
    exact_mod_cast (div_lt_one hbpos).mp hlt
  refine Finite.of_injective
    (fun s : SlopeTuple κ =>
      (⟨(s.a ⟨0, hzero⟩ : ℕ), hbound s⟩ : Fin ((κ.faces.getLast hne).2 : ℕ))) ?_
  intro s s' hss
  have hval : (s.a ⟨0, hzero⟩ : ℕ) = (s'.a ⟨0, hzero⟩ : ℕ) :=
    congrArg Fin.val hss
  have ha : s.a = s'.a := by
    funext j
    have hj : j = ⟨0, hzero⟩ := by
      have := j.isLt; ext; omega
    rw [hj]
    exact PNat.coe_injective hval
  cases s; cases s'
  simp_all

/-! ## Unit II-P3: `Npg`, `one_le_ceil_height`

The blueprint's `(hpos : ...)` placeholder is discharged internally: slopes are
positive by construction (`a j : ℕ+`), so `h_i > 0` for every `i < e` (the unit
sketch's "slopes > 0, h_e = 0 ⟹ h_i > 0 for i < e") needs no extra hypothesis,
matching the `Npg` docstring's unconditional "every ⌈h_i⌉ ≥ 1". -/

/-- N(P) = Σ_{i<e} ⌈h_i⌉, with every ⌈h_i⌉ ≥ 1 (slopes > 0, h_e = 0). -/
noncomputable def Npg (κ : FaceKind e) (s : SlopeTuple κ) : ℤ :=
  ∑ i ∈ Finset.range e, ⌈heights κ s i⌉

/-- Every column of `Npg` contributes at least 1: for `i < e` the height `h_i`
is positive (all slopes > 0, right-anchored at `h_e = 0` — the last face's
term alone is already positive), so `1 ≤ ⌈h_i⌉` by `Int.one_le_ceil_iff`. -/
theorem one_le_ceil_height (κ : FaceKind e) (s : SlopeTuple κ) {i : ℕ}
    (hi : i < e) : 1 ≤ ⌈heights κ s i⌉ := by
  rw [Int.one_le_ceil_iff]
  have hne : κ.faces ≠ [] := by
    intro h
    have hs := κ.hsum
    rw [h] at hs
    simp at hs
    omega
  have hk : 0 < κ.faces.length := List.length_pos_of_ne_nil hne
  set jl : Fin κ.faces.length := ⟨κ.faces.length - 1, by omega⟩ with hjl
  unfold heights
  refine Finset.sum_pos' (fun j _ => ?_) ⟨jl, Finset.mem_univ _, ?_⟩
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  · apply mul_pos
    · exact div_pos (by exact_mod_cast (s.a jl).pos)
        (by exact_mod_cast (κ.faces.get jl).2.pos)
    · have hx1 : κ.x ((jl : ℕ) + 1) = e := by
        have hlen : (jl : ℕ) + 1 = κ.faces.length := by
          simp only [hjl]; omega
        rw [hlen, κ.x_length]
      have hx0 : κ.x (jl : ℕ) < e := by
        have hrec := κ.x_succ_of_lt jl.isLt
        have hL : 1 ≤ (κ.faces[(jl : ℕ)].1 : ℕ) := κ.faces[(jl : ℕ)].1.pos
        omega
      have hlt : 0 < max (κ.x ((jl : ℕ) + 1)) i - max (κ.x (jl : ℕ)) i := by
        rw [hx1]; omega
      exact_mod_cast hlt

/-! ## Unit II-P5: `aMin` and the nested-minimum period shift `aMin_shift`

Blueprint §1.6 gives the unit as `theorem aMin_shift ...` under the docstring
"L6b(ii), the nested-minimum period shift: a_j^min(s+1) = a_j^min(s) + b_j";
the body is realized per the math source of record
(`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` §3, L6b(ii) proof):
`a_j^min(s)` is the LEAST element `a` of the residue class `r_j + b_jℤ ⊆ ℤ`
with slope `a/b_j > s`. Here `aMin b r s` realizes it for an abstract
modulus `b : ℕ+`, class representative `r : ℤ`, threshold `s : ℚ` — at face
`j` of a `SlopeTuple` instantiate `b := (κ.faces.get j).2`, `r := s.a j`.
The three defining clauses are certified (`aMin_emod`, `aMin_slope_gt`,
`aMin_min`), and `aMin_shift` is proved from them exactly by the blueprint
sketch: the bijection `a ↦ a − b` of the residue class, minimality both ways.
-/

/-- `a^min(s)`: the least element `a` of the residue class `r + bℤ` (inside
`ℤ`) with slope `a/b > s` (brief §3, L6b(ii)). Explicit form: the least
integer exceeding `s·b` is `M := ⌊s·b⌋ + 1`, and the least class member
`≥ M` is `M + ((r − M) mod b)`. The defining clauses — class membership,
threshold, minimality — are certified by `aMin_emod`, `aMin_slope_gt`,
`aMin_min` below. -/
def aMin (b : ℕ+) (r : ℤ) (s : ℚ) : ℤ :=
  (⌊s * ((b : ℕ) : ℚ)⌋ + 1) + (r - (⌊s * ((b : ℕ) : ℚ)⌋ + 1)) % ((b : ℕ) : ℤ)

/-- `aMin` lies in the residue class `r + bℤ`. -/
theorem aMin_emod (b : ℕ+) (r : ℤ) (s : ℚ) :
    aMin b r s % ((b : ℕ) : ℤ) = r % ((b : ℕ) : ℤ) := by
  unfold aMin
  rw [Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod,
    add_sub_cancel]

/-- `aMin` clears the threshold: `s < aMin/b`. -/
theorem aMin_slope_gt (b : ℕ+) (r : ℤ) (s : ℚ) :
    s < ((aMin b r s : ℤ) : ℚ) / ((b : ℕ) : ℚ) := by
  have hbQ : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast b.pos
  have hbZ : ((b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast b.ne_zero
  rw [lt_div_iff₀ hbQ]
  have hM : ⌊s * ((b : ℕ) : ℚ)⌋ + 1 ≤ aMin b r s := by
    have := Int.emod_nonneg (r - (⌊s * ((b : ℕ) : ℚ)⌋ + 1)) hbZ
    unfold aMin; omega
  calc s * ((b : ℕ) : ℚ) < ((⌊s * ((b : ℕ) : ℚ)⌋ + 1 : ℤ) : ℚ) := by
        push_cast; exact Int.lt_floor_add_one _
    _ ≤ ((aMin b r s : ℤ) : ℚ) := by exact_mod_cast hM

/-- Minimality: `aMin` is ≤ every element of the residue class clearing the
threshold. -/
theorem aMin_min (b : ℕ+) (r : ℤ) (s : ℚ) {a : ℤ}
    (hmod : a % ((b : ℕ) : ℤ) = r % ((b : ℕ) : ℤ))
    (hgt : s < (a : ℚ) / ((b : ℕ) : ℚ)) :
    aMin b r s ≤ a := by
  have hbQ : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast b.pos
  have hbZ : (0 : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast b.pos
  -- `a` clears the integer threshold `M := ⌊s·b⌋ + 1`.
  have hMa : ⌊s * ((b : ℕ) : ℚ)⌋ + 1 ≤ a := by
    have : ⌊s * ((b : ℕ) : ℚ)⌋ < a := Int.floor_lt.mpr ((lt_div_iff₀ hbQ).mp hgt)
    omega
  -- `aMin` sits within one period above `M`.
  have hlt : aMin b r s < ⌊s * ((b : ℕ) : ℚ)⌋ + 1 + ((b : ℕ) : ℤ) := by
    have := Int.emod_lt_of_pos (r - (⌊s * ((b : ℕ) : ℚ)⌋ + 1)) hbZ
    unfold aMin; omega
  -- Two class members within one period of each other coincide or differ by ≥ b.
  by_contra hcon
  push Not at hcon
  have hdvd : ((b : ℕ) : ℤ) ∣ aMin b r s - a := by
    refine Int.dvd_of_emod_eq_zero ?_
    rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero, aMin_emod, hmod]
  have := Int.le_of_dvd (by omega) hdvd
  omega

/-- L6b(ii), the nested-minimum period shift: a_j^min(s+1) = a_j^min(s) + b_j. -/
theorem aMin_shift (b : ℕ+) (r : ℤ) (s : ℚ) :
    aMin b r (s + 1) = aMin b r s + ((b : ℕ) : ℤ) := by
  have hbQ : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast b.pos
  have hbZ : ((b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast b.ne_zero
  -- (≤): `aMin b r s + b` is in the class and clears `s + 1` — minimality at `s + 1`.
  have h1 : aMin b r (s + 1) ≤ aMin b r s + ((b : ℕ) : ℤ) := by
    refine aMin_min b r (s + 1) ?_ ?_
    · rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod_of_dvd _ dvd_rfl,
        aMin_emod]
    · have := aMin_slope_gt b r s
      rw [lt_div_iff₀ hbQ] at this ⊢
      push_cast
      nlinarith
  -- (≥): `aMin b r (s+1) − b` is in the class and clears `s` — minimality at `s`.
  have h2 : aMin b r s ≤ aMin b r (s + 1) - ((b : ℕ) : ℤ) := by
    refine aMin_min b r s ?_ ?_
    · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ dvd_rfl,
        aMin_emod]
    · have := aMin_slope_gt b r (s + 1)
      rw [lt_div_iff₀ hbQ] at this ⊢
      push_cast
      nlinarith
  omega

/-! ## Unit II-P8: `faceDeg_bound` + `handoff_mu_lt` + `patt_mult_lt`

L4 arithmetic (the (SL≥2)(a) hand-off bound), blueprint §1.6. Sketch: the
rightmost face has b_k ≥ 2, so d_k = L_k/b_k < L_k ≤ e; any other face sits
left of the rightmost one, so L_j ≤ e − L_k ≤ e − 1 and d_j ≤ L_j < e. The
helpers `FaceKind.x_mono` / `FaceKind.d_eq_zero_of_le` record the
monotonicity and out-of-range facts used. -/

namespace FaceKind

/-- Vertex abscissas are monotone (they saturate at `e` past the last face). -/
theorem x_mono (κ : FaceKind e) : Monotone κ.x := by
  apply monotone_nat_of_le_succ
  intro m
  by_cases hm : m < κ.faces.length
  · rw [κ.x_succ_of_lt hm]; omega
  · unfold FaceKind.x
    rw [List.take_of_length_le (Nat.le_of_not_lt hm),
      List.take_of_length_le (by omega)]

/-- Out of range, `d j = 0`. -/
theorem d_eq_zero_of_le (κ : FaceKind e) {j : ℕ} (hj : κ.faces.length ≤ j) :
    κ.d j = 0 := by
  unfold FaceKind.d
  rw [List.getElem?_eq_none hj]

end FaceKind

/-- L4(ii) arithmetic (the (SL≥2)(a) hand-off bound), degree half: every
residual degree is `< e` — the rightmost face since `b_k ≥ 2` gives
`d_k = L_k/b_k < L_k ≤ e`, every other face since the rightmost face's width
forces `L_j ≤ e − L_k ≤ e − 1`. -/
theorem faceDeg_bound (κ : FaceKind e) (he : 2 ≤ e) :
    ∀ j, κ.d j < e := by
  intro j
  rcases Nat.lt_or_ge j κ.faces.length with hj | hj
  · rw [κ.d_of_lt hj]
    have hLpos : 0 < (κ.faces[j].1 : ℕ) := (κ.faces[j].1).pos
    have hx : κ.x (j + 1) = κ.x j + (κ.faces[j].1 : ℕ) := κ.x_succ_of_lt hj
    have hxe : κ.x (j + 1) ≤ e := by
      have h := κ.x_mono (show j + 1 ≤ κ.faces.length from hj)
      rwa [κ.x_length] at h
    rcases Nat.lt_or_ge (j + 1) κ.faces.length with hj1 | hj1
    · -- a face to the right exists: `L_j ≤ e − L_{j+1} ≤ e − 1`, and `d_j ≤ L_j`
      have hx1 : κ.x (j + 2) = κ.x (j + 1) + (κ.faces[j + 1].1 : ℕ) :=
        κ.x_succ_of_lt hj1
      have hxe1 : κ.x (j + 2) ≤ e := by
        have h := κ.x_mono (show j + 2 ≤ κ.faces.length from hj1)
        rwa [κ.x_length] at h
      have hL1pos : 0 < (κ.faces[j + 1].1 : ℕ) := (κ.faces[j + 1].1).pos
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · -- the rightmost face: `b_j ≥ 2`, so `d_j < L_j ≤ e`
      obtain rfl : j = κ.faces.length - 1 := by omega
      have hne : κ.faces ≠ [] := by
        intro h0
        rw [h0] at hj
        simp at hj
      have hb : 2 ≤ ((κ.faces[κ.faces.length - 1]'(by omega)).2 : ℕ) := by
        have h := κ.hlast hne
        rwa [List.getLast_eq_getElem] at h
      exact lt_of_lt_of_le (Nat.div_lt_self hLpos hb) (by omega)
  · rw [κ.d_eq_zero_of_le hj]; omega

set_option linter.unusedVariables false in
/-- L4(ii) arithmetic (the (SL≥2)(a) hand-off bound): any residual factor of
multiplicity μ ≥ 2 and degree D with μ·D ≤ d_j has μ < e.
(`hμ` is part of the verbatim blueprint statement; the proof gets
`μ ≤ μ·D ≤ d_j < e` from `hD` alone, hence the linter opt-out.) -/
theorem handoff_mu_lt (κ : FaceKind e) (he : 2 ≤ e) {μ D j : ℕ}
    (hμ : 2 ≤ μ) (hle : μ * D ≤ κ.d j) (hD : 1 ≤ D) : μ < e :=
  lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right μ hD) hle)
    (faceDeg_bound κ he j)

/-- L4(i) arithmetic (the divisor-pattern half): a multiset of atoms (D, m) with
Σ D·m = e, not equal to {(1,e)}, has every atom's m < e. -/
theorem patt_mult_lt {e : ℕ} (he : 1 ≤ e) (π : Multiset (ℕ+ × ℕ+))
    (hdeg : (π.map fun x => (x.1 : ℕ) * x.2).sum = e)
    (hne : π ≠ {(1, ⟨e, he⟩)}) : ∀ x ∈ π, (x.2 : ℕ) < e := by
  rintro ⟨D, m⟩ hx
  show (m : ℕ) < e
  by_contra hcon
  have hcon' : e ≤ (m : ℕ) := Nat.le_of_not_lt hcon
  obtain ⟨π', rfl⟩ := Multiset.exists_cons_of_mem hx
  rw [Multiset.map_cons, Multiset.sum_cons] at hdeg
  replace hdeg : (D : ℕ) * (m : ℕ) +
      (π'.map fun x => (x.1 : ℕ) * (x.2 : ℕ)).sum = e := hdeg
  -- the atom (D, m) already exhausts the budget: D·m = e, and the rest sums to 0
  have hm_le : (m : ℕ) ≤ (D : ℕ) * (m : ℕ) := Nat.le_mul_of_pos_left _ D.pos
  have hDm_le : (D : ℕ) * (m : ℕ) ≤ e := le_of_le_of_eq (Nat.le_add_right _ _) hdeg
  have hAe : (D : ℕ) * (m : ℕ) = e := le_antisymm hDm_le (hcon'.trans hm_le)
  rw [hAe] at hdeg
  have hSum0 : (π'.map fun x => (x.1 : ℕ) * (x.2 : ℕ)).sum = 0 := by omega
  -- so the remaining pattern is empty (every atom contributes ≥ 1)
  have hπ' : π' = 0 := by
    by_contra hne0
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne0
    obtain ⟨π'', rfl⟩ := Multiset.exists_cons_of_mem hy
    rw [Multiset.map_cons, Multiset.sum_cons] at hSum0
    replace hSum0 : (y.1 : ℕ) * (y.2 : ℕ) +
        (π''.map fun x => (x.1 : ℕ) * (x.2 : ℕ)).sum = 0 := hSum0
    have hypos : 0 < (y.1 : ℕ) * (y.2 : ℕ) := Nat.mul_pos y.1.pos y.2.pos
    omega
  -- and D·m = e with m ≥ e forces m = e, D = 1: the excluded pattern {(1, e)}
  have hme : (m : ℕ) = e := le_antisymm (le_of_le_of_eq hm_le hAe) hcon'
  have hD1 : (D : ℕ) = 1 := by
    have h : (D : ℕ) * e = 1 * e := by
      rw [one_mul]
      conv_lhs => rw [← hme]
      exact hAe
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hDp : D = 1 := by
    apply PNat.coe_inj.mp
    simpa using hD1
  have hmp : m = ⟨e, he⟩ := by
    apply PNat.coe_inj.mp
    exact hme
  exact hne (by rw [hπ', hDp, hmp, Multiset.cons_zero])

/-! ## Unit II-P4: `BumpAdmissible`, `bump`, `cPrime`, `elemMove_Npg`, `one_le_cPrime`

L6b(i), the conditional elementary move (REV2 finding 8: `bump` requires
`BumpAdmissible`, so the last-face and ordering counterexamples are excluded).
Transcription notes: (a) the blueprint's `by omega` for the index bound
`κ.faces.length - 1 < κ.faces.length` cannot see `h : κ.faces ≠ []`, so the
(proof-irrelevant) Fin proof component is `Nat.sub_lt (List.length_pos_of_ne_nil h)
Nat.one_pos`, exactly as in the landed `SlopeTuple.hlt1`; (b) ℕ+-to-ℚ casts are
routed explicitly through ℕ, matching the landed `SlopeTuple`/`heights` cast forms.

Sketch (L6b(i) proof): the bump adds exactly `1` to slope `j` and changes nothing
else, so column `i` gains the width of the part of face `j` lying right of `i` —
`L_j` left of the face, `x_{j+1} − i` inside it, `0` right of it (`heights_bump`).
Each gain is a natural number, so ceilings translate (`Int.ceil_add_natCast`), and
summing the columns gives `x_j·L_j` (left region) plus the Gauss sum
`L_j(L_j+1)/2` (inside the face) — that is, `cPrime` (`sum_max_sub_max`). -/

/-- Admissibility of the elementary numerator change. It is deliberately false when
the change would break slope order or the terminal bound `s_k < 1`. -/
def SlopeTuple.BumpAdmissible {κ : FaceKind e} (s : SlopeTuple κ)
    (j : Fin κ.faces.length) : Prop :=
  let a' := fun i => if i = j then (s.a i : ℕ) + (κ.faces.get i).2 else s.a i
  (∀ i i', i < i' →
    (a' i' : ℚ) / (((κ.faces.get i').2 : ℕ) : ℚ) <
      (a' i : ℚ) / (((κ.faces.get i).2 : ℕ) : ℚ)) ∧
  (∀ h : κ.faces ≠ [],
    (a' ⟨κ.faces.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil h) Nat.one_pos⟩ : ℚ) /
      (((κ.faces.getLast h).2 : ℕ) : ℚ) < 1)

/-- The elementary numerator change at face `j`: `a_j ↦ a_j + b_j` (slope `+ 1`),
every other face unchanged. Coprimality is preserved (`gcd(a+b,b) = gcd(a,b)`);
the order and terminal fields are exactly the two `BumpAdmissible` clauses. -/
noncomputable def SlopeTuple.bump {κ : FaceKind e} (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : s.BumpAdmissible j) : SlopeTuple κ where
  a := fun i => if i = j then s.a i + (κ.faces.get i).2 else s.a i
  hcop := by
    intro i
    split_ifs with hij
    · rw [PNat.add_coe]
      exact Nat.coprime_add_self_left.mpr (s.hcop i)
    · exact s.hcop i
  hdesc := by
    intro i i' hlt
    have h1 := hj.1 i i' hlt
    simpa only [apply_ite (fun t : ℕ+ => (t : ℕ)), PNat.add_coe] using h1
  hlt1 := by
    intro h
    have h2 := hj.2 h
    simpa only [apply_ite (fun t : ℕ+ => (t : ℕ)), PNat.add_coe] using h2

@[simp] theorem SlopeTuple.bump_a {κ : FaceKind e} (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : s.BumpAdmissible j) (i : Fin κ.faces.length) :
    (s.bump j hj).a i = if i = j then s.a i + (κ.faces.get i).2 else s.a i := rfl

/-- L6b(i), conditional elementary move. -/
def cPrime (κ : FaceKind e) (j : Fin κ.faces.length) : ℕ :=
  κ.x j * (κ.faces.get j).1 +
    (κ.faces.get j).1 * ((κ.faces.get j).1 + 1) / 2

/-- Column-sum arithmetic for the elementary move: summing the width of the
face part right of column `i` (face spanning `[A, A+L] ⊆ [0, E]`) over the `E`
columns: `A` columns see the full width `L`, the columns inside the face see the
Gauss run `L, L−1, …, 1`, the columns right of the face see `0`. -/
theorem sum_max_sub_max (A L E : ℕ) (h : A + L ≤ E) :
    ∑ i ∈ Finset.range E, (max (A + L) i - max A i) =
      A * L + L * (L + 1) / 2 := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (A + L)) h,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le A) (Nat.le_add_right A L)]
  have h1 : ∑ i ∈ Finset.Ico 0 A, (max (A + L) i - max A i) = A * L := by
    have hterm : ∀ i ∈ Finset.Ico 0 A, max (A + L) i - max A i = L := by
      intro i hi
      have := (Finset.mem_Ico.mp hi).2
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, Nat.sub_zero,
      smul_eq_mul]
  have h2 : ∑ i ∈ Finset.Ico A (A + L), (max (A + L) i - max A i) =
      L * (L + 1) / 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hAL : A + L - A = L := by omega
    rw [hAL]
    have hterm : ∀ t ∈ Finset.range L,
        max (A + L) (A + t) - max A (A + t) = L - t := by
      intro t ht
      have := Finset.mem_range.mp ht
      omega
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_range_reflect (fun t => L - t) L]
    have hterm2 : ∀ t ∈ Finset.range L, L - (L - 1 - t) = t + 1 := by
      intro t ht
      have := Finset.mem_range.mp ht
      omega
    rw [Finset.sum_congr rfl hterm2]
    have hshift : ∑ t ∈ Finset.range L, (t + 1) = ∑ t ∈ Finset.range (L + 1), t := by
      rw [Finset.sum_range_succ', Nat.add_zero]
    rw [hshift, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]
  have h3 : ∑ i ∈ Finset.Ico (A + L) E, (max (A + L) i - max A i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := (Finset.mem_Ico.mp hi).1
    omega
  rw [h1, h2, h3, Nat.add_zero]

/-- The column identity of the elementary move: the bumped polygon's height at
column `i` is the old height plus the (integer) width of the part of face `j`
lying right of `i`. -/
theorem heights_bump (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : s.BumpAdmissible j) (i : ℕ) :
    heights κ (s.bump j hj) i =
      heights κ s i +
        ((max (κ.x ((j : ℕ) + 1)) i - max (κ.x (j : ℕ)) i : ℕ) : ℚ) := by
  unfold heights
  have hterm : ∀ jj : Fin κ.faces.length,
      (((s.bump j hj).a jj : ℕ) : ℚ) / (((κ.faces.get jj).2 : ℕ) : ℚ) *
          ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ) =
        ((s.a jj : ℕ) : ℚ) / (((κ.faces.get jj).2 : ℕ) : ℚ) *
            ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ) +
          (if jj = j
            then ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ)
            else 0) := by
    intro jj
    by_cases hij : jj = j
    · rw [if_pos hij, SlopeTuple.bump_a, if_pos hij, PNat.add_coe]
      have hb : (((κ.faces.get jj).2 : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (κ.faces.get jj).2.ne_zero
      push_cast
      field_simp
    · rw [if_neg hij, SlopeTuple.bump_a, if_neg hij, add_zero]
  rw [Finset.sum_congr rfl fun jj _ => hterm jj, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]

/-- L6b(i): the conditional elementary move raises `N(P)` by exactly
`c′_j = x_j·L_j + L_j(L_j+1)/2`. -/
theorem elemMove_Npg (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : s.BumpAdmissible j) :
    Npg κ (s.bump j hj) = Npg κ s + cPrime κ j := by
  have hx1 : κ.x ((j : ℕ) + 1) = κ.x (j : ℕ) + ((κ.faces.get j).1 : ℕ) := by
    simpa [List.get_eq_getElem] using κ.x_succ_of_lt j.isLt
  have hxe : κ.x (j : ℕ) + ((κ.faces.get j).1 : ℕ) ≤ e := by
    have h := κ.x_mono (show (j : ℕ) + 1 ≤ κ.faces.length from j.isLt)
    rw [κ.x_length] at h
    rw [← hx1]
    exact h
  have hcell : ∀ i ∈ Finset.range e,
      ⌈heights κ (s.bump j hj) i⌉ =
        ⌈heights κ s i⌉ +
          ((max (κ.x ((j : ℕ) + 1)) i - max (κ.x (j : ℕ)) i : ℕ) : ℤ) := by
    intro i _
    rw [heights_bump κ s j hj i, Int.ceil_add_natCast]
  unfold Npg
  rw [Finset.sum_congr rfl hcell, Finset.sum_add_distrib, ← Nat.cast_sum,
    hx1, sum_max_sub_max (κ.x (j : ℕ)) ((κ.faces.get j).1 : ℕ) e hxe]
  rfl

/-- L6b(i): every elementary move gain is at least 1 (`L_j ≥ 1`, so already the
Gauss-sum half is `≥ 1·2/2 = 1`). -/
theorem one_le_cPrime (κ : FaceKind e) (j : Fin κ.faces.length) :
    1 ≤ cPrime κ j := by
  have hL : 1 ≤ ((κ.faces.get j).1 : ℕ) := (κ.faces.get j).1.pos
  have h2 : 1 * 2 ≤ ((κ.faces.get j).1 : ℕ) * (((κ.faces.get j).1 : ℕ) + 1) :=
    Nat.mul_le_mul hL (by omega)
  have h1 : 1 ≤ ((κ.faces.get j).1 : ℕ) * (((κ.faces.get j).1 : ℕ) + 1) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
  calc 1 ≤ ((κ.faces.get j).1 : ℕ) * (((κ.faces.get j).1 : ℕ) + 1) / 2 := h1
    _ ≤ cPrime κ j := Nat.le_add_left _ _

/-! ## Unit II-P6: `gapStep`, `heights_gapStep`, `gapStep_Npg`

L6b(ii), the enumeration-affinity milestone. Blueprint §1.6 gives the unit as
`theorem gapStep_Npg ...` under its docstring; the body is realized per the
math source of record (`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§3, L6b(ii) proof), exactly as unit II-P5 did for `aMin_shift`:

* A unit step of the gap variable `w_j` (blueprint `w_1, …, w_{k−1}`;
  0-indexed: `j` with `(j : ℕ) + 1 < k`, so the terminal face is never
  stepped) evaluates, through the nested minima, to the SIMULTANEOUS
  one-period advance `a_{j′} ↦ a_{j′} + b_{j′}` on every face `j′ ≤ j`,
  faces right of `j` unchanged: on face `j` it is the elementary move
  (`w_j` counts periods above the minimum), and on each `j′ < j` the
  threshold slope `s_{j′+1}` grew by exactly 1, so the nested minimum
  shifts one full period (II-P5's `aMin_shift`) — certified here by
  `gapStep_aMin_shift`. This composite is `SlopeTuple.gapStep`; it is
  unconditionally admissible (each stepped slope grows by exactly 1, so
  the descending order survives, and the terminal bound is untouched).
* The ΔN law `gapStep_Npg`: `ΔN = c_j := Σ_{j′≤j} c′_{j′}`. Rather than a
  `Fin`-indexed right-to-left recursion through intermediate tuples, the
  composite is computed in one pass by the column identity
  `heights_gapStep` — column `i` gains `Σ_{j′≤j}` (width of face `j′`
  right of `i`), a natural number, so ceilings translate and II-P4's
  column-sum engine `sum_max_sub_max` evaluates each face's total to
  `c′_{j′}` (`cPrime`). Same arithmetic content as the blueprint sketch's
  composition of II-P4 across II-P5's shifted minima, without the
  intermediate-admissibility bookkeeping.
* `c_j ≥ 1` is `one_le_gapStep_gain` (the `j′ = j` term alone, by
  `one_le_cPrime`).
* "The vertex count k is w-independent" is type-level in this scaffold:
  `gapStep` returns a `SlopeTuple κ` over the SAME `κ`, and the vertex
  data — the abscissas `κ.x` and the count `κ.faces.length` — are
  functions of `κ` alone, never of the slope tuple (II-P4's note "the
  vertex columns are the x_j, fixed by the L's"). -/

/-- The unit gap-variable step at face `j` (`j` not terminal): every numerator
at `j′ ≤ j` advances one period (`a_{j′} ↦ a_{j′} + b_{j′}`, slope `+ 1`),
faces right of `j` unchanged. Coprimality is preserved
(`gcd(a+b,b) = gcd(a,b)`); the descending order survives because stepped
slopes all grow by exactly 1 and unstepped faces lie strictly right; the
terminal bound is untouched (`(j : ℕ) + 1 < k`). -/
noncomputable def SlopeTuple.gapStep {κ : FaceKind e} (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : (j : ℕ) + 1 < κ.faces.length) :
    SlopeTuple κ where
  a := fun i => if (i : ℕ) ≤ (j : ℕ) then s.a i + (κ.faces.get i).2 else s.a i
  hcop := by
    intro i
    split_ifs with hij
    · rw [PNat.add_coe]
      exact Nat.coprime_add_self_left.mpr (s.hcop i)
    · exact s.hcop i
  hdesc := by
    intro i i' hlt
    have h := s.hdesc i i' hlt
    have hvlt : (i : ℕ) < (i' : ℕ) := hlt
    have hbi : (0 : ℚ) < (((κ.faces.get i).2 : ℕ) : ℚ) := by
      exact_mod_cast (κ.faces.get i).2.pos
    have hbi' : (0 : ℚ) < (((κ.faces.get i').2 : ℕ) : ℚ) := by
      exact_mod_cast (κ.faces.get i').2.pos
    by_cases h2 : (i' : ℕ) ≤ (j : ℕ)
    · -- both faces stepped: each slope grew by exactly 1
      have h1 : (i : ℕ) ≤ (j : ℕ) := by omega
      rw [if_pos h1, if_pos h2, PNat.add_coe, PNat.add_coe]
      push_cast
      rw [add_div, add_div, div_self (ne_of_gt hbi), div_self (ne_of_gt hbi')]
      linarith
    · rw [if_neg h2]
      by_cases h1 : (i : ℕ) ≤ (j : ℕ)
      · -- left face stepped, right face not: s_{i'} < s_i < s_i + 1
        rw [if_pos h1, PNat.add_coe]
        push_cast
        rw [add_div, div_self (ne_of_gt hbi)]
        linarith
      · rw [if_neg h1]
        exact h
  hlt1 := by
    intro h
    have hcond : ¬ (κ.faces.length - 1 ≤ (j : ℕ)) := by omega
    rw [if_neg hcond]
    exact s.hlt1 h

@[simp] theorem SlopeTuple.gapStep_a {κ : FaceKind e} (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : (j : ℕ) + 1 < κ.faces.length)
    (i : Fin κ.faces.length) :
    (s.gapStep j hj).a i =
      if (i : ℕ) ≤ (j : ℕ) then s.a i + (κ.faces.get i).2 else s.a i := rfl

/-- The "through shifted minima" clause of L6b(ii) (II-P5 transported along
`gapStep`): if face `i ≤ j` sat at the least member of its residue class
above threshold `t` (`aMin`), then after the unit gap step it sits at the
least class member above `t + 1` — its new numerator IS the shifted nested
minimum, so the step performs the elementary move on face `i` as well. -/
theorem gapStep_aMin_shift (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : (j : ℕ) + 1 < κ.faces.length)
    (i : Fin κ.faces.length) (hij : (i : ℕ) ≤ (j : ℕ)) (r : ℤ) (t : ℚ)
    (hmin : ((s.a i : ℕ) : ℤ) = aMin (κ.faces.get i).2 r t) :
    (((s.gapStep j hj).a i : ℕ) : ℤ) = aMin (κ.faces.get i).2 r (t + 1) := by
  rw [aMin_shift, ← hmin, SlopeTuple.gapStep_a, if_pos hij, PNat.add_coe]
  push_cast
  ring

/-- The column identity of the unit gap step: column `i` gains the sum, over
the stepped faces `j′ ≤ j`, of the (integer) width of the part of face `j′`
lying right of `i` — each stepped face contributes its II-P4 column gain. -/
theorem heights_gapStep (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : (j : ℕ) + 1 < κ.faces.length) (i : ℕ) :
    heights κ (s.gapStep j hj) i =
      heights κ s i +
        ((∑ j' ∈ Finset.univ.filter
            (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
          (max (κ.x ((j' : ℕ) + 1)) i - max (κ.x (j' : ℕ)) i) : ℕ) : ℚ) := by
  unfold heights
  have hterm : ∀ jj : Fin κ.faces.length,
      (((s.gapStep j hj).a jj : ℕ) : ℚ) / (((κ.faces.get jj).2 : ℕ) : ℚ) *
          ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ) =
        ((s.a jj : ℕ) : ℚ) / (((κ.faces.get jj).2 : ℕ) : ℚ) *
            ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ) +
          (if (jj : ℕ) ≤ (j : ℕ)
            then ((max (κ.x ((jj : ℕ) + 1)) i - max (κ.x (jj : ℕ)) i : ℕ) : ℚ)
            else 0) := by
    intro jj
    by_cases hij : (jj : ℕ) ≤ (j : ℕ)
    · rw [if_pos hij, SlopeTuple.gapStep_a, if_pos hij, PNat.add_coe]
      have hb : (((κ.faces.get jj).2 : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (κ.faces.get jj).2.ne_zero
      push_cast
      field_simp
    · rw [if_neg hij, SlopeTuple.gapStep_a, if_neg hij, add_zero]
  rw [Nat.cast_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun jj _ => hterm jj

/-- L6b(ii), enumeration affinity: a unit step of the gap variable w_j performs the
elementary move on face j AND (through shifted minima) on every j′ < j:
ΔN = c_j := Σ_{j′≤j} c′_{j′} ≥ 1; the vertex count k is w-independent.
(The `≥ 1` clause is `one_le_gapStep_gain` below; k-independence is carried by
the type — `gapStep` fixes `κ`, and the vertex data `κ.x`/`κ.faces.length`
are functions of `κ` alone.) -/
theorem gapStep_Npg (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) (hj : (j : ℕ) + 1 < κ.faces.length) :
    Npg κ (s.gapStep j hj) = Npg κ s +
      ((∑ j' ∈ Finset.univ.filter
          (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
        cPrime κ j' : ℕ) : ℤ) := by
  have hcell : ∀ i ∈ Finset.range e,
      ⌈heights κ (s.gapStep j hj) i⌉ =
        ⌈heights κ s i⌉ +
          ((∑ j' ∈ Finset.univ.filter
              (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
            (max (κ.x ((j' : ℕ) + 1)) i - max (κ.x (j' : ℕ)) i) : ℕ) : ℤ) := by
    intro i _
    rw [heights_gapStep κ s j hj i, Int.ceil_add_natCast]
  have hswap : ∑ i ∈ Finset.range e,
      (∑ j' ∈ Finset.univ.filter
          (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
        (max (κ.x ((j' : ℕ) + 1)) i - max (κ.x (j' : ℕ)) i)) =
      ∑ j' ∈ Finset.univ.filter
          (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
        cPrime κ j' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have hx1 : κ.x ((j' : ℕ) + 1) = κ.x (j' : ℕ) + ((κ.faces.get j').1 : ℕ) := by
      simpa [List.get_eq_getElem] using κ.x_succ_of_lt j'.isLt
    have hxe : κ.x (j' : ℕ) + ((κ.faces.get j').1 : ℕ) ≤ e := by
      have h := κ.x_mono (show (j' : ℕ) + 1 ≤ κ.faces.length from j'.isLt)
      rw [κ.x_length] at h
      rw [← hx1]
      exact h
    rw [hx1, sum_max_sub_max (κ.x (j' : ℕ)) ((κ.faces.get j').1 : ℕ) e hxe]
    rfl
  unfold Npg
  rw [Finset.sum_congr rfl hcell, Finset.sum_add_distrib, ← Nat.cast_sum, hswap]

/-- L6b(ii): every unit gap step gains at least 1 — already the `j′ = j` term
of `c_j` is `c′_j ≥ 1` (`one_le_cPrime`). -/
theorem one_le_gapStep_gain (κ : FaceKind e) (j : Fin κ.faces.length) :
    1 ≤ ∑ j' ∈ Finset.univ.filter
        (fun j' : Fin κ.faces.length => (j' : ℕ) ≤ (j : ℕ)),
      cPrime κ j' :=
  le_trans (one_le_cPrime κ j)
    (Finset.single_le_sum (f := fun j' => cPrime κ j')
      (fun _ _ => Nat.zero_le _) (by simp))

end LeanUrat.Scaffold
