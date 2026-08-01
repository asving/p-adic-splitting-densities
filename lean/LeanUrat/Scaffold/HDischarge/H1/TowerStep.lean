/-
HDISCHARGE_H1 §5.3 — `H1/TowerStep.lean`: H1-U8 (`kp_step`), the door-1 core
(math source blueprint §2.2 KP-STEP).  Statement transcribed VERBATIM from
`lean/blueprints/HDISCHARGE_H1.md` §5.3 (REV 2, re-probed 2026-08-05 with the
`DevBound` row; findings 10/11 discipline: the hypothesis block is exactly the
displayed one — no enlargement, no weakening).

H1-U8 honesty ledger (what is PROVED vs what is STAGING):
* U8a (`u8_key_prime`) — PROVED: `in(Φ')` is prime in `gr(w')` at ANY stage
  carrying a `GenuineStageModel`.  ROUTE DEVIATION NOTE (the U6 precedent): the
  blueprint's sketch "Irreducible ν.ψ → Prime ψhom via Θ/isLoc + (s4a)
  localization avoidance" was probed and NOT taken — the model's localization
  monoid `homMon` CONTAINS the key's initial form (`homMon_gen`), so `in(Φ')`
  is INVERTED in `Lo` and primeness cannot pull back along `gr ↪ gr_loc`
  (avoidance fails at the key itself; same obstruction Order1's header records
  for the U6 graded halves).  Instead KEY-g's weighted-Gauss/bottom-monomial
  argument is transported to the state INTRINSICALLY, from the Stage laws
  alone: the honest state analogue of (s4a) is the DISPLAYED support-window
  pair `u8_supp_key` (every `z`-exponent of `σ'.R f` sits at a minimizing
  development slot: `e'·n = j − t'·w f`, `j ≥ 0`) + `u8_bot` (a minimizing
  slot 0 pins an ATTAINED bottom monomial) — `T^{s'}`-multiples of realizable
  residuals avoid the bottom slot (`u8_nodvd_of_min0`: the transported
  "Φ̄₀ ∤ ψ_hom" step), which is the localization-avoidance content at the
  state.  `Irreducible ν.ψ` is NOT consumed: the Lean `KPBlock` pins `ψhom`
  only up to a `Gr`-unit of `in(Φ')` (we take `ψhom := in(Φ')`, unit `1`), and
  the key-polynomial primeness of `in(Φ')` is already forced by the stage's
  own (S1)/(S2)/(S5)/DEF-4 laws (`hK1`/`hS5`/`hStretch`/`hbez`) through the
  genuine graded model — ψ-irreducibility lives in the A-M2/B-M1 non-vacuity
  chain (what makes `(σ', M)` instantiable), not in this implication.
* U8b (degree block) — STAGING ONLY [REV 2, finding 11]: with `ψhom = in(Φ')`
  and unit `1`, `kpa_block` is LITERALLY the `DevBound` row `D.block`.  This
  discharges NOTHING: member (b) retires only with OP-B1 PROVED (the row
  derived, never assumed).
* U8c (`kp_step`) — assembly.  DISCLOSURE: the binders `ν`, `hΦ`, `he`, `hh`,
  `hprev` are not consumed by this proof (they are the blueprint's math-face
  keying of the block to the creating read; the statement is verbatim-fenced).
  Never cite this theorem as evidence for (H1) beyond what its binders carry:
  non-vacuity of `M` at depth ≥ 2 is the OPEN math leaf A-M2.
-/
import LeanUrat.Scaffold.HDischarge.H1.Order1
import LeanUrat.Moves.L0_FactA_exists

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ## A. Laurent toolkit: shift and anchored-minimum convolution -/

section Laurent

variable {K : Type*} [Field K]

/-- `(T a * x) n = x (n − a)` — the Laurent shift, from the monoid-algebra
single-multiplication formula. -/
lemma u8_T_mul_apply (a : ℤ) (x : LaurentPolynomial K) (n : ℤ) :
    (LaurentPolynomial.T a * x : LaurentPolynomial K) n = x (n - a) := by
  rw [show (LaurentPolynomial.T a : LaurentPolynomial K) = AddMonoidAlgebra.single a 1 from rfl,
    AddMonoidAlgebra.single_mul_apply, one_mul]
  congr 1
  omega

/-- **Anchored-minimum convolution** (the general-minimum form of Order1's
`u5_bot_coeff_mul`): if `supp x ⊆ [n₀, ∞)` and `supp y ⊆ [m₀, ∞)`, the only
convolution cell landing at `n₀ + m₀` is `(n₀, m₀)`. -/
lemma u8_min_coeff_mul (x y : LaurentPolynomial K) (n₀ m₀ : ℤ)
    (hx : ∀ n ∈ x.support, n₀ ≤ n) (hy : ∀ m ∈ y.support, m₀ ≤ m) :
    (x * y) (n₀ + m₀) = x n₀ * y m₀ := by
  classical
  rw [AddMonoidAlgebra.mul_apply]
  rw [Finsupp.sum, Finset.sum_eq_single n₀]
  · rw [Finsupp.sum, Finset.sum_eq_single m₀]
    · simp
    · intro b hb hbne
      have hb0 : m₀ ≤ b := hy b hb
      rw [if_neg (by omega)]
    · intro h0
      rw [Finsupp.notMem_support_iff.mp h0]
      simp
  · intro a ha hane
    have ha0 : n₀ ≤ a := hx a ha
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb0 : m₀ ≤ b := hy b hb
    rw [if_neg (by omega)]
  · intro h0
    rw [Finsupp.notMem_support_iff.mp h0, Finsupp.sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    simp

end Laurent

/-! ## B. The state residual of a development: the minimizing-slot formula

The (s1)/(s2) content at the Lean face: for ANY `Φ'`-development at ANY stage,
the residual `σ'.R f` recomposes from EXACTLY the minimizing slots, each
contributing its (S5) digit monomial marched by `T^{s'·j}`.  This is the
"marched homogenization" seen through `(R, w)`. -/

section RDev

open scoped Classical

variable (σ' : Stage p F)

/-- Truncated slot family: the development witness of a partial sum. -/
private lemma u8_trunc_dev (B : ℕ → Polynomial ℤ_[p])
    (hdeg : ∀ j, (B j).degree < σ'.Φ.degree) (m : ℕ) :
    Moves.IsDevelopment σ'.Φ (∑ j ∈ Finset.range m, B j * σ'.Φ ^ j)
      (fun j => if j < m then B j else 0) m := by
  refine ⟨fun j => ?_, fun j hj => by simp [Nat.not_lt.mpr hj], ?_⟩
  · by_cases hjm : j < m
    · simpa [hjm] using hdeg j
    · simpa [hjm] using lt_of_le_of_lt bot_le (stage_degree_pos σ')
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp [Finset.mem_range.mp hj]

/-- Zero partial sums have all-zero slots (Fact A uniqueness). -/
private lemma u8_zero_slots (B : ℕ → Polynomial ℤ_[p])
    (hdeg : ∀ j, (B j).degree < σ'.Φ.degree) (m : ℕ)
    (h0 : (∑ j ∈ Finset.range m, B j * σ'.Φ ^ j) = 0) :
    ∀ j, j < m → B j = 0 := by
  intro j hj
  have huniq := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
    σ'.hmonic m _ (fun k => if k < m then B k else 0) (u8_trunc_dev σ' B hdeg m) j
  rw [h0] at huniq
  simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at huniq
  simpa [hj] using huniq

/-- Weight of a nonzero single slot: `w (B_j·Φ'^j) = w B_j + j·w Φ'`. -/
private lemma u8_slot_w (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (j : ℕ) :
    σ'.w (B * σ'.Φ ^ j) = σ'.w B + (j : ℤ) * σ'.w σ'.Φ := by
  have hΦne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  rw [σ'.hwmul B (σ'.Φ ^ j) hB (pow_ne_zero j hΦne), stage_w_pow σ' σ'.Φ hΦne j]

/-- Residual of a nonzero single slot: `R (B_j·Φ'^j) = R B_j · T (s'·j)`. -/
private lemma u8_slot_R (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (j : ℕ) :
    σ'.R (B * σ'.Φ ^ j) = σ'.R B * LaurentPolynomial.T (σ'.s * j) := by
  have hΦne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  rw [σ'.hRmul B (σ'.Φ ^ j) hB (pow_ne_zero j hΦne), stage_R_pow σ' σ'.Φ hΦne j,
    σ'.hRΦ, LaurentPolynomial.T_pow, mul_comm (j : ℤ) σ'.s]

/-- **The minimizing-slot recomposition** of the state residual: for a partial
sum of a slot family (all slots coefficients), the residual is the sum of the
per-slot residuals over EXACTLY the weight-minimizing nonzero slots. -/
lemma u8_R_dev (B : ℕ → Polynomial ℤ_[p])
    (hdeg : ∀ j, (B j).degree < σ'.Φ.degree) :
    ∀ m, (∑ j ∈ Finset.range m, B j * σ'.Φ ^ j) ≠ 0 →
      σ'.R (∑ j ∈ Finset.range m, B j * σ'.Φ ^ j) =
        ∑ j ∈ Finset.range m,
          if B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ =
              σ'.w (∑ i ∈ Finset.range m, B i * σ'.Φ ^ i)
          then σ'.R (B j) * LaurentPolynomial.T (σ'.s * j) else 0 := by
  have hΦne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  intro m
  induction m with
  | zero => intro h0; simp at h0
  | succ m ih =>
    intro hne
    set Sm := ∑ j ∈ Finset.range m, B j * σ'.Φ ^ j with hSm
    set G := B m * σ'.Φ ^ m with hG
    have hsplit : ∑ j ∈ Finset.range (m + 1), B j * σ'.Φ ^ j = Sm + G :=
      Finset.sum_range_succ _ m
    by_cases hBm : B m = 0
    · -- silent top slot: the sum and all conditions are those of `Sm`
      have hGz : G = 0 := by rw [hG, hBm, zero_mul]
      have hS : ∑ j ∈ Finset.range (m + 1), B j * σ'.Φ ^ j = Sm := by
        rw [hsplit, hGz, add_zero]
      rw [hS] at hne ⊢
      rw [ih hne, Finset.sum_range_succ, if_neg (by simp [hBm]), add_zero]
    · have hGne : G ≠ 0 := mul_ne_zero hBm (pow_ne_zero m hΦne)
      have hwG : σ'.w G = σ'.w (B m) + (m : ℤ) * σ'.w σ'.Φ := u8_slot_w σ' (B m) hBm m
      have hRG : σ'.R G = σ'.R (B m) * LaurentPolynomial.T (σ'.s * m) :=
        u8_slot_R σ' (B m) hBm m
      by_cases hSz : Sm = 0
      · -- all lower slots zero: single-slot residual
        have hzero : ∀ j, j < m → B j = 0 := u8_zero_slots σ' B hdeg m hSz
        have hS : ∑ j ∈ Finset.range (m + 1), B j * σ'.Φ ^ j = G := by
          rw [hsplit, hSz, zero_add]
        rw [hS, hRG, Finset.sum_range_succ]
        have hlow : ∀ j ∈ Finset.range m,
            (if B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w G
             then σ'.R (B j) * LaurentPolynomial.T (σ'.s * j) else 0) = 0 := by
          intro j hj
          rw [if_neg]
          rintro ⟨hBj, -⟩
          exact hBj (hzero j (Finset.mem_range.mp hj))
        rw [Finset.sum_congr rfl hlow, Finset.sum_const_zero, zero_add,
          if_pos ⟨hBm, by rw [hwG]⟩]
      · -- genuine step: trichotomy on the weights
        have hSne : Sm + G ≠ 0 := by rw [← hsplit]; exact hne
        -- hK1 data for `Sm` and for the (m+1)-sum
        obtain ⟨hSlow, jS, hjSm, hjSnz, hjSeq⟩ :=
          σ'.hK1 Sm (fun j => if j < m then B j else 0) m hSz (u8_trunc_dev σ' B hdeg m)
        obtain ⟨hTlow, jT, hjTm, hjTnz, hjTeq⟩ :=
          σ'.hK1 (Sm + G) (fun j => if j < m + 1 then B j else 0) (m + 1)
            hSne (by rw [← hsplit]; exact u8_trunc_dev σ' B hdeg (m + 1))
        have hjSnz' : B jS ≠ 0 := by simpa [hjSm] using hjSnz
        have hjSeq' : σ'.w Sm = σ'.w (B jS) + (jS : ℤ) * σ'.w σ'.Φ := by
          simpa [hjSm] using hjSeq
        -- upper bounds: the (m+1)-weight is ≤ both `w Sm` and `w G`
        have hT_le_S : σ'.w (Sm + G) ≤ σ'.w Sm := by
          have := hTlow jS (by omega) (by simpa [hjSm, Nat.lt_succ_of_lt hjSm] using hjSnz')
          rw [hjSeq']
          simpa [Nat.lt_succ_of_lt hjSm, hjSm] using this
        have hT_le_G : σ'.w (Sm + G) ≤ σ'.w G := by
          have := hTlow m (by omega) (by simpa [Nat.lt_succ_self] using hBm)
          rw [hwG]
          simpa [Nat.lt_succ_self] using this
        -- lower bound: ultrametric
        have hT_ge : min (σ'.w Sm) (σ'.w G) ≤ σ'.w (Sm + G) :=
          σ'.hwult Sm G hSz hGne hSne
        rcases lt_trichotomy (σ'.w Sm) (σ'.w G) with hlt | heq | hgt
        · -- `Sm` strictly lighter: `R` and the minimizing slots are `Sm`'s
          have hwT : σ'.w (Sm + G) = σ'.w Sm := le_antisymm hT_le_S (by
            have hm : min (σ'.w Sm) (σ'.w G) = σ'.w Sm := min_eq_left (le_of_lt hlt)
            omega)
          have hRT : σ'.R (Sm + G) = σ'.R Sm := σ'.hRlt Sm G hSz hGne hSne (by omega)
          rw [hsplit, hRT, ih hSz, hwT, Finset.sum_range_succ,
            if_neg (by rintro ⟨-, h⟩; rw [← hwG] at h; omega), add_zero]
        · -- equal weights: `hRadd` recomposition, slots merge
          have hwT : σ'.w (Sm + G) = σ'.w Sm := le_antisymm hT_le_S (by omega)
          have hRT : σ'.R (Sm + G) = σ'.R Sm + σ'.R G :=
            σ'.hRadd Sm G hSz hGne hSne heq hwT
          rw [hsplit, hRT, ih hSz, hwT, Finset.sum_range_succ,
            if_pos ⟨hBm, by rw [← hwG]; exact heq.symm⟩, hRG]
        · -- `G` strictly lighter: single fresh minimizing slot `m`
          have hwT : σ'.w (Sm + G) = σ'.w G := le_antisymm hT_le_G (by
            have hm : min (σ'.w Sm) (σ'.w G) = σ'.w G := min_eq_right (le_of_lt hgt)
            omega)
          have hRT : σ'.R (Sm + G) = σ'.R G := by
            rw [add_comm] at hSne ⊢
            exact σ'.hRlt G Sm hGne hSz hSne (by omega)
          rw [hsplit, hRT, hRG, hwT, Finset.sum_range_succ, if_pos ⟨hBm, hwG.symm⟩]
          have hlow : ∀ j ∈ Finset.range m,
              (if B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w G
               then σ'.R (B j) * LaurentPolynomial.T (σ'.s * j) else 0) = 0 := by
            intro j hj
            have hjm := Finset.mem_range.mp hj
            rw [if_neg]
            rintro ⟨hBj, hwj⟩
            have hjlow := hSlow j hjm (by simpa [hjm] using hBj)
            simp only [hjm, if_pos] at hjlow
            omega
          rw [Finset.sum_congr rfl hlow, Finset.sum_const_zero, zero_add]

/-! ## C. The state support window (the displayed (s4a)-analogue) -/

/-- Shared exponent arithmetic: a minimizing slot `j` contributes the monomial
exponent `n_j` with `e'·n_j = j − t'·(w f)` (Bézout + DEF-4 stretch). -/
private lemma u8_exp_key (Bj : Polynomial ℤ_[p]) (hBj : Bj ≠ 0)
    (hin : inC σ'.Φ Bj) (j : ℕ) (wf : ℤ)
    (hmin : σ'.w Bj + (j : ℤ) * σ'.w σ'.Φ = wf) :
    (σ'.e : ℤ) * (-σ'.t * σ'.wPrev Bj + σ'.s * (j : ℤ)) = (j : ℤ) - σ'.t * wf := by
  have hwB : σ'.w Bj = (σ'.e : ℤ) * σ'.wPrev Bj := σ'.hStretch Bj hBj hin
  have h3 : (σ'.e : ℤ) * σ'.s = 1 - (σ'.h : ℤ) * σ'.t := by linarith [σ'.hbez]
  have e3 : σ'.w Bj = wf - (j : ℤ) * (σ'.h : ℤ) := by rw [σ'.hwΦ] at hmin; linarith
  have hcalc : (σ'.e : ℤ) * (-σ'.t * σ'.wPrev Bj + σ'.s * (j : ℤ))
      = -σ'.t * ((σ'.e : ℤ) * σ'.wPrev Bj) + ((σ'.e : ℤ) * σ'.s) * (j : ℤ) := by ring
  rw [← hwB, h3, e3] at hcalc
  rw [hcalc]; ring

/-- **(s4a) at the state — the support window** (KEY-g's `hwin` transported):
every `z`-exponent of `σ'.R f` is keyed to a minimizing development slot,
`e'·n = j − t'·(w f)` with `j ≥ 0` — the state analogue of "support ⊆ [0, ∞)". -/
lemma u8_supp_key (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hdev : Moves.IsDevelopment σ'.Φ f B N) (hf : f ≠ 0) :
    ∀ n ∈ (σ'.R f).support, ∃ j : ℕ, j < N ∧ B j ≠ 0 ∧
      σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w f ∧
      (σ'.e : ℤ) * n = (j : ℤ) - σ'.t * σ'.w f := by
  obtain ⟨hdeg, hvan, hsum⟩ := hdev
  have hform := u8_R_dev σ' B hdeg N (by rw [← hsum]; exact hf)
  rw [← hsum] at hform
  -- the Finsupp-world retyping of the formula (the L2_slotDecomp crossing pattern)
  have hform' : (σ'.R f : ℤ →₀ ↥σ'.K)
      = (∑ j ∈ Finset.range N,
          (if B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w f
           then σ'.R (B j) * LaurentPolynomial.T (σ'.s * (j : ℤ)) else 0
           : LaurentPolynomial ↥σ'.K) : ℤ →₀ ↥σ'.K) := hform
  intro n hn
  rw [Finsupp.mem_support_iff] at hn
  rw [hform', Finsupp.finsetSum_apply] at hn
  obtain ⟨j, hjmem, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rcases Classical.em (B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w f) with
    hcond | hcond
  · rw [if_pos hcond] at hjne
    obtain ⟨hBj, hmin⟩ := hcond
    obtain ⟨c, hc⟩ := σ'.hS5 (B j) hBj (hdeg j)
    rw [hc, LaurentPolynomial.mul_T_assoc,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply] at hjne
    rcases Classical.em (-σ'.t * σ'.wPrev (B j) + σ'.s * (j : ℤ) = n) with hn' | hn'
    · refine ⟨j, Finset.mem_range.mp hjmem, hBj, hmin, ?_⟩
      rw [← hn']
      exact u8_exp_key σ' (B j) hBj (hdeg j) j (σ'.w f) hmin
    · rw [if_neg hn'] at hjne
      exact absurd rfl hjne
  · rw [if_neg hcond] at hjne
    exact absurd rfl hjne

/-- **The attained bottom monomial**: if slot `0` is minimizing, `σ'.R f` has a
NONZERO coefficient at the bottom exponent `n₀ = −t'·wPrev(B₀)`, the bound
`e'·n₀ = −t'·(w f)` is attained there, and `n₀` is the support minimum. -/
lemma u8_bot (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hdev : Moves.IsDevelopment σ'.Φ f B N) (hf : f ≠ 0)
    (hB0 : B 0 ≠ 0) (hw0 : σ'.w (B 0) = σ'.w f) :
    (σ'.R f) (-σ'.t * σ'.wPrev (B 0)) ≠ 0 ∧
    (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0)) = -σ'.t * σ'.w f ∧
    ∀ n ∈ (σ'.R f).support, -σ'.t * σ'.wPrev (B 0) ≤ n := by
  obtain ⟨hdeg, hvan, hsum⟩ := hdev
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0] at hsum; simp at hsum; exact absurd hsum hf
    · exact h0
  have hii : (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0)) = -σ'.t * σ'.w f := by
    have hstr := σ'.hStretch (B 0) hB0 (hdeg 0)
    have hre : (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0))
        = -σ'.t * ((σ'.e : ℤ) * σ'.wPrev (B 0)) := by ring
    rw [hre, ← hstr, hw0]
  refine ⟨?_, hii, ?_⟩
  · -- the bottom coefficient is the slot-0 digit
    have hform := u8_R_dev σ' B hdeg N (by rw [← hsum]; exact hf)
    rw [← hsum] at hform
    have hform' : (σ'.R f : ℤ →₀ ↥σ'.K)
        = (∑ j ∈ Finset.range N,
            (if B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w f
             then σ'.R (B j) * LaurentPolynomial.T (σ'.s * (j : ℤ)) else 0
             : LaurentPolynomial ↥σ'.K) : ℤ →₀ ↥σ'.K) := hform
    obtain ⟨c, hc⟩ := σ'.hS5 (B 0) hB0 (hdeg 0)
    have hval : (σ'.R f : ℤ →₀ ↥σ'.K) (-σ'.t * σ'.wPrev (B 0)) = (c : ↥σ'.K) := by
      rw [hform', Finsupp.finsetSum_apply, Finset.sum_eq_single 0]
      · show ((if B 0 ≠ 0 ∧ σ'.w (B 0) + ((0 : ℕ) : ℤ) * σ'.w σ'.Φ = σ'.w f
             then σ'.R (B 0) * LaurentPolynomial.T (σ'.s * ((0 : ℕ) : ℤ)) else 0
             : LaurentPolynomial ↥σ'.K)) (-σ'.t * σ'.wPrev (B 0)) = (c : ↥σ'.K)
        have hcond0 : B 0 ≠ 0 ∧ σ'.w (B 0) + ((0 : ℕ) : ℤ) * σ'.w σ'.Φ = σ'.w f :=
          ⟨hB0, by simp [hw0]⟩
        rw [if_pos hcond0, hc, LaurentPolynomial.mul_T_assoc,
          ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply,
          if_pos (by push_cast; ring)]
      · intro j hjmem hjne0
        rcases Classical.em (B j ≠ 0 ∧ σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ = σ'.w f) with
          hcond | hcond
        · rw [if_pos hcond]
          obtain ⟨hBj, hmin⟩ := hcond
          obtain ⟨c', hc'⟩ := σ'.hS5 (B j) hBj (hdeg j)
          rw [hc', LaurentPolynomial.mul_T_assoc,
            ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply, if_neg]
          intro heq
          have hej := congrArg (fun z : ℤ => (σ'.e : ℤ) * z) heq
          rw [u8_exp_key σ' (B j) hBj (hdeg j) j (σ'.w f) hmin, hii] at hej
          have hj0 : (j : ℤ) = 0 := by linarith
          exact hjne0 (by exact_mod_cast hj0)
        · rw [if_neg hcond]
          rfl
      · intro h0mem
        exact absurd (Finset.mem_range.mpr hNpos) h0mem
    rw [hval]
    exact c.ne_zero
  · -- support minimality
    intro n hn
    obtain ⟨j, hjN, hBj, hmin, hje⟩ :=
      u8_supp_key σ' f B N ⟨hdeg, hvan, hsum⟩ hf n hn
    have hepos : (0 : ℤ) < (σ'.e : ℤ) := by have := σ'.he; omega
    by_contra hlt
    push_neg at hlt
    have hmul : (σ'.e : ℤ) * n < (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0)) :=
      mul_lt_mul_of_pos_left hlt hepos
    rw [hje, hii] at hmul
    have : (j : ℤ) < 0 := by linarith
    omega

/-! ## D. The divisibility dichotomy at the state key -/

/-- If slot `0` of a development is NOT minimizing (zero, or strictly heavier
than the attained minimum), the key initial form divides `in(f)` — the split
`f = B₀ + Φ'·q` with `in(f) = in(Φ')·in(q)`. -/
lemma u8_div_of_min_pos (M : GenuineStageModel σ') (f : Polynomial ℤ_[p])
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : Moves.IsDevelopment σ'.Φ f B N)
    (hf : f ≠ 0) (hnot : ¬ (B 0 ≠ 0 ∧ σ'.w (B 0) = σ'.w f)) :
    letI := M.Rg.ring; M.S.initialForm σ'.Φ ∣ M.S.initialForm f := by
  letI := M.Rg.ring
  obtain ⟨hdeg, hvan, hsum⟩ := hdev
  have hΦne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0] at hsum; simp at hsum; exact absurd hsum hf
    · exact h0
  -- split off slot 0:  f = B₀ + Φ'·q
  set q : Polynomial ℤ_[p] := ∑ j ∈ Finset.range (N - 1), B (j + 1) * σ'.Φ ^ j with hq
  have hqdev : Moves.IsDevelopment σ'.Φ q (fun j => B (j + 1)) (N - 1) :=
    ⟨fun j => hdeg (j + 1), fun j hj => hvan (j + 1) (by omega), rfl⟩
  have hfsplit : f = B 0 + σ'.Φ * q := by
    rw [hsum, show N = (N - 1) + 1 from by omega, Finset.sum_range_succ']
    rw [pow_zero, mul_one, add_comm]
    congr 1
    rw [hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  -- hK1 on f: the attained minimum sits at a slot ≥ 1
  obtain ⟨hflow, j₀, hj₀N, hj₀nz, hj₀eq⟩ := σ'.hK1 f B N hf ⟨hdeg, hvan, hsum⟩
  have hj₀nz' : B j₀ ≠ 0 := hj₀nz
  have hj₀eq' : σ'.w f = σ'.w (B j₀) + (j₀ : ℤ) * σ'.w σ'.Φ := hj₀eq
  have hj₀pos : 1 ≤ j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | h0
    · exfalso
      apply hnot
      refine ⟨by rwa [h0] at hj₀nz', ?_⟩
      rw [h0] at hj₀eq'
      simp at hj₀eq'
      omega
    · exact h0
  have hqne : q ≠ 0 := by
    intro h0
    have hz := u8_zero_slots σ' (fun j => B (j + 1)) (fun j => hdeg (j + 1)) (N - 1)
      (by rw [← hq]; exact h0) (j₀ - 1) (by omega)
    apply hj₀nz'
    rwa [show j₀ - 1 + 1 = j₀ from by omega] at hz
  -- weights: w q = w f − w Φ'
  obtain ⟨hqlow, jq, hjqN, hjqnz, hjqeq⟩ :=
    σ'.hK1 q (fun j => B (j + 1)) (N - 1) hqne hqdev
  have hjqnz' : B (jq + 1) ≠ 0 := hjqnz
  have hjqeq' : σ'.w q = σ'.w (B (jq + 1)) + (jq : ℤ) * σ'.w σ'.Φ := hjqeq
  have hle : σ'.w q ≤ σ'.w f - σ'.w σ'.Φ := by
    have h1 : σ'.w q ≤ σ'.w (B ((j₀ - 1) + 1)) + ((j₀ - 1 : ℕ) : ℤ) * σ'.w σ'.Φ :=
      hqlow (j₀ - 1) (by omega) (by
        show B ((j₀ - 1) + 1) ≠ 0
        rwa [show j₀ - 1 + 1 = j₀ from by omega])
    rw [show j₀ - 1 + 1 = j₀ from by omega,
      show ((j₀ - 1 : ℕ) : ℤ) = (j₀ : ℤ) - 1 from by omega] at h1
    linarith [h1, hj₀eq']
  have hge : σ'.w f - σ'.w σ'.Φ ≤ σ'.w q := by
    have h2 : σ'.w f ≤ σ'.w (B (jq + 1)) + ((jq + 1 : ℕ) : ℤ) * σ'.w σ'.Φ :=
      hflow (jq + 1) (by omega) hjqnz'
    rw [show ((jq + 1 : ℕ) : ℤ) = (jq : ℤ) + 1 from by omega] at h2
    linarith [h2, hjqeq']
  have hwΦq : σ'.w (σ'.Φ * q) = σ'.w f := by
    rw [σ'.hwmul σ'.Φ q hΦne hqne]
    omega
  rcases Classical.em (B 0 = 0) with hB00 | hB00
  · -- f = Φ'·q exactly
    have hfq : f = σ'.Φ * q := by rw [hfsplit, hB00, zero_add]
    rw [hfq, M.Rg.if_mul σ'.Φ q hΦne hqne]
    exact dvd_mul_right _ _
  · -- B₀ strictly heavier: the initial form ignores it
    have hwlt : σ'.w f < σ'.w (B 0) := by
      have h3 : σ'.w f ≤ σ'.w (B 0) + ((0 : ℕ) : ℤ) * σ'.w σ'.Φ := hflow 0 hNpos hB00
      have hne0 : σ'.w (B 0) ≠ σ'.w f := fun h => hnot ⟨hB00, h⟩
      simp at h3
      omega
    have hΦqne : σ'.Φ * q ≠ 0 := mul_ne_zero hΦne hqne
    have d1 : (M.S.deg (σ'.Φ * q) : WithTop ℤ) = M.S.w (σ'.Φ * q) := M.S.deg_eq hΦqne
    have d2 : (M.S.deg (B 0) : WithTop ℤ) = M.S.w (B 0) := M.S.deg_eq hB00
    rw [M.hSw _ hΦqne] at d1
    rw [M.hSw _ hB00] at d2
    have e1 : M.S.deg (σ'.Φ * q) = σ'.w (σ'.Φ * q) := by exact_mod_cast d1
    have e2 : M.S.deg (B 0) = σ'.w (B 0) := by exact_mod_cast d2
    have hdlt : M.S.deg (σ'.Φ * q) < M.S.deg (B 0) := by
      rw [e1, e2, hwΦq]; exact hwlt
    have hin : M.S.initialForm f = M.S.initialForm (σ'.Φ * q) := by
      have hadd := L1_initialForm_add_lt M.S M.Rg (σ'.Φ * q) (B 0) hΦqne hB00
        (by rw [add_comm, ← hfsplit]; exact hf) hdlt
      rw [hfsplit, add_comm (B 0) (σ'.Φ * q)]
      exact hadd
    rw [hin, L1_initialForm_mul M.S M.Rg σ'.Φ q hΦne hqne]
    exact dvd_mul_right _ _

/-- **The (s4a) avoidance at the state**: at a MINIMIZING slot 0 the key does
NOT divide `in(f)` — a `T^{s'}`-multiple of a realizable residual misses the
attained bottom monomial (its slot index would be `−1`). -/
lemma u8_nodvd_of_min0 (M : GenuineStageModel σ') (f : Polynomial ℤ_[p])
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : Moves.IsDevelopment σ'.Φ f B N)
    (hf : f ≠ 0) (hB0 : B 0 ≠ 0) (hw0 : σ'.w (B 0) = σ'.w f) :
    letI := M.Rg.ring; ¬ M.S.initialForm σ'.Φ ∣ M.S.initialForm f := by
  letI := M.Rg.ring
  intro hdvd
  obtain ⟨k, hk0, hRk, hwk⟩ := (u5_initialForm_dvd_iff σ' M f hf).mp hdvd
  obtain ⟨hbot, hbote, -⟩ := u8_bot σ' f B N hdev hf hB0 hw0
  obtain ⟨Bk, Nk, hkdev⟩ := L0_FactA_exists σ'.Φ σ'.hmonic σ'.hdeg k
  have hmem : (-σ'.t * σ'.wPrev (B 0) - σ'.s) ∈ (σ'.R k).support := by
    rw [Finsupp.mem_support_iff]
    intro hzero
    apply hbot
    rw [hRk, u8_T_mul_apply]
    exact hzero
  obtain ⟨jk, hjkN, hjknz, hjkmin, hjke⟩ := u8_supp_key σ' k Bk Nk hkdev hk0 _ hmem
  have hexp : (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0) - σ'.s)
      = (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (B 0)) - (σ'.e : ℤ) * σ'.s := by ring
  rw [hexp, hbote] at hjke
  have h3 : (σ'.e : ℤ) * σ'.s = 1 - (σ'.h : ℤ) * σ'.t := by linarith [σ'.hbez]
  have hw2 : σ'.t * σ'.w f = σ'.t * ((σ'.h : ℤ) + σ'.w k) := by rw [hwk]
  have hjk : (jk : ℤ) = -1 := by linarith [hjke, h3, hw2]
  omega

/-! ## E. Primeness of the key initial form (U8a) -/

/-- The homogeneous core: `in(Φ')` detects factors on products of initial
forms (KEY-g(ii) transported to the state via the bottom-monomial dichotomy). -/
lemma u8_hom_core (M : GenuineStageModel σ') (f g : Polynomial ℤ_[p])
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hdvd : letI := M.Rg.ring;
      M.S.initialForm σ'.Φ ∣ M.S.initialForm f * M.S.initialForm g) :
    (letI := M.Rg.ring; M.S.initialForm σ'.Φ ∣ M.S.initialForm f)
      ∨ (letI := M.Rg.ring; M.S.initialForm σ'.Φ ∣ M.S.initialForm g) := by
  letI := M.Rg.ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnf, hng⟩ := hcon
  obtain ⟨Bf, Nf, hfdev⟩ := L0_FactA_exists σ'.Φ σ'.hmonic σ'.hdeg f
  obtain ⟨Bg, Ng, hgdev⟩ := L0_FactA_exists σ'.Φ σ'.hmonic σ'.hdeg g
  -- both factors are slot-0-minimizing (else `u8_div_of_min_pos` fires)
  have hminf : Bf 0 ≠ 0 ∧ σ'.w (Bf 0) = σ'.w f := by
    by_contra h
    exact hnf (u8_div_of_min_pos σ' M f Bf Nf hfdev hf h)
  have hming : Bg 0 ≠ 0 ∧ σ'.w (Bg 0) = σ'.w g := by
    by_contra h
    exact hng (u8_div_of_min_pos σ' M g Bg Ng hgdev hg h)
  obtain ⟨hfbot, hfbote, hfbotmin⟩ := u8_bot σ' f Bf Nf hfdev hf hminf.1 hminf.2
  obtain ⟨hgbot, hgbote, hgbotmin⟩ := u8_bot σ' g Bg Ng hgdev hg hming.1 hming.2
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  -- the product residual attains its bottom monomial
  have hprod : (σ'.R (f * g))
      (-σ'.t * σ'.wPrev (Bf 0) + -σ'.t * σ'.wPrev (Bg 0)) ≠ 0 := by
    rw [σ'.hRmul f g hf hg,
      u8_min_coeff_mul (σ'.R f) (σ'.R g) _ _ hfbotmin hgbotmin]
    exact mul_ne_zero hfbot hgbot
  -- but the DIV witness forbids the bottom (slot −1 again)
  rw [← M.Rg.if_mul f g hf hg] at hdvd
  obtain ⟨k, hk0, hRk, hwk⟩ := (u5_initialForm_dvd_iff σ' M (f * g) hfg).mp hdvd
  obtain ⟨Bk, Nk, hkdev⟩ := L0_FactA_exists σ'.Φ σ'.hmonic σ'.hdeg k
  have hmem : (-σ'.t * σ'.wPrev (Bf 0) + -σ'.t * σ'.wPrev (Bg 0) - σ'.s)
      ∈ (σ'.R k).support := by
    rw [Finsupp.mem_support_iff]
    intro hzero
    apply hprod
    rw [hRk, u8_T_mul_apply]
    exact hzero
  obtain ⟨jk, hjkN, hjknz, hjkmin, hjke⟩ := u8_supp_key σ' k Bk Nk hkdev hk0 _ hmem
  have hexp : (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (Bf 0) + -σ'.t * σ'.wPrev (Bg 0) - σ'.s)
      = (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (Bf 0))
        + (σ'.e : ℤ) * (-σ'.t * σ'.wPrev (Bg 0)) - (σ'.e : ℤ) * σ'.s := by ring
  rw [hexp, hfbote, hgbote] at hjke
  have h3 : (σ'.e : ℤ) * σ'.s = 1 - (σ'.h : ℤ) * σ'.t := by linarith [σ'.hbez]
  have hwfg : σ'.w f + σ'.w g = (σ'.h : ℤ) + σ'.w k := by
    rw [← σ'.hwmul f g hf hg]; exact hwk
  have hw2 : σ'.t * (σ'.w f + σ'.w g) = σ'.t * ((σ'.h : ℤ) + σ'.w k) := by rw [hwfg]
  have hjk : (jk : ℤ) = -1 := by linarith [hjke, h3, hw2]
  omega

/-- `in(Φ')` is not a unit: a unit would divide `in(1) = 1`, but `1` is its own
slot-0-minimizing development (`u8_nodvd_of_min0` at `f = 1`). -/
lemma u8_key_not_unit (M : GenuineStageModel σ') :
    letI := M.Rg.ring; ¬ IsUnit (M.S.initialForm σ'.Φ) := by
  letI := M.Rg.ring
  intro hunit
  have hdev1 : Moves.IsDevelopment σ'.Φ 1 (fun j => if j = 0 then 1 else 0) 1 := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · by_cases hj0 : j = 0
      · simpa [hj0] using stage_degree_pos σ'
      · simpa [hj0] using lt_of_le_of_lt bot_le (stage_degree_pos σ')
    · simp [Nat.one_le_iff_ne_zero.mp hj]
    · simp
  have hnd := u8_nodvd_of_min0 σ' M 1 (fun j => if j = 0 then 1 else 0) 1 hdev1
    one_ne_zero (by simp) (by simp)
  exact hnd hunit.dvd

/-- **U8a — (KPirr) at the state**: `in(Φ')` is PRIME in `gr(w')`, from the
Stage laws + genuine model alone (truncation at the maximal non-divisible
components, exactly the U5 skeleton, with the state homogeneous core). -/
lemma u8_key_prime (M : GenuineStageModel σ') :
    letI := M.Rg.ring; Prime (M.S.initialForm σ'.Φ) := by
  letI := M.Rg.ring
  haveI : IsDomain M.S.Gr := u5_gr_domain σ' M
  have hΦ0 : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  refine ⟨?_, u8_key_not_unit σ' M, ?_⟩
  · intro hz
    rw [u5_ring_zero_eq M.S M.Rg] at hz
    exact L0_initialForm_ne_zero M.S hΦ0 hz
  intro x y hdvd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnx, hny⟩ := hcon
  classical
  -- the non-divisible component sets are nonempty
  have hSx : ∃ γ ∈ DFinsupp.support x,
      ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ) := by
    by_contra hall
    push_neg at hall
    refine hnx (u5_dvd_of_dvd_components M.S M.Rg _ x fun γ => ?_)
    by_cases hγ : γ ∈ DFinsupp.support x
    · exact hall γ hγ
    · rw [DFinsupp.notMem_support_iff.mp hγ, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  have hSy : ∃ γ ∈ DFinsupp.support y,
      ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ) := by
    by_contra hall
    push_neg at hall
    refine hny (u5_dvd_of_dvd_components M.S M.Rg _ y fun γ => ?_)
    by_cases hγ : γ ∈ DFinsupp.support y
    · exact hall γ hγ
    · rw [DFinsupp.notMem_support_iff.mp hγ, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  set Sx := (DFinsupp.support x).filter
    (fun γ => ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ)) with hSxdef
  set Sy := (DFinsupp.support y).filter
    (fun γ => ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ)) with hSydef
  have hSxne : Sx.Nonempty := by
    obtain ⟨γ, h1, h2⟩ := hSx
    exact ⟨γ, Finset.mem_filter.mpr ⟨h1, h2⟩⟩
  have hSyne : Sy.Nonempty := by
    obtain ⟨γ, h1, h2⟩ := hSy
    exact ⟨γ, Finset.mem_filter.mpr ⟨h1, h2⟩⟩
  set m := Sx.max' hSxne with hm
  set n := Sy.max' hSyne with hn
  -- truncations at m and n
  set x' : M.S.Gr := DFinsupp.filter (fun γ => γ ≤ m) x with hx'
  set y' : M.S.Gr := DFinsupp.filter (fun γ => γ ≤ n) y with hy'
  have hx'app : ∀ γ, x' γ = if γ ≤ m then x γ else 0 := fun γ => DFinsupp.filter_apply _ γ x
  have hy'app : ∀ γ, y' γ = if γ ≤ n then y γ else 0 := fun γ => DFinsupp.filter_apply _ γ y
  -- the key divides the discarded tails componentwise
  have hdvd_high_x : ∀ γ : ℤ, m < γ →
      M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ) := by
    intro γ hγ
    by_cases hmem : γ ∈ DFinsupp.support x
    · by_contra hnd
      have hin : γ ∈ Sx := Finset.mem_filter.mpr ⟨hmem, hnd⟩
      exact absurd (Sx.le_max' γ hin) (not_le.mpr hγ)
    · rw [DFinsupp.notMem_support_iff.mp hmem, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  have hdvd_high_y : ∀ γ : ℤ, n < γ →
      M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ) := by
    intro γ hγ
    by_cases hmem : γ ∈ DFinsupp.support y
    · by_contra hnd
      have hin : γ ∈ Sy := Finset.mem_filter.mpr ⟨hmem, hnd⟩
      exact absurd (Sy.le_max' γ hin) (not_le.mpr hγ)
    · rw [DFinsupp.notMem_support_iff.mp hmem, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  -- component formula for ring subtraction
  have hsub_apply : ∀ (a b : M.S.Gr) (γ : ℤ), (a - b) γ = a γ - b γ := by
    intro a b γ
    have h1 : (a - b) + b = a := by ring
    have h2 := congrArg (fun z : M.S.Gr => z γ) h1
    simp only at h2
    rw [M.Rg.add_def] at h2
    have h3 := congrArg (fun t => t - b γ) h2
    simpa using h3
  have hxtail : M.S.initialForm σ'.Φ ∣ x - x' := by
    refine u5_dvd_of_dvd_components M.S M.Rg _ (x - x') fun γ => ?_
    by_cases hγ : γ ≤ m
    · rw [hsub_apply x x' γ, hx'app γ, if_pos hγ, sub_self, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
    · rw [hsub_apply x x' γ, hx'app γ, if_neg hγ, sub_zero]
      exact hdvd_high_x γ (not_le.mp hγ)
  have hytail : M.S.initialForm σ'.Φ ∣ y - y' := by
    refine u5_dvd_of_dvd_components M.S M.Rg _ (y - y') fun γ => ?_
    by_cases hγ : γ ≤ n
    · rw [hsub_apply y y' γ, hy'app γ, if_pos hγ, sub_self, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
    · rw [hsub_apply y y' γ, hy'app γ, if_neg hγ, sub_zero]
      exact hdvd_high_y γ (not_le.mp hγ)
  -- the key divides the truncated product
  have hdvd' : M.S.initialForm σ'.Φ ∣ x' * y' := by
    have hxy' : x' * y' = x * y - ((x - x') * y + x' * (y - y')) := by ring
    rw [hxy']
    exact dvd_sub hdvd (dvd_add (hxtail.mul_right y) (hytail.mul_left x'))
  -- its top component is the product of the pinned components
  have hx'bd : ∀ i, m < i → x' i = 0 := by
    intro i hi
    rw [hx'app i, if_neg (not_le.mpr hi)]
  have hy'bd : ∀ j, n < j → y' j = 0 := by
    intro j hj
    rw [hy'app j, if_neg (not_le.mpr hj)]
  have htop : (x' * y') (m + n) = M.S.pmul m n (x m) (y n) := by
    have h1 := u5_mul_component_top M.S M.Rg m n x' y' hx'bd hy'bd
    rw [hx'app m, if_pos le_rfl, hy'app n, if_pos le_rfl] at h1
    exact h1
  have hdvd_top : M.S.initialForm σ'.Φ ∣
      DirectSum.of (fun δ => M.S.grPiece δ) m (x m)
        * DirectSum.of (fun δ => M.S.grPiece δ) n (y n) := by
    have h1 := u5_key_dvd_components σ' M (x' * y') hdvd' (m + n)
    rw [htop, ← M.Rg.mul_of] at h1
    exact h1
  -- both pinned components are nonzero initial forms; fire the homogeneous core
  have hxm : x m ≠ 0 := by
    have hin := Sx.max'_mem hSxne
    rw [← hm] at hin
    exact DFinsupp.mem_support_iff.mp (Finset.mem_filter.mp hin).1
  have hyn : y n ≠ 0 := by
    have hin := Sy.max'_mem hSyne
    rw [← hn] at hin
    exact DFinsupp.mem_support_iff.mp (Finset.mem_filter.mp hin).1
  obtain ⟨u, hu0, _, huof⟩ := u5_piece_repr M.S hxm
  obtain ⟨v, hv0, _, hvof⟩ := u5_piece_repr M.S hyn
  rw [huof, hvof] at hdvd_top
  have hmnd : ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) m (x m) := by
    have hin := Sx.max'_mem hSxne
    rw [← hm] at hin
    exact (Finset.mem_filter.mp hin).2
  have hnnd : ¬ M.S.initialForm σ'.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) n (y n) := by
    have hin := Sy.max'_mem hSyne
    rw [← hn] at hin
    exact (Finset.mem_filter.mp hin).2
  rcases u8_hom_core σ' M u v hu0 hv0 hdvd_top with h | h
  · exact hmnd (huof ▸ h)
  · exact hnnd (hvof ▸ h)

end RDev

/-! ## F. H1-U8 assembly: `kp_step` -/

set_option linter.unusedVariables false in
/-- **H1-U8 (`kp_step`)** — the door-1 core (blueprint §5.3, statement
VERBATIM; math source §2.2 KP-STEP).  `ψ̂ := in(Φ')` itself, unit `1`;
(KPirr) is U8a (`u8_key_prime`); the degree block is U8b — LITERALLY the
`DevBound` row (STAGING ONLY, finding 11: discharges nothing until OP-B1 is
proved and the row derived).  See the module header for the honesty ledger
(route deviation; the unconsumed ν-binders; the open A-M2 non-vacuity leaf). -/
theorem kp_step (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h)
    (hprev : σ'.wPrev = ν.σ.w) (D : DevBound ν σ' M) :
    Nonempty (KPBlock σ' M) := by
  letI := M.Rg.ring
  exact ⟨{ ψhom := M.S.initialForm σ'.Φ
           homog := ⟨M.S.deg σ'.Φ, M.S.mkPiece σ'.Φ, rfl⟩
           kpa_init := ⟨1, by rw [Units.val_one, one_mul]⟩
           kpirr := u8_key_prime σ' M
           kpa_block := D.block }⟩

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.kp_step
