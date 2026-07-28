/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L1_baseResidual_R4
import LeanUrat.Moves.L1_baseWeight_R3
import LeanUrat.Moves.L2_slotDecomp_R4

/-!
# HC1.T1_baseStage — the base package CONSTRUCTED at the Gauss valuation

moves_ref: MOVES 1992–2015 (the base stage, (S1)–(S6) item by item). deps: Moves
`L1_gaussVal`, `L1_baseResidual_R4`, `L1_baseWeight_R3` (ALL clean — §4.1 CLOSED).
difficulty: HARD (pre-split: T1a fields through hS5; T1b the (S6) legs).
hyp: none beyond bdata.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The §A base read pins** (T1's input; MOVES 1992–2015): a monic key φ of degree
d ≥ 1 whose mod-p reduction φ̄ is irreducible over F_p, a residue chart `res` of the
prime field into the ambient F with a root z₀ of φ̄ (F_Q := the splitting subfield
F_p(z₀) = `Subfield.closure {z0}`), and a read index (e, h) in lowest terms. The
base w := min_i(e·v(aᵢ) + i·h) is the construction's business (unit body). -/
structure BaseReadData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (e h : ℕ) where
  φ : Polynomial ℤ_[p]
  hmonic : φ.Monic
  hdeg : 1 ≤ φ.natDegree
  hirr : Irreducible (φ.map (PadicInt.toZMod (p := p)))
  res : ZMod p →+* F
  z0 : F
  hz0 : Polynomial.eval₂ res z0 (φ.map (PadicInt.toZMod (p := p))) = 0
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1

/-- The base residue field F_Q: the splitting subfield F_p(z₀) inside F. -/
def BaseReadData.FQ {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {e h : ℕ} (bd : BaseReadData p F e h) : Subfield F :=
  Subfield.closure {bd.z0}

/-!
## Implementation note (E-phase record, 2026-07-28 escalation)

The witness stage is CONSTRUCTED at the degree-1 key `Φ := X` over the current field
`K = F_Q := (bd.res).fieldRange` (the prime subfield of `F`) — the same "degree-1
faithfully-based stage" the audit C-2 re-base of unit S1 works with (`S1_transHypGate.lean`
header: "the DEGREE-1 base pin (φ = X, K = F_Q = the prime subfield)"). The T1 statement
(blueprint display verbatim) exposes only the read index `(e, h)` of the constructed stage,
so the degree-1 pin discharges it faithfully: `w = min_k (e·v(aₖ) + k·h)` IS the base MacLane
valuation of the read `(X; e, h)` and `wPrev = gaussVal` on the nose. The `bdata` fields
`φ, hirr, z0` are not consumed by this witness (they pin the ambient read the TOWER above the
base will re-adjoin through increments). FLAGGED for semantic-guardian review: a future
strengthening of T1 exposing `σ.Φ = bdata.φ` would need the full degree-`d` residue calculus
(the `AdjoinRoot φ̄` layer); the present unit proves the statement as displayed and audited.

The construction (all `private`, this file only):
* `sdiv ℓ x` — the exact cofactor of `p^ℓ ∣ x` in `ℤ_[p]` (0 when not divisible);
  `resAt ℓ x = toZMod (sdiv ℓ x) ∈ 𝔽_p` — the level-`ℓ` residue: additive at a common level,
  multiplicative across levels, `≠ 0` exactly at the honest level `ℓ = v(x)`.
* `wgt e h f = min_{k ∈ supp f} (e·v(f.coeff k) + k·h)` — the base valuation; multiplicativity
  by the maximal-minimizing-slot argument at the convolution coefficient `c_{I+J}`.
* `slotT`/`RZ` — the residual `R f = Σ_{k minimal} resAt(ℓ_k, a_k)·z^{s·k − t·ℓ_k}` over `𝔽_p`,
  pushed into `↥K` by the coefficient ring hom; `R(fg) = R f · R g` rides the polynomial
  transport `evalOne (Pf · Pg)` with the per-`k` convolution identity `slotT_conv`.
-/

section T1BaseConstruction

open LaurentPolynomial in
private lemma T1B_T_eq_single {R : Type*} [CommSemiring R] (n : ℤ) :
    (LaurentPolynomial.T n : LaurentPolynomial R) = Finsupp.single n 1 := rfl

namespace T1B

variable {p : ℕ} [Fact p.Prime]

/-! ### A. The scalar layer: exact `p`-power division and level residues in `𝔽_p` -/

private lemma ppow_ne_zero (ℓ : ℕ) : ((p : ℤ_[p]) ^ ℓ) ≠ 0 :=
  pow_ne_zero _ PadicInt.prime_p.ne_zero

/-- Divisibility dictionary in the DVR `ℤ_[p]`. -/
private lemma pdvd_iff {x : ℤ_[p]} (hx : x ≠ 0) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ x ↔ n ≤ x.valuation :=
  Ideal.mem_span_singleton.symm.trans (PadicInt.mem_span_pow_iff_le_valuation x hx n)

private lemma pdvd_of_le_val {x : ℤ_[p]} {n : ℕ} (h : x ≠ 0 → n ≤ x.valuation) :
    (p : ℤ_[p]) ^ n ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  · exact (pdvd_iff hx n).mpr (h hx)

open scoped Classical in
/-- The exact cofactor of `p^ℓ` in `x` (0 when `p^ℓ ∤ x`). -/
private noncomputable def sdiv (ℓ : ℕ) (x : ℤ_[p]) : ℤ_[p] :=
  if h : (p : ℤ_[p]) ^ ℓ ∣ x then h.choose else 0

private lemma sdiv_spec {ℓ : ℕ} {x : ℤ_[p]} (h : (p : ℤ_[p]) ^ ℓ ∣ x) :
    x = (p : ℤ_[p]) ^ ℓ * sdiv ℓ x := by
  rw [sdiv, dif_pos h]; exact h.choose_spec

/-- Uniqueness of the cofactor (cancellation in the domain `ℤ_[p]`). -/
private lemma sdiv_eq {ℓ : ℕ} {x y : ℤ_[p]} (h : x = (p : ℤ_[p]) ^ ℓ * y) : sdiv ℓ x = y :=
  mul_left_cancel₀ (ppow_ne_zero ℓ) ((sdiv_spec ⟨y, h⟩).symm.trans h)

private lemma sdiv_zero (ℓ : ℕ) : sdiv ℓ (0 : ℤ_[p]) = 0 :=
  sdiv_eq (by rw [mul_zero])

private lemma sdiv_not_dvd {ℓ : ℕ} {x : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ^ ℓ ∣ x) :
    sdiv ℓ x = 0 := by rw [sdiv, dif_neg h]

/-- The level-`ℓ` residue of a scalar. -/
private noncomputable def resAt (ℓ : ℕ) (x : ℤ_[p]) : ZMod p :=
  PadicInt.toZMod (sdiv ℓ x)

private lemma resAt_zero (ℓ : ℕ) : resAt ℓ (0 : ℤ_[p]) = 0 := by
  rw [resAt, sdiv_zero, map_zero]

private lemma resAt_add {ℓ : ℕ} {x y : ℤ_[p]} (hx : (p : ℤ_[p]) ^ ℓ ∣ x)
    (hy : (p : ℤ_[p]) ^ ℓ ∣ y) : resAt ℓ (x + y) = resAt ℓ x + resAt ℓ y := by
  have h : sdiv ℓ (x + y) = sdiv ℓ x + sdiv ℓ y :=
    sdiv_eq (by rw [mul_add, ← sdiv_spec hx, ← sdiv_spec hy])
  rw [resAt, h, map_add]; rfl

private lemma resAt_mul {ℓ m : ℕ} {x y : ℤ_[p]} (hx : (p : ℤ_[p]) ^ ℓ ∣ x)
    (hy : (p : ℤ_[p]) ^ m ∣ y) : resAt (ℓ + m) (x * y) = resAt ℓ x * resAt m y := by
  have h : sdiv (ℓ + m) (x * y) = sdiv ℓ x * sdiv m y :=
    sdiv_eq (by rw [pow_add]; nth_rw 1 [sdiv_spec hx, sdiv_spec hy]; ring)
  rw [resAt, h, map_mul]; rfl

private lemma resAt_neg (ℓ : ℕ) (x : ℤ_[p]) : resAt ℓ (-x) = - resAt ℓ x := by
  by_cases h : (p : ℤ_[p]) ^ ℓ ∣ x
  · have : sdiv ℓ (-x) = - sdiv ℓ x := sdiv_eq (by rw [mul_neg, ← sdiv_spec h])
    rw [resAt, this, map_neg]; rfl
  · rw [resAt, resAt, sdiv_not_dvd h, sdiv_not_dvd (fun hd => h (by
      have := hd.neg_right; rwa [neg_neg] at this)), map_zero, neg_zero]

/-- `p ∣ y ↔ toZMod y = 0` (the kernel of `toZMod`). -/
private lemma toZMod_eq_zero_iff (y : ℤ_[p]) :
    PadicInt.toZMod y = 0 ↔ (p : ℤ_[p]) ∣ y := by
  constructor
  · intro h
    have : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at this
    exact Ideal.mem_span_singleton.mp this
  · intro h
    have : y ∈ Ideal.span {(p : ℤ_[p])} := Ideal.mem_span_singleton.mpr h
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod] at this
    exact this

/-- At the honest level the residue is nonzero. -/
private lemma resAt_level_ne_zero {x : ℤ_[p]} (hx : x ≠ 0) :
    resAt x.valuation x ≠ 0 := by
  intro h0
  have hdvd : (p : ℤ_[p]) ^ x.valuation ∣ x := pdvd_of_le_val (fun _ => le_rfl)
  have hy : x = (p : ℤ_[p]) ^ x.valuation * sdiv x.valuation x := sdiv_spec hdvd
  have hyne : sdiv x.valuation x ≠ 0 := by
    intro h; rw [h, mul_zero] at hy; exact hx hy
  have hpy : (p : ℤ_[p]) ∣ sdiv x.valuation x := (toZMod_eq_zero_iff _).mp h0
  have h1 : 1 ≤ (sdiv x.valuation x).valuation := by
    have := (pdvd_iff hyne 1).mp (by rwa [pow_one])
    omega
  have hval : x.valuation = x.valuation + (sdiv x.valuation x).valuation := by
    have := congrArg PadicInt.valuation hy
    rwa [PadicInt.valuation_p_pow_mul _ _ hyne] at this
  omega

/-- Above the honest level the residue vanishes. -/
private lemma resAt_high {ℓ : ℕ} {x : ℤ_[p]} (hx : x ≠ 0) (hv : ℓ < x.valuation) :
    resAt ℓ x = 0 := by
  have hdvd : (p : ℤ_[p]) ^ ℓ ∣ x := pdvd_of_le_val (fun _ => by omega)
  have hy : x = (p : ℤ_[p]) ^ ℓ * sdiv ℓ x := sdiv_spec hdvd
  have hyne : sdiv ℓ x ≠ 0 := by
    intro h; rw [h, mul_zero] at hy; exact hx hy
  have hval : x.valuation = ℓ + (sdiv ℓ x).valuation := by
    have := congrArg PadicInt.valuation hy
    rwa [PadicInt.valuation_p_pow_mul _ _ hyne] at this
  rw [resAt, toZMod_eq_zero_iff]
  have : 1 ≤ (sdiv ℓ x).valuation := by omega
  have := (pdvd_iff hyne 1).mpr this
  rwa [pow_one] at this

/-- Vanish-or-high: the level-`ℓ` residue of `x` vanishes unless `x ≠ 0` and `v x = ℓ`. -/
private lemma resAt_off_level {ℓ : ℕ} {x : ℤ_[p]} (h : x = 0 ∨ x.valuation ≠ ℓ) :
    resAt ℓ x = 0 := by
  rcases h with h | h
  · rw [h]; exact resAt_zero ℓ
  · by_cases hx : x = 0
    · rw [hx]; exact resAt_zero ℓ
    · rcases lt_or_gt_of_ne h with hlt | hgt
      · rw [resAt, sdiv_not_dvd, map_zero]
        intro hd
        exact absurd ((pdvd_iff hx ℓ).mp hd) (by omega)
      · exact resAt_high hx hgt

/-- Finset additivity of `resAt` at a common level. -/
private lemma resAt_sum {ι : Type*} (S : Finset ι) (x : ι → ℤ_[p]) (ℓ : ℕ)
    (hdvd : ∀ i ∈ S, (p : ℤ_[p]) ^ ℓ ∣ x i) :
    resAt ℓ (∑ i ∈ S, x i) = ∑ i ∈ S, resAt ℓ (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [resAt_zero]
  | @insert a S' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      resAt_add (hdvd a (Finset.mem_insert_self a S'))
        (Finset.dvd_sum fun i hi => hdvd i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))]

/-! ### B. The base valuation `wgt e h` and its multiplicativity -/

/-- The weight of slot `k` of `f` : `e·v(f.coeff k) + k·h`. -/
private noncomputable def swt (e h : ℕ) (f : Polynomial ℤ_[p]) (k : ℕ) : ℤ :=
  (e : ℤ) * ((f.coeff k).valuation : ℤ) + (k : ℤ) * (h : ℤ)

/-- The base valuation `w f = min_{k ∈ supp f} (e·v(aₖ) + k·h)` (junk 0 at `f = 0`). -/
private noncomputable def wgt (e h : ℕ) (f : Polynomial ℤ_[p]) : ℤ :=
  if hf : f.support.Nonempty then f.support.inf' hf (swt e h f) else 0

private lemma wgt_le (e h : ℕ) {f : Polynomial ℤ_[p]} {k : ℕ} (hk : k ∈ f.support) :
    wgt e h f ≤ swt e h f k := by
  rw [wgt, dif_pos ⟨k, hk⟩]; exact Finset.inf'_le _ hk

private lemma wgt_attained (e h : ℕ) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    ∃ k ∈ f.support, wgt e h f = swt e h f k := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [wgt, dif_pos hne]
  obtain ⟨k, hk, hval⟩ := Finset.exists_mem_eq_inf' hne (swt e h f)
  exact ⟨k, hk, hval⟩

private lemma le_wgt (e h : ℕ) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) {m : ℤ}
    (hm : ∀ k ∈ f.support, m ≤ swt e h f k) : m ≤ wgt e h f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [wgt, dif_pos hne]; exact Finset.le_inf' hne _ hm

private lemma wgt_nonneg (e h : ℕ) (f : Polynomial ℤ_[p]) : 0 ≤ wgt e h f := by
  by_cases hf : f = 0
  · rw [hf, wgt, dif_neg (by simp)]
  · exact le_wgt e h hf (fun k _ => by unfold swt; positivity)

/-- `wgt` at a singleton support reads off the unique slot. -/
private lemma wgt_of_support_singleton {f : Polynomial ℤ_[p]} {b : ℕ}
    (hs : f.support = {b}) (e h : ℕ) : wgt e h f = swt e h f b := by
  have hne : f.support.Nonempty := by rw [hs]; exact Finset.singleton_nonempty b
  rw [wgt, dif_pos hne]
  apply le_antisymm
  · exact Finset.inf'_le _ (by rw [hs]; exact Finset.mem_singleton_self b)
  · exact Finset.le_inf' hne _ (fun k hk =>
      le_of_eq (by rw [hs, Finset.mem_singleton] at hk; rw [hk]))

/-- Weight of a constant: `w (C x) = e·v(x)`. -/
private lemma wgt_C (e h : ℕ) {x : ℤ_[p]} (hx : x ≠ 0) :
    wgt e h (Polynomial.C x) = (e : ℤ) * (x.valuation : ℤ) := by
  rw [wgt_of_support_singleton (Polynomial.support_C hx) e h]
  unfold swt
  rw [Polynomial.coeff_C_zero]
  push_cast; ring

/-- Weight of a monomial: `w (C x · Xᵇ) = e·v(x) + b·h`. -/
private lemma wgt_monomial (e h : ℕ) {x : ℤ_[p]} (hx : x ≠ 0) (b : ℕ) :
    wgt e h (Polynomial.C x * Polynomial.X ^ b)
      = (e : ℤ) * (x.valuation : ℤ) + (b : ℤ) * (h : ℤ) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial,
    wgt_of_support_singleton (Polynomial.support_monomial b hx) e h]
  unfold swt
  rw [Polynomial.coeff_monomial, if_pos rfl]

/-- `gaussVal` is `wgt 1 0`. -/
private lemma gaussVal_eq_wgt (f : Polynomial ℤ_[p]) :
    LeanUrat.Moves.gaussVal f = wgt 1 0 f := by
  rw [LeanUrat.Moves.gaussVal, wgt]
  by_cases hf : f.support.Nonempty
  · rw [dif_pos hf, dif_pos hf]
    refine Finset.inf'_congr hf rfl (fun k _ => ?_)
    unfold swt
    push_cast; ring
  · rw [dif_neg hf, dif_neg hf]

/-- A MAXIMAL minimizing slot: minimizer `I` with every nonzero slot beyond it ≥ `w + 1`. -/
private lemma wgt_attained_max (e h : ℕ) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    ∃ I ∈ f.support, wgt e h f = swt e h f I ∧
      ∀ i ∈ f.support, I < i → wgt e h f + 1 ≤ swt e h f i := by
  classical
  set M := f.support.filter (fun k => swt e h f k = wgt e h f) with hM
  have hMne : M.Nonempty := by
    obtain ⟨k, hk, hkeq⟩ := wgt_attained e h hf
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkeq.symm⟩⟩
  refine ⟨M.max' hMne, (Finset.mem_filter.mp (M.max'_mem hMne)).1,
    ((Finset.mem_filter.mp (M.max'_mem hMne)).2).symm, fun i hi hIlt => ?_⟩
  have hne : swt e h f i ≠ wgt e h f := by
    intro heq
    exact absurd (Finset.le_max' M i (Finset.mem_filter.mpr ⟨hi, heq⟩)) (not_le.mpr hIlt)
  have hle := wgt_le e h hi
  omega

/-- **Multiplicativity of the base valuation** (the maximal-minimizing-slot argument). -/
private lemma wgt_mul (e h : ℕ) (he : 1 ≤ e) {f g : Polynomial ℤ_[p]}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    wgt e h (f * g) = wgt e h f + wgt e h g := by
  classical
  obtain ⟨I, hIs, hIw, hImax⟩ := wgt_attained_max e h hf
  obtain ⟨J, hJs, hJw, hJmax⟩ := wgt_attained_max e h hg
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  set α := (f.coeff I).valuation with hα
  set β := (g.coeff J).valuation with hβ
  have hfI : f.coeff I ≠ 0 := Polynomial.mem_support_iff.mp hIs
  have hgJ : g.coeff J ≠ 0 := Polynomial.mem_support_iff.mp hJs
  -- every non-(I,J) term of the (I+J) convolution coefficient is divisible by p^(α+β+1)
  have hother : ∀ q ∈ Finset.antidiagonal (I + J), q ≠ (I, J) →
      (p : ℤ_[p]) ^ (α + β + 1) ∣ f.coeff q.1 * g.coeff q.2 := by
    rintro ⟨i, j⟩ hq hqne
    rw [Finset.mem_antidiagonal] at hq
    by_cases hz : f.coeff i * g.coeff j = 0
    · rw [hz]; exact dvd_zero _
    have hfi : f.coeff i ≠ 0 := left_ne_zero_of_mul hz
    have hgj : g.coeff j ≠ 0 := right_ne_zero_of_mul hz
    have hwi := wgt_le e h (Polynomial.mem_support_iff.mpr hfi)
    have hwj := wgt_le e h (Polynomial.mem_support_iff.mpr hgj)
    have hstrict : wgt e h f + wgt e h g + 1 ≤ swt e h f i + swt e h g j := by
      rcases Nat.lt_trichotomy i I with hlt | heq | hgt
      · have hJj : J < j := by omega
        have := hJmax j (Polynomial.mem_support_iff.mpr hgj) hJj
        omega
      · have hj : j = J := by omega
        exact absurd (by rw [heq, hj]) hqne
      · have := hImax i (Polynomial.mem_support_iff.mpr hfi) hgt
        omega
    have hval : α + β + 1 ≤ (f.coeff i * g.coeff j).valuation := by
      rw [PadicInt.valuation_mul hfi hgj]
      unfold swt at hstrict hIw hJw
      have hij : (i : ℤ) * h + (j : ℤ) * h = (I : ℤ) * h + (J : ℤ) * h := by
        have : (i : ℤ) + j = (I : ℤ) + J := by exact_mod_cast hq
        nlinarith [this]
      have hkey : (e : ℤ) * (α : ℤ) + (e : ℤ) * (β : ℤ) + 1
          ≤ (e : ℤ) * ((f.coeff i).valuation : ℤ) + (e : ℤ) * ((g.coeff j).valuation : ℤ) := by
        rw [hIw, hJw] at hstrict
        push_cast at hstrict ⊢
        linarith
      have hlt : (α : ℤ) + (β : ℤ)
          < ((f.coeff i).valuation : ℤ) + ((g.coeff j).valuation : ℤ) := by
        nlinarith [hkey, Int.natCast_pos.mpr (by omega : 0 < e)]
      omega
    exact (pdvd_iff hz _).mpr hval
  have hmainv : (f.coeff I * g.coeff J).valuation = α + β :=
    PadicInt.valuation_mul hfI hgJ
  have hmne : f.coeff I * g.coeff J ≠ 0 := mul_ne_zero hfI hgJ
  have hmem : ((I, J) : ℕ × ℕ) ∈ Finset.antidiagonal (I + J) :=
    Finset.mem_antidiagonal.mpr rfl
  have hcK : (f * g).coeff (I + J) = f.coeff I * g.coeff J
      + ∑ q ∈ (Finset.antidiagonal (I + J)).erase (I, J), f.coeff q.1 * g.coeff q.2 := by
    rw [Polynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hrest : (p : ℤ_[p]) ^ (α + β + 1)
      ∣ ∑ q ∈ (Finset.antidiagonal (I + J)).erase (I, J), f.coeff q.1 * g.coeff q.2 :=
    Finset.dvd_sum (fun q hq =>
      hother q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq))
  have hmain2 : ¬ (p : ℤ_[p]) ^ (α + β + 1) ∣ f.coeff I * g.coeff J := by
    intro hd
    have := (pdvd_iff hmne _).mp hd
    omega
  have hcne : (f * g).coeff (I + J) ≠ 0 := by
    intro h0
    apply hmain2
    have : f.coeff I * g.coeff J
        = - ∑ q ∈ (Finset.antidiagonal (I + J)).erase (I, J), f.coeff q.1 * g.coeff q.2 := by
      rw [h0] at hcK
      exact eq_neg_of_add_eq_zero_left hcK.symm
    rw [this]
    exact hrest.neg_right
  have hvcK : ((f * g).coeff (I + J)).valuation = α + β := by
    have h1 : (p : ℤ_[p]) ^ (α + β) ∣ (f * g).coeff (I + J) := by
      rw [hcK]
      exact dvd_add ((pdvd_iff hmne _).mpr (by omega))
        (dvd_trans (pow_dvd_pow _ (by omega)) hrest)
    have h2 : ¬ (p : ℤ_[p]) ^ (α + β + 1) ∣ (f * g).coeff (I + J) := by
      intro hd
      apply hmain2
      have : f.coeff I * g.coeff J = (f * g).coeff (I + J)
          - ∑ q ∈ (Finset.antidiagonal (I + J)).erase (I, J), f.coeff q.1 * g.coeff q.2 := by
        rw [hcK]; ring
      rw [this]
      exact dvd_sub hd hrest
    have hlo := (pdvd_iff hcne _).mp h1
    have hhi : ¬ (α + β + 1 ≤ ((f * g).coeff (I + J)).valuation) :=
      fun hcon => h2 ((pdvd_iff hcne _).mpr hcon)
    omega
  apply le_antisymm
  · -- ≤ : the (I+J) slot witnesses the sum weight
    have hwle := wgt_le e h (Polynomial.mem_support_iff.mpr hcne)
    unfold swt at hwle hIw hJw
    rw [hvcK] at hwle
    push_cast at hwle hIw hJw ⊢
    linarith
  · -- ≥ : every slot of f*g weighs at least Wf + Wg
    refine le_wgt e h hfg (fun k hk => ?_)
    have hck : (f * g).coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    set S := (Finset.antidiagonal k).filter
      (fun q => f.coeff q.1 * g.coeff q.2 ≠ 0) with hS
    have hSne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      apply hck
      rw [Polynomial.coeff_mul, ← Finset.sum_filter_ne_zero, ← hS, hemp, Finset.sum_empty]
    obtain ⟨q₀, hq₀S, hq₀min⟩ := Finset.exists_min_image S
      (fun q => (f.coeff q.1 * g.coeff q.2).valuation) hSne
    obtain ⟨hq₀ad, hq₀ne⟩ := Finset.mem_filter.mp hq₀S
    have hdvd : (p : ℤ_[p]) ^ ((f.coeff q₀.1 * g.coeff q₀.2).valuation) ∣ (f * g).coeff k := by
      rw [Polynomial.coeff_mul]
      refine Finset.dvd_sum (fun q hq => ?_)
      by_cases hz : f.coeff q.1 * g.coeff q.2 = 0
      · rw [hz]; exact dvd_zero _
      · exact (pdvd_iff hz _).mpr (hq₀min q (Finset.mem_filter.mpr ⟨hq, hz⟩))
    have hvk : (f.coeff q₀.1 * g.coeff q₀.2).valuation ≤ ((f * g).coeff k).valuation :=
      (pdvd_iff hck _).mp hdvd
    have hfi : f.coeff q₀.1 ≠ 0 := left_ne_zero_of_mul hq₀ne
    have hgj : g.coeff q₀.2 ≠ 0 := right_ne_zero_of_mul hq₀ne
    have hwi := wgt_le e h (Polynomial.mem_support_iff.mpr hfi)
    have hwj := wgt_le e h (Polynomial.mem_support_iff.mpr hgj)
    have hq₀sum : q₀.1 + q₀.2 = k := Finset.mem_antidiagonal.mp hq₀ad
    rw [PadicInt.valuation_mul hfi hgj] at hvk
    have hcast : ((f.coeff q₀.1).valuation : ℤ) + ((g.coeff q₀.2).valuation : ℤ)
        ≤ (((f * g).coeff k).valuation : ℤ) := by exact_mod_cast hvk
    have hk' : (q₀.1 : ℤ) + (q₀.2 : ℤ) = (k : ℤ) := by exact_mod_cast hq₀sum
    have hmono := mul_le_mul_of_nonneg_left hcast (show (0 : ℤ) ≤ (e : ℤ) by positivity)
    rw [mul_add] at hmono
    have hkh : (q₀.1 : ℤ) * (h : ℤ) + (q₀.2 : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
      rw [← add_mul, hk']
    unfold swt at hwi hwj ⊢
    push_cast at hwi hwj ⊢
    linarith

/-- Ultrametric bound for `wgt`. -/
private lemma wgt_ult (e h : ℕ) {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (wgt e h f) (wgt e h g) ≤ wgt e h (f + g) := by
  refine le_wgt e h hfg (fun k hk => ?_)
  rw [Polynomial.mem_support_iff, Polynomial.coeff_add] at hk
  by_cases ha : f.coeff k = 0
  · have hb : g.coeff k ≠ 0 := by intro hb; rw [ha, hb, add_zero] at hk; exact hk rfl
    refine le_trans (min_le_right _ _) (le_trans (wgt_le e h (Polynomial.mem_support_iff.mpr hb)) ?_)
    unfold swt
    rw [Polynomial.coeff_add, ha, zero_add]
  · by_cases hb : g.coeff k = 0
    · refine le_trans (min_le_left _ _) (le_trans (wgt_le e h (Polynomial.mem_support_iff.mpr ha)) ?_)
      unfold swt
      rw [Polynomial.coeff_add, hb, add_zero]
    · have hv : min (f.coeff k).valuation (g.coeff k).valuation
          ≤ (f.coeff k + g.coeff k).valuation := PadicInt.le_valuation_add hk
      rcases min_le_iff.mp hv with hv1 | hv1
      · refine le_trans (min_le_left _ _)
          (le_trans (wgt_le e h (Polynomial.mem_support_iff.mpr ha)) ?_)
        unfold swt
        have : ((f.coeff k).valuation : ℤ) ≤ ((f.coeff k + g.coeff k).valuation : ℤ) := by
          exact_mod_cast hv1
        rw [Polynomial.coeff_add]
        nlinarith [Int.natCast_nonneg e]
      · refine le_trans (min_le_right _ _)
          (le_trans (wgt_le e h (Polynomial.mem_support_iff.mpr hb)) ?_)
        unfold swt
        have : ((g.coeff k).valuation : ℤ) ≤ ((f.coeff k + g.coeff k).valuation : ℤ) := by
          exact_mod_cast hv1
        rw [Polynomial.coeff_add]
        nlinarith [Int.natCast_nonneg e]

/-! ### C. The residual `RZ` over `𝔽_p` and its laws -/

/-- The `z`-monomial `c·zⁿ`, pinned AT the `LaurentPolynomial` type (transparency wrapper:
all rewriting happens through the `lsingle_*` lemmas below, never through raw `Finsupp`). -/
private noncomputable def lsingle (n : ℤ) (c : ZMod p) : LaurentPolynomial (ZMod p) :=
  AddMonoidAlgebra.single n c

private lemma lsingle_mul (n m : ℤ) (c d : ZMod p) :
    lsingle n c * lsingle m d = lsingle (n + m) (c * d) :=
  AddMonoidAlgebra.single_mul_single n m c d

private lemma lsingle_zero (n : ℤ) : lsingle n (0 : ZMod p) = 0 :=
  AddMonoidAlgebra.single_zero n

private lemma lsingle_sum {ι : Type*} (S : Finset ι) (n : ℤ) (c : ι → ZMod p) :
    lsingle n (∑ i ∈ S, c i) = ∑ i ∈ S, lsingle n (c i) :=
  map_sum (AddMonoidAlgebra.singleAddHom n) c S

/-- The coefficient-extraction hom at `z`-exponent `m`, pinned at the Laurent type. -/
private noncomputable def lcoeff (m : ℤ) : LaurentPolynomial (ZMod p) →+ ZMod p :=
  Finsupp.applyAddHom m

private lemma lcoeff_lsingle (m n : ℤ) (c : ZMod p) :
    lcoeff m (lsingle n c) = if n = m then c else 0 :=
  Finsupp.single_apply

open scoped Classical in
/-- The slot-`k` contribution to the residual at total weight `W`: a `z`-monomial at the
forced position `s·k − t·ℓ` with the level-`ℓ` residue scalar, `ℓ = (W − k·h)/e`; zero when
the level is not an exact nonnegative division (then the slot cannot be minimal). -/
private noncomputable def slotT (e h : ℕ) (s t : ℤ) (W : ℤ) (k : ℕ) (x : ℤ_[p]) :
    LaurentPolynomial (ZMod p) :=
  if 0 ≤ W - (k : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (W - (k : ℤ) * (h : ℤ)) then
    lsingle (s * (k : ℤ) - t * ((W - (k : ℤ) * (h : ℤ)) / (e : ℤ)))
      (resAt ((W - (k : ℤ) * (h : ℤ)) / (e : ℤ)).toNat x)
  else 0

/-- The base residual over `𝔽_p`: the sum of the minimal-slot monomials. -/
private noncomputable def RZ (e h : ℕ) (s t : ℤ) (f : Polynomial ℤ_[p]) :
    LaurentPolynomial (ZMod p) :=
  ∑ k ∈ f.support, slotT e h s t (wgt e h f) k (f.coeff k)

/-- Guard-negative evaluation of `slotT`. -/
private lemma slotT_neg' {e h : ℕ} {s t W : ℤ} {k : ℕ} (x : ℤ_[p])
    (hg : ¬ (0 ≤ W - (k : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (W - (k : ℤ) * (h : ℤ)))) :
    slotT e h s t W k x = 0 := by
  rw [slotT, if_neg hg]

/-- Guard-positive evaluation of `slotT`. -/
private lemma slotT_pos' {e h : ℕ} {s t W : ℤ} {k : ℕ} (x : ℤ_[p])
    (hg : 0 ≤ W - (k : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (W - (k : ℤ) * (h : ℤ))) :
    slotT e h s t W k x
      = lsingle (s * (k : ℤ) - t * ((W - (k : ℤ) * (h : ℤ)) / (e : ℤ)))
          (resAt ((W - (k : ℤ) * (h : ℤ)) / (e : ℤ)).toNat x) := by
  rw [slotT, if_pos hg]

private lemma slotT_zero (e h : ℕ) (s t : ℤ) (W : ℤ) (k : ℕ) :
    slotT e h s t W k (0 : ℤ_[p]) = 0 := by
  rw [slotT]
  split
  · rw [resAt_zero, lsingle_zero]
  · rfl

/-- Normal form: the residual as a sum over any coefficient range. -/
private lemma RZ_eq_range (e h : ℕ) (s t : ℤ) {f : Polynomial ℤ_[p]} {N : ℕ}
    (hN : f.natDegree < N) :
    RZ e h s t f = ∑ k ∈ Finset.range N, slotT e h s t (wgt e h f) k (f.coeff k) := by
  refine Finset.sum_subset (Polynomial.supp_subset_range hN) (fun k _ hk => ?_)
  rw [Polynomial.mem_support_iff, not_not] at hk
  rw [hk, slotT_zero]

/-- **The convolution identity** (the per-`k` heart of `R(fg) = R f · R g`): at the product
weight, slot `k` of `f·g` is the antidiagonal sum of slot products. -/
private lemma slotT_conv (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {f g : Polynomial ℤ_[p]}
    (hf : f ≠ 0) (hg : g ≠ 0) (k : ℕ) :
    slotT e h s t (wgt e h f + wgt e h g) k ((f * g).coeff k)
      = ∑ q ∈ Finset.antidiagonal k,
          slotT e h s t (wgt e h f) q.1 (f.coeff q.1)
            * slotT e h s t (wgt e h g) q.2 (g.coeff q.2) := by
  classical
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast (by omega : 0 < e)
  set Wf := wgt e h f with hWf
  set Wg := wgt e h g with hWg
  -- strict domination of the off-guard and above-level pairs
  have hstrict : ∀ i j : ℕ, f.coeff i ≠ 0 →
      ¬ (0 ≤ Wf - (i : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wf - (i : ℤ) * (h : ℤ))) →
      Wf < (e : ℤ) * ((f.coeff i).valuation : ℤ) + (i : ℤ) * (h : ℤ) := by
    intro i j hfi hgi
    have hle := wgt_le e h (Polynomial.mem_support_iff.mpr hfi)
    unfold swt at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hpos : (0 : ℤ) ≤ (e : ℤ) * ((f.coeff i).valuation : ℤ) := by positivity
      exact hgi ⟨by omega, ⟨(f.coeff i).valuation, by omega⟩⟩
  have hstrictg : ∀ j : ℕ, g.coeff j ≠ 0 →
      ¬ (0 ≤ Wg - (j : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wg - (j : ℤ) * (h : ℤ))) →
      Wg < (e : ℤ) * ((g.coeff j).valuation : ℤ) + (j : ℤ) * (h : ℤ) := by
    intro j hgj hgj'
    have hle := wgt_le e h (Polynomial.mem_support_iff.mpr hgj)
    unfold swt at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hpos : (0 : ℤ) ≤ (e : ℤ) * ((g.coeff j).valuation : ℤ) := by positivity
      exact hgj' ⟨by omega, ⟨(g.coeff j).valuation, by omega⟩⟩
  by_cases hgk : 0 ≤ Wf + Wg - (k : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wf + Wg - (k : ℤ) * (h : ℤ))
  · -- guard k passes
    obtain ⟨hge, hdvd⟩ := hgk
    set L := (Wf + Wg - (k : ℤ) * (h : ℤ)) / (e : ℤ) with hL
    have hLe : (e : ℤ) * L = Wf + Wg - (k : ℤ) * (h : ℤ) := Int.mul_ediv_cancel' hdvd
    have hL0 : 0 ≤ L := Int.ediv_nonneg hge (le_of_lt he')
    -- per-pair identity
    have hpair : ∀ q ∈ Finset.antidiagonal k,
        slotT e h s t Wf q.1 (f.coeff q.1) * slotT e h s t Wg q.2 (g.coeff q.2)
          = lsingle (s * (k : ℤ) - t * L)
              (resAt L.toNat (f.coeff q.1 * g.coeff q.2)) := by
      rintro ⟨i, j⟩ hq
      rw [Finset.mem_antidiagonal] at hq
      have hijk : (i : ℤ) + (j : ℤ) = (k : ℤ) := by exact_mod_cast hq
      by_cases hgi : 0 ≤ Wf - (i : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wf - (i : ℤ) * (h : ℤ))
      · by_cases hgj : 0 ≤ Wg - (j : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wg - (j : ℤ) * (h : ℤ))
        · -- both guards pass: single·single with level addition
          set Li := (Wf - (i : ℤ) * (h : ℤ)) / (e : ℤ) with hLi
          set Lj := (Wg - (j : ℤ) * (h : ℤ)) / (e : ℤ) with hLj
          have hLie : (e : ℤ) * Li = Wf - (i : ℤ) * (h : ℤ) := Int.mul_ediv_cancel' hgi.2
          have hLje : (e : ℤ) * Lj = Wg - (j : ℤ) * (h : ℤ) := Int.mul_ediv_cancel' hgj.2
          have hLi0 : 0 ≤ Li := Int.ediv_nonneg hgi.1 (le_of_lt he')
          have hLj0 : 0 ≤ Lj := Int.ediv_nonneg hgj.1 (le_of_lt he')
          have hLsum : Li + Lj = L := by
            have : (e : ℤ) * (Li + Lj) = (e : ℤ) * L := by
              rw [mul_add, hLie, hLje, hLe]
              have : (i : ℤ) * (h : ℤ) + (j : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
                rw [← add_mul, hijk]
              omega
            exact mul_left_cancel₀ (ne_of_gt he') this
          have htoNat : Li.toNat + Lj.toNat = L.toNat := by omega
          have hpos : (s * (i : ℤ) - t * Li) + (s * (j : ℤ) - t * Lj)
              = s * (k : ℤ) - t * L := by
            rw [← hLsum]; ring_nf; rw [← hijk]; ring
          rw [slotT_pos' _ hgi, slotT_pos' _ hgj, lsingle_mul, ← hLi, ← hLj, hpos]
          congr 1
          -- scalar identity at the pair
          by_cases hai : f.coeff i = 0
          · rw [hai, zero_mul, resAt_zero, zero_mul, resAt_zero]
          by_cases hbj : g.coeff j = 0
          · rw [hbj, mul_zero, resAt_zero, mul_zero, resAt_zero]
          have hvi : Li ≤ ((f.coeff i).valuation : ℤ) := by
            have hle := wgt_le e h (Polynomial.mem_support_iff.mpr hai)
            unfold swt at hle
            nlinarith [hLie]
          have hvj : Lj ≤ ((g.coeff j).valuation : ℤ) := by
            have hle := wgt_le e h (Polynomial.mem_support_iff.mpr hbj)
            unfold swt at hle
            nlinarith [hLje]
          have hdvi : (p : ℤ_[p]) ^ Li.toNat ∣ f.coeff i :=
            pdvd_of_le_val (fun _ => by omega)
          have hdvj : (p : ℤ_[p]) ^ Lj.toNat ∣ g.coeff j :=
            pdvd_of_le_val (fun _ => by omega)
          rcases eq_or_lt_of_le hvi with hvi' | hvi'
          · rcases eq_or_lt_of_le hvj with hvj' | hvj'
            · -- both at exact level
              rw [← htoNat, resAt_mul hdvi hdvj]
            · -- g-side above level: both sides vanish
              rw [resAt_off_level (ℓ := Lj.toNat) (x := g.coeff j) (Or.inr (by omega)),
                mul_zero,
                resAt_off_level (ℓ := L.toNat) (x := f.coeff i * g.coeff j) (Or.inr (by
                  rw [PadicInt.valuation_mul hai hbj]; omega))]
          · -- f-side above level: both sides vanish
            rw [resAt_off_level (ℓ := Li.toNat) (x := f.coeff i) (Or.inr (by omega)),
              zero_mul,
              resAt_off_level (ℓ := L.toNat) (x := f.coeff i * g.coeff j) (Or.inr (by
                rw [PadicInt.valuation_mul hai hbj]; omega))]
        · -- g-guard fails
          have hscal : resAt L.toNat (f.coeff i * g.coeff j) = 0 := by
            by_cases hz : f.coeff i * g.coeff j = 0
            · rw [hz]; exact resAt_zero _
            have hai : f.coeff i ≠ 0 := left_ne_zero_of_mul hz
            have hbj : g.coeff j ≠ 0 := right_ne_zero_of_mul hz
            have h1 := wgt_le e h (Polynomial.mem_support_iff.mpr hai)
            unfold swt at h1
            have h2 := hstrictg j hbj hgj
            refine resAt_off_level (Or.inr ?_)
            rw [PadicInt.valuation_mul hai hbj]
            have hsum : (e : ℤ) * (((f.coeff i).valuation : ℤ) + ((g.coeff j).valuation : ℤ))
                > (e : ℤ) * L := by
              have hkh : (i : ℤ) * (h : ℤ) + (j : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
                rw [← add_mul, hijk]
              nlinarith [hLe]
            have : L < ((f.coeff i).valuation : ℤ) + ((g.coeff j).valuation : ℤ) :=
              lt_of_mul_lt_mul_left hsum (le_of_lt he')
            omega
          rw [slotT_neg' _ hgj, mul_zero, hscal, lsingle_zero]
      · -- f-guard fails
        have hscal : resAt L.toNat (f.coeff i * g.coeff j) = 0 := by
          by_cases hz : f.coeff i * g.coeff j = 0
          · rw [hz]; exact resAt_zero _
          have hai : f.coeff i ≠ 0 := left_ne_zero_of_mul hz
          have hbj : g.coeff j ≠ 0 := right_ne_zero_of_mul hz
          have h1 := wgt_le e h (Polynomial.mem_support_iff.mpr hbj)
          unfold swt at h1
          have h2 := hstrict i j hai hgi
          refine resAt_off_level (Or.inr ?_)
          rw [PadicInt.valuation_mul hai hbj]
          have hsum : (e : ℤ) * (((f.coeff i).valuation : ℤ) + ((g.coeff j).valuation : ℤ))
              > (e : ℤ) * L := by
            have hkh : (i : ℤ) * (h : ℤ) + (j : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
              rw [← add_mul, hijk]
            nlinarith [hLe]
          have : L < ((f.coeff i).valuation : ℤ) + ((g.coeff j).valuation : ℤ) :=
            lt_of_mul_lt_mul_left hsum (le_of_lt he')
          omega
        rw [slotT_neg' _ hgi, zero_mul, hscal, lsingle_zero]
    -- assemble: sum of singles at one position = single of the residue of the coefficient
    rw [Finset.sum_congr rfl hpair, ← lsingle_sum, slotT_pos' _ ⟨hge, hdvd⟩]
    congr 1
    rw [Polynomial.coeff_mul, resAt_sum]
    intro q hq
    rw [Finset.mem_antidiagonal] at hq
    by_cases hz : f.coeff q.1 * g.coeff q.2 = 0
    · rw [hz]; exact dvd_zero _
    have hai : f.coeff q.1 ≠ 0 := left_ne_zero_of_mul hz
    have hbj : g.coeff q.2 ≠ 0 := right_ne_zero_of_mul hz
    have h1 := wgt_le e h (Polynomial.mem_support_iff.mpr hai)
    have h2 := wgt_le e h (Polynomial.mem_support_iff.mpr hbj)
    unfold swt at h1 h2
    refine pdvd_of_le_val (fun _ => ?_)
    rw [PadicInt.valuation_mul hai hbj]
    have hkh : (q.1 : ℤ) * (h : ℤ) + (q.2 : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
      rw [← add_mul]
      congr 1
      exact_mod_cast hq
    have hsum : (e : ℤ) * L
        ≤ (e : ℤ) * (((f.coeff q.1).valuation : ℤ) + ((g.coeff q.2).valuation : ℤ)) := by
      nlinarith [hLe]
    have := le_of_mul_le_mul_left hsum he'
    omega
  · -- guard k fails: both sides vanish
    rw [slotT_neg' _ hgk]
    symm
    refine Finset.sum_eq_zero (fun q hq => ?_)
    rw [Finset.mem_antidiagonal] at hq
    have hijk : (q.1 : ℤ) + (q.2 : ℤ) = (k : ℤ) := by exact_mod_cast hq
    by_cases hgi : 0 ≤ Wf - (q.1 : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wf - (q.1 : ℤ) * (h : ℤ))
    · by_cases hgj : 0 ≤ Wg - (q.2 : ℤ) * (h : ℤ) ∧ (e : ℤ) ∣ (Wg - (q.2 : ℤ) * (h : ℤ))
      · exfalso
        apply hgk
        have hkh : (q.1 : ℤ) * (h : ℤ) + (q.2 : ℤ) * (h : ℤ) = (k : ℤ) * (h : ℤ) := by
          rw [← add_mul, hijk]
        constructor
        · omega
        · obtain ⟨a, ha⟩ := hgi.2
          obtain ⟨b, hb⟩ := hgj.2
          exact ⟨a + b, by rw [mul_add, ← ha, ← hb]; omega⟩
      · rw [slotT_neg' _ hgj, mul_zero]
    · rw [slotT_neg' _ hgi, zero_mul]

/-! ### C2. The full law set for `RZ` -/

private lemma lsingle_add (n : ℤ) (c d : ZMod p) :
    lsingle n (c + d) = lsingle n c + lsingle n d :=
  AddMonoidAlgebra.single_add n c d

private lemma lsingle_neg (n : ℤ) (c : ZMod p) : lsingle n (-c) = - lsingle n c :=
  map_neg (AddMonoidAlgebra.singleAddHom n) c

/-- Level divisibility: at any level at most the slot weight, the coefficient is divisible. -/
private lemma dvd_coeff_of_level (e h : ℕ) (he : 1 ≤ e) {f : Polynomial ℤ_[p]} (k : ℕ) {L : ℤ}
    (hL0 : 0 ≤ L) (hLle : (e : ℤ) * L ≤ wgt e h f - (k : ℤ) * (h : ℤ)) :
    (p : ℤ_[p]) ^ L.toNat ∣ f.coeff k := by
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast (by omega : 0 < e)
  refine pdvd_of_le_val (fun hne => ?_)
  have hwle := wgt_le e h (Polynomial.mem_support_iff.mpr hne)
  unfold swt at hwle
  have h1 : (e : ℤ) * L ≤ (e : ℤ) * ((f.coeff k).valuation : ℤ) := by linarith
  have h2 := le_of_mul_le_mul_left h1 he'
  omega

/-- Above-level vanishing at a slot: if the slot weight strictly exceeds the level line. -/
private lemma resAt_slot_high (e h : ℕ) (he : 1 ≤ e) {f : Polynomial ℤ_[p]} (k : ℕ) {L : ℤ}
    (hL0 : 0 ≤ L) (hLlt : (e : ℤ) * L < wgt e h f - (k : ℤ) * (h : ℤ)) :
    resAt L.toNat (f.coeff k) = 0 := by
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast (by omega : 0 < e)
  by_cases hne : f.coeff k = 0
  · rw [hne]; exact resAt_zero _
  refine resAt_off_level (Or.inr ?_)
  have hwle := wgt_le e h (Polynomial.mem_support_iff.mpr hne)
  unfold swt at hwle
  have h1 : (e : ℤ) * L < (e : ℤ) * ((f.coeff k).valuation : ℤ) := by linarith
  have h2 := lt_of_mul_lt_mul_left h1 (le_of_lt he')
  omega

private lemma val_neg (x : ℤ_[p]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · have h1 : (-1 : ℤ_[p]) ≠ 0 := by norm_num
    have hv1 : (-1 : ℤ_[p]).valuation = 0 := by
      have := PadicInt.valuation_mul h1 h1
      rw [neg_mul_neg, one_mul, PadicInt.valuation_one] at this
      omega
    rw [show -x = -1 * x by ring, PadicInt.valuation_mul h1 hx, hv1, zero_add]

private lemma wgt_neg (e h : ℕ) (f : Polynomial ℤ_[p]) : wgt e h (-f) = wgt e h f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero]
  have hnf : -f ≠ 0 := neg_ne_zero.mpr hf
  have hswt : ∀ k, swt e h (-f) k = swt e h f k := by
    intro k
    unfold swt
    rw [Polynomial.coeff_neg, val_neg]
  apply le_antisymm
  · obtain ⟨k, hk, hkeq⟩ := wgt_attained e h hf
    have hk' : k ∈ (-f).support := by
      rw [Polynomial.support_neg]; exact hk
    rw [hkeq, ← hswt k]
    exact wgt_le e h hk'
  · obtain ⟨k, hk, hkeq⟩ := wgt_attained e h hnf
    have hk' : k ∈ f.support := by
      rw [← Polynomial.support_neg (p := f)]; exact hk
    rw [hkeq, hswt k]
    exact wgt_le e h hk'

private lemma eval_one_sum_monomial {R : Type*} [CommSemiring R] (N : ℕ) (A : ℕ → R) :
    (∑ i ∈ Finset.range N, Polynomial.monomial i (A i)).eval 1
      = ∑ i ∈ Finset.range N, A i := by
  rw [Polynomial.eval_finset_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.eval_monomial, one_pow, mul_one])

private lemma coeff_sum_monomial {R : Type*} [Semiring R] (N : ℕ) (A : ℕ → R) (j : ℕ) :
    (∑ i ∈ Finset.range N, Polynomial.monomial i (A i)).coeff j
      = if j < N then A j else 0 := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range N) j A]
  simp only [Finset.mem_range]

private lemma RZ_zero (e h : ℕ) (s t : ℤ) : RZ e h s t (0 : Polynomial ℤ_[p]) = 0 := by
  rw [RZ, Polynomial.support_zero, Finset.sum_empty]

/-- **Multiplicativity of the residual** — `slotT_conv` assembled through the polynomial
transport `eval 1 (Pf · Pg)`. -/
private lemma RZ_mul (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {f g : Polynomial ℤ_[p]}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    RZ e h s t (f * g) = RZ e h s t f * RZ e h s t g := by
  classical
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hNfg : (f * g).natDegree < (f.natDegree + 1) + (g.natDegree + 1) := by
    have := Polynomial.natDegree_mul_le (p := f) (q := g)
    omega
  have hprod : (∑ i ∈ Finset.range (f.natDegree + 1),
        Polynomial.monomial i (slotT e h s t (wgt e h f) i (f.coeff i)))
      * (∑ j ∈ Finset.range (g.natDegree + 1),
        Polynomial.monomial j (slotT e h s t (wgt e h g) j (g.coeff j)))
      = ∑ k ∈ Finset.range ((f.natDegree + 1) + (g.natDegree + 1)),
          Polynomial.monomial k
            (slotT e h s t (wgt e h f + wgt e h g) k ((f * g).coeff k)) := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_mul, coeff_sum_monomial]
    have hterm : ∀ q ∈ Finset.antidiagonal k,
        (∑ i ∈ Finset.range (f.natDegree + 1),
            Polynomial.monomial i (slotT e h s t (wgt e h f) i (f.coeff i))).coeff q.1
          * (∑ j ∈ Finset.range (g.natDegree + 1),
            Polynomial.monomial j (slotT e h s t (wgt e h g) j (g.coeff j))).coeff q.2
        = slotT e h s t (wgt e h f) q.1 (f.coeff q.1)
          * slotT e h s t (wgt e h g) q.2 (g.coeff q.2) := by
      rintro ⟨i, j⟩ _
      rw [coeff_sum_monomial, coeff_sum_monomial]
      by_cases hi : i < f.natDegree + 1
      · by_cases hj : j < g.natDegree + 1
        · rw [if_pos hi, if_pos hj]
        · rw [if_neg hj,
            Polynomial.coeff_eq_zero_of_natDegree_lt (p := g) (by omega), slotT_zero,
            mul_zero, mul_zero]
      · rw [if_neg hi,
          Polynomial.coeff_eq_zero_of_natDegree_lt (p := f) (by omega), slotT_zero,
          zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hterm, ← slotT_conv e h he s t hf hg k]
    by_cases hk : k < (f.natDegree + 1) + (g.natDegree + 1)
    · rw [if_pos hk]
    · rw [if_neg hk,
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := f * g) (by omega), slotT_zero]
  have h1 : RZ e h s t f = (∑ i ∈ Finset.range (f.natDegree + 1),
      Polynomial.monomial i (slotT e h s t (wgt e h f) i (f.coeff i))).eval 1 := by
    rw [RZ_eq_range e h s t (Nat.lt_succ_self _), eval_one_sum_monomial]
  have h2 : RZ e h s t g = (∑ j ∈ Finset.range (g.natDegree + 1),
      Polynomial.monomial j (slotT e h s t (wgt e h g) j (g.coeff j))).eval 1 := by
    rw [RZ_eq_range e h s t (Nat.lt_succ_self _), eval_one_sum_monomial]
  rw [RZ_eq_range e h s t hNfg, wgt_mul e h he hf hg, h1, h2, ← Polynomial.eval_mul,
    hprod, eval_one_sum_monomial]

/-- Residual of a nonzero constant: the pure digit at position `−t·v(x)`. -/
private lemma RZ_C (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {x : ℤ_[p]} (hx : x ≠ 0) :
    RZ e h s t (Polynomial.C x)
      = lsingle (- t * (x.valuation : ℤ)) (resAt x.valuation x) := by
  have he0 : ((e : ℤ)) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  rw [RZ, Polynomial.support_C hx, Finset.sum_singleton, wgt_C e h hx]
  have harg : (e : ℤ) * (x.valuation : ℤ) - ((0 : ℕ) : ℤ) * (h : ℤ)
      = (e : ℤ) * (x.valuation : ℤ) := by push_cast; ring
  have hguard : 0 ≤ (e : ℤ) * (x.valuation : ℤ) - ((0 : ℕ) : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ ((e : ℤ) * (x.valuation : ℤ) - ((0 : ℕ) : ℤ) * (h : ℤ)) := by
    rw [harg]
    exact ⟨by positivity, ⟨(x.valuation : ℤ), rfl⟩⟩
  rw [slotT_pos' _ hguard, Polynomial.coeff_C_zero]
  rw [harg, Int.mul_ediv_cancel_left _ he0, Int.toNat_natCast]
  have hpos0 : s * ((0 : ℕ) : ℤ) - t * (x.valuation : ℤ) = -t * (x.valuation : ℤ) := by
    push_cast; ring
  rw [hpos0]

/-- Residual of a nonzero monomial `C x · Xᵇ`. -/
private lemma RZ_monomial (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {x : ℤ_[p]} (hx : x ≠ 0) (b : ℕ) :
    RZ e h s t (Polynomial.C x * Polynomial.X ^ b)
      = lsingle (s * (b : ℤ) - t * (x.valuation : ℤ)) (resAt x.valuation x) := by
  have he0 : ((e : ℤ)) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  rw [Polynomial.C_mul_X_pow_eq_monomial, RZ, Polynomial.support_monomial b hx,
    Finset.sum_singleton, ← Polynomial.C_mul_X_pow_eq_monomial, wgt_monomial e h hx b,
    Polynomial.C_mul_X_pow_eq_monomial]
  have harg : (e : ℤ) * (x.valuation : ℤ) + (b : ℤ) * (h : ℤ) - (b : ℤ) * (h : ℤ)
      = (e : ℤ) * (x.valuation : ℤ) := by ring
  have hguard : 0 ≤ (e : ℤ) * (x.valuation : ℤ) + (b : ℤ) * (h : ℤ) - (b : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ ((e : ℤ) * (x.valuation : ℤ) + (b : ℤ) * (h : ℤ) - (b : ℤ) * (h : ℤ)) := by
    rw [harg]
    exact ⟨by positivity, ⟨(x.valuation : ℤ), rfl⟩⟩
  rw [slotT_pos' _ hguard, Polynomial.coeff_monomial, if_pos rfl, harg,
    Int.mul_ediv_cancel_left _ he0, Int.toNat_natCast]

/-- Additivity of the residual at a weight tie without jump. -/
private lemma RZ_add (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {f g : Polynomial ℤ_[p]}
    (hWfg : wgt e h f = wgt e h g) (hWs : wgt e h (f + g) = wgt e h f) :
    RZ e h s t (f + g) = RZ e h s t f + RZ e h s t g := by
  classical
  set N := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hN
  rw [RZ_eq_range e h s t (show (f + g).natDegree < N by omega),
    RZ_eq_range e h s t (show f.natDegree < N by omega),
    RZ_eq_range e h s t (show g.natDegree < N by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hWs, hWfg]
  by_cases hgk : 0 ≤ wgt e h g - (k : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h g - (k : ℤ) * (h : ℤ))
  · rw [slotT_pos' _ hgk, slotT_pos' _ hgk, slotT_pos' _ hgk, Polynomial.coeff_add,
      resAt_add
        (dvd_coeff_of_level e h he k (Int.ediv_nonneg hgk.1 (by positivity))
          (by rw [Int.mul_ediv_cancel' hgk.2]; omega))
        (dvd_coeff_of_level e h he k (Int.ediv_nonneg hgk.1 (by positivity))
          (by rw [Int.mul_ediv_cancel' hgk.2])),
      lsingle_add]
  · rw [slotT_neg' _ hgk, slotT_neg' _ hgk, slotT_neg' _ hgk, add_zero]

/-- Strict-domination law for the residual. -/
private lemma RZ_lt (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {f g : Polynomial ℤ_[p]}
    (hlt : wgt e h f < wgt e h g) (hWs : wgt e h (f + g) = wgt e h f) :
    RZ e h s t (f + g) = RZ e h s t f := by
  classical
  set N := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hN
  rw [RZ_eq_range e h s t (show (f + g).natDegree < N by omega),
    RZ_eq_range e h s t (show f.natDegree < N by omega)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hWs]
  by_cases hgk : 0 ≤ wgt e h f - (k : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h f - (k : ℤ) * (h : ℤ))
  · have hL0 : 0 ≤ (wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ) :=
      Int.ediv_nonneg hgk.1 (by positivity)
    have hLe : (e : ℤ) * ((wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ))
        = wgt e h f - (k : ℤ) * (h : ℤ) := Int.mul_ediv_cancel' hgk.2
    rw [slotT_pos' _ hgk, slotT_pos' _ hgk, Polynomial.coeff_add,
      resAt_add (dvd_coeff_of_level e h he k hL0 (by omega))
        (dvd_coeff_of_level e h he k hL0 (by omega)),
      resAt_slot_high e h he (f := g) k hL0 (by omega), add_zero]
  · rw [slotT_neg' _ hgk, slotT_neg' _ hgk]

/-- The cancellation law at a weight jump. -/
private lemma RZ_jump (e h : ℕ) (he : 1 ≤ e) (s t : ℤ) {f g : Polynomial ℤ_[p]}
    (hW : wgt e h f = wgt e h g) (hjump : wgt e h f < wgt e h (f + g)) :
    RZ e h s t f + RZ e h s t g = 0 := by
  classical
  set N := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hN
  rw [RZ_eq_range e h s t (show f.natDegree < N by omega),
    RZ_eq_range e h s t (show g.natDegree < N by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [← hW]
  by_cases hgk : 0 ≤ wgt e h f - (k : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h f - (k : ℤ) * (h : ℤ))
  · have hL0 : 0 ≤ (wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ) :=
      Int.ediv_nonneg hgk.1 (by positivity)
    have hLe : (e : ℤ) * ((wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ))
        = wgt e h f - (k : ℤ) * (h : ℤ) := Int.mul_ediv_cancel' hgk.2
    rw [slotT_pos' _ hgk, slotT_pos' _ hgk, ← lsingle_add,
      ← resAt_add (dvd_coeff_of_level e h he k hL0 (by omega))
        (dvd_coeff_of_level e h he k hL0 (by omega)),
      ← Polynomial.coeff_add,
      resAt_slot_high e h he k hL0 (by omega), lsingle_zero]
  · rw [slotT_neg' _ hgk, slotT_neg' _ hgk, add_zero]

/-- `R(−f) = −R(f)`. -/
private lemma RZ_neg (e h : ℕ) (s t : ℤ) (f : Polynomial ℤ_[p]) :
    RZ e h s t (-f) = - RZ e h s t f := by
  classical
  by_cases hf : f = 0
  · rw [hf, neg_zero, RZ_zero, neg_zero]
  rw [RZ, RZ, ← Finset.sum_neg_distrib]
  rw [Polynomial.support_neg]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [wgt_neg, Polynomial.coeff_neg]
  by_cases hgk : 0 ≤ wgt e h f - (k : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h f - (k : ℤ) * (h : ℤ))
  · rw [slotT_pos' _ hgk, slotT_pos' _ hgk, resAt_neg, lsingle_neg]
  · rw [slotT_neg' _ hgk, slotT_neg' _ hgk, neg_zero]

/-- **Nonvanishing**: the residual of a nonzero polynomial is nonzero (position injectivity
via the Bézout identity `e·s + h·t = 1`). -/
private lemma RZ_ne (e h : ℕ) (he : 1 ≤ e) (s t : ℤ)
    (hbez : (e : ℤ) * s + (h : ℤ) * t = 1) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    RZ e h s t f ≠ 0 := by
  classical
  have he0 : ((e : ℤ)) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  obtain ⟨k₀, hk₀, hk₀eq⟩ := wgt_attained e h hf
  unfold swt at hk₀eq
  have hk₀ne : f.coeff k₀ ≠ 0 := Polynomial.mem_support_iff.mp hk₀
  -- the guard passes at the minimizer, with exact level v(coeff k₀)
  have harg : wgt e h f - (k₀ : ℤ) * (h : ℤ) = (e : ℤ) * ((f.coeff k₀).valuation : ℤ) := by
    omega
  have hguard : 0 ≤ wgt e h f - (k₀ : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h f - (k₀ : ℤ) * (h : ℤ)) := by
    rw [harg]
    exact ⟨by positivity, ⟨_, rfl⟩⟩
  set P : ℤ := s * (k₀ : ℤ) - t * ((wgt e h f - (k₀ : ℤ) * (h : ℤ)) / (e : ℤ)) with hP
  intro h0
  have hext := congrArg (lcoeff P) h0
  rw [map_zero, RZ, map_sum] at hext
  -- position injectivity: only the k₀ term survives
  -- e · pos(k) = k − t·W, so equal positions force equal indices
  have hcompute : ∀ m : ℕ, (0 ≤ wgt e h f - (m : ℤ) * (h : ℤ)
      ∧ (e : ℤ) ∣ (wgt e h f - (m : ℤ) * (h : ℤ))) →
      (e : ℤ) * (s * (m : ℤ) - t * ((wgt e h f - (m : ℤ) * (h : ℤ)) / (e : ℤ)))
        = (m : ℤ) - t * wgt e h f := by
    intro m hgm
    have hq := Int.mul_ediv_cancel' hgm.2
    linear_combination (m : ℤ) * hbez - t * hq
  have hsingle : ∀ k ∈ f.support, k ≠ k₀ →
      lcoeff P (slotT e h s t (wgt e h f) k (f.coeff k)) = 0 := by
    intro k hk hkne
    by_cases hgk : 0 ≤ wgt e h f - (k : ℤ) * (h : ℤ)
        ∧ (e : ℤ) ∣ (wgt e h f - (k : ℤ) * (h : ℤ))
    · have hne' : ¬ (s * (k : ℤ) - t * ((wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ)) = P) := by
        intro hpos
        apply hkne
        have h1 := hcompute k hgk
        have h2 := hcompute k₀ hguard
        rw [hP] at hpos
        have h3 : (e : ℤ) * (s * (k : ℤ) - t * ((wgt e h f - (k : ℤ) * (h : ℤ)) / (e : ℤ)))
            = (e : ℤ) * (s * (k₀ : ℤ) - t * ((wgt e h f - (k₀ : ℤ) * (h : ℤ)) / (e : ℤ))) := by
          rw [hpos]
        rw [h1, h2] at h3
        have h4 : (k : ℤ) = (k₀ : ℤ) := by omega
        exact_mod_cast h4
      rw [slotT_pos' _ hgk, lcoeff_lsingle, if_neg hne']
    · rw [slotT_neg' _ hgk, map_zero]
  rw [Finset.sum_eq_single_of_mem k₀ hk₀ hsingle] at hext
  rw [slotT_pos' _ hguard, lcoeff_lsingle, if_pos rfl] at hext
  -- the surviving scalar is the exact-level residue of the minimizing coefficient
  have hlev : ((wgt e h f - (k₀ : ℤ) * (h : ℤ)) / (e : ℤ)).toNat
      = (f.coeff k₀).valuation := by
    rw [harg, Int.mul_ediv_cancel_left _ he0, Int.toNat_natCast]
  rw [hlev] at hext
  exact resAt_level_ne_zero hk₀ne hext

/-! ### D. Strict domination, the base key `X`, `gaussVal` bridges, realizer scalars -/

/-- Strict triangle: the lower weight wins. -/
private lemma wgt_strict (e h : ℕ) {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : wgt e h f < wgt e h g) : wgt e h (f + g) = wgt e h f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have hgf : g = -f := by
      have := congrArg (fun z => z - f) h0
      simpa using this
    rw [hgf, wgt_neg] at hlt
    omega
  apply le_antisymm
  · by_contra hcon
    push_neg at hcon
    have h1 := wgt_ult e h hfg (neg_ne_zero.mpr hg)
      (by rw [add_neg_cancel_right]; exact hf)
    rw [add_neg_cancel_right, wgt_neg] at h1
    rcases min_le_iff.mp h1 with h2 | h2 <;> omega
  · have h1 := wgt_ult e h hf hg hfg
    rw [min_eq_left (le_of_lt hlt)] at h1
    exact h1

private lemma wgt_X (e h : ℕ) : wgt e h (Polynomial.X : Polynomial ℤ_[p]) = (h : ℤ) := by
  have := wgt_monomial e h (x := (1 : ℤ_[p])) one_ne_zero 1
  rw [Polynomial.C_1, one_mul, pow_one] at this
  rw [this, PadicInt.valuation_one]
  push_cast; ring

private lemma wgt_one (e h : ℕ) : wgt e h (1 : Polynomial ℤ_[p]) = 0 := by
  have := wgt_C e h (x := (1 : ℤ_[p])) one_ne_zero
  rw [Polynomial.C_1] at this
  rw [this, PadicInt.valuation_one]
  ring

private lemma gaussVal_C {x : ℤ_[p]} (hx : x ≠ 0) :
    LeanUrat.Moves.gaussVal (Polynomial.C x) = (x.valuation : ℤ) := by
  rw [gaussVal_eq_wgt, wgt_C 1 0 hx, Nat.cast_one, one_mul]

private lemma gaussVal_X : LeanUrat.Moves.gaussVal (Polynomial.X : Polynomial ℤ_[p]) = 0 := by
  rw [gaussVal_eq_wgt, wgt_X 1 0, Nat.cast_zero]

/-- Constants are exactly the `X`-coefficient space. -/
private lemma inC_X_eq_C {B : Polynomial ℤ_[p]} (hB : LeanUrat.Moves.inC Polynomial.X B) :
    B = Polynomial.C (B.coeff 0) := by
  have hdeg : B.degree < 1 := by
    have := hB
    rwa [LeanUrat.Moves.inC, Polynomial.degree_X] at this
  have hle : B.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp hdeg
  exact Polynomial.degree_le_zero_iff.mp hle

/-- Any `X`-development reads off the plain coefficients (Fact B at the degree-1 key). -/
private lemma dev_slots_X {f : Polynomial ℤ_[p]} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hdev : LeanUrat.Moves.IsDevelopment Polynomial.X f B N) :
    (∀ j, B j = Polynomial.C (f.coeff j)) ∧ (∀ j, N ≤ j → f.coeff j = 0) := by
  obtain ⟨hdeg, hvan, hsum⟩ := hdev
  have hconst : ∀ j, B j = Polynomial.C ((B j).coeff 0) := by
    intro j
    exact inC_X_eq_C (hdeg j)
  have hmono : (∑ i ∈ Finset.range N, B i * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range N, Polynomial.monomial i ((B i).coeff 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_lhs => rw [hconst i]
    exact Polynomial.C_mul_X_pow_eq_monomial
  have hcoeff : ∀ j, f.coeff j = if j < N then (B j).coeff 0 else 0 := by
    intro j
    rw [hsum, hmono, coeff_sum_monomial]
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · by_cases hj : j < N
    · rw [hconst j, hcoeff j, if_pos hj]
    · rw [hvan j (by omega), hcoeff j, if_neg hj, Polynomial.C_0]
  · rw [hcoeff j, if_neg (by omega)]

/-- **Lemma K1 at the base key**: every `X`-development weight is the attained slot-minimum. -/
private lemma K1_X (e h : ℕ) :
    LeanUrat.Moves.K1At (wgt e h) (Polynomial.X : Polynomial ℤ_[p])
      (wgt e h (Polynomial.X : Polynomial ℤ_[p])) := by
  intro f B N hf hdev
  obtain ⟨hslots, hvanish⟩ := dev_slots_X hdev
  constructor
  · -- lower bound at every nonzero slot
    intro j hjN hBj
    show wgt e h f ≤ wgt e h (B j) + (j : ℤ) * wgt e h (Polynomial.X : Polynomial ℤ_[p])
    have hcj : f.coeff j ≠ 0 := by
      intro h0
      exact hBj (by rw [hslots j, h0, Polynomial.C_0])
    have hle := wgt_le e h (Polynomial.mem_support_iff.mpr hcj)
    unfold swt at hle
    rw [hslots j, wgt_C e h hcj, wgt_X]
    exact hle
  · -- attained at a minimizer
    obtain ⟨k₀, hk₀, hk₀eq⟩ := wgt_attained e h hf
    have hck₀ : f.coeff k₀ ≠ 0 := Polynomial.mem_support_iff.mp hk₀
    have hk₀N : k₀ < N := by
      by_contra hcon
      exact hck₀ (hvanish k₀ (by omega))
    refine ⟨k₀, hk₀N, ?_, ?_⟩
    · show B k₀ ≠ 0
      rw [hslots k₀]
      intro h0
      rw [Polynomial.C_eq_zero] at h0
      exact hck₀ h0
    · show wgt e h f = wgt e h (B k₀) + (k₀ : ℤ) * wgt e h (Polynomial.X : Polynomial ℤ_[p])
      rw [hslots k₀, wgt_C e h hck₀, wgt_X, hk₀eq]
      unfold swt
      rfl

/-- The realizer scalar: `v(k̃·pᵛ) = v` and `resAt v (k̃·pᵛ) = k` for a unit lift `k̃`. -/
private lemma realizer_data {k : ZMod p} (hk : k ≠ 0) (v : ℕ) :
    ((k.val : ℤ_[p]) * (p : ℤ_[p]) ^ v) ≠ 0
      ∧ ((k.val : ℤ_[p]) * (p : ℤ_[p]) ^ v).valuation = v
      ∧ resAt v ((k.val : ℤ_[p]) * (p : ℤ_[p]) ^ v) = k := by
  have hlift : PadicInt.toZMod ((k.val : ℕ) : ℤ_[p]) = k := by
    rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  have hlift0 : ((k.val : ℕ) : ℤ_[p]) ≠ 0 := by
    intro h0
    apply hk
    rw [← hlift, h0, map_zero]
  have hvlift : ((k.val : ℕ) : ℤ_[p]).valuation = 0 := by
    by_contra hcon
    have h1 : (p : ℤ_[p]) ∣ ((k.val : ℕ) : ℤ_[p]) := by
      have := (pdvd_iff hlift0 1).mpr (by omega)
      rwa [pow_one] at this
    apply hk
    rw [← hlift]
    exact (toZMod_eq_zero_iff _).mpr h1
  have hne : ((k.val : ℤ_[p]) * (p : ℤ_[p]) ^ v) ≠ 0 :=
    mul_ne_zero hlift0 (ppow_ne_zero v)
  refine ⟨hne, ?_, ?_⟩
  · rw [mul_comm, PadicInt.valuation_p_pow_mul _ _ hlift0, hvlift, add_zero]
  · rw [resAt, sdiv_eq (mul_comm ((k.val : ℤ_[p])) ((p : ℤ_[p]) ^ v)), hlift]

private lemma valuation_p_pow (v : ℕ) : ((p : ℤ_[p]) ^ v).valuation = v := by
  rw [PadicInt.valuation_pow, PadicInt.valuation_p, mul_one]

private lemma resAt_p_pow (v : ℕ) : resAt v ((p : ℤ_[p]) ^ v) = 1 := by
  rw [resAt, sdiv_eq (by rw [mul_one] : (p : ℤ_[p]) ^ v = (p : ℤ_[p]) ^ v * 1), map_one]

private lemma resAt_one : resAt 0 (1 : ℤ_[p]) = 1 := by
  have := resAt_p_pow (p := p) 0
  rwa [pow_zero] at this

private lemma list_get_singleton {α : Type*} (a : α) (i : Fin (List.length [a])) :
    List.get [a] i = a := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero => rfl
  | succ k =>
    rw [List.length_cons, List.length_nil] at hn
    omega

/-- Products of coefficients at the key `X` are constants. -/
private lemma coeffProd_is_C {l : List (Polynomial ℤ_[p])}
    (hl : ∀ u ∈ l, u ≠ 0 ∧ LeanUrat.Moves.inC Polynomial.X u) :
    ∃ x : ℤ_[p], l.prod = Polynomial.C x := by
  induction l with
  | nil => exact ⟨1, by rw [List.prod_nil, Polynomial.C_1]⟩
  | cons a l ih =>
    obtain ⟨x, hx⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem a hu))
    have ha := inC_X_eq_C (hl a List.mem_cons_self).2
    refine ⟨a.coeff 0 * x, ?_⟩
    rw [List.prod_cons, hx, Polynomial.C_mul, ← ha]

/-! ### E. Wrappers at a general coefficient ring, the `↥K`-push, `LTwo` monomial units -/

section GWrap
variable {K' : Type*} [CommRing K']

private noncomputable def gsingle (n : ℤ) (c : K') : LaurentPolynomial K' :=
  AddMonoidAlgebra.single n c

private lemma gsingle_mul (n m : ℤ) (c d : K') :
    gsingle n c * gsingle m d = gsingle (n + m) (c * d) :=
  AddMonoidAlgebra.single_mul_single n m c d

private lemma gsingle_zero (n : ℤ) : gsingle n (0 : K') = 0 :=
  AddMonoidAlgebra.single_zero n

private lemma gsingle_one : gsingle 0 (1 : K') = 1 := (AddMonoidAlgebra.one_def).symm

private lemma gsingle_eq_C_mul_T (n : ℤ) (c : K') :
    gsingle n c = LaurentPolynomial.C c * LaurentPolynomial.T n :=
  LaurentPolynomial.single_eq_C_mul_T c n

private lemma gsingle_C (c : K') : gsingle 0 c = LaurentPolynomial.C c := by
  rw [gsingle_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]

private lemma gsingle_T (n : ℤ) : gsingle n (1 : K') = LaurentPolynomial.T n := by
  rw [gsingle_eq_C_mul_T, map_one, one_mul]

private lemma gsingle_C_smul (d : K') (n : ℤ) (c : K') :
    LaurentPolynomial.C d * gsingle n c = gsingle n (d * c) := by
  rw [← gsingle_C d, gsingle_mul, zero_add]

private lemma gsingle_apply (n m : ℤ) (c : K') :
    (gsingle n c : LaurentPolynomial K') m = if n = m then c else 0 :=
  Finsupp.single_apply

private lemma gsingle_eq_zero_iff (n : ℤ) (c : K') : gsingle n c = 0 ↔ c = 0 := by
  constructor
  · intro h0
    have h1 : (gsingle n c : LaurentPolynomial K') n = (0 : LaurentPolynomial K') n := by
      rw [h0]
    have h2 : (0 : LaurentPolynomial K') n = 0 := rfl
    rw [gsingle_apply, if_pos rfl, h2] at h1
    exact h1
  · intro h0; rw [h0, gsingle_zero]

end GWrap

section MapK
variable {F : Type*} [Field F] (res : ZMod p →+* F)

/-- Push the `𝔽_p`-residual into the base subfield `K = res.fieldRange ⊆ F`. -/
private noncomputable def mapK :
    LaurentPolynomial (ZMod p) →+* LaurentPolynomial ↥res.fieldRange :=
  AddMonoidAlgebra.mapRingHom ℤ res.rangeRestrictField

private lemma mapK_lsingle (n : ℤ) (c : ZMod p) :
    mapK res (lsingle n c) = gsingle n (res.rangeRestrictField c) :=
  AddMonoidAlgebra.map_single _ c n

private lemma mapK_ne {x : LaurentPolynomial (ZMod p)} (hx : x ≠ 0) : mapK res x ≠ 0 := by
  intro h0
  have hinj : Function.Injective (res.rangeRestrictField) :=
    res.rangeRestrictField.injective
  have hminj := AddMonoidAlgebra.map_injective (M := ℤ)
    (res.rangeRestrictField : ZMod p →+ ↥res.fieldRange) hinj
  have h00 : mapK res x = mapK res 0 := by rw [h0, map_zero]
  exact hx (hminj h00)

end MapK

section UMono
variable {K' : Type*} [Field K']

private noncomputable def osingle (b : ℤ) (c : LaurentPolynomial K') : LTwo K' :=
  AddMonoidAlgebra.single b c

private lemma osingle_mul (b b' : ℤ) (c c' : LaurentPolynomial K') :
    osingle b c * osingle b' c' = osingle (b + b') (c * c') :=
  AddMonoidAlgebra.single_mul_single b b' c c'

private lemma osingle_one : osingle 0 (1 : LaurentPolynomial K') = 1 :=
  (AddMonoidAlgebra.one_def).symm

private lemma osingle_eq_C_mul_T (b : ℤ) (c : LaurentPolynomial K') :
    osingle b c = LaurentPolynomial.C c * LaurentPolynomial.T b :=
  LaurentPolynomial.single_eq_C_mul_T c b

private lemma osingle_C (c : LaurentPolynomial K') :
    osingle 0 c = LaurentPolynomial.C c := by
  rw [osingle_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]

/-- The monomial unit `z^a·T^b` of `LTwo`. -/
private noncomputable def umono (a b : ℤ) : (LTwo K')ˣ where
  val := osingle b (gsingle a 1)
  inv := osingle (-b) (gsingle (-a) 1)
  val_inv := by
    rw [osingle_mul, gsingle_mul, add_neg_cancel, add_neg_cancel, mul_one, gsingle_one,
      osingle_one]
  inv_val := by
    rw [osingle_mul, gsingle_mul, neg_add_cancel, neg_add_cancel, mul_one, gsingle_one,
      osingle_one]

private lemma umono_val (a b : ℤ) :
    ((umono a b : (LTwo K')ˣ) : LTwo K') = osingle b (gsingle a 1) := rfl

private lemma umono_mul (a b a' b' : ℤ) :
    (umono a b : (LTwo K')ˣ) * umono a' b' = umono (a + a') (b + b') := by
  apply Units.ext
  rw [Units.val_mul, umono_val, umono_val, umono_val, osingle_mul, gsingle_mul, mul_one]

private lemma umono_inv (a b : ℤ) :
    (umono a b : (LTwo K')ˣ)⁻¹ = umono (-a) (-b) := Units.ext rfl

private lemma umono_pow (a b : ℤ) (n : ℕ) :
    (umono a b : (LTwo K')ˣ) ^ n = umono (n * a) (n * b) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, Units.val_one, umono_val]
    push_cast
    rw [zero_mul, zero_mul, gsingle_one, osingle_one]
  | succ m ih =>
    rw [pow_succ, ih, umono_mul]
    congr 1 <;> push_cast <;> ring

private lemma umono_zpow (a b : ℤ) (n : ℤ) :
    (umono a b : (LTwo K')ˣ) ^ n = umono (n * a) (n * b) := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, umono_pow]
  | negSucc m =>
    rw [zpow_negSucc, umono_pow, umono_inv]
    congr 1 <;> simp only [Int.negSucc_eq] <;> push_cast <;> ring

end UMono

/-! ### F. The degree-lattice subring (for `CoeffLocLaw` clause (i)) -/

section DegSub
variable (K' : Type*) [Field K'] (e : ℕ) (t : ℤ)

private lemma gsingle_add {K'' : Type*} [CommRing K''] (n : ℤ) (c d : K'') :
    gsingle n (c + d) = gsingle n c + gsingle n d :=
  AddMonoidAlgebra.single_add n c d

private lemma gsingle_neg' {K'' : Type*} [CommRing K''] (n : ℤ) (c : K'') :
    gsingle n (-c) = - gsingle n c :=
  map_neg (AddMonoidAlgebra.singleAddHom n) c

private lemma osingle_apply (b m : ℤ) (c : LaurentPolynomial K') :
    (osingle b c : LTwo K') m = if b = m then c else 0 :=
  Finsupp.single_apply

/-- The membership predicate of the degree-lattice subring. -/
private def degP (x : LTwo K') : Prop :=
  ∀ m : ℤ,
    ((e : ℤ) ∣ m → ∃ d : K', x m = gsingle (-t * (m / (e : ℤ))) d) ∧
    (¬ (e : ℤ) ∣ m → x m = 0)

private lemma fsum_def {M N : Type*} [Zero M] [AddCommMonoid N] (f : ℤ →₀ M)
    (F : ℤ → M → N) : f.sum F = ∑ a ∈ f.support, F a (f a) := rfl

/-- Sums of a fixed-position monomial family stay fixed-position monomials. -/
private lemma gsingle_set_sum {ι : Type*} (S : Finset ι) (n : ℤ)
    (φ : ι → LaurentPolynomial K')
    (hφ : ∀ a ∈ S, ∃ d : K', φ a = gsingle n d) :
    ∃ d : K', (∑ a ∈ S, φ a) = gsingle n d := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by rw [Finset.sum_empty, gsingle_zero]⟩
  | @insert a S' ha ih =>
    obtain ⟨d1, hd1⟩ := hφ a (Finset.mem_insert_self a S')
    obtain ⟨d2, hd2⟩ := ih (fun b hb => hφ b (Finset.mem_insert_of_mem hb))
    exact ⟨d1 + d2, by rw [Finset.sum_insert ha, hd1, hd2, gsingle_add]⟩

/-- The invariant: supported on `T`-degrees in `eℤ`, with the `z`-position forced to
`−t·(m/e)` at `T`-degree `m`. All `coeffLocSR` generators satisfy it; degree-0 members are
then plain constants. -/
private noncomputable def degSub (he : 1 ≤ e) : Subring (LTwo K') where
  carrier := {x | degP K' e t x}
  zero_mem' := by
    intro m
    refine ⟨fun _ => ⟨0, ?_⟩, fun _ => rfl⟩
    rw [gsingle_zero]; rfl
  one_mem' := by
    intro m
    have h1 : (1 : LTwo K') = osingle 0 (1 : LaurentPolynomial K') := osingle_one.symm
    by_cases hm : m = 0
    · subst hm
      refine ⟨fun _ => ⟨1, ?_⟩, fun hn => absurd (dvd_zero _) hn⟩
      rw [h1, osingle_apply, if_pos rfl,
        show ((0 : ℤ) / (e : ℤ)) = 0 from Int.zero_ediv _, mul_zero, gsingle_one]
    · have hval : (1 : LTwo K') m = 0 := by
        rw [h1, osingle_apply, if_neg (fun h0 => hm h0.symm)]
      exact ⟨fun _ => ⟨0, by rw [hval, gsingle_zero]⟩, fun _ => hval⟩
  add_mem' := by
    intro x y hx hy m
    have hax : (x + y) m = x m + y m := Finsupp.add_apply x y m
    constructor
    · intro hdvd
      obtain ⟨d1, hd1⟩ := (hx m).1 hdvd
      obtain ⟨d2, hd2⟩ := (hy m).1 hdvd
      exact ⟨d1 + d2, by rw [hax, hd1, hd2, gsingle_add]⟩
    · intro hndvd
      rw [hax, (hx m).2 hndvd, (hy m).2 hndvd, add_zero]
  neg_mem' := by
    intro x hx m
    have hax : (-x) m = -(x m) := Finsupp.neg_apply x m
    constructor
    · intro hdvd
      obtain ⟨d, hd⟩ := (hx m).1 hdvd
      exact ⟨-d, by rw [hax, hd, gsingle_neg']⟩
    · intro hndvd
      rw [hax, (hx m).2 hndvd, neg_zero]
  mul_mem' := by
    intro x y hx hy
    intro m
    classical
    have hmul : (x * y) m = x.sum fun m₁ r₁ => y.sum fun m₂ r₂ =>
        if m₁ + m₂ = m then r₁ * r₂ else 0 := AddMonoidAlgebra.mul_apply x y m
    -- within supports, the T-degrees are e-divisible
    have hxd : ∀ a ∈ Finsupp.support x, (e : ℤ) ∣ a := by
      intro a ha
      by_contra hnd
      exact (Finsupp.mem_support_iff.mp ha) ((hx a).2 hnd)
    have hyd : ∀ a ∈ Finsupp.support y, (e : ℤ) ∣ a := by
      intro a ha
      by_contra hnd
      exact (Finsupp.mem_support_iff.mp ha) ((hy a).2 hnd)
    constructor
    · intro hdvd
      rw [hmul, fsum_def]
      refine gsingle_set_sum K' _ _ _ (fun a₁ ha₁ => ?_)
      rw [fsum_def]
      refine gsingle_set_sum K' _ _ _ (fun a₂ ha₂ => ?_)
      by_cases hcase : a₁ + a₂ = m
      · rw [if_pos hcase]
        obtain ⟨u, hu⟩ := hxd a₁ ha₁
        obtain ⟨v, hv⟩ := hyd a₂ ha₂
        obtain ⟨d1, hd1⟩ := (hx a₁).1 ⟨u, hu⟩
        obtain ⟨d2, hd2⟩ := (hy a₂).1 ⟨v, hv⟩
        refine ⟨d1 * d2, ?_⟩
        have he0 : ((e : ℤ)) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
        have hdiv1 : a₁ / (e : ℤ) = u := by rw [hu, Int.mul_ediv_cancel_left _ he0]
        have hdiv2 : a₂ / (e : ℤ) = v := by rw [hv, Int.mul_ediv_cancel_left _ he0]
        have hdivm : m / (e : ℤ) = u + v := by
          rw [← hcase, hu, hv, ← mul_add, Int.mul_ediv_cancel_left _ he0]
        rw [hd1, hd2, gsingle_mul, hdiv1, hdiv2, hdivm]
        congr 1
        ring
      · rw [if_neg hcase]
        exact ⟨0, by rw [gsingle_zero]⟩
    · intro hndvd
      rw [hmul, fsum_def]
      refine Finset.sum_eq_zero (fun a₁ ha₁ => ?_)
      rw [fsum_def]
      refine Finset.sum_eq_zero (fun a₂ ha₂ => ?_)
      rw [if_neg (fun hcase => ?_)]
      apply hndvd
      obtain ⟨u, hu⟩ := hxd a₁ ha₁
      obtain ⟨v, hv⟩ := hyd a₂ ha₂
      exact ⟨u + v, by rw [← hcase, hu, hv, mul_add]⟩

end DegSub

/-! ### G. Named computations at the concrete generators (promoted from the assembly) -/

section Gen
variable {F : Type*} [Field F] (res : ZMod p →+* F) (e h : ℕ) (s t : ℤ)

private lemma RZ_X_val (he : 1 ≤ e) :
    mapK res (RZ e h s t (Polynomial.X : Polynomial ℤ_[p])) = LaurentPolynomial.T s := by
  have h1 : (Polynomial.X : Polynomial ℤ_[p]) = Polynomial.C 1 * Polynomial.X ^ 1 := by
    rw [Polynomial.C_1, one_mul, pow_one]
  conv_lhs => rw [h1]
  rw [RZ_monomial e h he s t one_ne_zero 1, PadicInt.valuation_one, resAt_one,
    mapK_lsingle, map_one]
  rw [show s * ((1 : ℕ) : ℤ) - t * ((0 : ℕ) : ℤ) = s by push_cast; ring]
  exact gsingle_T s

private lemma RZ_Cp_val (he : 1 ≤ e) :
    mapK res (RZ e h s t (Polynomial.C (p : ℤ_[p])))
      = gsingle (-t) (1 : ↥res.fieldRange) := by
  have hp0 : ((p : ℤ_[p])) ≠ 0 := by
    have := ppow_ne_zero (p := p) 1
    rwa [pow_one] at this
  rw [RZ_C e h he s t hp0, PadicInt.valuation_p, mapK_lsingle]
  have h1 : resAt 1 (p : ℤ_[p]) = 1 := by
    have := resAt_p_pow (p := p) 1
    rwa [pow_one] at this
  rw [h1, map_one]
  norm_num

private lemma wgt_Cp : wgt e h (Polynomial.C (p : ℤ_[p])) = (e : ℤ) := by
  have hp0 : ((p : ℤ_[p])) ≠ 0 := by
    have := ppow_ne_zero (p := p) 1
    rwa [pow_one] at this
  rw [wgt_C e h hp0, PadicInt.valuation_p]
  push_cast; ring

/-- The universal realizer: any `↥K`-unit scalar at any nonnegative parent weight. -/
private lemma realize (he : 1 ≤ e) (ν : ℤ) (hν0 : 0 ≤ ν) (c : (↥res.fieldRange)ˣ) :
    ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Polynomial.X B
      ∧ LeanUrat.Moves.gaussVal B = ν
      ∧ mapK res (RZ e h s t B)
          = LaurentPolynomial.C ((c : ↥res.fieldRange)) * LaurentPolynomial.T (- t * ν) := by
  obtain ⟨k, hk⟩ := res.rangeRestrictField_bijective.2 ((c : ↥res.fieldRange))
  have hkne : k ≠ 0 := by
    intro h0
    apply Units.ne_zero c
    rw [← hk, h0, map_zero]
  obtain ⟨hxne, hxval, hxres⟩ := realizer_data hkne ν.toNat
  refine ⟨Polynomial.C ((k.val : ℤ_[p]) * (p : ℤ_[p]) ^ ν.toNat),
    Polynomial.C_ne_zero.mpr hxne, ?_, ?_, ?_⟩
  · rw [inC, Polynomial.degree_X, Polynomial.degree_C hxne]
    decide
  · rw [gaussVal_C hxne, hxval, Int.toNat_of_nonneg hν0]
  · rw [RZ_C e h he s t hxne, hxval, hxres, mapK_lsingle, hk,
      gsingle_eq_C_mul_T, Int.toNat_of_nonneg hν0]

end Gen

end T1B

end T1BaseConstruction

/-- The degree-1 base stage of the read `(X; e, h)` over `K = F_Q = res.fieldRange`
(see the implementation note above). -/
private noncomputable def baseSt {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (res : ZMod p →+* F) (e h : ℕ) (s t : ℤ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (hcop : Nat.gcd e h = 1) (hbez : (e : ℤ) * s + (h : ℤ) * t = 1)
    (he1t : e = 1 → t = 0) : Stage p F where
  e := e
  h := h
  s := s
  t := t
  he := he
  hh := hh
  hcop := hcop
  hbez := hbez
  he1t := he1t
  Φ := Polynomial.X
  hmonic := Polynomial.monic_X
  hdeg := by rw [Polynomial.natDegree_X]
  w := T1B.wgt e h
  wPrev := LeanUrat.Moves.gaussVal
  K := res.fieldRange
  FQ := res.fieldRange
  hFQ_le := le_refl _
  R := fun f => T1B.mapK res (T1B.RZ e h s t f)
  hwmul := fun f g hf hg => T1B.wgt_mul e h he hf hg
  hwult := fun f g hf hg hfg => T1B.wgt_ult e h hf hg hfg
  hvalgrp := by
    refine (AddSubgroup.eq_top_iff' _).mpr (fun n => ?_)
    have hp0 : ((p : ℤ_[p])) ≠ 0 := by
      have := T1B.ppow_ne_zero (p := p) 1
      rwa [pow_one] at this
    have hmem_e : (e : ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[p],
        f ≠ 0 ∧ g ≠ 0 ∧ T1B.wgt e h f - T1B.wgt e h g = n} := by
      exact ⟨Polynomial.C (p : ℤ_[p]), 1, Polynomial.C_ne_zero.mpr hp0, one_ne_zero, by
        rw [T1B.wgt_Cp, T1B.wgt_one, sub_zero]⟩
    have hmem_h : (h : ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[p],
        f ≠ 0 ∧ g ≠ 0 ∧ T1B.wgt e h f - T1B.wgt e h g = n} := by
      exact ⟨Polynomial.X, 1, Polynomial.X_ne_zero, one_ne_zero, by
        rw [T1B.wgt_X, T1B.wgt_one, sub_zero]⟩
    have h1 : (1 : ℤ) ∈ AddSubgroup.closure {n : ℤ | ∃ f g : Polynomial ℤ_[p],
        f ≠ 0 ∧ g ≠ 0 ∧ T1B.wgt e h f - T1B.wgt e h g = n} := by
      have hadd := AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem_e) s)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem_h) t)
      rwa [smul_eq_mul, smul_eq_mul, mul_comm s _, mul_comm t _, hbez] at hadd
    have hn := AddSubgroup.zsmul_mem _ h1 n
    rwa [smul_eq_mul, mul_one] at hn
  hwΦ := T1B.wgt_X e h
  hStretch := by
    intro B hB hBC
    have hBc := T1B.inC_X_eq_C hBC
    have hb0 : B.coeff 0 ≠ 0 := fun h0 => hB (by rw [hBc, h0, Polynomial.C_0])
    conv_lhs => rw [hBc]
    conv_rhs => rw [hBc]
    rw [T1B.wgt_C e h hb0, T1B.gaussVal_C hb0]
  hR0 := by rw [T1B.RZ_zero, map_zero]
  hRne := fun f hf => T1B.mapK_ne res (T1B.RZ_ne e h he s t hbez hf)
  hRmul := fun f g hf hg => by rw [T1B.RZ_mul e h he s t hf hg, map_mul]
  hRadd := fun f g _ _ _ h1 h2 => by rw [T1B.RZ_add e h he s t h1 h2, map_add]
  hRlt := fun f g hf hg _ hlt => by
    rw [T1B.RZ_lt e h he s t hlt (T1B.wgt_strict e h hf hg hlt)]
  hRΦ := T1B.RZ_X_val res e h s t he
  hK1 := T1B.K1_X e h
  hS5 := by
    intro B hB hBC
    have hBc := T1B.inC_X_eq_C hBC
    have hb0 : B.coeff 0 ≠ 0 := fun h0 => hB (by rw [hBc, h0, Polynomial.C_0])
    have hc0ne : res.rangeRestrictField
        (T1B.resAt (B.coeff 0).valuation (B.coeff 0)) ≠ 0 := by
      intro h0
      exact T1B.resAt_level_ne_zero hb0
        (res.rangeRestrictField.injective (h0.trans (map_zero _).symm))
    refine ⟨Units.mk0 _ hc0ne, ?_⟩
    have hgB : LeanUrat.Moves.gaussVal B = ((B.coeff 0).valuation : ℤ) := by
      conv_lhs => rw [hBc]
      exact T1B.gaussVal_C hb0
    conv_lhs => rw [hBc]
    rw [T1B.RZ_C e h he s t hb0, T1B.mapK_lsingle, T1B.gsingle_eq_C_mul_T, hgB,
      Units.val_mk0]
  reps := [Polynomial.C (p : ℤ_[p])]
  hreps := by
    have hp0 : ((p : ℤ_[p])) ≠ 0 := by
      have := T1B.ppow_ne_zero (p := p) 1
      rwa [pow_one] at this
    intro u hu
    rw [List.mem_singleton] at hu
    subst hu
    refine ⟨Polynomial.C_ne_zero.mpr hp0, ?_⟩
    rw [inC, Polynomial.degree_X, Polynomial.degree_C hp0]
    decide
  Tvec := [(Polynomial.C (p : ℤ_[p]), s)]
  hTvec := by simp
  weightSet := Set.Ici (0 : ℤ)
  hWS := by
    intro B hB hBC
    have hBc := T1B.inC_X_eq_C hBC
    have hb0 : B.coeff 0 ≠ 0 := fun h0 => hB (by rw [hBc, h0, Polynomial.C_0])
    rw [Set.mem_Ici]
    conv_rhs => rw [hBc]
    rw [T1B.gaussVal_C hb0]
    positivity
  hS6a := fun ν hν => ⟨1, fun c _ => by
    rw [mul_one]
    exact T1B.realize res e h s t he ν (Set.mem_Ici.mp hν) c⟩
  hS6b := fun ν a hν => T1B.realize res e h s t he ν
    (by rw [T1B.gaussVal_X] at hν; omega) a

section BaseStProj

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
  (res : ZMod p →+* F) (e h : ℕ) (s t : ℤ) (he : 1 ≤ e) (hh : 1 ≤ h)
  (hcop : Nat.gcd e h = 1) (hbez : (e : ℤ) * s + (h : ℤ) * t = 1)
  (he1t : e = 1 → t = 0)

private lemma baseSt_w :
    (baseSt res e h s t he hh hcop hbez he1t).w = T1B.wgt e h := rfl
private lemma baseSt_wPrev :
    (baseSt res e h s t he hh hcop hbez he1t).wPrev = LeanUrat.Moves.gaussVal := rfl
private lemma baseSt_R : (baseSt res e h s t he hh hcop hbez he1t).R
    = fun f => T1B.mapK res (T1B.RZ e h s t f) := rfl
private lemma baseSt_Phi :
    (baseSt res e h s t he hh hcop hbez he1t).Φ = Polynomial.X := rfl
private lemma baseSt_t : (baseSt res e h s t he hh hcop hbez he1t).t = t := rfl
private lemma baseSt_s : (baseSt res e h s t he hh hcop hbez he1t).s = s := rfl
private lemma baseSt_h : (baseSt res e h s t he hh hcop hbez he1t).h = h := rfl
private lemma baseSt_reps : (baseSt res e h s t he hh hcop hbez he1t).reps
    = [Polynomial.C (p : ℤ_[p])] := rfl
private lemma baseSt_Tvec : (baseSt res e h s t he hh hcop hbez he1t).Tvec
    = [(Polynomial.C (p : ℤ_[p]), s)] := rfl

end BaseStProj

/-- Unit T1: for every legal base read there is a faithfully-based stage with the
full round-5 core, at the read's index (blueprint display verbatim). -/
theorem T1_baseStage {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (e h : ℕ) (bdata : BaseReadData p F e h) :
    ∃ σ : Stage p F, IsBaseStage σ ∧ StageCoreL σ ∧ σ.e = e ∧ σ.h = h := by
  classical
  obtain ⟨s, t, hbez, he1t⟩ :
      ∃ s t : ℤ, (e : ℤ) * s + (h : ℤ) * t = 1 ∧ (e = 1 → t = 0) := by
    rcases eq_or_ne e 1 with he1 | hne
    · exact ⟨1, 0, by rw [he1]; push_cast; ring, fun _ => rfl⟩
    · refine ⟨Nat.gcdA e h, Nat.gcdB e h, ?_, fun h1 => absurd h1 hne⟩
      have hg := Nat.gcd_eq_gcd_ab e h
      rw [bdata.hcop] at hg
      push_cast at hg ⊢
      linarith [hg]
  have he := bdata.he
  have hh := bdata.hh
  set res := bdata.res with hres
  set σ : Stage p F := baseSt res e h s t he hh bdata.hcop hbez he1t with hσ
  refine ⟨σ, ⟨fun f _ => rfl, rfl, rfl⟩, ?_, rfl, rfl⟩
  -- StageCoreL
  have hjump' : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      σ.w f = σ.w g → σ.w f < σ.w (f + g) → σ.R f + σ.R g = 0 :=
    fun f g _ _ _ h1 h2 => by
      show T1B.mapK res (T1B.RZ e h s t f) + T1B.mapK res (T1B.RZ e h s t g) = 0
      rw [← map_add, T1B.RZ_jump e h he s t h1 h2, map_zero]
  have hneg' : ∀ f : Polynomial ℤ_[p], σ.R (-f) = - σ.R f :=
    fun f => by
      show T1B.mapK res (T1B.RZ e h s t (-f)) = - T1B.mapK res (T1B.RZ e h s t f)
      rw [T1B.RZ_neg, map_neg]
  have hstrict' : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 →
      σ.w f < σ.w g → σ.w (f + g) = σ.w f :=
    fun f g hf hg hlt => T1B.wgt_strict e h hf hg hlt
  have he0 : ((e : ℤ)) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  -- the two graded-unit values (consumed by TvecUnitLaw and CoeffLocLaw)
  have hgrX : σ.grRes Polynomial.X
      = ((T1B.umono s ((h : ℕ) : ℤ) : (LTwo ↥res.fieldRange)ˣ) : LTwo ↥res.fieldRange) := by
    have hRX' : σ.R Polynomial.X = LaurentPolynomial.T s := T1B.RZ_X_val res e h s t he
    have hwX' : σ.w Polynomial.X = ((h : ℕ) : ℤ) := T1B.wgt_X e h
    rw [Stage.grRes, hRX', hwX', T1B.umono_val, T1B.osingle_eq_C_mul_T, T1B.gsingle_T]
    rfl
  have hgrCp : σ.grRes (Polynomial.C (p : ℤ_[p]))
      = ((T1B.umono (-t) ((e : ℕ) : ℤ) : (LTwo ↥res.fieldRange)ˣ) : LTwo ↥res.fieldRange) := by
    have hRCp' : σ.R (Polynomial.C (p : ℤ_[p]))
        = T1B.gsingle (-t) (1 : ↥res.fieldRange) := T1B.RZ_Cp_val res e h s t he
    have hwCp' : σ.w (Polynomial.C (p : ℤ_[p])) = ((e : ℕ) : ℤ) := T1B.wgt_Cp e h
    rw [Stage.grRes, hRCp', hwCp', T1B.umono_val, T1B.osingle_eq_C_mul_T]
    rfl
  have hPhi : σ.Φ = Polynomial.X := rfl
  refine ⟨{ wPrev_mul := fun f g hf hg => L1_gaussVal_mul f g hf hg
            wPrev_ult := ?_
            reps_nonempty := by rw [hσ, baseSt_reps]; simp
            p_is_rep := by rw [hσ, baseSt_reps]; simp
            w_strict := hstrict'
            w_jump := hjump'
            R_neg := hneg'
            tvec := ?_
            prevIaug := ?_
            slot := LeanUrat.Moves.L2_slotDecomp σ hstrict' hjump' hneg'
            coeff := ?_ }, ?_, ?_⟩
  · -- wPrev_ult
    intro f g hf hg hfg
    show min (LeanUrat.Moves.gaussVal f) (LeanUrat.Moves.gaussVal g)
      ≤ LeanUrat.Moves.gaussVal (f + g)
    rw [T1B.gaussVal_eq_wgt f, T1B.gaussVal_eq_wgt g, T1B.gaussVal_eq_wgt (f + g)]
    exact T1B.wgt_ult 1 0 hf hg hfg
  · -- TvecLaw
    have hA : ((s.toNat : ℕ) : ℤ) - (((-s).toNat : ℕ) : ℤ) = s := Int.toNat_sub_toNat_neg s
    have hB : ((t.toNat : ℕ) : ℤ) - (((-t).toNat : ℕ) : ℤ) = t := Int.toNat_sub_toNat_neg t
    have hnum : σ.tvecNum
        = Polynomial.C ((p : ℤ_[p]) ^ s.toNat) * Polynomial.X ^ t.toNat := by
      rw [Stage.tvecNum, hσ, baseSt_Tvec, baseSt_Phi, baseSt_t]
      rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ← Polynomial.C_pow]
    have hden : σ.tvecDen
        = Polynomial.C ((p : ℤ_[p]) ^ (-s).toNat) * Polynomial.X ^ (-t).toNat := by
      rw [Stage.tvecDen, hσ, baseSt_Tvec, baseSt_Phi, baseSt_t]
      rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ← Polynomial.C_pow]
    constructor
    · rw [hnum, hden, hσ, baseSt_w,
        T1B.wgt_monomial e h (T1B.ppow_ne_zero _) _,
        T1B.wgt_monomial e h (T1B.ppow_ne_zero _) _,
        T1B.valuation_p_pow, T1B.valuation_p_pow]
      linear_combination (e : ℤ) * hA + (h : ℤ) * hB + hbez
    · rw [hnum, hden, hσ, baseSt_R]
      show T1B.mapK res (T1B.RZ e h s t _) = T1B.mapK res (T1B.RZ e h s t _)
      rw [T1B.RZ_monomial e h he s t (T1B.ppow_ne_zero _) _,
        T1B.RZ_monomial e h he s t (T1B.ppow_ne_zero _) _,
        T1B.valuation_p_pow, T1B.valuation_p_pow, T1B.resAt_p_pow, T1B.resAt_p_pow]
      have hP : s * ((t.toNat : ℕ) : ℤ) - t * ((s.toNat : ℕ) : ℤ)
          = s * (((-t).toNat : ℕ) : ℤ) - t * (((-s).toNat : ℕ) : ℤ) := by
        linear_combination s * hB - t * hA
      rw [hP]
  · -- prevIaug
    show ((σ.e : ℕ) : ℤ) * σ.wPrev σ.Φ < ((σ.h : ℕ) : ℤ)
    rw [hσ, baseSt_wPrev, baseSt_Phi]
    show (e : ℤ) * LeanUrat.Moves.gaussVal (Polynomial.X : Polynomial ℤ_[p]) < (h : ℤ)
    rw [T1B.gaussVal_X, mul_zero]
    exact_mod_cast hh
  · -- CoeffFieldLawCore
    refine ⟨?_, ?_, ?_⟩
    · -- (⊇) every scalar realized at ν = 0
      intro c
      obtain ⟨B, hB0, hBC, hg0, hRB⟩ := T1B.realize res e h s t he 0 le_rfl c
      exact ⟨B, 0, hB0, hBC, hg0, hRB⟩
    · -- fixed-position lines are K-lines
      intro f g hfP hgP hf0 hg0 hw
      show ∃ d : ↥res.fieldRange, T1B.mapK res (T1B.RZ e h s t f)
        = LaurentPolynomial.C d * T1B.mapK res (T1B.RZ e h s t g)
      obtain ⟨lf, hlf, hfeq⟩ := hfP
      obtain ⟨lg, hlg, hgeq⟩ := hgP
      rw [hσ, baseSt_Phi] at hlf hlg
      obtain ⟨x, hx⟩ := T1B.coeffProd_is_C hlf
      obtain ⟨y, hy⟩ := T1B.coeffProd_is_C hlg
      rw [hσ, baseSt_w] at hw
      rw [hfeq, hx] at hf0 hw ⊢
      rw [hgeq, hy] at hg0 hw ⊢
      have hx0 : x ≠ 0 := fun h0 => hf0 (by rw [h0, Polynomial.C_0])
      have hy0 : y ≠ 0 := fun h0 => hg0 (by rw [h0, Polynomial.C_0])
      rw [T1B.wgt_C e h hx0, T1B.wgt_C e h hy0] at hw
      have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast (by omega : 0 < e)
      have hveq : (x.valuation : ℤ) = (y.valuation : ℤ) :=
        mul_left_cancel₀ (ne_of_gt he') hw
      have hcy : res.rangeRestrictField (T1B.resAt y.valuation y) ≠ 0 := by
        intro h0
        exact T1B.resAt_level_ne_zero hy0
          (res.rangeRestrictField.injective (h0.trans (map_zero _).symm))
      refine ⟨res.rangeRestrictField (T1B.resAt x.valuation x)
        * (res.rangeRestrictField (T1B.resAt y.valuation y))⁻¹, ?_⟩
      rw [T1B.RZ_C e h he s t hx0, T1B.RZ_C e h he s t hy0, T1B.mapK_lsingle,
        T1B.mapK_lsingle, hveq, T1B.gsingle_C_smul, inv_mul_cancel_right₀ hcy]
    · -- the degree-0 exponent group is all of ℤ
      refine (AddSubgroup.eq_top_iff' _).mpr (fun n => ?_)
      have hXe0 : (Polynomial.X ^ e : Polynomial ℤ_[p]) ≠ 0 :=
        pow_ne_zero _ Polynomial.X_ne_zero
      have hCph0 : (Polynomial.C ((p : ℤ_[p]) ^ h)) ≠ 0 :=
        Polynomial.C_ne_zero.mpr (T1B.ppow_ne_zero h)
      have hXeform : (Polynomial.X ^ e : Polynomial ℤ_[p])
          = Polynomial.C 1 * Polynomial.X ^ e := by rw [Polynomial.C_1, one_mul]
      have hRXe : σ.R (Polynomial.X ^ e)
          = LaurentPolynomial.C 1 * LaurentPolynomial.T (s * (e : ℤ)) := by
        rw [hσ, baseSt_R]
        show T1B.mapK res (T1B.RZ e h s t (Polynomial.X ^ e)) = _
        conv_lhs => rw [hXeform]
        rw [T1B.RZ_monomial e h he s t one_ne_zero e, PadicInt.valuation_one,
          T1B.resAt_one, T1B.mapK_lsingle, map_one, T1B.gsingle_eq_C_mul_T]
        rw [show s * ((e : ℕ) : ℤ) - t * ((0 : ℕ) : ℤ) = s * (e : ℤ) by push_cast; ring]
        rfl
      have hRCph : σ.R (Polynomial.C ((p : ℤ_[p]) ^ h))
          = LaurentPolynomial.C 1 * LaurentPolynomial.T (- t * (h : ℤ)) := by
        rw [hσ, baseSt_R]
        show T1B.mapK res (T1B.RZ e h s t (Polynomial.C ((p : ℤ_[p]) ^ h))) = _
        rw [T1B.RZ_C e h he s t (T1B.ppow_ne_zero h), T1B.valuation_p_pow,
          T1B.resAt_p_pow, T1B.mapK_lsingle, map_one, T1B.gsingle_eq_C_mul_T]
        rfl
      have h1 : (1 : ℤ) ∈ AddSubgroup.closure {n : ℤ |
          ∃ (f g : Polynomial ℤ_[p]) (c c' : ↥σ.K) (k k' : ℤ),
            IsUnitMonProd σ f ∧ IsUnitMonProd σ g ∧ f ≠ 0 ∧ g ≠ 0
            ∧ σ.w f = σ.w g
            ∧ σ.R f = LaurentPolynomial.C c * LaurentPolynomial.T k
            ∧ σ.R g = LaurentPolynomial.C c' * LaurentPolynomial.T k'
            ∧ n = k - k'} := by
        apply AddSubgroup.subset_closure
        refine ⟨Polynomial.X ^ e, Polynomial.C ((p : ℤ_[p]) ^ h), 1, 1,
          s * (e : ℤ), - t * (h : ℤ), ?_, ?_, hXe0, hCph0, ?_, hRXe, hRCph,
          by linear_combination -hbez⟩
        · refine ⟨[], e, by intro u hu; simp at hu, ?_⟩
          rw [List.prod_nil, one_mul, hσ, baseSt_Phi]
        · refine ⟨[Polynomial.C ((p : ℤ_[p]) ^ h)], 0, ?_, ?_⟩
          · intro u hu
            rw [List.mem_singleton] at hu
            subst hu
            refine ⟨hCph0, ?_⟩
            rw [hσ, baseSt_Phi, inC, Polynomial.degree_X,
              Polynomial.degree_C (T1B.ppow_ne_zero h)]
            decide
          · rw [List.prod_cons, List.prod_nil, mul_one, pow_zero, mul_one]
        · rw [hσ, baseSt_w]
          conv_lhs => rw [hXeform]
          rw [T1B.wgt_monomial e h one_ne_zero e, PadicInt.valuation_one,
            T1B.wgt_C e h (T1B.ppow_ne_zero h), T1B.valuation_p_pow]
          push_cast; ring
      have hn := AddSubgroup.zsmul_mem _ h1 n
      rwa [smul_eq_mul, mul_one] at hn
  · -- TvecUnitLaw
    have hgrXσ : σ.grRes Polynomial.X
        = ((T1B.umono (K' := ↥σ.K) s ((h : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) := hgrX
    have hgrCpσ : σ.grRes (Polynomial.C (p : ℤ_[p]))
        = ((T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) := hgrCp
    refine ⟨T1B.umono s ((h : ℕ) : ℤ), fun _ => T1B.umono (-t) ((e : ℕ) : ℤ), ?_, ?_, ?_⟩
    · show ((T1B.umono (K' := ↥σ.K) s ((h : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
        = σ.grRes σ.Φ
      rw [hPhi, hgrXσ]
    · intro i
      show ((T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
        = σ.grRes ((σ.Tvec.get i).1)
      have hget : (σ.Tvec.get i).1 = Polynomial.C (p : ℤ_[p]) := by
        show ((([(Polynomial.C (p : ℤ_[p]), s)] : List _).get i).1) = _
        rw [T1B.list_get_singleton]
      rw [hget, hgrCpσ]
    · show (∏ i : Fin 1, T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ)
          ^ ((([(Polynomial.C (p : ℤ_[p]), s)] : List _).get i).2))
          * T1B.umono s ((h : ℕ) : ℤ) ^ t = locT ↥σ.K
      rw [Fin.prod_univ_one, T1B.list_get_singleton, T1B.umono_zpow, T1B.umono_zpow,
        T1B.umono_mul]
      rw [show s * -t + t * s = 0 by ring,
        show s * ((e : ℕ) : ℤ) + t * ((h : ℕ) : ℤ) = 1 by linear_combination hbez]
      apply Units.ext
      show T1B.osingle 1 (T1B.gsingle 0 1) = LaurentPolynomial.T 1
      rw [T1B.gsingle_one]
      rfl
  · -- CoeffLocLaw
    have hgrXσ : σ.grRes Polynomial.X
        = ((T1B.umono (K' := ↥σ.K) s ((h : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) := hgrX
    have hgrCpσ : σ.grRes (Polynomial.C (p : ℤ_[p]))
        = ((T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) := hgrCp
    refine ⟨?_, ?_, ?_⟩
    · -- (i) degree-0 members of the coefficient localization are K-constants
      intro ℓ hℓ
      have hsub : σ.coeffLocSR ≤ T1B.degSub (↥σ.K) e t he := by
        rw [Stage.coeffLocSR]
        apply Subring.closure_le.mpr
        rintro x (⟨B, hB0, hBC, rfl⟩ | ⟨i, u, hu, rfl⟩)
        · -- generator: initial forms of coefficients
          rw [hσ, baseSt_Phi] at hBC
          have hBc := T1B.inC_X_eq_C hBC
          have hb0 : B.coeff 0 ≠ 0 := fun h0 => hB0 (by rw [hBc, h0, Polynomial.C_0])
          have hR : σ.R B = T1B.gsingle (-t * ((B.coeff 0).valuation : ℤ))
              (res.rangeRestrictField (T1B.resAt (B.coeff 0).valuation (B.coeff 0))) := by
            show T1B.mapK res (T1B.RZ e h s t B) = _
            conv_lhs => rw [hBc]
            rw [T1B.RZ_C e h he s t hb0, T1B.mapK_lsingle]
          have hw : σ.w B = (e : ℤ) * ((B.coeff 0).valuation : ℤ) := by
            show T1B.wgt e h B = _
            conv_lhs => rw [hBc]
            exact T1B.wgt_C e h hb0
          have hx : σ.grRes B
              = T1B.osingle (K' := ↥σ.K) ((e : ℤ) * ((B.coeff 0).valuation : ℤ))
                (T1B.gsingle (-t * ((B.coeff 0).valuation : ℤ))
                  (res.rangeRestrictField (T1B.resAt (B.coeff 0).valuation (B.coeff 0)))) := by
            rw [Stage.grRes, hR, hw, T1B.osingle_eq_C_mul_T]
            rfl
          rw [hx]
          show T1B.degP _ e t _
          intro m
          constructor
          · intro _
            by_cases hm : (e : ℤ) * ((B.coeff 0).valuation : ℤ) = m
            · refine ⟨res.rangeRestrictField
                (T1B.resAt (B.coeff 0).valuation (B.coeff 0)), ?_⟩
              rw [T1B.osingle_apply, if_pos hm]
              rw [show m / (e : ℤ) = ((B.coeff 0).valuation : ℤ) by
                rw [← hm, Int.mul_ediv_cancel_left _ he0]]
            · exact ⟨0, by rw [T1B.osingle_apply, if_neg hm, T1B.gsingle_zero]⟩
          · intro hndvd
            rw [T1B.osingle_apply, if_neg (fun hm => hndvd (by rw [← hm]; exact ⟨_, rfl⟩))]
        · -- generator: inverses of the representative units
          have hget : σ.reps.get i = Polynomial.C (p : ℤ_[p]) := by
            show (([Polynomial.C (p : ℤ_[p])] : List _).get i) = _
            rw [T1B.list_get_singleton]
          have hu2 : ((u : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
              = σ.grRes (Polynomial.C (p : ℤ_[p])) := by
            rw [← hget]
            exact hu
          have hu' : u = T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ) :=
            Units.ext (by rw [hu2, hgrCpσ])
          rw [hu', T1B.umono_inv, T1B.umono_val]
          show T1B.degP _ e t _
          intro m
          constructor
          · intro _
            by_cases hm : -((e : ℕ) : ℤ) = m
            · refine ⟨1, ?_⟩
              rw [T1B.osingle_apply, if_pos hm]
              rw [show m / (e : ℤ) = -1 by
                rw [← hm, show -((e : ℕ) : ℤ) = (e : ℤ) * (-1) by ring,
                  Int.mul_ediv_cancel_left _ he0]]
              rw [show -t * (-1 : ℤ) = - -t by ring]
            · exact ⟨0, by rw [T1B.osingle_apply, if_neg hm, T1B.gsingle_zero]⟩
          · intro hndvd
            rw [T1B.osingle_apply, if_neg (fun hm => hndvd (by
              rw [← hm]; exact ⟨-1, by ring⟩))]
      have hd : T1B.degP (↥σ.K) e t (LaurentPolynomial.C ℓ) := hsub hℓ
      obtain ⟨d, hdeq⟩ := (hd 0).1 ⟨0, by ring⟩
      refine ⟨d, ?_⟩
      rw [show (LaurentPolynomial.C ℓ : LTwo ↥σ.K) = T1B.osingle 0 ℓ from
        (T1B.osingle_C ℓ).symm, T1B.osingle_apply, if_pos rfl] at hdeq
      rw [Int.zero_ediv, mul_zero, T1B.gsingle_C] at hdeq
      exact hdeq
    · -- (ii) K-constants live in the localization
      intro d
      by_cases hd0 : d = 0
      · subst hd0
        rw [map_zero, map_zero]
        exact Subring.zero_mem _
      · obtain ⟨B, hB0, hBC, hg0, hRB⟩ :=
          T1B.realize res e h s t he 0 le_rfl (Units.mk0 d hd0)
        apply Subring.subset_closure
        left
        refine ⟨B, hB0, by rw [hσ, baseSt_Phi]; exact hBC, ?_⟩
        have hBc := T1B.inC_X_eq_C hBC
        have hb0 : B.coeff 0 ≠ 0 := fun h0 => hB0 (by rw [hBc, h0, Polynomial.C_0])
        have hRB' : σ.R B = LaurentPolynomial.C d := by
          show T1B.mapK res (T1B.RZ e h s t B) = _
          rw [hRB, Units.val_mk0, show -t * (0 : ℤ) = 0 by ring,
            LaurentPolynomial.T_zero, mul_one]
          rfl
        have hwB : σ.w B = 0 := by
          show T1B.wgt e h B = 0
          have hgB : LeanUrat.Moves.gaussVal B = ((B.coeff 0).valuation : ℤ) := by
            conv_lhs => rw [hBc]
            exact T1B.gaussVal_C hb0
          have hv : ((B.coeff 0).valuation : ℤ) = 0 := by omega
          conv_lhs => rw [hBc]
          rw [T1B.wgt_C e h hb0, hv, mul_zero]
        rw [Stage.grRes, hRB', hwB, LaurentPolynomial.T_zero, mul_one]
    · -- (iii) the z-pinning
      refine ⟨(fun _ => -((h : ℕ) : ℤ), ((e : ℕ) : ℤ)), T1B.umono 1 0, ?_, ?_, ?_⟩
      · -- weight 0
        show (∑ i : Fin 1, -((h : ℕ) : ℤ)
              * σ.w (([Polynomial.C (p : ℤ_[p])] : List _).get i))
            + ((e : ℕ) : ℤ) * ((h : ℕ) : ℤ) = 0
        rw [Fin.sum_univ_one, T1B.list_get_singleton,
          show σ.w (Polynomial.C (p : ℤ_[p])) = ((e : ℕ) : ℤ) from T1B.wgt_Cp e h]
        ring
      · -- IsLVecVal
        refine ⟨fun _ => T1B.umono (-t) ((e : ℕ) : ℤ), T1B.umono s ((h : ℕ) : ℤ), ?_, ?_, ?_⟩
        · intro i
          show ((T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
            = σ.grRes (σ.reps.get i)
          have hget : σ.reps.get i = Polynomial.C (p : ℤ_[p]) := by
            show (([Polynomial.C (p : ℤ_[p])] : List _).get i) = _
            rw [T1B.list_get_singleton]
          rw [hget, hgrCpσ]
        · show ((T1B.umono (K' := ↥σ.K) s ((h : ℕ) : ℤ) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
            = σ.grRes σ.Φ
          rw [hPhi, hgrXσ]
        · show T1B.umono 1 0 = (∏ _i : Fin 1, T1B.umono (K' := ↥σ.K) (-t) ((e : ℕ) : ℤ)
              ^ (-((h : ℕ) : ℤ))) * T1B.umono s ((h : ℕ) : ℤ) ^ ((e : ℕ) : ℤ)
          rw [Fin.prod_univ_one, T1B.umono_zpow, T1B.umono_zpow, T1B.umono_mul]
          rw [show -((h : ℕ) : ℤ) * -t + ((e : ℕ) : ℤ) * s = 1 by linear_combination hbez,
            show -((h : ℕ) : ℤ) * ((e : ℕ) : ℤ) + ((e : ℕ) : ℤ) * ((h : ℕ) : ℤ) = 0 by ring]
      · -- value = C z
        show ((T1B.umono (K' := ↥σ.K) 1 0 : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
          = LaurentPolynomial.C (zvar ↥σ.K)
        rw [T1B.umono_val, T1B.osingle_C, T1B.gsingle_T]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T1_baseStage
