/-
HDISCHARGE_H1 §5.2 — `H1/Order1.lean`: the proved-slice instances (wave 1; the
non-vacuity gates). This file is the landing site for H1-U5 (`kpBlock_base`),
H1-U6 (`grb_key_laws_base`), and H1-U7 (`key1SiteBlock_base`).

CURRENT CONTENT: H1-U6 + H1-U7.

STATEMENT PROVENANCE FLAG (H1-U7 prover, 2026-08-01; extended by the H1-U6 prover,
2026-08-01): the blueprint's §5.2 H1-U6/U7 bullets carry NO displayed verbatim Lean
statements (unlike the §5.1 rows) — U6's spec is "the order-1 `GrBKeyLaws` instance:
math source GD23 RES-1 + KEY-g(iii)", statement shape per the §5.1 U3 row, binder
block PROBE-FIRST (the §5.2 discipline). The U6 statement below was probed against
the corpus base carriers (`U31.bStage`/`HK13.bStageP`: `s = 1`, `t = 0`, `h = 1`;
the U31 inert gate read: `e = 1`, `h = 1`) and is stated at the base CONFIGURATION
pins (`hσs`/`hσt`/`hνe`/`hlevel`), not at a hard-coded carrier, so both bStage-family
instances are hosted. E-phase/orchestrator sign-off on the binder shape is REQUIRED
before citing either unit as the §5.2 retirement.

H1-U6 honesty ledger (what is PROVED vs what is a ROW):
* `key_res` — PROVED (`nodeLift_key_res`): GD23 KEY-g(iii) at order 1, the residual
  of the standard lift IS `toLaurent ψ` on the nose (`c = 1`, `k = 0`), from
  `IsNodeLift` + the stage residual laws (`hRmul`/`hRadd`/`hRΦ`/`hK1`).
* `faithful_at` — PROVED FROM the named row `SiteDevPin` (`faithful_at_of_sitePin`):
  the graded halves (GD23 (GR-B)(4) order-1 shadow) are genuine theorems of the
  `GenuineStageModel` laws — positive half via `L1_initialForm_add_lt`/`_mul` +
  `kpa_init`, negative half via gr-domain cancellation (`L1_gr_domain_iff_val`) +
  `kpa_block`. The row `SiteDevPin` (below) is the RES-1 recorded-site march input
  — "an anchored f's σ'-development has its FIRST minimal slot at exactly ν.μ" —
  the order-1 dictionary tie between the node's recorded (hOrd/hRanch) site and the
  child slots. Its derivation from `hOrd`/`hRanch` is the S9/child-residual
  machinery (HC1 S9w/`ChildResData`), NOT re-proved here; per the [M]-hypothesis
  discipline it stays a NAMED structure row (the `DevBound` precedent, blueprint
  §5.3), never an axiom. DEVIATION NOTE against the §5.2 input list: the listed
  inputs `L3_residual_mul`/`L4_grRes_eq_genuine` were probed and NOT consumed — the
  Θ/LTwo route trivializes ψhom-divisibility (every localization image of ψhom is a
  unit), so the graded halves are proved Gr-intrinsically instead; `hOrd`/`hRanch`
  are consumed by `SiteDevPin`'s discharge, not by this file.
-/
import LeanUrat.Scaffold.HDischarge.H1.Defs
import LeanUrat.Scaffold.DictIII.GDOrder1
import LeanUrat.MovesGr.L0_initialForm_ne_zero
import LeanUrat.MovesGr.L1_initialForm_mul
import LeanUrat.MovesGr.L1_initialForm_add_lt
import LeanUrat.MovesGr.L1_gr_domain_iff_val_v3
import LeanUrat.MovesGr.L4_grRes_eq_genuine

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ## H1-U6 stage-level helpers: residual apparatus consequences -/

section StageHelpers

variable (σ : Stage p F)

/-- `R 1 = 1` — from the pinned key residual `R Φ = T^s` (a unit), no domain needed. -/
theorem stage_R_one : σ.R 1 = 1 := by
  have h := σ.hRmul σ.Φ 1 σ.hmonic.ne_zero one_ne_zero
  rw [mul_one, σ.hRΦ] at h
  have h2 := congrArg (fun x => LaurentPolynomial.T (-σ.s) * x) h
  simp only [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
    LaurentPolynomial.T_zero, one_mul] at h2
  exact h2.symm

/-- The stage key has positive degree (`hdeg` in `WithBot ℕ` form). -/
theorem stage_degree_pos : (0 : WithBot ℕ) < σ.Φ.degree :=
  Polynomial.natDegree_pos_iff_degree_pos.mp
    (show 0 < σ.Φ.natDegree by have := σ.hdeg; omega)

/-- `w (f^n) = n · w f` for `f ≠ 0`. -/
theorem stage_w_pow (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    ∀ n : ℕ, σ.w (f ^ n) = (n : ℤ) * σ.w f := by
  intro n
  induction n with
  | zero =>
    have h := σ.hwmul (f ^ 0) (f ^ 0) (pow_ne_zero 0 hf) (pow_ne_zero 0 hf)
    rw [pow_zero, mul_one] at h
    simpa using by omega
  | succ n ih =>
    rw [pow_succ, σ.hwmul (f ^ n) f (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

/-- `R (f^n) = (R f)^n` for `f ≠ 0`. -/
theorem stage_R_pow (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    ∀ n : ℕ, σ.R (f ^ n) = (σ.R f) ^ n := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, stage_R_one]
  | succ n ih => rw [pow_succ, pow_succ, σ.hRmul (f ^ n) f (pow_ne_zero n hf) hf, ih]

end StageHelpers

/-! ## H1-U6 leg 1: the key residual (GD23 KEY-g(iii) at order 1) -/

/-- **H1-U6 leg 1 — `key_res` at the base configuration** (GD23 KEY-g(iii), order 1):
at a node whose frame carries the base pins (`s = 1`, `t = 0`, so in particular any
`bStage`/`bStageP`-headed read) and whose read is level for the frame scale
(`e = 1`, `h = σ.h` — the inert/KEY1 configuration of the §5.2 U5 bullet, `d₀ = 1`),
the frame residual of ANY `IsNodeLift` key is `toLaurent ψ` on the nose: all lift
terms share the frame weight `g·σ.h`, so `hRadd` recomposes the ψ-digits along the
`T`-powers with no carries. This is the honest order-1 shadow of (GR-B-KEY)(3). -/
theorem nodeLift_key_res (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) (hνe : ν.e = 1) (hlevel : ν.h = ν.σ.h)
    (hΦ : IsNodeLift ν Φhat) :
    ∃ (c : (↥ν.σ.K)ˣ) (k : ℤ),
      ν.σ.R Φhat = LaurentPolynomial.C ((c : ↥ν.σ.K)) * LaurentPolynomial.T k *
        Polynomial.toLaurent ν.ψ := by
  classical
  obtain ⟨tt, h0, hcl, heq⟩ := hΦ
  set g := ν.g with hg
  set σ := ν.σ with hσ
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  -- the full coefficient family of the lift, slots 0..g
  set BB : ℕ → Polynomial ℤ_[p] :=
    fun k => if k < g then tt k else if k = g then 1 else 0 with hBB
  -- the lift is the (g+1)-slot development Σ BB k · Φ^k
  have hkey : Φhat = ∑ k ∈ Finset.range (g + 1), BB k * σ.Φ ^ k := by
    rw [Finset.sum_range_succ]
    have h1 : ∑ k ∈ Finset.range g, BB k * σ.Φ ^ k =
        ∑ k ∈ Finset.range g, tt k * σ.Φ ^ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hBB]
      simp [Finset.mem_range.mp hk]
    have h2 : BB g = 1 := by rw [hBB]; simp
    rw [h1, h2, one_mul, heq, hνe]
    simp only [one_mul]
    exact add_comm _ _
  -- ψ-digit facts: `BB k ≠ 0 ↔ ψ.coeff k ≠ 0` on slots ≤ g, with the recorded data
  have hψg : ν.ψ.coeff g = 1 := by
    have := ν.hψmonic.coeff_natDegree
    rwa [ν.hψdeg] at this
  -- per-slot residual and weight
  have hslotR : ∀ k ≤ g, BB k ≠ 0 →
      σ.R (BB k * σ.Φ ^ k) =
        LaurentPolynomial.C (ν.ψ.coeff k) * LaurentPolynomial.T (k : ℤ) := by
    intro k hk hBk
    rcases lt_or_eq_of_le hk with hklt | hkeq
    · have httk : tt k ≠ 0 := by
        intro h
        apply hBk
        rw [hBB]
        simp [hklt, h]
      have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
      obtain ⟨_, _, _, hR⟩ := hcl k hklt hψk
      have hBBk : BB k = tt k := by rw [hBB]; simp [hklt]
      rw [hBBk, σ.hRmul (tt k) (σ.Φ ^ k) httk (pow_ne_zero k hΦne),
        stage_R_pow σ σ.Φ hΦne k, σ.hRΦ, hR, hσt, LaurentPolynomial.T_pow, hσs]
      simp [LaurentPolynomial.T_zero]
    · have hBBk : BB k = 1 := by rw [hBB]; simp [hkeq]
      rw [hBBk, one_mul, stage_R_pow σ σ.Φ hΦne k, σ.hRΦ,
        LaurentPolynomial.T_pow, hσs, hkeq, hψg]
      simp
  have hslotW : ∀ k ≤ g, BB k ≠ 0 →
      σ.w (BB k) + (k : ℤ) * σ.w σ.Φ = (g : ℤ) * (σ.h : ℤ) := by
    intro k hk hBk
    rcases lt_or_eq_of_le hk with hklt | hkeq
    · have httk : tt k ≠ 0 := by
        intro h
        apply hBk
        rw [hBB]
        simp [hklt, h]
      have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
      obtain ⟨_, _, hw, _⟩ := hcl k hklt hψk
      have hBBk : BB k = tt k := by rw [hBB]; simp [hklt]
      rw [hBBk, hw, σ.hwΦ, hlevel]
      ring
    · have hBBk : BB k = 1 := by rw [hBB]; simp [hkeq]
      have hw1 : σ.w 1 = 0 := by
        have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
        rw [mul_one] at h
        omega
      rw [hBBk, hw1, σ.hwΦ, hkeq]
      ring
  -- degrees: every slot is a coefficient (deg < deg Φ)
  have hdegBB : ∀ k, (BB k).degree < σ.Φ.degree := by
    intro k
    have hΦdeg : (0 : WithBot ℕ) < σ.Φ.degree := stage_degree_pos σ
    rw [hBB]
    by_cases hklt : k < g
    · simp only [if_pos hklt]
      by_cases httk : tt k = 0
      · rw [httk]; simpa using lt_of_le_of_lt bot_le hΦdeg
      · have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
        obtain ⟨_, hin, _, _⟩ := hcl k hklt hψk
        exact hin
    · simp only [if_neg hklt]
      by_cases hkeq : k = g
      · simpa [hkeq, Polynomial.degree_one] using hΦdeg
      · simpa [hkeq] using lt_of_le_of_lt bot_le hΦdeg
  -- partial sums: residual recomposition by induction (all slots share weight g·σ.h)
  have main : ∀ m, m ≤ g + 1 →
      σ.R (∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) =
        ∑ k ∈ Finset.range m, LaurentPolynomial.C (ν.ψ.coeff k) *
          LaurentPolynomial.T (k : ℤ) ∧
      ((∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) ≠ 0 →
        σ.w (∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) = (g : ℤ) * (σ.h : ℤ)) := by
    intro m
    induction m with
    | zero => intro _; simp [σ.hR0]
    | succ m ih =>
      intro hm1
      have hm : m ≤ g + 1 := by omega
      have hmg : m ≤ g := by omega
      obtain ⟨ihR, ihW⟩ := ih hm
      set Sm := ∑ k ∈ Finset.range m, BB k * σ.Φ ^ k with hSm
      -- the (m+1)-slot partial sum is a development; if nonzero, hK1 pins its weight
      have hdev : ∀ (mm : ℕ), mm ≤ g + 1 →
          Moves.IsDevelopment σ.Φ (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k)
            (fun k => if k < mm then BB k else 0) mm := by
        intro mm _
        refine ⟨fun j => ?_, fun j hj => by simp [Nat.not_lt.mpr hj], ?_⟩
        · by_cases hjm : j < mm
          · simpa [hjm] using hdegBB j
          · simpa [hjm] using lt_of_le_of_lt bot_le (stage_degree_pos σ)
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp [Finset.mem_range.mp hk]
      have hWof : ∀ (mm : ℕ), mm ≤ g + 1 →
          (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) ≠ 0 →
          σ.w (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) = (g : ℤ) * (σ.h : ℤ) := by
        intro mm hmm hne
        obtain ⟨_, ⟨j, hjmm, hjnz, hjeq⟩⟩ :=
          σ.hK1 _ _ mm hne (hdev mm hmm)
        simp only [] at hjnz hjeq
        have hjnz' : BB j ≠ 0 := by
          intro h
          apply hjnz
          simp [hjmm, h]
        have hjeq' : σ.w (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) =
            σ.w (BB j) + (j : ℤ) * σ.w σ.Φ := by
          simpa [hjmm] using hjeq
        rw [hjeq']
        exact hslotW j (by omega) hjnz'
      -- zero partial sums have all-zero slots (Fact A uniqueness), so zero digit sums
      have hzero_digits : Sm = 0 → ∀ k, k < m → ν.ψ.coeff k = 0 := by
        intro hS0 k hk
        have huniq := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
          σ.hmonic m Sm (fun k => if k < m then BB k else 0) (hdev m hm) k
        rw [hS0] at huniq
        simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at huniq
        have hBk0 : BB k = 0 := by
          have := huniq
          simpa [hk] using this
        by_contra hψk
        rcases lt_or_eq_of_le (le_of_lt (lt_of_lt_of_le hk hmg)) with hklt | hkeq
        · obtain ⟨htt, _, _, _⟩ := hcl k hklt hψk
          apply htt
          have : BB k = tt k := by rw [hBB]; simp [hklt]
          rwa [this] at hBk0
        · have : BB k = 1 := by rw [hBB]; simp [hkeq]
          rw [this] at hBk0
          exact one_ne_zero hBk0
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← hSm]
      by_cases hBm : BB m = 0
      · -- silent slot: digit is zero too
        have hψm : ν.ψ.coeff m = 0 := by
          by_contra hψm
          rcases lt_or_eq_of_le hmg with hmlt | hmeq
          · obtain ⟨htt, _, _, _⟩ := hcl m hmlt hψm
            apply htt
            have : BB m = tt m := by rw [hBB]; simp [hmlt]
            rwa [this] at hBm
          · have : BB m = 1 := by rw [hBB]; simp [hmeq]
            rw [this] at hBm
            exact one_ne_zero hBm
        constructor
        · rw [hBm, zero_mul, add_zero, hψm, map_zero, zero_mul, add_zero]
          exact ihR
        · intro hne
          rw [hBm, zero_mul, add_zero] at hne ⊢
          exact ihW hne
      · have hFm : BB m * σ.Φ ^ m ≠ 0 := mul_ne_zero hBm (pow_ne_zero m hΦne)
        have hFmR : σ.R (BB m * σ.Φ ^ m) =
            LaurentPolynomial.C (ν.ψ.coeff m) * LaurentPolynomial.T (m : ℤ) :=
          hslotR m hmg hBm
        have hFmW : σ.w (BB m * σ.Φ ^ m) = (g : ℤ) * (σ.h : ℤ) := by
          rw [σ.hwmul (BB m) (σ.Φ ^ m) hBm (pow_ne_zero m hΦne),
            stage_w_pow σ σ.Φ hΦne m]
          exact hslotW m hmg hBm
        by_cases hS0 : Sm = 0
        · rw [hS0, zero_add]
          constructor
          · rw [hFmR]
            have : ∑ k ∈ Finset.range m, LaurentPolynomial.C (ν.ψ.coeff k) *
                LaurentPolynomial.T (k : ℤ) = 0 := by
              refine Finset.sum_eq_zero fun k hk => ?_
              rw [hzero_digits hS0 k (Finset.mem_range.mp hk), map_zero, zero_mul]
            rw [this, zero_add]
          · intro _; exact hFmW
        · -- genuine recomposition step: equal weights, hRadd fires
          have hsum_ne : Sm + BB m * σ.Φ ^ m ≠ 0 := by
            intro habs
            have hdevs := hdev (m + 1) hm1
            rw [Finset.sum_range_succ] at hdevs
            have := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
              σ.hmonic (m + 1) (Sm + BB m * σ.Φ ^ m)
              (fun k => if k < m + 1 then BB k else 0) hdevs m
            rw [habs] at this
            simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at this
            apply hBm
            simpa [Nat.lt_succ_self] using this
          have hWm1 : σ.w (Sm + BB m * σ.Φ ^ m) = (g : ℤ) * (σ.h : ℤ) := by
            have := hWof (m + 1) hm1 (by rwa [Finset.sum_range_succ])
            rwa [Finset.sum_range_succ] at this
          have hradd := σ.hRadd Sm (BB m * σ.Φ ^ m) hS0 hFm hsum_ne
            (by rw [ihW hS0, hFmW]) (by rw [hWm1, ihW hS0])
          constructor
          · rw [hradd, ihR, hFmR]
          · intro _; exact hWm1
  -- assemble: c = 1, k = 0
  refine ⟨1, 0, ?_⟩
  have hfin := (main (g + 1) le_rfl).1
  rw [← hkey] at hfin
  have hψsum : Polynomial.toLaurent ν.ψ =
      ∑ k ∈ Finset.range (g + 1), LaurentPolynomial.C (ν.ψ.coeff k) *
        LaurentPolynomial.T (k : ℤ) := by
    conv_lhs => rw [ν.ψ.as_sum_range' (g + 1) (by rw [ν.hψdeg]; omega)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => Polynomial.toLaurent_C_mul_T k _
  rw [hfin, ← hψsum]
  simp [LaurentPolynomial.T_zero]

/-! ## H1-U6 graded helpers: initial forms at pinned degrees -/

section GradedHelpers

variable (S : SideVal p)

/-- Initial form at a pinned weight: if `S.w f = m` exactly, `initialForm f` is the
degree-`m` class of `f` (the cast-free display used by the piece-level additivity). -/
theorem initialForm_eq_of {f : Polynomial ℤ_[p]} {m : ℤ}
    (hw : S.w f = (m : WithTop ℤ)) :
    S.initialForm f = DirectSum.of (fun γ => S.grPiece γ) m
      (Submodule.Quotient.mk ⟨f, le_of_eq hw.symm⟩) := by
  have hd : S.deg f = m := by
    unfold SideVal.deg
    rw [hw]
    rfl
  subst hd
  rfl

/-- The `Rg.ring` addition IS the DirectSum addition (componentwise tie, from
`add_def`; re-derivation of the private L1 lemma). -/
theorem ring_add_eq_DS (Rg : GradedRingStr S) (x y : S.Gr) :
    (letI := Rg.ring; x + y) = x + y := by
  refine DFinsupp.ext fun γ => ?_
  rw [Rg.add_def]
  rfl

/-- **Equal-weight pair additivity of the initial form** (the D.1(b) tie at EQUAL
weights, derived at the piece level — quotient classes add, `DirectSum.of` is
additive, `add_def` ties the ring addition): if `f`, `g`, and `f + g` all sit at
the same exact weight `m`, then `[f+g] = [f] + [g]` in `gr`. -/
theorem initialForm_add_of_w_eq (Rg : GradedRingStr S) {f g : Polynomial ℤ_[p]}
    {m : ℤ} (hf : S.w f = (m : WithTop ℤ)) (hg : S.w g = (m : WithTop ℤ))
    (hfg : S.w (f + g) = (m : WithTop ℤ)) :
    (letI := Rg.ring; S.initialForm (f + g) = S.initialForm f + S.initialForm g) := by
  rw [initialForm_eq_of S hf, initialForm_eq_of S hg, initialForm_eq_of S hfg,
    ring_add_eq_DS S Rg]
  have hsub : (⟨f + g, le_of_eq hfg.symm⟩ : S.ge m) =
      ⟨f, le_of_eq hf.symm⟩ + ⟨g, le_of_eq hg.symm⟩ := rfl
  rw [hsub, Submodule.Quotient.mk_add]
  exact map_add (DirectSum.of (fun γ => S.grPiece γ) m) _ _

/-- `[x^n] = [x]^n` for `x ≠ 0` (iterated D.1(c)). -/
theorem initialForm_pow (Rg : GradedRingStr S) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    ∀ n : ℕ, (letI := Rg.ring; S.initialForm (x ^ n) = (S.initialForm x) ^ n) := by
  letI := Rg.ring
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, Rg.one_def]
  | succ n ih =>
    rw [pow_succ, pow_succ, L1_initialForm_mul S Rg (x ^ n) x (pow_ne_zero n hx) hx, ih]

end GradedHelpers

/-! ## H1-U6 row: the RES-1 recorded-site march input -/

/-- **H1-U6 [M]-hypothesis row — the recorded-site development pin** (GD23 RES-1's
order-1 dictionary tie, stated as the slot-min consequence the graded halves
consume): every `f` anchored at the node's recorded site (`HasAnchorK` at
`(ν.a, ν.Ranch)`, the `GrBKeyLaws.faithful_at` guard) has a `σ'.Φ`-development
whose FIRST minimal slot sits at exactly `ν.μ` — slot `ν.μ` attains the `hK1`
slot-minimum and every lower slot is strictly heavier. Mathematically this is the
anchored-march/RES-1 content `ord_ψ(Ranch) = μ ⟹ j₀ = μ` (the node's `hOrd` +
`hRanch` fields consumed through the child-residual recomposition); its Lean
discharge is the HC1 S9w/`ChildResData` machinery, NOT assumed here — per the
[M]-discipline it is a NAMED row (the blueprint §5.3 `DevBound` precedent), never
an axiom, and `grb_key_laws_base` displays it as an explicit binder. -/
structure SiteDevPin (ν : Node p F) (σ' : Stage p F) : Prop where
  pin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
    HasAnchorK (ν.σ.R f) ν.a ν.Ranch →
    ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ),
      Moves.IsDevelopment σ'.Φ f B N ∧ B ν.μ ≠ 0 ∧
      σ'.w f = σ'.w (B ν.μ) + (ν.μ : ℤ) * σ'.w σ'.Φ ∧
      (∀ j, j < ν.μ → B j ≠ 0 → σ'.w f < σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ)

/-! ## H1-U6 leg 2: the guarded ord tie from the site pin -/

/-- **H1-U6 leg 2 — `faithful_at` from the site pin** (GD23 (GR-B)(4), order-1
instance): given the `SiteDevPin` row, the recorded-site guarded ord tie holds —
`ψhom^μ ∥ initialForm f` for every anchored `f`. Positive half: split the
development at slot `μ` as `f = Φ'^μ·q + r`; the pin + `hK1` force
`w(Φ'^μ q) = w f` with `r` strictly heavier, so `[f] = [Φ']^μ·[q]` by
`L1_initialForm_add_lt`/`_mul` and `kpa_init` supplies `ψhom^μ`. Negative half:
split `q = B_μ + Φ'·q₂`; gr is a domain (`L1_gr_domain_iff_val` + `hSw`/`hwmul`),
so `ψhom^{μ+1} ∣ [f]` cancels to `ψhom ∣ [q]`, and both weight cases push the
divisibility onto `[B_μ]` — refuted by `kpa_block` (`deg B_μ < deg Φ'`). -/
theorem faithful_at_of_sitePin (ν : Node p F) (σ' : Stage p F)
    (M : GenuineStageModel σ') (KB : KPBlock σ' M) (hsite : SiteDevPin ν σ') :
    letI := M.Rg.ring; ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      HasAnchorK (ν.σ.R f) ν.a ν.Ranch →
      (KB.ψhom ^ ν.μ ∣ M.S.initialForm f ∧
        ¬ KB.ψhom ^ (ν.μ + 1) ∣ M.S.initialForm f) := by
  letI := M.Rg.ring
  -- gr is a domain: w is multiplicative through hSw
  haveI hdom : IsDomain M.S.Gr := by
    rw [L1_gr_domain_iff_val M.S M.Rg]
    intro f g hf hg
    rw [M.hSw _ (mul_ne_zero hf hg), M.hSw f hf, M.hSw g hg,
      σ'.hwmul f g hf hg]
    push_cast
    rfl
  intro f hf hanch
  obtain ⟨B, N, ⟨hdeg, hvan, hsum⟩, hBμ, hμmin, hlow⟩ := hsite.pin f hf hanch
  set μ := ν.μ with hμdef
  set Φ' := σ'.Φ with hΦ'def
  have hΦ'ne : Φ' ≠ 0 := σ'.hmonic.ne_zero
  have hμN : μ < N := by
    by_contra hge
    exact hBμ (hvan μ (by omega))
  -- split the development at slot μ:  f = r + Φ'^μ · q,  q = B μ + Φ' · q₂
  set r : Polynomial ℤ_[p] := ∑ j ∈ Finset.range μ, B j * Φ' ^ j with hr
  set q : Polynomial ℤ_[p] := ∑ j ∈ Finset.range (N - μ), B (μ + j) * Φ' ^ j with hq
  set q₂ : Polynomial ℤ_[p] :=
    ∑ j ∈ Finset.range (N - μ - 1), B (μ + 1 + j) * Φ' ^ j with hq₂
  have hsplit : f = r + Φ' ^ μ * q := by
    rw [hsum, show N = μ + (N - μ) by omega, Finset.sum_range_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have hqsplit : q = B μ + Φ' * q₂ := by
    rw [hq, show N - μ = 1 + (N - μ - 1) by omega, Finset.sum_range_add]
    congr 1
    · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show μ + (1 + j) = μ + 1 + j by omega, pow_add, pow_one]
      ring
  -- q and q₂ are developments (shifted slots); r is a development on the low slots
  have hqdev : Moves.IsDevelopment Φ' q (fun j => B (μ + j)) (N - μ) :=
    ⟨fun j => hdeg (μ + j), fun j hj => hvan (μ + j) (by omega), rfl⟩
  have hq₂dev : Moves.IsDevelopment Φ' q₂ (fun j => B (μ + 1 + j)) (N - μ - 1) :=
    ⟨fun j => hdeg (μ + 1 + j), fun j hj => hvan (μ + 1 + j) (by omega), rfl⟩
  have hrdev : Moves.IsDevelopment Φ' r (fun j => if j < μ then B j else 0) μ := by
    refine ⟨fun j => ?_, fun j hj => by simp [Nat.not_lt.mpr hj], ?_⟩
    · by_cases hjμ : j < μ
      · simpa [hjμ] using hdeg j
      · -- `degree 0 = ⊥ < degree Φ'`
        simpa [hjμ] using lt_of_le_of_lt bot_le (stage_degree_pos σ')
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [Finset.mem_range.mp hj]
  have hqne : q ≠ 0 := by
    intro h0
    have := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
      σ'.hmonic (N - μ) q (fun j => B (μ + j)) hqdev 0
    rw [h0] at this
    simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at this
    exact hBμ (by simpa using this)
  -- weights: hK1 on f, q pin everything to the slot-μ level
  obtain ⟨hfmin, _⟩ := σ'.hK1 f B N hf ⟨hdeg, hvan, hsum⟩
  have hwq : σ'.w q = σ'.w (B μ) := by
    obtain ⟨hqlow, ⟨j, hjN, hjnz, hjeq⟩⟩ :=
      σ'.hK1 q (fun j => B (μ + j)) (N - μ) hqne hqdev
    have h1 : σ'.w q ≤ σ'.w (B μ) := by
      have := hqlow 0 (by omega) (by simpa using hBμ)
      simpa using this
    have h2 : σ'.w (B μ) ≤ σ'.w q := by
      have hfj := hfmin (μ + j) (by omega) hjnz
      rw [hμmin] at hfj
      rw [hjeq]
      push_cast at hfj ⊢
      linarith
    omega
  have hwΦμq : σ'.w (Φ' ^ μ * q) = σ'.w f := by
    rw [σ'.hwmul (Φ' ^ μ) q (pow_ne_zero μ hΦ'ne) hqne,
      stage_w_pow σ' Φ' hΦ'ne μ, hwq, hμmin]
    ring
  -- the initial form factors through slot μ
  have hinf : M.S.initialForm f =
      M.S.initialForm (Φ' ^ μ) * M.S.initialForm q := by
    have hbase : M.S.initialForm f = M.S.initialForm (Φ' ^ μ * q) := by
      by_cases hr0 : r = 0
      · rw [hsplit, hr0, zero_add]
      · -- r is strictly heavier than Φ'^μ·q
        have hwr : σ'.w f < σ'.w r := by
          obtain ⟨_, ⟨j, hjμ, hjnz, hjeq⟩⟩ :=
            σ'.hK1 r (fun j => if j < μ then B j else 0) μ hr0 hrdev
          have hjnz' : B j ≠ 0 := by
            intro h
            apply hjnz
            simp [hjμ, h]
          have := hlow j hjμ hjnz'
          rw [hjeq]
          simpa [hjμ] using this
        have hΦμqne : Φ' ^ μ * q ≠ 0 := mul_ne_zero (pow_ne_zero μ hΦ'ne) hqne
        have hdlt : M.S.deg (Φ' ^ μ * q) < M.S.deg r := by
          have d1 : (M.S.deg (Φ' ^ μ * q) : WithTop ℤ) = M.S.w (Φ' ^ μ * q) :=
            M.S.deg_eq hΦμqne
          have d2 : (M.S.deg r : WithTop ℤ) = M.S.w r := M.S.deg_eq hr0
          rw [M.hSw _ hΦμqne] at d1
          rw [M.hSw _ hr0] at d2
          have e1 : M.S.deg (Φ' ^ μ * q) = σ'.w (Φ' ^ μ * q) := by exact_mod_cast d1
          have e2 : M.S.deg r = σ'.w r := by exact_mod_cast d2
          rw [e1, e2, hwΦμq]
          exact hwr
        have := L1_initialForm_add_lt M.S M.Rg (Φ' ^ μ * q) r hΦμqne hr0
          (by rw [add_comm, ← hsplit]; exact hf) hdlt
        rw [hsplit, add_comm]
        exact this
    rw [hbase,
      L1_initialForm_mul M.S M.Rg (Φ' ^ μ) q (pow_ne_zero μ hΦ'ne) hqne]
  obtain ⟨u, hu⟩ := KB.kpa_init
  have hinΦμ : M.S.initialForm (Φ' ^ μ) = (u : M.S.Gr) ^ μ * KB.ψhom ^ μ := by
    rw [initialForm_pow M.S M.Rg Φ' hΦ'ne μ, hu, mul_pow]
  have hψne : KB.ψhom ≠ 0 := KB.kpirr.ne_zero
  -- the block at slot μ: ψhom never divides a coefficient's initial form
  have hblockμ : ¬ KB.ψhom ∣ M.S.initialForm (B μ) := by
    have hdegμ : (B μ).natDegree < σ'.Φ.natDegree :=
      Polynomial.natDegree_lt_natDegree hBμ (hdeg μ)
    exact KB.kpa_block (B μ) hBμ hdegμ
  constructor
  · -- positive half
    refine ⟨(u : M.S.Gr) ^ μ * M.S.initialForm q, ?_⟩
    rw [hinf, hinΦμ]
    ring
  · -- negative half
    intro hdvd
    have hcancel : KB.ψhom ∣ M.S.initialForm q := by
      -- direct cancellation: ψhom^{μ+1} ∣ ψhom^μ · (u^μ · [q])  ⟹  ψhom ∣ u^μ·[q]
      have h2 : KB.ψhom ^ μ * KB.ψhom ∣
          KB.ψhom ^ μ * ((u : M.S.Gr) ^ μ * M.S.initialForm q) := by
        rw [← pow_succ]
        rw [hinf, hinΦμ] at hdvd
        have hre : (u : M.S.Gr) ^ μ * KB.ψhom ^ μ * M.S.initialForm q =
            KB.ψhom ^ μ * ((u : M.S.Gr) ^ μ * M.S.initialForm q) := by ring
        rwa [hre] at hdvd
      have h3 : KB.ψhom ∣ (u : M.S.Gr) ^ μ * M.S.initialForm q :=
        (mul_dvd_mul_iff_left (pow_ne_zero μ hψne)).mp h2
      -- strip the unit u^μ
      obtain ⟨c, hc⟩ := h3
      refine ⟨((u⁻¹ : (M.S.Gr)ˣ) : M.S.Gr) ^ μ * c, ?_⟩
      have huu : ((u⁻¹ : (M.S.Gr)ˣ) : M.S.Gr) ^ μ * ((u : M.S.Gr) ^ μ) = 1 := by
        rw [← mul_pow]
        norm_cast
        simp
      calc M.S.initialForm q
          = ((u⁻¹ : (M.S.Gr)ˣ) : M.S.Gr) ^ μ * ((u : M.S.Gr) ^ μ *
              M.S.initialForm q) := by rw [← mul_assoc, huu, one_mul]
        _ = ((u⁻¹ : (M.S.Gr)ˣ) : M.S.Gr) ^ μ * (KB.ψhom * c) := by rw [hc]
        _ = KB.ψhom * (((u⁻¹ : (M.S.Gr)ˣ) : M.S.Gr) ^ μ * c) := by ring
    -- push the divisibility onto [B μ] and refute with the block
    by_cases hq₂0 : q₂ = 0
    · apply hblockμ
      have : q = B μ := by rw [hqsplit, hq₂0, mul_zero, add_zero]
      rwa [this] at hcancel
    · -- weight cases on Φ'·q₂ against B μ
      have hΦq₂ne : Φ' * q₂ ≠ 0 := mul_ne_zero hΦ'ne hq₂0
      have hwq₂ : σ'.w (B μ) ≤ σ'.w (Φ' * q₂) := by
        obtain ⟨_, ⟨j, hjN, hjnz, hjeq⟩⟩ :=
          σ'.hK1 q₂ (fun j => B (μ + 1 + j)) (N - μ - 1) hq₂0 hq₂dev
        have hfj := hfmin (μ + 1 + j) (by omega) hjnz
        rw [hμmin] at hfj
        rw [σ'.hwmul Φ' q₂ hΦ'ne hq₂0, hjeq]
        push_cast at hfj ⊢
        linarith
      rcases lt_or_eq_of_le hwq₂ with hlt | heq
      · -- Φ'·q₂ strictly heavier: [q] = [B μ]
        apply hblockμ
        have hdlt : M.S.deg (B μ) < M.S.deg (Φ' * q₂) := by
          have d1 : (M.S.deg (B μ) : WithTop ℤ) = M.S.w (B μ) := M.S.deg_eq hBμ
          have d2 : (M.S.deg (Φ' * q₂) : WithTop ℤ) = M.S.w (Φ' * q₂) :=
            M.S.deg_eq hΦq₂ne
          rw [M.hSw _ hBμ] at d1
          rw [M.hSw _ hΦq₂ne] at d2
          have e1 : M.S.deg (B μ) = σ'.w (B μ) := by exact_mod_cast d1
          have e2 : M.S.deg (Φ' * q₂) = σ'.w (Φ' * q₂) := by exact_mod_cast d2
          rw [e1, e2]
          exact hlt
        have hin : M.S.initialForm q = M.S.initialForm (B μ) := by
          have := L1_initialForm_add_lt M.S M.Rg (B μ) (Φ' * q₂) hBμ hΦq₂ne
            (by rw [← hqsplit]; exact hqne) hdlt
          rw [hqsplit]
          exact this
        rwa [hin] at hcancel
      · -- equal weights: [q] = [B μ] + [Φ']·[q₂], subtract the ψhom-multiple
        apply hblockμ
        have hwqBμ : σ'.w q = σ'.w (B μ) := hwq
        have hwq' : σ'.w q = σ'.w (Φ' * q₂) := by rw [hwqBμ]; exact heq
        have hSf : M.S.w (B μ) = ((σ'.w q : ℤ) : WithTop ℤ) := by
          rw [M.hSw _ hBμ, hwqBμ]
        have hSg : M.S.w (Φ' * q₂) = ((σ'.w q : ℤ) : WithTop ℤ) := by
          rw [M.hSw _ hΦq₂ne, ← hwq']
        have hSfg : M.S.w (B μ + Φ' * q₂) = ((σ'.w q : ℤ) : WithTop ℤ) := by
          rw [← hqsplit, M.hSw _ hqne]
        have hin : M.S.initialForm q =
            M.S.initialForm (B μ) + M.S.initialForm (Φ' * q₂) := by
          conv_lhs => rw [hqsplit]
          exact initialForm_add_of_w_eq M.S M.Rg hSf hSg hSfg
        have hdvd2 : KB.ψhom ∣ M.S.initialForm (Φ' * q₂) := by
          rw [L1_initialForm_mul M.S M.Rg Φ' q₂ hΦ'ne hq₂0, hu]
          exact ⟨(u : M.S.Gr) * M.S.initialForm q₂, by ring⟩
        have : M.S.initialForm (B μ) =
            M.S.initialForm q - M.S.initialForm (Φ' * q₂) := by
          rw [hin]; ring
        rw [this]
        exact dvd_sub hcancel hdvd2

/-! ## H1-U6: the order-1 `GrBKeyLaws` instance -/

/-- **H1-U6 — `grb_key_laws_base`** (blueprint §5.2, statement shape per the §5.1 U3
row; binder block PROBE-FIRST, probed against the `bStage`/`bStageP` base carriers
and the U31 inert gate read — see the file-header provenance flag): at the order-1
base configuration (frame pins `s = 1`/`t = 0`, level read `e = 1`/`h = σ.h` — the
d₀ = 1 KEY1 configuration of the U5 bullet), the (GR-B-KEY) laws hold for any
key-compliance block `KB` over the state model, given the recorded ν ↔ σ' link data
and the `SiteDevPin` row. `key_res` and `faithful_at` are PROVED (GD23 KEY-g(iii) +
RES-1/(GR-B)(4) order-1 instances — `nodeLift_key_res`, `faithful_at_of_sitePin`);
the links are data ties supplied by the history; `SiteDevPin` is the named RES-1
march row (its discharge = the S9w child-residual machinery). Never cite this
theorem as evidence for (H1) beyond order 1. -/
theorem grb_key_laws_base (ν : Node p F) (σ' : Stage p F)
    (M : GenuineStageModel σ') (KB : KPBlock σ' M)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) (hνe : ν.e = 1) (hlevel : ν.h = ν.σ.h)
    (he : σ'.e = ν.e) (hh : σ'.h = ν.h) (hprev : σ'.wPrev = ν.σ.w)
    (hΦ : IsNodeLift ν σ'.Φ) (hsite : SiteDevPin ν σ') :
    GrBKeyLaws ν σ' M KB where
  link_e := he
  link_h := hh
  link_prev := hprev
  link_key := hΦ
  key_res := nodeLift_key_res ν σ'.Φ hσs hσt hνe hlevel hΦ
  faithful_at := faithful_at_of_sitePin ν σ' M KB hsite

/-! ## H1-U7 (unchanged) -/

/-- H1-U7 — `Key1SiteBlock` at the base, pure packaging of U5+U6 (blueprint §5.2):
from a key-compliance block `KB` (U5's construction, `kpBlock_base`) and the
(GR-B-KEY) laws for it (U6's instance, `grb_key_laws_base`), the (H1)(d) site
block holds. This is the introduction rule of `Key1SiteBlock`'s existential;
non-vacuity at the base enters ONLY through the U5/U6 binders — never cite this
lemma alone as evidence for (H1). -/
theorem key1SiteBlock_base (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (KB : KPBlock σ' M) (laws : GrBKeyLaws ν σ' M KB) : Key1SiteBlock ν σ' M :=
  ⟨KB, laws⟩


/-! # H1-U5 (`kpBlock_base`) — the base-stage KPBlock construction (prover H1-U5,
2026-08-01). Sections A–F below are the U5 build; all helpers are `private` and
`u5_`-prefixed (unit-local), so the public surface added by this unit is
`kpBlock_base` alone. See this file's header for the math route and the probe-first
base binder record. -/

open LeanUrat.MovesGr.SideVal

/-! ## A. Pure Laurent bottom-coefficient toolkit (the `K[z̄]`-primeness face) -/

section Laurent

variable {K : Type*} [Field K]

/-- Bottom coefficient of a product of nonnegatively supported Laurent polynomials:
only the `(0,0)` convolution cell survives. -/
private lemma u5_bot_coeff_mul (x y : LaurentPolynomial K)
    (hx : ∀ n ∈ x.support, (0 : ℤ) ≤ n) (hy : ∀ n ∈ y.support, (0 : ℤ) ≤ n) :
    (x * y) 0 = x 0 * y 0 := by
  classical
  rw [AddMonoidAlgebra.mul_apply]
  rw [Finsupp.sum, Finset.sum_eq_single (0 : ℤ)]
  · rw [Finsupp.sum, Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro b hb hbne
      rw [if_neg (by omega)]
    · intro h0
      rw [Finsupp.notMem_support_iff.mp h0]
      simp
  · intro a ha hane
    have ha0 : (0 : ℤ) ≤ a := hx a ha
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb0 : (0 : ℤ) ≤ b := hy b hb
    rw [if_neg (by omega)]
  · intro h0
    rw [Finsupp.notMem_support_iff.mp h0, Finsupp.sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    simp

/-- `(T 1 * z) 0 = 0` for nonnegatively supported `z`. -/
private lemma u5_T_one_mul_coeff_zero (z : LaurentPolynomial K)
    (hz : ∀ n ∈ z.support, (0 : ℤ) ≤ n) :
    (LaurentPolynomial.T (1 : ℤ) * z : LaurentPolynomial K) 0 = 0 := by
  classical
  have hTs : ∀ n ∈ (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial K).support, (0 : ℤ) ≤ n := by
    intro n hn
    rw [Finsupp.mem_support_iff, LaurentPolynomial.T_apply] at hn
    by_cases h : (1 : ℤ) = n
    · omega
    · rw [if_neg h] at hn; exact absurd rfl hn
  rw [u5_bot_coeff_mul (LaurentPolynomial.T (1 : ℤ)) z hTs hz]
  simp [LaurentPolynomial.T_apply]

end Laurent

/-! ## B. The graded component toolkit (re-derivation of `L1_gr_domain_iff_val_v3`'s
private layer — those lemmas are `private` there; HK13R precedent for re-deriving). -/

section Toolkit

variable (S : SideVal p) (Rg : GradedRingStr S)

/-- ring `+` = DirectSum `+` (elementwise, from the componentwise `add_def`). -/
private lemma u5_ring_add_eq (x y : S.Gr) :
    (letI := Rg.ring; x + y) = x + y := by
  refine DFinsupp.ext fun γ => ?_
  rw [Rg.add_def]
  rfl

/-- degree-γ `of`-classes add through the ring's `+`. -/
private lemma u5_of_add_of (γ : ℤ) (a b : S.grPiece γ) :
    (letI := Rg.ring;
      DirectSum.of (fun δ => S.grPiece δ) γ a + DirectSum.of (fun δ => S.grPiece δ) γ b)
      = DirectSum.of (fun δ => S.grPiece δ) γ (a + b) :=
  (u5_ring_add_eq S Rg _ _).trans ((DirectSum.of (fun δ => S.grPiece δ) γ).map_add a b).symm

/-- `of γ 0` is the RING zero. -/
private lemma u5_of_zero_ring (γ : ℤ) :
    DirectSum.of (fun δ => S.grPiece δ) γ (0 : S.grPiece γ)
      = (letI := Rg.ring; (0 : S.Gr)) := by
  letI := Rg.ring
  have h1 := u5_of_add_of S Rg γ 0 0
  rw [add_zero] at h1
  exact add_right_cancel (h1.trans (zero_add _).symm)

/-- the ring zero IS the DirectSum zero. -/
private lemma u5_ring_zero_eq :
    (letI := Rg.ring; (0 : S.Gr)) = 0 :=
  (u5_of_zero_ring S Rg 0).symm.trans ((DirectSum.of (fun δ => S.grPiece δ) 0).map_zero)

/-- γ-bounded generators: homogeneous classes in degrees `≤ γ`. -/
private def u5_genSet (γ : ℤ) : Set S.Gr :=
  {z | ∃ i : ℤ, i ≤ γ ∧ ∃ c : S.grPiece i, z = DirectSum.of (fun δ => S.grPiece δ) i c}

/-- every γ-bounded element lies in the additive closure of the γ-bounded generators. -/
private lemma u5_mem_closure_of_bdd (γ : ℤ) (x : S.Gr)
    (hx : ∀ i, γ < i → x i = 0) : x ∈ AddSubmonoid.closure (u5_genSet S γ) := by
  classical
  rw [← DirectSum.sum_support_of x]
  refine sum_mem fun i hi => AddSubmonoid.subset_closure ?_
  exact ⟨i, not_lt.mp fun h => (DFinsupp.mem_support_iff.mp hi) (hx i h), x i, rfl⟩

/-- all homogeneous generators. -/
private def u5_genAll : Set S.Gr :=
  {z | ∃ (i : ℤ) (c : S.grPiece i), z = DirectSum.of (fun δ => S.grPiece δ) i c}

/-- every element lies in the additive closure of the homogeneous classes. -/
private lemma u5_mem_closure_all (x : S.Gr) : x ∈ AddSubmonoid.closure (u5_genAll S) := by
  classical
  rw [← DirectSum.sum_support_of x]
  exact sum_mem fun i _ => AddSubmonoid.subset_closure ⟨i, x i, rfl⟩

/-- left distributivity of the ring product over a DirectSum-flavored sum. -/
private lemma u5_mulr_addDS_left {w x y : S.Gr}
    (h : w = x + y) (z : S.Gr) :
    (letI := Rg.ring; w * z) = (letI := Rg.ring; x * z + y * z) := by
  letI := Rg.ring
  rw [h.trans (u5_ring_add_eq S Rg x y).symm, add_mul]

/-- right distributivity of the ring product over a DirectSum-flavored sum. -/
private lemma u5_mulr_addDS_right {w x y : S.Gr}
    (h : w = x + y) (z : S.Gr) :
    (letI := Rg.ring; z * w) = (letI := Rg.ring; z * x + z * y) := by
  letI := Rg.ring
  rw [h.trans (u5_ring_add_eq S Rg x y).symm, mul_add]

/-- single-left component formula (bounded right factor). -/
private lemma u5_mul_of_component (γ δ i : ℤ) (hi : i ≤ γ) (c : S.grPiece i) (y : S.Gr)
    (hy : y ∈ AddSubmonoid.closure (u5_genSet S δ)) :
    (letI := Rg.ring; DirectSum.of (fun ε => S.grPiece ε) i c * y) (γ + δ)
      = S.pmul γ δ ((DirectSum.of (fun ε => S.grPiece ε) i c) γ) (y δ) := by
  letI := Rg.ring
  induction hy using AddSubmonoid.closure_induction with
  | mem z hz =>
      obtain ⟨j, hj, d, rfl⟩ := hz
      rw [Rg.mul_of i j c d]
      by_cases hii : i = γ
      · subst hii
        by_cases hjj : j = δ
        · subst hjj
          rw [DirectSum.of_eq_same, DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : i + δ ≠ i + j),
            DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjj), map_zero]
      · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : γ + δ ≠ i + j),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hii), map_zero, LinearMap.zero_apply]
  | zero =>
      rw [DirectSum.zero_apply, map_zero, ← u5_ring_zero_eq S Rg, mul_zero,
        u5_ring_zero_eq S Rg, DirectSum.zero_apply]
  | add x1 x2 hx1c hx2c ih1 ih2 =>
      rw [u5_mulr_addDS_right S Rg rfl _, Rg.add_def, ih1, ih2, DirectSum.add_apply,
        map_add]

/-- top-component formula: for γ-bounded `x` and δ-bounded `y`,
`(x * y) (γ+δ) = pmul γ δ (x γ) (y δ)`. -/
private lemma u5_mul_component_top (γ δ : ℤ) (x y : S.Gr)
    (hxb : ∀ i, γ < i → x i = 0) (hyb : ∀ j, δ < j → y j = 0) :
    (letI := Rg.ring; x * y) (γ + δ) = S.pmul γ δ (x γ) (y δ) := by
  letI := Rg.ring
  have hyc := u5_mem_closure_of_bdd S δ y hyb
  have hxc := u5_mem_closure_of_bdd S γ x hxb
  clear hxb hyb
  induction hxc using AddSubmonoid.closure_induction with
  | mem z hz =>
      obtain ⟨i, hi, c, rfl⟩ := hz
      exact u5_mul_of_component S Rg γ δ i hi c y hyc
  | zero =>
      rw [DirectSum.zero_apply, map_zero, LinearMap.zero_apply, ← u5_ring_zero_eq S Rg,
        zero_mul, u5_ring_zero_eq S Rg, DirectSum.zero_apply]
  | add x1 x2 hx1c hx2c ih1 ih2 =>
      rw [u5_mulr_addDS_left S Rg rfl y, Rg.add_def, ih1, ih2, DirectSum.add_apply,
        map_add (S.pmul γ δ), LinearMap.add_apply]

/-- shifted component formula against a SINGLE homogeneous left factor — no bounds
needed (the left factor occupies one degree, so exactly one convolution cell can
land at `i + γ`). -/
private lemma u5_of_mul_apply_shift (i γ : ℤ) (c₀ : S.grPiece i) (x : S.Gr) :
    (letI := Rg.ring; DirectSum.of (fun δ => S.grPiece δ) i c₀ * x) (i + γ)
      = S.pmul i γ c₀ (x γ) := by
  letI := Rg.ring
  have hxc := u5_mem_closure_all S x
  induction hxc using AddSubmonoid.closure_induction with
  | mem z hz =>
      obtain ⟨j, d, rfl⟩ := hz
      rw [Rg.mul_of i j c₀ d]
      by_cases hjγ : j = γ
      · subst hjγ
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : i + γ ≠ i + j),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjγ), map_zero]
  | zero =>
      rw [DirectSum.zero_apply, map_zero, ← u5_ring_zero_eq S Rg, mul_zero,
        u5_ring_zero_eq S Rg, DirectSum.zero_apply]
  | add x1 x2 hx1c hx2c ih1 ih2 =>
      rw [u5_mulr_addDS_right S Rg rfl _, Rg.add_def, ih1, ih2, DirectSum.add_apply,
        map_add]

/-- if `d` ring-divides every `of`-component of `x`, it divides `x` (the
"homogeneous ideal, backward" face). -/
private lemma u5_dvd_of_dvd_components (d x : S.Gr)
    (h : ∀ γ : ℤ, (letI := Rg.ring; d ∣ DirectSum.of (fun δ => S.grPiece δ) γ (x γ))) :
    letI := Rg.ring; d ∣ x := by
  classical
  let D : AddSubmonoid S.Gr :=
    { carrier := {z | letI := Rg.ring; d ∣ z}
      zero_mem' := by
        have h0 := (letI := Rg.ring; dvd_zero d)
        rwa [u5_ring_zero_eq S Rg] at h0
      add_mem' := by
        intro a b ha hb
        have hab := (letI := Rg.ring; dvd_add ha hb)
        rwa [u5_ring_add_eq S Rg a b] at hab }
  have hx : x ∈ D := by
    rw [← DirectSum.sum_support_of x]
    exact sum_mem fun γ _ => h γ
  exact hx

/-- an element of exact weight `γ` has its initial form in the degree-`γ` slot. -/
private lemma u5_initialForm_pin (u : Polynomial ℤ_[p]) (γ : ℤ)
    (hw : S.w u = (γ : WithTop ℤ)) :
    S.initialForm u
      = DirectSum.of (fun δ => S.grPiece δ) γ
          (Submodule.Quotient.mk ⟨u, le_of_eq hw.symm⟩) := by
  have hdeg : S.deg u = γ := by
    unfold SideVal.deg
    rw [hw]
    rfl
  subst hdeg
  rfl

/-- piece surjectivity: every nonzero homogeneous class IS an initial form. -/
private lemma u5_piece_repr {γ : ℤ} {c : S.grPiece γ} (hc : c ≠ 0) :
    ∃ u : Polynomial ℤ_[p], u ≠ 0 ∧ S.w u = (γ : WithTop ℤ) ∧
      DirectSum.of (fun δ => S.grPiece δ) γ c = S.initialForm u := by
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (S.gtIn γ) c
  have hle : S.w (u : Polynomial ℤ_[p]) ≤ (γ : WithTop ℤ) := by
    by_contra hlt
    exact hc (by rw [← hu, Submodule.Quotient.mk_eq_zero]; exact not_le.mp hlt)
  have hw : S.w (u : Polynomial ℤ_[p]) = (γ : WithTop ℤ) := le_antisymm hle u.2
  have hu0 : (u : Polynomial ℤ_[p]) ≠ 0 := by
    intro h0
    rw [h0, S.w_zero] at hw
    exact WithTop.top_ne_coe hw
  refine ⟨u, hu0, hw, ?_⟩
  rw [u5_initialForm_pin S u γ hw, ← hu]

end Toolkit

/-! ## C. Model-level layer: domain, Θ∘ι-injectivity, the `(R, w)` keying -/

section Model

variable (σ : Stage p F) (M : GenuineStageModel σ)

/-- `gr_w(A)` is a domain at any genuine stage model. -/
private lemma u5_gr_domain : letI := M.Rg.ring; IsDomain M.S.Gr := by
  refine (L1_gr_domain_iff_val M.S M.Rg).mpr ?_
  intro f g hf hg
  rw [M.hSw _ (mul_ne_zero hf hg), M.hSw f hf, M.hSw g hg, σ.hwmul f g hf hg,
    WithTop.coe_add]

/-- every element of the homogeneous monoid is nonzero. -/
private lemma u5_homMon_ne_zero :
    letI := M.Rg.ring; ∀ x ∈ M.homMon, x ≠ (0 : M.S.Gr) := by
  letI := M.Rg.ring
  haveI : IsDomain M.S.Gr := u5_gr_domain σ M
  intro x hx
  rw [M.homMon_gen] at hx
  induction hx using Submonoid.closure_induction with
  | mem g hg =>
      rcases hg with ⟨ũ, hũ, rfl⟩ | hg
      · intro hz
        rw [u5_ring_zero_eq M.S M.Rg] at hz
        exact L0_initialForm_ne_zero M.S (σ.hreps ũ hũ).1 hz
      · rcases hg with rfl
        intro hz
        rw [u5_ring_zero_eq M.S M.Rg] at hz
        exact L0_initialForm_ne_zero M.S σ.hmonic.ne_zero hz
  | one => exact one_ne_zero
  | mul a b _ _ ha hb => exact mul_ne_zero ha hb

/-- Θ∘ι is injective (localization at a monoid of nonzerodivisors of a domain). -/
private lemma u5_theta_iota_injective :
    letI := M.Rg.ring; letI := M.Loring; letI := M.alg;
    Function.Injective (fun x : M.S.Gr => M.Θ (algebraMap M.S.Gr M.Lo x)) := by
  letI := M.Rg.ring
  letI := M.Loring
  letI := M.alg
  haveI : IsDomain M.S.Gr := u5_gr_domain σ M
  haveI := M.isLoc
  have hM : M.homMon ≤ nonZeroDivisors M.S.Gr := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (u5_homMon_ne_zero σ M x hx)
  exact M.Θ.injective.comp (IsLocalization.injective M.Lo hM)

/-- initial forms are keyed by the residual pair `(σ.R f, σ.w f)`. -/
private lemma u5_initialForm_eq_iff (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) :
    (M.S.initialForm f = M.S.initialForm g) ↔ (σ.R f = σ.R g ∧ σ.w f = σ.w g) := by
  letI := M.Rg.ring
  letI := M.Loring
  letI := M.alg
  constructor
  · intro h
    have h1 : σ.grRes f = σ.grRes g := by
      rw [L4_grRes_eq_genuine σ M f hf, L4_grRes_eq_genuine σ M g hg, h]
    simp only [Stage.grRes] at h1
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h1
    have h2 : (Finsupp.single (σ.w f) (σ.R f) : ℤ →₀ LaurentPolynomial ↥σ.K)
        = Finsupp.single (σ.w g) (σ.R g) := h1
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h2 with ⟨hw, hR⟩ | ⟨hRf, _⟩
    · exact ⟨hR, hw⟩
    · exact absurd hRf (σ.hRne f hf)
  · rintro ⟨hR, hw⟩
    apply u5_theta_iota_injective σ M
    show M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm f))
        = M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm g))
    rw [← L4_grRes_eq_genuine σ M f hf, ← L4_grRes_eq_genuine σ M g hg]
    simp only [Stage.grRes]
    rw [hR, hw]

end Model

/-! ## D. The divisibility characterization (KEY-g's homogeneous-extraction face) -/

section Div

variable (σ : Stage p F) (M : GenuineStageModel σ)

/-- key multiples have key-divisible `of`-components (the "homogeneous ideal,
forward" face at the key). -/
private lemma u5_key_dvd_components (x : M.S.Gr)
    (hdvd : letI := M.Rg.ring; M.S.initialForm σ.Φ ∣ x) :
    ∀ κ : ℤ, letI := M.Rg.ring;
      M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) κ (x κ) := by
  letI := M.Rg.ring
  intro κ
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨γ, rfl⟩ : ∃ γ : ℤ, κ = (σ.h : ℤ) + γ := ⟨κ - (σ.h : ℤ), by ring⟩
  have hΦw : M.S.w σ.Φ = ((σ.h : ℤ) : WithTop ℤ) := by
    rw [M.hSw σ.Φ σ.hmonic.ne_zero, σ.hwΦ]
  have hΦof := u5_initialForm_pin M.S σ.Φ (σ.h : ℤ) hΦw
  have hcomp : x ((σ.h : ℤ) + γ)
      = M.S.pmul (σ.h : ℤ) γ (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩) (c γ) := by
    rw [hc, hΦof]
    exact u5_of_mul_apply_shift M.S M.Rg (σ.h : ℤ) γ _ c
  rw [hcomp, ← M.Rg.mul_of, ← hΦof]
  exact dvd_mul_right _ _

/-- **(DIV)** `in(Φ) ∣ in(f)` in `gr` iff the residual pair of `f` factors through
the key pair `(T s, h)` realizably. -/
private lemma u5_initialForm_dvd_iff (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    (letI := M.Rg.ring; M.S.initialForm σ.Φ ∣ M.S.initialForm f)
      ↔ ∃ g : Polynomial ℤ_[p], g ≠ 0 ∧
          σ.R f = LaurentPolynomial.T σ.s * σ.R g ∧ σ.w f = (σ.h : ℤ) + σ.w g := by
  letI := M.Rg.ring
  haveI : IsDomain M.S.Gr := u5_gr_domain σ M
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦw : M.S.w σ.Φ = ((σ.h : ℤ) : WithTop ℤ) := by
    rw [M.hSw σ.Φ hΦ0, σ.hwΦ]
  have hΦof := u5_initialForm_pin M.S σ.Φ (σ.h : ℤ) hΦw
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ (0 : M.S.Gr) := by
      rintro rfl
      rw [mul_zero, u5_ring_zero_eq M.S M.Rg] at hc
      exact L0_initialForm_ne_zero M.S hf hc
    classical
    set δ₀ : ℤ := M.S.deg f - (σ.h : ℤ) with hδ₀
    -- components of c away from δ₀ vanish
    have hslot : ∀ γ : ℤ, γ ≠ δ₀ → c γ = 0 := by
      intro γ hγ
      by_contra hne
      have hcomp : (M.S.initialForm f) ((σ.h : ℤ) + γ)
          = M.S.pmul (σ.h : ℤ) γ (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩) (c γ) := by
        rw [hc, hΦof]
        exact u5_of_mul_apply_shift M.S M.Rg (σ.h : ℤ) γ _ c
      have hzero : (M.S.initialForm f) ((σ.h : ℤ) + γ) = 0 := by
        show (DirectSum.of (fun δ => M.S.grPiece δ) (M.S.deg f) (M.S.mkPiece f))
          ((σ.h : ℤ) + γ) = 0
        exact DirectSum.of_eq_of_ne _ _ _ (by omega)
      have hpz : M.S.pmul (σ.h : ℤ) γ
          (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩) (c γ) = 0 := by
        rw [← hcomp, hzero]
      have hofz : DirectSum.of (fun δ => M.S.grPiece δ) ((σ.h : ℤ))
            (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩)
          * DirectSum.of (fun δ => M.S.grPiece δ) γ (c γ) = (0 : M.S.Gr) := by
        rw [M.Rg.mul_of, hpz, u5_of_zero_ring M.S M.Rg]
      rcases mul_eq_zero.mp hofz with h1 | h1
      · exact L0_initialForm_ne_zero M.S hΦ0
          ((hΦof.trans h1).trans (u5_ring_zero_eq M.S M.Rg))
      · apply hne
        rw [u5_ring_zero_eq M.S M.Rg] at h1
        have h2 := congrArg (fun z : M.S.Gr => z γ) h1
        simpa using h2
    have hcδ : c δ₀ ≠ 0 := by
      intro h0
      apply hc0
      rw [u5_ring_zero_eq M.S M.Rg]
      refine DFinsupp.ext fun γ => ?_
      rw [DirectSum.zero_apply]
      by_cases hγ : γ = δ₀
      · rw [hγ]; exact h0
      · exact hslot γ hγ
    obtain ⟨u, hu0, huw, huof⟩ := u5_piece_repr M.S hcδ
    have hcof : c = DirectSum.of (fun δ => M.S.grPiece δ) δ₀ (c δ₀) := by
      refine DFinsupp.ext fun γ => ?_
      by_cases hγ : γ = δ₀
      · subst hγ
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ hγ, hslot γ hγ]
    have hfin : M.S.initialForm f = M.S.initialForm (σ.Φ * u) := by
      rw [M.Rg.if_mul σ.Φ u hΦ0 hu0, hc, hcof, huof]
    have hkey := (u5_initialForm_eq_iff σ M f (σ.Φ * u) hf (mul_ne_zero hΦ0 hu0)).mp hfin
    refine ⟨u, hu0, ?_, ?_⟩
    · rw [hkey.1, σ.hRmul σ.Φ u hΦ0 hu0, σ.hRΦ]
    · rw [hkey.2, σ.hwmul σ.Φ u hΦ0 hu0, σ.hwΦ]
  · rintro ⟨g, hg0, hR, hw⟩
    have hfin : M.S.initialForm f = M.S.initialForm (σ.Φ * g) := by
      apply (u5_initialForm_eq_iff σ M f (σ.Φ * g) hf (mul_ne_zero hΦ0 hg0)).mpr
      constructor
      · rw [σ.hRmul σ.Φ g hΦ0 hg0, σ.hRΦ, hR]
      · rw [σ.hwmul σ.Φ g hΦ0 hg0, σ.hwΦ, hw]
    rw [hfin, M.Rg.if_mul σ.Φ g hΦ0 hg0]
    exact dvd_mul_right _ _

end Div

/-! ## E. Nonunit, the homogeneous prime core, and primeness -/

section Prime

variable (σ : Stage p F) (M : GenuineStageModel σ)

/-- weights are nonnegative at the base (from the support window + `hRne`). -/
private lemma u5_w_nonneg
    (hwin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∀ n ∈ (σ.R f).support, (0 : ℤ) ≤ n ∧ n * (σ.h : ℤ) ≤ σ.w f) :
    ∀ f : Polynomial ℤ_[p], f ≠ 0 → 0 ≤ σ.w f := by
  intro f hf
  have hne : σ.R f ≠ 0 := σ.hRne f hf
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨h0, hh⟩ := hwin f hf n hn
  have hh1 : (0 : ℤ) ≤ (σ.h : ℤ) := by positivity
  have := mul_nonneg h0 hh1
  omega

/-- negative-degree pieces are trivial at the base. -/
private lemma u5_neg_piece_zero
    (hwpos : ∀ f : Polynomial ℤ_[p], f ≠ 0 → 0 ≤ σ.w f)
    {γ : ℤ} (hγ : γ < 0) (c : M.S.grPiece γ) : c = 0 := by
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (M.S.gtIn γ) c
  rw [← hu, Submodule.Quotient.mk_eq_zero]
  show (γ : WithTop ℤ) < M.S.w (u : Polynomial ℤ_[p])
  by_cases hu0 : (u : Polynomial ℤ_[p]) = 0
  · rw [hu0, M.S.w_zero]
    exact WithTop.coe_lt_top γ
  · rw [M.hSw _ hu0]
    exact WithTop.coe_lt_coe.mpr (lt_of_lt_of_le hγ (hwpos _ hu0))

/-- `in(Φ)` is not a unit of `gr` (its inverse would live in a negative degree). -/
private lemma u5_key_not_unit
    (hwpos : ∀ f : Polynomial ℤ_[p], f ≠ 0 → 0 ≤ σ.w f) :
    letI := M.Rg.ring; ¬ IsUnit (M.S.initialForm σ.Φ) := by
  letI := M.Rg.ring
  haveI : IsDomain M.S.Gr := u5_gr_domain σ M
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  have hv : M.S.initialForm σ.Φ * ((u⁻¹ : M.S.Grˣ) : M.S.Gr) = 1 := by
    rw [← hu]
    exact u.mul_inv
  set v : M.S.Gr := ((u⁻¹ : M.S.Grˣ) : M.S.Gr) with hvdef
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦw : M.S.w σ.Φ = ((σ.h : ℤ) : WithTop ℤ) := by
    rw [M.hSw σ.Φ hΦ0, σ.hwΦ]
  have hΦof := u5_initialForm_pin M.S σ.Φ (σ.h : ℤ) hΦw
  have hv0 : v ≠ (0 : M.S.Gr) := by
    rintro h0
    rw [h0, mul_zero] at hv
    exact zero_ne_one hv
  classical
  have hsupp : (DFinsupp.support v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    apply hv0
    exact (DFinsupp.support_eq_empty.mp hemp).trans (u5_ring_zero_eq M.S M.Rg).symm
  set γt := (DFinsupp.support v).max' hsupp with hγt
  have hvt : v γt ≠ 0 :=
    DFinsupp.mem_support_iff.mp ((DFinsupp.support v).max'_mem hsupp)
  have hcomp : (1 : M.S.Gr) ((σ.h : ℤ) + γt)
      = M.S.pmul (σ.h : ℤ) γt (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩) (v γt) := by
    rw [← hv, hΦof]
    exact u5_of_mul_apply_shift M.S M.Rg (σ.h : ℤ) γt _ v
  have hpne : M.S.pmul (σ.h : ℤ) γt
      (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩) (v γt) ≠ 0 := by
    intro hz
    have hofz : DirectSum.of (fun δ => M.S.grPiece δ) ((σ.h : ℤ))
          (Submodule.Quotient.mk ⟨σ.Φ, le_of_eq hΦw.symm⟩)
        * DirectSum.of (fun δ => M.S.grPiece δ) γt (v γt) = (0 : M.S.Gr) := by
      rw [M.Rg.mul_of, hz, u5_of_zero_ring M.S M.Rg]
    rcases mul_eq_zero.mp hofz with h1 | h1
    · exact L0_initialForm_ne_zero M.S hΦ0
        ((hΦof.trans h1).trans (u5_ring_zero_eq M.S M.Rg))
    · apply hvt
      rw [u5_ring_zero_eq M.S M.Rg] at h1
      have h2 := congrArg (fun z : M.S.Gr => z γt) h1
      simpa using h2
  have h1w : M.S.w 1 = ((0 : ℤ) : WithTop ℤ) := by
    rw [M.S.w_one]
    rfl
  have h1of := u5_initialForm_pin M.S 1 0 h1w
  have hidx : (σ.h : ℤ) + γt = 0 := by
    by_contra hne
    apply hpne
    rw [← hcomp, M.Rg.one_def, h1of]
    exact DirectSum.of_eq_of_ne _ _ _ hne
  have hh1 : 1 ≤ σ.h := σ.hh
  have hγneg : γt < 0 := by omega
  exact hvt (u5_neg_piece_zero σ M hwpos hγneg (v γt))

/-- `σ.s = 1` at the `t = 0` base (Bézout). -/
private lemma u5_s_eq_one (ht0 : σ.t = 0) : σ.s = 1 := by
  have hbez := σ.hbez
  rw [ht0, mul_zero, add_zero] at hbez
  have he : 1 ≤ (σ.e : ℤ) := by exact_mod_cast σ.he
  nlinarith [hbez, he, sq_nonneg (σ.s - 1), sq_nonneg ((σ.e : ℤ) - 1)]

/-- the homogeneous prime core (KEY-g(ii) at the base): `in(Φ)` detects factors on
products of initial forms. -/
private lemma u5_hom_core
    (ht0 : σ.t = 0)
    (hwin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∀ n ∈ (σ.R f).support, (0 : ℤ) ≤ n ∧ n * (σ.h : ℤ) ≤ σ.w f)
    (hquo : ∀ f : Polynomial ℤ_[p], f ≠ 0 → (∀ n ∈ (σ.R f).support, (1 : ℤ) ≤ n) →
      ∃ g : Polynomial ℤ_[p], g ≠ 0 ∧
        σ.R g = LaurentPolynomial.T (-1) * σ.R f ∧ σ.w g = σ.w f - σ.h)
    (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdvd : letI := M.Rg.ring;
      M.S.initialForm σ.Φ ∣ M.S.initialForm f * M.S.initialForm g) :
    (letI := M.Rg.ring; M.S.initialForm σ.Φ ∣ M.S.initialForm f)
      ∨ (letI := M.Rg.ring; M.S.initialForm σ.Φ ∣ M.S.initialForm g) := by
  letI := M.Rg.ring
  have hs1 := u5_s_eq_one σ ht0
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  rw [← M.Rg.if_mul f g hf hg] at hdvd
  obtain ⟨k, hk0, hRk, _⟩ := (u5_initialForm_dvd_iff σ M (f * g) hfg).mp hdvd
  rw [hs1, σ.hRmul f g hf hg] at hRk
  -- bottom-coefficient dichotomy in K[z̄^{±1}]
  have hbot : (σ.R f) 0 * (σ.R g) 0 = 0 := by
    have h1 : (σ.R f * σ.R g) 0 = 0 := by
      rw [hRk]
      exact u5_T_one_mul_coeff_zero (σ.R k) (fun n hn => (hwin k hk0 n hn).1)
    rw [← u5_bot_coeff_mul (σ.R f) (σ.R g) (fun n hn => (hwin f hf n hn).1)
      (fun n hn => (hwin g hg n hn).1)]
    exact h1
  have key : ∀ u : Polynomial ℤ_[p], u ≠ 0 → (σ.R u) 0 = 0 →
      (letI := M.Rg.ring; M.S.initialForm σ.Φ ∣ M.S.initialForm u) := by
    intro u hu0 hcoeff
    have hguard : ∀ n ∈ (σ.R u).support, (1 : ℤ) ≤ n := by
      intro n hn
      have h0 := (hwin u hu0 n hn).1
      have hne : n ≠ 0 := by
        intro h
        subst h
        exact Finsupp.mem_support_iff.mp hn hcoeff
      omega
    obtain ⟨q, hq0, hRq, hwq⟩ := hquo u hu0 hguard
    refine (u5_initialForm_dvd_iff σ M u hu0).mpr ⟨q, hq0, ?_, ?_⟩
    · rw [hs1, hRq, ← mul_assoc, ← LaurentPolynomial.T_add]
      norm_num
    · rw [hwq]
      ring
  rcases mul_eq_zero.mp hbot with h1 | h1
  · exact Or.inl (key f hf h1)
  · exact Or.inr (key g hg h1)

/-- **(KPirr)** `in(Φ)` is prime in `gr` — the graded reduction of the homogeneous
core (truncation at the maximal non-divisible components). -/
private lemma u5_key_prime
    (ht0 : σ.t = 0)
    (hwin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∀ n ∈ (σ.R f).support, (0 : ℤ) ≤ n ∧ n * (σ.h : ℤ) ≤ σ.w f)
    (hquo : ∀ f : Polynomial ℤ_[p], f ≠ 0 → (∀ n ∈ (σ.R f).support, (1 : ℤ) ≤ n) →
      ∃ g : Polynomial ℤ_[p], g ≠ 0 ∧
        σ.R g = LaurentPolynomial.T (-1) * σ.R f ∧ σ.w g = σ.w f - σ.h) :
    letI := M.Rg.ring; Prime (M.S.initialForm σ.Φ) := by
  letI := M.Rg.ring
  haveI : IsDomain M.S.Gr := u5_gr_domain σ M
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  refine ⟨?_, u5_key_not_unit σ M (u5_w_nonneg σ hwin), ?_⟩
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
      ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ) := by
    by_contra hall
    push_neg at hall
    refine hnx (u5_dvd_of_dvd_components M.S M.Rg _ x fun γ => ?_)
    by_cases hγ : γ ∈ DFinsupp.support x
    · exact hall γ hγ
    · rw [DFinsupp.notMem_support_iff.mp hγ, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  have hSy : ∃ γ ∈ DFinsupp.support y,
      ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ) := by
    by_contra hall
    push_neg at hall
    refine hny (u5_dvd_of_dvd_components M.S M.Rg _ y fun γ => ?_)
    by_cases hγ : γ ∈ DFinsupp.support y
    · exact hall γ hγ
    · rw [DFinsupp.notMem_support_iff.mp hγ, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  set Sx := (DFinsupp.support x).filter
    (fun γ => ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ)) with hSxdef
  set Sy := (DFinsupp.support y).filter
    (fun γ => ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ)) with hSydef
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
  -- ψ divides the discarded tails componentwise
  have hdvd_high_x : ∀ γ : ℤ, m < γ →
      M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (x γ) := by
    intro γ hγ
    by_cases hmem : γ ∈ DFinsupp.support x
    · by_contra hnd
      have hin : γ ∈ Sx := Finset.mem_filter.mpr ⟨hmem, hnd⟩
      exact absurd (Sx.le_max' γ hin) (not_le.mpr hγ)
    · rw [DFinsupp.notMem_support_iff.mp hmem, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
  have hdvd_high_y : ∀ γ : ℤ, n < γ →
      M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) γ (y γ) := by
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
  have hxtail : M.S.initialForm σ.Φ ∣ x - x' := by
    refine u5_dvd_of_dvd_components M.S M.Rg _ (x - x') fun γ => ?_
    by_cases hγ : γ ≤ m
    · rw [hsub_apply x x' γ, hx'app γ, if_pos hγ, sub_self, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
    · rw [hsub_apply x x' γ, hx'app γ, if_neg hγ, sub_zero]
      exact hdvd_high_x γ (not_le.mp hγ)
  have hytail : M.S.initialForm σ.Φ ∣ y - y' := by
    refine u5_dvd_of_dvd_components M.S M.Rg _ (y - y') fun γ => ?_
    by_cases hγ : γ ≤ n
    · rw [hsub_apply y y' γ, hy'app γ, if_pos hγ, sub_self, u5_of_zero_ring M.S M.Rg]
      exact dvd_zero _
    · rw [hsub_apply y y' γ, hy'app γ, if_neg hγ, sub_zero]
      exact hdvd_high_y γ (not_le.mp hγ)
  -- ψ divides the truncated product
  have hdvd' : M.S.initialForm σ.Φ ∣ x' * y' := by
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
  have hdvd_top : M.S.initialForm σ.Φ ∣
      DirectSum.of (fun δ => M.S.grPiece δ) m (x m)
        * DirectSum.of (fun δ => M.S.grPiece δ) n (y n) := by
    have h1 := u5_key_dvd_components σ M (x' * y') hdvd' (m + n)
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
  have hmnd : ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) m (x m) := by
    have hin := Sx.max'_mem hSxne
    rw [← hm] at hin
    exact (Finset.mem_filter.mp hin).2
  have hnnd : ¬ M.S.initialForm σ.Φ ∣ DirectSum.of (fun δ => M.S.grPiece δ) n (y n) := by
    have hin := Sy.max'_mem hSyne
    rw [← hn] at hin
    exact (Finset.mem_filter.mp hin).2
  rcases u5_hom_core σ M ht0 hwin hquo u v hu0 hv0 hdvd_top with h | h
  · exact hmnd (huof ▸ h)
  · exact hnnd (hvof ▸ h)

end Prime

/-! ## F. The degree block and the H1-U5 assembly -/

section Assembly

variable (σ : Stage p F) (M : GenuineStageModel σ)

/-- **(KPa) degree block** at the base: no coefficient (degree `< deg Φ`) has its
initial form divisible by `in(Φ)` — its residual is slot-0 anchored (`hS5` at
`t = 0`) while key multiples avoid slot 0. -/
private lemma u5_kpa_block
    (ht0 : σ.t = 0)
    (hwin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∀ n ∈ (σ.R f).support, (0 : ℤ) ≤ n ∧ n * (σ.h : ℤ) ≤ σ.w f) :
    letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
      B.natDegree < σ.Φ.natDegree → ¬ M.S.initialForm σ.Φ ∣ M.S.initialForm B := by
  letI := M.Rg.ring
  intro B hB hdeg hdvd
  have hs1 := u5_s_eq_one σ ht0
  obtain ⟨g, hg0, hRB, _⟩ := (u5_initialForm_dvd_iff σ M B hB).mp hdvd
  rw [hs1] at hRB
  -- the coefficient's residual is slot-0 anchored (hS5 at t = 0)
  have hinC : inC σ.Φ B := by
    show B.degree < σ.Φ.degree
    exact Polynomial.degree_lt_degree hdeg
  obtain ⟨c, hc⟩ := σ.hS5 B hB hinC
  rw [ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one] at hc
  have hc0 : (σ.R B) 0 = (c : ↥σ.K) := by
    rw [hc, ← LaurentPolynomial.single_eq_C]
    exact Finsupp.single_eq_same
  -- but a T·(...)-multiple has vanishing slot 0
  have hz : (σ.R B) 0 = 0 := by
    rw [hRB]
    exact u5_T_one_mul_coeff_zero (σ.R g) (fun n hn => (hwin g hg0 n hn).1)
  rw [hc0] at hz
  exact c.ne_zero hz

/-- **H1-U5 (`kpBlock_base`)** — the `KPBlock` at a base stage (d₀ = 1; O-1thr
KEY1). Verbatim target of blueprint §5.2 with the probe-first base binder block
(see the module header for the probe record of each binder against the HC1/HC2
base builders). `ψ̂ := in(Φ)` itself, unit `1`. -/
theorem kpBlock_base (σ : Stage p F) (M : GenuineStageModel σ)
    (hd1 : σ.Φ.natDegree = 1) (ht0 : σ.t = 0)
    (hwin : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∀ n ∈ (σ.R f).support, (0 : ℤ) ≤ n ∧ n * (σ.h : ℤ) ≤ σ.w f)
    (hquo : ∀ f : Polynomial ℤ_[p], f ≠ 0 → (∀ n ∈ (σ.R f).support, (1 : ℤ) ≤ n) →
      ∃ g : Polynomial ℤ_[p], g ≠ 0 ∧
        σ.R g = LaurentPolynomial.T (-1) * σ.R f ∧ σ.w g = σ.w f - σ.h) :
    Nonempty (KPBlock σ M) := by
  letI := M.Rg.ring
  exact ⟨{ ψhom := M.S.initialForm σ.Φ
           homog := ⟨M.S.deg σ.Φ, M.S.mkPiece σ.Φ, rfl⟩
           kpa_init := ⟨1, by rw [Units.val_one, one_mul]⟩
           kpirr := u5_key_prime σ M ht0 hwin hquo
           kpa_block := u5_kpa_block σ M ht0 hwin }⟩

end Assembly

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.kpBlock_base
