/-
# First-order recurrence limit with varying (convergent) forcing

Blueprint Target D (`RECLIMIT_BLUEPRINT.md`).  This is a NEW leaf module, imported by
nothing yet.  It provides the analytic engine missing from the suite:

* `vanishing_forcing_tendsto_zero` — the ε/2 contraction core: a recurrence
  `y(N+1) = r·y N + g(N+1)` with `0 ≤ r < 1` and `g → 0` has `y → 0`.
* `firstOrder_recurrence_limit` — the affine shift of the core: `x(N+1) = r·x N + f(N+1)`
  with `0 ≤ r < 1` and `f → L` has `x → L/(1-r)`.  Specializes
  `NestedCollapse.geometricLimit_of_selfLoop` (constant forcing) to the varying-forcing case
  that `nodeTrunc_tendsto` actually needs.
* `firstOrder_recurrence_limit_err` — one-line corollary folding a vanishing additive
  error `e → 0` into the forcing.

Stated over `ℝ` per the formalize target.  Everything is core-only (no `sorry`); intended
axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open Filter Topology

namespace LeanUrat.OM.LimitRecurrence

/-- **Vanishing-forcing contraction (the ε/2 engine).**
If `y(N+1) = r·y N + g(N+1)` with `0 ≤ r < 1` and `g → 0`, then `y → 0`. -/
theorem vanishing_forcing_tendsto_zero (y g : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ N, y (N + 1) = r * y N + g (N + 1))
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto y atTop (𝓝 0) := by
  have h1r : (0 : ℝ) < 1 - r := sub_pos.mpr hr1
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- The forcing tolerance is ε(1-r)/2, NOT ε/2.
  have htol_pos : 0 < ε * (1 - r) / 2 := by positivity
  -- Step 1: pick M past which |g n| < ε(1-r)/2.
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hg) (ε * (1 - r) / 2) htol_pos
  -- |g n| < ε(1-r)/2 for n ≥ M, written without `dist`.
  have hMabs : ∀ n, M ≤ n → |g n| < ε * (1 - r) / 2 := by
    intro n hn
    have := hM n hn
    rwa [Real.dist_eq, sub_zero] at this
  -- Step 2: the tail contraction invariant  |y (M + j)| ≤ r^j · |y M| + ε/2.
  have hstep : ∀ j, |y (M + j)| ≤ r ^ j * |y M| + ε / 2 := by
    intro j
    induction j with
    | zero =>
        simp only [Nat.add_zero, pow_zero, one_mul]
        have : (0 : ℝ) ≤ ε / 2 := by positivity
        linarith
    | succ k ih =>
        -- n := M + k ≥ M, and M + (k+1) = n + 1.
        have hnk : M ≤ M + k := Nat.le_add_right M k
        have hidx : M + (k + 1) = (M + k) + 1 := by omega
        rw [hidx, hrec (M + k)]
        -- triangle + |r·y| = r·|y| (r ≥ 0).
        have htri : |r * y (M + k) + g (M + k + 1)|
            ≤ |r * y (M + k)| + |g (M + k + 1)| := abs_add_le _ _
        have hmul : |r * y (M + k)| = r * |y (M + k)| := by
          rw [abs_mul, abs_of_nonneg hr0]
        -- forcing bound at index M + k + 1 ≥ M.
        have hgb : |g (M + k + 1)| < ε * (1 - r) / 2 :=
          hMabs (M + k + 1) (by omega)
        -- monotone contraction on the IH (r ≥ 0).
        have hcontr : r * |y (M + k)| ≤ r * (r ^ k * |y M| + ε / 2) := by
          gcongr
        -- assemble; the closing identity r·(ε/2) + ε(1-r)/2 = ε/2 is EXACT (handled by nlinarith).
        have hchain : |r * y (M + k) + g (M + k + 1)| < r ^ (k + 1) * |y M| + ε / 2 :=
          calc |r * y (M + k) + g (M + k + 1)|
              ≤ |r * y (M + k)| + |g (M + k + 1)| := htri
            _ = r * |y (M + k)| + |g (M + k + 1)| := by rw [hmul]
            _ < r * (r ^ k * |y M| + ε / 2) + ε * (1 - r) / 2 :=
                  add_lt_add_of_le_of_lt hcontr hgb
            _ = r ^ (k + 1) * |y M| + ε / 2 := by rw [pow_succ]; ring
        exact le_of_lt hchain
  -- Step 3: pick J past which r^J · |y M| < ε/2.
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hyM0 : (0 : ℝ) ≤ |y M| := abs_nonneg _
  have hε2 : 0 < ε / 2 := by positivity
  -- choose J with r^J * |y M| < ε/2
  obtain ⟨J, hJ⟩ : ∃ J, ∀ j, J ≤ j → r ^ j * |y M| < ε / 2 := by
    rcases eq_or_lt_of_le hyM0 with hzero | hpos
    · -- |y M| = 0: any J works (the product is 0 < ε/2).
      refine ⟨0, fun j _ => ?_⟩
      rw [← hzero, mul_zero]; exact hε2
    · -- |y M| > 0: use r^j → 0 to get r^j < (ε/2)/|y M|.
      have htgt : 0 < ε / 2 / |y M| := by positivity
      obtain ⟨J, hJ'⟩ := (Metric.tendsto_atTop.mp hpow) (ε / 2 / |y M|) htgt
      refine ⟨J, fun j hj => ?_⟩
      have := hJ' j hj
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr0 j)] at this
      -- r^j < (ε/2)/|y M|  ⟹  r^j * |y M| < ε/2
      rw [lt_div_iff₀ hpos] at this
      linarith
  -- Step 4: combine.  For n ≥ M + J, write n = M + j with j ≥ J.
  refine ⟨M + J, fun n hn => ?_⟩
  -- j := n - M, with n = M + j and j ≥ J.
  obtain ⟨j, rfl⟩ : ∃ j, n = M + j := ⟨n - M, by omega⟩
  have hjJ : J ≤ j := by omega
  -- |y (M+j)| ≤ r^j|yM| + ε/2 (step 2), and r^j|yM| < ε/2 (step 3 at index j ≥ J).
  have hbound := hstep j
  have hJbound := hJ j hjJ
  -- dist (y (M+j)) 0 = |y (M+j)|
  rw [Real.dist_eq, sub_zero]
  calc |y (M + j)| ≤ r ^ j * |y M| + ε / 2 := hbound
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Varying-forcing first-order recurrence limit.**
If `x(N+1) = r · x N + f(N+1)` with a fixed contraction `0 ≤ r < 1` and a convergent forcing
`f → L`, then `x → L / (1 - r)`.  The constant-forcing
`NestedCollapse.geometricLimit_of_selfLoop` is the special case `f ≡ a`, `L = a`. -/
theorem firstOrder_recurrence_limit (x f : ℕ → ℝ) (r L : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ N, x (N + 1) = r * x N + f (N + 1))
    (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto x atTop (𝓝 (L / (1 - r))) := by
  have hr1' : (1 : ℝ) - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  set S : ℝ := L / (1 - r) with hS
  -- The fixed-point equation r·S + L = S.
  have hfix : r * S + L = S := by
    rw [hS]; field_simp; ring
  -- Affine shift: y N := x N - S, g N := f N - L.
  set y : ℕ → ℝ := fun N => x N - S with hy
  set g : ℕ → ℝ := fun N => f N - L with hg
  -- y satisfies the vanishing-forcing recurrence.
  have hrec' : ∀ N, y (N + 1) = r * y N + g (N + 1) := by
    intro N
    simp only [hy, hg]
    have := hrec N
    -- x(N+1) - S = r·(x N - S) + (f(N+1) - L) + (r·S + L - S) and the last bracket is 0
    nlinarith [this, hfix]
  -- g → 0.
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have : Tendsto g atTop (𝓝 (L - L)) := hf.sub_const L
    simpa using this
  -- Core gives y → 0.
  have hy0 : Tendsto y atTop (𝓝 0) :=
    vanishing_forcing_tendsto_zero y g r hr0 hr1 hrec' hg0
  -- x = y + S → 0 + S = S.
  have hx : Tendsto (fun N => y N + S) atTop (𝓝 (0 + S)) :=
    hy0.add_const S
  have hxeq : (fun N => y N + S) = x := by
    funext N; simp only [hy]; ring
  rw [hxeq, zero_add] at hx
  exact hx

/-- **Varying-forcing recurrence limit with a vanishing additive error.**
Same as `firstOrder_recurrence_limit` but with an extra vanishing error `e → 0` in the
recurrence.  Obtained by folding `e` into the forcing. -/
theorem firstOrder_recurrence_limit_err (x f e : ℕ → ℝ) (r L : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ N, x (N + 1) = r * x N + f (N + 1) + e (N + 1))
    (hf : Tendsto f atTop (𝓝 L)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 (L / (1 - r))) := by
  -- f' := f + e converges to L + 0 = L; recurrence becomes x(N+1) = r·x N + f'(N+1).
  have hf' : Tendsto (fun N => f N + e N) atTop (𝓝 L) := by
    have := hf.add he
    simpa using this
  have hrec' : ∀ N, x (N + 1) = r * x N + (fun N => f N + e N) (N + 1) := by
    intro N; simp only; rw [hrec N]; ring
  exact firstOrder_recurrence_limit x (fun N => f N + e N) r L hr0 hr1 hrec' hf'

end LeanUrat.OM.LimitRecurrence
