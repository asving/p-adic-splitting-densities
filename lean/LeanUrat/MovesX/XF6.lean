/-
Unit XF.6 ballCover  [PROVED — performance-repaired 2026-07-27]
moves_ref: "the a₀-translation, union bound + Fubini" (pairwise-congruence form;
`Event`/`fTail` = Defs).
sketch: f′ a₀-free (`xf6_gEq` via `xf6_polyDiff`); each event point sits over a root θᵢ
of the tail `g = fTail` with `V.w (aeval θᵢ (F a0)) ≤ c := p^{−(D−n·v)/(n−1)}`
(`xf6_capture`, via XF.2 + XF.4 + the multiplicative pigeonhole `xf6_argmin`); two points
captured by the same root are ultrametrically congruent (`xf6_ultra`: a `ValExt` value is
nonarchimedean since it is bounded by 1 on ℕ); raising the closeness to the (n−1)-th
power gives the integer valuation bound (`xf6_endgame`, sign-split-free). `idx` picks a
capturing root index (`xf6_idx`).
PERF REPAIR (2026-07-27, escalation prover): the fleet's monolithic proof (fleet record
328e926; preserved at lean/notes/XF6_pending_reverify_2026-07-27.lean.txt) hit a kernel
deterministic timeout at `ballCover` (>1200s). Bisection localized the bomb to the
`(hgeq a0).symm ▸ V` transport of `ValExt` along the derivative equation: the stuck
`Eq.rec` in the type index forces kernel defeq dives comparing `fTail` against the
a₀-family derivative (a must-fail comparison after unfolding into Finsupp land). Repair:
(i) the transport + `xf6_prodTransfer` replaced by the `subst`-based wrapper
`xf6_resRootSum` over an abstract `g` with hypothesis `g = fTail …` (consumers pass
`rfl`); (ii) the proof split into per-declaration private lemmas so each kernel
certification is small. Full file now certifies in ~6s.
deps: XF.2 (proved), XF.4/XF.5 (INTERNAL unit, V explicit). Statement verbatim
(statement-fence). difficulty: MEDIUM-HARD.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF2
import LeanUrat.MovesX.XF4
import LeanUrat.MovesX.XF5

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

open Polynomial

/-! ### Helper lemmas (unchanged from the fleet proof) -/

/-- Any `ValExt`'s absolute value is nonarchimedean: it extends `‖·‖_p`, hence is bounded
by `1` on `ℕ`, and a `NormedDivisionRing` with that property is ultrametric. -/
private lemma xf6_ultra {p : ℕ} [Fact p.Prime] {g : Polynomial ℚ_[p]} (V : ValExt p g)
    (x y : V.L) : V.w (x - y) ≤ max (V.w x) (V.w y) := by
  set e := WithAbs.equiv V.w with he
  have hnorm : ∀ z : V.L, ‖e.symm z‖ = V.w z := by
    intro z; rw [WithAbs.norm_eq_apply_ofAbs]; congr 1
  have hU : IsUltrametricDist (WithAbs V.w) := by
    apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro k
    have h0 : ((k : WithAbs V.w)) = e.symm (k : V.L) := by simp [he]
    rw [h0, hnorm]
    have h1 : ((k : V.L)) = algebraMap ℚ_[p] V.L (k : ℚ_[p]) := by push_cast; rfl
    rw [h1, V.ext]
    exact_mod_cast (PadicInt.norm_le_one ((k : ℤ_[p])))
  have hmax := IsUltrametricDist.norm_add_le_max (e.symm x) (- e.symm y)
  rwa [show e.symm x + - e.symm y = e.symm (x - y) by rw [← sub_eq_add_neg, ← map_sub],
      norm_neg, hnorm, hnorm, hnorm] at hmax

/-- The tail `∑ᵢ C(aᵢ)Xⁱ` of `polyOfCoeffs` has degree `< n`. -/
private lemma xf6_deglt (n : ℕ) (hn : 1 ≤ n) {p : ℕ} [Fact p.Prime] (a : Fin n → ℤ_[p]) :
    (∑ i : Fin n, C (a i) * X ^ (i:ℕ)).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine lt_of_le_of_lt (Finset.sup_le (fun i _ => ?_)) (WithBot.coe_lt_coe.mpr (by omega : n - 1 < n))
  exact le_trans (degree_C_mul_X_pow_le (i:ℕ) (a i)) (WithBot.coe_le_coe.mpr (by omega : (i:ℕ) ≤ n - 1))

private lemma xf6_monic (n : ℕ) (hn : 1 ≤ n) {p : ℕ} [Fact p.Prime] (a : Fin n → ℤ_[p]) :
    (polyOfCoeffs ℤ_[p] n a).Monic := by
  unfold polyOfCoeffs; exact monic_X_pow_add (xf6_deglt n hn a)

private lemma xf6_natDegree (n : ℕ) (hn : 1 ≤ n) {p : ℕ} [Fact p.Prime] (a : Fin n → ℤ_[p]) :
    (polyOfCoeffs ℤ_[p] n a).natDegree = n := by
  unfold polyOfCoeffs
  have hd : (X ^ n + ∑ i : Fin n, C (a i) * X ^ (i:ℕ)).degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
    exact xf6_deglt n hn a
  exact natDegree_eq_of_degree_eq_some hd

/-- Two family members with constant terms `a0`, `b0` differ by the constant `C (a0 - b0)`. -/
private lemma xf6_polyDiff (n : ℕ) (hn : 1 ≤ n) {p : ℕ} [Fact p.Prime]
    (aTail : Fin (n - 1) → ℤ_[p]) (a0 b0 : ℤ_[p]) :
    polyOfCoeffs ℤ_[p] n ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))
    - polyOfCoeffs ℤ_[p] n ((Fin.cons b0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))
    = C (a0 - b0) := by
  unfold polyOfCoeffs
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have hcons : ∀ x : Fin (n-1+1),
      (Fin.cons a0 aTail : Fin (n-1+1) → ℤ_[p]) x - (Fin.cons b0 aTail : Fin (n-1+1) → ℤ_[p]) x
        = if x = 0 then a0 - b0 else 0 := by
    intro x; induction x using Fin.cases with | zero => simp | succ j => simp
  have hterm : ∀ i : Fin n,
      C (((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1)) i) * X ^ (i:ℕ)
      - C (((Fin.cons b0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1)) i) * X ^ (i:ℕ)
      = if (i:ℕ) = 0 then C (a0 - b0) else 0 := by
    intro i
    rw [← sub_mul, ← map_sub]
    simp only [Function.comp_apply, hcons]
    by_cases hi : (i:ℕ) = 0
    · have hz : Fin.cast (by omega : n = n - 1 + 1) i = 0 := by simp [Fin.ext_iff, hi]
      rw [hz]; simp [hi]
    · have hz : ¬ (Fin.cast (by omega : n = n - 1 + 1) i = 0) := by simp [Fin.ext_iff, hi]
      rw [if_neg hz, if_neg hi]; simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext (by simp [h]))
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Product of a multiset of reals, each `≥ a ≥ 0`, is `≥ a ^ card`. -/
private lemma xf6_prodGe (m : Multiset ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ x ∈ m, a ≤ x) :
    a ^ m.card ≤ m.prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    rw [Multiset.card_cons, Multiset.prod_cons, pow_succ]
    have hb : a ≤ b := h b (Multiset.mem_cons_self b t)
    have ht : ∀ x ∈ t, a ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have htp : (0:ℝ) ≤ t.prod := Multiset.prod_nonneg (fun x hx => le_trans ha (ht x hx))
    calc a ^ t.card * a ≤ t.prod * b := mul_le_mul (ih ht) hb ha htp
      _ = b * t.prod := by ring

/-- Multiplicative pigeonhole: if a nonempty multiset of nonneg reals has product `≤ P`,
some element is `≤ c` where `c ^ card = P`. -/
private lemma xf6_argmin {ι : Type*} (s : Multiset ι) (hne : s ≠ 0) (f : ι → ℝ)
    (hpos : ∀ x ∈ s, 0 ≤ f x) (k : ℕ) (hk : s.card = k) (hk0 : k ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (P : ℝ) (hP : (s.map f).prod ≤ P) (hcP : c ^ k = P) :
    ∃ x ∈ s, f x ≤ c := by
  classical
  obtain ⟨x0, hx0mem, hx0min⟩ := Finset.exists_min_image s.toFinset f (by
    rwa [Finset.nonempty_iff_ne_empty, Ne, Multiset.toFinset_eq_empty])
  have hx0s : x0 ∈ s := Multiset.mem_toFinset.mp hx0mem
  refine ⟨x0, hx0s, ?_⟩
  have hmin : ∀ y ∈ s.map f, f x0 ≤ y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    exact hx0min z (Multiset.mem_toFinset.mpr hz)
  have hlb : (f x0) ^ k ≤ (s.map f).prod := by
    have := xf6_prodGe (s.map f) (f x0) (hpos x0 hx0s) hmin
    rwa [Multiset.card_map, hk] at this
  have hkc : (f x0) ^ k ≤ c ^ k := by rw [hcP]; exact le_trans hlb hP
  exact le_of_pow_le_pow_left₀ hk0 hc hkc

/-! ### New per-declaration helpers (the performance split) -/

/-- XF.4's root-product identity over an abstract `g` given `g = f′` — a `subst`-based
wrapper replacing the fleet proof's `(hgeq a0).symm ▸ V` transport + `xf6_prodTransfer`
(whose stuck `Eq.rec` in the `ValExt` type index forced kernel defeq dives). -/
private lemma xf6_resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n) {g : Polynomial ℚ_[p]} (V : ValExt p g)
    (hg : (f.map PadicInt.Coe.ringHom).derivative = g) :
    ‖f.resultant f.derivative‖ =
      ‖(n : ℚ_[p])‖ ^ n *
        (((g.map (algebraMap ℚ_[p] V.L)).roots).map
          (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.Coe.ringHom)))).prod := by
  subst hg
  exact resRootSum p n h2 f hm hd V

/-- The tail derivative is a₀-free: every family member's mapped derivative is `fTail`. -/
private lemma xf6_gEq (n : ℕ) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (aTail : Fin (n - 1) → ℤ_[p]) (a0 : ℤ_[p]) :
    ((polyOfCoeffs ℤ_[p] n ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map
        PadicInt.Coe.ringHom).derivative = fTail n p hn aTail := by
  have hzero : (polyOfCoeffs ℤ_[p] n ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))
      - polyOfCoeffs ℤ_[p] n ((Fin.cons (0 : ℤ_[p]) aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).derivative
      = 0 := by
    rw [xf6_polyDiff n hn aTail a0 0, derivative_C]
  rw [derivative_sub] at hzero
  have hder := sub_eq_zero.mp hzero
  rw [derivative_map, hder, ← derivative_map]
  rfl

/-- `natDegree (fTail) = n - 1`. -/
private lemma xf6_fTailDeg (n : ℕ) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (aTail : Fin (n - 1) → ℤ_[p]) :
    (fTail n p hn aTail).natDegree = n - 1 := by
  rw [← xf6_gEq n hn p aTail 0, Polynomial.natDegree_derivative,
      (xf6_monic n hn _).natDegree_map PadicInt.Coe.ringHom, xf6_natDegree n hn _]

/-- The real-power cycle `(p^(x/(n-1)))^(n-1) = p^x` (left power `Monoid.npow`, inner
powers `Real.rpow`). -/
private lemma xf6_rpow_cycle (p : ℕ) (hp0 : (0 : ℝ) < p) (n : ℕ) (h2 : 2 ≤ n) (x : ℝ) :
    ((p : ℝ) ^ (x / ((n : ℝ) - 1))) ^ (n - 1) = (p : ℝ) ^ x := by
  have hn1R : ((n : ℝ) - 1) ≠ 0 := by
    have h2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  rw [← Real.rpow_natCast ((p : ℝ) ^ (x / ((n : ℝ) - 1))) (n - 1), ← Real.rpow_mul hp0.le]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp

/-- The capture: an event point's family member is `c`-small at some root of the tail,
`c = p^(−(D−n·v_p(n))/(n−1))`. `g` is abstract with `hgfT : g = fTail …` so that no
hypothesis re-typing (`set`/`replace` on `V`) is ever needed — the goal mentions `V.L`. -/
private lemma xf6_capture (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n)
    (aTail : Fin (n - 1) → ℤ_[p]) {g : Polynomial ℚ_[p]} (V : ValExt p g)
    (hgfT : g = fTail n p (by omega) aTail)
    (a0 : ℤ_[p]) (hev : Event p n D (by omega) aTail a0) :
    ∃ θ ∈ (g.map (algebraMap ℚ_[p] V.L)).roots,
      V.w (Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
          ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom))
        ≤ (p : ℝ) ^ (((-((D : ℤ) - n * padicValNat p n) : ℤ) : ℝ) / ((n : ℝ) - 1)) := by
  classical
  have hn : 1 ≤ n := by omega
  set F : Polynomial ℤ_[p] :=
    polyOfCoeffs ℤ_[p] n ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1)) with hF
  have hFmon : F.Monic := xf6_monic n hn _
  have hFdeg : F.natDegree = n := xf6_natDegree n hn _
  have hgeq : (F.map PadicInt.Coe.ringHom).derivative = g := by
    rw [hF, hgfT]; exact xf6_gEq n hn p aTail a0
  set R : Multiset V.L := (g.map (algebraMap ℚ_[p] V.L)).roots with hR
  have hgdeg : g.natDegree = n - 1 := by rw [hgfT]; exact xf6_fTailDeg n (by omega) p aTail
  have hRcard : R.card = n - 1 := by
    have h1 : (g.map (algebraMap ℚ_[p] V.L)).roots.card = (g.map (algebraMap ℚ_[p] V.L)).natDegree :=
      Polynomial.splits_iff_card_roots.mp V.splits
    rw [hR, h1, Polynomial.natDegree_map, hgdeg]
  have hRne : R ≠ 0 := by rw [Ne, ← Multiset.card_eq_zero, hRcard]; omega
  -- constants
  have hnpos : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnnorm : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hnpos, Padic.valuation_natCast]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set e0 : ℤ := (D : ℤ) - n * padicValNat p n with he0
  set P : ℝ := (p : ℝ) ^ (-e0) with hPdef
  set c : ℝ := (p : ℝ) ^ (((-e0 : ℤ) : ℝ) / ((n : ℝ) - 1)) with hcdef
  have hcpos : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hck : c ^ (n - 1) = P := by
    rw [hcdef, hPdef, xf6_rpow_cycle p hp0 n h2, Real.rpow_intCast]
  have hnpow : ‖(n : ℚ_[p])‖ ^ n = (p : ℝ) ^ (-(n * padicValNat p n : ℤ)) := by
    rw [hnnorm, ← zpow_natCast ((p : ℝ) ^ (-(padicValNat p n : ℤ))) n, ← zpow_mul]
    congr 1; push_cast; ring
  -- the three ingredients: root-product identity, disc–resultant bridge, event bound
  have hres : ‖F.resultant F.derivative‖ = ‖(n : ℚ_[p])‖ ^ n *
      (R.map (fun θ => V.w (Polynomial.aeval θ (F.map PadicInt.Coe.ringHom)))).prod := by
    rw [hR]; exact xf6_resRootSum p n h2 F hFmon hFdeg V hgeq
  have hbridge := discResBridge p F hFmon (by rw [hFdeg]; omega)
  have hdnorm : ‖F.discr‖ ≤ (p : ℝ) ^ (-(D : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact hev
  have hcomb : ‖(n : ℚ_[p])‖ ^ n *
      (R.map (fun θ => V.w (Polynomial.aeval θ (F.map PadicInt.Coe.ringHom)))).prod
      ≤ (p : ℝ) ^ (-(D : ℤ)) := by rw [← hres, ← hbridge]; exact hdnorm
  have hprod : (R.map (fun θ => V.w (Polynomial.aeval θ (F.map PadicInt.Coe.ringHom)))).prod ≤ P := by
    rw [hnpow] at hcomb
    have hpp : (0 : ℝ) < (p : ℝ) ^ (-(n * padicValNat p n : ℤ)) := by positivity
    have hAP : (p : ℝ) ^ (-(n * padicValNat p n : ℤ)) * P = (p : ℝ) ^ (-(D : ℤ)) := by
      rw [hPdef, he0, ← zpow_add₀ (ne_of_gt hp0)]; congr 1; ring
    rw [← hAP] at hcomb
    exact le_of_mul_le_mul_left hcomb hpp
  exact xf6_argmin R hRne _ (fun θ _ => (V.w).nonneg _) (n - 1) hRcard (by omega) c hcpos P hprod hck

/-- The index map: a root enumeration `E` and an index choice `idx` capturing every
event point. `g` abstract as in `xf6_capture`. -/
private lemma xf6_idx (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n)
    (aTail : Fin (n - 1) → ℤ_[p]) {g : Polynomial ℚ_[p]} (V : ValExt p g)
    (hgfT : g = fTail n p (by omega) aTail) :
    ∃ (idx : ℤ_[p] → Fin (n - 1)) (E : Fin (n - 1) → V.L),
      ∀ a0 : ℤ_[p], Event p n D (by omega) aTail a0 →
        V.w (Polynomial.aeval (E (idx a0)) ((polyOfCoeffs ℤ_[p] n
            ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom))
          ≤ (p : ℝ) ^ (((-((D : ℤ) - n * padicValNat p n) : ℤ) : ℝ) / ((n : ℝ) - 1)) := by
  classical
  have hn : 1 ≤ n := by omega
  set R : Multiset V.L := (g.map (algebraMap ℚ_[p] V.L)).roots with hR
  have hgdeg : g.natDegree = n - 1 := by rw [hgfT]; exact xf6_fTailDeg n (by omega) p aTail
  have hRcard : R.card = n - 1 := by
    have h1 : (g.map (algebraMap ℚ_[p] V.L)).roots.card = (g.map (algebraMap ℚ_[p] V.L)).natDegree :=
      Polynomial.splits_iff_card_roots.mp V.splits
    rw [hR, h1, Polynomial.natDegree_map, hgdeg]
  have hlen : R.toList.length = n - 1 := by rw [Multiset.length_toList, hRcard]
  set E : Fin (n - 1) → V.L := fun i => R.toList.get (Fin.cast hlen.symm i) with hE
  have captureIdx : ∀ a0 : ℤ_[p], Event p n D (by omega : 1 ≤ n) aTail a0 →
      ∃ i : Fin (n - 1), V.w (Polynomial.aeval (E i) ((polyOfCoeffs ℤ_[p] n
          ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom))
        ≤ (p : ℝ) ^ (((-((D : ℤ) - n * padicValNat p n) : ℤ) : ℝ) / ((n : ℝ) - 1)) := by
    intro a0 hev
    obtain ⟨θ, hθmem, hθle⟩ := xf6_capture p n D h2 aTail V hgfT a0 hev
    rw [← hR] at hθmem
    rw [← Multiset.mem_toList] at hθmem
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hθmem
    refine ⟨Fin.cast hlen k, ?_⟩
    have hEk : E (Fin.cast hlen k) = θ := by
      rw [hE]; simp only []
      rw [show (Fin.cast hlen.symm (Fin.cast hlen k)) = k from by ext; simp]
      exact hk
    rw [hEk]; exact hθle
  refine ⟨fun a0 => if h : Event p n D (by omega : 1 ≤ n) aTail a0
      then Classical.choose (captureIdx a0 h) else ⟨0, by omega⟩, E, ?_⟩
  intro a0 hev
  simp only []
  rw [dif_pos hev]
  exact Classical.choose_spec (captureIdx a0 hev)

/-- Ultrametric closeness: two family members `c`-small at the same point have
`c`-close constant terms. -/
private lemma xf6_close (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n)
    (aTail : Fin (n - 1) → ℤ_[p]) {g : Polynomial ℚ_[p]} (V : ValExt p g)
    (θ : V.L) (a0 b0 : ℤ_[p]) (c : ℝ)
    (ha : V.w (Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
        ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom)) ≤ c)
    (hb : V.w (Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
        ((Fin.cons b0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom)) ≤ c) :
    ‖a0 - b0‖ ≤ c := by
  have hult := xf6_ultra V (Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
      ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom))
      (Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
      ((Fin.cons b0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom))
  have hdiffeval : Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
        ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom)
      - Polynomial.aeval θ ((polyOfCoeffs ℤ_[p] n
        ((Fin.cons b0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map PadicInt.Coe.ringHom)
      = algebraMap ℚ_[p] V.L (PadicInt.Coe.ringHom (a0 - b0)) := by
    rw [← map_sub, ← Polynomial.map_sub, xf6_polyDiff n hn aTail a0 b0, Polynomial.map_C,
        Polynomial.aeval_C]
  have h3 := le_trans hult (max_le ha hb)
  rw [hdiffeval, V.ext,
      show PadicInt.Coe.ringHom (a0 - b0) = ((a0 - b0 : ℤ_[p]) : ℚ_[p]) from rfl,
      PadicInt.padic_norm_e_of_padicInt] at h3
  exact h3

/-- Endgame: `c`-closeness of the constant terms gives the `tailExp` congruence
(no sign split needed — the `⌈·⌉ ≤ ·` argument is unconditional). -/
private lemma xf6_endgame (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (a0 b0 : ℤ_[p])
    (hnormle : ‖a0 - b0‖ ≤ (p : ℝ) ^ (((-((D : ℤ) - n * padicValNat p n) : ℤ) : ℝ) / ((n : ℝ) - 1))) :
    (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0) := by
  classical
  have hn : 1 ≤ n := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set e0 : ℤ := (D : ℤ) - n * padicValNat p n with he0
  set P : ℝ := (p : ℝ) ^ (-e0) with hPdef
  set c : ℝ := (p : ℝ) ^ (((-e0 : ℤ) : ℝ) / ((n : ℝ) - 1)) with hcdef
  have hck : c ^ (n - 1) = P := by
    rw [hcdef, hPdef, xf6_rpow_cycle p hp0 n h2, Real.rpow_intCast]
  rcases eq_or_ne a0 b0 with hab | hab
  · rw [hab, sub_self]; exact dvd_zero _
  · rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
        PadicInt.norm_le_pow_iff_le_valuation _ (sub_ne_zero.mpr hab)]
    have hvalnorm : ‖a0 - b0‖ = (p : ℝ) ^ (-((a0 - b0).valuation : ℤ)) :=
      PadicInt.norm_eq_zpow_neg_valuation (sub_ne_zero.mpr hab)
    have hpow : ‖a0 - b0‖ ^ (n - 1) ≤ P := by
      calc ‖a0 - b0‖ ^ (n - 1) ≤ c ^ (n - 1) :=
            pow_le_pow_left₀ (norm_nonneg _) hnormle _
        _ = P := hck
    rw [hvalnorm, ← zpow_natCast ((p : ℝ) ^ (-((a0 - b0).valuation : ℤ))) (n - 1),
        ← zpow_mul, hPdef] at hpow
    have hexp : -((a0 - b0).valuation : ℤ) * ((n - 1 : ℕ) : ℤ) ≤ -e0 :=
      (zpow_le_zpow_iff_right₀ hp1).mp hpow
    have he0le : e0 ≤ ((a0 - b0).valuation : ℤ) * ((n - 1 : ℕ) : ℤ) := by linarith
    have hden : (0 : ℚ) < (n - 1 : ℚ) := by
      have : (2 : ℚ) ≤ n := by exact_mod_cast h2
      linarith
    refine Int.toNat_le.mpr ?_
    change ⌈((D : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)⌉ ≤ ((a0 - b0).valuation : ℤ)
    refine Int.ceil_le.mpr ?_
    rw [div_le_iff₀ hden]
    have he0le' : e0 ≤ ((a0 - b0).valuation : ℤ) * ((n : ℤ) - 1) := by
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub hn]; norm_num
      rw [hcast] at he0le; exact he0le
    rw [he0] at he0le'
    have hQ := (Int.cast_le (R := ℚ)).mpr he0le'
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] at hQ
    push_cast at ⊢
    linarith

theorem ballCover (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (V : ValExt p (fTail n p (by omega) aTail)) :
    ∃ idx : ℤ_[p] → Fin (n - 1), ∀ a0 b0,
      Event p n D (by omega) aTail a0 → Event p n D (by omega) aTail b0 →
      idx a0 = idx b0 → (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0) := by
  classical
  obtain ⟨idx, E, hcap⟩ := xf6_idx p n D h2 aTail V rfl
  refine ⟨idx, fun a0 b0 ha hb hidx => ?_⟩
  have h1 := hcap a0 ha
  have hb1 := hcap b0 hb
  rw [hidx] at h1
  exact xf6_endgame p n D h2 a0 b0
    (xf6_close p n (by omega) aTail V (E (idx b0)) a0 b0 _ h1 hb1)

end LeanUrat.MovesX
