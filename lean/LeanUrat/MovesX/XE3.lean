/-
Unit XE.3 envelopeSqrt — the √N fallback  [RESTATED-POST-REFUTATION 2026-07-27: the
previous ∀N conclusion was kernel-certified FALSE (notes/XE3_REFUTATION_2026-07-27.lean;
adjudication in blueprint §7). ∃ N₀ before ∀ N ≥ N₀, as in XE.2; D9 REBIND as in XE.2 (constants before ∀ X). Body sorry.]
moves_ref: "Given (X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) PLUS the same two leg
tags …: env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N} — subexponential, enough for X.3's qualitative
form, NOT for SQUEEZE's constants". Same signature as XE.2 MINUS `PR` (X2ProgressP);
XD.4 in place of PR. The rev-4 leg-tag line: BR's witness b carries IsLeafB ∧ NsFreeB,
hence FourthPieceB by the first disjunct — exactly XD.4's hypothesis.
deps: XD.4; otherwise as XE.2. difficulty: HARD.
hyp_fields: (X2-HYP)'s inputs + both leg tags.

PROOF ARCHITECTURE (from MOVES_2026-07-24 lines 11255–11350, the threshold+cap
dichotomy). Choose N₀, c3', c4' as (n,K)-functions. For N ≥ N₀ put
  A := ⌈c0+ccap⌉₊ + 1,  q := (N−A−1)/A,  M := Nat.sqrt q,  D := (2M − 2⌊log₂n⌋)/(2s+1).
(1) BRIDGE: X2BridgeP's clause-2 mass-zero gives frac(Undec N) ≤ frac(DeepEvent M) +
    frac(TallEvent M), since the witness-branch piece W(N) ⊆ DeepEvent M ∪ TallEvent M.
    That inclusion is the XD.4 (=(X2-HYP)) √-dichotomy at the fourth-piece witness b:
    N < thr(b)+cap(b) ⟹ (N−1−ccap) < (c0+ccap)·(d_total+1)²  ∨  < (c0+ccap)·(maxH)²;
    with (c0+ccap)·M² ≤ N−1−ccap (the choice of M) this forces M ≤ d_total OR M < maxH.
(2) DEEP LEG: DeepEvent M ⊆ {D ≤ v_p(disc)} ∪ {disc=0} via XC.3's 2d_total ≤
    (2s+1)v+2⌊log₂n⌋ chain; vdisc_le_tail + XF.7 give frac ≤ (n−1)·n^{n/(n−1)}·p^{−D/(n−1)}
    (the p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} absorption, p-free).
(3) TALL LEG: X2TailsP gives frac(TallEvent M) ≤ CT·p^{−cT·M} directly.
(4) √N ABSORPTION: M ≳ √N/(2√A) and D ≳ M give both exponents ≥ c4'·√N for N ≥ N₀.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XC3
import LeanUrat.MovesX.XD4
import LeanUrat.MovesX.XE1a
import LeanUrat.MovesX.XE1b
import LeanUrat.MovesX.XE1c
import LeanUrat.MovesX.XE1d
import LeanUrat.MovesX.XE1e
import LeanUrat.MovesX.XE1f
import LeanUrat.MovesX.XE1g
import LeanUrat.MovesX.XE1h
import LeanUrat.MovesX.XF7
import LeanUrat.MovesX.XG2b
import LeanUrat.MovesX.XG2c
import LeanUrat.MovesX.XG2d

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Real

/-- If `m < maxH H` then some node of `H` has height `> m`. -/
private lemma maxH_gt {n : ℕ} : ∀ (H : XHistory n) (m : ℕ), m < maxH H → ∃ ν ∈ H, m < ν.h := by
  intro H
  induction H with
  | nil => intro m hm; simp only [maxH, List.map_nil, List.foldr_nil] at hm; omega
  | cons a l ih =>
    intro m hm
    have hcons : maxH (a :: l) = max a.h (maxH l) := by
      simp only [maxH, List.map_cons, List.foldr_cons]
    rw [hcons] at hm
    rcases lt_or_ge m a.h with h1 | h1
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h1⟩
    · have hml : m < maxH l := by omega
      obtain ⟨ν, hν, hνh⟩ := ih m hml
      exact ⟨ν, List.mem_cons.mpr (Or.inr hν), hνh⟩

/-- From `a·M² < a·y²` with `a ≥ 0` (over ℚ, `M y : ℕ`) conclude `M < y`. -/
private lemma nat_lt_of_mul_sq_lt {a : ℚ} (ha : 0 ≤ a) {M y : ℕ}
    (h : a * (M:ℚ)^2 < a * (y:ℚ)^2) : M < y := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0] at h; simp at h
  · have hsq : (M:ℚ)^2 < (y:ℚ)^2 := lt_of_mul_lt_mul_left h (le_of_lt hpos)
    have hn : M^2 < y^2 := by exact_mod_cast hsq
    exact lt_of_pow_lt_pow_left' 2 hn

/-- The `p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)}` absorption (p-free): from the ceiling bound on
`tailExp`, upgrade the zpow envelope `(n−1)·p^{−tailExp}` to `(n−1)·n^{n/(n−1)}·p^{−D/(n−1)}`. -/
private lemma offset_absorb (p n D : ℕ) (hn : 2 ≤ n) (v : ℕ) (hv : p ^ v ≤ n) (hp1 : (1:ℝ) ≤ p)
    (te : ℤ) (hte : ((D:ℚ) - n*v)/(n-1) ≤ (te:ℚ)) :
    ((n:ℝ)-1) * (p:ℝ)^(-te) ≤ ((n:ℝ)-1) * (n:ℝ)^((n:ℝ)/((n:ℝ)-1)) * (p:ℝ)^(-((D:ℝ)/((n:ℝ)-1))) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < (n:ℝ) - 1 := by linarith
  set nr : ℝ := (n:ℝ) with hnr
  set Dr : ℝ := (D:ℝ) with hDr
  set vr : ℝ := (v:ℝ) with hvr
  have hteR : (Dr - nr*vr)/(nr-1) ≤ (te:ℝ) := by rw [hnr, hDr, hvr]; exact_mod_cast hte
  have step1 : (p:ℝ)^(-te) ≤ (p:ℝ)^(-(Dr/(nr-1)) + nr*vr/(nr-1)) := by
    rw [← Real.rpow_intCast (p:ℝ) (-te)]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    rw [neg_le]
    have h : -(-(Dr/(nr-1)) + nr*vr/(nr-1)) = (Dr - nr*vr)/(nr-1) := by ring
    rw [h]; exact hteR
  have step2 : (p:ℝ)^(-(Dr/(nr-1)) + nr*vr/(nr-1))
      = (p:ℝ)^(-(Dr/(nr-1))) * (p:ℝ)^(nr*vr/(nr-1)) := Real.rpow_add hp0 _ _
  have step3 : (p:ℝ)^(nr*vr/(nr-1)) ≤ nr^(nr/(nr-1)) := by
    have hmul : nr*vr/(nr-1) = vr * (nr/(nr-1)) := by ring
    rw [hmul, Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [hvr, Real.rpow_natCast]
    calc (p:ℝ)^v = ((p^v : ℕ):ℝ) := by push_cast; ring
      _ ≤ (n:ℝ) := by exact_mod_cast hv
  calc ((n:ℝ)-1) * (p:ℝ)^(-te)
      ≤ ((n:ℝ)-1) * ((p:ℝ)^(-(Dr/(nr-1))) * (p:ℝ)^(nr*vr/(nr-1))) := by
          apply mul_le_mul_of_nonneg_left (by rw [← step2]; exact step1) (by linarith)
    _ ≤ ((n:ℝ)-1) * ((p:ℝ)^(-(Dr/(nr-1))) * nr^(nr/(nr-1))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply mul_le_mul_of_nonneg_left step3 (by positivity)
    _ = ((n:ℝ)-1) * nr^(nr/(nr-1)) * (p:ℝ)^(-(Dr/(nr-1))) := by ring

/-- The √N absorption: `M ≳ √N/(2√A)` and `D ≳ M/(2s+1)` push both leg exponents above
`c4'·√N` once `N ≥ N₀` (encoded by `hN6`, `hNabsN`). -/
private lemma final_absorb (A s2 L M D N n : ℕ) (cT sA : ℝ)
    (hA : 1 ≤ A) (hs2 : 1 ≤ s2) (hn : 2 ≤ n)
    (hcT : 0 < cT) (hsApos : 0 < sA) (hsA2 : sA^2 = (A:ℝ))
    (hMG : N ≤ 2*A*M^2 + 3*A) (hDG : 2*M ≤ s2*D + s2 + 2*L)
    (hN6 : 6*A ≤ N) (hNabsN : 4*A*(s2+2*L)^2 ≤ N)
    (c4' : ℝ) (hc4T : c4' ≤ cT/(2*sA)) (hc4D : c4' ≤ 1/(2*sA*s2*((n:ℝ)-1))) :
    (c4' * Real.sqrt N ≤ cT * M) ∧ (c4' * Real.sqrt N ≤ (D:ℝ)/((n:ℝ)-1)) := by
  have hn1pos : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs2R : (0:ℝ) < (s2:ℝ) := by exact_mod_cast hs2
  have h4AM : (N:ℝ) ≤ 4*A*M^2 := by
    have h1 : (N:ℝ) ≤ 2*A*M^2 + 3*A := by exact_mod_cast hMG
    have h2 : (6*A:ℝ) ≤ N := by exact_mod_cast hN6
    nlinarith [h1, h2]
  have hMlow : Real.sqrt N ≤ 2*sA*M := by
    have hsq : (2*sA*(M:ℝ))^2 = 4*A*M^2 := by
      rw [show (2*sA*(M:ℝ))^2 = 4*sA^2*(M:ℝ)^2 by ring, hsA2]
    have hle : (N:ℝ) ≤ (2*sA*M)^2 := by rw [hsq]; exact h4AM
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at this
  have htall : c4' * Real.sqrt N ≤ cT * M := by
    calc c4' * Real.sqrt N ≤ (cT/(2*sA)) * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hc4T (Real.sqrt_nonneg _)
      _ = cT * (Real.sqrt N / (2*sA)) := by ring
      _ ≤ cT * (M:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hcT)
          rw [div_le_iff₀ (by positivity)]
          calc Real.sqrt N ≤ 2*sA*M := hMlow
            _ = M * (2*sA) := by ring
  refine ⟨htall, ?_⟩
  have e3 : 2*sA*((s2:ℝ)+2*L) ≤ Real.sqrt N := by
    have hsq : (2*sA*((s2:ℝ)+2*L))^2 = 4*A*((s2:ℝ)+2*L)^2 := by
      rw [show (2*sA*((s2:ℝ)+2*L))^2 = 4*sA^2*((s2:ℝ)+2*L)^2 by ring, hsA2]
    have hNle : (4*A*((s2:ℝ)+2*L)^2) ≤ N := by
      have : ((4*A*(s2+2*L)^2 : ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hNabsN
      push_cast at this; linarith [this]
    have hle : (2*sA*((s2:ℝ)+2*L))^2 ≤ (N:ℝ) := by rw [hsq]; exact hNle
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at this
  have hDGr : 2*(M:ℝ) ≤ s2*D + s2 + 2*L := by exact_mod_cast hDG
  have hDlow : Real.sqrt N ≤ 2*sA*s2*D := by
    nlinarith [hMlow, e3, hDGr, hsApos]
  have hX : (0:ℝ) < 2*sA*(s2:ℝ)*((n:ℝ)-1) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hsApos) hs2R) hn1pos
  calc c4' * Real.sqrt N ≤ (1/(2*sA*(s2:ℝ)*((n:ℝ)-1))) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hc4D (Real.sqrt_nonneg _)
    _ = Real.sqrt N / (2*sA*(s2:ℝ)*((n:ℝ)-1)) := by ring
    _ ≤ (D:ℝ)/((n:ℝ)-1) := by
        rw [div_le_div_iff₀ hX hn1pos]
        nlinarith [hDlow, hn1pos]

/-- DEEP LEG: the mass of the deep event decays like `p^{−D/(n−1)}`, with a p-free
constant. Uses XC.3 (`x1bReduction`), the context's `vdisc_le_tail`, and XF.7
(`tailCountBound`) with the `offset_absorb` upgrade. -/
private lemma deepLegBound {n : ℕ} (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (p : ℕ) [Fact p.Prime] (M D : ℕ)
    (hD : (2 * K.s + 1) * D + 2 * Nat.log 2 n ≤ 2 * M) :
    ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
      ≤ ((n:ℝ) - 1) * (n:ℝ) ^ ((n:ℝ) / ((n:ℝ) - 1)) * (p:ℝ) ^ (-((D:ℝ) / ((n:ℝ) - 1))) := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp0q : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
  -- STEP 1: pointwise inclusion into the level-D vdisc-tail set
  have hincl : DeepEvent (X.ctx p) M ⊆ { f | D ≤ vdisc f ∨ f ∈ discZero n p } := by
    intro f hf
    obtain ⟨b, hMb⟩ := hf
    change D ≤ vdisc f ∨ f ∈ discZero n p
    by_cases hd : f ∈ discZero n p
    · exact Or.inr hd
    · refine Or.inl ?_
      have hstr : (X.gmn p).inStratum f ((X.ctx p).hist b) := X.gmnLink p f b
      have hred := x1bReduction X K AL WC p f ((X.ctx p).hist b) hstr hd ((X.ctx p).wf b) (by omega)
      have hkey : (2 * K.s + 1) * D ≤ (2 * K.s + 1) * vdisc f := by omega
      exact Nat.le_of_mul_le_mul_left hkey (by omega)
  -- STEP 2–4: monotonicity, vdisc_le_tail, XF.7 combine (ℚ)
  have hchain : (X.ctx p).frac (DeepEvent (X.ctx p) M) ≤ (tailCount p n D : ℚ) / (p:ℚ)^(n*D) :=
    le_trans ((X.ctx p).frac_mono _ _ hincl) ((X.ctx p).vdisc_le_tail D)
  have h3 := tailCountBound p n D hn
  have hQ : (X.ctx p).frac (DeepEvent (X.ctx p) M)
      ≤ ((n:ℚ) - 1) * (p:ℚ)^(-(tailExp p n D)) := by
    refine le_trans hchain ?_
    have hpne : (p:ℚ) ≠ 0 := hp0q.ne'
    rw [div_le_iff₀ (by positivity)]
    have e1 : ((n:ℚ)-1) * (p:ℚ)^(-(tailExp p n D)) * (p:ℚ)^(n*D)
        = ((n:ℚ)-1) * (p:ℚ)^((n*D:ℕ):ℤ) * (p:ℚ)^(-(tailExp p n D)) := by
      rw [zpow_natCast]; ring
    rw [e1]
    calc (tailCount p n D : ℚ)
        = (tailCount p n D : ℚ) * (p:ℚ)^(tailExp p n D) * (p:ℚ)^(-(tailExp p n D)) := by
            rw [mul_assoc, ← zpow_add₀ hpne, add_neg_cancel, zpow_zero, mul_one]
      _ ≤ ((n:ℚ)-1) * (p:ℚ)^((n*D:ℕ):ℤ) * (p:ℚ)^(-(tailExp p n D)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
  -- cast to ℝ
  have hQR : ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
      ≤ ((n:ℝ) - 1) * (p:ℝ)^(-(tailExp p n D)) := by
    have hcast : (((n:ℚ)-1) * (p:ℚ)^(-(tailExp p n D)) : ℝ)
        = ((n:ℝ)-1) * (p:ℝ)^(-(tailExp p n D)) := by push_cast; ring
    calc ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
        ≤ (((n:ℚ)-1) * (p:ℚ)^(-(tailExp p n D)) : ℝ) := by exact_mod_cast hQ
      _ = ((n:ℝ)-1) * (p:ℝ)^(-(tailExp p n D)) := hcast
  -- STEP 5: the offset absorption
  refine le_trans hQR ?_
  have hv : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hte : ((D:ℚ) - n * (padicValNat p n)) / ((n:ℚ) - 1) ≤ ((tailExp p n D : ℤ) : ℚ) := by
    have := Int.le_ceil (((D:ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ))
    -- unfold tailExp
    have heq : ((D:ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)
        = ((D:ℚ) - n * (padicValNat p n)) / ((n:ℚ) - 1) := by push_cast; ring
    rw [heq] at this
    simpa [tailExp] using this
  exact offset_absorb p n D hn (padicValNat p n) hv hp1 (tailExp p n D) hte

theorem envelopeSqrt (n : ℕ) (hn : 2 ≤ n) (K : XConsts n) :
    ∃ N₀ : ℕ, ∃ c3' c4' : ℝ, 0 < c3' ∧ 0 < c4' ∧
      ∀ (X : XFamily n), X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N →
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3' * (p : ℝ) ^ (-(c4' * Real.sqrt N)) := by
  -- (n,K)-only constants (bound BEFORE any X or p — the D9 discipline)
  set A : ℕ := ⌈K.c0 + K.ccap⌉₊ + 1 with hA_def
  set L : ℕ := Nat.log 2 n with hL_def
  set s2 : ℕ := 2 * K.s + 1 with hs2_def
  set sA : ℝ := Real.sqrt A with hsA_def
  have hApos : 1 ≤ A := by rw [hA_def]; omega
  have hs2pos : 1 ≤ s2 := by rw [hs2_def]; omega
  have hAR0 : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hsA2 : sA^2 = (A:ℝ) := by rw [hsA_def]; exact Real.sq_sqrt hAR0.le
  have hsApos : 0 < sA := by rw [hsA_def]; exact Real.sqrt_pos.mpr hAR0
  have hn1R : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- witnesses
  set N₀ : ℕ := 6*A + 4*A*(s2+2*L)^2 + A*L^2 + (A+1) with hN0_def
  set c3' : ℝ := ((n:ℝ)-1)*(n:ℝ)^((n:ℝ)/((n:ℝ)-1)) + K.CT with hc3_def
  set c4' : ℝ := min (K.cT/(2*sA)) (1/(2*sA*(s2:ℝ)*((n:ℝ)-1))) with hc4_def
  have hCdeep_nn : (0:ℝ) ≤ ((n:ℝ)-1)*(n:ℝ)^((n:ℝ)/((n:ℝ)-1)) :=
    mul_nonneg hn1R.le (Real.rpow_nonneg (by positivity) _)
  have hc3pos : 0 < c3' := by
    rw [hc3_def]
    have h2 : (0:ℝ) < (n:ℝ)^((n:ℝ)/((n:ℝ)-1)) := Real.rpow_pos_of_pos (by positivity) _
    have := mul_pos hn1R h2
    linarith [K.CTpos]
  have hc4pos : 0 < c4' := by
    rw [hc4_def]
    refine lt_min (div_pos K.cTpos (mul_pos (by norm_num) hsApos)) ?_
    exact div_pos (by norm_num)
      (mul_pos (mul_pos (mul_pos (by norm_num) hsApos) (by exact_mod_cast hs2pos)) hn1R)
  refine ⟨N₀, c3', c4', hc3pos, hc4pos, ?_⟩
  intro X BR AF CP AL WC TL NS R p _inst N hN
  -- per-N objects
  set q : ℕ := (N - A - 1)/A with hq_def
  set M : ℕ := Nat.sqrt q with hM_def
  set D : ℕ := (2*M - 2*L)/s2 with hD_def
  -- unpack the N₀ threshold
  have hN6 : 6*A ≤ N := by rw [hN0_def] at hN; omega
  have hNabs : 4*A*(s2+2*L)^2 ≤ N := by rw [hN0_def] at hN; omega
  have hNA1 : A + 1 ≤ N := by rw [hN0_def] at hN; omega
  have hNbig : A*L^2 + A + 1 ≤ N := by rw [hN0_def] at hN; omega
  -- nat facts on M
  have hC1nat : A * M^2 + A + 1 ≤ N := by
    have hMq : M^2 ≤ q := by rw [hM_def]; exact Nat.sqrt_le' q
    have hqA : q * A ≤ N - A - 1 := Nat.div_mul_le_self _ _
    have hAM : A * M^2 ≤ A * q := Nat.mul_le_mul_left A hMq
    have hcomm : A * q = q * A := Nat.mul_comm _ _
    omega
  have hMGnat : N ≤ 2*A*M^2 + 3*A := by
    have hlt : q < (M+1)*(M+1) := by rw [hM_def]; exact Nat.lt_succ_sqrt q
    have h2m : 2*M ≤ M^2 + 1 := by nlinarith [Nat.zero_le M]
    have hq1 : q ≤ 2*M^2 + 1 := by nlinarith [hlt, h2m]
    have hdm := Nat.div_add_mod (N-A-1) A
    rw [← hq_def] at hdm
    have hmod : (N-A-1) % A < A := Nat.mod_lt _ (by omega)
    have hNq : N ≤ A*q + 2*A := by omega
    have hAq : A * q ≤ A * (2*M^2 + 1) := Nat.mul_le_mul_left A hq1
    have hexp : A * (2*M^2 + 1) = 2*A*M^2 + A := by ring
    omega
  have hLMnat : L ≤ M := by
    rw [hM_def]
    have h1 : A * L^2 ≤ N - A - 1 := by omega
    have h2 : (A * L^2)/A ≤ (N-A-1)/A := Nat.div_le_div_right h1
    have h3 : (A * L^2)/A = L^2 := by rw [Nat.mul_div_cancel_left _ (by omega)]
    rw [h3] at h2
    rw [Nat.le_sqrt]
    calc L*L = L^2 := by ring
      _ ≤ (N-A-1)/A := h2
  have hDupper : s2 * D + 2*L ≤ 2*M := by
    rw [hD_def]
    have h1 : s2 * ((2*M-2*L)/s2) ≤ 2*M - 2*L := by
      have := Nat.div_mul_le_self (2*M-2*L) s2
      rw [Nat.mul_comm] at this; exact this
    omega
  have hDG : 2*M ≤ s2 * D + s2 + 2*L := by
    rw [hD_def]
    have hdm := Nat.div_add_mod (2*M-2*L) s2
    have hmod : (2*M-2*L) % s2 < s2 := Nat.mod_lt _ (by omega)
    omega
  -- ℚ version of the M-choice bound: (c0+ccap)·M² ≤ N−1−ccap
  have hAc0cc : (K.c0 + K.ccap : ℚ) ≤ (A:ℚ) := by
    rw [hA_def]; push_cast
    have := Nat.le_ceil (K.c0 + K.ccap)
    linarith
  have hAccap : (K.ccap : ℚ) ≤ (A:ℚ) := le_trans (by linarith [K.c0nonneg]) hAc0cc
  have hC1q : (K.c0 + K.ccap) * (M:ℚ)^2 ≤ (N:ℚ) - 1 - K.ccap := by
    have hnat : (A:ℚ)*(M:ℚ)^2 + A + 1 ≤ (N:ℚ) := by exact_mod_cast hC1nat
    have hM2nn : (0:ℚ) ≤ (M:ℚ)^2 := by positivity
    calc (K.c0 + K.ccap)*(M:ℚ)^2 ≤ (A:ℚ)*(M:ℚ)^2 := mul_le_mul_of_nonneg_right hAc0cc hM2nn
      _ ≤ (N:ℚ) - A - 1 := by linarith
      _ ≤ (N:ℚ) - 1 - K.ccap := by linarith [hAccap]
  -- prime facts
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  -- POINTWISE: the witness-branch piece lands in DeepEvent M ∪ TallEvent M
  have hpw : ∀ f : MonicBox n p,
      (∃ b : (X.ctx p).Branch f, IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
        N < (X.ctx p).threshold b + capHB (X.ctx p) b) →
      f ∈ DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M := by
    intro f hw
    obtain ⟨b, hleaf, hnsfree, hlt⟩ := hw
    have hfp : FourthPieceB (X.ctx p) b := ⟨Or.inl hleaf, hnsfree⟩
    have hdich := x2hypAssembled X K AF CP p f b hfp N hlt
    have hcc_nn : (0:ℚ) ≤ K.c0 + K.ccap := add_nonneg K.c0nonneg K.ccapnonneg
    rcases hdich with hLcase | hRcase
    · -- deep
      refine Or.inl ?_
      have hlt2 : (K.c0+K.ccap)*(M:ℚ)^2
          < (K.c0+K.ccap)*((dTotal ((X.ctx p).hist b)+1 : ℕ):ℚ)^2 := by
        have hcast : ((dTotal ((X.ctx p).hist b)+1:ℕ):ℚ) = (dTotal ((X.ctx p).hist b):ℚ)+1 := by
          push_cast; ring
        rw [hcast]; exact lt_of_le_of_lt hC1q hLcase
      have hMlt : M < dTotal ((X.ctx p).hist b) + 1 := nat_lt_of_mul_sq_lt hcc_nn hlt2
      exact ⟨b, by omega⟩
    · -- tall
      refine Or.inr ?_
      have hlt2 : (K.c0+K.ccap)*(M:ℚ)^2
          < (K.c0+K.ccap)*(maxH ((X.ctx p).hist b):ℚ)^2 := lt_of_le_of_lt hC1q hRcase
      have hMlt : M < maxH ((X.ctx p).hist b) := nat_lt_of_mul_sq_lt hcc_nn hlt2
      obtain ⟨ν, hν, hνh⟩ := maxH_gt _ M hMlt
      exact ⟨b, ν, hν, le_of_lt hνh⟩
  -- BRIDGE: frac(Undec N) ≤ frac(Deep M) + frac(Tall M)
  obtain ⟨_, hnull⟩ := BR p N
  have hsub : (X.ctx p).Undec N ⊆
      (DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M) ∪
      { f | f ∈ (X.ctx p).Undec N ∧ ¬ ∃ b : (X.ctx p).Branch f,
          IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
            N < (X.ctx p).threshold b + capHB (X.ctx p) b } := by
    intro f hf
    by_cases hw : ∃ b : (X.ctx p).Branch f,
        IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
          N < (X.ctx p).threshold b + capHB (X.ctx p) b
    · exact Or.inl (hpw f hw)
    · exact Or.inr ⟨hf, hw⟩
  have hfrac : (X.ctx p).frac ((X.ctx p).Undec N)
      ≤ (X.ctx p).frac (DeepEvent (X.ctx p) M) + (X.ctx p).frac (TallEvent (X.ctx p) M) := by
    calc (X.ctx p).frac ((X.ctx p).Undec N)
        ≤ (X.ctx p).frac ((DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M) ∪
            { f | f ∈ (X.ctx p).Undec N ∧ ¬ ∃ b : (X.ctx p).Branch f,
                IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
                  N < (X.ctx p).threshold b + capHB (X.ctx p) b }) :=
          (X.ctx p).frac_mono _ _ hsub
      _ ≤ (X.ctx p).frac (DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M) +
            (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧ ¬ ∃ b : (X.ctx p).Branch f,
                IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
                  N < (X.ctx p).threshold b + capHB (X.ctx p) b } :=
          (X.ctx p).frac_union_le _ _
      _ = (X.ctx p).frac (DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M) + 0 := by rw [hnull]
      _ = (X.ctx p).frac (DeepEvent (X.ctx p) M ∪ TallEvent (X.ctx p) M) := by ring
      _ ≤ (X.ctx p).frac (DeepEvent (X.ctx p) M) + (X.ctx p).frac (TallEvent (X.ctx p) M) :=
          (X.ctx p).frac_union_le _ _
  have hfracR : ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ)
      ≤ ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
        + ((X.ctx p).frac (TallEvent (X.ctx p) M) : ℝ) := by exact_mod_cast hfrac
  -- the two leg exponent comparisons
  have habs := final_absorb A s2 L M D N n K.cT sA hApos hs2pos hn K.cTpos hsApos hsA2
    hMGnat hDG hN6 hNabs c4' (by rw [hc4_def]; exact min_le_left _ _)
    (by rw [hc4_def]; exact min_le_right _ _)
  obtain ⟨htallcmp, hdeepcmp⟩ := habs
  -- the two leg bounds, funneled to the target base E := p^(-(c4'·√N))
  set E : ℝ := (p:ℝ)^(-(c4' * Real.sqrt N)) with hE_def
  have hDupper' : (2 * K.s + 1) * D + 2 * Nat.log 2 n ≤ 2 * M := hDupper
  have hdeepB : ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
      ≤ ((n:ℝ)-1)*(n:ℝ)^((n:ℝ)/((n:ℝ)-1)) * E := by
    refine le_trans (deepLegBound hn X K AL WC p M D hDupper') ?_
    apply mul_le_mul_of_nonneg_left _ hCdeep_nn
    rw [hE_def]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    linarith [hdeepcmp]
  have htallB : ((X.ctx p).frac (TallEvent (X.ctx p) M) : ℝ) ≤ K.CT * E := by
    refine le_trans (TL p M) ?_
    rw [hE_def]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt K.CTpos)
    apply Real.rpow_le_rpow_of_exponent_le hp1
    linarith [htallcmp]
  calc ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ)
      ≤ ((X.ctx p).frac (DeepEvent (X.ctx p) M) : ℝ)
        + ((X.ctx p).frac (TallEvent (X.ctx p) M) : ℝ) := hfracR
    _ ≤ (((n:ℝ)-1)*(n:ℝ)^((n:ℝ)/((n:ℝ)-1)) * E) + (K.CT * E) := add_le_add hdeepB htallB
    _ = c3' * E := by rw [hc3_def]; ring

end LeanUrat.MovesX
