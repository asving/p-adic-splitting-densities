/-
Unit HK-57  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton;
NEW unit at REVISION 2, split out of HK-19, finding 16)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-57.

INFORMAL STATEMENT (blueprint): "SideReads at read 0, clauses (iii)–(vi):
(iii) anchor/ord at ν₀ (fq-adic development, hOrd μ = 1); (iv) LandingKey ν₀ Φ̂ (the
recorded lift); (v) polOM/canonRoot (policy values, rfl-grade); (vi) Fact-B
uniqueness."  deps: HK-19.

E-PHASE SHAPE: literal conjunct types of `SideReads HK18.ν₀gate HK19.Bdev0 5 U31.fq`
(the read-0 Φnext is the recorded child key = the landing key Φ̂ = `U31.fq`, pinned by
`ReadsOf`'s interior clause), so HK-22 reassembles ⟨HK-19 (i)/(ii), HK-57 (iii)–(vi)⟩.

PROOF SKETCH (P-phase):
(iii) θ fgate = 8·(2q₁² + q₁ + 2) with q₁ = X² + X + 1, so bw fgate = 3 and
  bR fgate = toLaurent(X² + X + 1) = T 0 · toLaurent ψ₂: `HasAnchorK … 0 ψ₂` at a = 0;
  ord_ψ₂ ψ₂ = 1 (U31's private `ord_ψ₂`, de-privatize or reprove).
(iv) `LandingKey ν₀gate fq` — ν₀gate is non-recentering (root): `IsNodeLift ν₀gate fq`
  with the SAME realizer witness as U31's `landingKey_ν₀` (tt₀ = C 4 at weight
  2 = h·(g−0), tt₁ = C 2 at weight 1, positions T 0 at t = 0; fq = X² + tt₁·X + tt₀)
  — ν₀gate and U31.ν₀ share (ψ, g, e, h, t), and their σ's (bStageP after the ratified
  2026-07-30 re-key vs. U31.bStage) are byte-identical on every field these reads
  touch (w, R, Φ, K; the wPrev positions are scaled by t = 0), so the proof transports.
(v) lift = 0 = (polOM 2 F4).liftOf ν₀gate (no `RecenterLiftSpec` realizer exists at the
  base stage — U31's clause-(v) argument verbatim: bR never vanishes on nonzero input);
  canonRoot ν₀gate = canonRoot U31.ν₀ = r₀ (canonRoot reads (σ, ψ) only — same data).
(vi) VERTEX READ-OFF: the window sum IS fgate (HK-19's `Bdev0_dev`); any fq-adic
  development Bh of fgate has Bh 1 = C 2 by Fact-B uniqueness (`L0_FactB_unique`
  against the canonical development (C 16, C 2, 1) — fgate = fq² + 2·fq + 16 is
  literally in that shape); digPrime zbar (C 2) = eval of bR(C 2) = 1; and
  vtx ν₀gate = z̄^(a−μ·m̂)·((ψ₂/ₘψ₂)%ₘψ₂)(z̄) = z̄⁰·1 = 1 (a = 0, t = 0 ⟹ m̂ = 0)
  — U31's clause-(vi) N-4 gate-re-run proof at the new constants.
Difficulty hard-fable ~70 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK19

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK57

open HK18 HK19

/-- The 2-adic normal form of `θ fgate` (P-phase local): `θ fgate = 8·(2q₁² + q₁ + 2)`
with cofactor reducing to `ψ₂ = z² + z + 1` mod 2 — the anchor's supply. -/
lemma NF_θ_fgate : U31.NF (U31.θ fgate) 3
    (Polynomial.C 2 * U31.q₁ ^ 2 + U31.q₁ + Polynomial.C 2) := by
  constructor
  · have hθfq : U31.θ U31.fq = (Polynomial.C 2) ^ 2 * U31.q₁ := HK13R.NF_θ_fq.1
    show U31.θ (U31.fq ^ 2 + Polynomial.C 2 * U31.fq + Polynomial.C 16) = _
    rw [map_add, map_add, map_pow, map_mul, hθfq, U31.θ_C, U31.θ_C]
    have h16 : (Polynomial.C (16 : ℤ_[2])) = (Polynomial.C (2 : ℤ_[2])) ^ 4 := by
      rw [← C_pow]
      norm_num
    rw [h16]
    ring
  · have hmap : (Polynomial.C 2 * U31.q₁ ^ 2 + U31.q₁ + Polynomial.C 2).map U31.ρ
        = X ^ 2 + X + 1 := by
      rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, HK13R.ρ_two, HK13R.map_ρ_q₁, Polynomial.C_0, zero_mul, zero_add,
        add_zero]
    rw [hmap]
    exact HK13R.XXone_ne_zero

/-- SideReads clause (iii), ANCHOR, at (ν₀gate, Bdev0, 5): the recorded (a, Ranch) =
(0, ψ₂) anchor the frame residual of the window sum (= fgate). Byte-copy of the first
(iii) conjunct of `SideReads`. -/
theorem sideReads0_anchor :
    HasAnchorK (ν₀gate.σ.R (∑ j ∈ Finset.range 5, Bdev0 j * ν₀gate.σ.Φ ^ j))
      ν₀gate.a ν₀gate.Ranch := by
  show HasAnchorK (U31.bR (∑ j ∈ Finset.range 5, Bdev0 j * (X : Polynomial ℤ_[2]) ^ j))
    0 U31.ψ₂
  rw [← Bdev0_dev.2.2]
  constructor
  · rw [HK13R.ψ₂_coeff_zero]
    exact one_ne_zero
  · have hmap : (Polynomial.C 2 * U31.q₁ ^ 2 + U31.q₁ + Polynomial.C 2).map U31.ρ
        = X ^ 2 + X + 1 := by
      rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, HK13R.ρ_two, HK13R.map_ρ_q₁, Polynomial.C_0, zero_mul, zero_add,
        add_zero]
    rw [HK13R.bR_eq NF_θ_fgate, hmap, LaurentPolynomial.T_zero, one_mul]
    rfl

/-- SideReads clause (iii), ψ-ORDER, at ν₀gate: ord_ψ₂ (Ranch = ψ₂) = μ = 1. Byte-copy
of the second (iii) conjunct of `SideReads`. -/
theorem sideReads0_ord : OrdPsiPoly ν₀gate.ψ ν₀gate.Ranch ν₀gate.μ :=
  HK13R.ord_ψ₂

/-- SideReads clause (iv), DESCENT WITNESS, at read 0: the recorded landing produces the
designated next key Φ̂ = fq — `LandingKey ν₀gate fq` (the recorded lift; U31's
`landingKey_ν₀` witness transports verbatim). -/
theorem sideReads0_landing : LandingKey ν₀gate U31.fq := by
  constructor
  · intro h
    exact ReadSpecies.noConfusion h
  · intro _
    refine ⟨fun k => if k = 0 then Polynomial.C 4 else if k = 1 then Polynomial.C 2 else 0,
      ?_, ?_, ?_⟩
    · intro k hk
      match k with
      | 0 =>
          have hk' : U31.ψ₂.coeff 0 = 0 := hk
          rw [HK13R.ψ₂_coeff_zero] at hk'
          exact absurd hk' one_ne_zero
      | 1 =>
          have hk' : U31.ψ₂.coeff 1 = 0 := hk
          rw [HK13R.ψ₂_coeff_one] at hk'
          exact absurd hk' one_ne_zero
      | (n + 2) => rfl
    · intro k hk hne
      have hk2 : k < 2 := hk
      interval_cases k
      · refine ⟨?_, HK13R.inC_C, ?_, ?_⟩
        · show (Polynomial.C (4 : ℤ_[2])) ≠ 0
          exact Polynomial.C_ne_zero.mpr (by norm_num)
        · show U31.bw (Polynomial.C 4) = ((1 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
          rw [bw_C4]
          norm_num
        · have hgoal : U31.bR (Polynomial.C 4) = (LaurentPolynomial.C (U31.ψ₂.coeff 0)) *
              (LaurentPolynomial.T (- (0 : ℤ) * gaussVal (Polynomial.C (4 : ℤ_[2]))) :
                LaurentPolynomial ↥U31.K2) := by
            rw [HK13R.bR_const (by norm_num : (4 : ℤ_[2]) ≠ 0), HK13R.ψ₂_coeff_zero,
              map_one, neg_zero, zero_mul, LaurentPolynomial.T_zero, one_mul]
          exact hgoal
      · refine ⟨?_, HK13R.inC_C, ?_, ?_⟩
        · show (Polynomial.C (2 : ℤ_[2])) ≠ 0
          exact Polynomial.C_ne_zero.mpr HK13R.two_ne_zero'
        · show U31.bw (Polynomial.C 2) = ((1 : ℕ) : ℤ) * (((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
          rw [HK13R.bw_C2]
          norm_num
        · have hgoal : U31.bR (Polynomial.C 2) = (LaurentPolynomial.C (U31.ψ₂.coeff 1)) *
              (LaurentPolynomial.T (- (0 : ℤ) * gaussVal (Polynomial.C (2 : ℤ_[2]))) :
                LaurentPolynomial ↥U31.K2) := by
            rw [HK13R.bR_C2, HK13R.ψ₂_coeff_one, map_one, neg_zero, zero_mul,
              LaurentPolynomial.T_zero, one_mul]
          exact hgoal
    · show U31.fq = X ^ (1 * 2) + ∑ k ∈ Finset.range 2,
        (if k = 0 then Polynomial.C 4 else if k = 1 then Polynomial.C 2 else 0) * X ^ (1 * k)
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [U31.fq]
      ring

/-- SideReads clause (v), first leg: ν₀gate carries the polOM lift (= 0; no recentering
realizer exists at the base stage). -/
theorem sideReads0_polOM : ν₀gate.lift = (polOM 2 F4).liftOf ν₀gate := by
  have hno : ¬ ∃ tL, RecenterLiftSpec ν₀gate tL := by
    rintro ⟨tL, _, htne, _, hR⟩
    have hzero : (LaurentPolynomial.C ((0 : ↥U31.K2))) *
        (LaurentPolynomial.T (0 : ℤ) : LaurentPolynomial ↥U31.K2) = 0 := by
      rw [map_zero, zero_mul]
    exact HK13R.bR_ne tL htne (hR.trans hzero)
  have hlift : (polOM 2 F4).liftOf ν₀gate = 0 := by
    classical
    show (if h : ∃ tL, RecenterLiftSpec ν₀gate tL then h.choose else 0) = 0
    rw [dif_neg hno]
  rw [hlift]
  rfl

/-- SideReads clause (v), second leg: the recorded residue root is THE canonical one
(canonRoot reads (σ, ψ) only, so it agrees with U31's r₀ pinning). -/
theorem sideReads0_canonRoot : ((ν₀gate.zbar : F4ˣ) : F4) = canonRoot ν₀gate := rfl

/-- SideReads clause (vi), VERTEX READ-OFF, at (ν₀gate, Bdev0, 5, Φnext = fq): in ANY
fq-adic development of the window sum (= fgate), the vertex-slot (μ = 1) digit is the
recorded transported vertex value vtx ν₀gate (= 1). Fact-B uniqueness forces
Bh 1 = C 2. Byte-copy of the (vi) conjunct of `SideReads`. -/
theorem sideReads0_vertex :
    ∀ (Bh : ℕ → Polynomial ℤ_[2]) (Nh : ℕ),
      IsDevelopment U31.fq (∑ j ∈ Finset.range 5, Bdev0 j * ν₀gate.σ.Φ ^ j) Bh Nh →
      ν₀gate.σ.digPrime ν₀gate.zbar (Bh ν₀gate.μ) = ν₀gate.vtx := by
  intro Bh Nh hdev
  have hdev' : IsDevelopment U31.fq fgate Bh Nh := by
    have h2 : IsDevelopment U31.fq
        (∑ j ∈ Finset.range 5, Bdev0 j * (X : Polynomial ℤ_[2]) ^ j) Bh Nh := hdev
    rwa [← Bdev0_dev.2.2] at h2
  have hfq_deg : U31.fq.degree = 2 := by
    rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
    rfl
  have hcanon : IsDevelopment U31.fq fgate
      (fun j => if j = 0 then Polynomial.C 16 else if j = 1 then Polynomial.C 2
        else if j = 2 then 1 else 0) 3 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      · rw [hfq_deg]
        exact lt_of_le_of_lt degree_C_le (by norm_num)
      · rw [hfq_deg]
        exact lt_of_le_of_lt degree_C_le (by norm_num)
      · rw [hfq_deg]
        exact lt_of_le_of_lt degree_one_le (by norm_num)
      · rw [degree_zero, hfq_deg]
        decide
    · intro j hj
      dsimp only
      split_ifs with h1 h2 h3
      · exact absurd h1 (by omega)
      · exact absurd h2 (by omega)
      · exact absurd h3 (by omega)
      · rfl
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [fgate]
      ring
  have hBh1 : Bh 1 = Polynomial.C 2 := by
    have h := L0_FactB_unique U31.fq U31.fq_monic fgate hdev' hcanon 1
    simpa using h
  have hψ₂_deg : U31.ψ₂.degree = 2 := by
    rw [Polynomial.degree_eq_natDegree HK13R.ψ₂_ne_zero, HK13R.ψ₂_natDegree]
    rfl
  have hvp : ν₀gate.vtxPoly = 1 := by
    have hdiv : U31.ψ₂ /ₘ U31.ψ₂ = 1 := by
      have h := Polynomial.mul_divByMonic_cancel_left (1 : Polynomial ↥U31.K2)
        HK13R.ψ₂_monic
      rwa [mul_one] at h
    have hmod : (1 : Polynomial ↥U31.K2) %ₘ U31.ψ₂ = 1 := by
      refine (Polynomial.modByMonic_eq_self_iff HK13R.ψ₂_monic).mpr ?_
      rw [Polynomial.degree_one, hψ₂_deg]
      decide
    have h0 : ν₀gate.vtxPoly = (U31.ψ₂ /ₘ U31.ψ₂ ^ 1) %ₘ U31.ψ₂ := rfl
    rw [h0, pow_one, hdiv, hmod]
    rfl
  have hexp : ν₀gate.a - (ν₀gate.μ : ℤ) * ν₀gate.mhat = 0 := by
    have hmh : ν₀gate.mhat = 0 := by
      show -ν₀gate.t * (ν₀gate.h : ℤ) * (ν₀gate.g : ℤ) = 0
      have ht : ν₀gate.t = 0 := rfl
      rw [ht]
      ring
    have ha : ν₀gate.a = 0 := rfl
    rw [ha, hmh, mul_zero, sub_zero]
  have hvtx : ν₀gate.vtx = 1 := by
    unfold Node.vtx
    rw [hvp, Polynomial.eval₂_one, mul_one, hexp, zpow_zero, Units.val_one]
  show ν₀gate.σ.digPrime ν₀gate.zbar (Bh 1) = ν₀gate.vtx
  rw [hBh1, hvtx]
  show LaurentPolynomial.eval₂ U31.K2.subtype ν₀gate.zbar (U31.bR (Polynomial.C 2)) = 1
  rw [HK13R.bR_C2]
  exact map_one _

end HK57

end LeanUrat.MovesJ
