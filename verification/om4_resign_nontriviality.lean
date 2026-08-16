import Leanspec.ChapE
import Leanspec.ChapD
/-!
# A-E.2 / A-D.2 non-triviality certificates: the RE-SIGNED Display-A carriers are NOT
# trivially provable — the old vacuity witnesses (and their whole genre) fail

Companion to `verification/om4_shadow_vacuity.lean` (which proves the pre-re-sign shadows
trivially, for every carrier/block).  This file certifies the OPPOSITE for the re-signed
forms, in the strongest machine-checkable sense: each re-signed carrier is **FALSE at a
concrete instance**, so no proof of `∀ …, Carrier …` of the vacuity-witness genre can
exist, and in particular the old witnesses (singleton self-block; fabricated one-side
interface; `⟨v, hv, 1⟩`) do not replay.

* **E-side, `(LB1)` (A-E.2):** `lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁` — over
  `O = ℤ`, key `X`, block `F = X² + X + 1`, a two-side trigger interface with unit class
  weights forces a monic-linear integer factorization of `X² + X + 1`, which does not
  exist.  The singleton self-block fails `hcount`/`hdegsum`; nothing else can succeed.
* **E-side, `(MP1)` (A-E.2):** `mp1_resigned_not_trivial : ¬ MP1Carrier C₂ B₂` — over
  `O = ℤ`, key `X²`, block `F = X⁴ − 5X² + 4`, recentering `Λ = 4` gives the recentered
  key `X² − 4 = (X−2)(X+2)`: the record's item-5 clause `hirr` (irreducibility of the
  peeled key) is FALSE — exactly the clause the fabricated interface never supplied.
* **D-side, `(H-VARTHETA-RES)` (A-D.2):** `hvarthetaRes_resigned_not_trivial` — exact
  height HOLDS at the instance (so the old trivializer
  `hvarthetaResVoided_of_exact_height` still fires for the VOIDED form —
  `voided_still_trivial_here` below), yet the re-signed sitewise carrier is FALSE: the
  ambient residue datum sends the `s = 2` ϑ-quotient to `−i ∈ ℂˣ`, not in `ℚ`'s image.

Footprint discipline: every theorem below must use Lean core only (`#print axioms` at the
end); the SlotCarrier/BlockData/RungInterface instances are REAL (no stub axiom enters).

Check from the repo root with:
    cd leanspec && lake env lean ../verification/om4_resign_nontriviality.lean
-/

open Polynomial

namespace OM4ResignCert

open LeanspecE

/-! ## Part 0 — a real `SlotCarrier` over `ℤ`: degree-graded heights (`hgt A = −deg A` on
nonzero `A`, `⊤` at `0`), leading-coefficient digits in `ℚ`.  Every carrier law is PROVED;
`Full` is empty so `(LIFT)` is vacuous (legitimate: `Full`'s finite-domain obligation is
the instances', E.10). -/

open scoped Classical in
/-- The degree-graded slot carrier over `ℤ` at key degree `D`, `(DEG-EF)` data `(e, f)`. -/
noncomputable def gradedCarrier (D e f : ℕ) (hD : 0 < D) (hef : D = e * f)
    (he : 1 ≤ e) (hf : 1 ≤ f) : SlotCarrier ℤ ℚ where
  D := D
  hD := hD
  eC := e
  fC := f
  hef := hef
  heC := he
  hfC := hf
  hgt := fun A => if A = 0 then ⊤ else (((-(A.natDegree : ℤ) : ℤ)) : WithTop ℤ)
  dig := fun A => (A.leadingCoeff : ℚ)
  hgt_zero := by simp
  dig_zero := by simp
  hgt_ne_top := by intro A hA _; simp [hA]
  dig_ne_zero := by
    intro A hA _
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hA
  hgt_add_ge := by
    intro A B
    by_cases hA : A = 0
    · simp [hA]
    by_cases hB : B = 0
    · simp [hB]
    by_cases hAB : A + B = 0
    · simp [hA, hB, hAB]
    · simp only [if_neg hA, if_neg hB, if_neg hAB]
      have h := Polynomial.natDegree_add_le A B
      rcases le_total A.natDegree B.natDegree with hle | hle
      · refine le_trans (min_le_right _ _) ?_
        exact_mod_cast (by omega : -(B.natDegree : ℤ) ≤ -((A + B).natDegree : ℤ))
      · refine le_trans (min_le_left _ _) ?_
        exact_mod_cast (by omega : -(A.natDegree : ℤ) ≤ -((A + B).natDegree : ℤ))
  hgt_add_eq := by
    intro A B hne
    by_cases hA : A = 0
    · simp [hA]
    by_cases hB : B = 0
    · simp [hB]
    · have hd : A.natDegree ≠ B.natDegree := by
        intro h; exact hne (by simp [if_neg hA, if_neg hB, h])
      have hAB : A + B ≠ 0 := by
        intro h
        have hBA : B = -A := eq_neg_of_add_eq_zero_right h
        exact hd (by rw [hBA, natDegree_neg])
      rcases Nat.lt_or_ge A.natDegree B.natDegree with hlt | hge
      · have h1 : (A + B).natDegree = B.natDegree :=
          Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
        simp only [if_neg hA, if_neg hB, if_neg hAB, h1, ← WithTop.coe_min]
        exact_mod_cast
          (by omega : -(B.natDegree : ℤ) = min (-(A.natDegree : ℤ)) (-(B.natDegree : ℤ)))
      · have hlt' : B.natDegree < A.natDegree := by omega
        have h1 : (A + B).natDegree = A.natDegree :=
          Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt'
        simp only [if_neg hA, if_neg hB, if_neg hAB, h1, ← WithTop.coe_min]
        exact_mod_cast
          (by omega : -(A.natDegree : ℤ) = min (-(A.natDegree : ℤ)) (-(B.natDegree : ℤ)))
  dig_add := by
    intro A B k hA hB hne
    have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
    have hB0 : B ≠ 0 := by intro h; rw [h] at hB; simp at hB
    rw [if_neg hA0] at hA
    rw [if_neg hB0] at hB
    have hdA : -(A.natDegree : ℤ) = k := by exact_mod_cast hA
    have hdB : -(B.natDegree : ℤ) = k := by exact_mod_cast hB
    have hd : B.natDegree = A.natDegree := by omega
    have hsum_ne : A.leadingCoeff + B.leadingCoeff ≠ 0 := by
      intro h
      apply hne
      show (A.leadingCoeff : ℚ) + (B.leadingCoeff : ℚ) = 0
      exact_mod_cast h
    have hcoeff : (A + B).coeff A.natDegree = A.leadingCoeff + B.leadingCoeff := by
      rw [Polynomial.coeff_add, Polynomial.leadingCoeff, Polynomial.leadingCoeff, hd]
    have hne0 : A + B ≠ 0 := by
      intro h
      apply hsum_ne
      rw [← hcoeff, h, Polynomial.coeff_zero]
    have hdeg_le : (A + B).natDegree ≤ A.natDegree := by
      have := Polynomial.natDegree_add_le A B
      omega
    have hdeg_ge : A.natDegree ≤ (A + B).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hsum_ne)
    have hdeg : (A + B).natDegree = A.natDegree := le_antisymm hdeg_le hdeg_ge
    refine ⟨?_, ?_⟩
    · rw [if_neg hne0, hdeg]
      exact_mod_cast hdA
    · have hlc : (A + B).leadingCoeff = A.leadingCoeff + B.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hdeg, hcoeff]
      show ((A + B).leadingCoeff : ℚ) = (A.leadingCoeff : ℚ) + (B.leadingCoeff : ℚ)
      rw [hlc]; push_cast; ring
  Full := fun _ => False
  hlift := by intro k hk; exact hk.elim

/-! ## Part 1 — the `(LB1)` countermodel: `O = ℤ`, `D = 1`, `F = X² + X + 1`, a two-side
trigger interface with unit class weights. -/

/-- `C₁`: the degree-graded carrier at `D = 1`. -/
noncomputable def C₁ : SlotCarrier ℤ ℚ :=
  gradedCarrier 1 1 1 one_pos rfl le_rfl le_rfl

/-- `B₁`: key `X`, mass `2`, `F = X² + X + 1` (irreducible over `ℚ`, disc `−3`). -/
noncomputable def B₁ : BlockData C₁ where
  Φ := X
  F := X ^ 2 + X + 1
  μ := 2
  hμ := by norm_num
  hΦ := monic_X
  hΦdeg := natDegree_X
  A := fun j => if j ≤ 1 then 1 else 0
  hdev := by
    simp [Finset.sum_range_succ]
    ring
  hdegA := by
    intro j hj
    interval_cases j <;> simp [C₁, gradedCarrier]
  hkeyfree := by
    refine ⟨1, -(X + 1), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := by norm_num
  T := 0

/-- The two-side trigger interface: sides `(1,1)` and `(2,1)`, one linear class each, all
weights `1`. -/
noncomputable def I₁ : RungInterface.{0, 0, 0} C₁ B₁ where
  sides := {(1, 1), (2, 1)}
  hside_cop := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> exact ⟨by decide, le_rfl⟩
  hside_node := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [B₁]
  len := fun _ => 1
  hlen_pos := fun _ _ => le_rfl
  hlen_sum := by simp [B₁]
  linFac := fun _ => {((0 : ℚ), 1)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp
  rootCount := fun _ => 1
  haccount := by
    intro p hp
    simp [C₁, gradedCarrier]
  classCount := fun _ _ => 1
  classCountHi := fun _ _ => 1
  hnonempty := by
    intro p hp
    exact ⟨fun q _ => le_rfl, fun q hq => by simp at hq⟩
  hforce := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    refine ⟨fun q _ => ?_, fun q hq => by simp at hq⟩
    rcases hp with rfl | rfl <;> simp [C₁, gradedCarrier]
  hexhaust := by
    intro p hp
    simp
  W := Unit
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := ()

lemma B₁_F_natDegree : B₁.F.natDegree = 2 := by
  show (X ^ 2 + X + 1 : ℤ[X]).natDegree = 2
  compute_degree!

/-- **THE `(LB1)` NON-TRIVIALITY CERTIFICATE.**  The re-signed `LB1Carrier` is FALSE at
`(C₁, B₁)`: the interface `I₁` is a trigger (two sides), its class weights force every
suite block to be monic linear, and `X² + X + 1` has no monic-linear integer
factorization.  In particular the pre-A-E.2 singleton self-block witness does not replay
(it fails `hcount`/`hdegsum`), and no other trivial recipe can exist. -/
theorem lb1_resigned_not_trivial : ¬ LB1Carrier.{0, 0, 0} C₁ B₁ := by
  intro h
  obtain ⟨S⟩ := h I₁ (Or.inl (by decide))
  -- every suite block has degree 1 (all parent class weights are 1)
  have hdeg1 : ∀ x ∈ S.blocks, x.1.F.natDegree = 1 := by
    intro x hx
    obtain ⟨p, _, hc⟩ := S.hcount x hx
    rcases hc with ⟨q, _, he⟩ | ⟨q, _, he⟩ <;> simpa [I₁] using he
  -- degree sum 2 ⟹ exactly two blocks
  have hsum : (S.blocks.map fun x => x.1.F.natDegree).sum = 2 := by
    rw [S.hdegsum, B₁_F_natDegree]
  have hrep : (S.blocks.map fun x => x.1.F.natDegree) =
      List.replicate (S.blocks.map fun x => x.1.F.natDegree).length 1 := by
    apply List.eq_replicate_of_mem
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact hdeg1 x hx
  have hlen : S.blocks.length = 2 := by
    have := hsum
    rw [hrep, List.sum_replicate, smul_eq_mul, mul_one] at this
    simpa using this
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  -- the product identity in ℤ[X]
  have hprod : (X ^ 2 + X + 1 : ℤ[X]) = x.1.F * y.1.F := by
    have := S.hprod
    rw [hxy] at this
    simpa [B₁] using this
  have hxdeg : x.1.F.natDegree = 1 := hdeg1 x (by rw [hxy]; simp)
  have hydeg : y.1.F.natDegree = 1 := hdeg1 y (by rw [hxy]; simp)
  -- write both factors as aX + b, cX + d
  have hxle : x.1.F.degree ≤ 1 := by
    have h := degree_le_natDegree (p := x.1.F)
    rw [hxdeg] at h
    exact_mod_cast h
  have hyle : y.1.F.degree ≤ 1 := by
    have h := degree_le_natDegree (p := y.1.F)
    rw [hydeg] at h
    exact_mod_cast h
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, x.1.F = C a * X + C b :=
    ⟨_, _, eq_X_add_C_of_degree_le_one hxle⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℤ, y.1.F = C c * X + C d :=
    ⟨_, _, eq_X_add_C_of_degree_le_one hyle⟩
  rw [hab, hcd] at hprod
  have hexp : (C a * X + C b) * (C c * X + C d)
      = C (a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
    simp only [C_mul, C_add]
    ring
  rw [hexp] at hprod
  -- coefficient comparison at 2, 1, 0
  have h2 := congrArg (fun p : ℤ[X] => p.coeff 2) hprod
  have h1 := congrArg (fun p : ℤ[X] => p.coeff 1) hprod
  have h0 := congrArg (fun p : ℤ[X] => p.coeff 0) hprod
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one, coeff_C,
    mul_ite, mul_one, mul_zero] at h2 h1 h0
  norm_num at h2 h1 h0
  -- h2 : a * c = 1 (up to orientation); h1 : middle = 1; h0 : b * d = 1
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h2.symm with ⟨ha1, hc1⟩ | ⟨ha1, hc1⟩ <;>
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h0.symm with ⟨hb1, hd1⟩ | ⟨hb1, hd1⟩ <;>
    rw [ha1, hc1, hb1, hd1] at h1 <;> norm_num at h1

/-! ## Part 2 — the `(MP1)` countermodel: `O = ℤ`, `D = 2`, key `X²`,
`F = X⁴ − 5X² + 4`, recentering `Λ = 4` ⟹ peeled key `X² − 4`, REDUCIBLE. -/

/-- `C₂`: the degree-graded carrier at `D = 2`, `(e, f) = (2, 1)`. -/
noncomputable def C₂ : SlotCarrier ℤ ℚ :=
  gradedCarrier 2 2 1 two_pos rfl one_le_two le_rfl

/-- `B₂`: key `X²`, mass `2`, `F = X⁴ − 5X² + 4 = (X² − 4)(X² − 1)`. -/
noncomputable def B₂ : BlockData C₂ where
  Φ := X ^ 2
  F := X ^ 4 - 5 * X ^ 2 + 4
  μ := 2
  hμ := by norm_num
  hΦ := monic_X_pow 2
  hΦdeg := natDegree_X_pow 2
  A := fun j => if j = 0 then 4 else if j = 1 then -5 else 0
  hdev := by
    simp [Finset.sum_range_succ]
    ring
  hdegA := by
    intro j hj
    interval_cases j <;>
      simp [C₂, gradedCarrier, Polynomial.natDegree_ofNat]
  hkeyfree := by
    -- 1 = (1/4)·F − (1/4)(X² − 5)·X²
    have h4 : (4 : FractionRing ℤ) ≠ 0 := by
      intro h
      have h0 : algebraMap ℤ (FractionRing ℤ) 4 = algebraMap ℤ (FractionRing ℤ) 0 := by
        rw [map_ofNat, map_zero, h]
      exact absurd (IsFractionRing.injective ℤ (FractionRing ℤ) h0) (by norm_num)
    refine ⟨C ((4 : FractionRing ℤ)⁻¹), -(C ((4 : FractionRing ℤ)⁻¹) * (X ^ 2 - 5)), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat]
    have hC : (C ((4 : FractionRing ℤ)⁻¹)) * (4 : (FractionRing ℤ)[X]) = 1 := by
      rw [show (4 : (FractionRing ℤ)[X]) = C (4 : FractionRing ℤ) from
          (map_ofNat (C : (FractionRing ℤ) →+* (FractionRing ℤ)[X]) 4).symm,
        ← C_mul, inv_mul_cancel₀ h4, C_1]
    linear_combination hC
  hA0 := by norm_num
  T := 0

/-- `B₂'`: the block carrying the recentered key `X² − 4` (its own data: mass `1`,
`F = X² − 3`). -/
noncomputable def B₂' : BlockData C₂ where
  Φ := X ^ 2 - 4
  F := X ^ 2 - 3
  μ := 1
  hμ := le_rfl
  hΦ := by
    have h := monic_X_pow_sub_C (4 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)
    have e : (X ^ 2 - C (4 : ℤ)) = (X ^ 2 - 4 : ℤ[X]) := by
      rw [map_ofNat]
    rwa [e] at h
  hΦdeg := by
    show (X ^ 2 - 4 : ℤ[X]).natDegree = C₂.D
    have e : (X ^ 2 - 4 : ℤ[X]) = X ^ 2 - C (4 : ℤ) := by rw [map_ofNat]
    rw [e, natDegree_X_pow_sub_C]
    rfl
  A := fun _ => 1
  hdev := by
    simp
    ring
  hdegA := by
    intro j hj
    simp [C₂, gradedCarrier]
  hkeyfree := by
    -- (X² − 3) − (X² − 4) = 1
    refine ⟨1, -1, ?_⟩
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
    ring
  hA0 := one_ne_zero
  T := 0

/-- degree-1 monic-shape factors of the peeled key over the fraction field are non-units. -/
lemma not_isUnit_linear (c : FractionRing ℤ) : ¬ IsUnit (X - C c) := by
  intro h
  have := natDegree_eq_zero_of_isUnit h
  simp at this

/-- **THE `(MP1)` NON-TRIVIALITY CERTIFICATE.**  The re-signed `MP1Carrier` is FALSE at
`(C₂, B₂)`: the frame-legal recentering `Λ = 4` yields the peeled key `X² − 4`, reducible
over the fraction field — so the record's item-5 clause `hirr` cannot be supplied.  In
particular the pre-A-E.2 fabricated-interface witness does not replay (it never addressed
`hirr`), and no other trivial recipe can exist. -/
theorem mp1_resigned_not_trivial : ¬ MP1Carrier.{0, 0, 0} C₂ B₂ := by
  intro h
  have hΛne : (4 : ℤ[X]) ≠ 0 := by norm_num
  have hΛdeg : (4 : ℤ[X]).natDegree < C₂.D := by
    show (4 : ℤ[X]).natDegree < 2
    simp [Polynomial.natDegree_ofNat]
  have hΦeq : B₂'.Φ = B₂.Φ - 4 := rfl
  have hdvd : B₂'.Φ ∣ B₂.F := by
    refine ⟨X ^ 2 - 1, ?_⟩
    show (X ^ 4 - 5 * X ^ 2 + 4 : ℤ[X]) = (X ^ 2 - 4) * (X ^ 2 - 1)
    ring
  obtain ⟨E⟩ := h 4 hΛne hΛdeg B₂' hΦeq hdvd
  -- the peeled key factors over the fraction field
  have hfactor : (B₂'.Φ.map (algebraMap ℤ (FractionRing ℤ)))
      = (X - C (2 : FractionRing ℤ)) * (X + C (2 : FractionRing ℤ)) := by
    show ((X ^ 2 - 4 : ℤ[X]).map (algebraMap ℤ (FractionRing ℤ))) = _
    have hC2 : (C (2 : FractionRing ℤ)) = (2 : (FractionRing ℤ)[X]) :=
      map_ofNat (C : (FractionRing ℤ) →+* (FractionRing ℤ)[X]) 2
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, hC2]
    ring
  rcases E.hirr.isUnit_or_isUnit hfactor with hu | hu
  · exact not_isUnit_linear _ hu
  · have e : (X + C (2 : FractionRing ℤ)) = X - C (-(2 : FractionRing ℤ)) := by
      rw [map_neg, sub_neg_eq_add]
    rw [e] at hu
    exact not_isUnit_linear _ hu

/-! ## Part 3 — the `(H-VARTHETA-RES)` countermodel (A-D.2): exact height holds, the old
trivializer fires for the VOIDED form, and the re-signed sitewise carrier is FALSE. -/

open LeanspecD

/-- The carrier group: `Multiplicative (ℤ × ℤ)` (first coordinate = height, second =
an ambient direction the height cannot see). -/
abbrev G₀ := Multiplicative (ℤ × ℤ)

/-- The height homomorphism: first coordinate. -/
def v₀ : G₀ →* Multiplicative ℤ := AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ)

/-- A normalizer section with EXACT height but a non-homomorphic twist in the second
coordinate (`δ(2) = 1`, else `0`). -/
def N₀ : NormSection G₀ where
  n := fun k => Multiplicative.ofAdd (k, if k = 2 then 1 else 0)
  n_zero := by simp

lemma v₀_exact : ∀ k : ℤ, v₀ (N₀.n k) = Multiplicative.ofAdd k := by
  intro k
  simp [v₀, N₀]

/-- The `i` of `ℂ` as a unit. -/
noncomputable def Iu : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

/-- The ambient residue datum: on the value-zero subgroup, `(0, m) ↦ i^m ∈ ℂˣ`. -/
noncomputable def ρ₀ : MonoidHom.ker v₀ →* ℂˣ :=
  (zpowersHom ℂˣ Iu).comp
    ((AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ ℤ)).comp (MonoidHom.ker v₀).subtype)

/-- The `s = 2` ϑ-quotient at `q = 1`: `n(1)² · n(2)⁻¹ = ofAdd (0, −1)`. -/
lemma varthetaEl_value : N₀.varthetaEl 1 2 = Multiplicative.ofAdd ((0 : ℤ), (-1 : ℤ)) := by
  show (N₀.n 1) ^ 2 * (N₀.n ((2 : ℕ) * 1))⁻¹ = Multiplicative.ofAdd ((0 : ℤ), (-1 : ℤ))
  simp only [N₀]
  norm_num
  rfl

/-- **The old trivializer still fires for the VOIDED form at this very instance** — the
contrast line: `⟨v₀, exact height, trivial res⟩` inhabits `HVarthetaResVoided`. -/
theorem voided_still_trivial_here : HVarthetaResVoided G₀ ℚ N₀ v₀ :=
  hvarthetaResVoided_of_exact_height ℚ N₀ v₀ v₀_exact

/-- **THE `(H-VARTHETA-RES)` NON-TRIVIALITY CERTIFICATE.**  Exact height holds at
`(N₀, v₀)`, yet the re-signed sitewise carrier is FALSE for the ambient residue datum
`ρ₀` at `q = 1`: the `s = 2` ϑ-quotient has ambient residue `i⁻¹ = −i`, which is not the
image of any `u ∈ ℚˣ` (imaginary part `−1 ≠ 0`).  So the pre-A-D.2 recipe
(exact height ⟹ carrier, via the trivial hom) does not replay against the re-signed
form. -/
theorem hvarthetaRes_resigned_not_trivial :
    (∀ k : ℤ, v₀ (N₀.n k) = Multiplicative.ofAdd k) ∧
      ¬ HVarthetaRes G₀ ℚ ℂ N₀ v₀ ρ₀ 1 := by
  refine ⟨v₀_exact, ?_⟩
  intro h
  obtain ⟨hmem, u, hu⟩ := h 2
  -- compute the ambient residue of the s = 2 ϑ-quotient
  have hval : ((ρ₀ ⟨N₀.varthetaEl 1 2, hmem⟩ : ℂˣ) : ℂ) = -Complex.I := by
    have : ρ₀ ⟨N₀.varthetaEl 1 2, hmem⟩ = Iu ^ (-1 : ℤ) := by
      simp [ρ₀, varthetaEl_value, Iu]
    rw [this]
    simp [Iu, Complex.inv_I]
  rw [hval] at hu
  -- the right side is a rational cast, of imaginary part 0
  have him := congrArg Complex.im hu
  have : (algebraMap ℚ ℂ (u : ℚ)) = ((u : ℚ) : ℂ) :=
    eq_ratCast (algebraMap ℚ ℂ) (u : ℚ)
  rw [this] at him
  simp [Complex.ratCast_im] at him

/-! ## Footprint census: Lean core only (no `sorry`, no repo axiom, no stub axiom). -/

#print axioms lb1_resigned_not_trivial
#print axioms mp1_resigned_not_trivial
#print axioms hvarthetaRes_resigned_not_trivial
#print axioms voided_still_trivial_here

end OM4ResignCert
