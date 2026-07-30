/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-E0 — THE ZpBridge COUNTERMODEL GATE (bridge campaign BP1, RISK R1; runs FIRST)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.6 (†11f) /
§4 group E / §5 R1, and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (Q2: the
`MovesT.ramIdx`/`resDeg` repair path is signed off CONDITIONAL on this unit's
compiled countermodel — a fence event).

SEALED PREDICTION (recorded before any proving):
take p = 3, c = −1 (a non-square unit: p ≡ 3 mod 4), h := X² − p²·c = X² + 9 over
ℤ_[3].  Then
  (i)   h is monic of natDegree 2 and X² + 9 is irreducible over ℚ_3
        (roots ±3√−1, and −1 is not a square in ℚ_3);
  (ii)  `AdjoinRoot h = ℤ_3[π], π² = −9` IS a local ring (E0a): R/(3) =
        𝔽_3[X]/(X²) is local and 3 lies in the Jacobson radical of the finite
        ℤ_3-algebra R, so R has the unique maximal ideal m = (3, π);
  (iii) `MovesT.ramIdx h = 1` (E0b): (3) ≤ m but 3 ∉ m² = (9, 3π)
        (else 1 = 3a + πb ∈ m), so sSup {k | (3) ≤ m^k} = 1;
  (iv)  `MovesT.resDeg h = 1` (E0c): R/m = 𝔽_3[X]/(X, X²) = 𝔽_3, inertiaDeg 1;
  (v)   hence the aggregate degree conjunct of `ZpBridge.zf_factor` FAILS at
        g := h: the unique admissible factor multiset is {h} (monic ℚ_p
        factorizations are unique and `Polynomial.map PadicInt.Coe.ringHom` is
        injective), and {ramIdx h · resDeg h} = {1} ≠ {2} = {natDegree h} — so
        NO `ZpBridge 2 3 X` instance exists, for ANY classifier X (E0d).
TRUE INVARIANTS for contrast: ℚ_3(√−1)/ℚ_3 is the unramified quadratic extension,
(e, f) = (1, 2).  `ℤ_3[3√−1]` is a NON-MAXIMAL order, and `MovesT.ramIdx/resDeg`
read the ORDER's `IsLocalRing`-dispatched invariants, not the field's — exactly
blueprint finding R1.

DISPOSITION either way: if the pieces below PROVE, Q2's repair (re-point
`ramIdx`/`resDeg` at the valuation ring of the field `AdjoinRoot (h.map Coe)`) is
triggered and E5–E7 stay gated until it lands; if a piece REFUTES (a Mathlib
convention saves the aggregate), the deliverable is the refutation memo and E5–E7
un-gate.  CROSS-AREA FENCE (the M1 soundness lesson): once this countermodel
COMPILES sorry-free it must NOT coexist with an un-repaired sorried
`zf_factor`-instance universal — the Q2 repair lands in the same window.

Units: E0a `e0_isLocalRing` · E0b `e0_ramIdx` · E0c `e0_resDeg` ·
E0d `e0_zf_factor_false` + `e0_no_zpBridge`.  Deps: none (front-runner).

LANDED 2026-07-30 (IB-E0 prover): ALL pieces are now sorry-free — the sealed
prediction is CONFIRMED, the countermodel COMPILES, R1 stands.  Fence check at
landing time (grep-verified): NO sorried `ZpBridge`-producing universal exists
in-tree — the Q2-gated IB-E9 assembly `bridgeZpBridge` is not yet declared, and
`BridgeMk`/`BridgeInputs` only CONSUME a bridge as a hypothesis field (which this
gate renders vacuous at (n, p) = (2, 3): that is the finding, not a soundness
clash) — so the compiled witness may live here.  Q2's repair is TRIGGERED;
E5–E7 remain gated until the `ramIdx`/`resDeg` re-point lands.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- The countermodel polynomial (†11f): h := X² − p²·c at p = 3, c = −1, i.e.
    X² + 9 over ℤ_[3].  Monic, degree 2, ℚ_3-irreducible; `AdjoinRoot e0Poly` is
    the non-maximal order ℤ_3[3√−1]. -/
noncomputable def e0Poly : Polynomial ℤ_[3] := X ^ 2 + C 9

/-- E0 piece: e0Poly is monic (leading coefficient 1 in degree 2). -/
theorem e0Poly_monic : e0Poly.Monic :=
  monic_X_pow_add_C _ (by norm_num : (2 : ℕ) ≠ 0)

/-- E0 piece: natDegree e0Poly = 2. -/
theorem e0Poly_natDegree : e0Poly.natDegree = 2 := natDegree_X_pow_add_C

/-- Helper (mod-3 heart of the countermodel): no element of `ZMod 3` squares to
    `−1` — the squares mod 3 are {0, 1} and −1 = 2. -/
private lemma e0_zmod3_sq_ne_neg_one : ∀ t : ZMod 3, t ^ 2 ≠ -1 := by decide

/-- Helper: no 3-adic integer squares to `−1` (read off mod 3). -/
private lemma e0_padic_sq_ne_neg_one (w : ℤ_[3]) : w ^ 2 ≠ -1 := by
  intro hw
  have h := congrArg PadicInt.toZMod hw
  rw [map_pow, map_neg, map_one] at h
  exact e0_zmod3_sq_ne_neg_one _ h

/-- E0 piece: X² + 9 is irreducible over ℚ_3 — its roots ±3√−1 need √−1, and −1
    is not a square in ℚ_3 (not a square in 𝔽_3; p odd, unit square lifting). -/
theorem e0Poly_irreducible : Irreducible (e0Poly.map PadicInt.Coe.ringHom) := by
  have hmap : e0Poly.map PadicInt.Coe.ringHom = X ^ 2 + C (9 : ℚ_[3]) := by
    simp only [e0Poly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, map_ofNat]
  rw [hmap]
  by_contra hred
  obtain ⟨c, d, h0, h1⟩ :=
    ((monic_X_pow_add_C (9 : ℚ_[3]) (by norm_num : (2 : ℕ) ≠ 0)).not_irreducible_iff_exists_add_mul_eq_coeff
      natDegree_X_pow_add_C).mp hred
  have hc0 : (X ^ 2 + C (9 : ℚ_[3])).coeff 0 = 9 := by simp
  have hc1 : (X ^ 2 + C (9 : ℚ_[3])).coeff 1 = 0 := by simp [coeff_X_pow]
  rw [hc0] at h0
  rw [hc1] at h1
  -- h0 : 9 = c * d, h1 : 0 = c + d ⟹ c² = −9
  have hc2 : c ^ 2 = -9 := by
    have hd : d = -c := by linear_combination -h1
    rw [hd] at h0
    linear_combination h0
  -- c is a 3-adic integer: ‖c‖² = ‖−9‖ ≤ 1
  have hc_le : ‖c‖ ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h9 : ‖c ^ 2‖ ≤ 1 := by
      rw [hc2, norm_neg, show (9 : ℚ_[3]) = ((9 : ℤ) : ℚ_[3]) by norm_num]
      exact Padic.norm_int_le_one 9
    rw [norm_pow] at h9
    nlinarith [sq_nonneg (‖c‖ - 1), norm_nonneg c]
  set z : ℤ_[3] := ⟨c, hc_le⟩ with hz
  have hz2 : z ^ 2 = -9 := by
    apply PadicInt.ext
    push_cast
    exact hc2
  -- mod 3: z̄² = 0 ⟹ z̄ = 0 ⟹ 3 ∣ z
  have hz0 : PadicInt.toZMod z = 0 := by
    have hsq : PadicInt.toZMod z ^ 2 = 0 := by
      have h2 := congrArg PadicInt.toZMod hz2
      rw [map_pow, map_neg, map_ofNat] at h2
      rw [h2]
      decide
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hdvd : ((3 : ℕ) : ℤ_[3]) ∣ z := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hz0
  obtain ⟨w, hw⟩ := hdvd
  -- 9(w² + 1) = 0 in the domain ℤ_[3] ⟹ w² = −1: impossible mod 3
  rw [hw, show ((3 : ℕ) : ℤ_[3]) = (3 : ℤ_[3]) by norm_num] at hz2
  have h9w : (9 : ℤ_[3]) * (w ^ 2 + 1) = 0 := by linear_combination hz2
  have h9ne : (9 : ℤ_[3]) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h9w with h | h
  · exact h9ne h
  · exact e0_padic_sq_ne_neg_one w (by linear_combination h)

/-! ### The order's residue reads (E0a/E0b/E0c machinery)

`e0Psi : ℤ_3[π] → 𝔽_3` (root ↦ 0, mod 3) is the residue read whose kernel is
exactly the nonunits — it drives the locality proof, and `e0Chi : ℤ_3[π] → ℤ/9`
(root ↦ 0, mod 9) separates 3 from m² for the ramification read. -/

/-- The mod-3 residue read of the order: `ℤ_3[π] → 𝔽_3`, `π ↦ 0` (well-defined:
    0² + 9 ≡ 0 mod 3). -/
noncomputable def e0Psi : AdjoinRoot e0Poly →+* ZMod 3 :=
  AdjoinRoot.lift PadicInt.toZMod 0 (by
    change (X ^ 2 + C (9 : ℤ_[3])).eval₂ PadicInt.toZMod 0 = 0
    rw [eval₂_add, eval₂_X_pow, eval₂_C, map_ofNat]
    decide)

theorem e0Psi_of (a : ℤ_[3]) :
    e0Psi (AdjoinRoot.of e0Poly a) = PadicInt.toZMod a :=
  AdjoinRoot.lift_of _

theorem e0Psi_root : e0Psi (AdjoinRoot.root e0Poly) = 0 :=
  AdjoinRoot.lift_root _

/-- The mod-9 read of the order: `ℤ_3[π] → ℤ/9`, `π ↦ 0` (well-defined:
    0² + 9 ≡ 0 mod 9). -/
noncomputable def e0Chi : AdjoinRoot e0Poly →+* ZMod (3 ^ 2) :=
  AdjoinRoot.lift (PadicInt.toZModPow 2) 0 (by
    change (X ^ 2 + C (9 : ℤ_[3])).eval₂ (PadicInt.toZModPow 2) 0 = 0
    rw [eval₂_add, eval₂_X_pow, eval₂_C, map_ofNat]
    decide)

theorem e0Chi_of (a : ℤ_[3]) :
    e0Chi (AdjoinRoot.of e0Poly a) = PadicInt.toZModPow 2 a :=
  AdjoinRoot.lift_of _

theorem e0Chi_root : e0Chi (AdjoinRoot.root e0Poly) = 0 :=
  AdjoinRoot.lift_root _

/-- The defining relation, order-side: π² = −9. -/
theorem e0_root_sq :
    AdjoinRoot.root e0Poly ^ 2 = AdjoinRoot.of e0Poly (-9) := by
  have h2 : AdjoinRoot.mk e0Poly (X ^ 2 + C (9 : ℤ_[3])) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_pow, AdjoinRoot.mk_X] at h2
  rw [show AdjoinRoot.mk e0Poly (C (9 : ℤ_[3])) = AdjoinRoot.of e0Poly 9 from rfl] at h2
  rw [map_neg]
  linear_combination h2

/-- E0 workhorse (quadratic-order normal form): every element of `ℤ_3[π]` is
    `a + b·π` with `a, b ∈ ℤ_3` (the mod-by-monic representative has degree ≤ 1). -/
theorem e0_repr (x : AdjoinRoot e0Poly) :
    ∃ a b : ℤ_[3],
      x = AdjoinRoot.of e0Poly a + AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨(q %ₘ e0Poly).coeff 0, (q %ₘ e0Poly).coeff 1, ?_⟩
  have hne1 : e0Poly ≠ 1 := by
    intro h1
    have h2 := e0Poly_natDegree
    rw [h1, natDegree_one] at h2
    exact (by norm_num : (0 : ℕ) ≠ 2) h2
  have hdeg : (q %ₘ e0Poly).natDegree ≤ 1 := by
    have h2 := natDegree_modByMonic_lt q e0Poly_monic hne1
    rw [e0Poly_natDegree] at h2
    omega
  have hx : AdjoinRoot.mk e0Poly q = AdjoinRoot.mk e0Poly (q %ₘ e0Poly) := by
    conv_lhs => rw [← modByMonic_add_div q e0Poly]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  rw [hx]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, AdjoinRoot.mk_X]
  simp only [show ∀ y : ℤ_[3], AdjoinRoot.mk e0Poly (C y) = AdjoinRoot.of e0Poly y
    from fun _ => rfl]
  ring

/-- THE UNIT CRITERION on the order (hard direction): nonzero mod-3 residue read
    forces a unit — conjugation: (a + bπ)(a − bπ) = a² + 9b², a unit of ℤ_3 when
    3 ∤ a (its mod-3 read is ā² ≠ 0). -/
theorem e0_isUnit_of_psi_ne_zero {x : AdjoinRoot e0Poly} (hx : e0Psi x ≠ 0) :
    IsUnit x := by
  obtain ⟨a, b, rfl⟩ := e0_repr x
  rw [map_add, map_mul, e0Psi_of, e0Psi_of, e0Psi_root, mul_zero, add_zero] at hx
  -- hx : toZMod a ≠ 0; the norm form N = a² + 9b² is then a unit of ℤ_3
  have hN : IsUnit (a ^ 2 + 9 * b ^ 2) := by
    by_contra hnu
    have hmem : a ^ 2 + 9 * b ^ 2 ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact mem_nonunits_iff.mpr hnu
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
    rw [map_add, map_mul, map_pow, map_pow, map_ofNat] at hmem
    rw [show (9 : ZMod 3) = 0 by decide, zero_mul, add_zero] at hmem
    exact hx ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hmem)
  have hconj : (AdjoinRoot.of e0Poly a + AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly) *
      (AdjoinRoot.of e0Poly a - AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly)
      = AdjoinRoot.of e0Poly (a ^ 2 + 9 * b ^ 2) := by
    have expand : (AdjoinRoot.of e0Poly a + AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly) *
        (AdjoinRoot.of e0Poly a - AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly)
        = AdjoinRoot.of e0Poly a ^ 2
          - AdjoinRoot.of e0Poly b ^ 2 * AdjoinRoot.root e0Poly ^ 2 := by ring
    rw [expand, e0_root_sq, ← map_pow, ← map_pow, ← map_mul, ← map_sub]
    congr 1
    ring
  refine isUnit_of_mul_isUnit_left
    (y := AdjoinRoot.of e0Poly a - AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly) ?_
  rw [hconj]
  exact (AdjoinRoot.of e0Poly).isUnit_map hN

/-- E0a — LOCALITY of the order: `AdjoinRoot e0Poly = ℤ_3[π], π² = −9` is local
    (m = (3, π); R/(3) = 𝔽_3[X]/(X²) is local and 3 is in the Jacobson radical of
    the finite ℤ_3-algebra).  NOTE: this is the piece that makes the junk
    dispatch of `MovesT.ramIdx`/`resDeg` FIRE, so the countermodel reads the
    order's invariants, not junk 0. -/
theorem e0_isLocalRing : IsLocalRing (AdjoinRoot e0Poly) := by
  haveI : Nontrivial (AdjoinRoot e0Poly) := e0Psi.domain_nontrivial
  apply IsLocalRing.of_nonunits_add
  intro x y hx hy
  rw [mem_nonunits_iff] at hx hy ⊢
  intro hunit
  have hpx : e0Psi x = 0 := by
    by_contra h
    exact hx (e0_isUnit_of_psi_ne_zero h)
  have hpy : e0Psi y = 0 := by
    by_contra h
    exact hy (e0_isUnit_of_psi_ne_zero h)
  have h0 : e0Psi (x + y) = 0 := by rw [map_add, hpx, hpy, add_zero]
  have hu0 : IsUnit (0 : ZMod 3) := h0 ▸ hunit.map e0Psi
  exact not_isUnit_zero hu0

/-- The E0a conclusion as an instance, so that downstream statements about the
    order's maximal ideal elaborate. -/
instance e0_instIsLocalRing : IsLocalRing (AdjoinRoot e0Poly) := e0_isLocalRing

/-- π is in the maximal ideal (its mod-3 read is 0). -/
theorem e0_root_mem_max :
    AdjoinRoot.root e0Poly ∈ IsLocalRing.maximalIdeal (AdjoinRoot e0Poly) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have h := hunit.map e0Psi
  rw [e0Psi_root] at h
  exact not_isUnit_zero h

/-- The mod-9 read of any nonunit of the order is divisible by 3 (a nonunit is
    3a′ + bπ, and χ kills π while sending 3 to 3). -/
theorem e0Chi_nonunit {x : AdjoinRoot e0Poly} (hx : ¬IsUnit x) :
    ∃ t : ZMod (3 ^ 2), e0Chi x = 3 * t := by
  obtain ⟨a, b, rfl⟩ := e0_repr x
  have ha : PadicInt.toZMod a = 0 := by
    by_contra h
    refine hx (e0_isUnit_of_psi_ne_zero ?_)
    rw [map_add, map_mul, e0Psi_of, e0Psi_of, e0Psi_root, mul_zero, add_zero]
    exact h
  have hmem : ((3 : ℕ) : ℤ_[3]) ∣ a := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact ha
  obtain ⟨c, hc⟩ := hmem
  refine ⟨PadicInt.toZModPow 2 c, ?_⟩
  rw [map_add, map_mul, e0Chi_of, e0Chi_of, e0Chi_root, mul_zero, add_zero, hc,
    map_mul, map_natCast]
  norm_num

/-- E0b — the order's ramification read is 1: (3) ≤ m = (3, π) but
    3 ∉ m² = (9, 3π) (else 1 = 3a + πb ∈ m), so
    `Ideal.ramificationIdx (max ℤ_3) (max R) = sSup {k | (3) ≤ m^k} = 1`. -/
theorem e0_ramIdx : MovesT.ramIdx e0Poly = 1 := by
  unfold MovesT.ramIdx
  rw [dif_pos e0_instIsLocalRing]
  refine Ideal.ramificationIdx_spec ?_ ?_
  · -- map (3) ≤ m¹: the image of 3 is a nonunit
    rw [pow_one, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h0 : e0Psi (algebraMap ℤ_[3] (AdjoinRoot e0Poly) ((3 : ℕ) : ℤ_[3])) = 0 := by
      rw [AdjoinRoot.algebraMap_eq, e0Psi_of, map_natCast]
      decide
    have h := hunit.map e0Psi
    rw [h0] at h
    exact not_isUnit_zero h
  · -- ¬ map (3) ≤ m²: χ (mod 9) kills m² but not 3
    intro hle
    have h3mem : algebraMap ℤ_[3] (AdjoinRoot e0Poly) ((3 : ℕ) : ℤ_[3])
        ∈ IsLocalRing.maximalIdeal (AdjoinRoot e0Poly) ^ (1 + 1) := by
      apply hle
      apply Ideal.mem_map_of_mem
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    have hker : IsLocalRing.maximalIdeal (AdjoinRoot e0Poly) ^ (1 + 1)
        ≤ RingHom.ker e0Chi := by
      rw [pow_succ, pow_one]
      refine Ideal.mul_le.mpr fun r hr s hs => ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr hs
      obtain ⟨t, ht⟩ := e0Chi_nonunit hr
      obtain ⟨u, hu⟩ := e0Chi_nonunit hs
      rw [RingHom.mem_ker, map_mul, ht, hu]
      calc (3 : ZMod (3 ^ 2)) * t * (3 * u) = 3 * 3 * (t * u) := by ring
        _ = 0 := by rw [show (3 : ZMod (3 ^ 2)) * 3 = 0 by decide, zero_mul]
    have h30 := hker h3mem
    rw [RingHom.mem_ker, AdjoinRoot.algebraMap_eq, e0Chi_of, map_natCast] at h30
    exact (by decide : ((3 : ℕ) : ZMod (3 ^ 2)) ≠ 0) h30

/-- Units of ℤ_3 are read off through the order: a is a unit iff a + 0·π is. -/
theorem e0_of_isUnit_iff {a : ℤ_[3]} :
    IsUnit (AdjoinRoot.of e0Poly a) ↔ IsUnit a := by
  constructor
  · intro h
    have hzu : IsUnit (PadicInt.toZMod a) := by
      have h2 := h.map e0Psi
      rwa [e0Psi_of] at h2
    by_contra hnu
    have hmem : a ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact mem_nonunits_iff.mpr hnu
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
    exact hzu.ne_zero hmem
  · intro h
    exact h.map (AdjoinRoot.of e0Poly)

/-- The order's maximal ideal contracts to (3): the countermodel's m lies over
    the maximal ideal of ℤ_3. -/
theorem e0_comap_max :
    Ideal.comap (algebraMap ℤ_[3] (AdjoinRoot e0Poly))
      (IsLocalRing.maximalIdeal (AdjoinRoot e0Poly)) = IsLocalRing.maximalIdeal ℤ_[3] := by
  ext a
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr e0_of_isUnit_iff

instance e0_liesOver :
    (IsLocalRing.maximalIdeal (AdjoinRoot e0Poly)).LiesOver
      (IsLocalRing.maximalIdeal ℤ_[3]) :=
  ⟨e0_comap_max.symm⟩

/-- E0c — the order's residue read is 1: R/m = 𝔽_3[X]/(X, X²) = 𝔽_3, so
    inertiaDeg = 1.  (The FIELD's residue degree is 2 — the order is not maximal;
    that contrast is the whole finding.) -/
theorem e0_resDeg : MovesT.resDeg e0Poly = 1 := by
  unfold MovesT.resDeg
  rw [dif_pos e0_instIsLocalRing]
  rw [Ideal.inertiaDeg_algebraMap]
  have hbij : Function.Bijective
      (algebraMap (ℤ_[3] ⧸ IsLocalRing.maximalIdeal ℤ_[3])
        (AdjoinRoot e0Poly ⧸ IsLocalRing.maximalIdeal (AdjoinRoot e0Poly))) := by
    constructor
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨a, b, rfl⟩ := e0_repr x
      refine ⟨Ideal.Quotient.mk _ a, ?_⟩
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver, AdjoinRoot.algebraMap_eq, map_add]
      have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot e0Poly))
          (AdjoinRoot.of e0Poly b * AdjoinRoot.root e0Poly) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_left _ _ e0_root_mem_max
      rw [hz, add_zero]
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij)]
  exact Module.finrank_self _

/-- E0d — THE COUNTERMODEL: no factor multiset satisfies `zf_factor`'s conjuncts
    1, 2 and the (3∧4)-composite at g := e0Poly.  Route: by conjuncts 1–2 and
    uniqueness of monic ℚ_p-factorizations (+ injectivity of
    `Polynomial.map PadicInt.Coe.ringHom`), factors = {e0Poly}; then the
    composite demands {ramIdx·resDeg} = {1} = {2} = {natDegree} — false. -/
theorem e0_zf_factor_false :
    ¬ ∃ factors : Multiset (Polynomial ℤ_[3]),
      e0Poly.map PadicInt.Coe.ringHom
          = (factors.map (Polynomial.map PadicInt.Coe.ringHom)).prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible (h.map PadicInt.Coe.ringHom)) ∧
      factors.map (fun h => MovesT.ramIdx h * MovesT.resDeg h)
        = factors.map Polynomial.natDegree := by
  rintro ⟨factors, hprod, hfac, hagg⟩
  have hEirr : Irreducible (e0Poly.map PadicInt.Coe.ringHom) := e0Poly_irreducible
  have hsingle : factors = {e0Poly} := by
    obtain ⟨g, T, rfl⟩ : ∃ g T, factors = g ::ₘ T := by
      rcases Multiset.empty_or_exists_mem factors with h0 | ⟨g, hg⟩
      · exfalso
        rw [h0, Multiset.map_zero, Multiset.prod_zero] at hprod
        exact hEirr.not_isUnit (by rw [hprod]; exact isUnit_one)
      · obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hg
        exact ⟨g, T, hT⟩
    rw [Multiset.map_cons, Multiset.prod_cons] at hprod
    have hT0 : T = 0 := by
      by_contra hne
      obtain ⟨g', hg'⟩ := Multiset.exists_mem_of_ne_zero hne
      rcases hEirr.isUnit_or_isUnit hprod with hu | hu
      · exact ((hfac g (Multiset.mem_cons_self g T)).2).not_isUnit hu
      · have hdvd : g'.map PadicInt.Coe.ringHom
            ∣ (T.map (Polynomial.map PadicInt.Coe.ringHom)).prod :=
          Multiset.dvd_prod (Multiset.mem_map_of_mem _ hg')
        exact ((hfac g' (Multiset.mem_cons_of_mem hg')).2).not_isUnit
          (isUnit_of_dvd_unit hdvd hu)
    subst hT0
    rw [Multiset.map_zero, Multiset.prod_zero, mul_one] at hprod
    have hg_eq : g = e0Poly :=
      (Polynomial.map_injective PadicInt.Coe.ringHom
        (fun _ _ h => PadicInt.ext h) hprod).symm
    rw [hg_eq]
    rfl
  rw [hsingle, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.singleton_inj] at hagg
  simp only [e0_ramIdx, e0_resDeg, e0Poly_natDegree] at hagg
  norm_num at hagg

/-- E0d assembly — THE CONSEQUENCE (blueprint †11f): as currently typed, NO
    `ZpBridge` instance exists at (n, p) = (2, 3), for ANY classifier `X`
    (the ∃ in `zf_factor` gives no freedom).  The wiring below is REAL (compiled
    now); only the pieces above carry sorries. -/
theorem e0_no_zpBridge (X : ClassifierSpec 2 3) : IsEmpty (ZpBridge 2 3 X) := by
  constructor
  intro B
  obtain ⟨factors, hprod, hfac, hzf, hdeg⟩ :=
    B.zf_factor e0Poly e0Poly_monic e0Poly_natDegree
  refine e0_zf_factor_false ⟨factors, hprod, hfac, ?_⟩
  calc factors.map (fun h => MovesT.ramIdx h * MovesT.resDeg h)
      = (factors.map (fun h => (MovesT.ramIdx h, MovesT.resDeg h))).map
          (fun ef => ef.1 * ef.2) := by
        rw [Multiset.map_map]; rfl
    _ = (B.zfType e0Poly).map (fun ef => ef.1 * ef.2) := by rw [hzf]
    _ = factors.map Polynomial.natDegree := hdeg

end LeanUrat.MovesU
