/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H97r4
import Uniformity.ChapH.H95
import Uniformity.ChapG.G54
import Uniformity.ChapG.G72
import Uniformity.Density.Statement

/-!
# Uniformity.ChapH.H97b — `package_three`: `P(3)` HOLDS, UNCONDITIONALLY

**Chapter H, NODE H97b** (unit OM-1, `docs/openmath-campaign/OM-1_n3-rate_2026-08-16.md`,
steps S8 + S9; the node name follows the charter's booking "new node file H97b"). *The second
base case, unconditional: `InductionPackage 3` is a theorem.*

`InductionPackage 3` holds with constants **`(K, B, c) = (1, 0, 3)`**:

* the **menu** member is chapter G's five-type cubic menu `coveringMenu_three` (G.54);
* the **rate** member is the NEW `rate_three`:
  `undecidedSeq O 3 M ≤ (q^(M−3))⁻¹` for `M ≥ 1`, over EVERY complete DVR with finite residue
  field, with the constants bound outside the quantifier over `O` — i.e.
  `RateSpecies (residueCard O) 1 0 3 (undecidedSeq O 3)` (H.65).

**The unroll (S8), all in ℕ.** H97r4's recursion `u(M+3) ≤ q^(2(M+3)) + q⁴·u(M)` and the
trivial base `u(M) ≤ q^(3M)` give, by 3-step strong induction,

    u(M) · q^M ≤ q^(3M+3)          (`undecidedCount_three_mul_le`),

whose step is the single inequality `1 + q ≤ q³` (here `2 ≤ q` is load-bearing). Dividing by
`q^(3M)` this is `undecidedSeq O 3 M ≤ q³·q^(−M)`, which is the species bound `(q^(M−3))⁻¹`
for `M ≥ 3` and is weaker than the trivial `s(M) ≤ 1 = (q^(M−0))⁻¹`-at-`c`-exponent-`0` for
`M < 3` — the ℕ-subtraction corner is handled by exactly that case split.

**RELATION TO H.97 (the statement fence).** H.97's `package_three_of_rate` and its `hrate`
hypothesis (constants `(1, 1, 0)`) are UNTOUCHED. `hrate (1,1,0)` is NOT discharged here:
at `M = 1` it demands the exact level-1 census `u(1) = q²` (true, tight, certified
numerically — `verification/om1_n3_rate_check.py`), which this counting chain does not
supply. `InductionPackage` is existential in the constants, so `package_three` lands
directly with `(1, 0, 3)`; chapter G's H-1 frontier (the rate) is CLOSED by this node, and
H.97 survives as the record of the frontier's original shape.

**Payoffs beyond the package** (each a consumer that was waiting on the `n = 3` rate):

* `undecidedSeq_three_tendsto_zero`, `drainage_three` — the `n = 3` undecided mass drains,
  unconditionally, general `O` (the `leanfinal` form of what the leancheck sidecar proved at
  `b00b0505`; here it comes from the RATE rather than from a separate limit argument);
* `drainageAt_three : DrainageAt 3` — the named degree-3 drainage Prop, closing the
  hypothesis that G.71 kept as chapter G's frontier interface (G.71 itself stays landed and
  untouched);
* `genuineDensity_three_eq_decidedDensity` — THE density equals the certified one at `n = 3`;
* `totalMass_three` — G.72's five-type sum equals `1`, now unconditional.

**TEETH.** `verification/om1_n3_rate_check.py` (2026-08-16, ALL CHECKS PASSED): the sharp
triple count TIGHT at every cell, the peel count and reduction verified on full enumerations
(`p = 2, N ≤ 6`; `p = 3, N ≤ 4`), the recursion and the `(1,0,3)` species shape replayed in
exact rationals (`q = 2, 3, 4`, `M ≤ 40`), the deep honest-decider fractions
(`N3_CHECK` §6c) all under `q^(3−N)`.

DEPENDS: H.65 (`RateSpecies`), H.95 (`InductionPackage`), H97r1–r4 · chapter G
`coveringMenu_three` (G.54), `undecidedCount_two_eq` (G.36, consumed in r4),
`totalMass_three_of_drainage` (G.72) · landed `undecidedSeq`, `residueCard`,
`drainage_of_undecided_comp`, `genuineDensity_eq_of_drainage`.

## Status

Sorry-free, axiom-free (Lean core only). **UNCONDITIONAL.**
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

section Rate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The trivial bound: there are at most `q^(nN)` classes at level `N`, undecided or not. -/
theorem undecidedCount_le_card (n N : ℕ) :
    undecidedCount O n N ≤ residueCard O ^ (n * N) := by
  rw [undecidedCount, ← card_coeff (O := O) n N]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- **S8, the ℕ master bound.** `u(M) · q^M ≤ q^(3M+3)` for every `M` — the unrolled
recursion, with no real division and no natural subtraction. Base (`M < 3`): the trivial
`u ≤ q^(3M)` and `4M ≤ 3M + 3`. Step: H97r4's recursion, `q^(3M+9)·(1 + q) ≤ q^(3M+12)`,
i.e. `1 + q ≤ q³` — the one place `2 ≤ q` is used. -/
theorem undecidedCount_three_mul_le (M : ℕ) :
    undecidedCount O 3 M * residueCard O ^ M ≤ residueCard O ^ (3 * M + 3) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hq1 : 1 ≤ residueCard O := by omega
    by_cases hM : M < 3
    · calc undecidedCount O 3 M * residueCard O ^ M
          ≤ residueCard O ^ (3 * M) * residueCard O ^ M :=
            Nat.mul_le_mul_right _ (undecidedCount_le_card 3 M)
        _ = residueCard O ^ (3 * M + M) := by rw [← pow_add]
        _ ≤ residueCard O ^ (3 * M + 3) := Nat.pow_le_pow_right hq1 (by omega)
    · obtain ⟨K, rfl⟩ : ∃ K, M = K + 3 := ⟨M - 3, by omega⟩
      have hrec := undecidedCount_three_recursion (O := O) K
      have hih := ih K (by omega)
      have hone : 1 + residueCard O ≤ residueCard O ^ 3 := by
        calc 1 + residueCard O ≤ residueCard O + residueCard O := by omega
          _ = 2 * residueCard O := by ring
          _ ≤ residueCard O * residueCard O := Nat.mul_le_mul_right _ hq2
          _ ≤ (residueCard O * residueCard O) * residueCard O :=
              Nat.le_mul_of_pos_right _ (by omega)
          _ = residueCard O ^ 3 := by ring
      calc undecidedCount O 3 (K + 3) * residueCard O ^ (K + 3)
          ≤ (residueCard O ^ (2 * (K + 3)) + residueCard O ^ 4 * undecidedCount O 3 K)
              * residueCard O ^ (K + 3) := Nat.mul_le_mul_right _ hrec
        _ = residueCard O ^ (3 * K + 9)
              + residueCard O ^ 7 * (undecidedCount O 3 K * residueCard O ^ K) := by
            ring
        _ ≤ residueCard O ^ (3 * K + 9)
              + residueCard O ^ 7 * residueCard O ^ (3 * K + 3) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hih) _
        _ = residueCard O ^ (3 * K + 9) * (1 + residueCard O) := by
            ring
        _ ≤ residueCard O ^ (3 * K + 9) * residueCard O ^ 3 :=
            Nat.mul_le_mul_left _ hone
        _ = residueCard O ^ (3 * (K + 3) + 3) := by
            ring

/-- **THE `n = 3` RATE (S8).** `RateSpecies (residueCard O) 1 0 3 (undecidedSeq O 3)`:
`undecidedSeq O 3 M ≤ (q^(M−3))⁻¹` for `M ≥ 1` (ℕ-subtraction), over every complete DVR
with finite residue field — chapter G's named frontier, CLOSED, with constants `(1, 0, 3)`
independent of `O`. -/
theorem rate_three : Induction.RateSpecies (residueCard O) 1 0 3 (undecidedSeq O 3) := by
  intro M hM
  simp only [pow_zero, one_mul, mul_one]
  -- the ℕ form: `u(M) · q^(M−3) ≤ q^(3M)`, by the master bound (`M ≥ 3`) or trivially
  have hnat : undecidedCount O 3 M * residueCard O ^ (M - 3) ≤ residueCard O ^ (3 * M) := by
    by_cases h3 : 3 ≤ M
    · have hq0 : 0 < residueCard O := residueCard_pos O
      refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq0 3)
      calc undecidedCount O 3 M * residueCard O ^ (M - 3) * residueCard O ^ 3
          = undecidedCount O 3 M * residueCard O ^ M := by
            rw [mul_assoc, ← pow_add]
            congr 2
            omega
        _ ≤ residueCard O ^ (3 * M + 3) := undecidedCount_three_mul_le M
        _ = residueCard O ^ (3 * M) * residueCard O ^ 3 := by rw [← pow_add]
    · have h0 : M - 3 = 0 := by omega
      rw [h0, pow_zero, mul_one]
      exact undecidedCount_le_card 3 M
  have hcast : (undecidedCount O 3 M : ℝ) * (residueCard O : ℝ) ^ (M - 3)
      ≤ (residueCard O : ℝ) ^ (3 * M) := by exact_mod_cast hnat
  rw [undecidedSeq, div_le_iff₀ (qpow_pos _)]
  calc (undecidedCount O 3 M : ℝ)
      = (undecidedCount O 3 M : ℝ) * (residueCard O : ℝ) ^ (M - 3)
          * ((residueCard O : ℝ) ^ (M - 3))⁻¹ :=
        (mul_inv_cancel_right₀ (ne_of_gt (qpow_pos _)) _).symm
    _ ≤ (residueCard O : ℝ) ^ (3 * M) * ((residueCard O : ℝ) ^ (M - 3))⁻¹ := by
        gcongr
    _ = ((residueCard O : ℝ) ^ (M - 3))⁻¹ * (residueCard O : ℝ) ^ (3 * M) := by ring

end Rate

/-! ## `P(3)` and the drainage payoffs -/

section Package

/-- **NODE H97b.** `P(3)` HOLDS, UNCONDITIONALLY, with constants `(K, B, c) = (1, 0, 3)`:
the menu is chapter G's five-type cubic menu and the rate is `rate_three`. Together with
H.96's `package_two`, both base cases of `THEOREM GENIND.B` are now theorems. -/
theorem package_three : InductionPackage 3 := by
  refine ⟨1, 0, 3, zero_le_one, ?_⟩
  intro O _ _ _ _ _
  exact ⟨⟨{c3split, c3linInert, c3inert, c3linRam, c3ram}, coveringMenu_three⟩, rate_three⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The `n = 3` undecided mass drains** — the rate's limit, by the squeeze under
`q³ · (q⁻¹)^N`. -/
theorem undecidedSeq_three_tendsto_zero :
    Tendsto (fun N => undecidedSeq O 3 N) atTop (𝓝 0) := by
  have hq1 : (1 : ℝ) < (residueCard O : ℝ) := by
    exact_mod_cast one_lt_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := lt_trans zero_lt_one hq1
  have hbound : ∀ N, undecidedSeq O 3 N
      ≤ (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ)⁻¹) ^ N := by
    intro N
    have hnat := undecidedCount_three_mul_le (O := O) N
    have hcast : (undecidedCount O 3 N : ℝ) * (residueCard O : ℝ) ^ N
        ≤ (residueCard O : ℝ) ^ (3 * N + 3) := by exact_mod_cast hnat
    rw [undecidedSeq, div_le_iff₀ (qpow_pos _), inv_pow]
    calc (undecidedCount O 3 N : ℝ)
        = (undecidedCount O 3 N : ℝ) * (residueCard O : ℝ) ^ N
            * ((residueCard O : ℝ) ^ N)⁻¹ :=
          (mul_inv_cancel_right₀ (ne_of_gt (qpow_pos _)) _).symm
      _ ≤ (residueCard O : ℝ) ^ (3 * N + 3) * ((residueCard O : ℝ) ^ N)⁻¹ := by gcongr
      _ = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ N)⁻¹
            * (residueCard O : ℝ) ^ (3 * N) := by
          rw [show 3 * N + 3 = 3 + 3 * N from by ring, pow_add]
          ring
  have hgeom : Tendsto (fun N : ℕ => (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ)⁻¹) ^ N)
      atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt (inv_pos.mpr hq0)) (inv_lt_one_of_one_lt₀ hq1)
    have h2 := h.const_mul ((residueCard O : ℝ) ^ 3)
    rwa [mul_zero] at h2
  exact squeeze_zero
    (fun N => div_nonneg (Nat.cast_nonneg _) (le_of_lt (qpow_pos _))) hbound hgeom

/-- **DRAINAGE AT `n = 3`, UNCONDITIONAL** (the `leanfinal` form; the leancheck sidecar's
`drainage_three` @ `b00b0505` proved the same statement in the sidecar). Every splitting
type's ambiguity gap drains, for every complete DVR with finite residue field. -/
theorem drainage_three (σ : FactorizationType) : UndecidedVanishes O 3 σ :=
  drainage_of_undecided_comp (φ := id) tendsto_id undecidedSeq_three_tendsto_zero σ

/-- **THE `n = 3` TIE.** THE density equals the certified one, for every type. -/
theorem genuineDensity_three_eq_decidedDensity (σ : FactorizationType) :
    genuineDensity O 3 σ = decidedDensity O 3 σ :=
  genuineDensity_eq_of_drainage (drainage_three σ)

/-- **The five-type total mass is `1`, unconditionally** — G.72's conditional node, fired. -/
theorem totalMass_three :
    genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram = 1 :=
  totalMass_three_of_drainage (fun σ => drainage_three σ)

end Package

/-- **`DrainageAt 3`** — the named degree-3 drainage Prop of `Statement.lean`, now a theorem.
(G.71's frontier interface is superseded for every drainage consumer; G.71 itself stays
landed as the record of the HEX3.A route.) -/
theorem drainageAt_three : DrainageAt 3 := by
  intro O _ _ _ _ _ σ
  exact drainage_three σ

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.undecidedCount_le_card
#print axioms Uniformity.Density.undecidedCount_three_mul_le
#print axioms Uniformity.Density.rate_three
#print axioms Uniformity.Density.package_three
#print axioms Uniformity.Density.undecidedSeq_three_tendsto_zero
#print axioms Uniformity.Density.drainage_three
#print axioms Uniformity.Density.genuineDensity_three_eq_decidedDensity
#print axioms Uniformity.Density.totalMass_three
#print axioms Uniformity.Density.drainageAt_three

end AxCheck
