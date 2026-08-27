/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp10b

/-!
# Uniformity.ChapC.C132kp6b — the μ₃ key-structure bank and the converse (M3-KP6b)

**[M3-KP6b, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6; the μ₃
campaign's LAST node): the `hconv` hypothesis of `C132fd0.s2SourceLawsTwo_of` is
DISCHARGED — for μ₃ key polynomials, equal normalized residuals force initial equivalence
(published Prop 5.6's (2)→(3) one level up).  With M3-RP10b's `hex` already landed, this
fires ★★★ `s2Mu3_calculus_nonempty : Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)` —
the UNCONDITIONAL depth-2 calculus.

## The dictionary (the port of `C130kp7`'s Parts 1–6, one level up)

* ★ `s2Mu3Minimal_natDegree_four_dvd` (published Lemma 2.10's genre at `deg Φ₂ = 4`):
  a monic μ₃-minimal polynomial has degree divisible by `4`.  The refuter for
  `deg g = 4m + r` (`1 ≤ r ≤ 3`) is `Q := Φ₂^(m+1) /ₘ g` — the division identity makes
  `g·Q − Φ₂^(m+1) = −(Φ₂^(m+1) %ₘ g)` of degree `< deg g` carrying `g·Q`'s initial form
  (this replaces the μ₂ proof's hand-built coefficient-matching multiplier, which does not
  port: `Φ₂ = Φ′² + 4x` has no vanishing-coefficient pattern).  The key power sits at
  `21(m+1)`, strictly above `μ₃(g·Q) ≤ (2c_r + 21m) + 2c_{4−r} ≤ 21m + 20`, where
  `c_1, c_2, c_3 = 2, 5, 7` are the inner cleared μ₂ bounds of monic digits of degree
  `1, 2, 3` (top-digit stage heights; the `r = 2` case is tight: `20 < 21`).
* ★ `s2Mu3Minimal_exactGrade` (published Lemma 2.11's invariant at slope `21/4`):
  μ₃-minimality pins the grade `μ₃(g) = 21·(deg g/4)` — the top digit is `1`, and a
  strictly smaller grade would make the truncation `g − Φ₂^m` a smaller-degree carrier of
  `g`'s initial form.
* ★ `s2Mu3KeyPoly_slotZero` (published Lemma 5.1's `s(g) = 0` clause): a μ₃ key of degree
  `> 4` has slot 0 on its grade line — one-step deflation (the private
  `mu3Dvd_phi2_of_not_slotZero` remainder argument, the file-local copy of M3-KP4's) plus
  μ₃-primality: `g ∼ Φ₂·q` forces `g ∣μ₃ Φ₂` (killed by minimality, `deg Φ₂ = 4 < deg g`)
  or `g ∣μ₃ q` (killed by the grade ledger `β = 21 + γ ∧ γ = β + γ′` in ℕ).
* the assembled bank: every μ₃ key `g` with `m := deg g/4` has exact grade `21m`, nonzero
  residual scalar (trailing `y`-power `0`, so the normalized residual IS the graded
  residual), `deg R₄(g) = deg g/8`, and the degree dictionary
  `m = 1 ∨ m = 2·deg R₄(g)` (the `∼ Φ₂` fiber versus the proper degree-`8·deg ψ` keys).
* ★★ `s2Mu3_residual_to_initial` — the converse: keyhood + equal residuals force equal
  degrees, hence a COMMON exact grade `21m`; the trivial strip turns residual equality
  into graded equality; the graded-piece IFF (file-local copy of M3-KP4's) fires backward.
* ★★★ `s2Mu3_hconv` (the exact `hconv` shape), `s2Mu3_initial_iff_residual` (both
  directions, forward from M3-KP6), and `s2Mu3_calculus_nonempty` (the star).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): the three
structure mechanisms (`s2Mu3Minimal_natDegree_four_dvd`, `s2Mu3Minimal_exactGrade`,
`s2Mu3KeyPoly_slotZero`), the degree dictionary (`s2Mu3KeyPoly_natDegree_pin`), and the
converse (`s2Mu3_residual_to_initial`).

Sorry-free, no new axiom, no statement touched; Lean-core footprint (AxChk footer).
-/

set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Uniformity.Density.Tower.C132kp6b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C131v Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132kp6
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private copies and the inner monic-digit bounds

The private-copy pattern of `C130kp7`/`C132kp4`: numerals, stage heights, and the three
fresh inner cleared μ₂ bounds `c_1, c_2, c_3 = 2, 5, 7` for monic digits of degree
`1, 2, 3` (the μ₂ development of a degree-`j` monic has its top slot `j/2` at height `0`
if `j` is even, `≤ 1` if odd — `dvSupp ≤ 2·hgt + 5·slot`). -/

private theorem phi2_natDegree :
    (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree = 4 :=
  s2Φ₂_natDegree h2 hq

private theorem phi2_monic : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic :=
  s2Φ₂_monic h2 hq

private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy of C130kp7's `stageHeight_one`. -/
private theorem stageHeight_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- private copy of C130kp7's monic-linear stage bound. -/
private theorem stageHeight_le_one_of_monic_linear {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) : (s2Frame h2 hq).stageHeight A ≤ 1 := by
  rw [KeyFrame.stageHeight_eq_inf]
  refine le_trans (Finset.inf_le (Finset.mem_range.mpr (show 1 < A.natDegree + 1 by omega))) ?_
  have hc : A.coeff 1 = 1 := by rw [← hdeg]; exact hA.coeff_natDegree
  rw [hc]
  simp only [e1_eq h2 hq, h_eq h2 hq, gaussVal_C, AddValuation.map_one, smul_zero, zero_add]
  simp

/-- **the degree-1 inner bound**: a monic linear digit has cleared μ₂ value `≤ 2`. -/
private theorem dvSupp_le_of_monic_deg1 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (2 : ℕ∞) := by
  have hself : dev (s2Frame h2 hq).key A 0 = A := by
    rw [dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
    rw [Polynomial.degree_eq_natDegree hA.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hdeg]
    exact_mod_cast (by omega : 1 < 2)
  have hhgt : dvHgt (s2Frame h2 hq) A 0 ≤ (1 : ℕ∞) := by
    rw [dvHgt, hself]
    exact stageHeight_le_one_of_monic_linear h2 hq hA hdeg
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 0) ?_
  simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [two_nsmul]
  calc dvHgt (s2Frame h2 hq) A 0 + dvHgt (s2Frame h2 hq) A 0
      ≤ (1 : ℕ∞) + (1 : ℕ∞) := add_le_add hhgt hhgt
    _ = 2 := one_add_one_eq_two

/-- **the degree-2 inner bound**: a monic quadratic digit has cleared μ₂ value `≤ 5`. -/
private theorem dvSupp_le_of_monic_deg2 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 2) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (5 : ℕ∞) := by
  have htop : dev (s2Frame h2 hq).key A 1 = 1 :=
    dev_top_eq_one (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos 1 A hA
      (by rw [key_natDegree_two h2 hq]; omega)
  have hhgt : dvHgt (s2Frame h2 hq) A 1 = 0 := by
    rw [dvHgt, htop]
    exact stageHeight_one h2 hq
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 1) ?_
  rw [hhgt, smul_zero, zero_add]
  simp only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  exact le_rfl

/-- **the degree-3 inner bound**: a monic cubic digit has cleared μ₂ value `≤ 7` (its top
digit is monic linear, so the slot-1 height is `≤ 1`). -/
private theorem dvSupp_le_of_monic_deg3 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 3) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (7 : ℕ∞) := by
  have hdle : ((s2Frame h2 hq).key : Polynomial O).degree ≤ A.degree := by
    rw [Polynomial.degree_eq_natDegree hA.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hdeg]
    exact_mod_cast (by omega : 2 ≤ 3)
  have hQm : (A /ₘ (s2Frame h2 hq).key).Monic :=
    monic_divByMonic hA (s2Frame h2 hq).hmonic hdle
  have hQd : (A /ₘ (s2Frame h2 hq).key).natDegree = 1 := by
    rw [Polynomial.natDegree_divByMonic A (s2Frame h2 hq).hmonic,
      key_natDegree_two h2 hq, hdeg]
  have hd1 : dev (s2Frame h2 hq).key A 1 = A /ₘ (s2Frame h2 hq).key := by
    rw [show dev (s2Frame h2 hq).key A 1
        = dev (s2Frame h2 hq).key (A /ₘ (s2Frame h2 hq).key) 0 from rfl, dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
    rw [Polynomial.degree_eq_natDegree hQm.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hQd]
    exact_mod_cast (by omega : 1 < 2)
  have hhgt : dvHgt (s2Frame h2 hq) A 1 ≤ (1 : ℕ∞) := by
    rw [dvHgt, hd1]
    exact stageHeight_le_one_of_monic_linear h2 hq hQm hQd
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 1) ?_
  simp only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  rw [two_nsmul]
  calc dvHgt (s2Frame h2 hq) A 1 + dvHgt (s2Frame h2 hq) A 1 + (5 : ℕ∞)
      ≤ (1 : ℕ∞) + (1 : ℕ∞) + (5 : ℕ∞) := add_le_add (add_le_add hhgt hhgt) le_rfl
    _ = 7 := by norm_num

/-! ## Part 1 — the μ₃ term bound, the top digits, and the top-slot pin -/

/-- **the μ₃ term bound in ℕ** (the port of C130kp7's `grade_le_of_dvHgt_le` one level up):
an exact μ₃ grade is at most `2c + 21j` for any slot-`j` pin bound `c`. -/
private theorem mu3_grade_le_of_pin_le {β c j : ℕ} {g : Polynomial O}
    (hβ : S2Mu3ExactGrade h2 hq β g)
    (hc : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g j
      ≤ (c : ℕ∞)) :
    β ≤ 2 * c + 21 * j := by
  have hterm := C132nv2.dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (phi2_monic h2 hq) (by rw [phi2_natDegree h2 hq]; norm_num) g 21
    (by norm_num : (0 : ℕ) < 2) j
  rw [(S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hβ] at hterm
  have h2c : (2 : ℕ) • dv2Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) g j ≤ ((2 * c : ℕ) : ℕ∞) := by
    rw [two_nsmul]
    calc dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g j
          + dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g j
        ≤ (c : ℕ∞) + (c : ℕ∞) := add_le_add hc hc
      _ = ((2 * c : ℕ) : ℕ∞) := by push_cast; ring
  have hle : ((β : ℕ) : ℕ∞) ≤ ((2 * c + 21 * j : ℕ) : ℕ∞) := by
    calc ((β : ℕ) : ℕ∞)
        ≤ 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g j
            + ((21 * j : ℕ) : ℕ∞) := by
          refine hterm.trans (le_of_eq ?_)
          push_cast
          ring
      _ ≤ ((2 * c : ℕ) : ℕ∞) + ((21 * j : ℕ) : ℕ∞) := add_le_add h2c le_rfl
      _ = ((2 * c + 21 * j : ℕ) : ℕ∞) := by push_cast; ring
  exact_mod_cast hle

/-- **the μ₃ top digit at fractional degree**: a monic polynomial of degree `4m + r`
(`1 ≤ r ≤ 3`) has monic degree-`r` top `Φ₂`-digit (kp7's odd-top-digit induction at the
degree-4 development). -/
private theorem dev_phi2_top_monic :
    ∀ (m : ℕ) (A : Polynomial O) (r : ℕ), 1 ≤ r → r ≤ 3 → A.Monic →
      A.natDegree = 4 * m + r →
      (dev (s2DepthTwoKeyAt h2 hq 2) A m).Monic ∧
        (dev (s2DepthTwoKeyAt h2 hq 2) A m).natDegree = r := by
  intro m
  induction m with
  | zero =>
    intro A r hr1 hr3 hA hdeg
    have hself : dev (s2DepthTwoKeyAt h2 hq 2) A 0 = A := by
      rw [dev_zero_pin]
      refine (Polynomial.modByMonic_eq_self_iff (phi2_monic h2 hq)).mpr ?_
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (phi2_monic h2 hq).ne_zero,
        phi2_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 4 * 0 + r < 4)
    rw [hself]
    exact ⟨hA, by omega⟩
  | succ m ih =>
    intro A r hr1 hr3 hA hdeg
    rw [show dev (s2DepthTwoKeyAt h2 hq 2) A (m + 1)
        = dev (s2DepthTwoKeyAt h2 hq 2) (A /ₘ (s2DepthTwoKeyAt h2 hq 2)) m from rfl]
    have hdle : ((s2DepthTwoKeyAt h2 hq 2) : Polynomial O).degree ≤ A.degree := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (phi2_monic h2 hq).ne_zero,
        phi2_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 4 ≤ 4 * (m + 1) + r)
    refine ih _ r hr1 hr3 (monic_divByMonic hA (phi2_monic h2 hq) hdle) ?_
    rw [Polynomial.natDegree_divByMonic A (phi2_monic h2 hq), phi2_natDegree h2 hq, hdeg]
    omega

/-- the inner cleared value of the digit `1` is `0`. -/
private theorem dvSupp_one_eq_zero : dvSupp (s2Frame h2 hq) (1 : Polynomial O) 5 2 = 0 := by
  have hhgt : dvHgt (s2Frame h2 hq) (1 : Polynomial O) 0 = 0 := by
    rw [dvHgt, dev_zero_pin]
    have hself : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 := by
      refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
      rw [Polynomial.degree_eq_natDegree (one_ne_zero : (1 : Polynomial O) ≠ 0),
        Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
        Polynomial.natDegree_one, key_natDegree_two h2 hq]
      exact_mod_cast (by omega : 0 < 2)
    rw [hself]
    exact stageHeight_one h2 hq
  refine le_antisymm ?_ _root_.zero_le
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) 1 5 (by norm_num : (0 : ℕ) < 2) 0) ?_
  rw [hhgt, smul_zero, zero_add]
  simp

/-- **the top pin at full degree**: monic of degree `4m` has slot-`m` pin `0` (the top
digit is `1`). -/
private theorem dv2Pin_top_of_monic_mul_four {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 4 * m) :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g m = 0 := by
  rw [dv2Pin, dev_top_eq_one (phi2_monic h2 hq)
      (by rw [phi2_natDegree h2 hq]; norm_num) m g hmon
      (by rw [phi2_natDegree h2 hq]; omega),
    dv2Hgt_eq_dvSupp h2 hq, dvSupp_one_eq_zero h2 hq]

/-- **the top slot is on its own line**: monic of degree `4m` has slot `m` on the
grade-`21m` line. -/
private theorem slot_top_of_monic_mul_four {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 4 * m) : S2Mu3SlotOnGrade h2 hq (21 * m) g m :=
  (s2Mu3SlotOnGrade_iff h2 hq).mpr
    ⟨0, by rw [dv2Pin_top_of_monic_mul_four h2 hq hmon hd]; norm_num, by omega⟩

/-! ## Part 2 — ★ the divisibility pin (published Lemma 2.10's genre at `deg Φ₂ = 4`)

μ₃-minimality forces `4 ∣ deg`.  For `deg g = 4m + r` (`1 ≤ r ≤ 3`), the refuter is
`f := g·Q − Φ₂^(m+1)` with `Q := Φ₂^(m+1) /ₘ g`: the division identity gives `f = −(Φ₂^(m+1) %ₘ g)`
of degree `< deg g`, while the grade comparison `μ₃(g·Q) ≤ 21m + 2(c_r + c_{4−r}) ≤ 21m + 20
< 21(m+1) = μ₃(Φ₂^(m+1))` makes `f ∼μ₃ g·Q` — so `g ∣μ₃ f`, violating minimality. -/

/-- ★ **the divisibility pin**: a monic μ₃-minimal polynomial has degree divisible by 4. -/
theorem s2Mu3Minimal_natDegree_four_dvd {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu3Minimal h2 hq g) : 4 ∣ g.natDegree := by
  by_contra hndvd
  obtain ⟨m, r, hr1, hr3, hd⟩ : ∃ m r, 1 ≤ r ∧ r ≤ 3 ∧ g.natDegree = 4 * m + r :=
    ⟨g.natDegree / 4, g.natDegree % 4, by omega, by omega, by omega⟩
  obtain ⟨hAmon, hAdeg⟩ := dev_phi2_top_monic h2 hq m g r hr1 hr3 hmon hd
  -- the divisor and its complement
  have hΦpmon : ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)).Monic :=
    (phi2_monic h2 hq).pow _
  have hΦpdeg : ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)).natDegree
      = 4 * (m + 1) := by
    rw [Polynomial.natDegree_pow, phi2_natDegree h2 hq]
    ring
  have hdle : g.degree ≤ ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)).degree := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
      Polynomial.degree_eq_natDegree hΦpmon.ne_zero, hΦpdeg, hd]
    exact_mod_cast (by omega : 4 * m + r ≤ 4 * (m + 1))
  set Q := (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) /ₘ g with hQdef
  have hQmon : Q.Monic := monic_divByMonic hΦpmon hmon hdle
  have hQdeg : Q.natDegree = 4 - r := by
    rw [hQdef, Polynomial.natDegree_divByMonic _ hmon, hΦpdeg, hd]
    omega
  have hQself : Q %ₘ (s2DepthTwoKeyAt h2 hq 2) = Q :=
    (Polynomial.modByMonic_eq_self_iff (phi2_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [phi2_natDegree h2 hq, hQdeg]; omega))
  -- the two pin bounds, per residue
  obtain ⟨cg, cQ, hsum, hpg, hpQ⟩ : ∃ cg cQ : ℕ, cg + cQ ≤ 10 ∧
      dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g m ≤ (cg : ℕ∞) ∧
      dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) Q 0 ≤ (cQ : ℕ∞) := by
    have hpg_eq : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g m
        = dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) g m) 5 2 := by
      rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq]
    have hpQ_eq : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) Q 0
        = dvSupp (s2Frame h2 hq) Q 5 2 := by
      rw [dv2Pin, dev_zero_pin, hQself, dv2Hgt_eq_dvSupp h2 hq]
    rw [hpg_eq, hpQ_eq]
    interval_cases r
    · exact ⟨2, 7, by norm_num, dvSupp_le_of_monic_deg1 h2 hq hAmon hAdeg,
        dvSupp_le_of_monic_deg3 h2 hq hQmon (by omega)⟩
    · exact ⟨5, 5, by norm_num, dvSupp_le_of_monic_deg2 h2 hq hAmon hAdeg,
        dvSupp_le_of_monic_deg2 h2 hq hQmon (by omega)⟩
    · exact ⟨7, 2, by norm_num, dvSupp_le_of_monic_deg3 h2 hq hAmon hAdeg,
        dvSupp_le_of_monic_deg1 h2 hq hQmon (by omega)⟩
  -- grades
  obtain ⟨β, hβ⟩ := S2Mu3ExactGrade_exists h2 hq hmon.ne_zero
  obtain ⟨γ, hγ⟩ := S2Mu3ExactGrade_exists h2 hq hQmon.ne_zero
  have hβle : β ≤ 2 * cg + 21 * m := mu3_grade_le_of_pin_le h2 hq hβ hpg
  have hγle : γ ≤ 2 * cQ + 21 * 0 := mu3_grade_le_of_pin_le h2 hq hγ hpQ
  have hgQ : S2Mu3ExactGrade h2 hq (β + γ) (g * Q) := S2Mu3ExactGrade_mul h2 hq hβ hγ
  have hkp : S2Mu3ExactGrade h2 hq (21 * (m + 1))
      ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) :=
    S2Mu3ExactGrade_key_pow h2 hq (m + 1)
  have hlt : β + γ < 21 * (m + 1) := by omega
  -- the perturbation carries the product's initial form
  have hltc : ((β + γ : ℕ) : WithTop ℤ) < ((21 * (m + 1) : ℕ) : WithTop ℤ) := by
    exact_mod_cast hlt
  have hvgq : s2Hgt₃ h2 hq (g * Q) = ((β + γ : ℕ) : WithTop ℤ) := hgQ
  have hvkp : s2Hgt₃ h2 hq ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1))
      = ((21 * (m + 1) : ℕ) : WithTop ℤ) := hkp
  have hvf : s2Hgt₃ h2 hq (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1))
      = ((β + γ : ℕ) : WithTop ℤ) := by
    rw [sub_eq_add_neg, s2Hgt₃_add_eq h2 hq _ _ (by
        rw [s2Hgt₃_neg h2 hq, hvgq, hvkp]; exact hltc.ne), s2Hgt₃_neg h2 hq, hvgq, hvkp]
    exact min_eq_left hltc.le
  have hf_exact : S2Mu3ExactGrade h2 hq (β + γ)
      (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) := hvf
  have hf0 : g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) ≠ 0 :=
    S2Mu3ExactGrade_not_zero h2 hq hf_exact
  have hequiv : S2Mu3InitialEquiv h2 hq
      (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) (g * Q) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [show (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) - g * Q
          = -((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) from by ring,
        s2Hgt₃_neg h2 hq, hvkp, hvf]
      exact hltc
    · rw [hvf, hvgq]
  have hdvd : S2Mu3Dvd h2 hq g
      (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) := ⟨Q, hequiv⟩
  -- the degree collapse: the difference is minus the remainder
  have hmodid : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) %ₘ g + g * Q
      = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) :=
    Polynomial.modByMonic_add_div ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)) g
  have hfeq : g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)
      = -((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) %ₘ g) := by
    linear_combination hmodid
  have hfdeg : (g * Q - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1)).natDegree
      < g.natDegree := by
    have hR0 : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (m + 1) %ₘ g ≠ 0 := by
      intro h0
      rw [hfeq, h0, neg_zero] at hf0
      exact hf0 rfl
    rw [hfeq, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt _ hmon)
  exact hmin.2 _ hf0 hfdeg hdvd

/-! ## Part 3 — ★ the grade pin (published Lemma 2.11's invariant at slope `21/4`) -/

/-- ★ **the grade pin**: a monic μ₃-minimal polynomial has exact grade `21·(deg g/4)`. -/
theorem s2Mu3Minimal_exactGrade {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu3Minimal h2 hq g) :
    S2Mu3ExactGrade h2 hq (21 * (g.natDegree / 4)) g := by
  have h4 := s2Mu3Minimal_natDegree_four_dvd h2 hq hmon hmin
  set m := g.natDegree / 4 with hm
  have hd : g.natDegree = 4 * m := by omega
  obtain ⟨β, hβ⟩ := S2Mu3ExactGrade_exists h2 hq hmon.ne_zero
  have hle : β ≤ 2 * 0 + 21 * m :=
    mu3_grade_le_of_pin_le h2 hq hβ
      (le_of_eq (dv2Pin_top_of_monic_mul_four h2 hq hmon hd))
  rcases (show β ≤ 21 * m from by omega).lt_or_eq with hlt | heq
  · -- strictly below the top term: the truncation `g − Φ₂^m` refutes minimality
    exfalso
    have hkp : S2Mu3ExactGrade h2 hq (21 * m)
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) :=
      S2Mu3ExactGrade_key_pow h2 hq m
    rcases eq_or_ne (g - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) 0 with hf0 | hf0
    · have hg : g = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m := sub_eq_zero.mp hf0
      rw [hg] at hβ
      exact absurd (S2Mu3ExactGrade_unique h2 hq hβ hkp) (by omega)
    · have hltc : ((β : ℕ) : WithTop ℤ) < ((21 * m : ℕ) : WithTop ℤ) := by
        exact_mod_cast hlt
      have hvg : s2Hgt₃ h2 hq g = ((β : ℕ) : WithTop ℤ) := hβ
      have hvk : s2Hgt₃ h2 hq ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m)
          = ((21 * m : ℕ) : WithTop ℤ) := hkp
      have hvf : s2Hgt₃ h2 hq (g - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m)
          = ((β : ℕ) : WithTop ℤ) := by
        rw [sub_eq_add_neg, s2Hgt₃_add_eq h2 hq _ _ (by
            rw [s2Hgt₃_neg h2 hq, hvg, hvk]; exact hltc.ne), s2Hgt₃_neg h2 hq, hvg, hvk]
        exact min_eq_left hltc.le
      have hequiv : S2Mu3InitialEquiv h2 hq
          (g - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) g := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [show (g - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) - g
              = -((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) from by ring,
            s2Hgt₃_neg h2 hq, hvk, hvf]
          exact hltc
        · rw [hvf, hvg]
      have hdvd : S2Mu3Dvd h2 hq g (g - (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m) :=
        ⟨1, by rw [mul_one]; exact hequiv⟩
      have hkm : ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m).Monic :=
        (phi2_monic h2 hq).pow m
      have hdeg_eq : g.degree = ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ m).degree := by
        rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
          Polynomial.degree_eq_natDegree hkm.ne_zero, Polynomial.natDegree_pow,
          phi2_natDegree h2 hq, hd, Nat.mul_comm]
      have hdlt := Polynomial.degree_sub_lt hdeg_eq hmon.ne_zero
        (by rw [hmon.leadingCoeff, hkm.leadingCoeff])
      exact hmin.2 _ hf0 (Polynomial.natDegree_lt_natDegree hf0 hdlt) hdvd
  · rw [← heq]
    exact hβ

/-! ## Part 4 — the graded-piece IFF (file-local copies of M3-KP4's private lemmas)

`C132kp4` proved these for the carried-key argument but kept them private; the statements
and proofs below are its verbatim file-local copies (same public ingredient set). -/

private theorem s2Mu3GradedRes_neg_of_le {β : ℕ} {g : Polynomial O}
    (hg : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) g 21 2) :
    s2Mu3GradedRes h2 hq β (-g) = -s2Mu3GradedRes h2 hq β g := by
  have hneg : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (-g) 21 2 := by
    rw [dv2Supp_neg _ (s2Φ₂_monic h2 hq)]
    exact hg
  have hsum := s2Mu3GradedRes_add_of_le h2 hq hg hneg
  rw [add_neg_cancel, s2Mu3GradedRes_zero] at hsum
  linear_combination hsum.symm

private theorem initialEquiv_iff_gradedRes {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hh : S2Mu3ExactGrade h2 hq β h) :
    S2Mu3InitialEquiv h2 hq g h ↔
      s2Mu3GradedRes h2 hq β g = s2Mu3GradedRes h2 hq β h := by
  have hvg : s2Hgt₃ h2 hq g = (β : WithTop ℤ) := hg
  have hvh : s2Hgt₃ h2 hq h = (β : WithTop ℤ) := hh
  constructor
  · intro hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · have habove : S2Mu3AboveGrade h2 hq β (g - h) := by
        show (β : WithTop ℤ) < s2Hgt₃ h2 hq (g - h)
        rw [← hvg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu3GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu3GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      exact hadd
    · exact absurd hg0 (S2Mu3ExactGrade_not_zero h2 hq hg)
  · intro hres
    rcases eq_or_ne (g - h) 0 with hgh0 | hgh0
    · rw [sub_eq_zero.mp hgh0]
      exact S2Mu3InitialEquiv_refl h2 hq h
    · have hnegh : S2Mu3ExactGrade h2 hq β (-h) := by
        rw [S2Mu3ExactGrade_iff_dv2Supp, dv2Supp_neg _ (s2Φ₂_monic h2 hq)]
        exact (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh
      have hvneg : s2Hgt₃ h2 hq (-h) = (β : WithTop ℤ) := hnegh
      have hge : (β : WithTop ℤ) ≤ s2Hgt₃ h2 hq (g - h) := by
        have hmin := s2Hgt₃_add_ge h2 hq g (-h)
        rw [← sub_eq_add_neg, hvg, hvneg, min_self] at hmin
        exact hmin
      rcases hge.lt_or_eq with hlt | heqv
      · refine Or.inl ⟨?_, hvg.trans hvh.symm⟩
        rw [hvg]
        exact hlt
      · have hexact : S2Mu3ExactGrade h2 hq β (g - h) := heqv.symm
        have hne := s2Mu3GradedRes_ne_zero_of_exact h2 hq hexact
        have hadd := s2Mu3GradedRes_add_of_le h2 hq
          (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg).symm)
          (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hnegh).symm)
        rw [← sub_eq_add_neg,
          s2Mu3GradedRes_neg_of_le h2 hq
            (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm),
          hres, add_neg_cancel] at hadd
        exact absurd hadd hne

/-! ## Part 5 — the on-line coefficient tooth (file-local copies of M3-KP4's privates) -/

private theorem innerGradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 4) (ht : 0 < t) :
    (s2GradedRes h2 hq m A).coeff t = 0 := by
  rw [s2GradedRes_coeff]
  refine s2GradedCoeff_eq_zero_of_not_slotOnGrade h2 hq ?_
  intro hgate
  obtain ⟨m', hm', -⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  have hdev : dev (s2Frame h2 hq).key A (m % 2 + 2 * t) = 0 :=
    dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos A _
      (by rw [key_natDegree_two h2 hq]; omega)
  have htop : dvHgt (s2Frame h2 hq) A (m % 2 + 2 * t) = ⊤ := by
    rw [dvHgt, hdev]
    exact (s2Frame h2 hq).stageHeight_zero
  rw [htop] at hm'
  exact WithTop.top_ne_coe hm'

private theorem eval_one_innerGradedRes {m : ℕ} {A : Polynomial O} (hA : A.natDegree < 4) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
      (s2GradedRes h2 hq m A).coeff 0 := by
  have hconst : s2GradedRes h2 hq m A =
      Polynomial.C ((s2GradedRes h2 hq m A).coeff 0) := by
    refine Polynomial.ext fun t => ?_
    match t with
    | 0 => simp
    | t + 1 =>
        rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
        exact innerGradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)
  calc
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
        Polynomial.eval 1 (Polynomial.C ((s2GradedRes h2 hq m A).coeff 0)) :=
      congrArg _ hconst
    _ = (s2GradedRes h2 hq m A).coeff 0 := Polynomial.eval_C

private theorem mu3Coeff_ne_zero_of_slot {β s : ℕ} {g : Polynomial O}
    (hgate : S2Mu3SlotOnGrade h2 hq β g s) :
    s2Mu3Coeff h2 hq β g (s / 2) ≠ 0 := by
  let A := dev (s2DepthTwoKeyAt h2 hq 2) g s
  have hinner : S2ExactGrade h2 hq ((β - 21 * s) / 2) A :=
    s2Mu3SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : A.natDegree < 4 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g s)
      rwa [s2Φ₂_natDegree h2 hq] at h
  have hcoeff := s2Mu3Coeff_slot h2 hq hgate
  rw [s2Mu3Eps_eq_one, one_mul, eval_one_innerGradedRes h2 hq hdeg] at hcoeff
  rw [hcoeff]
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hinner hdeg

/-! ## Part 6 — the deflation lemma (file-local copy of M3-KP4's private remainder
argument): an off-line slot 0 makes the development key `Φ₂` a μ₃-divisor. -/

private theorem mu3Dvd_phi2_of_not_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu3ExactGrade h2 hq β f) (hgate : ¬ S2Mu3SlotOnGrade h2 hq β f 0) :
    S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) f := by
  let phi := s2DepthTwoKeyAt h2 hq 2
  have hmon : (phi : Polynomial O).Monic := s2Φ₂_monic h2 hq
  have hmod : f %ₘ phi + phi * (f /ₘ phi) = f := Polynomial.modByMonic_add_div f phi
  rcases eq_or_ne (f %ₘ phi) 0 with hr0 | hr0
  · exact S2Mu3Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  have hdegr : (f %ₘ phi).natDegree < 4 := by
    have h := Polynomial.natDegree_lt_natDegree hr0 (Polynomial.degree_modByMonic_lt f hmon)
    rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq] at h
    exact h
  have hdevr : dev phi (f %ₘ phi) 0 = f %ₘ phi := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff hmon).mpr (Polynomial.degree_modByMonic_lt f hmon)
  have hsupp_r : dv2Supp ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) 21 2 =
      2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 := by
    rw [dv2Supp_eq_inf_range ((s2Tower h2 hq).levelDatum h2) hmon
      (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; norm_num)
      (by norm_num : (0 : ℕ) < 2) _ (M := 4) hdegr,
      show Finset.range 4 = {0, 1, 2, 3} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton]
    have hpin (j : ℕ) (hj : 0 < j) :
        dv2Pin ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) j = ⊤ := by
      rw [dv2Pin, dev_eq_zero_of_lt hmon
        (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; norm_num) _ j
        (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; omega)]
      exact Uniformity.Density.Tower.dv2Hgt_zero _
    simp only [hpin 1 (by norm_num), hpin 2 (by norm_num), hpin 3 (by norm_num),
      C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
      Nat.cast_zero, mul_zero, add_zero]
    simp only [min_eq_left le_top]
    rw [show dv2Pin ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) 0 =
        dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 by
      rw [dv2Pin, hdevr, dv2Pin, dev_zero_pin]]
  have hle : (β : ℕ∞) ≤ 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 := by
    have hterm := C132nv2.dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [phi2_natDegree h2 hq]; norm_num)
      f 21 (by norm_num : (0 : ℕ) < 2) 0
    rw [(S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hf] at hterm
    simpa using hterm
  have hne : 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 ≠ (β : ℕ∞) := by
    intro heq
    have hfin : dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at heq
      exact WithTop.top_ne_coe heq
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    refine hgate ((s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨m, hm.symm, ?_⟩)
    rw [← hm, nsmul_eq_mul] at heq
    have h2m : (2 * m : ℕ) = β := by exact_mod_cast heq
    omega
  have hltE : (β : ℕ∞) < 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 :=
    lt_of_le_of_ne hle (Ne.symm hne)
  have hgt : s2Hgt₃ h2 hq f < s2Hgt₃ h2 hq (f %ₘ phi) := by
    have hvf : s2Hgt₃ h2 hq f = (β : WithTop ℤ) := hf
    rw [hvf, s2Hgt₃_eq_dv2Supp, hsupp_r,
      show (β : WithTop ℤ) = C130s6.toZ (β : ℕ∞) by norm_cast]
    exact toZ_lt_toZ_iff.mpr hltE
  have hkw : phi * (f /ₘ phi) = f - f %ₘ phi := (sub_eq_of_eq_add' hmod.symm).symm
  have hval_kw : s2Hgt₃ h2 hq (phi * (f /ₘ phi)) = s2Hgt₃ h2 hq f := by
    rw [hkw, sub_eq_add_neg,
      s2Hgt₃_add_eq h2 hq _ _ (by rw [s2Hgt₃_neg h2 hq]; exact ne_of_lt hgt),
      s2Hgt₃_neg h2 hq]
    exact min_eq_left (le_of_lt hgt)
  refine ⟨f /ₘ phi, Or.inl ⟨?_, hval_kw.symm⟩⟩
  rw [show f - phi * (f /ₘ phi) = f %ₘ phi by rw [hkw]; ring]
  exact hgt

/-! ## Part 7 — ★ the slot-0 pin (published Lemma 5.1's `s(g) = 0` clause)

A μ₃ key of degree `> 4` has slot 0 ON the grade line — one-step deflation: an off-line
slot 0 factors the initial form as `Φ₂·q`; primality forces `g ∣μ₃ Φ₂` (killed by
minimality, `deg Φ₂ = 4 < deg g`) or `g ∣μ₃ q` (killed by the grade ledger:
`β = 21 + γ` and `γ = β + γ′` cannot both hold in ℕ). -/

/-- ★ **the slot-0 pin**: a μ₃ key polynomial of degree `> 4` has slot 0 on its grade
line. -/
theorem s2Mu3KeyPoly_slotZero {g : Polynomial O} {β : ℕ} (hkey : S2Mu3KeyPoly h2 hq g)
    (hβ : S2Mu3ExactGrade h2 hq β g) (hdeg : 4 < g.natDegree) :
    S2Mu3SlotOnGrade h2 hq β g 0 := by
  obtain ⟨hmon, hmin, -, -, hprime⟩ := hkey
  by_contra hgate
  obtain ⟨q, hq'⟩ := mu3Dvd_phi2_of_not_slotZero h2 hq hβ hgate
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq'
    exact hmon.ne_zero ((S2Mu3InitialEquiv_zero_right h2 hq).mp hq')
  have hprod : S2Mu3Dvd h2 hq g ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * q) :=
    ⟨1, by rw [mul_one]; exact S2Mu3InitialEquiv_symm h2 hq hq'⟩
  rcases hprime _ _ hprod with hL | hR
  · -- `g ∣μ₃ Φ₂` refutes minimality
    exact hmin.2 _ (phi2_monic h2 hq).ne_zero
      (by rw [phi2_natDegree h2 hq]; omega) hL
  · -- `g ∣μ₃ q` refutes the grade ledger
    obtain ⟨q', hq''⟩ := hR
    have hq'0 : q' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq''
      exact hq0 ((S2Mu3InitialEquiv_zero_right h2 hq).mp hq'')
    obtain ⟨γ, hγ⟩ := S2Mu3ExactGrade_exists h2 hq hq0
    obtain ⟨γ', hγ'⟩ := S2Mu3ExactGrade_exists h2 hq hq'0
    have hkq : S2Mu3ExactGrade h2 hq (21 + γ)
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * q) :=
      S2Mu3ExactGrade_mul h2 hq (tooth_Φ₂ h2 hq) hγ
    have hkqβ : S2Mu3ExactGrade h2 hq β
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * q) :=
      S2Mu3ExactGrade_of_initialEquiv h2 hq hβ hq'
    have h1 : β = 21 + γ := S2Mu3ExactGrade_unique h2 hq hkqβ hkq
    have hgq' : S2Mu3ExactGrade h2 hq (β + γ') (g * q') :=
      S2Mu3ExactGrade_mul h2 hq hβ hγ'
    have hq2 : S2Mu3ExactGrade h2 hq (β + γ') q :=
      S2Mu3ExactGrade_of_initialEquiv h2 hq hgq' (S2Mu3InitialEquiv_symm h2 hq hq'')
    have h2' : γ = β + γ' := S2Mu3ExactGrade_unique h2 hq hγ hq2
    omega

/-! ## Part 8 — the key-structure master (published Lemma 5.3, one level up)

For a μ₃ key `g` with `m := deg g/4`: `4 ∣ deg g`, exact grade `21m`, the slot of the
grade's own parity on the line (slot 0 for proper keys, the top slot for the `∼ Φ₂`
fiber), and the parity dichotomy `m = 1 ∨ 2 ∣ m`. -/

private theorem key_master {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    4 ∣ g.natDegree
    ∧ S2Mu3ExactGrade h2 hq (21 * (g.natDegree / 4)) g
    ∧ S2Mu3SlotOnGrade h2 hq (21 * (g.natDegree / 4)) g (g.natDegree / 4 % 2)
    ∧ (g.natDegree / 4 = 1 ∨ 2 ∣ g.natDegree / 4) := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  have h4 := s2Mu3Minimal_natDegree_four_dvd h2 hq hmon hmin
  have hβ := s2Mu3Minimal_exactGrade h2 hq hmon hmin
  have hpos : 0 < g.natDegree := hmin.1
  rcases Nat.lt_or_ge 4 g.natDegree with hbig | hsmall
  · -- `deg g > 4`: the slot-0 pin fires, the grade is even
    have h0 := s2Mu3KeyPoly_slotZero h2 hq ⟨hmon, hmin, hirr⟩ hβ hbig
    have hm2 : 2 ∣ g.natDegree / 4 := by
      obtain ⟨c, -, hc⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp h0
      omega
    refine ⟨h4, hβ, ?_, Or.inr hm2⟩
    rw [show g.natDegree / 4 % 2 = 0 from by omega]
    exact h0
  · -- `deg g = 4`: the top slot IS the parity slot (grade 21, odd)
    have hd4 : g.natDegree = 4 := by omega
    have htop := slot_top_of_monic_mul_four h2 hq hmon (m := 1) (by omega)
    refine ⟨h4, hβ, ?_, Or.inl (by omega)⟩
    rw [show g.natDegree / 4 = 1 from by omega]
    exact htop

/-- **the grade of a μ₃ key polynomial**: `μ₃(g) = 21·(deg g/4)` (published Lemma 2.11 at
keys; the equal-value input of the Prop 5.6 assembly is DERIVED, never hypothesized). -/
theorem s2Mu3KeyPoly_exactGrade {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    S2Mu3ExactGrade h2 hq (21 * (g.natDegree / 4)) g :=
  (key_master h2 hq hkey).2.1

/-- **the residual scalar of a μ₃ key polynomial is nonzero** (published Lemma 5.3's
`s(g) = 0` read at the graded residual: the lowest `y`-coefficient lives). -/
theorem s2Mu3KeyPoly_gradedRes_coeff_zero_ne_zero {g : Polynomial O}
    (hkey : S2Mu3KeyPoly h2 hq g) :
    (s2Mu3GradedRes h2 hq (21 * (g.natDegree / 4)) g).coeff 0 ≠ 0 := by
  obtain ⟨-, -, hlow, -⟩ := key_master h2 hq hkey
  have h := mu3Coeff_ne_zero_of_slot h2 hq hlow
  rw [show g.natDegree / 4 % 2 / 2 = 0 from by omega] at h
  rw [s2Mu3GradedRes_coeff]
  exact h

/-- ★ **the strip is trivial on μ₃ keys**: the normalized residual of a key polynomial IS
its graded residual at the pinned grade — the trailing `y`-power is `0`. -/
theorem s2Mu3KeyPoly_normRes_eq_gradedRes {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    s2Mu3NormRes h2 hq g = s2Mu3GradedRes h2 hq (21 * (g.natDegree / 4)) g := by
  have hβ := s2Mu3KeyPoly_exactGrade h2 hq hkey
  have hntd : (s2Mu3GradedRes h2 hq (21 * (g.natDegree / 4)) g).natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero
      (s2Mu3KeyPoly_gradedRes_coeff_zero_ne_zero h2 hq hkey))
  rw [s2Mu3NormRes_of_exact h2 hq hβ, hntd]
  exact Function.iterate_zero_apply _ _

/-- **the residual degree of a μ₃ key polynomial**: `deg R₄(g) = deg g/8` (published
Corollary 4.4's `s′ − s = e·deg R` at `s = 0`, `e = 2`, with `deg g = 4s′`). -/
theorem s2Mu3KeyPoly_normRes_natDegree {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    (s2Mu3NormRes h2 hq g).natDegree = g.natDegree / 8 := by
  have h4 := (key_master h2 hq hkey).1
  rw [s2Mu3KeyPoly_normRes_eq_gradedRes h2 hq hkey]
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [s2Mu3GradedRes_coeff]
    refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
    rw [dv2Pin, dev_eq_zero_of_lt (phi2_monic h2 hq)
      (by rw [phi2_natDegree h2 hq]; norm_num)]
    · exact Uniformity.Density.Tower.dv2Hgt_zero _
    · rw [phi2_natDegree h2 hq]
      omega
  · have htop := slot_top_of_monic_mul_four h2 hq hkey.1
      (m := g.natDegree / 4) (by omega)
    have h := mu3Coeff_ne_zero_of_slot h2 hq htop
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [s2Mu3GradedRes_coeff, show g.natDegree / 8 = g.natDegree / 4 / 2 from by omega]
    exact h

/-- ★ **the μ₃ degree dictionary** (published Lemma 5.3's degree display at
`(e, m) = (2, 2)`, one level up; the `∼ Φ₂` fiber at `deg g = 4`): a μ₃ key polynomial's
degree is determined by its normalized residual — `deg g/4 = 1` or
`deg g/4 = 2·deg R₄(g)` (equivalently `deg g = 8·deg R₄(g)`). -/
theorem s2Mu3KeyPoly_natDegree_pin {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    g.natDegree / 4 = 1 ∨ g.natDegree / 4 = 2 * (s2Mu3NormRes h2 hq g).natDegree := by
  obtain ⟨h4, -, -, hpar⟩ := key_master h2 hq hkey
  have hdeg := s2Mu3KeyPoly_normRes_natDegree h2 hq hkey
  rcases hpar with h1 | h2'
  · exact Or.inl h1
  · right
    rw [hdeg]
    omega

/-! ## Part 9 — ★★ M3-KP6b: the converse, the `hconv` discharge, and the fired calculus -/

/-- ★★ **M3-KP6b, the converse** (published Prop 5.6's (2)→(3), the hard direction, at the
μ₃ operators): residual equality forces initial equivalence for μ₃ key polynomials.  The
dictionary forces equal degrees, hence equal grades `21·(deg/4)`; the trivial strip turns
residual equality into graded equality at the common exact grade; the graded-piece IFF
fires backward.  The zero clause never arises — keys are monic. -/
theorem s2Mu3_residual_to_initial {g h : Polynomial O} (hkg : S2Mu3KeyPoly h2 hq g)
    (hkh : S2Mu3KeyPoly h2 hq h) (hres : s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h) :
    S2Mu3InitialEquiv h2 hq g h := by
  have hpin_g := s2Mu3KeyPoly_natDegree_pin h2 hq hkg
  have hpin_h := s2Mu3KeyPoly_natDegree_pin h2 hq hkh
  have hdg := s2Mu3KeyPoly_normRes_natDegree h2 hq hkg
  have hdh := s2Mu3KeyPoly_normRes_natDegree h2 hq hkh
  have h4g := (key_master h2 hq hkg).1
  have h4h := (key_master h2 hq hkh).1
  have hpos_g : 0 < g.natDegree := hkg.2.1.1
  have hpos_h : 0 < h.natDegree := hkh.2.1.1
  rw [hres] at hpin_g hdg
  have hd : g.natDegree = h.natDegree := by
    rcases hpin_g with h1g | h2g <;> rcases hpin_h with h1h | h2h <;> omega
  have hβg := s2Mu3KeyPoly_exactGrade h2 hq hkg
  have heqg := s2Mu3KeyPoly_normRes_eq_gradedRes h2 hq hkg
  rw [hd] at hβg heqg
  exact (initialEquiv_iff_gradedRes h2 hq hβg (s2Mu3KeyPoly_exactGrade h2 hq hkh)).mpr
    (by rw [← heqg, ← s2Mu3KeyPoly_normRes_eq_gradedRes h2 hq hkh, hres])

/-- ★★★ **M3-KP6b — the `hconv` hypothesis of `C132fd0.s2SourceLawsTwo_of`, DISCHARGED**
(byte-identical to the hypothesis shape; see `C132fd0.lean:115`). -/
theorem s2Mu3_hconv :
    ∀ g h : Polynomial O,
      S2Mu3KeyPoly h2 hq g → S2Mu3KeyPoly h2 hq h →
        s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h → S2Mu3InitialEquiv h2 hq g h :=
  fun _ _ hkg hkh hres => s2Mu3_residual_to_initial h2 hq hkg hkh hres

/-- ★★ the assembled Proposition-5.6 field at μ₃ (both directions; forward is M3-KP6's
universal `s2Mu3_initial_to_residual`). -/
theorem s2Mu3_initial_iff_residual :
    ∀ g h : Polynomial O, S2Mu3KeyPoly h2 hq g → S2Mu3KeyPoly h2 hq h →
      (S2Mu3InitialEquiv h2 hq g h ↔ s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h) :=
  fun _ _ hkg hkh =>
    ⟨s2Mu3_initial_to_residual h2 hq, s2Mu3_residual_to_initial h2 hq hkg hkh⟩

/-- ★★★ **THE UNCONDITIONAL DEPTH-2 CALCULUS**: M3-RP10b's conditional
`s2Mu3_calculus_nonempty_of_conv` fired with the landed `hconv` — the μ₃ campaign
closes. -/
theorem s2Mu3_calculus_nonempty :
    Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  C132rp10b.s2Mu3_calculus_nonempty_of_conv h2 hq (s2Mu3_hconv h2 hq)

end S2

end Uniformity.Density.Tower.C132kp6b

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3Minimal_natDegree_four_dvd
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3Minimal_exactGrade
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_slotZero
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_exactGrade
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_gradedRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_normRes_eq_gradedRes
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_normRes_natDegree
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3KeyPoly_natDegree_pin
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3_residual_to_initial
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3_hconv
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3_initial_iff_residual
#print axioms Uniformity.Density.Tower.C132kp6b.s2Mu3_calculus_nonempty

end AxCheck
