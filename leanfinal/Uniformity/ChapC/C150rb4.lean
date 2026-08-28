/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C16
import Uniformity.ChapC.C47
import Uniformity.ChapC.C56a
import Uniformity.ChapC.C83
import Uniformity.ChapC.C131v
import Uniformity.ChapB.B35a

/-!
# Uniformity.ChapC.C150rb4 — RB3R: `refine_invariants` re-based against the Hensel engine

**Unit RB3R (2026-08-28).** Re-adjudication of the C.56 `refine_invariants` gap
(`C150rb3.lean`'s BLOCKED note, carried by `runs/wave-c/verdict_C93T.md` row (2)) against
the completed dv-graded Hensel engine (C133mh0–mh15, C134*).  Full mapping table and the
outcome record: `runs/wave-c/verdict_RB3R.md`.

## What lands here (the derivable clauses of the signed conclusion)

For `Φ₂⁺ := composedKey T - k2DigitLift T s lam` (the corrected key of the signed
`refine_invariants`, leanspec `ChapC.lean:2163`):

* `natDegree_k2DigitLift_lt` — the lift's degree bound `deg(k2DigitLift T s m) < T.D₂`,
  coefficient-independent (pure exponent numerology: C.16 `slotIdx_spec`'s `i < e₁`,
  `towerSolve_lt`'s `b < e₂`).  This is the `.27` rider "deg lift < D₂ always" as a
  theorem.
* `corrected_monic`, `corrected_natDegree` — **conjuncts 1 and 2 of the signed
  conclusion**, with STRICTLY FEWER hypotheses (no `f`, no side/residual data: any `s`,
  any `lam`).
* `corrected_top_digit` — IsTestKey conjunct 3 at `Φ₂⁺` (`dev F.key Φ₂⁺ (e₂f₂) = 1`),
  same hypothesis-light form.
* `dev_k2DigitLift_off_lattice` + `corrected_offLattice_digit` — IsTestKey conjunct 4 at
  `Φ₂⁺`, CONDITIONAL on `T.e₂ ∣ lam`: on the lattice the lift's `F.key`-digits sit at
  abscissae `e₂·t` only, and the off-lattice digits of `Φ₂⁺` vanish exactly.

## What does NOT land (the honest remainder — see verdict_RB3R.md)

IsTestKey conjunct 4 (at `e₂ ∤ lam`) and conjunct 5's zero-branch are NOT provable for
`Φ₂⁺`: every term of `k2DigitLift T s lam` sits at `F.key`-exponent `b₀ + e₂t` with
`b₀ = towerSolve u₂ e₂ (lam - Δ) ≠ 0` iff `e₂ ∤ lam` (`Δ ≡ 0 (mod e₂)`), so the
corrected key carries the lift's own digits at off-lattice abscissae (conjunct 4's
positions), and at zero-label slots (`(towerLabel T).coeff t = 0`) the corrected digit
is `-`(the lift's slot digit), which vanishes only when the `k2Coord`-read of `s` at `t`
vanishes.  Neither exact zero is implied by the signed hypotheses.  This is a
STATEMENT-level finding about the signed `IsTestKey` conjunct (the source clause
`EFF.GENTOW1.28` claims the perturbation-stable package — monic, degree, one-sidedness,
residual, side digits — NOT the exact-zero test-family shape), not a missing-mathematics
gap: the perturbation-stable package is exactly what C133mh0's M4 family (MH.6)
preserves.  Conjunct 5's nonzero branch (exact slot heights + twist reads preserved) is
derivable from landed atoms (C131ae `twistRead_add_eq_left_of_lt` + the grade-`lam`
height floor of the lift) and is priced in the verdict as the reusable remainder for the
repaired statement.

## DEPENDS

C.16 (`slotIdx_spec`) · C.47 (`composedKey_monic/_natDegree/_top_digit/_offLattice_digit`)
· C.56a (`k2DigitLift`, `n2Exp`) · C.83 (`towerSolve`) · C131v (`dev_sub`) ·
B.04/B32a/B35a (`dev` calculus: `dev_eq_zero_of_lt`, `dev_add_of_monic`,
`dev_mul_pow`, `dev_mul_pow_of_lt`).

## Status

Sorry-free, axiom-free (Lean core only) — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C150rb4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density.Leaf
open Uniformity.Density.Tower
open Uniformity.Density.Tower.C131v (dev_sub)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Part 0 — `towerSolve` bounds (C.83's solve, the two small facts every exponent
numerology below consumes) -/

/-- The C.83 solve is bounded by the modulus: `towerSolve u e k < e` (for `0 < e`; the
junk branch returns `0`). -/
theorem towerSolve_lt {e : ℕ} (he : 0 < e) (u k : ℕ) : towerSolve u e k < e := by
  unfold towerSolve
  cases hfind : (List.range e).find? (fun b => (b * u) % e == k % e) with
  | none => simpa using he
  | some b =>
    have hb : b ∈ List.range e := List.mem_of_find?_eq_some hfind
    simpa using List.mem_range.mp hb

/-- On the lattice the solve is `0`: `e ∣ k → towerSolve u e k = 0` (the first candidate
`b = 0` already satisfies `0·u ≡ k (mod e)`; at `e = 0` the junk branch returns `0`). -/
theorem towerSolve_eq_zero_of_dvd {e k : ℕ} (h : e ∣ k) (u : ℕ) : towerSolve u e k = 0 := by
  unfold towerSolve
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  · have hk : k % e = 0 := by
      obtain ⟨c, rfl⟩ := h
      exact Nat.mul_mod_right e c
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp he)
    rw [List.range_succ_eq_map, List.find?_cons_of_pos (by simp [hk])]
    rfl

/-! ### Part 0b — the `n2Exp` component bounds (definitional bridges + the two bounds) -/

/-- `n2Exp`'s middle component IS the frame slot index (definitional). -/
theorem n2Exp_snd_fst_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) :
    (n2Exp T m).2.1
      = F.slotIdx ((m - towerSolve T.u₂ T.e₂ m * T.u₂) / T.e₂) := rfl

/-- `n2Exp`'s last component IS the `(u₂, e₂)` solve (definitional). -/
theorem n2Exp_snd_snd_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) :
    (n2Exp T m).2.2 = towerSolve T.u₂ T.e₂ m := rfl

/-- The `X`-exponent component of `n2Exp` is `< e₁` (C.16's `slotIdx_spec`). -/
theorem n2Exp_snd_fst_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : (n2Exp T m).2.1 < F.e₁ :=
  (F.slotIdx_spec _).1

/-- The `F.key`-exponent component of `n2Exp` is `< e₂` (`towerSolve_lt`). -/
theorem n2Exp_snd_snd_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : (n2Exp T m).2.2 < T.e₂ :=
  towerSolve_lt T.he₂ _ _

/-! ### Part 0c — private `dev` glue (Finset-sum additivity; the B35a/B04 atoms are
per-pair, the corpus keeps their `Finset` glue local — the C133mh0 precedent) -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem dev_zero' {φ : Polynomial O} (j : ℕ) :
    dev φ (0 : Polynomial O) j = 0 := by
  induction j with
  | zero => exact Polynomial.zero_modByMonic φ
  | succ j ih => rw [dev, Polynomial.zero_divByMonic]; exact ih

private theorem dev_finset_sum {φ : Polynomial O} (hφ : φ.Monic) {ι : Type*}
    (sfin : Finset ι) (g : ι → Polynomial O) (j : ℕ) :
    dev φ (∑ i ∈ sfin, g i) j = ∑ i ∈ sfin, dev φ (g i) j := by
  classical
  induction sfin using Finset.induction_on with
  | empty => simpa using dev_zero' j
  | @insert a sfin' ha ih =>
    rw [Finset.sum_insert ha, dev_add_of_monic hφ, ih, Finset.sum_insert ha]

/-! ### Part 1 — the lift's degree bound (`.27`'s "deg lift < D₂ always", now a theorem) -/

/-- The `X`-exponent of every lift term is `< D′ = e₁f₁` (no `F.key`-carry). -/
private theorem xexp_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (M : ℕ) {r : ℕ} (hr : r < F.f₁) :
    (n2Exp T M).2.1 + F.e₁ * r < F.e₁ * F.f₁ :=
  calc (n2Exp T M).2.1 + F.e₁ * r
      < F.e₁ + F.e₁ * r := Nat.add_lt_add_right (n2Exp_snd_fst_lt T M) _
    _ = F.e₁ * (r + 1) := by ring
    _ ≤ F.e₁ * F.f₁ := Nat.mul_le_mul le_rfl hr

/-- The `F.key`-exponent of every lift term is `< e₂f₂` (inside the digit window). -/
private theorem keyexp_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (M : ℕ) {t : ℕ} (ht : t < T.f₂) :
    (n2Exp T M).2.2 + T.e₂ * t < T.e₂ * T.f₂ :=
  calc (n2Exp T M).2.2 + T.e₂ * t
      < T.e₂ + T.e₂ * t := Nat.add_lt_add_right (n2Exp_snd_snd_lt T M) _
    _ = T.e₂ * (t + 1) := by ring
    _ ≤ T.e₂ * T.f₂ := Nat.mul_le_mul le_rfl ht

private theorem natDegree_C_mul_X_pow_le (c : O) (p : ℕ) :
    (Polynomial.C c * Polynomial.X ^ p).natDegree ≤ p :=
  le_trans Polynomial.natDegree_mul_le (by simp)

private theorem natDegree_term_le (F : KeyFrame O π) (c : O) (p q : ℕ) :
    (Polynomial.C c * Polynomial.X ^ p * F.key ^ q).natDegree
      ≤ p + q * (F.e₁ * F.f₁) := by
  have h1 : (Polynomial.C c * Polynomial.X ^ p).natDegree ≤ p :=
    le_trans Polynomial.natDegree_mul_le (by simp)
  have h2 : (F.key ^ q).natDegree = q * (F.e₁ * F.f₁) := by
    rw [Polynomial.natDegree_pow, F.hdeg]
  refine le_trans Polynomial.natDegree_mul_le ?_
  omega

/-- **The `K₂`-digit lift has degree `< D₂`,** coefficient-independently: every term
`C(c)·X^(i+e₁r)·F.key^(b+e₂t)` has `i < e₁` (C.16 `slotIdx_spec`), `r < f₁`, `b < e₂`
(`towerSolve_lt`), `t < f₂`, hence degree `≤ (i+e₁r) + (b+e₂t)·e₁f₁ < e₁f₁·e₂f₂ = D₂`.
This is the `.27` TERMINAL-display rider "deg lift < D₂ always" as a theorem. -/
theorem natDegree_k2DigitLift_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (m : ℕ) :
    (k2DigitLift T s m).natDegree < T.D₂ := by
  have hD2 : T.D₂ = (F.e₁ * F.f₁) * (T.e₂ * T.f₂) := rfl
  have hD2pos : 0 < T.D₂ := by
    rw [hD2]
    exact Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (Nat.mul_pos T.he₂ T.hf₂)
  have hbound : (k2DigitLift T s m).natDegree ≤ T.D₂ - 1 := by
    unfold k2DigitLift
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    have hr' : r < F.f₁ := Finset.mem_range.mp hr
    have ht' : t < T.f₂ := Finset.mem_range.mp ht
    set M := m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t) with hM
    have hterm := natDegree_term_le F
      (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r) * π ^ (n2Exp T M).1)
      ((n2Exp T M).2.1 + F.e₁ * r) ((n2Exp T M).2.2 + T.e₂ * t)
    have hlt : (n2Exp T M).2.1 + F.e₁ * r
        + ((n2Exp T M).2.2 + T.e₂ * t) * (F.e₁ * F.f₁) < T.D₂ := by
      have hq1 : (n2Exp T M).2.2 + T.e₂ * t + 1 ≤ T.e₂ * T.f₂ := keyexp_lt T M ht'
      calc (n2Exp T M).2.1 + F.e₁ * r
            + ((n2Exp T M).2.2 + T.e₂ * t) * (F.e₁ * F.f₁)
          < F.e₁ * F.f₁ + ((n2Exp T M).2.2 + T.e₂ * t) * (F.e₁ * F.f₁) :=
            Nat.add_lt_add_right (xexp_lt T M hr') _
        _ = ((n2Exp T M).2.2 + T.e₂ * t + 1) * (F.e₁ * F.f₁) := by ring
        _ ≤ (T.e₂ * T.f₂) * (F.e₁ * F.f₁) := Nat.mul_le_mul hq1 le_rfl
        _ = T.D₂ := by rw [hD2]; ring
    omega
  omega

/-! ### Part 2 — signed conjuncts 1 and 2: the corrected key is monic of degree `D₂` -/

/-- The C.48-pattern dictionary numeral: `keyDeg₂ = D₂` at the tower level datum. -/
theorem keyDeg₂_eq_D₂ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.levelDatum hπ).keyDeg₂ = T.D₂ := by
  have hr : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  rw [LevelDatum.keyDeg₂, hr, show (T.levelDatum hπ).ℓ = T.e₂ from rfl, TowerDatum.D₂]
  ring

private theorem natDegree_lift_lt_key {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (s : AdjoinRoot (towerLabel T)) (lam : ℕ) :
    (k2DigitLift T s lam).natDegree < (composedKey T).natDegree := by
  rw [composedKey_natDegree T hπ, keyDeg₂_eq_D₂ T hπ]
  exact natDegree_k2DigitLift_lt T s lam

/-- **Signed `refine_invariants`, conjunct 1** (with strictly fewer hypotheses): the
corrected key `Φ₂⁺ = Φ₂ - k2DigitLift T s lam` is monic — the lift's degree is `< D₂`
and `Φ₂` is monic of degree `D₂`. -/
theorem corrected_monic {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (s : AdjoinRoot (towerLabel T)) (lam : ℕ) :
    (composedKey T - k2DigitLift T s lam).Monic := by
  have hdd : (-(k2DigitLift T s lam)).degree < (composedKey T).degree := by
    rw [Polynomial.degree_neg]
    exact Polynomial.degree_lt_degree (natDegree_lift_lt_key T hπ s lam)
  have h := (composedKey_monic T).add_of_left hdd
  rwa [← sub_eq_add_neg] at h

/-- **Signed `refine_invariants`, conjunct 2** (with strictly fewer hypotheses): the
corrected key keeps degree `D₂` exactly. -/
theorem corrected_natDegree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (s : AdjoinRoot (towerLabel T)) (lam : ℕ) :
    (composedKey T - k2DigitLift T s lam).natDegree = T.D₂ := by
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (natDegree_lift_lt_key T hπ s lam),
    composedKey_natDegree T hπ, keyDeg₂_eq_D₂ T hπ]

/-! ### Part 3 — IsTestKey conjunct 3 at the corrected key: the top digit is `1` -/

/-- **IsTestKey conjunct 3 at `Φ₂⁺`:** the leading `F.key`-digit of the corrected key is
`1` — the lift's digits all sit strictly below abscissa `e₂f₂` (degree bound + B.04),
so the top digit is `Φ₂`'s own (C.47). -/
theorem corrected_top_digit {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (lam : ℕ) :
    dev F.key (composedKey T - k2DigitLift T s lam) (T.e₂ * T.f₂) = 1 := by
  have hkeypos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  have hz : dev F.key (k2DigitLift T s lam) (T.e₂ * T.f₂) = 0 := by
    refine dev_eq_zero_of_lt F.hmonic hkeypos _ _ ?_
    rw [F.hdeg]
    calc (k2DigitLift T s lam).natDegree
        < T.D₂ := natDegree_k2DigitLift_lt T s lam
      _ = T.e₂ * T.f₂ * (F.e₁ * F.f₁) := by rw [TowerDatum.D₂]; ring
  rw [dev_sub F.hmonic, composedKey_top_digit T, hz, sub_zero]

/-! ### Part 4 — IsTestKey conjunct 4 at the corrected key, conditional on `e₂ ∣ lam` -/

/-- **The lift's digit support in the lattice case:** if `T.e₂ ∣ m`, every term of
`k2DigitLift T s m` sits at `F.key`-exponent `towerSolve u₂ e₂ (m-Δ) + e₂t = e₂t`
(the grade shifts `Δ` are `≡ 0 (mod e₂)`, so the solve vanishes on the lattice), and
all off-lattice `F.key`-digits of the lift vanish. -/
theorem dev_k2DigitLift_off_lattice {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) {m j : ℕ}
    (hm : T.e₂ ∣ m) (hj : ¬ T.e₂ ∣ j) :
    dev F.key (k2DigitLift T s m) j = 0 := by
  classical
  have hkeypos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  unfold k2DigitLift
  rw [dev_finset_sum F.hmonic]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [dev_finset_sum F.hmonic]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hr' : r < F.f₁ := Finset.mem_range.mp hr
  set M := m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t) with hM
  have hMdvd : T.e₂ ∣ M := by
    have hΔ : T.e₂ ∣ F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t :=
      Nat.dvd_add ⟨F.e₁ * F.h * r, by ring⟩ ⟨T.u₂ * t, by ring⟩
    obtain ⟨a, ha⟩ := hm
    obtain ⟨b, hb⟩ := hΔ
    exact ⟨a - b, by rw [hM, ha, hb, Nat.mul_sub]⟩
  have hb0 : (n2Exp T M).2.2 = 0 := by
    rw [n2Exp_snd_snd_eq]; exact towerSolve_eq_zero_of_dvd hMdvd T.u₂
  rcases Nat.lt_trichotomy j ((n2Exp T M).2.2 + T.e₂ * t) with hlt | heq | hgt
  · exact dev_mul_pow_of_lt F.hmonic _ _ _ hlt
  · exact absurd ⟨t, by omega⟩ hj
  · obtain ⟨d, rfl⟩ : ∃ d, j = ((n2Exp T M).2.2 + T.e₂ * t) + (d + 1) :=
      ⟨j - ((n2Exp T M).2.2 + T.e₂ * t) - 1, by omega⟩
    rw [dev_mul_pow F.hmonic]
    refine dev_eq_zero_of_lt F.hmonic hkeypos _ _ ?_
    calc (Polynomial.C
          (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r) * π ^ (n2Exp T M).1)
          * Polynomial.X ^ ((n2Exp T M).2.1 + F.e₁ * r)).natDegree
        ≤ (n2Exp T M).2.1 + F.e₁ * r := natDegree_C_mul_X_pow_le _ _
      _ < F.e₁ * F.f₁ := xexp_lt T M hr'
      _ = 1 * F.key.natDegree := by rw [F.hdeg, one_mul]
      _ ≤ (d + 1) * F.key.natDegree := Nat.mul_le_mul (by omega) le_rfl

/-- **IsTestKey conjunct 4 at `Φ₂⁺`, conditional on `T.e₂ ∣ lam`:** the corrected key's
off-lattice digits vanish exactly when the slope sits on the `e₂`-lattice.  (At
`e₂ ∤ lam` this conjunct FAILS for `Φ₂⁺` — the lift's own digits occupy the shifted
lattice `towerSolve u₂ e₂ lam + e₂·[0,f₂)`; see the module docstring and
`runs/wave-c/verdict_RB3R.md`.) -/
theorem corrected_offLattice_digit {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) {lam : ℕ}
    (hdvd : T.e₂ ∣ lam) {b : ℕ} (hb : b < T.e₂ * T.f₂) (hnd : ¬ T.e₂ ∣ b) :
    dev F.key (composedKey T - k2DigitLift T s lam) b = 0 := by
  rw [dev_sub F.hmonic, composedKey_offLattice_digit T hb hnd,
    dev_k2DigitLift_off_lattice T s hdvd hnd, sub_zero]

end Uniformity.Density.Tower.C150rb4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C150rb4.towerSolve_lt
#print axioms Uniformity.Density.Tower.C150rb4.towerSolve_eq_zero_of_dvd
#print axioms Uniformity.Density.Tower.C150rb4.n2Exp_snd_fst_lt
#print axioms Uniformity.Density.Tower.C150rb4.n2Exp_snd_snd_lt
#print axioms Uniformity.Density.Tower.C150rb4.natDegree_k2DigitLift_lt
#print axioms Uniformity.Density.Tower.C150rb4.keyDeg₂_eq_D₂
#print axioms Uniformity.Density.Tower.C150rb4.corrected_monic
#print axioms Uniformity.Density.Tower.C150rb4.corrected_natDegree
#print axioms Uniformity.Density.Tower.C150rb4.corrected_top_digit
#print axioms Uniformity.Density.Tower.C150rb4.dev_k2DigitLift_off_lattice
#print axioms Uniformity.Density.Tower.C150rb4.corrected_offLattice_digit

end AxCheck
