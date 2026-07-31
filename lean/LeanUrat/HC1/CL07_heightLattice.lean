/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower

/-!
# HC1.CL07_heightLattice — LAT: the height lattice lemma (BP5 CL-07)

**Unit CL-07** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4, "LAT";
§3.2 "Supporting arithmetic (LAT, unit CL-07)").

**Informal statement.** Every coordinate height lies on the nonnegative
`(1/strTop)·ℕ` lattice: `ht c ≥ 0` and `∃ n : ℕ, ht c = n / strTop`; supported by
the divisibility chain `e_r·STR_r ∣ strTop` for every level `r`.

**Proof sketch.** `κ_r = h_r/(e_r·STR_r)` (DefsTower `kappa`); nonnegativity is
direct from the formula (`l`, slots, `κ ≥ 0` as ℕ-casts). For the lattice claim
clear denominators via the divisibility chain: `e_r·STR_r = STR_{r+1}` divides
`STR_K·e_K = strTop` for every `r ≤ K` — induction on `strAux` (each step multiplies
by the next `e`, so `strAux (r+1) ∣ strAux (K+1) = strTop`; cf. the private
`t4_strAux`/`t4_strTop_eq` toolkit in `T4_slotMinHt.lean`). Then
`strTop·ht c = strTop·l + Σ_r slot_r·(h_r·(strTop/(e_r·STR_r)))` is a ℕ-sum.

**E-phase resolutions recorded.**
* The blueprint states the unit as one display joined by "+"; it is emitted here as
  TWO named declarations (`CL07_heightLattice`, `CL07_strTop_dvd`) so the downstream
  consumers (CL-08's `wE` well-definedness, CL-09's lattice-support legs, CL-13's
  on-lattice step) can cite each half separately. No content change.
* `T.str r` is DefsTower's EXCLUSIVE accumulated stretch (audit C-1), so
  `(T.stg r).e * T.str r = T.strAux (r.val + 1)` — the divisibility is stated in the
  blueprint's `e_r·STR_r` form verbatim.

**Deps.** none (day-one unit). difficulty: routine-opus. Size: ~40. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Private stretch toolkit (copies of T4/CL27's `strAux`/`strTop`/`ND` lemmas —
the corpus re-proves these per unit; the originals are `private`). -/

/-- `strAux` recursion at an in-range index. -/
private lemma cl07_strAux_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    T.strAux (k + 1) = T.strAux k * (T.stg ⟨k, hk⟩).e := by
  have h : T.strAux (k + 1)
      = T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := rfl
  rw [h, dif_pos hk]

private lemma cl07_strAux_pos (T : Tower p F) (k : ℕ) : 0 < T.strAux k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [Tower.strAux]
    apply Nat.mul_pos ih
    split
    · exact (T.stg _).he
    · exact Nat.one_pos

private lemma cl07_strTop_eq (T : Tower p F) : T.strTop = T.strAux (T.K + 1) := by
  rw [cl07_strAux_succ T T.K (Nat.lt_succ_self _)]; rfl

private lemma cl07_strTop_pos (T : Tower p F) : 0 < T.strTop := by
  rw [cl07_strTop_eq]; exact cl07_strAux_pos T _

/-- `strAux` divides along the chain. -/
private lemma cl07_strAux_dvd (T : Tower p F) (a : ℕ) :
    ∀ b, a ≤ b → T.strAux a ∣ T.strAux b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ n hn ih =>
    have h : T.strAux (n + 1)
        = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
    rw [h]
    exact Dvd.dvd.mul_right ih _

/-- The ℕ-valued lattice height of one κ-place: `ND r = h_r · (strTop / STR_{r+1})`
(= `strTop·κ_r`, an integer by the stretch-divisibility chain); junk 1 beyond K. -/
private noncomputable def cl07_ND (T : Tower p F) (r : ℕ) : ℕ :=
  if h : r < T.K + 1 then (T.stg ⟨r, h⟩).h * (T.strAux (T.K + 1) / T.strAux (r + 1)) else 1

/-- `ND` is `strTop·κ` as rationals (the exact-division cast). -/
private lemma cl07_ND_cast (T : Tower p F) (r : Fin (T.K + 1)) :
    ((cl07_ND T r.val : ℕ) : ℚ) = (T.strTop : ℚ) * T.kappa r := by
  have hlt : r.val < T.K + 1 := r.isLt
  rw [cl07_ND, dif_pos hlt]
  have hdvd : T.strAux (r.val + 1) ∣ T.strAux (T.K + 1) :=
    cl07_strAux_dvd T (r.val + 1) (T.K + 1) (by omega)
  have hM : (T.strAux (T.K + 1) / T.strAux (r.val + 1)) * T.strAux (r.val + 1)
      = T.strAux (T.K + 1) := Nat.div_mul_cancel hdvd
  have hstgr : T.stg ⟨r.val, hlt⟩ = T.stg r := by congr 1
  have hstr1 : T.strAux (r.val + 1) = T.str r * (T.stg r).e := by
    rw [show T.str r = T.strAux r.val from rfl, ← hstgr]
    exact cl07_strAux_succ T r.val hlt
  have hSpos : (0 : ℚ) < (T.strAux (r.val + 1) : ℚ) := by
    exact_mod_cast cl07_strAux_pos T (r.val + 1)
  have hden : ((T.stg r).e : ℚ) * (T.str r : ℚ) ≠ 0 := by
    have he := (T.stg r).he
    have hstr : 0 < T.str r := cl07_strAux_pos T r.val
    positivity
  apply mul_right_cancel₀ (ne_of_gt hSpos)
  have hNat : (T.stg ⟨r.val, hlt⟩).h * (T.strAux (T.K + 1) / T.strAux (r.val + 1))
        * T.strAux (r.val + 1)
      = T.strAux (T.K + 1) * (T.stg ⟨r.val, hlt⟩).h := by
    rw [mul_assoc, hM]; ring
  have hL : (((T.stg ⟨r.val, hlt⟩).h * (T.strAux (T.K + 1) / T.strAux (r.val + 1)) : ℕ) : ℚ)
        * (T.strAux (r.val + 1) : ℚ)
      = (T.strAux (T.K + 1) : ℚ) * ((T.stg ⟨r.val, hlt⟩).h : ℚ) := by
    exact_mod_cast hNat
  have hR : (T.strTop : ℚ) * T.kappa r * (T.strAux (r.val + 1) : ℚ)
      = (T.strAux (T.K + 1) : ℚ) * ((T.stg ⟨r.val, hlt⟩).h : ℚ) := by
    have hcast : (T.strAux (r.val + 1) : ℚ) = ((T.stg r).e : ℚ) * (T.str r : ℚ) := by
      rw [hstr1]; push_cast; ring
    rw [Tower.kappa, cl07_strTop_eq T, hcast, hstgr]
    calc (T.strAux (T.K + 1) : ℚ) * (((T.stg r).h : ℚ) / (((T.stg r).e : ℚ) * (T.str r : ℚ)))
          * (((T.stg r).e : ℚ) * (T.str r : ℚ))
        = (T.strAux (T.K + 1) : ℚ)
          * ((((T.stg r).h : ℚ) / (((T.stg r).e : ℚ) * (T.str r : ℚ)))
            * (((T.stg r).e : ℚ) * (T.str r : ℚ))) := by ring
      _ = (T.strAux (T.K + 1) : ℚ) * ((T.stg r).h : ℚ) := by
          rw [div_mul_cancel₀ _ hden]
  exact hL.trans hR.symm

/-- **CL-07 (LAT), divisibility half**: the per-level scale divides the frame scale —
`e_r·STR_r ∣ strTop` (each `κ_r = h_r/(e_r·STR_r)` has denominator dividing the
frame stretch `strTop = STR_K·e_K`). -/
theorem CL07_strTop_dvd (T : Tower p F) :
    ∀ r : Fin (T.K + 1), (T.stg r).e * T.str r ∣ T.strTop := by
  intro r
  have hlt : r.val < T.K + 1 := r.isLt
  have hstgr : T.stg ⟨r.val, hlt⟩ = T.stg r := by congr 1
  have hsucc : T.strAux (r.val + 1) = T.strAux r.val * (T.stg ⟨r.val, hlt⟩).e :=
    cl07_strAux_succ T r.val hlt
  have heq : (T.stg r).e * T.str r = T.strAux (r.val + 1) := by
    rw [hsucc, hstgr, show T.str r = T.strAux r.val from rfl]; ring
  rw [heq, cl07_strTop_eq]
  exact cl07_strAux_dvd T (r.val + 1) (T.K + 1) (by omega)

/-- **CL-07 (LAT), lattice half**: every coordinate height is nonnegative and lies on
the `(1/strTop)`-lattice: `0 ≤ ht c` and `ht c = n/strTop` for some `n : ℕ`. -/
theorem CL07_heightLattice (T : Tower p F) :
    ∀ c : T.Coord, 0 ≤ T.ht c ∧ ∃ n : ℕ, T.ht c = (n : ℚ) / (T.strTop : ℚ) := by
  intro c
  have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast cl07_strTop_pos T
  have hstrne : (T.strTop : ℚ) ≠ 0 := ne_of_gt hstrpos
  set n : ℕ := T.strTop * c.l + ∑ r : Fin (T.K + 1), c.slot r * cl07_ND T r.val with hn
  have hcast : (n : ℚ) = (T.strTop : ℚ) * T.ht c := by
    rw [hn, Tower.ht]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [cl07_ND_cast T r]; ring
  have heq : T.ht c = (n : ℚ) / (T.strTop : ℚ) := by
    rw [eq_div_iff hstrne, hcast]; exact mul_comm _ _
  refine ⟨?_, n, heq⟩
  rw [heq]
  exact div_nonneg (by positivity) (le_of_lt hstrpos)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL07_strTop_dvd
#print axioms LeanUrat.HC1.CL07_heightLattice
