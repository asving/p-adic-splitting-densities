/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Development
import LeanUrat.OM.RphiRing
import LeanUrat.OM.CellCard

/-!
# RestartEquiv — Phase-B wave W4d1: THE RESTART EQUIVALENCE at level `N`

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md` W4d SPEC (pinned 2026-07-04) with the
D0-VERIFIED pattern correction (`/workspace-vast/asving/tmp/phaseb_w4d0/SUMMARY.md`): the fresh
cluster pattern is PURE ideal membership, e-SCALED, STRICT, RESIDUE-FREE —

    FreshClusterPattern β  :=  ∀ j < μ,  β j ∈ (θ)^(e·(μ−j) + 1)

(NOT the originally pinned `≥ μ−j` + endpoint exactness + unit residues, refuted by the gate).
Math source: `notes/RESTART_LEMMA.md` §13.1 (the cell event in development coordinates).

**Setting** (order 1, f = 1, h = 1, W1's banked `RphiRing` layer): `c : (ZMod (p^N))ˣ` the lift
of the residual root `c̄`, `φ := X^e − c·p` (`RphiRing.phi`, h = 1), and the single-side cell of
slope `−1/e`, width `s = μ·e`, residual `(y − c̄)^μ`: path `[(0, μ), (μ·e, 0)]`, shape `[(1, μ)]`
(the `mkCell` menu cell), ROOT-REFINED by the pin `residualOf f = (X − C c̄)^μ` (`InCellAt`; the
menu cell only carries the shape, so at `p ≥ 3` the root pin genuinely refines — the d0 gate's
per-case tables are root-refined, e.g. C1a/C1b split the p = 3 fiber 6 as 3 + 3).

**Deliverables.**
1. `FreshClusterPattern` + `card_freshPattern_slots` (per-slot product, via W1
   `card_span_theta_pow`) + `card_freshPattern = p^(μ(Ne−1) − eμ(μ+1)/2)`; the honest-subtraction
   condition is `μ < N` (`slot_exponent_le`) — exactly the menu height bound `μ ≤ N−1`.
2. `restartDigits` — φ-adic development (`developEquiv` at `k = μ, m = e`) composed with the
   digit identification `digitEquiv`, per digit.
3. **THE DICTIONARY** `inCellAt_iff_pattern`: `InCellAt f ↔ FreshClusterPattern (restartDigits' f)`,
   decomposed as (i) `phi_pow_coeff` — the cap `φ^μ` carries the exact on-side values
   `C(μ,t)(−c·p)^(μ−t)`; (ii) `coeffCond_of_slotPattern` — strict digit floors do not disturb the
   on-side reads (⟸); (iii) `slotPattern_of_coeffCond` — the triangular converse (⟹), by
   downward induction on the digit index (the lowest failing slot would corrupt an on-side read).
4. `restartEquiv : {f // InCellAt f} ≃ {β // FreshClusterPattern β}`; the inverse is the explicit
   reassembly `β ↦ φ^μ + Σ lift(β_j)·φ^j` (`restartEquiv_symm_apply_val`).
5. `card_restart_fiber` + the five MANDATORY d0 gates (fiber cards 2/16/3/256/8) + the W4b
   cross-check at (p,N,e,μ) = (2,3,2,2) against `CellCard.cell_card_raw` (both = 16).

**Box size spelling.** The box is `monicBox p N (μ * e)` (not `e * μ`): `developEquiv` produces
`monicBox p N (k * m)` at `k = μ, m = e`, so `μ * e` avoids a propositional cast in the pipeline.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints (checked with
`#print axioms`, prints removed after checking).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RestartEquiv

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.CellCard
open LeanUrat.OM.RphiRing
open LeanUrat.OM.Development

variable (p N e μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## 0. Base-ring toolkit: `π`-divisibility, residue reduction, level digits -/

section Toolkit

/-- Ring divisibility by `p^m` in `ZMod (p^N)` is `Nat` divisibility of `val` (for `m ≤ N`). -/
theorem pow_dvd_iff_dvd_val {m : ℕ} (hm : m ≤ N) (x : ZMod (p ^ N)) :
    (p : ZMod (p ^ N)) ^ m ∣ x ↔ (p : ℕ) ^ m ∣ x.val := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  constructor
  · rintro ⟨y, rfl⟩
    have hcast : (p : ZMod (p ^ N)) ^ m = ((p ^ m : ℕ) : ZMod (p ^ N)) := by push_cast; ring
    rw [hcast, ZMod.val_mul, ZMod.val_natCast, Nat.dvd_mod_iff (pow_dvd_pow p hm)]
    exact Dvd.dvd.mul_right ((Nat.dvd_mod_iff (pow_dvd_pow p hm)).mpr dvd_rfl) _
  · rintro ⟨t, ht⟩
    refine ⟨((t : ℕ) : ZMod (p ^ N)), ?_⟩
    have hx : ((x.val : ℕ) : ZMod (p ^ N)) = x := ZMod.natCast_rightInverse x
    rw [← hx, ht]
    push_cast
    ring

/-- Reduction of the level-`N` base ring to the residue field (`val` mod `p`). -/
def resp (x : ZMod (p ^ N)) : ZMod p := ((x.val : ℕ) : ZMod p)

theorem resp_eq_castHom (hN : 0 < N) (x : ZMod (p ^ N)) :
    resp p N x = ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p) x := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  rw [ZMod.castHom_apply]
  exact ZMod.natCast_val x

theorem resp_add (hN : 0 < N) (x y : ZMod (p ^ N)) :
    resp p N (x + y) = resp p N x + resp p N y := by
  simp only [resp_eq_castHom p N hN, map_add]

theorem resp_mul (hN : 0 < N) (x y : ZMod (p ^ N)) :
    resp p N (x * y) = resp p N x * resp p N y := by
  simp only [resp_eq_castHom p N hN, map_mul]

theorem resp_sub (hN : 0 < N) (x y : ZMod (p ^ N)) :
    resp p N (x - y) = resp p N x - resp p N y := by
  simp only [resp_eq_castHom p N hN, map_sub]

theorem resp_neg (hN : 0 < N) (x : ZMod (p ^ N)) : resp p N (-x) = -resp p N x := by
  simp only [resp_eq_castHom p N hN, map_neg]

theorem resp_pow (hN : 0 < N) (x : ZMod (p ^ N)) (t : ℕ) :
    resp p N (x ^ t) = resp p N x ^ t := by
  simp only [resp_eq_castHom p N hN, map_pow]

theorem resp_natCast (hN : 0 < N) (n : ℕ) : resp p N ((n : ℕ) : ZMod (p ^ N)) = (n : ZMod p) := by
  rw [resp_eq_castHom p N hN, map_natCast]

/-- `resp` kills `p`. -/
theorem resp_p (hN : 0 < N) : resp p N ((p : ℕ) : ZMod (p ^ N)) = 0 := by
  rw [resp_natCast p N hN, ZMod.natCast_self]

/-- Vanishing under `resp` is exactly divisibility by `π = p`. -/
theorem resp_eq_zero_iff (hN : 0 < N) (x : ZMod (p ^ N)) :
    resp p N x = 0 ↔ (p : ZMod (p ^ N)) ∣ x := by
  have h2 : (p : ZMod (p ^ N)) ^ 1 ∣ x ↔ (p : ℕ) ^ 1 ∣ x.val := pow_dvd_iff_dvd_val p N hN x
  rw [pow_one, pow_one] at h2
  rw [h2]
  exact CharP.cast_eq_zero_iff (ZMod p) p x.val

/-- **The level digit of a `π^m`-multiple** (`m < N`): `digit p N m (π^m·u) = resp u`. -/
theorem digit_pow_mul {m : ℕ} (hm : m < N) (u : ZMod (p ^ N)) :
    digit p N m ((p : ZMod (p ^ N)) ^ m * u) = resp p N u := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have hval : ((p : ZMod (p ^ N)) ^ m * u).val = p ^ m * (u.val % p ^ (N - m)) := by
    have hcast : (p : ZMod (p ^ N)) ^ m = ((p ^ m : ℕ) : ZMod (p ^ N)) := by push_cast; ring
    have hlt : p ^ m < p ^ N := Nat.pow_lt_pow_right hp.out.one_lt hm
    have hsplit : ∀ a : ℕ, p ^ m * a % p ^ N = p ^ m * (a % p ^ (N - m)) := fun a => by
      rw [show p ^ N = p ^ m * p ^ (N - m) by rw [← pow_add]; congr 1; omega,
        Nat.mul_mod_mul_left]
    rw [hcast, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hsplit]
  unfold digit resp
  rw [hval, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)]
  have hmm : (u.val % p ^ (N - m)) % p = u.val % p :=
    Nat.mod_mod_of_dvd u.val (dvd_pow_self p (by omega : N - m ≠ 0))
  calc ((u.val % p ^ (N - m) : ℕ) : ZMod p)
      = ((u.val % p ^ (N - m) % p : ℕ) : ZMod p) := (ZMod.natCast_mod _ p).symm
    _ = ((u.val % p : ℕ) : ZMod p) := by rw [hmm]
    _ = ((u.val : ℕ) : ZMod p) := ZMod.natCast_mod _ p

end Toolkit

/-! ## 1. Deliverable 1: `FreshClusterPattern` and its cardinality -/

section Pattern

/-- **Deliverable 1 — the D0-VERIFIED fresh cluster pattern** (SUMMARY.md, 9 cases): PURE ideal
membership, e-SCALED, STRICT (`+1`), RESIDUE-FREE. No exactness and no residue condition at any
slot; the parent's endpoint pins are carried by the cap `φ^μ`, not by the digits. -/
def FreshClusterPattern (β : Fin μ → Rphi p N e 1 c) : Prop :=
  ∀ j : Fin μ, β j ∈ Ideal.span {theta p N e 1 c} ^ (e * (μ - j.1) + 1)

theorem span_theta_pow_eq (m : ℕ) :
    Ideal.span {theta p N e 1 c} ^ m = Ideal.span {theta p N e 1 c ^ m} :=
  Ideal.span_singleton_pow _ m

/-- **The honest-subtraction condition, spelled**: the slot exponent obeys
`e·(μ−j) + 1 ≤ N·e` for every `j` as soon as `μ < N` (worst case `j = 0`:
`e·μ + 1 ≤ N·e ⟺ μ < N`). `μ < N` is exactly the menu height bound `μ ≤ N−1` — the
cell exists at level `N` iff it holds, so nothing is lost. -/
theorem slot_exponent_le (he : 0 < e) (hμN : μ < N) (j : ℕ) :
    e * (μ - j) + 1 ≤ N * e := by
  have h2 : (μ - j) + 1 ≤ N := by omega
  have h1 : e * (μ - j) + e ≤ N * e := by
    calc e * (μ - j) + e = e * ((μ - j) + 1) := by ring
      _ ≤ e * N := Nat.mul_le_mul_left e h2
      _ = N * e := Nat.mul_comm e N
  omega

/-- Per-slot cardinality of the pattern ideal, via W1 `card_span_theta_pow`. -/
theorem card_slot (hN : 0 < N) (he : 0 < e) (hμN : μ < N) (j : ℕ) :
    Nat.card {x : Rphi p N e 1 c // x ∈ Ideal.span {theta p N e 1 c} ^ (e * (μ - j) + 1)}
      = p ^ (N * e - (e * (μ - j) + 1)) := by
  simp only [span_theta_pow_eq]
  exact card_span_theta_pow p N e c hN he _ (slot_exponent_le N e μ he hμN j)

/-- **Deliverable 1, per-slot product form** (banked FIRST, per the spec): the pattern space
is the product of the slot ideals. -/
theorem card_freshPattern_slots (hN : 0 < N) (he : 0 < e) (hμN : μ < N) :
    Nat.card {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β}
      = ∏ j : Fin μ, p ^ (N * e - (e * (μ - j.1) + 1)) := by
  haveI := finite_Rphi p N e 1 c hN he
  have e1 : {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β}
      ≃ ∀ j : Fin μ,
        {x : Rphi p N e 1 c // x ∈ Ideal.span {theta p N e 1 c} ^ (e * (μ - j.1) + 1)} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e1, Nat.card_pi]
  exact Finset.prod_congr rfl fun j _ => card_slot p N e μ c hN he hμN j.1

/-- The closed exponent: `Σ_j (Ne − (e(μ−j)+1)) = μ(Ne−1) − eμ(μ+1)/2`. -/
theorem freshExp_sum (he : 0 < e) (hμN : μ < N) :
    ∑ j : Fin μ, (N * e - (e * (μ - j.1) + 1)) = μ * (N * e - 1) - e * μ * (μ + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => N * e - (e * (μ - j) + 1)) μ]
  have hrefl : ∑ j ∈ Finset.range μ, (μ - j) = ∑ j ∈ Finset.range μ, (j + 1) := by
    conv_rhs => rw [← Finset.sum_range_reflect (fun j => j + 1) μ]
    exact Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj
      omega
  have hgauss2 : 2 * ∑ j ∈ Finset.range μ, (μ - j) = μ * (μ + 1) := by
    have h1 : ∑ j ∈ Finset.range μ, (j + 1) = (∑ j ∈ Finset.range μ, j) + μ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    have h2 := Finset.sum_range_id_mul_two μ
    have h3 : μ * (μ + 1) = μ * (μ - 1) + 2 * μ := by
      cases μ with
      | zero => rfl
      | succ m =>
          simp only [Nat.succ_sub_one]
          ring
    omega
  have hterm : ∀ j ∈ Finset.range μ, (N * e - (e * (μ - j) + 1)) + (e * (μ - j) + 1) = N * e :=
    fun j _ => by have := slot_exponent_le N e μ he hμN j; omega
  have hsplit : (∑ j ∈ Finset.range μ, (N * e - (e * (μ - j) + 1)))
      + (∑ j ∈ Finset.range μ, (e * (μ - j) + 1)) = μ * (N * e) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
  have hsum2 : ∑ j ∈ Finset.range μ, (e * (μ - j) + 1)
      = e * (∑ j ∈ Finset.range μ, (μ - j)) + μ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  have hdiv : e * μ * (μ + 1) / 2 = e * (∑ j ∈ Finset.range μ, (μ - j)) := by
    have h4 : e * μ * (μ + 1) = 2 * (e * (∑ j ∈ Finset.range μ, (μ - j))) := by
      calc e * μ * (μ + 1) = e * (2 * ∑ j ∈ Finset.range μ, (μ - j)) := by
            rw [hgauss2]; ring
        _ = 2 * (e * (∑ j ∈ Finset.range μ, (μ - j))) := by ring
    omega
  have hmul1 : μ * (N * e - 1) = μ * (N * e) - μ := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [hdiv, hmul1]
  rw [hsum2] at hsplit
  omega

/-- **Deliverable 1, closed form**: `#{β // FreshClusterPattern β} = p^(μ(Ne−1) − eμ(μ+1)/2)`. -/
theorem card_freshPattern (hN : 0 < N) (he : 0 < e) (hμN : μ < N) :
    Nat.card {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β}
      = p ^ (μ * (N * e - 1) - e * μ * (μ + 1) / 2) := by
  rw [card_freshPattern_slots p N e μ c hN he hμN, Finset.prod_pow_eq_pow_sum,
    freshExp_sum N e μ he hμN]

end Pattern

/-! ## 2. The one-slot dictionary: `(θ^{e·q+1})`-membership ⟺ strict per-coefficient `p`-floors

A digit `b` (a polynomial of degree `< e`) maps into the ideal `(θ^{e·q+1})` iff its constant
coefficient is divisible by `p^{q+1}` and its higher coefficients by `p^q` — the STRICT floor,
one deeper at `r = 0`.  Route: the constructive inclusion (`mem_of_slotCond`) plus the
cardinality sandwich against W1's `card_span_theta_pow` (`card_slotCond` counts the floor set to
the same `p^{Ne−(eq+1)}`, so the inclusion is onto). -/

section Slot

/-- The strict per-coefficient floor at depth `q` — the coefficient avatar of
`β ∈ (θ^{e·q+1})`. -/
def SlotCond (q : ℕ) (b : degreeLT (ZMod (p ^ N)) e) : Prop :=
  (p : ZMod (p ^ N)) ^ (q + 1) ∣ (b : (ZMod (p ^ N))[X]).coeff 0 ∧
    ∀ r : ℕ, 1 ≤ r → r < e → (p : ZMod (p ^ N)) ^ q ∣ (b : (ZMod (p ^ N))[X]).coeff r

/-- Uniform weak floor: under `SlotCond q`, every coefficient is divisible by `p^q`. -/
theorem SlotCond.dvd_coeff {q : ℕ} {b : degreeLT (ZMod (p ^ N)) e}
    (h : SlotCond p N e q b) {r : ℕ} (hr : r < e) :
    (p : ZMod (p ^ N)) ^ q ∣ (b : (ZMod (p ^ N))[X]).coeff r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · exact dvd_trans (pow_dvd_pow _ (Nat.le_succ q)) h.1
  · exact h.2 r hr1 hr

/-- **The constructive inclusion**: the strict floors land the digit in `(θ^{e·q+1})`
(each monomial `a_r·θ^r` has `vphi ≥ e·m_r + r ≥ e·q+1`). -/
theorem mem_of_slotCond (hN : 0 < N) (he : 0 < e) {q : ℕ} {b : degreeLT (ZMod (p ^ N)) e}
    (h : SlotCond p N e q b) :
    digitEquiv p N e 1 c hN he b ∈ Ideal.span {theta p N e 1 c ^ (e * q + 1)} := by
  have hdeg : (b : (ZMod (p ^ N))[X]).natDegree < e := by
    by_cases hB : (b : (ZMod (p ^ N))[X]) = 0
    · rw [hB, natDegree_zero]; exact he
    · exact (natDegree_lt_iff_degree_lt hB).mpr (mem_degreeLT.mp b.2)
  rw [digitEquiv_apply, show ((b : (ZMod (p ^ N))[X]))
    = ∑ r ∈ Finset.range e, (monomial r) ((b : (ZMod (p ^ N))[X]).coeff r)
    from as_sum_range' _ e hdeg, map_sum]
  refine Ideal.sum_mem _ fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← theta_eq_root]
  have key : ∀ m : ℕ, (p : ZMod (p ^ N)) ^ m ∣ (b : (ZMod (p ^ N))[X]).coeff r →
      e * q + 1 ≤ e * m + r →
      (AdjoinRoot.of (phi p N e 1 c)) ((b : (ZMod (p ^ N))[X]).coeff r) * theta p N e 1 c ^ r
        ∈ Ideal.span {theta p N e 1 c ^ (e * q + 1)} := by
    rintro m ⟨u, hu⟩ hle
    have hrw : (AdjoinRoot.of (phi p N e 1 c)) ((b : (ZMod (p ^ N))[X]).coeff r)
          * theta p N e 1 c ^ r
        = ((((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ m
            * (AdjoinRoot.of (phi p N e 1 c)) u) * theta p N e 1 c ^ (e * m + r) := by
      rw [hu, map_mul, map_pow, map_natCast, natCast_p_eq p N e c]
      ring
    rw [hrw]
    exact Ideal.mul_mem_left _ _
      (span_theta_pow_antitone p N e c hle (Ideal.subset_span rfl))
  by_cases h0 : r = 0
  · subst h0
    refine key (q + 1) h.1 ?_
    have h5 : e * (q + 1) = e * q + e := by ring
    omega
  · have hr1 : 1 ≤ r := by omega
    have hle2 : e * q + 1 ≤ e * q + r := by omega
    exact key q (h.2 r hr1 hr) hle2

/-- The floor set counts to `p^(Ne − (e·q+1))` — the same as the ideal (`card_span_theta_pow`). -/
theorem card_slotCond (_hN : 0 < N) (he : 0 < e) {q : ℕ} (hq : q + 1 ≤ N) :
    Nat.card {b : degreeLT (ZMod (p ^ N)) e // SlotCond p N e q b}
      = p ^ (N * e - (e * q + 1)) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have e1 : {b : degreeLT (ZMod (p ^ N)) e // SlotCond p N e q b}
      ≃ {v : Fin e → ZMod (p ^ N) //
          ∀ r : Fin e, (p : ℕ) ^ (if (r : ℕ) = 0 then q + 1 else q) ∣ (v r).val} := by
    refine (Polynomial.degreeLTEquiv (ZMod (p ^ N)) e).toEquiv.subtypeEquiv fun b => ?_
    constructor
    · rintro ⟨h0, hrest⟩ r
      show (p : ℕ) ^ (if (r : ℕ) = 0 then q + 1 else q)
        ∣ ((b : (ZMod (p ^ N))[X]).coeff (r : ℕ)).val
      by_cases hr0 : (r : ℕ) = 0
      · rw [if_pos hr0, hr0]
        exact (pow_dvd_iff_dvd_val p N hq _).mp h0
      · rw [if_neg hr0]
        exact (pow_dvd_iff_dvd_val p N (by omega) _).mp (hrest (r : ℕ) (by omega) r.2)
    · intro hall
      constructor
      · have h1 := hall ⟨0, he⟩
        have h2 : (if ((⟨0, he⟩ : Fin e) : ℕ) = 0 then q + 1 else q) = q + 1 := if_pos rfl
        rw [h2] at h1
        exact (pow_dvd_iff_dvd_val p N hq _).mpr h1
      · intro r hr1 hre
        have h1 := hall ⟨r, hre⟩
        have h2 : (if ((⟨r, hre⟩ : Fin e) : ℕ) = 0 then q + 1 else q) = q := by
          rw [show ((⟨r, hre⟩ : Fin e) : ℕ) = r from rfl, if_neg (by omega)]
        rw [h2] at h1
        exact (pow_dvd_iff_dvd_val p N (by omega) _).mpr h1
  rw [Nat.card_congr e1,
    card_dvd_pi p (fun r : Fin e => if (r : ℕ) = 0 then q + 1 else q)
      (fun r => by split <;> omega)]
  congr 1
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hzero : (if ((0 : Fin (e' + 1)) : ℕ) = 0 then q + 1 else q) = q + 1 := if_pos rfl
  have hsucc : ∀ i : Fin e',
      (N - if ((i.succ : Fin (e' + 1)) : ℕ) = 0 then q + 1 else q) = N - q := fun i => by
    rw [if_neg (by simp [Fin.val_succ])]
  have hsum2 : (∑ i : Fin e',
        (N - if ((i.succ : Fin (e' + 1)) : ℕ) = 0 then q + 1 else q))
      = e' * (N - q) := by
    rw [Finset.sum_congr rfl fun i _ => hsucc i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_succ, hzero, hsum2]
  have hRle : (e' + 1) * q + 1 ≤ N * (e' + 1) := by
    have h6 : (e' + 1) * (q + 1) ≤ (e' + 1) * N := Nat.mul_le_mul_left (e' + 1) hq
    have h7 : (e' + 1) * (q + 1) = (e' + 1) * q + (e' + 1) := Nat.mul_succ (e' + 1) q
    have h8 : (e' + 1) * N = N * (e' + 1) := Nat.mul_comm _ _
    omega
  zify [hq, show q ≤ N by omega, hRle]
  ring

/-- The forward map of the slot dictionary, packaged (so its `val` reduces syntactically). -/
def slotEmbed (hN : 0 < N) (he : 0 < e) (q : ℕ)
    (b' : {b : degreeLT (ZMod (p ^ N)) e // SlotCond p N e q b}) :
    {x : Rphi p N e 1 c // x ∈ Ideal.span {theta p N e 1 c ^ (e * q + 1)}} :=
  ⟨digitEquiv p N e 1 c hN he b'.1, mem_of_slotCond p N e c hN he b'.2⟩

theorem slotEmbed_val (hN : 0 < N) (he : 0 < e) (q : ℕ)
    (b' : {b : degreeLT (ZMod (p ^ N)) e // SlotCond p N e q b}) :
    (slotEmbed p N e c hN he q b').1 = digitEquiv p N e 1 c hN he b'.1 := rfl

/-- **The one-slot dictionary** (ideal membership ⟺ strict floors): the constructive inclusion
is onto by the cardinality sandwich. -/
theorem digitEquiv_mem_iff (hN : 0 < N) (he : 0 < e) {q : ℕ} (hq : q + 1 ≤ N)
    (b : degreeLT (ZMod (p ^ N)) e) :
    digitEquiv p N e 1 c hN he b ∈ Ideal.span {theta p N e 1 c ^ (e * q + 1)}
      ↔ SlotCond p N e q b := by
  haveI := finite_Rphi p N e 1 c hN he
  constructor
  · intro hmem
    have hle : e * q + 1 ≤ N * e := by
      have h1 : e * (q + 1) ≤ e * N := Nat.mul_le_mul_left e hq
      have h2 : e * (q + 1) = e * q + e := by ring
      have h3 : e * N = N * e := Nat.mul_comm e N
      omega
    have hDinj : Function.Injective (digitEquiv p N e 1 c hN he) := EquivLike.injective _
    have hbij : Function.Bijective (slotEmbed p N e c hN he q) := by
      rw [Nat.bijective_iff_injective_and_card]
      constructor
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        rw [slotEmbed_val, slotEmbed_val] at h1
        exact Subtype.ext (hDinj h1)
      · rw [card_slotCond p N e hN he hq]
        exact (card_span_theta_pow p N e c hN he _ hle).symm
    obtain ⟨bb, hFb⟩ := hbij.2 ⟨digitEquiv p N e 1 c hN he b, hmem⟩
    have h2 : (slotEmbed p N e c hN he q bb).1 = digitEquiv p N e 1 c hN he b := by
      rw [hFb]
    rw [slotEmbed_val] at h2
    have hbb : bb.1 = b := hDinj h2
    exact hbb ▸ bb.2
  · exact mem_of_slotCond p N e c hN he

end Slot

/-! ## 3. The x-adic coefficient formula of the φ-adic assembly

`f = φ^μ + Σ_j b_j φ^j` with `φ = X^e − c·p`: expanding `φ^j` binomially, the x-adic coefficient
at `k·e + r` (`r < e`) is the `p`-weighted TRIANGULAR combination
`Σ_j b_{j,r}·C(j,k)·(−c·p)^(j−k)` plus the cap term `C(μ,k)·(−c·p)^(μ−k)·[r = 0]`. -/

section CoeffFormula

/-- `−c·p`, the twist constant of `φ = X^e + C(wneg)`. -/
def wneg : ZMod (p ^ N) := -((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)))

/-- The unit part of the cap coefficient: `C(μ,k)·(−c)^(μ−k)` (so that the cap x-coefficient at
`k·e` is exactly `p^(μ−k) · capU k`). -/
def capU (k : ℕ) : ZMod (p ^ N) := (μ.choose k : ZMod (p ^ N)) * (-(c : ZMod (p ^ N))) ^ (μ - k)

/-- The residual root: the residue of the lift `c`. -/
def cbar : ZMod p := resp p N ((c : ZMod (p ^ N)))

/-- The residual target coefficients: `(X − c̄)^μ` has `X^k`-coefficient `bres k`. -/
def bres (k : ℕ) : ZMod p := (μ.choose k : ZMod p) * (-(cbar p N c)) ^ (μ - k)

/-- `φ = X^e + C(−c·p)` at `h = 1`. -/
theorem phi_eq_one : phi p N e 1 c = X ^ e + C (wneg p N c) := by
  rw [phi_eq, pow_one]
  unfold wneg
  rw [map_neg, sub_eq_add_neg]

/-- The cap coefficient splits as `p`-power times unit part. -/
theorem cap_split (k : ℕ) :
    (μ.choose k : ZMod (p ^ N)) * wneg p N c ^ (μ - k)
      = (p : ZMod (p ^ N)) ^ (μ - k) * capU p N μ c k := by
  unfold wneg capU
  ring

theorem resp_capU (hN : 0 < N) (k : ℕ) :
    resp p N (capU p N μ c k) = bres p N μ c k := by
  unfold capU bres cbar
  rw [resp_mul p N hN, resp_natCast p N hN, resp_pow p N hN, resp_neg p N hN]

/-- **The triangular coefficient extraction**: for `b` of degree `< e` and `r < e`,
`(b·φ^j).coeff (k·e+r) = b.coeff r · C(j,k) · (−c·p)^(j−k)` (zero for `k > j` via `C(j,k) = 0`
— the ℕ-subtraction junk in the exponent is killed by the vanishing binomial). -/
theorem coeff_mul_phi_pow (_he : 0 < e) (b : (ZMod (p ^ N))[X])
    (hb : b.degree < (e : WithBot ℕ)) (j k r : ℕ) (hr : r < e) :
    (b * phi p N e 1 c ^ j).coeff (k * e + r)
      = b.coeff r * (j.choose k : ZMod (p ^ N)) * wneg p N c ^ (j - k) := by
  rw [phi_eq_one, add_pow, Finset.mul_sum, finsetSum_coeff]
  have hterm : ∀ m : ℕ, b * ((X ^ e) ^ m * C (wneg p N c) ^ (j - m)
        * ((j.choose m : ℕ) : (ZMod (p ^ N))[X]))
      = (b * X ^ (e * m)) * C (wneg p N c ^ (j - m) * (j.choose m : ZMod (p ^ N))) := by
    intro m
    rw [← pow_mul, ← C_pow, ← C_eq_natCast, C_mul]
    ring
  rw [Finset.sum_congr rfl fun m _ => by rw [hterm m, coeff_mul_C, coeff_mul_X_pow']]
  have hvanish : ∀ m : ℕ, m < k →
      (if e * m ≤ k * e + r then b.coeff (k * e + r - e * m) else 0)
        * (wneg p N c ^ (j - m) * (j.choose m : ZMod (p ^ N))) = 0 := by
    intro m hlt
    have hek : e * k = k * e := Nat.mul_comm e k
    have hcond : e * m ≤ k * e + r := by
      have h2 : e * m ≤ e * k := Nat.mul_le_mul_left e hlt.le
      omega
    have hidx : e ≤ k * e + r - e * m := by
      have h2 : e * (m + 1) ≤ e * k := Nat.mul_le_mul_left e hlt
      have h3 : e * (m + 1) = e * m + e := Nat.mul_succ e m
      omega
    rw [if_pos hcond,
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hb (Nat.cast_le.mpr hidx)), zero_mul]
  by_cases hkj : k ≤ j
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]
    · have hek : e * k = k * e := Nat.mul_comm e k
      have hcond : e * k ≤ k * e + r := by omega
      rw [if_pos hcond, show k * e + r - e * k = r by omega]
      ring
    · intro m hm hmk
      rw [Finset.mem_range] at hm
      rcases Nat.lt_or_ge m k with hlt | hge
      · exact hvanish m hlt
      · have hmk' : k < m := by omega
        have hcond : ¬ e * m ≤ k * e + r := by
          have h2 : e * (k + 1) ≤ e * m := Nat.mul_le_mul_left e hmk'
          have h3 : e * (k + 1) = e * k + e := Nat.mul_succ e k
          have hek : e * k = k * e := Nat.mul_comm e k
          omega
        rw [if_neg hcond, zero_mul]
  · have hrhs : (j.choose k : ZMod (p ^ N)) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.cast_zero
    rw [hrhs, mul_zero, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    exact hvanish m (by omega)

/-- The reassembled development `φ^μ + Σ_j b_j φ^j` — the underlying polynomial of
`developEquiv.symm` (see `developEquiv_symm_val`). -/
def assemble (b : Fin μ → degreeLT (ZMod (p ^ N)) e) : (ZMod (p ^ N))[X] :=
  phi p N e 1 c ^ μ + ∑ j : Fin μ, (b j : (ZMod (p ^ N))[X]) * phi p N e 1 c ^ (j : ℕ)

theorem developEquiv_symm_val (hN : 0 < N) (he : 0 < e)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) :
    (((developEquiv p N e μ hN (phi p N e 1 c) (monic_phi p N e 1 c he)
        (natDegree_phi p N e 1 c hN) he).symm b : QuotientBox.monicBox p N (μ * e)) :
          { f : (ZMod (p ^ N))[X] // f.Monic ∧ f.natDegree = μ * e }).1
      = assemble p N e μ c b := rfl

/-- **Dictionary lemma (i) `cap_matches`**: the cap `φ^μ` alone carries the exact on-side
values — its `(k·e+r)` coefficient is `C(μ,k)·(−c·p)^(μ−k)` at `r = 0`, and `0` off-pattern. -/
theorem phi_pow_coeff (hN : 0 < N) (he : 0 < e) (k r : ℕ) (hr : r < e) :
    (phi p N e 1 c ^ μ).coeff (k * e + r)
      = if r = 0 then (μ.choose k : ZMod (p ^ N)) * wneg p N c ^ (μ - k) else 0 := by
  haveI := nontrivial_base p N hN
  have hdeg1 : (1 : (ZMod (p ^ N))[X]).degree < (e : WithBot ℕ) := by
    rw [degree_one]
    exact_mod_cast he
  conv_lhs => rw [← one_mul (phi p N e 1 c ^ μ)]
  rw [coeff_mul_phi_pow p N e c he 1 hdeg1 μ k r hr, coeff_one]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos h0, one_mul]
  · rw [if_neg h0, if_neg h0, zero_mul, zero_mul]

/-- **The x-adic coefficient formula** of the assembly: cap term + triangular perturbation. -/
theorem assemble_coeff (hN : 0 < N) (he : 0 < e) (b : Fin μ → degreeLT (ZMod (p ^ N)) e)
    (k r : ℕ) (hr : r < e) :
    (assemble p N e μ c b).coeff (k * e + r)
      = (if r = 0 then (μ.choose k : ZMod (p ^ N)) * wneg p N c ^ (μ - k) else 0)
        + ∑ j : Fin μ, (b j : (ZMod (p ^ N))[X]).coeff r * ((j : ℕ).choose k : ZMod (p ^ N))
            * wneg p N c ^ ((j : ℕ) - k) := by
  unfold assemble
  rw [coeff_add, finsetSum_coeff, phi_pow_coeff p N e μ c hN he k r hr]
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    coeff_mul_phi_pow p N e c he _ (mem_degreeLT.mp (b j).2) (j : ℕ) k r hr

end CoeffFormula

/-! ## 4. THE DICTIONARY at coefficient level: cell conditions ⟺ digit pattern

`CoeffCond` is the `matches_iff` shape of the root-refined cell membership, reindexed by
`i = k·e + r`: divisibility floors at every column plus exact digit pins at pattern columns.
`SlotPattern` is the strict per-digit floor (depth `μ − j` at digit `j`). -/

section Dictionary

/-- The unpacked (root-refined) cell conditions on the x-adic coefficients. -/
def CoeffCond (a : ℕ → ZMod (p ^ N)) : Prop :=
  (∀ k r : ℕ, k < μ → r < e → (p : ZMod (p ^ N)) ^ (μ - k) ∣ a (k * e + r)) ∧
    (∀ k : ℕ, k < μ → digit p N (μ - k) (a (k * e)) = bres p N μ c k)

/-- The per-digit strict pattern: digit `j` obeys `SlotCond` at depth `μ − j`. -/
def SlotPattern (b : Fin μ → degreeLT (ZMod (p ^ N)) e) : Prop :=
  ∀ j : Fin μ, SlotCond p N e (μ - (j : ℕ)) (b j)

/-- `wneg^t = (−c)^t · p^t` — the unit/`p`-power split of the twist powers. -/
theorem wneg_pow_split (t : ℕ) :
    wneg p N c ^ t = (-(c : ZMod (p ^ N))) ^ t * (p : ZMod (p ^ N)) ^ t := by
  unfold wneg
  ring

/-- **Divisibility transfer through the twist**: a `p^d`-floor on `x`, tensored with the
`p^t`-factor from `wneg^t`, lands `x·y·wneg^t` in the `p^(d+t)`-floor (`d + t = D`). -/
private theorem dvd_mul_wneg_pow {d t D : ℕ} (hD : d + t = D) {x : ZMod (p ^ N)}
    (hx : (p : ZMod (p ^ N)) ^ d ∣ x) (y : ZMod (p ^ N)) :
    (p : ZMod (p ^ N)) ^ D ∣ x * y * wneg p N c ^ t := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u * y * (-(c : ZMod (p ^ N))) ^ t, ?_⟩
  rw [hu, wneg_pow_split p N c t, ← hD, pow_add]
  ring

/-- **Dictionary lemma (ii) `digit_perturbation`** (the ⟸ direction): the strict digit floors
imply the cell's coefficient conditions — every perturbation term sits at least one level below
the on-side reads, so the cap's exact values survive untouched. -/
theorem coeffCond_of_slotPattern (hN : 0 < N) (he : 0 < e) (hμN : μ < N)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) (hb : SlotPattern p N e μ b) :
    CoeffCond p N e μ c (fun i => (assemble p N e μ c b).coeff i) := by
  have hweak : ∀ (j : Fin μ) (k r : ℕ), r < e →
      (p : ZMod (p ^ N)) ^ (μ - k)
        ∣ (b j : (ZMod (p ^ N))[X]).coeff r * (((j : ℕ)).choose k : ZMod (p ^ N))
            * wneg p N c ^ ((j : ℕ) - k) := by
    intro j k r hr
    by_cases hkj : k ≤ (j : ℕ)
    · have hjμ : (j : ℕ) < μ := j.2
      exact dvd_mul_wneg_pow p N c (by omega : (μ - (j:ℕ)) + ((j:ℕ) - k) = μ - k)
        (SlotCond.dvd_coeff p N e (hb j) hr) _
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
      exact dvd_zero _
  have hstrict : ∀ (j : Fin μ) (k : ℕ),
      (p : ZMod (p ^ N)) ^ (μ - k + 1)
        ∣ (b j : (ZMod (p ^ N))[X]).coeff 0 * (((j : ℕ)).choose k : ZMod (p ^ N))
            * wneg p N c ^ ((j : ℕ) - k) := by
    intro j k
    by_cases hkj : k ≤ (j : ℕ)
    · have hjμ : (j : ℕ) < μ := j.2
      exact dvd_mul_wneg_pow p N c
        (by omega : (μ - (j:ℕ) + 1) + ((j:ℕ) - k) = μ - k + 1) (hb j).1 _
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
      exact dvd_zero _
  constructor
  · intro k r hk hr
    show (p : ZMod (p ^ N)) ^ (μ - k) ∣ (assemble p N e μ c b).coeff (k * e + r)
    rw [assemble_coeff p N e μ c hN he b k r hr]
    refine dvd_add ?_ (Finset.dvd_sum fun j _ => hweak j k r hr)
    by_cases h0 : r = 0
    · rw [if_pos h0, cap_split p N μ c k]
      exact Dvd.intro _ rfl
    · rw [if_neg h0]
      exact dvd_zero _
  · intro k hk
    show digit p N (μ - k) ((assemble p N e μ c b).coeff (k * e)) = bres p N μ c k
    have hco := assemble_coeff p N e μ c hN he b k 0 he
    rw [Nat.add_zero, if_pos rfl] at hco
    obtain ⟨t, ht⟩ := Finset.dvd_sum fun (j : Fin μ) (_ : j ∈ Finset.univ) => hstrict j k
    rw [hco, cap_split p N μ c k, ht,
      show (p : ZMod (p ^ N)) ^ (μ - k + 1)
          = (p : ZMod (p ^ N)) ^ (μ - k) * (p : ZMod (p ^ N)) from pow_succ _ _,
      show (p : ZMod (p ^ N)) ^ (μ - k) * capU p N μ c k
            + (p : ZMod (p ^ N)) ^ (μ - k) * (p : ZMod (p ^ N)) * t
          = (p : ZMod (p ^ N)) ^ (μ - k) * (capU p N μ c k + (p : ZMod (p ^ N)) * t) by ring,
      digit_pow_mul p N (by omega : μ - k < N),
      resp_add p N hN, resp_capU p N μ c hN k, resp_mul p N hN, resp_p p N hN, zero_mul,
      add_zero]

/-- **Dictionary lemma (iii), the triangular converse** (the ⟹ direction): the cell's
coefficient conditions force every digit's strict floor — downward induction from the cap: the
LOWEST failing digit slot would win the coefficient valuation at its own column (the
dominant-transversal step), contradicting the floor/pin there. -/
theorem slotPattern_of_coeffCond (hN : 0 < N) (he : 0 < e) (hμN : μ < N)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e)
    (hcc : CoeffCond p N e μ c (fun i => (assemble p N e μ c b).coeff i)) :
    SlotPattern p N e μ b := by
  have hfloor : ∀ k r : ℕ, k < μ → r < e →
      (p : ZMod (p ^ N)) ^ (μ - k) ∣ (assemble p N e μ c b).coeff (k * e + r) :=
    fun k r hk hr => hcc.1 k r hk hr
  have hpin : ∀ k : ℕ, k < μ →
      digit p N (μ - k) ((assemble p N e μ c b).coeff (k * e)) = bres p N μ c k :=
    fun k hk => hcc.2 k hk
  have hlow : ∀ (j' : Fin μ) (k r : ℕ), (j' : ℕ) < k →
      (b j' : (ZMod (p ^ N))[X]).coeff r * (((j' : ℕ)).choose k : ZMod (p ^ N))
          * wneg p N c ^ ((j' : ℕ) - k) = 0 := by
    intro j' k r hlt
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, zero_mul]
  have main : ∀ t : ℕ, ∀ j : Fin μ, μ - (j : ℕ) ≤ t → SlotCond p N e (μ - (j : ℕ)) (b j) := by
    intro t
    induction t with
    | zero =>
        intro j hj
        exfalso
        have := j.2
        omega
    | succ t ih =>
        intro j hj
        have hjμ : (j : ℕ) < μ := j.2
        have hup_weak : ∀ r : ℕ, r < e → ∀ j' ∈ Finset.univ.erase j,
            (p : ZMod (p ^ N)) ^ (μ - (j : ℕ)) ∣
              (b j' : (ZMod (p ^ N))[X]).coeff r
                * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                * wneg p N c ^ ((j' : ℕ) - (j : ℕ)) := by
          intro r hr j' hj'
          rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with hlt | hge
          · rw [hlow j' (j : ℕ) r hlt]
            exact dvd_zero _
          · have hj'μ : (j' : ℕ) < μ := j'.2
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun hEq => (Finset.mem_erase.mp hj').1 (Fin.ext hEq)
            exact dvd_mul_wneg_pow p N c (by omega : (μ - (j':ℕ)) + ((j':ℕ) - (j:ℕ)) = μ - (j:ℕ))
              (SlotCond.dvd_coeff p N e (ih j' (by omega)) hr) _
        have hup_strict : ∀ j' ∈ Finset.univ.erase j,
            (p : ZMod (p ^ N)) ^ (μ - (j : ℕ) + 1) ∣
              (b j' : (ZMod (p ^ N))[X]).coeff 0
                * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                * wneg p N c ^ ((j' : ℕ) - (j : ℕ)) := by
          intro j' hj'
          rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with hlt | hge
          · rw [hlow j' (j : ℕ) 0 hlt]
            exact dvd_zero _
          · have hj'μ : (j' : ℕ) < μ := j'.2
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun hEq => (Finset.mem_erase.mp hj').1 (Fin.ext hEq)
            exact dvd_mul_wneg_pow p N c
              (by omega : (μ - (j':ℕ) + 1) + ((j':ℕ) - (j:ℕ)) = μ - (j:ℕ) + 1)
              (ih j' (by omega)).1 _
        have hextract : ∀ r : ℕ, r < e →
            (assemble p N e μ c b).coeff ((j : ℕ) * e + r)
              = (if r = 0 then (μ.choose (j : ℕ) : ZMod (p ^ N))
                    * wneg p N c ^ (μ - (j : ℕ)) else 0)
                + ((b j : (ZMod (p ^ N))[X]).coeff r
                  + ∑ j' ∈ Finset.univ.erase j,
                      (b j' : (ZMod (p ^ N))[X]).coeff r
                        * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                        * wneg p N c ^ ((j' : ℕ) - (j : ℕ))) := by
          intro r hr
          rw [assemble_coeff p N e μ c hN he b (j : ℕ) r hr]
          congr 1
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
          congr 1
          rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, mul_one]
        constructor
        · -- strict floor at the constant coefficient
          have hid := hextract 0 he
          rw [Nat.add_zero, if_pos rfl] at hid
          have hfl := hfloor (j : ℕ) 0 hjμ he
          rw [Nat.add_zero] at hfl
          obtain ⟨u, hu⟩ := hfl
          have hp1 := hpin (j : ℕ) hjμ
          rw [hu, digit_pow_mul p N (by omega : μ - (j : ℕ) < N)] at hp1
          have hdiff : resp p N (u - capU p N μ c (j : ℕ)) = 0 := by
            rw [resp_sub p N hN, hp1, resp_capU p N μ c hN (j : ℕ), sub_self]
          obtain ⟨w1, hw1⟩ := (resp_eq_zero_iff p N hN _).mp hdiff
          obtain ⟨T, hT⟩ := Finset.dvd_sum (hup_strict)
          exact ⟨w1 - T, by linear_combination -hid + hu - cap_split p N μ c (j : ℕ) - hT
            + (p : ZMod (p ^ N)) ^ (μ - (j : ℕ)) * hw1⟩
        · -- weak floors at the higher coefficients
          intro r hr1 hre
          have hid := hextract r hre
          rw [if_neg (by omega), zero_add] at hid
          obtain ⟨T, hT⟩ := Finset.dvd_sum (hup_weak r hre)
          obtain ⟨u, hu⟩ := hfloor (j : ℕ) r hjμ hre
          exact ⟨u - T, by rw [mul_sub, ← hu, ← hT]; linear_combination -hid⟩
  exact fun j => main μ j (by omega)

end Dictionary

/-! ## 5. The restart cell and the root-refined membership `InCellAt` -/

section Cell

open LeanUrat.OM.OMCountV2 (NodeConfig)

/-- The single-side path of slope `−1/e`, width `μ·e`: `[(0, μ), (μ·e, 0)]`. -/
def restartPath : List (ℕ × ℕ) := [(0, μ), (μ * e, 0)]

/-- The restart menu cell: single side of slope `−1/e`, residual shape `{(1, μ)}` (`mkCell`). -/
def restartCell : NodeConfig := mkCell (μ * e) (restartPath e μ) [[(1, μ)]]

theorem restartPath_menuPath (hμ2 : 2 ≤ μ) (hμN : μ < N) (he : 0 < e) :
    MenuPath (μ * e) N (restartPath e μ) :=
  ⟨μ, (μ * e, 0), [], rfl, by omega, by omega, Nat.mul_pos (by omega) he, by omega,
    ChainOK.nil rfl rfl⟩

theorem sideDeg_restart : sideDeg ((0, μ), (μ * e, 0)) = μ :=
  Nat.gcd_eq_left ⟨e, rfl⟩

theorem sideE_restart (hμ : 0 < μ) : CellCard.sideE ((0, μ), (μ * e, 0)) = e := by
  show μ * e / sideDeg ((0, μ), (μ * e, 0)) = e
  rw [sideDeg_restart e μ]
  exact Nat.mul_div_cancel_left e hμ

theorem restartShapes (hμ : 0 < μ) : ShapesFor (restartPath e μ) [[(1, μ)]] := by
  show List.Forall₂ _ [[(1, μ)]] (sidePairs (restartPath e μ))
  rw [show sidePairs (restartPath e μ) = [((0, μ), (μ * e, 0))] from rfl]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [sideDeg_restart e μ, mem_shapesOfDegree_iff]
  refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨le_refl 1, hμ⟩
  · simp

/-- The column ceiling of the restart path: `⌈μ − i/e⌉ = μ − ⌊i/e⌋`. -/
theorem ceilAt_restart (hμ : 0 < μ) (i : ℕ) (hi : i ≤ μ * e) :
    ceilAt (restartPath e μ) i = μ - i / e := by
  show (if i ≤ 0 then μ
      else if i ≤ μ * e then μ - (μ - 0) * (i - 0) / (μ * e - 0)
      else ceilAt [(μ * e, 0)] i) = μ - i / e
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos (le_refl 0), Nat.zero_div, Nat.sub_zero]
  · rw [if_neg (by omega), if_pos hi]
    congr 1
    simp only [Nat.sub_zero]
    exact Nat.mul_div_mul_left i e hμ

/-- **The root-refined cell membership**: `f` matches the menu cell AND its side residual is
exactly `(X − c̄)^μ` (the menu cell only records the SHAPE; the root pin genuinely refines at
`p ≥ 3` — d0 gate cases C1a/C1b split the p = 3 fiber 6 = 3 + 3). -/
def InCellAt (f : QuotientBox.monicBox p N (μ * e)) : Prop :=
  InCell p f (restartCell e μ) ∧
    residualOf p f ((0, μ), (μ * e, 0)) = (X - C (cbar p N c)) ^ μ

/-- The pinned target residual has coefficients `bres` (all `k`; above degree both vanish). -/
theorem target_coeff (k : ℕ) :
    ((X - C (cbar p N c)) ^ μ).coeff k = bres p N μ c k := by
  rw [sub_eq_add_neg, ← map_neg C, coeff_X_add_C_pow]
  unfold bres
  ring

theorem cbar_ne_zero (hN : 0 < N) : cbar p N c ≠ 0 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have h1 : IsUnit (cbar p N c) := by
    rw [cbar, resp_eq_castHom p N hN]; exact (Units.isUnit c).map _
  exact h1.ne_zero

theorem bres_zero_ne (hN : 0 < N) (_hμ : 0 < μ) : bres p N μ c 0 ≠ 0 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  unfold bres
  rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  exact pow_ne_zero _ (neg_ne_zero.mpr (cbar_ne_zero p N c hN))

theorem target_shape (hμ : μ ≠ 0) :
    polyShape p ((X - C (cbar p N c)) ^ μ) = ([(1, μ)] : List (ℕ × ℕ)) := by
  rw [sub_eq_add_neg, ← map_neg C, polyShape_pow_linear p (-(cbar p N c)) hμ]
  rfl

/-- The side polynomial of a digit vector on the restart side is the pinned target iff every
pattern read is the matching binomial residue. -/
theorem sidePolyR_eq_target_iff (_hN : 0 < N) (_he : 0 < e) (hμ : 0 < μ)
    (rr : Fin (μ * e) → ZMod p) :
    sidePolyR p rr ((0, μ), (μ * e, 0)) = (X - C (cbar p N c)) ^ μ
      ↔ ∀ k : ℕ, k < μ → rho p rr (k * e) = bres p N μ c k := by
  have hIdx : ∀ k : ℕ,
      ((0, μ), (μ * e, 0)).1.1 + k * CellCard.sideE ((0, μ), (μ * e, 0)) = k * e := fun k => by
    rw [sideE_restart e μ hμ]
    show 0 + k * e = k * e
    exact Nat.zero_add _
  constructor
  · intro hsp k hk
    have h2 : (sidePolyR p rr ((0, μ), (μ * e, 0))).coeff k
        = ((X - C (cbar p N c)) ^ μ).coeff k := by rw [hsp]
    rw [sidePolyR_coeff, sideDeg_restart e μ, hIdx k, target_coeff p N μ c k,
      if_pos (by omega)] at h2
    exact h2
  · intro h
    ext k
    rw [sidePolyR_coeff, sideDeg_restart e μ, hIdx k, target_coeff p N μ c k]
    by_cases hk : k < μ
    · rw [if_pos (by omega)]
      exact h k hk
    · by_cases hkμ : k = μ
      · subst hkμ
        rw [if_pos (le_refl k), rho_ge p rr (by omega)]
        unfold bres
        rw [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
      · rw [if_neg (by omega)]
        unfold bres
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- The pattern reads of the ceiling-digit vector are the level-`(μ−k)` digits. -/
theorem rho_restart_read (he : 0 < e) (hμ : 0 < μ) (f : QuotientBox.monicBox p N (μ * e))
    (k : ℕ) (hk : k < μ) :
    rho p (fun i : Fin (μ * e) =>
        digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) (k * e)
      = digit p N (μ - k) ((f.1).coeff (k * e)) := by
  have hke : k * e < μ * e := by
    have h1 : (k + 1) * e ≤ μ * e := Nat.mul_le_mul_right e (by omega)
    have h2 : (k + 1) * e = k * e + e := Nat.succ_mul k e
    omega
  rw [rho_lt p _ hke]
  show digit p N (ceilAt (restartPath e μ) (k * e)) ((f.1).coeff (k * e)) = _
  rw [ceilAt_restart e μ hμ (k * e) (le_of_lt hke),
    show k * e / e = k from by rw [Nat.mul_comm]; exact Nat.mul_div_cancel_left k he]

set_option maxHeartbeats 800000 in
/-- **The membership unpacking** (the `matches_iff` shape, e-reindexed and root-refined):
`InCellAt f` holds iff the x-adic coefficients of `f` satisfy `CoeffCond`. -/
theorem inCellAt_iff_coeffCond (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAt p N e μ c f ↔ CoeffCond p N e μ c (fun i => (f.1).coeff i) := by
  have hμ : 0 < μ := by omega
  have hP := restartPath_menuPath N e μ hμ2 hμN he
  have hsh := restartShapes e μ hμ
  have hM := matches_iff p hN hP hsh f
  have hprMem : ((0, μ), (μ * e, 0)) ∈ sidePairs (restartPath e μ) :=
    List.mem_singleton_self _
  -- floors reindexing, both ways
  have hfloors : (∀ i : Fin (μ * e),
        (p : ℕ) ^ ceilAt (restartPath e μ) i.1 ∣ (((f.1)).coeff i.1).val)
      ↔ (∀ k r : ℕ, k < μ → r < e →
          (p : ZMod (p ^ N)) ^ (μ - k) ∣ (f.1).coeff (k * e + r)) := by
    constructor
    · intro h k r hk hr
      have hi : k * e + r < μ * e := by
        have h1 : (k + 1) * e ≤ μ * e := Nat.mul_le_mul_right e (by omega)
        have h2 : (k + 1) * e = k * e + e := Nat.succ_mul k e
        omega
      have h3 := h ⟨k * e + r, hi⟩
      rw [ceilAt_restart e μ hμ (k * e + r) (le_of_lt hi),
        show (k * e + r) / e = k from by
          rw [Nat.mul_comm, Nat.mul_add_div he, Nat.div_eq_of_lt hr, Nat.add_zero]] at h3
      exact (pow_dvd_iff_dvd_val p N (by omega) _).mpr h3
    · intro h i
      have hk : i.1 / e < μ := by
        rw [Nat.div_lt_iff_lt_mul he]
        exact i.2
      have hr : i.1 % e < e := Nat.mod_lt _ he
      have hbound : ∀ g : ℕ, μ - g ≤ N := fun g => by omega
      have h3 := h (i.1 / e) (i.1 % e) hk hr
      rw [show i.1 / e * e + i.1 % e = i.1 from by
        rw [Nat.mul_comm]; exact Nat.div_add_mod i.1 e] at h3
      rw [ceilAt_restart e μ hμ i.1 (le_of_lt i.2)]
      exact (pow_dvd_iff_dvd_val p N (hbound (i.1 / e)) _).mp h3
  constructor
  · rintro ⟨hin, hres⟩
    obtain ⟨hdvd, _⟩ := hM.mp ((inCell_mkCell_iff p hP hsh).mp hin)
    have hsp : sidePolyR p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) ((0, μ), (μ * e, 0))
        = (X - C (cbar p N c)) ^ μ := by
      rw [← residualOf_eq_sidePolyR p hN hP hprMem f hdvd]
      exact hres
    refine ⟨hfloors.mp hdvd, ?_⟩
    intro k hk
    have h5 := (sidePolyR_eq_target_iff p N e μ c hN he hμ _).mp hsp k hk
    rw [rho_restart_read p N e μ he hμ f k hk] at h5
    exact h5
  · rintro ⟨hflo, hpins⟩
    have hdvd := hfloors.mpr hflo
    have hsp : sidePolyR p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) ((0, μ), (μ * e, 0))
        = (X - C (cbar p N c)) ^ μ := by
      refine (sidePolyR_eq_target_iff p N e μ c hN he hμ _).mpr ?_
      intro k hk
      rw [rho_restart_read p N e μ he hμ f k hk]
      exact hpins k hk
    have hside : SideCond p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) [(1, μ)]
        ((0, μ), (μ * e, 0)) := by
      constructor
      · rw [hsp, target_shape p N μ c (by omega)]
      · show rho p (fun i : Fin (μ * e) =>
            digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) 0 ≠ 0
        rw [show (0 : ℕ) = 0 * e from (Nat.zero_mul e).symm,
          rho_restart_read p N e μ he hμ f 0 hμ]
        rw [Nat.zero_mul]
        have h6 := hpins 0 hμ
        rw [Nat.zero_mul] at h6
        simp only [] at h6
        intro h0
        rw [h0] at h6
        exact bres_zero_ne p N μ c hN hμ h6.symm
    have hdig : DigCond p (restartPath e μ) [[(1, μ)]] (fun i : Fin (μ * e) =>
        digit p N (ceilAt (restartPath e μ) i.1) ((f.1).coeff i.1)) := by
      show List.Forall₂ _ [[(1, μ)]] (sidePairs (restartPath e μ))
      rw [show sidePairs (restartPath e μ) = [((0, μ), (μ * e, 0))] from rfl]
      exact List.Forall₂.cons hside List.Forall₂.nil
    refine ⟨(inCell_mkCell_iff p hP hsh).mpr (hM.mpr ⟨hdvd, hdig⟩), ?_⟩
    rw [residualOf_eq_sidePolyR p hN hP hprMem f hdvd]
    exact hsp

end Cell

/-! ## 6. Deliverables 2–5: `restartDigits`, THE DICTIONARY, `restartEquiv`, the fiber card -/

section Main

/-- The develop equivalence specialized to the restart key `φ` (`k = μ`, `m = e`). -/
def developPhi (hN : 0 < N) (he : 0 < e) :
    QuotientBox.monicBox p N (μ * e) ≃ (Fin μ → degreeLT (ZMod (p ^ N)) e) :=
  developEquiv p N e μ hN (phi p N e 1 c) (monic_phi p N e 1 c he)
    (natDegree_phi p N e 1 c hN) he

theorem developPhi_symm_val (hN : 0 < N) (he : 0 < e)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) :
    ((developPhi p N e μ c hN he).symm b).1 = assemble p N e μ c b := rfl

/-- **Deliverable 2 (unbundled)**: the digit avatars of `f` — the φ-adic development
(`developEquiv`) composed with the digit identification (`digitEquiv`), per digit. -/
def restartDigits' (hN : 0 < N) (he : 0 < e) (f : QuotientBox.monicBox p N (μ * e)) :
    Fin μ → Rphi p N e 1 c :=
  fun j => digitEquiv p N e 1 c hN he (developPhi p N e μ c hN he f j)

/-- **Deliverable 2**: the digit avatars of a cell-fiber element. -/
def restartDigits (hN : 0 < N) (he : 0 < e)
    (f : {f : QuotientBox.monicBox p N (μ * e) // InCellAt p N e μ c f}) :
    Fin μ → Rphi p N e 1 c :=
  restartDigits' p N e μ c hN he f.1

/-- The dictionary at develop level: `InCellAt f ⟺ SlotPattern (developPhi f)` — pieces (i),
(ii), (iii) composed through the coefficient formula. -/
theorem inCellAt_iff_slotPattern (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAt p N e μ c f ↔ SlotPattern p N e μ (developPhi p N e μ c hN he f) := by
  rw [inCellAt_iff_coeffCond p N e μ c hN he hμ2 hμN f]
  have hf : (developPhi p N e μ c hN he).symm (developPhi p N e μ c hN he f) = f :=
    Equiv.symm_apply_apply _ _
  have hval : assemble p N e μ c (developPhi p N e μ c hN he f) = f.1 := by
    rw [← developPhi_symm_val p N e μ c hN he (developPhi p N e μ c hN he f), hf]
  constructor
  · intro hcc
    refine slotPattern_of_coeffCond p N e μ c hN he hμN _ ?_
    rw [hval]
    exact hcc
  · intro hsp
    have h2 := coeffCond_of_slotPattern p N e μ c hN he hμN _ hsp
    rw [hval] at h2
    exact h2

/-- The per-slot dictionary summed: `SlotPattern b ⟺ FreshClusterPattern (digitEquiv ∘ b)`. -/
theorem slotPattern_iff_pattern (hN : 0 < N) (he : 0 < e) (hμN : μ < N)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) :
    SlotPattern p N e μ b
      ↔ FreshClusterPattern p N e μ c (fun j => digitEquiv p N e 1 c hN he (b j)) := by
  unfold SlotPattern FreshClusterPattern
  refine forall_congr' fun j => ?_
  rw [span_theta_pow_eq p N e c]
  exact (digitEquiv_mem_iff p N e c hN he (by have := j.2; omega) (b j)).symm

/-- **Deliverable 3 — THE DICTIONARY** (the one hard lemma of W4d1): root-refined cell
membership ⟺ the D0-verified fresh cluster pattern of the digit avatars. -/
theorem inCellAt_iff_pattern (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAt p N e μ c f
      ↔ FreshClusterPattern p N e μ c (restartDigits' p N e μ c hN he f) := by
  rw [inCellAt_iff_slotPattern p N e μ c hN he hμ2 hμN f,
    slotPattern_iff_pattern p N e μ c hN he hμN _]
  exact Iff.rfl

/-- **Deliverable 4 — THE RESTART EQUIVALENCE at level `N`** (W4d1): the root-refined cell
fiber is in bijection with the fresh-cluster-pattern coset. Forward: `restartDigits`; inverse:
the explicit reassembly `β ↦ φ^μ + Σ_j lift(β_j)·φ^j` (`restartEquiv_symm_apply_val`). -/
def restartEquiv (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    {f : QuotientBox.monicBox p N (μ * e) // InCellAt p N e μ c f}
      ≃ {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β} :=
  ((developPhi p N e μ c hN he).subtypeEquiv fun f =>
      inCellAt_iff_slotPattern p N e μ c hN he hμ2 hμN f).trans
    ((Equiv.piCongrRight fun _ => (digitEquiv p N e 1 c hN he).toEquiv).subtypeEquiv fun b =>
      slotPattern_iff_pattern p N e μ c hN he hμN b)

/-- The forward map of `restartEquiv` IS `restartDigits`. -/
theorem restartEquiv_apply_val (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : {f : QuotientBox.monicBox p N (μ * e) // InCellAt p N e μ c f}) :
    (restartEquiv p N e μ c hN he hμ2 hμN f).1 = restartDigits p N e μ c hN he f := rfl

/-- The inverse of `restartEquiv` is the explicit reassembly `φ^μ + Σ_j lift(β_j)·φ^j`. -/
theorem restartEquiv_symm_apply_val (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (β : {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β}) :
    (((restartEquiv p N e μ c hN he hμ2 hμN).symm β).1).1
      = phi p N e 1 c ^ μ
        + ∑ j : Fin μ, ((digitEquiv p N e 1 c hN he).symm (β.1 j) : (ZMod (p ^ N))[X])
            * phi p N e 1 c ^ (j : ℕ) := rfl

/-- **Deliverable 5**: the root-refined restart fiber card — deliverable 1 transported through
deliverables 2–4. -/
theorem card_restart_fiber (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAt p N e μ c f}
      = p ^ (μ * (N * e - 1) - e * μ * (μ + 1) / 2) := by
  rw [Nat.card_congr (restartEquiv p N e μ c hN he hμ2 hμN),
    card_freshPattern p N e μ c hN he hμN]

end Main

/-! ## 7. MANDATORY GATES (d0 SUMMARY per-case fiber cards) and the W4b cross-check -/

section Gates

/-- **Gate A** (p,N,e,μ) = (2,3,1,2), c̃' = 1 (self-loop key, e = 1): fiber `2`. -/
theorem gate_A :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 1) // InCellAt 2 3 1 2 1 f} = 2 := by
  rw [card_restart_fiber 2 3 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Gate B** (p,N,e,μ) = (2,3,2,2), c̃' = 1 (the genuine ramified restart): fiber `16`. -/
theorem gate_B :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAt 2 3 2 2 1 f} = 16 := by
  rw [card_restart_fiber 2 3 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Gate C1a** (p,N,e,μ) = (3,3,1,2), c̃' = 1 (the p = 3 root-refined case): fiber `3`. -/
theorem gate_C1a :
    Nat.card {f : QuotientBox.monicBox 3 3 (2 * 1) // InCellAt 3 3 1 2 1 f} = 3 := by
  rw [card_restart_fiber 3 3 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Gate D** (p,N,e,μ) = (2,4,2,2), c̃' = 1: fiber `256`. -/
theorem gate_D :
    Nat.card {f : QuotientBox.monicBox 2 4 (2 * 2) // InCellAt 2 4 2 2 1 f} = 256 := by
  rw [card_restart_fiber 2 4 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Gate E** (p,N,e,μ) = (2,4,1,3), c̃' = 1 (μ = 3): fiber `8`. -/
theorem gate_E :
    Nat.card {f : QuotientBox.monicBox 2 4 (3 * 1) // InCellAt 2 4 1 3 1 f} = 8 := by
  rw [card_restart_fiber 2 4 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The restart cell at (2,3,2,2) IS the W4b menu cell `mkCell 4 [(0,2),(4,0)] [[(1,2)]]`. -/
theorem restartCell_B : restartCell 2 2 = mkCell 4 [(0, 2), (4, 0)] [[(1, 2)]] := by
  norm_num [restartCell, restartPath]

/-- The W4b value of the same cell through `CellCard.cell_card_raw`: also `16`. -/
theorem crosscheck_W4b_cellCard :
    Nat.card {f : QuotientBox.monicBox 2 3 4 //
        InCell 2 f (mkCell 4 [(0, 2), (4, 0)] [[(1, 2)]])} = 16 := by
  have hP : MenuPath 4 3 [(0, 2), (4, 0)] :=
    ⟨2, (4, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      ChainOK.nil rfl rfl⟩
  have hsh : ShapesFor [(0, 2), (4, 0)] [[(1, 2)]] := by
    show List.Forall₂ _ [[(1, 2)]] [((0, 2), (4, 0))]
    exact List.Forall₂.cons (by decide) List.Forall₂.nil
  rw [cell_card_raw 2 (by norm_num) hP hsh,
    show freeExp 4 3 [(0, 2), (4, 0)] = 4 from by decide,
    show prodSC 2 [[(1, 2)]] = 1 from by simp [prodSC, shapeCount_one_two]]
  norm_num

/-- **The W4d ↔ W4b cross-check at (2,3,2,2)** (MANDATORY): the restart-equivalence count and
the W4b `cell_card_raw` count agree — both `16`. (At `p = 2` the root pin is vacuous — `F₂ˣ` is
trivial — so both sides count the same cell fiber; `restartCell_B` identifies the cells.) -/
theorem crosscheck_B :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAt 2 3 2 2 1 f}
      = Nat.card {f : QuotientBox.monicBox 2 3 4 //
          InCell 2 f (mkCell 4 [(0, 2), (4, 0)] [[(1, 2)]])} := by
  rw [gate_B, crosscheck_W4b_cellCard]

end Gates

end

end LeanUrat.OM.RestartEquiv
