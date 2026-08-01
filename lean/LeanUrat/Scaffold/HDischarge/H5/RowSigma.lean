/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H5.Kernels

/-!
# Scaffold/HDischarge/H5/RowSigma — the symbolic (ROW-Σ) skeleton [units R1, R2, R3]

Statements VERBATIM from `lean/blueprints/HDISCHARGE_H5.md` §4.4 rows R1/R2/R3;
proofs per §3 Theorems R1/R2 (mirroring the leaf D-11 r4 §2A.2/§2A.1(b), steps
renamed to units).

Unit R1: `rowSigma_solved` — Σ_σ β_e(σ) = 1 in ℚ(q) for every e ≤ n, at any
𝔅_n member carrying an `REWitness` (the (RE) operative content) and
`MassFacts` (the M1 shadow: (EXM) + (BASE); NOT proved here — displayed
hypotheses, census-layer follow-on per blueprint §3).

Proof shape (`Nat.strong_induction_on`, the `beta_memRcyc` pattern):
* e ≤ 1: (BASE) = `M.base_total`.
* 2 ≤ e ≤ n: `hsolve` + `hblockU` give β_e(σ) = u⁻¹·t_σ with
  u = solveU(booking, e) = 1 − q·q^{−E} (re-entrant branch, fired by
  `W.booking_reentrant`); then
  1. [telescoping, unit K4 = `sum_rowOf`] Σ_σ t_σ = Σ_F m(F)·∏ᵢ (Σ_σ′
     powSubst Dᵢ (β_{μᵢ}(σ′)));
  2. [leg normalization] each inner sum = powSubst Dᵢ (Σ_σ′ β_{μᵢ}(σ′)) =
     powSubst Dᵢ 1 = 1 (`map_sum`/`map_one`; μᵢ < e by `W.handoff_lt`, IH);
  3. [mass input] Σ_F m(F) = 1 − κ₀ − κ₁ = u by (EXM) = `M.mass_complete`
     + `kappa_add`;
  4. [close] Σ_σ β_e(σ) = u⁻¹·u = 1 (`hu.1`).

Unit R2: `rowSigma_displayed_O1` / `rowSigma_displayed_O2r` /
`rowSigma_displayed_O3` — the three per-booking DISPLAYED totals (§3 Theorem
R2 = leaf §2A.1(b) EXACTLY): three DIFFERENT values, no booking's displayed
total is 1 (the round-4-finding-2 honesty display, machine-checked).
* (O1):  Σ_σ displayedRow = 1 − κ₀ − κ₁  (steps 1–3 alone);
* (O2′): Σ_σ displayedRow = (1 − κ₀ − κ₁) + κ₁·(Σ_σ β_e) = 1 − κ₀
  (consumes R1 at e);
* (O3):  Σ_σ displayedRow = q^E/(q^E − 1)·(1 − κ₀ − κ₁) = 1 − (q−1)/(q^E − 1)
  (`field_simp`/`ring` against `q^E − 1 ≠ 0`, the `kernel_ne_zero`
  ingredient re-derived via `cycS_ne_zero` + `Xpow_sub_one_mem_cycS`).

Falsifier gate (§5, pre-registered): the n = 2 totals against the landed N2
solve values are a scratch-level `#eval`-class check; the standing
`verification/` RESUM-n3 65/65 record exercises the n = 3 instances.
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst)

/-- The re-entrant branch of `Booking.solveU`, keyed by the (RE) disequality
`booking ≠ O2`: all three re-entrant bookings solve by `u = 1 − q·q^{−E}`
(helper for R1 step 0; the `Booking.O2` branch is never consumed under
`booking_reentrant`). -/
theorem solveU_reentrant {b : Booking} (hb : b ≠ Booking.O2) (e : ℕ) :
    b.solveU e = 1 - qX * (qX ^ blockE e)⁻¹ := by
  cases b with
  | O1 => rfl
  | O2 => exact absurd rfl hb
  | O2r => rfl
  | O3 => rfl

/-- **Unit R1** (symbolic (ROW-Σ)(a)): at any 𝔅_n member carrying an
`REWitness` and `MassFacts`, the solved row sums to 1 symbolically in ℚ(q) at
every block e ≤ n. Strong induction on e: (BASE) at e ≤ 1; at 2 ≤ e the block
solve β_e(σ) = u⁻¹·t_σ (re-entrant u, `hblockU` + `booking_reentrant`),
K4 telescoping + ring-hom leg normalization + (EXM) + `kappa_add` give
Σ_σ t_σ = u, and `hu.1` closes. [HDISCHARGE_H5 unit R1] -/
theorem rowSigma_solved {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) :
    ∀ e, e ≤ n → (∑ σ : SplittingType n, T.β e σ) = 1 := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro hen
    rcases Nat.lt_or_ge e 2 with he | he
    -- (BASE): e ≤ 1 is the trivial solve, one decided verdict with β = 1.
    · exact M.base_total e (Nat.lt_succ_iff.mp he)
    -- Step 0: the block solve factors out u⁻¹.
    · have hsum : (∑ σ : SplittingType n, T.β e σ)
          = (T.blocks e he).u⁻¹ * ∑ σ : SplittingType n, (T.blocks e he).trow σ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => (T.blocks e he).hsolve σ
      -- Steps 1–2: the canonical-row total collapses to the exit-mass total.
      have htrow : (∑ σ : SplittingType n, (T.blocks e he).trow σ)
          = ∑ F : (W.exits e).idx, (W.exits e).mass F := by
        rw [W.trow_canonical e he]
        simp only [tRow]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun F _ => ?_
        -- [K4 telescoping] then [leg normalization] on each hand-off leg.
        rw [sum_rowOf]
        have hprod : (∏ i : Fin ((W.exits e).handoff F).length,
            ∑ σ' : SplittingType n,
              powSubst (((W.exits e).handoff F).get i).2
                (T.β (((W.exits e).handoff F).get i).1 σ')) = 1 := by
          refine Finset.prod_eq_one fun i _ => ?_
          have hlt : (((W.exits e).handoff F).get i).1 < e :=
            W.handoff_lt e F _ (((W.exits e).handoff F).get_mem i)
          rw [← map_sum, ih _ hlt (le_of_lt (lt_of_lt_of_le hlt hen)), map_one]
        rw [hprod, mul_one]
      -- Step 3 input: (EXM) gives the exit-mass total 1 − κ₀ − κ₁, which is u.
      have hu_eq : (T.blocks e he).u = 1 - kappa0 e - kappa1 e := by
        rw [T.hblockU e he, solveU_reentrant W.booking_reentrant e, sub_sub,
          kappa_add]
      -- Step 4: close by u⁻¹·u = 1 (u ≠ 0 = `hu.1`).
      rw [hsum, htrow, M.mass_complete e he hen, ← hu_eq,
        inv_mul_cancel₀ (T.blocks e he).hu.1]

/-! ## Unit R2 — the three per-booking displayed totals (symbolic (ROW-Σ)(b)) -/

/-- Telescoping collapse of the canonical-row total (K4 + leg normalization,
factored for reuse across R2's three bookings): when every hand-off leg's
lower-block total is 1, the σ-total of `tRow` collapses to the exit-mass
total — `sum_rowOf` (K4) telescopes each stratum, and the ring hom `powSubst`
normalizes each leg (`map_sum`/`map_one`). [HDISCHARGE_H5 unit R2 helper] -/
theorem sum_tRow {n : ℕ} (β : ℕ → SplittingType n → Qq) (E : ExitData n)
    (hleg : ∀ F : E.idx, ∀ x ∈ E.handoff F,
      (∑ σ : SplittingType n, β x.1 σ) = 1) :
    (∑ σ : SplittingType n, tRow β E σ) = ∑ F : E.idx, E.mass F := by
  simp only [tRow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [sum_rowOf]
  have hprod : (∏ i : Fin (E.handoff F).length,
      ∑ σ' : SplittingType n,
        powSubst ((E.handoff F).get i).2 (β ((E.handoff F).get i).1 σ')) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← map_sum, hleg F _ ((E.handoff F).get_mem i), map_one]
  rw [hprod, mul_one]

/-- The R1-fed leg totals at block e: every hand-off leg of every exit stratum
sums to 1, by `rowSigma_solved` at the lower block μ < e ≤ n (`handoff_lt`).
[HDISCHARGE_H5 unit R2 helper] -/
theorem legTotals {n : ℕ} (T : BnMember n) (W : REWitness T) (M : MassFacts T W)
    {e : ℕ} (hen : e ≤ n) :
    ∀ F : (W.exits e).idx, ∀ x ∈ (W.exits e).handoff F,
      (∑ σ : SplittingType n, T.β x.1 σ) = 1 := fun F x hx =>
  rowSigma_solved T W M x.1
    (le_of_lt (lt_of_lt_of_le (W.handoff_lt e F x hx) hen))

/-- **Unit R2, (O1)** (symbolic (ROW-Σ)(b), first booking total): at (O1) the
displayed row IS the canonical row t, and its σ-total is the exit-mass total
1 − κ₀ − κ₁ = Φ^{(O1)} — steps 1–3 of the R1 induction alone (telescoping +
leg normalization + (EXM)); NOT 1 (leaf §2A.1(b), the round-4-finding-2
honesty display). [HDISCHARGE_H5 unit R2] -/
theorem rowSigma_displayed_O1 {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) (hb : T.booking = Booking.O1) {e : ℕ}
    (he2 : 2 ≤ e) (hen : e ≤ n) :
    (∑ σ : SplittingType n, displayedRow T.booking e T.β (W.exits e) σ)
      = 1 - kappa0 e - kappa1 e := by
  rw [hb]
  simp only [displayedRow]
  rw [sum_tRow T.β (W.exits e) (legTotals T W M hen), M.mass_complete e he2 hen]

/-- **Unit R2, (O2′)** (symbolic (ROW-Σ)(b), second booking total): the (O2′)
displayed row carries the κ₁-coefficient re-fed exit leg, so its σ-total is
(1 − κ₀ − κ₁) + κ₁·(Σ_σ β_e(σ)) = 1 − κ₀ (consumes R1 at e); NOT 1 (leaf
§2A.1(b)). [HDISCHARGE_H5 unit R2] -/
theorem rowSigma_displayed_O2r {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) (hb : T.booking = Booking.O2r) {e : ℕ}
    (he2 : 2 ≤ e) (hen : e ≤ n) :
    (∑ σ : SplittingType n, displayedRow T.booking e T.β (W.exits e) σ)
      = 1 - kappa0 e := by
  rw [hb]
  simp only [displayedRow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_tRow T.β (W.exits e) (legTotals T W M hen), M.mass_complete e he2 hen,
    rowSigma_solved T W M e hen, mul_one]
  ring

/-- **Unit R2, (O3)** (symbolic (ROW-Σ)(b), third booking total): the (O3)
displayed row carries the exit scaling q^E/(q^E − 1), so its σ-total is
q^E/(q^E − 1)·(1 − κ₀ − κ₁) = 1 − (q−1)/(q^E − 1); NOT 1 (leaf §2A.1(b)).
The division is licensed by q^E ≠ 0 and q^E − 1 ≠ 0 (the `kernel_ne_zero`
ingredient: q^E − 1 is the image of the 𝒮-member X^E − 1).
[HDISCHARGE_H5 unit R2] -/
theorem rowSigma_displayed_O3 {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) (hb : T.booking = Booking.O3) {e : ℕ}
    (he2 : 2 ≤ e) (hen : e ≤ n) :
    (∑ σ : SplittingType n, displayedRow T.booking e T.β (W.exits e) σ)
      = 1 - (qX - 1) * (qX ^ blockE e - 1)⁻¹ := by
  have hpow : qX ^ blockE e ≠ 0 := qX_pow_ne_zero _
  have hE1 : 1 ≤ blockE e := by
    have := blockE_ge_three he2; omega
  have hsubne : qX ^ blockE e - 1 ≠ 0 := by
    have himg : qX ^ blockE e - 1
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      simp [qX, map_sub, map_pow]
    rw [himg]
    exact RatFunc.algebraMap_ne_zero
      (MovesU.cycS_ne_zero (MovesU.Xpow_sub_one_mem_cycS hE1))
  rw [hb]
  simp only [displayedRow]
  rw [← Finset.mul_sum,
    sum_tRow T.β (W.exits e) (legTotals T W M hen), M.mass_complete e he2 hen,
    kappa0, kappa1]
  field_simp

/-- **Unit R3** (evaluated (ROW-Σ)(a)): the solved row sums to 1 at every
rational pool q₀ ≥ 2 — the subring-coercion sum identifies the `OKat q₀`
subtype total with R1's symbolic total, and `map_sum`/`map_one` of the
`evalAt q₀` ring hom evaluate it; membership binders from K2b
(`bnMember_beta_mem_OKat`). This is the form unit B2 consumes and the
(PACK-ii) upper bound rides. [HDISCHARGE_H5 unit R3] -/
theorem rowSigma_eval {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) {q₀ : ℚ} (hq : 2 ≤ q₀) {e : ℕ} (he : e ≤ n) :
    (∑ σ : SplittingType n,
      evalAt q₀ ⟨T.β e σ, bnMember_beta_mem_OKat T e σ q₀ hq⟩) = 1 := by
  rw [← map_sum]
  have hsub : (∑ σ : SplittingType n,
      (⟨T.β e σ, bnMember_beta_mem_OKat T e σ q₀ hq⟩ : OKat q₀)) = 1 := by
    refine Subtype.ext ?_
    push_cast
    exact rowSigma_solved T W M e he
  rw [hsub, map_one]

end LeanUrat.Scaffold.HDischarge.H5
