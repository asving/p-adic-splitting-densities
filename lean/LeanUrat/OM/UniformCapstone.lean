/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.UniformModelN2Recovery
import LeanUrat.MontesV2

/-!
# OM/UniformCapstone — Wave W6q-c: THE ALL-PRIMES UNIFORMITY CAPSTONE `montes_uniform_n2`
(blueprint `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §0/§1.2–§1.4/§2-W6q-c; ground truth
`notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (ACCEPTED), general-`q` throughout)

## The prize (blueprint §0)

**`montes_uniform_n2`**: FIXED polynomials per degree-2 type — `numR = 1, denR = X + 1`
(ramified), `numI = numS = X, denI = denS = 2X + 2` (inert and split) — defined ONCE, with
NO prime mentioned anywhere in them, such that for EVERY prime `p` (the wild `p = 2`
INCLUDED):

* (R) the density family `q' ↦ ∑_{T ∈ shapesOfU σ} CU T q'` equals `numₛ(q')/denₛ(q')` at
  every `q' > 1` — uniform rationality with the fixed, syntactically `p`-free `num/den`;
* (V) `(M7 p).countingDensity σ = numₛ(p)/denₛ(p)` with `denₛ(p) ≠ 0` — the genuine
  `N → ∞` decided-limit density of the COMPLETE `n = 2` stratum tree at `p`;
* (B) bracket uniqueness fired OUTRIGHT via the general-`p` exhaustion `hExhaustP`
  (pure counting, no axiom, discharged at every `p`).

The fixed values: `R_ram = 1/(q+1)`, `R_inert = R_split = q/(2(q+1))`, `Σ = 1`
(`gate_uniform_checksum`). This is the paper's theorem at `n = 2`: ONE rational function of
the prime, uniformly over all primes including the wild one (`gate_wild_included`).

## The engine (this module, over the W6q-b model `UniformModelN2`)

1. **The folded-weight bank (blueprint §1.3, the Codex-mandated discipline)**: each descend
   step's pool factor and digit probability are carried as ONE combined weight, never
   separately. Named lemmas FIRST: `w_step_le_half` (`(q−1)/q² ≤ 1/2`), `w_sum_le_third`
   (`Σ_m (q−1)q^{−2m} ≤ 1/(q+1) ≤ 1/3`), `w_dom` (`(q−1)q^{−2m} ≤ (1/2)^m`) — the blueprint
   §1.3 domination bank, recording the `q`-uniformity of the envelope constants. The two
   CONSUMED per-step sums: `stall_sum_le_one` (`Σ_m (q−1)q^{−m} ≤ 1`, the CRITICAL folded
   stall weight — at `q = 2` this is W6's `Σ (1/2)^m ≤ 1`) and `fix_sum_le`
   (`Σ_m (q−1)q^{−3m} ≤ (q−1)/(q³−1)`, the per-step descend ratio `r(q) = 1/(q²+q+1)` —
   at `q = 2` W6's `Σ (1/8)^m ≤ 1/7`).
2. **The generalized weighted slope-menu sum `msWP D K a r = Σ_{ms} a^{len} r^{Σms}`** with
   the two composition bounds: `msWP_stall_le` (`msWP D K (q−1) (1/q) ≤ D + 1`, the
   msW_half_le analogue — folded weight exactly critical, SAME polynomial-in-`N` constant
   as W6) and `msWP_fix_le` (`msWP D K (q−1) (1/q³) ≤ (q²+q+1)/(q²+q) = 1/(1−r(q))`, the
   msW_eighth_le analogue — the fixpoint closes EXACTLY at the blueprint §1.2 values).
   Per the Codex-mandated order, the normalized-count-to-∏w comparison
   (`transStallCountP_leW`: stall count `≤ q^N · (q−1)^len (1/q)^Σ`) is established BEFORE
   any composition bound is applied.
3. **The general-`p` envelope** `undecided_envelopeP`:
   `undecidedCountP p N / p^{2N} ≤ (⌊N/2⌋+1) · p^{−(N−1)}` for all `N ≥ 1` — the SAME
   constant shape as W6 (`C = 1`); `hExhaustP`: the envelope → 0 at every `p` (the
   exhaustion clause discharged unconditionally, ∀ p, pure counting).
4. **The per-family ledger and the squeeze (blueprint §1.2/§1.4)**: exact depth-0
   coefficient values (`chainC_ram_leafP` `= (q−1)q^{−3j}`, `chainC_inert_leafP`
   `= (q²−q)/2 · q^{−(3m+2)}`, `chainC_split_leafP` `= (q−1)q^{−(3k+2)}`, splitU
   `uLeafC = (q−1)(q−2)/2 · q^{−(3m+2)}`), the per-stratum exact normalized counts
   (`transChainCountP_cast`/`transChainCountU_cast` — count `= chainC · box` above
   threshold), the per-type upper bound `decidedP_le_valueP` closing EXACTLY at the fixed
   values (the `(q−1)`-cancellation ledger of blueprint §1.2 — the depth-0 checksum
   `[q² + q/2 + (q−2)/2 + 1 + 1]/(q²+q+1) = 1` is what makes the three closures exact),
   the lower bound via box partition + envelope, and the two-sided squeeze
   `uniformDecided_tendsto`.
5. **The model `M7 p : CountingModel p 2`** (the W6 `realMW6` construction at arbitrary
   `p`, over the W6q-b counts), the one-marker `MontesDataV2` instance `uniformD p`
   (bookkeeping markers, as in W6 — the interface is deliberately weak per its own
   docstring; the semantics live in the count definitions and the squeeze theorems here),
   and THE CAPSTONE fired through the V2 spine at `(M7 p, uniformD p)` for every `p`.

## Census anchors (blueprint §0/§4 mitigation, machine-checked in the gates)

* `p = 2` (the WILD prime): `1/3, 1/3, 1/3 = R_σ(2)` — `gate_uniform_p2_*`; and the
  model-level tie `gate_wild_included`: `(M7 2).countingDensity σ` IS the W6
  machine-checked `realMW6.countingDensity σ` (same counts by
  `UniformModelN2Recovery.decidedCountP_two_eq`, hence same limit).
* `p = 3`: `1/4, 3/8, 3/8 = R_σ(3)` — `gate_uniform_p3_*` (the fresh census mod `3⁷`:
  ram 182/729, inert = split = 91/243, undecided EXACTLY `3^{−6}` at `N = 7`; the note §7
  Case B mod `3⁶` run: `β_ram = 3/4 = q/(q+1)` ✓).
* checksum `Σ_σ R_σ(p) = 1` at every `p` — `gate_uniform_checksum`.

## Honest scope

* **Counting-side only**: the fibers are digit-condition fibers (`ChainPair`/`ChainPairU`
  composed through `descendPair`, translated by `affineEquiv`); σ-keying faithfulness is
  W6q-d's business (the `fullFiber7`-successor over re-scope #6), packaged separately.
* **Palindromy is OUT OF SCOPE by directive** (Asvin, 2026-07-22, post-W6c): the capstone
  carries NO `htameFE` hypothesis and NO palindromy clause. Consequently it cannot fire
  `MontesV2.goal_theorem_montes` itself (whose conclusion bundles palindromy from the
  `htameFE` input); it fires the SAME V2 spine one theorem lower —
  `MontesDataV2.countingDensity_eq_sum_coeff` at `(M7 p, uniformD p)`, the exact
  decomposition theorem `goal_theorem_montes` routes the value clause through. (The true
  uniform densities `1/(q+1)`, `q/(2(q+1))` are NOT palindromic, so the W6-style
  conditional clause would be vacuous baggage — the directive cuts it.)
* NO axiom, NO `sorry` anywhere: every declaration must be Lean-core-only (`AxCheck`
  below); `om_leaf_faithful` in the capstone cone is a FAILURE.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.UniformCapstone

open scoped Classical
open LeanUrat LeanUrat.CountingModel LeanUrat.RatFn Polynomial Filter Topology
open LeanUrat.OM
open LeanUrat.OM.QuotientBox
open LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox
open LeanUrat.OM.ChainMenu
open LeanUrat.OM.ChainMenuU
open LeanUrat.OM.UniformModelN2

/-! ## §P. THE FIXED POLYNOMIALS (defined ONCE, before any prime is mentioned — the
`p`-independence of the capstone's rational functions is SYNTACTICALLY manifest) -/

/-- Ramified numerator: `1`. -/
noncomputable def numR : Polynomial ℚ := 1

/-- Ramified denominator: `X + 1` (`R_ram(q) = 1/(q+1)`). -/
noncomputable def denR : Polynomial ℚ := X + 1

/-- Inert numerator: `X`. -/
noncomputable def numI : Polynomial ℚ := X

/-- Inert denominator: `2X + 2` (`R_inert(q) = q/(2(q+1))`). -/
noncomputable def denI : Polynomial ℚ := 2 * X + 2

/-- Split numerator: `X` — IDENTICAL to the inert one (the split/inert symmetry of the
uniform ledger, blueprint §1.2). -/
noncomputable def numS : Polynomial ℚ := X

/-- Split denominator: `2X + 2`. -/
noncomputable def denS : Polynomial ℚ := 2 * X + 2

theorem numR_eval (x : ℚ) : numR.eval x = 1 := by simp [numR]

theorem denR_eval (x : ℚ) : denR.eval x = x + 1 := by simp [denR]

theorem numI_eval (x : ℚ) : numI.eval x = x := by simp [numI]

theorem denI_eval (x : ℚ) : denI.eval x = 2 * x + 2 := by simp [denI]

theorem numS_eval (x : ℚ) : numS.eval x = x := by simp [numS]

theorem denS_eval (x : ℚ) : denS.eval x = 2 * x + 2 := by simp [denS]

theorem denR_ne_zero : denR ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  rw [denR_eval] at this
  norm_num at this

theorem denI_ne_zero : denI ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  rw [denI_eval] at this
  norm_num at this

theorem denS_ne_zero : denS ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  rw [denS_eval] at this
  norm_num at this

/-- The per-type FIXED numerator (off-menu types get `0`). -/
noncomputable def uniformNum (σ : FactorizationType) : Polynomial ℚ :=
  if σ = ramType2 then numR
  else if σ = inertType2 then numI
  else if σ = splitType2 then numS
  else 0

/-- The per-type FIXED denominator (off-menu types get `1`). -/
noncomputable def uniformDen (σ : FactorizationType) : Polynomial ℚ :=
  if σ = ramType2 then denR
  else if σ = inertType2 then denI
  else if σ = splitType2 then denS
  else 1

theorem uniformDen_ne_zero (σ : FactorizationType) : uniformDen σ ≠ 0 := by
  unfold uniformDen
  split_ifs
  · exact denR_ne_zero
  · exact denI_ne_zero
  · exact denS_ne_zero
  · exact one_ne_zero

/-- **The FIXED value function (blueprint §1.2)**: `R_ram = 1/(q+1)`,
`R_inert = R_split = q/(2(q+1))`; `0` off the degree-2 menu. -/
noncomputable def uniformValueFn (σ : FactorizationType) (q' : ℕ) : ℚ :=
  if σ = ramType2 then 1 / ((q' : ℚ) + 1)
  else if σ = inertType2 then (q' : ℚ) / (2 * ((q' : ℚ) + 1))
  else if σ = splitType2 then (q' : ℚ) / (2 * ((q' : ℚ) + 1))
  else 0

theorem uniformValueFn_off {σ : FactorizationType} (hσ : σ ∉ typeMenuP) (q' : ℕ) :
    uniformValueFn σ q' = 0 := by
  unfold typeMenuP at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rw [not_or, not_or] at hσ
  unfold uniformValueFn
  rw [if_neg hσ.1, if_neg hσ.2.1, if_neg hσ.2.2]

theorem uniformValueFn_nonneg (σ : FactorizationType) (q' : ℕ) :
    0 ≤ uniformValueFn σ q' := by
  unfold uniformValueFn
  split_ifs
  · positivity
  · positivity
  · positivity
  · exact le_refl 0

/-- The value function IS the fixed rational function at every `q'` (denominators are
pole-free on all of `ℕ`). -/
theorem uniformValueFn_eq_eval (σ : FactorizationType) (q' : ℕ) :
    uniformValueFn σ q'
      = (uniformNum σ).eval (q' : ℚ) / (uniformDen σ).eval (q' : ℚ) := by
  unfold uniformValueFn uniformNum uniformDen
  split_ifs
  · rw [numR_eval, denR_eval]
  · rw [numI_eval, denI_eval]
    congr 1
    ring
  · rw [numS_eval, denS_eval]
    congr 1
    ring
  · simp

theorem uniformDen_eval_ne (σ : FactorizationType) {q' : ℕ} (hq' : 0 < q') :
    (uniformDen σ).eval (q' : ℚ) ≠ 0 := by
  have hq : (0 : ℚ) < (q' : ℚ) := by exact_mod_cast hq'
  unfold uniformDen
  split_ifs
  · rw [denR_eval]; positivity
  · rw [denI_eval]; positivity
  · rw [denS_eval]; positivity
  · simp

/-- **Uniform rationality of the fixed value family** — witnessed by THE fixed
`uniformNum/uniformDen`, not an existential pair. -/
theorem uniformValueFn_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => uniformValueFn σ q') :=
  ⟨uniformNum σ, uniformDen σ, uniformDen_ne_zero σ, fun q' hq' =>
    ⟨uniformDen_eval_ne σ (by omega), uniformValueFn_eq_eval σ q'⟩⟩

/-! ## §Q. The generalized weighted slope-menu sum (the W6 `msW` with the pool folded in:
`msWP D K a r = Σ_{ms ∈ msMenu D K} a^{length} · r^{Σms}` — ONE combined weight per step,
per the Codex discipline; at `a = 1` this IS W6's `msW`) -/

/-- The folded-weight slope-menu sum. -/
noncomputable def msWP (D K : ℕ) (a r : ℚ) : ℚ :=
  ∑ ms ∈ msMenu D K, a ^ ms.length * r ^ ms.sum

theorem msWP_zero (K : ℕ) (a r : ℚ) : msWP 0 K a r = 1 := by
  unfold msWP
  show ∑ ms ∈ ({[]} : Finset (List ℕ)), a ^ ms.length * r ^ ms.sum = 1
  rw [Finset.sum_singleton]
  simp

/-- The depth recurrence `msWP (D+1) = 1 + (Σ_{m≤K} a·r^m) · msWP D` (the menu recursion
summed — mirror of W6's `msW_succ` with the folded weight). -/
theorem msWP_succ (D K : ℕ) (a r : ℚ) :
    msWP (D + 1) K a r = 1 + (∑ m ∈ Finset.Icc 1 K, a * r ^ m) * msWP D K a r := by
  unfold msWP
  show ∑ ms ∈ ({[]} : Finset (List ℕ))
      ∪ (Finset.Icc 1 K ×ˢ msMenu D K).image (fun x => x.1 :: x.2),
        a ^ ms.length * r ^ ms.sum = _
  rw [Finset.sum_union (by
    refine Finset.disjoint_left.mpr fun _ms hms hms' => ?_
    rw [Finset.mem_singleton] at hms
    rw [Finset.mem_image] at hms'
    obtain ⟨x, -, hx⟩ := hms'
    rw [hms] at hx
    exact List.cons_ne_nil x.1 x.2 hx)]
  rw [Finset.sum_singleton, List.sum_nil, List.length_nil, pow_zero, pow_zero, mul_one]
  congr 1
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    have h1 := List.head_eq_of_cons_eq hxy
    have h2 := List.tail_eq_of_cons_eq hxy
    exact Prod.ext h1 h2)]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun tl _ => ?_
  rw [List.sum_cons, List.length_cons]
  ring

theorem msWP_nonneg (D K : ℕ) {a r : ℚ} (ha : 0 ≤ a) (hr : 0 ≤ r) : 0 ≤ msWP D K a r :=
  Finset.sum_nonneg fun _ms _ => mul_nonneg (pow_nonneg ha _) (pow_nonneg hr _)

section PrimeBank

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## §R. The prime-cast bank -/

theorem pQ_two : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.two_le

theorem pQ_pos : (0 : ℚ) < (p : ℚ) := by
  have := pQ_two p
  linarith

theorem pQ_one_lt : (1 : ℚ) < (p : ℚ) := by
  have := pQ_two p
  linarith

theorem pQ_ne : ((p : ℚ)) ≠ 0 := ne_of_gt (pQ_pos p)

theorem pQ_pow_pos (k : ℕ) : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (pQ_pos p) k

theorem pQ_pow_ne (k : ℕ) : ((p : ℚ) ^ k) ≠ 0 := ne_of_gt (pQ_pow_pos p k)

theorem pQ_sub_one_nonneg : (0 : ℚ) ≤ (p : ℚ) - 1 := by
  have := pQ_two p
  linarith

theorem pQ_sub_one_cast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]

theorem pQ_sub_two_cast : ((p - 2 : ℕ) : ℚ) = (p : ℚ) - 2 := by
  rw [Nat.cast_sub hp.out.two_le]
  norm_num

theorem pQ_cube_sub_one_pos : (0 : ℚ) < (p : ℚ) ^ 3 - 1 := by
  have h := pQ_two p
  have h8 : (2 : ℚ) ^ 3 ≤ (p : ℚ) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
  norm_num at h8
  linarith

theorem pQ_sq_sub_one_pos : (0 : ℚ) < (p : ℚ) ^ 2 - 1 := by
  have h := pQ_two p
  nlinarith

theorem pQ_sq_add_pos : (0 : ℚ) < (p : ℚ) ^ 2 + p := by
  have h := pQ_two p
  nlinarith

theorem pQ_sq_add_add_pos : (0 : ℚ) < (p : ℚ) ^ 2 + p + 1 := by
  have h := pQ_two p
  nlinarith

theorem pQ_add_one_pos : (0 : ℚ) < (p : ℚ) + 1 := by
  have h := pQ_two p
  linarith

/-! ## §A. The folded-weight lemma bank (blueprint §1.3, named lemmas FIRST)

The blueprint's per-step domination facts, recording the `q`-uniformity of every envelope
constant: `w_m(q) := (q−1)·q^{−2m}` has `w_1 ≤ 1/2`, `Σ w_m = 1/(q+1) ≤ 1/3`, and
`w_m ≤ (1/2)^m` — all monotone non-increasing in `q` on `q ≥ 2`. The envelope's stall leg
consumes the CRITICAL folded weight `(q−1)·q^{−m}` (`stall_sum_le_one`, per-step sum ≤ 1 —
exactly W6's critical ratio, whence the SAME `⌊N/2⌋+1` polynomial constant); the squeeze's
fixpoint leg consumes `(q−1)·q^{−3m}` (`fix_sum_le`, per-step sum ≤ `r(q) = 1/(q²+q+1)`). -/

/-- Exact finite geometric sum against `1/p`, cleared-denominator form:
`(p−1) · Σ_{m=1}^{K} (1/p)^m = 1 − (1/p)^K`. -/
theorem sum_Icc_pinv (K : ℕ) :
    ((p : ℚ) - 1) * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ))⁻¹) ^ m = 1 - (((p : ℚ))⁻¹) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), mul_add, ih]
      have hkey : ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ (K + 1)
          = (((p : ℚ))⁻¹) ^ K - (((p : ℚ))⁻¹) ^ (K + 1) := by
        have hc : (p : ℚ) * ((p : ℚ))⁻¹ = 1 := mul_inv_cancel₀ (pQ_ne p)
        calc ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ (K + 1)
            = ((p : ℚ) * ((p : ℚ))⁻¹) * (((p : ℚ))⁻¹) ^ K - (((p : ℚ))⁻¹) ^ (K + 1) := by
              rw [pow_succ]
              ring
          _ = (((p : ℚ))⁻¹) ^ K - (((p : ℚ))⁻¹) ^ (K + 1) := by rw [hc, one_mul]
      linarith

/-- Exact finite geometric sum against `1/p²`, cleared-denominator form. -/
theorem sum_Icc_pinv_sq (K : ℕ) :
    ((p : ℚ) ^ 2 - 1) * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 2)⁻¹) ^ m
      = 1 - (((p : ℚ) ^ 2)⁻¹) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), mul_add, ih]
      have hkey : ((p : ℚ) ^ 2 - 1) * (((p : ℚ) ^ 2)⁻¹) ^ (K + 1)
          = (((p : ℚ) ^ 2)⁻¹) ^ K - (((p : ℚ) ^ 2)⁻¹) ^ (K + 1) := by
        have hc : (p : ℚ) ^ 2 * ((p : ℚ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pQ_pow_ne p 2)
        calc ((p : ℚ) ^ 2 - 1) * (((p : ℚ) ^ 2)⁻¹) ^ (K + 1)
            = ((p : ℚ) ^ 2 * ((p : ℚ) ^ 2)⁻¹) * (((p : ℚ) ^ 2)⁻¹) ^ K
                - (((p : ℚ) ^ 2)⁻¹) ^ (K + 1) := by
              rw [pow_succ]
              ring
          _ = (((p : ℚ) ^ 2)⁻¹) ^ K - (((p : ℚ) ^ 2)⁻¹) ^ (K + 1) := by rw [hc, one_mul]
      linarith

/-- Exact finite geometric sum against `1/p³`, cleared-denominator form. -/
theorem sum_Icc_pinv_cube (K : ℕ) :
    ((p : ℚ) ^ 3 - 1) * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m
      = 1 - (((p : ℚ) ^ 3)⁻¹) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), mul_add, ih]
      have hkey : ((p : ℚ) ^ 3 - 1) * (((p : ℚ) ^ 3)⁻¹) ^ (K + 1)
          = (((p : ℚ) ^ 3)⁻¹) ^ K - (((p : ℚ) ^ 3)⁻¹) ^ (K + 1) := by
        have hc : (p : ℚ) ^ 3 * ((p : ℚ) ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pQ_pow_ne p 3)
        calc ((p : ℚ) ^ 3 - 1) * (((p : ℚ) ^ 3)⁻¹) ^ (K + 1)
            = ((p : ℚ) ^ 3 * ((p : ℚ) ^ 3)⁻¹) * (((p : ℚ) ^ 3)⁻¹) ^ K
                - (((p : ℚ) ^ 3)⁻¹) ^ (K + 1) := by
              rw [pow_succ]
              ring
          _ = (((p : ℚ) ^ 3)⁻¹) ^ K - (((p : ℚ) ^ 3)⁻¹) ^ (K + 1) := by rw [hc, one_mul]
      linarith

/-- **The blueprint §1.3 single-step weight bound**: `w_1(q) = (q−1)/q² ≤ 1/2` for every
prime `q` (`⟺ (q−1)² + 1 > 0`). -/
theorem w_step_le_half : ((p : ℚ) - 1) / (p : ℚ) ^ 2 ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (pQ_pow_pos p 2) (by norm_num : (0 : ℚ) < 2)]
  nlinarith [sq_nonneg ((p : ℚ) - 1)]

/-- **The blueprint §1.3 per-step domination, sum form**:
`Σ_{m=1}^{K} (q−1)·q^{−2m} ≤ 1/(q+1)`. -/
theorem w_sum_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 2)⁻¹) ^ m ≤ 1 / ((p : ℚ) + 1) := by
  rw [← Finset.mul_sum]
  have hgeo := sum_Icc_pinv_sq p K
  have hpos := pQ_sq_sub_one_pos p
  have hy : (0 : ℚ) ≤ (((p : ℚ) ^ 2)⁻¹) ^ K := by positivity
  have hS : ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 2)⁻¹) ^ m ≤ 1 / ((p : ℚ) ^ 2 - 1) := by
    rw [le_div_iff₀ hpos, mul_comm]
    linarith
  have hfac : ((p : ℚ) - 1) / ((p : ℚ) ^ 2 - 1) = 1 / ((p : ℚ) + 1) := by
    rw [div_eq_div_iff (ne_of_gt hpos) (ne_of_gt (pQ_add_one_pos p))]
    ring
  calc ((p : ℚ) - 1) * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 2)⁻¹) ^ m
      ≤ ((p : ℚ) - 1) * (1 / ((p : ℚ) ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hS (pQ_sub_one_nonneg p)
    _ = 1 / ((p : ℚ) + 1) := by rw [mul_one_div, hfac]

/-- **`w_sum_le_third` (blueprint §1.3)**: the per-step domination closes below `1/3`
uniformly on `q ≥ 2` — `Σ_m (q−1)·q^{−2m} ≤ 1/(q+1) ≤ 1/3`. -/
theorem w_sum_le_third (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 2)⁻¹) ^ m ≤ 1 / 3 := by
  refine le_trans (w_sum_le p K) ?_
  rw [div_le_div_iff₀ (pQ_add_one_pos p) (by norm_num : (0 : ℚ) < 3)]
  have := pQ_two p
  linarith

/-- **`w_dom` (blueprint §1.3)**: the folded weight is dominated by W6's `q = 2` weight,
`(q−1)·q^{−2m} ≤ (1/2)^m` for every `m ≥ 1` — the `q`-monotonicity that makes every W6
chain-sum relaxation go through at general `q` with the same constants. -/
theorem w_dom (m : ℕ) (hm : 1 ≤ m) :
    ((p : ℚ) - 1) * (((p : ℚ) ^ 2)⁻¹) ^ m ≤ (1 / 2 : ℚ) ^ m := by
  have hP := pQ_pos p
  have h2 := pQ_two p
  -- (q−1)·(q²)^{−m} ≤ q·q^{−2m} = q^{−(2m−1)} ≤ 2^{−(2m−1)} ≤ 2^{−m}
  have h1 : ((p : ℚ) - 1) * (((p : ℚ) ^ 2)⁻¹) ^ m ≤ (((p : ℚ))⁻¹) ^ (2 * m - 1) := by
    have hpow : (((p : ℚ) ^ 2)⁻¹) ^ m = (((p : ℚ))⁻¹) ^ (2 * m) := by
      rw [← inv_pow, ← pow_mul]
    rw [hpow, show 2 * m = (2 * m - 1) + 1 by omega, pow_succ]
    have hbound : ((p : ℚ) - 1) * ((p : ℚ))⁻¹ ≤ 1 := by
      rw [← le_div_iff₀ (by positivity : (0 : ℚ) < ((p : ℚ))⁻¹), one_div, inv_inv]
      linarith
    calc ((p : ℚ) - 1) * ((((p : ℚ))⁻¹) ^ (2 * m - 1) * ((p : ℚ))⁻¹)
        = (((p : ℚ) - 1) * ((p : ℚ))⁻¹) * (((p : ℚ))⁻¹) ^ (2 * m - 1) := by ring
      _ ≤ 1 * (((p : ℚ))⁻¹) ^ (2 * m - 1) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = (((p : ℚ))⁻¹) ^ (2 * m - 1) := one_mul _
  have hinv : ((p : ℚ))⁻¹ ≤ (2 : ℚ)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have h2' : (((p : ℚ))⁻¹) ^ (2 * m - 1) ≤ ((2 : ℚ)⁻¹) ^ (2 * m - 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have h3 : ((2 : ℚ)⁻¹) ^ (2 * m - 1) ≤ ((2 : ℚ)⁻¹) ^ m := by
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc ((p : ℚ) - 1) * (((p : ℚ) ^ 2)⁻¹) ^ m
      ≤ (((p : ℚ))⁻¹) ^ (2 * m - 1) := h1
    _ ≤ ((2 : ℚ)⁻¹) ^ (2 * m - 1) := h2'
    _ ≤ ((2 : ℚ)⁻¹) ^ m := h3
    _ = (1 / 2 : ℚ) ^ m := by norm_num

/-- **The CRITICAL folded stall weight sums to ≤ 1** (the consumed per-step fact for the
envelope): `Σ_{m=1}^{K} (q−1)·q^{−m} = 1 − q^{−K} ≤ 1`. At `q = 2` this is exactly W6's
`sum_Icc_half_le`; the ratio is critical at EVERY `q`, whence the same `⌊N/2⌋+1` factor. -/
theorem stall_sum_le_one (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ m ≤ 1 := by
  rw [← Finset.mul_sum, sum_Icc_pinv p K]
  have : (0 : ℚ) ≤ (((p : ℚ))⁻¹) ^ K := by positivity
  linarith

theorem stall_sum_nonneg (K : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ m :=
  Finset.sum_nonneg fun m _ =>
    mul_nonneg (pQ_sub_one_nonneg p) (pow_nonneg (by positivity) m)

/-- **The fixpoint folded weight sums to ≤ `(q−1)/(q³−1) = r(q) = 1/(q²+q+1)`** (the
consumed per-step fact for the squeeze — note §4's per-step descend ratio; at `q = 2`
W6's `sum_Icc_eighth_le : ≤ 1/7`). -/
theorem fix_sum_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 3)⁻¹) ^ m
      ≤ ((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1) := by
  rw [← Finset.mul_sum]
  have hgeo := sum_Icc_pinv_cube p K
  have hpos := pQ_cube_sub_one_pos p
  have hy : (0 : ℚ) ≤ (((p : ℚ) ^ 3)⁻¹) ^ K := by positivity
  have hS : ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m ≤ 1 / ((p : ℚ) ^ 3 - 1) := by
    rw [le_div_iff₀ hpos, mul_comm]
    linarith
  calc ((p : ℚ) - 1) * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m
      ≤ ((p : ℚ) - 1) * (1 / ((p : ℚ) ^ 3 - 1)) :=
        mul_le_mul_of_nonneg_left hS (pQ_sub_one_nonneg p)
    _ = ((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1) := by rw [mul_one_div]

theorem fix_sum_nonneg (K : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 3)⁻¹) ^ m :=
  Finset.sum_nonneg fun m _ =>
    mul_nonneg (pQ_sub_one_nonneg p) (pow_nonneg (by positivity) m)

/-- The plain `1/p³` geometric tail bound (for pulling constants out of leaf sums):
`Σ_{m=1}^{K} (q^{−3})^m ≤ 1/(q³−1)`. -/
theorem sum_pcube_inv_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m ≤ 1 / ((p : ℚ) ^ 3 - 1) := by
  have hgeo := sum_Icc_pinv_cube p K
  have hpos := pQ_cube_sub_one_pos p
  have hy : (0 : ℚ) ≤ (((p : ℚ) ^ 3)⁻¹) ^ K := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  linarith

theorem sum_pcube_inv_nonneg (K : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m :=
  Finset.sum_nonneg fun m _ => pow_nonneg (by positivity) m

/-! ## §B. The two composition bounds (the msW_half_le / msW_eighth_le analogues) -/

/-- **The critical-ratio composition bound (msW_half_le analogue)**:
`Σ_{ms ∈ msMenu D K} (q−1)^{len} q^{−Σms} ≤ D + 1` — each depth contributes ≤ 1 (the folded
stall weight is exactly critical at every `q`, per `stall_sum_le_one`). -/
theorem msWP_stall_le (D K : ℕ) : msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹) ≤ (D : ℚ) + 1 := by
  induction D with
  | zero => rw [msWP_zero]; norm_num
  | succ D ih =>
      rw [msWP_succ]
      have hS := stall_sum_le_one p K
      have hS0 := stall_sum_nonneg p K
      have hW0 : 0 ≤ msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹) :=
        msWP_nonneg D K (pQ_sub_one_nonneg p) (by positivity)
      have hstep : (∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ m)
          * msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹) ≤ (D : ℚ) + 1 := by
        calc (∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ))⁻¹) ^ m)
            * msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹)
            ≤ 1 * msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹) :=
              mul_le_mul_of_nonneg_right hS hW0
          _ = msWP D K ((p : ℚ) - 1) (((p : ℚ))⁻¹) := one_mul _
          _ ≤ (D : ℚ) + 1 := ih
      push_cast
      linarith

/-- **The fixpoint composition bound (msW_eighth_le analogue)**:
`Σ_{ms ∈ msMenu D K} (q−1)^{len} q^{−3Σms} ≤ (q²+q+1)/(q²+q) = 1/(1 − r(q))` — the
geometric closure of the depth tower at the per-step descend ratio `r(q) = 1/(q²+q+1)`
(blueprint §1.2 Fixpoints; note §4 Claim 4.4(ii) at general `q`). -/
theorem msWP_fix_le (D K : ℕ) :
    msWP D K ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
      ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p) := by
  have hBpos := pQ_sq_add_pos p
  have hB1 : (1 : ℚ) ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p) := by
    rw [le_div_iff₀ hBpos]
    linarith
  induction D with
  | zero => rw [msWP_zero]; exact hB1
  | succ D ih =>
      rw [msWP_succ]
      have hS := fix_sum_le p K
      have hS0 := fix_sum_nonneg p K
      have hW0 : 0 ≤ msWP D K ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹) :=
        msWP_nonneg D K (pQ_sub_one_nonneg p) (by positivity)
      have hr0 : (0 : ℚ) ≤ ((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1) :=
        div_nonneg (pQ_sub_one_nonneg p) (le_of_lt (pQ_cube_sub_one_pos p))
      have hprod : (∑ m ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 3)⁻¹) ^ m)
          * msWP D K ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          ≤ (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1))
            * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)) :=
        mul_le_mul hS ih hW0 hr0
      have hkey : 1 + (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1))
          * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p))
          = ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p) := by
        have h4 : ((p : ℚ) ^ 3 - 1) ≠ 0 := ne_of_gt (pQ_cube_sub_one_pos p)
        have h5 : ((p : ℚ) ^ 2 + p) ≠ 0 := ne_of_gt hBpos
        have hp0 : ((p : ℚ)) ≠ 0 := pQ_ne p
        field_simp
        ring
      linarith

/-! ## §C. The per-family ledger (blueprint §1.2): exact depth-0 coefficient values,
the chain-coefficient factorization, and the exact per-level count identities -/

/-- Depth-0 ramified leaf value at general `p`: `chainC [] (ram (2j−1)) p = (q−1)·q^{−3j}`
(the `H = 2j−1` rung; blueprint §1.2 `ram H` row). -/
theorem chainC_ram_leafP (j : ℕ) (hj : 1 ≤ j) :
    chainC [] (ChainLeaf.ram (2 * j - 1)) p = ((p : ℚ) - 1) * (((p : ℚ) ^ 3)⁻¹) ^ j := by
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.ram (2 * j - 1)) = 3 * j := by
    simp only [chainVolExp, eLeaf, List.sum_nil]
    omega
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  rw [inv_pow, ← pow_mul]

/-- Depth-0 inert leaf value at general `p`:
`chainC [] (inert m) p = (q²−q)/2 · q^{−2} · q^{−3m}` (root-free residual pool). -/
theorem chainC_inert_leafP (m : ℕ) :
    chainC [] (ChainLeaf.inert m) p
      = ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (((p : ℚ) ^ 3)⁻¹) ^ m := by
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.inert m) = 3 * m + 2 := by
    simp [chainVolExp, eLeaf]
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  rw [pow_add, mul_inv, inv_pow, ← pow_mul]
  ring

/-- Depth-0 two-sided split leaf value at general `p`:
`chainC [] (split k) p = (q−1) · q^{−2} · q^{−3k}`. -/
theorem chainC_split_leafP (k : ℕ) :
    chainC [] (ChainLeaf.split k) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (((p : ℚ) ^ 3)⁻¹) ^ k := by
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.split k) = 3 * k + 2 := by
    simp [chainVolExp, eLeaf]
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  rw [pow_add, mul_inv, inv_pow, ← pow_mul]
  ring

/-- **The chain-coefficient factorization at general `p`** (the W6 `chainC_realP_factor`
with the pool carried): `chainC ms leaf p = (q−1)^{len} · q^{−3Σms} · chainC [] leaf p` —
the folded per-step weight times the leaf value. -/
theorem chainC_factorP (ms : List ℕ) (leaf : ChainLeaf) :
    chainC ms leaf p
      = ((p : ℚ) - 1) ^ ms.length * (((p : ℚ) ^ 3)⁻¹) ^ ms.sum * chainC [] leaf p := by
  rw [chainC, chainC, eval_chainMult, eval_chainMult]
  simp only [List.length_nil, List.sum_nil, pow_zero, one_mul]
  have hV : chainVolExp ms leaf = 3 * ms.sum + chainVolExp [] leaf := by
    simp [chainVolExp]
  rw [hV, pow_add, mul_inv]
  have h3 : (((p : ℚ) ^ 3)⁻¹) ^ ms.sum = ((p : ℚ) ^ (3 * ms.sum))⁻¹ := by
    rw [inv_pow, ← pow_mul]
  rw [h3]
  ring

/-- The rectangular chain-coefficient sum factorizes:
`Σ_{(ms,leaf)} chainC = msWP · leafSum` (mirror of W6's `sum_rect_chainC`). -/
theorem sum_rect_chainCP (D K K' : ℕ) (σ : FactorizationType) :
    ∑ x ∈ msMenu D K ×ˢ chainLeaves K' σ, chainC x.1 x.2 p
      = msWP D K ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
        * ∑ leaf ∈ chainLeaves K' σ, chainC [] leaf p := by
  rw [Finset.sum_product]
  unfold msWP
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ms _ => Finset.sum_congr rfl fun leaf _ => ?_
  rw [chainC_factorP p ms leaf]

/-! ### The splitU coefficient (the NEW family; honestly empty at `q = 2`) -/

/-- The splitU pool count in `ℚ`: `#rootedPairs = (q−1)(q−2)/2` (vanishes at `q = 2` —
the honest-empty family; `1` at `q = 3`, the census pool check). -/
theorem card_rootedPairs_castQ :
    (((rootedPairs p).card : ℕ) : ℚ) = ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 := by
  have h := two_mul_card_rootedPairs p
  have hc : (2 : ℚ) * (((rootedPairs p).card : ℕ) : ℚ)
      = ((p - 1 : ℕ) : ℚ) * ((p - 2 : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) h
  rw [pQ_sub_one_cast p, pQ_sub_two_cast p] at hc
  linarith

/-- The order-0 split pool count in `ℚ`: `#splitResPairs = (q²−q)/2`. -/
theorem card_splitResPairs_castQ :
    (((splitResPairs p).card : ℕ) : ℚ) = ((p : ℚ) ^ 2 - p) / 2 := by
  have h := two_mul_card_splitResPairs p
  have hc : (2 : ℚ) * (((splitResPairs p).card : ℕ) : ℚ)
      = (p : ℚ) * ((p - 1 : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) h
  rw [pQ_sub_one_cast p] at hc
  nlinarith [hc]

/-- **The depth-0 splitU coefficient** `uLeafC m q = (q−1)(q−2)/2 · q^{−2} · q^{−3m}`
(blueprint §1.1 splitU row: pool `(q−1)(q−2)/2`, per-height mass `q^{−3m}`). -/
noncomputable def uLeafC (m : ℕ) (q' : ℕ) : ℚ :=
  ((q' : ℚ) - 1) * ((q' : ℚ) - 2) / 2 * ((q' : ℚ) ^ 2)⁻¹ * (((q' : ℚ) ^ 3)⁻¹) ^ m

/-- **The splitU chain coefficient**, in factored form: folded step weight × leaf value. -/
noncomputable def chainCU (ms : List ℕ) (m : ℕ) (q' : ℕ) : ℚ :=
  ((q' : ℚ) - 1) ^ ms.length * (((q' : ℚ) ^ 3)⁻¹) ^ ms.sum * uLeafC m q'

theorem uLeafC_nonneg (m : ℕ) : 0 ≤ uLeafC m p := by
  unfold uLeafC
  have h2 := pQ_two p
  have h1 : (0 : ℚ) ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 := by
    have : (0 : ℚ) ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) := mul_nonneg (by linarith) (by linarith)
    linarith
  positivity

theorem chainCU_nonneg (ms : List ℕ) (m : ℕ) : 0 ≤ chainCU ms m p := by
  unfold chainCU
  have h1 := uLeafC_nonneg p m
  have h2 : (0 : ℚ) ≤ ((p : ℚ) - 1) ^ ms.length := pow_nonneg (pQ_sub_one_nonneg p) _
  positivity

/-- The rectangular splitU sum factorizes (the splitU coefficient is BORN factored). -/
theorem sum_rect_chainCU (D K K' : ℕ) :
    ∑ x ∈ msMenu D K ×ˢ Finset.Icc 1 K', chainCU x.1 x.2 p
      = msWP D K ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹) * ∑ m ∈ Finset.Icc 1 K', uLeafC m p := by
  rw [Finset.sum_product]
  unfold msWP
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ms _ => Finset.sum_congr rfl fun m _ => ?_
  unfold chainCU
  ring

/-! ### The exact per-level count identities (count = coefficient × box above threshold,
`0` below — the blueprint §1.2 ledger made per-level exact) -/

/-- Below the threshold the translated main-chain fiber is EMPTY. -/
theorem transChainCountP_zero_of_lt (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) {N : ℕ}
    (hlt : N < 2 * ms.sum + leafNeed leaf) :
    transChainCountP p c ms leaf N = 0 := by
  rw [transChainCountP_eq_pair]
  haveI : IsEmpty {a : pairBoxP p N // ChainPair p ms leaf N N a} :=
    ⟨fun x => chainPair_empty p ms leaf N N hlt _ x.2⟩
  exact Nat.card_of_isEmpty

/-- **The exact main-chain per-level identity** (above threshold): the translated count is
EXACTLY `chainC ms leaf p · p^{2N}` — translation is count-exact, and the closed form is
the blueprint §1.2 digit-freedom mass. -/
theorem transChainCountP_cast (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) {N : ℕ}
    (hthr : 2 * ms.sum + leafNeed leaf ≤ N) :
    ((transChainCountP p c ms leaf N : ℕ) : ℚ) = chainC ms leaf p * (p : ℚ) ^ (2 * N) := by
  rw [transChainCountP_eq_pair]
  have hN0 : 0 < N := by
    have := one_le_leafNeed leaf
    omega
  have e : {f : QuotientBox.monicBox p N 2 // ChainCell p ms leaf f}
      ≃ {a : pairBoxP p N // ChainPair p ms leaf N N a} :=
    Equiv.subtypeEquiv (coeffEquiv p N hN0) (fun f => Iff.rfl)
  rw [← Nat.card_congr e, card_chainCell_cast p ms leaf hms hOK hthr,
    chainC, eval_chainMult]
  have hVle := chainVolExp_le_two_mul ms leaf hthr
  have hsplit : (p : ℚ) ^ (2 * N)
      = (p : ℚ) ^ chainVolExp ms leaf * (p : ℚ) ^ (2 * N - chainVolExp ms leaf) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have h1 : ((p : ℚ)) ^ chainVolExp ms leaf ≠ 0 := pQ_pow_ne p _
  field_simp

/-- The per-stratum bound, all levels: the translated main-chain count never exceeds its
coefficient × box (mirror of W6's `transChainCount_le_coeff`). -/
theorem transChainCountP_le_coeff (c : ℕ) {ms : List ℕ} {leaf : ChainLeaf}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) (N : ℕ) :
    ((transChainCountP p c ms leaf N : ℕ) : ℚ)
      ≤ chainC ms leaf p * (p : ℚ) ^ (2 * N) := by
  rcases Nat.lt_or_ge N (2 * ms.sum + leafNeed leaf) with hlt | hge
  · rw [transChainCountP_zero_of_lt p c ms leaf hlt, Nat.cast_zero]
    exact mul_nonneg (chainC_nonneg ms leaf p) (le_of_lt (pQ_pow_pos p _))
  · exact le_of_eq (transChainCountP_cast p c ms leaf hms hOK hge)

/-- Below the threshold the translated splitU fiber is EMPTY. -/
theorem transChainCountU_zero_of_lt (c : ℕ) (ms : List ℕ) (m : ℕ) {N : ℕ}
    (hlt : N < 2 * ms.sum + leafNeedU m) :
    transChainCountU p c ms m N = 0 := by
  rw [transChainCountU_eq_pair]
  haveI : IsEmpty {a : pairBoxP p N // ChainPairU p ms m N N a} :=
    ⟨fun x => chainPairU_empty p ms m N N hlt _ x.2⟩
  exact Nat.card_of_isEmpty

/-- **The exact splitU per-level identity** (above threshold): the translated splitU count
is EXACTLY `chainCU ms m p · p^{2N}`. -/
theorem transChainCountU_cast (c : ℕ) (ms : List ℕ) (m : ℕ)
    (hms : ∀ x ∈ ms, 1 ≤ x) (hm : 1 ≤ m) {N : ℕ}
    (hthr : 2 * ms.sum + leafNeedU m ≤ N) :
    ((transChainCountU p c ms m N : ℕ) : ℚ) = chainCU ms m p * (p : ℚ) ^ (2 * N) := by
  rw [transChainCountU_eq_pair, card_chainPairU p ms m hms hm N N hthr le_rfl]
  simp only [leafNeedU] at hthr
  unfold leafCountU
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
    pQ_sub_one_cast p, card_rootedPairs_castQ p]
  unfold chainCU uLeafC
  have hy : ∀ k : ℕ, (((p : ℚ) ^ 3)⁻¹) ^ k = ((p : ℚ) ^ (3 * k))⁻¹ := fun k => by
    rw [inv_pow, ← pow_mul]
  rw [hy, hy]
  have hsplit : (p : ℚ) ^ (2 * N)
      = (p : ℚ) ^ (3 * ms.sum) * ((p : ℚ) ^ 2 * ((p : ℚ) ^ (3 * m)
        * ((p : ℚ) ^ (N - 2 * ms.sum - 2 * m - 1) * (p : ℚ) ^ (N - ms.sum - m - 1)))) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [hsplit]
  have h0 : ((p : ℚ)) ≠ 0 := pQ_ne p
  have h1 : ((p : ℚ)) ^ (3 * ms.sum) ≠ 0 := pQ_pow_ne p _
  have h2 : ((p : ℚ)) ^ 2 ≠ 0 := pQ_pow_ne p 2
  have h3 : ((p : ℚ)) ^ (3 * m) ≠ 0 := pQ_pow_ne p _
  field_simp

/-- The splitU per-stratum bound, all levels. -/
theorem transChainCountU_le_coeff (c : ℕ) {ms : List ℕ} {m : ℕ}
    (hms : ∀ x ∈ ms, 1 ≤ x) (hm : 1 ≤ m) (N : ℕ) :
    ((transChainCountU p c ms m N : ℕ) : ℚ) ≤ chainCU ms m p * (p : ℚ) ^ (2 * N) := by
  rcases Nat.lt_or_ge N (2 * ms.sum + leafNeedU m) with hlt | hge
  · rw [transChainCountU_zero_of_lt p c ms m hlt, Nat.cast_zero]
    exact mul_nonneg (chainCU_nonneg p ms m) (le_of_lt (pQ_pow_pos p _))
  · exact le_of_eq (transChainCountU_cast p c ms m hms hm hge)

/-! ### The window-`K` leaf sums (blueprint §1.2 family sums, bounded by their geometric
closures — `q = 2` values in ⟨⟩ recover W6's `1/7, 1/28, 1/28`) -/

/-- Ramified leaf sum `≤ (q−1)/(q³−1) = 1/(q²+q+1)` ⟨`1/7`⟩. -/
theorem sum_leaf_ramP_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K ramType2, chainC [] leaf p
      ≤ ((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1) := by
  rw [chainLeaves, if_pos rfl]
  rw [Finset.sum_image (by
    intro j hj j' hj' h
    rw [Finset.mem_coe, Finset.mem_Icc] at hj hj'
    have := ChainLeaf.ram.inj h
    omega)]
  calc ∑ j ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.ram (2 * j - 1)) p
      = ∑ j ∈ Finset.Icc 1 K, ((p : ℚ) - 1) * (((p : ℚ) ^ 3)⁻¹) ^ j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        exact chainC_ram_leafP p j hj.1
    _ ≤ ((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1) := fix_sum_le p K

/-- Inert leaf sum `≤ (q²−q)/2 · q^{−2} · 1/(q³−1)` ⟨`1/28`⟩. -/
theorem sum_leaf_inertP_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K inertType2, chainC [] leaf p
      ≤ ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_inert), if_pos rfl]
  rw [Finset.sum_image (by
    intro j _ j' _ h
    exact ChainLeaf.inert.inj h)]
  have hpool : (0 : ℚ) ≤ ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ := by
    have h2 := pQ_two p
    have h1 : (0 : ℚ) ≤ ((p : ℚ) ^ 2 - p) := by nlinarith
    positivity
  calc ∑ m ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.inert m) p
      = ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
          * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by
          rw [chainC_inert_leafP p m]
    _ ≤ ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) :=
        mul_le_mul_of_nonneg_left (sum_pcube_inv_le p K) hpool

/-- Two-sided split leaf sum `≤ (q−1) · q^{−2} · 1/(q³−1)` ⟨`1/28`⟩. -/
theorem sum_leaf_splitP_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K splitType2, chainC [] leaf p
      ≤ ((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split),
    if_pos rfl]
  rw [Finset.sum_image (by
    intro j _ j' _ h
    exact ChainLeaf.split.inj h)]
  have hpool : (0 : ℚ) ≤ ((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ := by
    have h1 := pQ_sub_one_nonneg p
    positivity
  calc ∑ k ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.split k) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [chainC_split_leafP p k]
    _ ≤ ((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) :=
        mul_le_mul_of_nonneg_left (sum_pcube_inv_le p K) hpool

theorem sum_leaf_nonnegP (K : ℕ) (σ : FactorizationType) :
    0 ≤ ∑ leaf ∈ chainLeaves K σ, chainC [] leaf p :=
  Finset.sum_nonneg fun leaf _ => chainC_nonneg [] leaf p

/-- The splitU leaf sum `≤ (q−1)(q−2)/2 · q^{−2} · 1/(q³−1)` ⟨`0` at `q = 2`⟩. -/
theorem sum_uLeaf_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, uLeafC m p
      ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) := by
  have hpool : (0 : ℚ) ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹ := by
    have h2 := pQ_two p
    have h1 : (0 : ℚ) ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) := mul_nonneg (by linarith) (by linarith)
    positivity
  calc ∑ m ∈ Finset.Icc 1 K, uLeafC m p
      = ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
          * ∑ m ∈ Finset.Icc 1 K, (((p : ℚ) ^ 3)⁻¹) ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by
          unfold uLeafC
          ring
    _ ≤ ((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1)) :=
        mul_le_mul_of_nonneg_left (sum_pcube_inv_le p K) hpool

theorem sum_uLeaf_nonneg (K : ℕ) : 0 ≤ ∑ m ∈ Finset.Icc 1 K, uLeafC m p :=
  Finset.sum_nonneg fun m _ => uLeafC_nonneg p m

/-! ### The order-0 exact values -/

theorem ord0Count_zero (σ : FactorizationType) : ord0Count p σ 0 = 0 := by
  unfold ord0Count
  have h1 : Nat.card {a : pairBoxP p 0 // Ord0SplitCell p 0 a} = 0 := by
    haveI : IsEmpty {a : pairBoxP p 0 // Ord0SplitCell p 0 a} :=
      ⟨fun x => ord0Split_zero_empty p x.1 x.2⟩
    exact Nat.card_of_isEmpty
  have h2 : Nat.card {a : pairBoxP p 0 // Ord0InertCell p 0 a} = 0 := by
    haveI : IsEmpty {a : pairBoxP p 0 // Ord0InertCell p 0 a} :=
      ⟨fun x => ord0Inert_zero_empty p x.1 x.2⟩
    exact Nat.card_of_isEmpty
  rw [h1, h2]
  split_ifs <;> simp

/-- The normalized order-0 pool weight per keyed type: `(q²−q)/2 · q^{−2} = (q−1)/(2q)` for
split/inert, `0` for everything else (blueprint §1.1: order-0 leaves contribute `(q−1)/(2q)`
to each of split/inert). -/
noncomputable def ord0Q (σ : FactorizationType) : ℚ :=
  (if σ = splitType2 then ((p : ℚ) ^ 2 - p) / 2
   else if σ = inertType2 then ((p : ℚ) ^ 2 - p) / 2 else 0) * ((p : ℚ) ^ 2)⁻¹

theorem ord0Q_nonneg (σ : FactorizationType) : 0 ≤ ord0Q p σ := by
  unfold ord0Q
  have h2 := pQ_two p
  have h1 : (0 : ℚ) ≤ ((p : ℚ) ^ 2 - p) := by nlinarith
  split_ifs
  · positivity
  · positivity
  · simp

/-- **The exact order-0 per-level identity** (`N ≥ 1`): `ord0Count σ N = ord0Q σ · p^{2N}`. -/
theorem ord0Count_eq (σ : FactorizationType) {N : ℕ} (hN : 1 ≤ N) :
    ord0Count p σ N = ord0Q p σ * (p : ℚ) ^ (2 * N) := by
  have hpow : (p : ℚ) ^ (N - 1) * (p : ℚ) ^ (N - 1) = (p : ℚ) ^ (2 * N) * ((p : ℚ) ^ 2)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pQ_pow_ne p 2), ← pow_add, ← pow_add]
    congr 1
    omega
  unfold ord0Count ord0Q
  split_ifs with h1 h2
  · rw [card_ord0Split p N hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      card_splitResPairs_castQ p, hpow]
    ring
  · rw [card_ord0Inert p N hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      card_noRootPairs_q p, hpow]
    ring
  · ring

/-! ## §D. The stall bridge and the folded-weight stall comparison -/

/-- `StallPairP` IS W6's general-`p` `StallPair` — identical recursion (the bridge the
blueprint's implementation note calls for; no transcription of the count bound needed). -/
theorem stallPairP_iff (ms : List ℕ) : ∀ (L₀ L₁ : ℕ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)),
    StallPairP p ms L₀ L₁ a ↔ SeriesAssembly.StallPair p ms L₀ L₁ a := by
  induction ms with
  | nil => intro L₀ L₁ a; exact Iff.rfl
  | cons m tl ih =>
      intro L₀ L₁ a
      constructor
      · rintro ⟨c, hstep, hrest⟩
        exact ⟨c, hstep, (ih _ _ _).mp hrest⟩
      · rintro ⟨c, hstep, hrest⟩
        exact ⟨c, hstep, (ih _ _ _).mpr hrest⟩

/-- The stall count bound transported to `StallPairP` (the banked general-`p`
`SeriesAssembly.card_stallPair_le` through the bridge): `≤ (p−1)^{len} · p^{L₁−Σms}`. -/
theorem card_stallPairP_le (ms : List ℕ) (hms : ∀ m ∈ ms, 1 ≤ m) (L₀ L₁ : ℕ)
    (hbud : ms ≠ [] → 2 * ms.sum + 2 ≤ L₀) (h01 : L₀ ≤ L₁) (hL₁ : 1 ≤ L₁) :
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StallPairP p ms L₀ L₁ a}
      ≤ (p - 1) ^ ms.length * p ^ (L₁ - ms.sum) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => stallPairP_iff p ms L₀ L₁ a))]
  exact SeriesAssembly.card_stallPair_le p ms hms L₀ L₁ hbud h01 hL₁

/-- **The normalized-count-to-∏w comparison (the Codex-mandated FIRST step, blueprint
§1.3)**: each translated stall count is bounded by `q^N ×` the folded weight
`(q−1)^{len}·q^{−Σms}` — pool factor and digit probability carried as ONE combined weight,
established BEFORE any composition bound is applied. -/
theorem transStallCountP_leW (c : ℕ) {ms : List ℕ} {N : ℕ} (hN : 0 < N)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hbud : ms ≠ [] → 2 * ms.sum + 2 ≤ N) (hsum : ms.sum ≤ N) :
    ((transStallCountP p c ms N : ℕ) : ℚ)
      ≤ (p : ℚ) ^ N * (((p : ℚ) - 1) ^ ms.length * (((p : ℚ))⁻¹) ^ ms.sum) := by
  rw [transStallCountP_eq_pair]
  have hcard := card_stallPairP_le p ms hms N N hbud le_rfl (by omega)
  calc ((Nat.card {a : pairBoxP p N // StallPairP p ms N N a} : ℕ) : ℚ)
      ≤ (((p - 1) ^ ms.length * p ^ (N - ms.sum) : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = (p : ℚ) ^ N * (((p : ℚ) - 1) ^ ms.length * (((p : ℚ))⁻¹) ^ ms.sum) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, pQ_sub_one_cast p]
        have hpow : (p : ℚ) ^ (N - ms.sum) = (p : ℚ) ^ N * (((p : ℚ))⁻¹) ^ ms.sum := by
          rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pQ_pow_ne p ms.sum), ← pow_add]
          congr 1
          omega
        rw [hpow]
        ring

/-- The general-`p` stall total: all `p` residue points × the level-`N` stall index
(`SeriesAssembly.stallIdx` is prime-free and reused as-is). -/
noncomputable def stallTotalP (N : ℕ) : ℚ :=
  ∑ c ∈ Finset.range p, ∑ ms ∈ SeriesAssembly.stallIdx N,
    ((transStallCountP p c ms N : ℕ) : ℚ)

/-- **The stall total bound** (composition applied AFTER the per-stratum comparison):
`stallTotalP ≤ q · (⌊N/2⌋+1) · q^N` — the ≤-relaxed folded chain sum at the critical
ratio, `q`-uniform constant `C = 1` (the W6 constant shape). -/
theorem stallTotalP_le (N : ℕ) (hN : 0 < N) :
    stallTotalP p N ≤ (p : ℚ) * ((((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N) := by
  unfold stallTotalP
  have hper : ∀ c : ℕ,
      ∑ ms ∈ SeriesAssembly.stallIdx N, ((transStallCountP p c ms N : ℕ) : ℚ)
        ≤ (((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N := by
    intro c
    calc ∑ ms ∈ SeriesAssembly.stallIdx N, ((transStallCountP p c ms N : ℕ) : ℚ)
        ≤ ∑ ms ∈ SeriesAssembly.stallIdx N,
            (p : ℚ) ^ N * (((p : ℚ) - 1) ^ ms.length * (((p : ℚ))⁻¹) ^ ms.sum) := by
          refine Finset.sum_le_sum fun ms hms => ?_
          rw [SeriesAssembly.stallIdx, Finset.mem_filter, mem_msMenu] at hms
          refine transStallCountP_leW p c hN (fun m hm => (hms.1.2 m hm).1)
            (fun hnil => ?_) ?_
          · rcases hms.2 with h | h
            · exact absurd h hnil
            · exact h
          · rcases hms.2 with h | h
            · subst h
              simp
            · omega
      _ = (p : ℚ) ^ N * ∑ ms ∈ SeriesAssembly.stallIdx N,
            ((p : ℚ) - 1) ^ ms.length * (((p : ℚ))⁻¹) ^ ms.sum := by
          rw [Finset.mul_sum]
      _ ≤ (p : ℚ) ^ N * msWP (N / 2) N ((p : ℚ) - 1) (((p : ℚ))⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (pQ_pow_pos p N))
          unfold msWP SeriesAssembly.stallIdx
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro ms _ _
          exact mul_nonneg (pow_nonneg (pQ_sub_one_nonneg p) _)
            (pow_nonneg (by positivity) _)
      _ ≤ (p : ℚ) ^ N * ((((N / 2 : ℕ) : ℚ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (pQ_pow_pos p N))
          exact msWP_stall_le p (N / 2) N
      _ = (((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N := by ring
  calc ∑ c ∈ Finset.range p, ∑ ms ∈ SeriesAssembly.stallIdx N,
        ((transStallCountP p c ms N : ℕ) : ℚ)
      ≤ ∑ _c ∈ Finset.range p, ((((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N) :=
        Finset.sum_le_sum fun c _ => hper c
    _ = (p : ℚ) * ((((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## §E. The top covering, the box bound, and THE ENVELOPE -/

/-- The combined leaf menu is W6's (prime-free; the bridge for `mem_allLeaves_self`). -/
theorem allLeavesP_eq (K : ℕ) : allLeavesP K = SeriesAssembly.allLeaves K := rfl

/-- **The top covering at general `p`**: every pair in the box is order-0 decided,
chain-decided (main or splitU family) at ONE of the `p` residue points, or stalled —
`box_coveringP` composed with `cluster_coveringP` (blueprint §2-W6q-b's decision tree). -/
theorem top_coveringP (N : ℕ) (hN : 0 < N) (a : pairBoxP p N) :
    (Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
      ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
        TransFiber p i.1 i.2.1 i.2.2 N a)
    ∨ (∃ i ∈ (Finset.range p) ×ˢ SeriesAssembly.stallIdx N,
        TransStallP p i.1 i.2 N a) := by
  rcases box_coveringP p N hN a with h | h | ⟨c, hc, hCl⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · rcases cluster_coveringP p N N le_rfl (transMapP p c N a) hCl with
      ⟨ms, leaf, hms, hOK, hth, hcp⟩ | ⟨ms, m, hms, hm, hth, hcp⟩ | ⟨ms, hms, hbud, hsp⟩
    · -- main-chain family
      have hmem1 : ms ∈ msMenu N N := by
        rw [mem_msMenu]
        have hlen := SeriesAssembly.length_le_sum hms
        have hneed := one_le_leafNeed leaf
        refine ⟨by omega, fun m hm => ⟨hms m hm, ?_⟩⟩
        have := SeriesAssembly.mem_le_sum hm
        omega
      have hmem2 : leaf ∈ allLeavesP N := by
        rw [allLeavesP_eq]
        exact SeriesAssembly.mem_allLeaves_self hOK
          (by have := one_le_leafNeed leaf; omega)
      exact Or.inl (Or.inr (Or.inr ⟨(c, ms, Sum.inl leaf),
        Finset.mem_product.mpr ⟨hc,
          Finset.mem_product.mpr ⟨hmem1, Finset.inl_mem_disjSum.mpr hmem2⟩⟩, hcp⟩))
    · -- splitU family
      have hmem1 : ms ∈ msMenu N N := by
        rw [mem_msMenu]
        have hlen := SeriesAssembly.length_le_sum hms
        have hneedU : 1 ≤ leafNeedU m := one_le_leafNeedU m
        refine ⟨by omega, fun x hx => ⟨hms x hx, ?_⟩⟩
        have := SeriesAssembly.mem_le_sum hx
        omega
      have hmem2 : m ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Icc]
        simp only [leafNeedU] at hth
        omega
      exact Or.inl (Or.inr (Or.inr ⟨(c, ms, Sum.inr m),
        Finset.mem_product.mpr ⟨hc,
          Finset.mem_product.mpr ⟨hmem1, Finset.inr_mem_disjSum.mpr hmem2⟩⟩, hcp⟩))
    · -- stall
      have hmem1 : ms ∈ SeriesAssembly.stallIdx N := by
        rw [SeriesAssembly.stallIdx, Finset.mem_filter, mem_msMenu]
        by_cases hnil : ms = []
        · subst hnil
          exact ⟨⟨by simp, by simp⟩, Or.inl rfl⟩
        · have hb := hbud hnil
          have hlen := SeriesAssembly.length_le_sum hms
          refine ⟨⟨by omega, fun m hm => ⟨hms m hm, ?_⟩⟩, Or.inr hb⟩
          have := SeriesAssembly.mem_le_sum hm
          omega
      exact Or.inr ⟨(c, ms), Finset.mem_product.mpr ⟨hc, hmem1⟩, hsp⟩

/-- The σ-sum of the order-0 counts is the two cell cards. -/
theorem ord0Total_eq (N : ℕ) :
    ∑ σ ∈ typeMenuP, ord0Count p σ N
      = ((Nat.card {a : pairBoxP p N // Ord0SplitCell p N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℕ) : ℚ) := by
  rw [sum_typeMenuP]
  unfold ord0Count
  rw [if_neg ram_ne_split, if_neg ram_ne_inert, if_neg inert_ne_split,
    if_pos rfl, if_pos rfl]
  ring

theorem card_pairBoxP (N : ℕ) :
    (Fintype.card (pairBoxP p N) : ℚ) = (p : ℚ) ^ (2 * N) := by
  rw [Fintype.card_prod, ZMod.card]
  push_cast
  rw [← pow_add]
  congr 1
  omega

/-- **The covering count bound**: box ≤ decided + stalls (the W6 §J assembly at general
`p`, with the FOUR chain families through the `TransFiber` sum index). -/
theorem box_le_decidedP_add_stall (N : ℕ) (hN : 0 < N) :
    (p : ℚ) ^ (2 * N) ≤ (∑ σ ∈ typeMenuP, decidedCountP p σ N) + stallTotalP p N := by
  classical
  have hcardsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (pairBoxP p N)))
    (p := fun a : pairBoxP p N => Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
      ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
        TransFiber p i.1 i.2.1 i.2.2 N a)
  have hDecBound : (Finset.univ.filter (fun a : pairBoxP p N =>
      Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
      ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
        TransFiber p i.1 i.2.1 i.2.2 N a)).card
      ≤ Nat.card {a : pairBoxP p N // Ord0SplitCell p N a}
        + Nat.card {a : pairBoxP p N // Ord0InertCell p N a}
        + ∑ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
            transFiberCount p i.1 i.2.1 i.2.2 N := by
    have hsub : Finset.univ.filter (fun a : pairBoxP p N =>
        Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
        ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
          TransFiber p i.1 i.2.1 i.2.2 N a)
        ⊆ (Finset.univ.filter (fun a : pairBoxP p N => Ord0SplitCell p N a))
          ∪ (Finset.univ.filter (fun a : pairBoxP p N => Ord0InertCell p N a))
          ∪ ((Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum
              (Finset.Icc 1 N))).biUnion (fun i =>
              Finset.univ.filter (fun a : pairBoxP p N =>
                TransFiber p i.1 i.2.1 i.2.2 N a)) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases ha.2 with h | h | ⟨i, hi, h⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩⟩)
    calc (Finset.univ.filter _).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun a : pairBoxP p N => Ord0SplitCell p N a))
            ∪ (Finset.univ.filter (fun a : pairBoxP p N => Ord0InertCell p N a))).card
          + (((Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum
              (Finset.Icc 1 N))).biUnion (fun i =>
              Finset.univ.filter (fun a : pairBoxP p N =>
                TransFiber p i.1 i.2.1 i.2.2 N a))).card :=
          Finset.card_union_le _ _
      _ ≤ ((Finset.univ.filter (fun a : pairBoxP p N => Ord0SplitCell p N a)).card
            + (Finset.univ.filter (fun a : pairBoxP p N => Ord0InertCell p N a)).card)
          + ∑ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum
              (Finset.Icc 1 N)),
              (Finset.univ.filter (fun a : pairBoxP p N =>
                TransFiber p i.1 i.2.1 i.2.2 N a)).card :=
          Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
      _ = _ := by
          rw [SeriesAssembly.filter_card_eq_nat_card, SeriesAssembly.filter_card_eq_nat_card]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [SeriesAssembly.filter_card_eq_nat_card]
          rfl
  have hStBound : (Finset.univ.filter (fun a : pairBoxP p N =>
      ¬(Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
      ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
        TransFiber p i.1 i.2.1 i.2.2 N a))).card
      ≤ ∑ i ∈ (Finset.range p) ×ˢ SeriesAssembly.stallIdx N,
          transStallCountP p i.1 i.2 N := by
    have hsub : Finset.univ.filter (fun a : pairBoxP p N =>
        ¬(Ord0SplitCell p N a ∨ Ord0InertCell p N a ∨
        ∃ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)),
          TransFiber p i.1 i.2.1 i.2.2 N a))
        ⊆ ((Finset.range p) ×ˢ SeriesAssembly.stallIdx N).biUnion (fun i =>
            Finset.univ.filter (fun a : pairBoxP p N => TransStallP p i.1 i.2 N a)) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases top_coveringP p N hN a with h | ⟨i, hi, hst⟩
      · exact absurd h ha.2
      · exact Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hst⟩⟩
    calc (Finset.univ.filter _).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ (Finset.range p) ×ˢ SeriesAssembly.stallIdx N,
            (Finset.univ.filter (fun a : pairBoxP p N => TransStallP p i.1 i.2 N a)).card :=
          Finset.card_biUnion_le
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [SeriesAssembly.filter_card_eq_nat_card]
          rfl
  -- assemble in ℕ, then cast
  have hNbound : Fintype.card (pairBoxP p N)
      ≤ (Nat.card {a : pairBoxP p N // Ord0SplitCell p N a}
          + Nat.card {a : pairBoxP p N // Ord0InertCell p N a}
          + ∑ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum
              (Finset.Icc 1 N)),
              transFiberCount p i.1 i.2.1 i.2.2 N)
        + ∑ i ∈ (Finset.range p) ×ˢ SeriesAssembly.stallIdx N,
            transStallCountP p i.1 i.2 N := by
    have hcu : (Finset.univ : Finset (pairBoxP p N)).card = Fintype.card (pairBoxP p N) :=
      Finset.card_univ
    omega
  have hQ : (p : ℚ) ^ (2 * N)
      ≤ ((Nat.card {a : pairBoxP p N // Ord0SplitCell p N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℕ) : ℚ)
        + (∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum
            (Finset.Icc 1 N), ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ))
        + (∑ c ∈ Finset.range p, ∑ ms ∈ SeriesAssembly.stallIdx N,
            ((transStallCountP p c ms N : ℕ) : ℚ)) := by
    rw [← card_pairBoxP p N]
    have hc1 : (∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum
        (Finset.Icc 1 N), ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ))
        = ((∑ i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum
            (Finset.Icc 1 N)), transFiberCount p i.1 i.2.1 i.2.2 N : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_product]
    have hc2 : (∑ c ∈ Finset.range p, ∑ ms ∈ SeriesAssembly.stallIdx N,
        ((transStallCountP p c ms N : ℕ) : ℚ))
        = ((∑ i ∈ (Finset.range p) ×ˢ SeriesAssembly.stallIdx N,
            transStallCountP p i.1 i.2 N : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_product]
    rw [hc1, hc2]
    exact_mod_cast hNbound
  have hfinal : (∑ σ ∈ typeMenuP, decidedCountP p σ N) + stallTotalP p N
      = ((Nat.card {a : pairBoxP p N // Ord0SplitCell p N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℕ) : ℚ)
        + (∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum
            (Finset.Icc 1 N), ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ))
        + (∑ c ∈ Finset.range p, ∑ ms ∈ SeriesAssembly.stallIdx N,
            ((transStallCountP p c ms N : ℕ) : ℚ)) := by
    have hd : ∑ σ ∈ typeMenuP, decidedCountP p σ N
        = (∑ σ ∈ typeMenuP, ord0Count p σ N) + ∑ σ ∈ typeMenuP, chainCountP p σ N := by
      unfold decidedCountP
      rw [Finset.sum_add_distrib]
    rw [hd, chainTotalP_eq, ord0Total_eq]
    unfold stallTotalP
    ring
  rw [hfinal]
  exact hQ

theorem undecidedP_le_stall (N : ℕ) (hN : 0 < N) :
    undecidedCountP p N ≤ stallTotalP p N := by
  unfold undecidedCountP
  linarith [box_le_decidedP_add_stall p N hN]

/-- The envelope as a named bound: `(⌊N/2⌋+1) · p^{−(N−1)}` — the SAME constant shape as
W6 (`C = 1`), now at every prime. -/
noncomputable def envBoundP (N : ℕ) : ℚ :=
  (((N / 2 : ℕ) : ℚ) + 1) * (((p : ℚ) ^ (N - 1))⁻¹)

theorem envBoundP_nonneg (N : ℕ) : 0 ≤ envBoundP p N := by
  unfold envBoundP
  positivity

theorem envBoundP_mul_box (N : ℕ) (hN : 1 ≤ N) :
    envBoundP p N * (p : ℚ) ^ (2 * N)
      = (p : ℚ) * ((((N / 2 : ℕ) : ℚ) + 1) * (p : ℚ) ^ N) := by
  unfold envBoundP
  have hsplit : (p : ℚ) ^ (2 * N) = (p : ℚ) ^ (N - 1) * (p : ℚ) ^ (N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have hne : (p : ℚ) ^ (N - 1) ≠ 0 := pQ_pow_ne p _
  field_simp
  ring

/-- **THE UNDECIDED ENVELOPE AT GENERAL `p`** (blueprint §1.3 target; all `N ≥ 1`):
`undecidedCountP p N / p^{2N} ≤ (⌊N/2⌋ + 1) · p^{−(N−1)}`. -/
theorem undecided_envelopeP (N : ℕ) (hN : 1 ≤ N) :
    undecidedCountP p N / (p : ℚ) ^ (2 * N)
      ≤ (((N / 2 : ℕ) : ℚ) + 1) * (((p : ℚ) ^ (N - 1))⁻¹) := by
  rw [div_le_iff₀ (pQ_pow_pos p _)]
  have h1 := undecidedP_le_stall p N (by omega)
  have h2 := stallTotalP_le p N (by omega)
  have harr := envBoundP_mul_box p N hN
  unfold envBoundP at harr
  linarith

theorem envBoundP_le {N : ℕ} (hN : 4 ≤ N) : envBoundP p N ≤ 2 / (N : ℚ) := by
  unfold envBoundP
  have h1 : (((N / 2 : ℕ) : ℚ) + 1) ≤ (N : ℚ) := by
    have h0 : (N / 2 : ℕ) + 1 ≤ N := by omega
    exact_mod_cast h0
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  have hcast : ((N : ℚ)) * N ≤ (2 : ℚ) * (p : ℚ) ^ (N - 1) := by
    have hn := SeriesAssembly.nat_sq_le_two_pow hN
    have h5 : ((N : ℚ)) ^ 2 ≤ (2 : ℚ) ^ N := by exact_mod_cast hn
    have h2P : (2 : ℚ) ^ (N - 1) ≤ (p : ℚ) ^ (N - 1) :=
      pow_le_pow_left₀ (by norm_num) (pQ_two p) _
    have hp2 : (2 : ℚ) ^ N = 2 * (2 : ℚ) ^ (N - 1) := by
      conv_lhs => rw [show N = N - 1 + 1 by omega]
      rw [pow_succ]
      ring
    nlinarith
  calc (((N / 2 : ℕ) : ℚ) + 1) * (((p : ℚ) ^ (N - 1))⁻¹)
      ≤ (N : ℚ) * (((p : ℚ) ^ (N - 1))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 2 / N := by
        rw [mul_inv_le_iff₀ (pQ_pow_pos p _), div_mul_eq_mul_div, le_div_iff₀ hNQ]
        linarith

theorem tendsto_envBoundP_zero :
    Tendsto (fun N => envBoundP p N) atTop (nhds 0) := by
  have h2 : Tendsto (fun N : ℕ => 2 / (N : ℚ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards with N using envBoundP_nonneg p N
  · filter_upwards [eventually_ge_atTop 4] with N hN using envBoundP_le p hN

/-- **`hExhaustP` — the exhaustion discharged at EVERY prime** (blueprint §0/§2-W6q-c;
pure counting, no axiom): the general-`p` full model's undecided density tends to `0`. -/
theorem hExhaustP :
    Tendsto (fun N => undecidedCountP p N / (p : ℚ) ^ (2 * N)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_envBoundP_zero p) ?_ ?_
  · filter_upwards with N
    exact div_nonneg (undecidedP_nonneg p N) (le_of_lt (pQ_pow_pos p _))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact undecided_envelopeP p N hN

/-! ## §F. Per-stratum normalized staircases and model monotonicity -/

/-- The normalized main-chain stratum count is a monotone staircase `0, …, 0, c, c, …`. -/
theorem normTransP_mono (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) :
    Monotone (fun N => ((transChainCountP p c ms leaf N : ℕ) : ℚ) / (p : ℚ) ^ (2 * N)) := by
  intro N₁ N₂ h12
  dsimp only
  rcases Nat.lt_or_ge N₁ (2 * ms.sum + leafNeed leaf) with hlt | hge
  · rw [transChainCountP_zero_of_lt p c ms leaf hlt, Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pQ_pow_pos p _))
  · rw [transChainCountP_cast p c ms leaf hms hOK hge,
      transChainCountP_cast p c ms leaf hms hOK (le_trans hge h12),
      mul_div_assoc, mul_div_assoc, div_self (pQ_pow_ne p _), div_self (pQ_pow_ne p _)]

/-- The normalized splitU stratum count is a monotone staircase. -/
theorem normTransU_mono (c : ℕ) (ms : List ℕ) (m : ℕ)
    (hms : ∀ x ∈ ms, 1 ≤ x) (hm : 1 ≤ m) :
    Monotone (fun N => ((transChainCountU p c ms m N : ℕ) : ℚ) / (p : ℚ) ^ (2 * N)) := by
  intro N₁ N₂ h12
  dsimp only
  rcases Nat.lt_or_ge N₁ (2 * ms.sum + leafNeedU m) with hlt | hge
  · rw [transChainCountU_zero_of_lt p c ms m hlt, Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pQ_pow_pos p _))
  · rw [transChainCountU_cast p c ms m hms hm hge,
      transChainCountU_cast p c ms m hms hm (le_trans hge h12),
      mul_div_assoc, mul_div_assoc, div_self (pQ_pow_ne p _), div_self (pQ_pow_ne p _)]

/-- The normalized order-0 count is `0, w, w, …` (constant from `N = 1`). -/
theorem ord0_div_le (σ : FactorizationType) {N₁ N₂ : ℕ} (h12 : N₁ ≤ N₂) :
    ord0Count p σ N₁ / (p : ℚ) ^ (2 * N₁) ≤ ord0Count p σ N₂ / (p : ℚ) ^ (2 * N₂) := by
  rcases Nat.eq_zero_or_pos N₁ with rfl | hN₁
  · rw [ord0Count_zero, zero_div]
    exact div_nonneg (ord0Count_nonneg p σ N₂) (le_of_lt (pQ_pow_pos p _))
  · have hN₂ : 0 < N₂ := by omega
    rw [ord0Count_eq p σ hN₁, ord0Count_eq p σ hN₂,
      mul_div_assoc, mul_div_assoc, div_self (pQ_pow_ne p _), div_self (pQ_pow_ne p _)]

/-- The splitU index rectangle grows with the level. -/
theorem uRect_mono {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    msMenu N₁ N₁ ×ˢ Finset.Icc 1 N₁ ⊆ msMenu N₂ N₂ ×ˢ Finset.Icc 1 N₂ := by
  intro x hx
  rw [Finset.mem_product] at hx ⊢
  constructor
  · obtain ⟨hlen, hall⟩ := (mem_msMenu N₁ N₁ x.1).mp hx.1
    refine (mem_msMenu N₂ N₂ x.1).mpr ⟨by omega, fun m hm => ⟨(hall m hm).1, ?_⟩⟩
    have := (hall m hm).2
    omega
  · exact Finset.Icc_subset_Icc le_rfl h hx.2

/-- **Full monotonicity in the level window** (the model's `decided_mono` field): order-0
staircase + per-stratum staircases + growing index rectangles, over all four families. -/
theorem decidedP_mono (σ : FactorizationType) :
    Monotone (fun N => decidedCountP p σ N / (p : ℚ) ^ (2 * N)) := by
  intro N₁ N₂ h12
  dsimp only
  unfold decidedCountP chainCountP
  rw [add_div, add_div, add_div, add_div]
  refine add_le_add (ord0_div_le p σ h12) (add_le_add ?_ ?_)
  · unfold chainCountMain
    rw [Finset.sum_div, Finset.sum_div]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [Finset.sum_div, Finset.sum_div]
    calc ∑ x ∈ msMenu N₁ N₁ ×ˢ chainLeaves N₁ σ,
          ((transChainCountP p c x.1 x.2 N₁ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₁)
        ≤ ∑ x ∈ msMenu N₁ N₁ ×ˢ chainLeaves N₁ σ,
          ((transChainCountP p c x.1 x.2 N₂ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₂) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.mem_product] at hx
          exact normTransP_mono p c x.1 x.2
            (fun m hm => (((mem_msMenu N₁ N₁ x.1).mp hx.1).2 m hm).1)
            (of_mem_chainLeaves hx.2).1 h12
      _ ≤ ∑ x ∈ msMenu N₂ N₂ ×ˢ chainLeaves N₂ σ,
          ((transChainCountP p c x.1 x.2 N₂ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₂) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (SeriesAssembly.rect_mono h12 σ) ?_
          intro x _ _
          exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pQ_pow_pos p _))
  · by_cases hσ : σ = splitType2
    · rw [if_pos hσ, if_pos hσ]
      unfold chainCountUTot
      rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_le_sum fun c _ => ?_
      rw [Finset.sum_div, Finset.sum_div]
      calc ∑ x ∈ msMenu N₁ N₁ ×ˢ Finset.Icc 1 N₁,
            ((transChainCountU p c x.1 x.2 N₁ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₁)
          ≤ ∑ x ∈ msMenu N₁ N₁ ×ˢ Finset.Icc 1 N₁,
            ((transChainCountU p c x.1 x.2 N₂ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₂) := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [Finset.mem_product] at hx
            exact normTransU_mono p c x.1 x.2
              (fun m hm => (((mem_msMenu N₁ N₁ x.1).mp hx.1).2 m hm).1)
              (Finset.mem_Icc.mp hx.2).1 h12
        _ ≤ ∑ x ∈ msMenu N₂ N₂ ×ˢ Finset.Icc 1 N₂,
            ((transChainCountU p c x.1 x.2 N₂ : ℕ) : ℚ) / (p : ℚ) ^ (2 * N₂) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (uRect_mono h12) ?_
            intro x _ _
            exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pQ_pow_pos p _))
    · rw [if_neg hσ, if_neg hσ, zero_div, zero_div]

/-- Counts vanish identically off the degree-2 menu. -/
theorem decidedCountP_off {σ : FactorizationType} (hσ : σ ∉ typeMenuP) (N : ℕ) :
    decidedCountP p σ N = 0 := by
  have hmem : σ ≠ ramType2 ∧ σ ≠ inertType2 ∧ σ ≠ splitType2 := by
    unfold typeMenuP at hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rw [not_or, not_or] at hσ
    exact hσ
  unfold decidedCountP ord0Count chainCountP chainCountMain
  rw [if_neg hmem.2.2, if_neg hmem.2.1, if_neg hmem.2.2,
    SeriesAssembly.chainLeaves_off hmem.1 hmem.2.1 hmem.2.2, Finset.product_empty]
  simp

/-! ## §G. The per-type (U) bound and the squeeze (blueprint §1.4) -/

/-- The main-chain families' aggregate bound: all `p` residue points × the folded
fixpoint sum × σ's leaf sum. -/
theorem chainCountMain_leP (σ : FactorizationType) (N : ℕ) :
    chainCountMain p σ N
      ≤ (p : ℚ) * (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf p) * (p : ℚ) ^ (2 * N) := by
  unfold chainCountMain
  have hper : ∀ c : ℕ,
      ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)
        ≤ (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
            * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf p) * (p : ℚ) ^ (2 * N) := by
    intro c
    calc ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)
        ≤ ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, chainC x.1 x.2 p * (p : ℚ) ^ (2 * N) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.mem_product] at hx
          exact transChainCountP_le_coeff p c
            (fun m hm => (((mem_msMenu N N x.1).mp hx.1).2 m hm).1)
            (of_mem_chainLeaves hx.2).1 N
      _ = (∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, chainC x.1 x.2 p) * (p : ℚ) ^ (2 * N) := by
          rw [Finset.sum_mul]
      _ = (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
            * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf p) * (p : ℚ) ^ (2 * N) := by
          rw [sum_rect_chainCP]
  calc ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ,
        ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)
      ≤ ∑ _c ∈ Finset.range p, (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf p) * (p : ℚ) ^ (2 * N) :=
        Finset.sum_le_sum fun c _ => hper c
    _ = (p : ℚ) * (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf p) * (p : ℚ) ^ (2 * N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- The splitU family's aggregate bound. -/
theorem chainCountUTot_leP (N : ℕ) :
    chainCountUTot p N
      ≤ (p : ℚ) * (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ m ∈ Finset.Icc 1 N, uLeafC m p) * (p : ℚ) ^ (2 * N) := by
  unfold chainCountUTot
  have hper : ∀ c : ℕ,
      ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N, ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ)
        ≤ (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
            * ∑ m ∈ Finset.Icc 1 N, uLeafC m p) * (p : ℚ) ^ (2 * N) := by
    intro c
    calc ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N, ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ)
        ≤ ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N, chainCU x.1 x.2 p * (p : ℚ) ^ (2 * N) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.mem_product] at hx
          exact transChainCountU_le_coeff p c
            (fun m hm => (((mem_msMenu N N x.1).mp hx.1).2 m hm).1)
            (Finset.mem_Icc.mp hx.2).1 N
      _ = (∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N, chainCU x.1 x.2 p) * (p : ℚ) ^ (2 * N) := by
          rw [Finset.sum_mul]
      _ = (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
            * ∑ m ∈ Finset.Icc 1 N, uLeafC m p) * (p : ℚ) ^ (2 * N) := by
          rw [sum_rect_chainCU]
  calc ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N,
        ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ)
      ≤ ∑ _c ∈ Finset.range p, (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ m ∈ Finset.Icc 1 N, uLeafC m p) * (p : ℚ) ^ (2 * N) :=
        Finset.sum_le_sum fun c _ => hper c
    _ = (p : ℚ) * (msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ m ∈ Finset.Icc 1 N, uLeafC m p) * (p : ℚ) ^ (2 * N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ### The three closure identities (the blueprint §1.2 `(q−1)`-cancellation ledger:
each fixpoint × leaf-sum product closes EXACTLY at the fixed value) -/

/-- Ram closure: `q · [1/(1−r(q))] · [(q−1)/(q³−1)] = 1/(q+1) = R_ram`. -/
theorem closure_ram :
    (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
        * (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1)))
      = uniformValueFn ramType2 p := by
  unfold uniformValueFn
  rw [if_pos rfl]
  have h0 : ((p : ℚ)) ≠ 0 := pQ_ne p
  have h1 : ((p : ℚ) ^ 2 + p) ≠ 0 := ne_of_gt (pQ_sq_add_pos p)
  have h2 : ((p : ℚ) ^ 3 - 1) ≠ 0 := ne_of_gt (pQ_cube_sub_one_pos p)
  have h3 : ((p : ℚ) + 1) ≠ 0 := ne_of_gt (pQ_add_one_pos p)
  field_simp
  ring

/-- Inert closure: `(q−1)/(2q) + q·[1/(1−r)]·[inert leaf sum] = q/(2(q+1)) = R_inert`. -/
theorem closure_inert :
    ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
      + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
          * (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
      = uniformValueFn inertType2 p := by
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_inert), if_pos rfl]
  have h0 : ((p : ℚ)) ≠ 0 := pQ_ne p
  have h1 : ((p : ℚ) ^ 2 + p) ≠ 0 := ne_of_gt (pQ_sq_add_pos p)
  have h2 : ((p : ℚ) ^ 3 - 1) ≠ 0 := ne_of_gt (pQ_cube_sub_one_pos p)
  have h3 : ((p : ℚ) + 1) ≠ 0 := ne_of_gt (pQ_add_one_pos p)
  field_simp
  ring

/-- Split closure: `(q−1)/(2q) + q·[1/(1−r)]·[two-sided + splitU leaf sums]
= q/(2(q+1)) = R_split` — the `(q−2)/2 + 1 = q/2` recombination (blueprint §1.2
`β_split`). -/
theorem closure_split :
    ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
      + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
          * (((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
      + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
          * (((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
              * (1 / ((p : ℚ) ^ 3 - 1))))
      = uniformValueFn splitType2 p := by
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
  have h0 : ((p : ℚ)) ≠ 0 := pQ_ne p
  have h1 : ((p : ℚ) ^ 2 + p) ≠ 0 := ne_of_gt (pQ_sq_add_pos p)
  have h2 : ((p : ℚ) ^ 3 - 1) ≠ 0 := ne_of_gt (pQ_cube_sub_one_pos p)
  have h3 : ((p : ℚ) + 1) ≠ 0 := ne_of_gt (pQ_add_one_pos p)
  field_simp
  ring

/-- **(U) The per-type value bound**: every level's decided count is at most
`R_σ(p) · box` — the ledger closes EXACTLY at the fixed values (blueprint §1.2/§1.4). -/
theorem decidedP_le_valueP (σ : FactorizationType) (N : ℕ) :
    decidedCountP p σ N ≤ uniformValueFn σ p * (p : ℚ) ^ (2 * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [decidedCountP_zero]
    exact mul_nonneg (uniformValueFn_nonneg σ p) (le_of_lt (pQ_pow_pos p _))
  · have hbox := pQ_pow_pos p (2 * N)
    have hW := msWP_fix_le p N N
    have hW0 : 0 ≤ msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹) :=
      msWP_nonneg N N (pQ_sub_one_nonneg p) (by positivity)
    have hB0 : (0 : ℚ) ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p) :=
      le_of_lt (div_pos (pQ_sq_add_add_pos p) (pQ_sq_add_pos p))
    by_cases h1 : σ = ramType2
    · subst h1
      have hord : ord0Count p ramType2 N = 0 := by
        unfold ord0Count
        rw [if_neg ram_ne_split, if_neg ram_ne_inert]
      have hchainU : (if ramType2 = splitType2 then chainCountUTot p N else 0) = 0 := by
        rw [if_neg ram_ne_split]
      have hprod : msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
          * ∑ leaf ∈ chainLeaves N ramType2, chainC [] leaf p
          ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
            * (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1)) :=
        mul_le_mul hW (sum_leaf_ramP_le p N) (sum_leaf_nonnegP p N ramType2) hB0
      have hmain : chainCountMain p ramType2 N
          ≤ (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
              * (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1))) * (p : ℚ) ^ (2 * N) := by
        refine le_trans (chainCountMain_leP p ramType2 N) ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (le_of_lt (pQ_pos p))) (le_of_lt hbox)
      unfold decidedCountP chainCountP
      rw [hord, hchainU, zero_add, add_zero]
      calc chainCountMain p ramType2 N
          ≤ (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
              * (((p : ℚ) - 1) / ((p : ℚ) ^ 3 - 1))) * (p : ℚ) ^ (2 * N) := hmain
        _ = uniformValueFn ramType2 p * (p : ℚ) ^ (2 * N) := by rw [closure_ram p]
    · by_cases h2 : σ = inertType2
      · subst h2
        have hord : ord0Count p inertType2 N
            = ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N) := by
          rw [ord0Count_eq p inertType2 hN]
          unfold ord0Q
          rw [if_neg inert_ne_split, if_pos rfl]
        have hchainU : (if inertType2 = splitType2 then chainCountUTot p N else 0) = 0 := by
          rw [if_neg inert_ne_split]
        have hprod : msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
            * ∑ leaf ∈ chainLeaves N inertType2, chainC [] leaf p
            ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
              * (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))) :=
          mul_le_mul hW (sum_leaf_inertP_le p N) (sum_leaf_nonnegP p N inertType2) hB0
        have hmain : chainCountMain p inertType2 N
            ≤ (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                * (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
              * (p : ℚ) ^ (2 * N) := by
          refine le_trans (chainCountMain_leP p inertType2 N) ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (le_of_lt (pQ_pos p))) (le_of_lt hbox)
        unfold decidedCountP chainCountP
        rw [hchainU, add_zero, hord]
        calc ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N)
              + chainCountMain p inertType2 N
            ≤ ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N)
              + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                  * (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
                * (p : ℚ) ^ (2 * N) := by linarith
          _ = (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
                + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                    * (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
                        * (1 / ((p : ℚ) ^ 3 - 1)))))
              * (p : ℚ) ^ (2 * N) := by ring
          _ = uniformValueFn inertType2 p * (p : ℚ) ^ (2 * N) := by rw [closure_inert p]
      · by_cases h3 : σ = splitType2
        · subst h3
          have hord : ord0Count p splitType2 N
              = ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N) := by
            rw [ord0Count_eq p splitType2 hN]
            unfold ord0Q
            rw [if_pos rfl]
          have hprodM : msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
              * ∑ leaf ∈ chainLeaves N splitType2, chainC [] leaf p
              ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                * (((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))) :=
            mul_le_mul hW (sum_leaf_splitP_le p N) (sum_leaf_nonnegP p N splitType2) hB0
          have hprodU : msWP N N ((p : ℚ) - 1) (((p : ℚ) ^ 3)⁻¹)
              * ∑ m ∈ Finset.Icc 1 N, uLeafC m p
              ≤ ((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                * (((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
                    * (1 / ((p : ℚ) ^ 3 - 1))) :=
            mul_le_mul hW (sum_uLeaf_le p N) (sum_uLeaf_nonneg p N) hB0
          have hmain : chainCountMain p splitType2 N
              ≤ (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                  * (((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
                * (p : ℚ) ^ (2 * N) := by
            refine le_trans (chainCountMain_leP p splitType2 N) ?_
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hprodM (le_of_lt (pQ_pos p))) (le_of_lt hbox)
          have hU : chainCountUTot p N
              ≤ (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                  * (((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
                      * (1 / ((p : ℚ) ^ 3 - 1))))
                * (p : ℚ) ^ (2 * N) := by
            refine le_trans (chainCountUTot_leP p N) ?_
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hprodU (le_of_lt (pQ_pos p))) (le_of_lt hbox)
          unfold decidedCountP chainCountP
          rw [if_pos rfl, hord]
          calc ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N)
                + (chainCountMain p splitType2 N + chainCountUTot p N)
              ≤ ((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹ * (p : ℚ) ^ (2 * N)
                + ((p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                    * (((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
                  * (p : ℚ) ^ (2 * N)
                  + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                      * (((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
                          * (1 / ((p : ℚ) ^ 3 - 1))))
                    * (p : ℚ) ^ (2 * N)) := by linarith
            _ = (((p : ℚ) ^ 2 - p) / 2 * ((p : ℚ) ^ 2)⁻¹
                  + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                      * (((p : ℚ) - 1) * ((p : ℚ) ^ 2)⁻¹ * (1 / ((p : ℚ) ^ 3 - 1))))
                  + (p : ℚ) * (((p : ℚ) ^ 2 + p + 1) / ((p : ℚ) ^ 2 + p)
                      * (((p : ℚ) - 1) * ((p : ℚ) - 2) / 2 * ((p : ℚ) ^ 2)⁻¹
                          * (1 / ((p : ℚ) ^ 3 - 1)))))
                * (p : ℚ) ^ (2 * N) := by ring
            _ = uniformValueFn splitType2 p * (p : ℚ) ^ (2 * N) := by rw [closure_split p]
        · rw [decidedCountP_off p (by
            unfold typeMenuP
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rw [not_or, not_or]
            exact ⟨h1, h2, h3⟩) N]
          exact mul_nonneg (uniformValueFn_nonneg σ p) (le_of_lt hbox)

/-- The (U) bound in normalized form. -/
theorem decidedP_upper (σ : FactorizationType) (N : ℕ) :
    decidedCountP p σ N / (p : ℚ) ^ (2 * N) ≤ uniformValueFn σ p := by
  rw [div_le_iff₀ (pQ_pow_pos p _)]
  exact decidedP_le_valueP p σ N

/-- The fixed values exhaust the box: `R_ram + R_inert + R_split = 1` (blueprint §1.2
checksum — the depth-0 `(q²+q+1)`-ledger total). -/
theorem uniformValue_checksum :
    uniformValueFn ramType2 p + uniformValueFn inertType2 p
      + uniformValueFn splitType2 p = 1 := by
  unfold uniformValueFn
  rw [if_pos rfl, if_neg (Ne.symm ram_ne_inert), if_pos rfl,
    if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
  have h3 : ((p : ℚ) + 1) ≠ 0 := ne_of_gt (pQ_add_one_pos p)
  field_simp
  ring

/-- The squeeze's lower half: box partition + (U) for the other two types + the envelope. -/
theorem decidedP_lower (σ : FactorizationType) (hσ : σ ∈ typeMenuP) (N : ℕ) (hN : 1 ≤ N) :
    uniformValueFn σ p - envBoundP p N ≤ decidedCountP p σ N / (p : ℚ) ^ (2 * N) := by
  have hbox : (0 : ℚ) < (p : ℚ) ^ (2 * N) := pQ_pow_pos p _
  rw [le_div_iff₀ hbox]
  have hb := box_le_decidedP_add_stall p N (by omega)
  have hstall_env : stallTotalP p N ≤ envBoundP p N * (p : ℚ) ^ (2 * N) := by
    rw [envBoundP_mul_box p N hN]
    exact stallTotalP_le p N (by omega)
  have hsum := sum_typeMenuP (fun σ' => decidedCountP p σ' N)
  rw [hsum] at hb
  have hle1 := decidedP_le_valueP p ramType2 N
  have hle2 := decidedP_le_valueP p inertType2 N
  have hle3 := decidedP_le_valueP p splitType2 N
  have hchk_box : uniformValueFn ramType2 p * (p : ℚ) ^ (2 * N)
      + uniformValueFn inertType2 p * (p : ℚ) ^ (2 * N)
      + uniformValueFn splitType2 p * (p : ℚ) ^ (2 * N) = (p : ℚ) ^ (2 * N) := by
    have hchk := uniformValue_checksum p
    linear_combination ((p : ℚ) ^ (2 * N)) * hchk
  unfold typeMenuP at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl
  · nlinarith [hb, hstall_env, hle2, hle3, hchk_box]
  · nlinarith [hb, hstall_env, hle1, hle3, hchk_box]
  · nlinarith [hb, hstall_env, hle1, hle2, hchk_box]

/-- **THE SQUEEZE (blueprint §1.4)**: the general-`p` model's per-type normalized decided
count tends to the FIXED value `R_σ(p)` — two-sided, (U) above, box partition + envelope
below. -/
theorem uniformDecided_tendsto (σ : FactorizationType) (hσ : σ ∈ typeMenuP) :
    Tendsto (fun N => decidedCountP p σ N / (p : ℚ) ^ (2 * N)) atTop
      (nhds (uniformValueFn σ p)) := by
  have hlow : Tendsto (fun N : ℕ => uniformValueFn σ p - envBoundP p N) atTop
      (nhds (uniformValueFn σ p)) := by
    simpa using (tendsto_const_nhds (x := uniformValueFn σ p)).sub (tendsto_envBoundP_zero p)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using decidedP_lower p σ hσ N hN
  · filter_upwards with N using decidedP_upper p σ N

/-! ## §H. THE MODEL `M7 p` and the V2 spine instance `uniformD p` -/

/-- **`M7 p` — the general-`p` FULL `n = 2` counting model** (the W6 `realMW6`
construction at arbitrary `p`, over the W6q-b counts: order-0 residual-shape cells + all
`p` residue points × all depths × the FOUR leaf families). -/
noncomputable def M7 : CountingModel p 2 where
  hq := hp.out.two_le
  decidedCount := decidedCountP p
  undecidedCount := undecidedCountP p
  decidedCount_nonneg := decidedCountP_nonneg p
  undecidedCount_nonneg := undecidedP_nonneg p
  typeMenu := typeMenuP
  typeMenu_degree := by
    intro σ hσ
    unfold typeMenuP at hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  decidedCount_off_menu := fun σ N hσ => decidedCountP_off p hσ N
  box_partition := by
    intro N
    unfold undecidedCountP
    ring
  decided_mono := decidedP_mono p
  densityVal := fun σ => uniformValueFn σ p
  decided_tendsto := by
    intro σ
    by_cases hσ : σ ∈ typeMenuP
    · exact uniformDecided_tendsto p σ hσ
    · rw [uniformValueFn_off hσ]
      refine Tendsto.congr (fun N => ?_) tendsto_const_nhds
      rw [decidedCountP_off p hσ N, zero_div]
  upper_tail := by
    intro σ N K' hNK
    have hBK := pQ_pow_pos p (2 * K')
    have hBN := pQ_pow_pos p (2 * N)
    by_cases hσ : σ ∈ typeMenuP
    · have hstep : ∀ σ' ∈ typeMenuP,
          (0 : ℚ) ≤ decidedCountP p σ' K' / (p : ℚ) ^ (2 * K')
            - decidedCountP p σ' N / (p : ℚ) ^ (2 * N) := fun σ' _ =>
        sub_nonneg.mpr (decidedP_mono p σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          decidedCountP p σ' K' / (p : ℚ) ^ (2 * K')
          - decidedCountP p σ' N / (p : ℚ) ^ (2 * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      have htotK : (∑ σ' ∈ typeMenuP, decidedCountP p σ' K') / (p : ℚ) ^ (2 * K') ≤ 1 :=
        (div_le_one hBK).mpr (sum_decidedP_le_box p K')
      have hundec : undecidedCountP p N / (p : ℚ) ^ (2 * N)
          = 1 - (∑ σ' ∈ typeMenuP, decidedCountP p σ' N) / (p : ℚ) ^ (2 * N) := by
        unfold undecidedCountP
        rw [sub_div, div_self (ne_of_gt hBN)]
      linarith
    · rw [decidedCountP_off p hσ N, decidedCountP_off p hσ K',
        zero_div, zero_div, zero_add]
      exact div_nonneg (undecidedP_nonneg p N) (le_of_lt hBN)

/-- The degree-2 menu is W6's (prime-free — the marker bridge). -/
theorem typeMenuP_eq_typeMenu6 : typeMenuP = SeriesAssembly.typeMenu6 := rfl

/-- One PRIME-FREE marker shape per type (bookkeeping for the deliberately-weak
`MontesDataV2` spine, exactly W6's `shapesOf6` — reusing `SeriesAssembly.marker`; the
semantics are pinned by the count definitions and the squeeze theorems, per the interface
docstring's statement-fence note). -/
noncomputable def shapesOfU (σ : FactorizationType) : Finset ClusterShape :=
  if σ ∈ typeMenuP then {SeriesAssembly.marker σ} else ∅

theorem markerU_type {σ : FactorizationType} (hσ : σ ∈ typeMenuP) :
    leafType (decodeLeaf (SeriesAssembly.marker σ)) = σ :=
  SeriesAssembly.marker_type (typeMenuP_eq_typeMenu6 ▸ hσ)

/-- The per-shape stratum count over the general-`p` model (keyed through the marker's
decoded type, as W6's `stratumCount6`). -/
noncomputable def stratumCountU (T : ClusterShape) (N : ℕ) : ℚ :=
  decidedCountP p (leafType (decodeLeaf T)) N

/-- The abstract per-shape coefficient: the FIXED value family at the marker's type —
PRIME-FREE, like the polynomials it evaluates to. -/
noncomputable def CU (T : ClusterShape) (q' : ℕ) : ℚ :=
  uniformValueFn (leafType (decodeLeaf T)) q'

/-- **`uniformD p` — the abstract-coefficient V2 spine over the general-`p` model** (the
W6 `realDW6` shape verbatim: one bookkeeping marker per type). -/
noncomputable def uniformD : LeanUrat.MontesV2.MontesDataV2 p 2 (M7 p) where
  shapesOf := shapesOfU
  stratumCount := stratumCountU p
  partition := by
    intro σ N
    show decidedCountP p σ N = ∑ T ∈ shapesOfU σ, stratumCountU p T N
    unfold shapesOfU
    by_cases hσ : σ ∈ typeMenuP
    · rw [if_pos hσ, Finset.sum_singleton]
      unfold stratumCountU
      rw [markerU_type hσ]
    · rw [if_neg hσ, Finset.sum_empty]
      exact decidedCountP_off p hσ N
  C := CU
  C_isRational := fun T => uniformValueFn_isRational (leafType (decodeLeaf T))
  stratum_tendsto_C := by
    intro σ T hT
    unfold shapesOfU at hT
    by_cases hσ : σ ∈ typeMenuP
    · rw [if_pos hσ, Finset.mem_singleton] at hT
      subst hT
      show Tendsto
        (fun N => stratumCountU p (SeriesAssembly.marker σ) N / (p : ℚ) ^ (2 * N))
        atTop (nhds (CU (SeriesAssembly.marker σ) p))
      unfold stratumCountU CU
      rw [markerU_type hσ]
      exact uniformDecided_tendsto p σ hσ
    · rw [if_neg hσ] at hT
      exact absurd hT (Finset.notMem_empty T)

/-! ## §I. THE CAPSTONE -/

set_option linter.unusedVariables false in
/-- **`montes_uniform_n2` — THE ALL-PRIMES UNIFORMITY CAPSTONE (blueprint §0, the
prize).**

For EVERY prime `p` (the wild `p = 2` INCLUDED) and every degree-2 type σ, over the full
general-`p` counting model `M7 p` (order-0 cells + all `p` residue points × all depths ×
all FOUR leaf families — the complete `n = 2` stratum tree):

* (R) **uniform rationality with the FIXED `p`-free polynomials**: the density family
  `q' ↦ ∑_{T ∈ shapesOfU σ} CU T q'` equals `uniformNum σ / uniformDen σ` — `numR = 1,
  denR = X + 1` (ram), `numI = numS = X, denI = denS = 2X + 2` (inert/split), defined
  ONCE above, no prime anywhere in them — at every `q' > 1`, denominator nonvanishing;
* (V) **the value tie at `p`**: `(M7 p).countingDensity σ` — the genuine `N → ∞`
  decided limit — equals `numₛ(p)/denₛ(p)` (with `denₛ(p) ≠ 0`): `1/(p+1)` ramified,
  `p/(2(p+1))` inert and split; fired through the V2 spine
  (`MontesDataV2.countingDensity_eq_sum_coeff` at `(M7 p, uniformD p)` — the exact
  decomposition theorem `goal_theorem_montes` routes its value clause through; the full
  `goal_theorem_montes` is NOT consumable here because its conclusion bundles palindromy
  from an `htameFE` input, and palindromy is OUT OF SCOPE by directive);
* (B) **bracket uniqueness, fired OUTRIGHT via `hExhaustP`** (the exhaustion discharged
  at every `p`, pure counting, no axiom): any `d` bracketed by the decided counts and the
  undecided remainder at every level IS the counting density.

**Honest scope**: counting-side digit fibers (σ-keying faithfulness = W6q-d's
`fullFiber7`-successor over re-scope #6, packaged separately); NO palindromy clause and NO
`htameFE` hypothesis (directive, 2026-07-22); footprint must be Lean core only
(`AxCheck` below). The hypothesis `hσ` pins the degree-2 scope of the STATEMENT (the
W6 clause shape, where it fed the palindromy transfer); with palindromy cut, no clause
consumes it — the linter is silenced locally rather than changing the capstone shape. -/
theorem montes_uniform_n2 (σ : FactorizationType) (hσ : σ.degree = 2) :
    (uniformDen σ ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → (uniformDen σ).eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ shapesOfU σ, CU T q')
          = (uniformNum σ).eval (q' : ℚ) / (uniformDen σ).eval (q' : ℚ)) ∧
      ((M7 p).countingDensity σ
          = (uniformNum σ).eval ((p : ℕ) : ℚ) / (uniformDen σ).eval ((p : ℕ) : ℚ)
        ∧ (uniformDen σ).eval ((p : ℕ) : ℚ) ≠ 0)) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N) ≤ d ∧
        d ≤ (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N)
              + (M7 p).undecidedCount N / (p : ℚ) ^ (2 * N)) →
      d = (M7 p).countingDensity σ := by
  have hsumval : ∀ q' : ℕ, (∑ T ∈ shapesOfU σ, CU T q') = uniformValueFn σ q' := by
    intro q'
    unfold shapesOfU
    by_cases hmem : σ ∈ typeMenuP
    · rw [if_pos hmem, Finset.sum_singleton]
      unfold CU
      rw [markerU_type hmem]
    · rw [if_neg hmem, Finset.sum_empty, uniformValueFn_off hmem]
  constructor
  · refine ⟨uniformDen_ne_zero σ,
      fun q' hq' => ⟨uniformDen_eval_ne σ (by omega), ?_⟩, ?_, ?_⟩
    · rw [hsumval q']
      exact uniformValueFn_eq_eval σ q'
    · -- (V): fire the V2 spine at (M7 p, uniformD p)
      rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff (uniformD p) σ]
      show (∑ T ∈ shapesOfU σ, CU T p) = _
      rw [hsumval p]
      exact uniformValueFn_eq_eval σ p
    · exact uniformDen_eval_ne σ hp.out.pos
  · intro d hd
    have hlim : Tendsto
        (fun N => (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N))
        atTop (nhds ((M7 p).countingDensity σ)) := (M7 p).decided_tendsto σ
    have h1 : (M7 p).countingDensity σ ≤ d := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hd N hN).1
    have h2 : d ≤ (M7 p).countingDensity σ := by
      have hEx : Tendsto
          (fun N => (M7 p).undecidedCount N / (p : ℚ) ^ (2 * N))
          atTop (nhds 0) := hExhaustP p
      have hlim2 : Tendsto
          (fun N => (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N)
            + (M7 p).undecidedCount N / (p : ℚ) ^ (2 * N))
          atTop (nhds ((M7 p).countingDensity σ)) := by
        have hadd := hlim.add hEx
        simpa using hadd
      refine ge_of_tendsto hlim2 ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hd N hN).2
    exact le_antisymm h2 h1

/-- G-checksum at EVERY prime: the three uniform densities exhaust the box. -/
theorem gate_uniform_checksum :
    (M7 p).countingDensity ramType2 + (M7 p).countingDensity inertType2
      + (M7 p).countingDensity splitType2 = 1 := by
  show uniformValueFn ramType2 p + uniformValueFn inertType2 p
      + uniformValueFn splitType2 p = 1
  exact uniformValue_checksum p

end PrimeBank

/-! ## §J. Gates at the anchor primes (blueprint §0 census anchors) -/

/-- `p = 2` recovery gate (ram): the uniform value at the WILD prime is W6's
machine-checked `1/3` — `R_ram(2) = 1/(2+1)`. -/
theorem gate_uniform_p2_ram : (M7 2).countingDensity ramType2 = 1 / 3 := by
  show uniformValueFn ramType2 2 = 1 / 3
  unfold uniformValueFn
  rw [if_pos rfl]
  norm_num

/-- `p = 2` recovery gate (inert): `R_inert(2) = 2/(2·3) = 1/3`. -/
theorem gate_uniform_p2_inert : (M7 2).countingDensity inertType2 = 1 / 3 := by
  show uniformValueFn inertType2 2 = 1 / 3
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_inert), if_pos rfl]
  norm_num

/-- `p = 2` recovery gate (split): `R_split(2) = 1/3`. -/
theorem gate_uniform_p2_split : (M7 2).countingDensity splitType2 = 1 / 3 := by
  show uniformValueFn splitType2 2 = 1 / 3
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
  norm_num

/-- `p = 3` census gate (ram): `R_ram(3) = 1/4` (the mod-`3⁷` census: 182/729 from below,
undecided exactly `3^{−6}` at `N = 7`). -/
theorem gate_uniform_p3_ram : (M7 3).countingDensity ramType2 = 1 / 4 := by
  show uniformValueFn ramType2 3 = 1 / 4
  unfold uniformValueFn
  rw [if_pos rfl]
  norm_num

/-- `p = 3` census gate (inert): `R_inert(3) = 3/8` (census: 91/243 from below). -/
theorem gate_uniform_p3_inert : (M7 3).countingDensity inertType2 = 3 / 8 := by
  show uniformValueFn inertType2 3 = 3 / 8
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_inert), if_pos rfl]
  norm_num

/-- `p = 3` census gate (split): `R_split(3) = 3/8`. -/
theorem gate_uniform_p3_split : (M7 3).countingDensity splitType2 = 3 / 8 := by
  show uniformValueFn splitType2 3 = 3 / 8
  unfold uniformValueFn
  rw [if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
  norm_num

/-- **`gate_wild_included` — the wild prime IS an instance of the uniform family**: the
general-`p` model at `p = 2` has THE SAME counting density as W6's machine-checked
`realMW6`, for EVERY type — the decided counts are equal level-by-level
(`UniformModelN2Recovery.decidedCountP_two_eq`), hence the decided limits coincide (limit
uniqueness in `ℚ`). This is a MODEL-level tie, not just a value coincidence. -/
theorem gate_wild_included (σ : FactorizationType) :
    (M7 2).countingDensity σ = SeriesAssembly.realMW6.countingDensity σ := by
  have hfun : ∀ N : ℕ,
      SeriesAssembly.decidedCount6 σ N / ((M9.realP : ℕ) : ℚ) ^ (2 * N)
        = decidedCountP 2 σ N / ((2 : ℕ) : ℚ) ^ (2 * N) := by
    intro N
    rw [decidedCountP_two_eq]
    norm_num [M9.realP]
  have h1 : Tendsto (fun N => decidedCountP 2 σ N / ((2 : ℕ) : ℚ) ^ (2 * N)) atTop
      (nhds ((M7 2).countingDensity σ)) := (M7 2).decided_tendsto σ
  have h2 : Tendsto (fun N => decidedCountP 2 σ N / ((2 : ℕ) : ℚ) ^ (2 * N)) atTop
      (nhds (SeriesAssembly.realMW6.countingDensity σ)) :=
    Tendsto.congr hfun (SeriesAssembly.realMW6.decided_tendsto σ)
  exact tendsto_nhds_unique h1 h2

end LeanUrat.OM.UniformCapstone

/-! ## AxCheck — THE CAPSTONE and every supporting declaration must be Lean core ONLY
(`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event;
`om_leaf_faithful` anywhere in this cone is a FAILURE). -/

section AxCheck

-- §A/§B: the folded-weight bank and the composition bounds
#print axioms LeanUrat.OM.UniformCapstone.w_step_le_half
#print axioms LeanUrat.OM.UniformCapstone.w_sum_le
#print axioms LeanUrat.OM.UniformCapstone.w_sum_le_third
#print axioms LeanUrat.OM.UniformCapstone.w_dom
#print axioms LeanUrat.OM.UniformCapstone.stall_sum_le_one
#print axioms LeanUrat.OM.UniformCapstone.fix_sum_le
#print axioms LeanUrat.OM.UniformCapstone.msWP_stall_le
#print axioms LeanUrat.OM.UniformCapstone.msWP_fix_le
-- §C: the ledger (exact per-level identities)
#print axioms LeanUrat.OM.UniformCapstone.chainC_ram_leafP
#print axioms LeanUrat.OM.UniformCapstone.chainC_inert_leafP
#print axioms LeanUrat.OM.UniformCapstone.chainC_split_leafP
#print axioms LeanUrat.OM.UniformCapstone.chainC_factorP
#print axioms LeanUrat.OM.UniformCapstone.card_rootedPairs_castQ
#print axioms LeanUrat.OM.UniformCapstone.transChainCountP_cast
#print axioms LeanUrat.OM.UniformCapstone.transChainCountU_cast
#print axioms LeanUrat.OM.UniformCapstone.ord0Count_eq
-- §D/§E: the stall bridge, the covering, THE ENVELOPE, hExhaustP
#print axioms LeanUrat.OM.UniformCapstone.stallPairP_iff
#print axioms LeanUrat.OM.UniformCapstone.card_stallPairP_le
#print axioms LeanUrat.OM.UniformCapstone.transStallCountP_leW
#print axioms LeanUrat.OM.UniformCapstone.stallTotalP_le
#print axioms LeanUrat.OM.UniformCapstone.top_coveringP
#print axioms LeanUrat.OM.UniformCapstone.box_le_decidedP_add_stall
#print axioms LeanUrat.OM.UniformCapstone.undecided_envelopeP
#print axioms LeanUrat.OM.UniformCapstone.hExhaustP
-- §F/§G: monotonicity, the (U) closures, the squeeze
#print axioms LeanUrat.OM.UniformCapstone.decidedP_mono
#print axioms LeanUrat.OM.UniformCapstone.closure_ram
#print axioms LeanUrat.OM.UniformCapstone.closure_inert
#print axioms LeanUrat.OM.UniformCapstone.closure_split
#print axioms LeanUrat.OM.UniformCapstone.decidedP_le_valueP
#print axioms LeanUrat.OM.UniformCapstone.uniformValue_checksum
#print axioms LeanUrat.OM.UniformCapstone.decidedP_lower
#print axioms LeanUrat.OM.UniformCapstone.uniformDecided_tendsto
-- §H/§I: the model, the spine instance, THE CAPSTONE
#print axioms LeanUrat.OM.UniformCapstone.M7
#print axioms LeanUrat.OM.UniformCapstone.uniformD
#print axioms LeanUrat.OM.UniformCapstone.numR
#print axioms LeanUrat.OM.UniformCapstone.denR
#print axioms LeanUrat.OM.UniformCapstone.numI
#print axioms LeanUrat.OM.UniformCapstone.denI
#print axioms LeanUrat.OM.UniformCapstone.numS
#print axioms LeanUrat.OM.UniformCapstone.denS
#print axioms LeanUrat.OM.UniformCapstone.uniformValueFn_isRational
#print axioms LeanUrat.OM.UniformCapstone.montes_uniform_n2
-- §J: the gates
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_checksum
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p2_ram
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p2_inert
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p2_split
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p3_ram
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p3_inert
#print axioms LeanUrat.OM.UniformCapstone.gate_uniform_p3_split
#print axioms LeanUrat.OM.UniformCapstone.gate_wild_included
-- Re-census: the W6 capstone (unchanged trusted base)
#print axioms LeanUrat.OM.SeriesAssembly.montes_unconditional_n2_full

end AxCheck
