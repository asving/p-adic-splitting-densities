/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E02
import Uniformity.ChapE.E25
import Uniformity.ChapE.E30

/-!
# Uniformity.ChapE.E66 — the `q = 3` gate AND the non-coincidence seam witness, EXECUTED

**Chapter E, NODE E.66** [gate] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §10, the executable
gates; GC-11's two-prime rule: never `q = 2` alone). ENV-E1. The file signs NO new declaration —
it is executed `example`s over the landed defs of E.02/E.25/E.30 only.

Two batteries, both fired at heights the sealed teeth never reached:

* **(i) `q = 3`, the frame `(e₁, f₁, h) = (3, 1, 2)`** — FINDING HE7-F1's own counterexample
  frame. The height `k = 1` is UNATTAINED: its class index solves `i₀·h ≡ k (mod e₁)`, i.e.
  `2i₀ ≡ 1 (mod 3)`, so `i₀ = 2` and the shallowest slot already sits at `i₀h = 4 > 1`; hence
  `T(1) = ∅` (E.30(iii)). The attainable heights `{3a + 2i}` are spot-checked (`1` out; `2, 3,
  4, 5` in), and the base rung's `bound₁ = (e₁f₁ − 1)h = (3·1 − 1)·2 = 4`.
* **(ii) the NON-coincidence seam regime at `(e₁, f₁, h) = (2, 2, 3)`** — `HYP.151`'s witness
  frame, pushed PAST the coincidence bound `k ≤ (D′ − 1)h = 9`. At `k = 10`: `i₀ = 0` (from
  `3i₀ ≡ 10 (mod 2)`), `T(10) = {t < 2 : (0 + 2t)·3 ≤ 10} = {0, 1}` is FULL, and `k = 10` is the
  FIRST height past the regime (`(D′−1)h + 1 = 10`). At `k = 11`: `i₀ = 1`, `T(11)` full.
  Seam-exponent integrality (E.25's `seam_exp_dvd`) is fired at both heights and both slots.

**Why this gate exists** (honesty E-6, verbatim from the blueprint): four hostile rounds missed
`HYP.151`'s defect INSIDE the coincidence regime, where `q(k) = 0` seals the tooth. Every check
in battery (ii) therefore sits strictly outside that regime, and the battery additionally
exhibits a PROPER (nonempty, non-full) reach set at the same frame — `T(3) = {0}` at `i₀ = 1` —
which the sealed teeth could not produce and which the `k`-uniform bound (E.30(ii)) provably
does not cover at `k = 3 < 9`.

## How the checks are written

* **the lemmas are FIRED, not just the defs evaluated.** Each `decide`d value is accompanied by
  the landed lemma that predicts it: `reachSet_empty_iff` (E.30(iii)) for `T(1) = ∅`,
  `reachSet_full_iff` (E.30(i)) and `reachSet_full_of_uniform` (E.30(ii)) for the two full sets,
  `seam_exp_dvd` (E.25) for the four integrality facts. A gate that only `decide`s bodies scores
  the definitions; scoring the lemmas is what kills a mis-stated hypothesis.
* **no `native_decide` anywhere** (repo policy).
* the GC-11 gate-spelling rider (A-E.1/E-D10) is not in play here: nothing in this file compares
  two σ-values. Every line is `ℕ`-arithmetic or a `Finset (Fin f₁)` equation, both with real
  `DecidableEq` instances.

## Frame bookkeeping (the corpus letters → the landed arguments)

`reachSet e h f₁ i₀ k` (E.30) takes the SLOPE denominator `e = e₁` first and the height `h`
second; `RungDatum.mk ℓ g u T` (E.01) takes the base rung of a frame `(e₁, f₁, h)` as
`ℓ = e₁, g = f₁, u = h, T = 0`, whose `nextBound 0 = (e₁f₁ − 1)h` is the frame's `bound₁`
(E.02). Battery (i) is therefore `reachSet 3 2 1 i₀ k` and `RungDatum.mk 3 1 2 0`; battery (ii)
is `reachSet 2 3 2 i₀ k`.

**DEPENDS.** E.02 (`nextBound`), E.25 (`seam_exp_dvd`), E.30 (`reachSet` and its three clauses)
— all imported.

**SOURCE.** `EFF.HE7.21` (FINDING HE7-F1's two counterexample frames, machine-confirmed by
HE7-T-LIFT2SHARP); `spec/HYPOTHESIS_LEDGER.md` HYP.151 (the `(2,2,3)` witness and the sharp
threshold `k > (D′−1)h = 9`); GC-11 (two primes, executed pre-fleet).

**TEETH.** the coincidence-regime trap (HYP.151; G.23's class) → this gate is the mechanical
instrument GC-11 mandates. Retained regression: `verification/chapE_gate_q3_seam.py`.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free: the file declares nothing, and every `example` closes by `decide`,
`norm_num`, or an application of a landed Lean-core lemma.
-/

namespace Uniformity.Density.Ladder

/-! ## Battery (i) — `q = 3` at the frame `(e₁, f₁, h) = (3, 1, 2)` (FINDING HE7-F1)

The prime is `q = 3` in the frame's slope denominator `e₁ = 3`; GC-11 forbids scoring `q = 2`
alone, and E.65 is the `q = 2` half. -/

/-- (i) the class index at `k = 1`: `i₀ = 2` solves `i₀·h ≡ k (mod e₁)`, i.e. `2·2 ≡ 1 (mod 3)`.
This is E.25's `hk` hypothesis shape (`k % e = (i * h) % e`) at the frame. -/
example : (2 * 2) % 3 = 1 % 3 := by decide

/-- (i) **the height `k = 1` is UNATTAINED**: `T(1) = ∅` at `i₀ = 2`, because the shallowest slot
sits at `i₀h = 4 > 1`. -/
example : reachSet 3 2 1 2 1 = ∅ := by decide

/-- (i) the same emptiness PREDICTED by E.30(iii) rather than computed: `reachSet_empty_iff`
fires at `k = 1 < i₀·h = 4`. -/
example : reachSet 3 2 1 2 1 = ∅ :=
  (reachSet_empty_iff (by norm_num)).mpr (by norm_num)

/-- (i) and the converse reading of the same clause: emptiness at this frame IS the height
inequality `k < i₀·h`, so no other explanation of `T(1) = ∅` is available. -/
example : (1 : ℕ) < 2 * 2 :=
  (reachSet_empty_iff (f₁ := 1) (e := 3) (h := 2) (i₀ := 2) (k := 1) (by norm_num)).mp
    (by decide)

/-- (i) the frame's base rung `(e₁, f₁, h, 0) = (3, 1, 2, 0)` and its `bound₁ = (3·1 − 1)·2 = 4`
(E.02's recursion at `b = 0`). -/
example : (RungDatum.mk 3 1 2 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 0 = 4 := by decide

/-- (i) the attainable heights `{3a + 2i}` — `1` is NOT of that shape … -/
example : ¬ ∃ a < 3, ∃ i < 3, 3 * a + 2 * i = 1 := by decide

/-- (i) … while `2`, `3`, `4` and `5` are. -/
example : ∃ a < 3, ∃ i < 3, 3 * a + 2 * i = 2 := by decide

example : ∃ a < 3, ∃ i < 3, 3 * a + 2 * i = 3 := by decide

example : ∃ a < 3, ∃ i < 3, 3 * a + 2 * i = 4 := by decide

example : ∃ a < 3, ∃ i < 3, 3 * a + 2 * i = 5 := by decide

/-! ## Battery (ii) — the NON-coincidence seam at `(e₁, f₁, h) = (2, 2, 3)` (HYP.151)

`D′ = e₁f₁ = 4`, so the coincidence bound is `(D′ − 1)h = 9`: every check below is at
`k ≥ 10 = (D′−1)h + 1`, i.e. strictly outside the regime where `q(k) = 0` seals the tooth.
The single exception is the deliberate PROPER-set check at `k = 3`, which exists to show the
frame is not degenerate. -/

/-- (ii) the coincidence bound at the frame: `(D′ − 1)h = (2·2 − 1)·3 = 9`, so `k = 10` is the
first height past the regime. -/
example : (2 * 2 - 1) * 3 = 9 := by decide

/-- (ii) the class index at `k = 10`: `i₀ = 0` (from `i₀·h ≡ k (mod e₁)`, `3i₀ ≡ 10 (mod 2)`). -/
example : (0 * 3) % 2 = 10 % 2 := by decide

/-- (ii) the class index at `k = 11`: `i₀ = 1`. -/
example : (1 * 3) % 2 = 11 % 2 := by decide

/-- (ii) `T(10) = {0, 1}` is FULL at `i₀ = 0`. -/
example : reachSet 2 3 2 0 10 = Finset.univ := by decide

/-- (ii) `T(11)` is FULL at `i₀ = 1`. -/
example : reachSet 2 3 2 1 11 = Finset.univ := by decide

/-- (ii) fullness at `k = 10` PREDICTED by E.30(i): the deepest slot `t = f₁ − 1 = 1` clears the
height, `(0 + 2·1)·3 = 6 ≤ 10`. -/
example : reachSet 2 3 2 0 10 = Finset.univ :=
  (reachSet_full_iff (by norm_num)).mpr (by norm_num)

/-- (ii) fullness at `k = 11` PREDICTED by E.30(ii), the `k`-uniform bound: `(e·f₁ − 1)h = 9 ≤ 11`
forces fullness whatever class `k = 11` lands in. This is the clause whose hypothesis the
coincidence regime hides — here it is fired strictly above the bound. -/
example : reachSet 2 3 2 1 11 = Finset.univ :=
  reachSet_full_of_uniform (by norm_num) (by norm_num) (by norm_num)

/-- (ii) seam-exponent integrality at `k = 10`, slot `t = 0` — `decide`d. -/
example : (2 : ℕ) ∣ 10 - (0 + 2 * 0) * 3 := by decide

/-- (ii) seam-exponent integrality at `k = 10`, slot `t = 1` — `decide`d. -/
example : (2 : ℕ) ∣ 10 - (0 + 2 * 1) * 3 := by decide

/-- (ii) seam-exponent integrality at `k = 11`, slot `t = 0` — `decide`d. -/
example : (2 : ℕ) ∣ 11 - (1 + 2 * 0) * 3 := by decide

/-- (ii) seam-exponent integrality at `k = 11`, slot `t = 1` — `decide`d. -/
example : (2 : ℕ) ∣ 11 - (1 + 2 * 1) * 3 := by decide

/-- (ii) the same four facts PREDICTED by E.25's `seam_exp_dvd` rather than computed, at
`k = 10`, both slots: coprimality `Nat.Coprime h e = Coprime 3 2`, class `10 % 2 = (0·3) % 2`,
floor `(0 + 2t)·3 ≤ 10`. -/
example : (2 : ℕ) ∣ 10 - (0 + 2 * 0) * 3 :=
  seam_exp_dvd (by decide) (by norm_num) (by decide) (by norm_num)

example : (2 : ℕ) ∣ 10 - (0 + 2 * 1) * 3 :=
  seam_exp_dvd (by decide) (by norm_num) (by decide) (by norm_num)

/-- (ii) and at `k = 11`, both slots (class `11 % 2 = (1·3) % 2`). -/
example : (2 : ℕ) ∣ 11 - (1 + 2 * 0) * 3 :=
  seam_exp_dvd (by decide) (by norm_num) (by decide) (by norm_num)

example : (2 : ℕ) ∣ 11 - (1 + 2 * 1) * 3 :=
  seam_exp_dvd (by decide) (by norm_num) (by decide) (by norm_num)

/-! ### The `q(k) ≠ 0`-side witness the sealed teeth lacked

A PROPER reach set at the same frame: `T(3) = {0}` at `i₀(3) = 1` — nonempty (so E.30(iii) does
not apply) and not full (so E.30(i)'s deepest slot fails). ⚠ `k = 3 < 9 = (D′−1)h`, so the
`k`-uniform bound E.30(ii) is SILENT here — which is precisely the point: inside the coincidence
regime the reach set carries information the uniform clause cannot see. -/

example : (1 * 3) % 2 = 3 % 2 := by decide

example : reachSet 2 3 2 1 3 ≠ Finset.univ := by decide

example : reachSet 2 3 2 1 3 ≠ ∅ := by decide

/-- the uniform clause's hypothesis genuinely FAILS at `k = 3`: `(e·f₁ − 1)h = 9 > 3`. So the
proper set above is not a counterexample to E.30(ii) — it is outside its scope. -/
example : ¬ ((2 * 2 - 1) * 3 ≤ 3) := by decide

end Uniformity.Density.Ladder
