/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D10
import Uniformity.ChapD.D27
import Uniformity.ChapD.D28
import Uniformity.ChapD.D45
import Uniformity.ChapD.D48

/-!
# Uniformity.ChapD.D66 — the `q = 3` gate: the X frame and the T4 threshold table, EXECUTED

**Chapter D, NODE D.66** [gate] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §10, the executable
gates; **amendment A-D.1 re-signs this node** — defect D-D1's reduce-then-decide rider, `Θ` as
literal data, and the MANDATORY new leg 5 that finding D-F1 forces). ENV-D5. The file signs one
small certificate theorem (`gate66h2inv`, leg 5's inverse datum); everything else is gate-local
data plus executed `example`s.

*The frame* (`EFF.T1.33`, verbatim values): the X frame `p = 3`, `e₁ = 2, f₁ = 1, h = 1`,
`η = 2 ∈ 𝔽₃`, `u₂ = 3` — GC-11's second prime (never `q = 2` alone).

* **leg 1, the exponent tables**: `iexp 2 1` / `aexp 2 1` / `qexp 2 1` on `k = −2…6`, plus
  `(C5-carry)` (D.15), `(C2-wrap)` with `wrap ≤ 1` (D.14) and D.27's binary-carry composite law,
  each EXECUTED on grids INCLUDING negative heights.
* **leg 2, the telescope**: `(ϑ_{1,0},…,ϑ_{1,4}) = (1, 1, 2, 2, 1)` (`2^{⌊s/2⌋} mod 3`) and the
  involution table `Θ_s·ϑ_s = 1` with `Θ = (1, 1, 2, 2, 1)` (`2⁻¹ = 2` in `𝔽₃`) — D.10 executed.
* **leg 3, the corrected/naive split** (the X frame's axis): D.28 clause 3's criterion fires —
  at `s ≥ 2` slots with `c_t ≠ 0`, `c_t(ϑ − 1) ≠ 0` since `ϑ₂ = 2 ≠ 1`.
* **leg 4, the T4 threshold table**: `thresholdTheta 3 3 1 = (10, 7, 4)` on `j = 0,1,2` —
  FR-M3's committed thresholds — plus the separator arithmetic against FR-M3's self-shadow pins
  `[12, 7, 4]`: `ν₀ = 12 > 10 = Θ₀` (untouched WITH SLACK, `ω₀ = 0` — D.48's fence) while
  `j = 1, 2` attain, stated both in `ℕ` and in `ℕ∞` (D.47's `nuIdx` codomain), together with
  D.45's antitony at this frame.
* **leg 5, FRAME-H2** (`e₁ = 3, h = 2`, coprime): the `h > 1` separator frame — see D-F1 below.

## The three riders that govern how these lines are written

1. **D-D1 (the mandatory §10 gate-writing rider).** `iexp` routes through `ZMod.inv`, whose
   `Nat.gcdA`/`Nat.xgcd` does NOT kernel-reduce: a bare `decide` FAILS on every line mentioning
   `iexp`, `aexp`, `qexp`, `wrap` or `Wfloor`, and `Θ_s = ϑ_s⁻¹` cannot be spelled at all. Legs
   1–3 therefore reduce through D.13's proved `iexp_one` (`h = 1` at the X frame) before
   deciding; **leg 5 has `h = 2`, so its reducer is D.13's `iexp_eq_of_inv 3 2 2 gate66h2inv`**,
   whose hypothesis is the `decide`-able inverse equation `2·2 = 1` in `ZMod 3`. Leg 4 is pure
   `ℕ`/`ℕ∞` with no `iexp` in sight, so a bare `decide` IS correct there. **No expected value
   changes.**
2. **`Θ` is committed as LITERAL DATA, with the involution as its certificate** (note SD-7). The
   gate never spells `Θ_s` as `(ϑ s)⁻¹`; it commits `gate66theta = [1, 1, 2, 2, 1]` and then
   EXECUTES `Θ_s·ϑ_s = 1` (D.10), which is the proof that the committed table IS the
   inverse-orientation telescope. Same for FRAME-H2's `gate66h2theta` over `𝔽₇`.
3. **`native_decide` appears NOWHERE** (repo policy: a `native_decide` anywhere in chapter D is a
   stop-the-line event).

## ⚠ FINDING D-F1 — the X frame cannot separate `aexp` from `qexp`, and leg 5 is the repair

At `h = 1` one has `i₀ = iexp 2 1 1 = 1`, so `qexp ≡ aexp` **identically**: both of leg 1's
tables come out `[-1,-1,0,0,1,1,2,2,3]`, the leg scores the same function twice, and an
`aexp`/`qexp` confusion **survives it**. This is a coverage hole in the frame, not a defect in
D.13/D.15. **Leg 5 closes it and is MANDATORY** (A-D.1): at FRAME-H2 (`e₁ = 3, h = 2`, so
`i₀ = iexp 3 2 1 = 2 ≠ 1`) the two functions differ at every `k ∈ {1,…,6}` — they agree only at
`k ∈ {−2, −1, 0}` — and an `aexp`/`qexp` swap is now a failing `decide`. Leg 5 additionally
scores a `Wfloor` table with a NON-CONSTANT `i(u₂) = 2` (`Wfloor 3 2 1 4 = (2,2,1,0)`), which no
`h = 1` frame in this chapter can do, so the misindexed-telescope mutant is killed in the
`i(u₂)` factor too; and, over `K₁ = 𝔽₇` with `η = 2` of order 3, it runs the orientation
discipline at a THIRD prime — the only frame here where the `ϑ`-exponent grows by 2 per two
steps.

**Leg 5 has NO source unit.** It is authored by amendment A-D.1 in response to D-F1, and it is a
GATE, not new mathematics: every value in it is computed from D.13/D.15/D.16's committed
definitions, nothing is compared against inherited evidence, and no expected value of an
inherited frame is touched. GC-10's "deviations only via dated AMENDMENT blocks" is satisfied by
A-D.1 itself.

DEPENDS (blueprint): D.10 (the involution), D.13 (`iexp`/`aexp`, `iexp_one`, `iexp_eq_of_inv`),
D.14 (`wrap`, `(C2-wrap)`), D.15 (`qexp`, `(C5-carry)`), D.16 (`Wfloor` — leg 5's table), D.18
(the telescope's exponent formula), D.27 (the binary-carry composite law), D.28 (clause 3's
corrected/naive criterion), D.45 (`thresholdTheta` and its antitony), D.48 (the untouched-with-
slack fence). Imported as D.10 + D.27 + D.28 + D.45 + D.48, which cover all ten transitively.

**PROOF.** reduce-then-`decide` throughout (`ℕ`/`ℤ`/`ℕ∞`/`ZMod 3`/`ZMod 7`), with the reducer
chosen per rider 1.

SOURCE: `EFF.T1.33` (frame X: "`p = 3, e₁ = 2, f₁ = 1, h = 1, η = 2, u₂ = 3`; corrected versus
naive p-adic split"); `EFF.T4.20` (FR-M3: thresholds `[10,7,4]`, self-shadow pins `[12,7,4]`,
`ω₀ = 0`, `ω₁, ω₂ ≠ 0` — the retained measured configuration leg 4 anchors); `EFF.T4.11` (the
separator's meaning). Leg 5: no source unit (see above).

**TEETH.** GC-11's second prime; T1's wrong-sign and misindexed-telescope teeth at `q = 3` (the
`+e₁·wrap` side of `(C2-wrap)` and the `−q(k)` sign, on grids INCLUDING negative heights); T1
§4.2 check 10's grade-data arithmetic (the `e_{i+1} ∤ u_{i+1}` witness); T4 S8 PE1(2)'s slack
check ("specifically inspect FR-M3's measured slack `[12,7,4]` against `[10,7,4]`") → **executed
Lean gate**. **Leg 5 adds the `aexp`/`qexp` separation tooth (D-F1) and the `i(u₂) ≠ 1` `Wfloor`
tooth** — the two mutant classes no `h = 1` frame in this chapter can kill.

ENVIRONMENT: ENV-D5 (the concrete gate arena; no `variable` block, no section variables).

## Status

Sorry-free, axiom-free (Lean core only): the one theorem and the four gate-local defs print Lean
core, and every `example` closes by `decide`, after a `simp only` reduction where rider 1
requires one.
-/

section XFrame

open Uniformity.Density.Gauge

/-! ### Leg 1 — the exponent tables and the three carry laws (reduce-then-decide) -/

/-- leg 1: the `iexp` table on `k = −2 … 6`. -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => iexp 2 1 k)
    = [0, 1, 0, 1, 0, 1, 0, 1, 0] := by simp only [iexp_one]; decide

/-- leg 1: the `aexp` table on `k = −2 … 6` (Lean's `Int./` is `ediv` at the pin). -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => aexp 2 1 k)
    = [-1, -1, 0, 0, 1, 1, 2, 2, 3] := by simp only [aexp, iexp_one]; decide

/-- leg 1: the `qexp` table on `k = −2 … 6`. ⚠ FINDING D-F1: at this frame (`h = 1`, so
`i₀ = 1`) `qexp = aexp` identically — the X frame does NOT separate D.13's `aexp` from D.15's
`qexp`, so it cannot on its own catch a `qexp`/`aexp` confusion. Leg 5 (FRAME-H2) is the repair,
and it is mandatory. -/
example : ([-2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => qexp 2 1 k)
    = [-1, -1, 0, 0, 1, 1, 2, 2, 3] := by simp only [qexp, iexp_one]; decide

/-- leg 1: `(C5-carry)` EXECUTED on a grid (D.15), including negative heights. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    qexp 2 1 (a + b) = qexp 2 1 a + qexp 2 1 b + wrap 2 1 a b := by
  simp only [qexp, wrap, iexp_one]; decide

/-- leg 1: `(C2-wrap)` EXECUTED on the same grid (D.14) — the wrong-sign tooth's kill site is
the `+e₁·wrap` side of this identity. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    iexp 2 1 a + iexp 2 1 b = iexp 2 1 (a + b) + 2 * wrap 2 1 a b
      ∧ wrap 2 1 a b ≤ 1 := by
  simp only [wrap, iexp_one]; decide

/-- leg 1: D.27's binary-carry composite law EXECUTED at `c₂ ∈ {0,1}` — both carry cases. -/
example : ∀ a ∈ ([-1, 0, 1, 2] : List ℤ), ∀ b ∈ ([-1, 0, 1, 2] : List ℤ),
    ∀ u ∈ ([1, 2, 3] : List ℤ), ∀ c ∈ ([0, 1] : List ℕ),
      qexp 2 1 (a + b - c * u)
        = qexp 2 1 a + qexp 2 1 b + wrap 2 1 a b
          - c * (qexp 2 1 u + wrap 2 1 (a + b - c * u) u) := by
  simp only [qexp, wrap, iexp_one]; decide

/-! ### Leg 2 — the telescope and the involution (`Θ` is DATA; the involution certifies it) -/

/-- gate-local data (D.66): the X-frame telescope in `𝔽₃ = ZMod 3` (`η = 2`), ASSEMBLED from
D.18's exponent formula `ϑ_s = η^{⌊s·i(u₂)/e₁⌋}` at `e₁ = 2, h = 1, u₂ = 3`. -/
def gate66vartheta (s : ℕ) : ZMod 3 := (2 : ZMod 3) ^ (s * iexp 2 1 3 / 2)

/-- leg 2: `(ϑ_{1,0},…,ϑ_{1,4}) = (1, 1, 2, 2, 1)`. -/
example : (List.range 5).map (fun s => gate66vartheta s) = [1, 1, 2, 2, 1] := by
  simp only [gate66vartheta, iexp_one]; decide

/-- gate-local data (D.66): the X-frame `Θ` table as LITERAL DATA. ⚠ `ZMod.inv` does not
kernel-reduce (defect D-D1), so `Θ` is NOT spelled `(ϑ s)⁻¹` here; it is committed as data and
the involution below is the check that it IS the inverse. `2⁻¹ = 2` in `𝔽₃`. -/
def gate66theta : List (ZMod 3) := [1, 1, 2, 2, 1]

/-- leg 2: the involution table `Θ_s·ϑ_s = 1` with `Θ = (1, 1, 2, 2, 1)` — D.10 EXECUTED. -/
example : ∀ s ∈ List.range 5, gate66theta.getD s 0 * gate66vartheta s = 1 := by
  simp only [gate66vartheta, gate66theta, iexp_one]; decide

/-! ### Leg 3 — the corrected/naive split, the X frame's own axis -/

/-- leg 3: the corrected/naive split — `ϑ₂ = 2 ≠ 1`, so D.28 clause 3's criterion fires. -/
example : gate66vartheta 2 ≠ 1 ∧ gate66vartheta 3 ≠ 1 := by
  simp only [gate66vartheta, iexp_one]; decide

/-- leg 3: the criterion at every nonzero unit digit — `c_t(ϑ₂ − 1) ≠ 0` for `c_t ≠ 0`. -/
example : ∀ c ∈ ([1, 2] : List (ZMod 3)), c * (gate66vartheta 2 - 1) ≠ 0 := by
  simp only [gate66vartheta, iexp_one]; decide

/-! ### Leg 4 — the T4 threshold table (pure `ℕ`/`ℕ∞`: bare `decide` IS correct here) -/

/-- leg 4: the T4 threshold table — **FR-M3's committed thresholds `[10,7,4]`**
(`EFF.T4.20`). -/
example : (List.range 3).map (fun j => thresholdTheta 3 3 1 j) = [10, 7, 4] := by decide

/-- leg 4: the separator arithmetic. FR-M3's self-shadow pins are `[12,7,4]`: at `j = 0`
`ν₀ = 12 > 10 = Θ₀` (untouched WITH SLACK, `ω₀ = 0` — D.48's fence), while `j = 1, 2`
attain. `EFF.T4.11`, `EFF.T4.20`. -/
example : thresholdTheta 3 3 1 0 < 12
    ∧ thresholdTheta 3 3 1 1 = 7
    ∧ thresholdTheta 3 3 1 2 = 4 := by decide

/-- leg 4: the same three facts in `ℕ∞`, the codomain of D.47's `nuIdx`. -/
example : ((thresholdTheta 3 3 1 0 : ℕ) : ℕ∞) < (12 : ℕ∞)
    ∧ ((thresholdTheta 3 3 1 1 : ℕ) : ℕ∞) = (7 : ℕ∞)
    ∧ ((thresholdTheta 3 3 1 2 : ℕ) : ℕ∞) = (4 : ℕ∞) := by decide

/-- leg 4: D.45's antitony EXECUTED at the FR-M3 frame. -/
example : thresholdTheta 3 3 1 2 < thresholdTheta 3 3 1 1
    ∧ thresholdTheta 3 3 1 1 < thresholdTheta 3 3 1 0 := by decide

end XFrame

/-! ## Leg 5 — FRAME-H2 (`e₁ = 3, h = 2`), the `h > 1` separator frame [A-D.1/D-F1]

The frame finding D-F1 makes this leg MANDATORY: without it nothing in chapter D scores D.15
independently of D.13.  `e₁ = 3, h = 2` are coprime, `2⁻¹ = 2` in `ZMod 3`, and
`i₀ = iexp 3 2 1 = 2 ≠ 1`.  The optional field leg runs over `K₁ = 𝔽₇` with `η = 2` (order 3) at
`u₂ = 1`.  Every row reduces with `iexp_eq_of_inv 3 2 2 gate66h2inv` in place of `iexp_one`. -/

section FrameH2

open Uniformity.Density.Gauge

/-- leg 5, the frame's inverse datum: `2·2 = 1` in `ZMod 3`, the `c` that makes `iexp 3 2`
kernel-reducible via D.13's `iexp_eq_of_inv` (defect D-D1's general repair). -/
theorem gate66h2inv : ((2 : ℕ) : ZMod 3) * (2 : ZMod 3) = 1 := by decide

/-- leg 5: `iexp 3 2` on `k = −3…6` — the wrap bit is genuinely three-valued here, `{0,1,2}`. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => iexp 3 2 k)
    = [0, 2, 1, 0, 2, 1, 0, 2, 1, 0] := by
  simp only [iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: `aexp 3 2` on the same range. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => aexp 3 2 k)
    = [-1, -2, -1, 0, -1, 0, 1, 0, 1, 2] := by
  simp only [aexp, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: `qexp 3 2` on the same range — visibly NOT the `aexp` table above. -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5, 6] : List ℤ).map (fun k => qexp 3 2 k)
    = [-2, -2, -1, 0, 0, 1, 2, 2, 3, 4] := by
  simp only [qexp, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5, ★ **the D-F1 separation itself**: `aexp 3 2 k ≠ qexp 3 2 k` for every `k ∈ {1,…,6}`
(they agree only at `k ∈ {−2, −1, 0}`) — in particular at `k = 1`, where `aexp = −1` and
`qexp = 0`.  An `aexp`/`qexp` swap now fails a `decide`. -/
example : ∀ k ∈ ([1, 2, 3, 4, 5, 6] : List ℤ), aexp 3 2 k ≠ qexp 3 2 k := by
  simp only [aexp, qexp, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: `(C2-wrap)` and `wrap ≤ 1` at `h = 2`, on the grid `a, b ∈ {−2,…,3}`. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    iexp 3 2 a + iexp 3 2 b = iexp 3 2 (a + b) + 3 * wrap 3 2 a b ∧ wrap 3 2 a b ≤ 1 := by
  simp only [wrap, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: `(C5-carry)` at `h = 2`, on the same grid. -/
example : ∀ a ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ), ∀ b ∈ ([-2, -1, 0, 1, 2, 3] : List ℤ),
    qexp 3 2 (a + b) = qexp 3 2 a + qexp 3 2 b + wrap 3 2 a b := by
  simp only [qexp, wrap, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: `Wfloor 3 2 1 4 t = (2, 2, 1, 0)` for `t = 0…3` — a `Wfloor` table with a
NON-CONSTANT `i(u₂) = 2` (the `h = 1` frames all have `i(u₂) = 1`, which cannot expose a
misindexed-telescope mutant in the `i(u₂)` factor). -/
example : (List.range 4).map (fun t => Wfloor 3 2 1 4 t) = [2, 2, 1, 0] := by
  simp only [Wfloor, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: the frame datum that makes all of the above bite — `i₀ = iexp 3 2 1 = 2 ≠ 1`. -/
example : iexp 3 2 1 = 2 := by simp only [iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-! #### Leg 5, the (recommended) `𝔽₇` telescope: a THIRD prime for the orientation discipline -/

/-- gate-local data (D.66, FRAME-H2): `ϑ_s = 2^{⌊2s/3⌋}` over `𝔽₇`, assembled from D.18's
exponent formula at `e₁ = 3, h = 2, η = 2, u₂ = 1`. -/
def gate66h2vartheta (s : ℕ) : ZMod 7 := (2 : ZMod 7) ^ (s * iexp 3 2 1 / 3)

/-- gate-local data (D.66, FRAME-H2): the committed inverse table `Θ = (1, 1, 4, 2, 2, 1)`, as
LITERAL DATA (rider 2), certified by the involution below. -/
def gate66h2theta : List (ZMod 7) := [1, 1, 4, 2, 2, 1]

/-- leg 5: the telescope `ϑ = (1, 1, 2, 4, 4, 1)` on `s = 0…5` — the only frame in this chapter
where the `ϑ`-exponent grows by 2 per two steps. -/
example : (List.range 6).map (fun s => gate66h2vartheta s) = [1, 1, 2, 4, 4, 1] := by
  simp only [gate66h2vartheta, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

/-- leg 5: the involution `Θ_s·ϑ_s = 1` on `s = 0…5` over `𝔽₇` — D.10's orientation discipline
at a third prime, and the certificate that the committed table IS the inverse. -/
example : ∀ s ∈ List.range 6, gate66h2theta.getD s 0 * gate66h2vartheta s = 1 := by
  simp only [gate66h2vartheta, gate66h2theta, iexp_eq_of_inv 3 2 2 gate66h2inv]; decide

end FrameH2

/-! ## Axiom footprint

Leg 5's certificate theorem plus the gate's DATA layer, printed here (D.68(iv)'s discipline
applied locally); the executed `example`s are anonymous by construction and carry no footprint of
their own — their content is the fact that they elaborate at all. -/

section AxCheck

#print axioms gate66vartheta
#print axioms gate66theta
#print axioms gate66h2inv
#print axioms gate66h2vartheta
#print axioms gate66h2theta

end AxCheck
