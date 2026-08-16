/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D14
import Uniformity.ChapD.D28
import Uniformity.ChapD.D32
import Uniformity.ChapD.D58

/-!
# Uniformity.ChapD.D65 — the `q = 2` gate: the F4-JOINT frame, EXECUTED

**Chapter D, NODE D.65** [gate] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §10, the executable
gates; **amendment A-D.1 re-signs this node** — defect D-D1's reduce-then-decide rider, stub-side
decision SD-6's `𝔽₄` carrier, and finding D-D9's indexing convention are folded in). ENV-D5. No
signed theorem: a gate file, whose content is gate-local data plus executed `example`s.

*The frame* (`EFF.T1.33`, verbatim values): the F4-JOINT axes `e₁ = 2, f₁ = 2, h = 1`,
`K₁ = 𝔽₄`, `η = ω` of order 3, `u₂ = 3` ("live wrap"). This is GC-11's `e > 1 ∧ f > 1` witness:
at the gauge layer the meaningful pair is the level datum `(e₁, f₁) = (2, 2)`, both `> 1`
simultaneously.

* **leg 1, the exponent tables** (pure `ℕ`/`ℤ`): `iexp 2 1 k = k % 2` on `k = −3…5` (INCLUDING
  negative heights — §14 item 5's question, answered); the live wrap `wrap 2 1 a b = 1` exactly
  on odd/odd; the telescope exponent table `⌊s·i(3)/2⌋ = (0,0,1,1)` for `s = 0…3`, and the same
  table read through `Wfloor` at `f₂ = 3`.
* **leg 2, the telescope vector**: `(ϑ_{1,0},…,ϑ_{1,3}) = (1, 1, ω, ω)` — `EFF.T1.34`'s `μ = 3`
  leg, as the exponents `(0,0,1,1)`.
* **leg 3, the `μ = 3` canonical vector, ALL THREE entries scored** (`EFF.T1.39` check 5):
  `Γ = (1, ω, ω)`, `u(β) = (ω, ω, ω²)` (D.32's B-law), canonical `= (ω, ω², 1)` (D.58 + D.35),
  plus the slotwise cancellation `Γ_t·u(β_t) = w^s` (D.33).
* **leg 4, the quadratic triple**: `ϑ₂ = ω ≠ 1`, so D.28 clause 3's criterion fires and
  `R_naive = y² + y + 1 ≠ y² + y + ω = R_corr` (the gauge-naive mutant's kill site); and
  `ψ^{(w)} = y² + ωy + 1`'s coefficients from `(WF-psi)`'s law `c_t·w^{f−t}`.

## The two riders that govern how these lines are written

1. **D-D1 (the mandatory §10 gate-writing rider).** `iexp` routes through `ZMod.inv`, whose
   `Nat.gcdA`/`Nat.xgcd` does NOT kernel-reduce: a bare `decide` FAILS on every line mentioning
   `iexp`, `wrap` or `Wfloor` (even `((1 : ℕ) : ZMod 2)⁻¹ = 1` is not `decide`-able at the
   v4.31.0 pin), and `Θ_s = ϑ_s⁻¹` cannot be spelled at all. So every such line reduces through
   D.13's proved `iexp_one` first — `h = 1` at this frame — and only then decides. **Not one
   expected value of `EFF.T1.33/.34` changes**; the rows change.
2. **SD-6 — the `𝔽₄` carrier, DECIDED (the §10 ⚠, resolved).** `GaloisField 2 2` and
   `AdjoinRoot (X²+X+1 : (ZMod 2)[X])` are quotient constructions with **no computable
   `DecidableEq` at the pin**, so no `decide` runs inside them and legs 2–4 cannot be executed in
   either. The signed carrier is therefore the **discrete-log model**: `ω` has order 3 and every
   quantity in legs 2–4 is a power of `ω`, so `⟨ω⟩ ≅ (ZMod 3, +)` carries them **faithfully** —
   products become sums, every committed expected value becomes an exponent, and `ω^a = 1 ↔
   a = 0` preserves all four mutant kills. (Consequently `Θ_s = ϑ_s⁻¹` is spelled ADDITIVELY,
   as `-`, and no `ZMod.inv` occurs anywhere in this file.) An agent who wants the honest `𝔽₄`
   must supply a `DecidableEq` instance and re-run; this is the signed default and the record of
   why. The composition-time signature's comment naming `gate_f4_theta_vector` /
   `gate_f4_canonical` as `𝔽₄`-valued public theorems is superseded by that re-sign: the executed
   rows are the anonymous `example`s below, over the discrete-log carrier — the same disposition
   as the landed D.67, which likewise signs no theorem.

## ⚠ FINDING D-D9 — the indexing convention of leg 3, STATED

All three vectors of leg 3 are listed in **ASCENDING `s`** (`s = 1, 2, 3`), which is **DESCENDING
slot `t`**. The blueprint never states this, and read in SLOT order the committed entries are
wrong: `Γ` in slot order is `(ω, ω, 1)` and `u(β)` is `(ω², ω, ω)`. This gate scores them in the
ascending-`s` order and says so at each row. Every consumer of this leg — and every reader of
`EFF.T1.34`'s `μ = 3` row — must fix the order before comparing. *Class: the wrong-but-well-typed
defect §12 rule 3 warns a stub gate cannot catch mechanically; found by recomputing, then
executed.*

DEPENDS (blueprint): D.13 (`iexp`, `iexp_one`), D.14 (`wrap`), D.16 (`Wfloor`), D.17 (the level-1
arena), D.18 (the telescope's exponent formula), D.28 (clause 3's corrected/naive criterion),
D.32 (the B-law), D.35 (the `w`-twist), D.58 (the realized residual). Imported as D.14 + D.28 +
D.32 + D.58, which cover all nine transitively.

**PROOF.** reduce-then-`decide` throughout (`ℕ`/`ℤ`/`ZMod 3`); `native_decide` appears NOWHERE
(repo policy: a `native_decide` anywhere in chapter D is a stop-the-line event).

SOURCE: `EFF.T1.33` (the F4-JOINT frame axes), `EFF.T1.34` (all expected values, including
check 5's discipline "score all three entries of the canonical `μ = 3` vector, not only the
`s = 2` B-unit" — leg 3 scores all three), `EFF.T1.36` (check 2: "exact coefficient equality,
not merely factor pattern" — legs 3–4 are coefficient equalities).

**TEETH.** T1 §4.2 checks 2 and 5, and all four planted teeth of `EFF.T1.45` (gauge-naive,
wrong-sign, misindexed telescope, inverse orientation — each flips a value in legs 2–4; the named
kill sites here are `ϑ₂ = ω ≠ 1` for gauge-naive and the `Wfloor` slot table for the misindexed
telescope) → **executed Lean gate**; plus GC-11's `e > 1 ∧ f > 1` obligation, discharged by the
frame itself.

ENVIRONMENT: ENV-D5 (the concrete gate arena; no `variable` block, no section variables).

## Status

Sorry-free, axiom-free (Lean core only): the file declares no theorem, and every `example` closes
by `decide` after a `simp only` reduction.
-/

section F4Joint

open Uniformity.Density.Gauge

/-! ### Leg 1 — the exponent tables (pure `ℕ`/`ℤ`, reduce-then-decide) -/

/-- leg 1: the `iexp` table at `e₁ = 2, h = 1` is `k % 2` — including negative heights
(§14 item 5's question, answered: `ZMod.val` is always the nonnegative representative). -/
example : ([-3, -2, -1, 0, 1, 2, 3, 4, 5] : List ℤ).map (fun k => iexp 2 1 k)
    = [1, 0, 1, 0, 1, 0, 1, 0, 1] := by simp only [iexp_one]; decide

/-- leg 1: the live wrap — `wrap 2 1 a b = 1` exactly on odd/odd. -/
example : ∀ a ∈ ([0, 1, 2, 3] : List ℤ), ∀ b ∈ ([0, 1, 2, 3] : List ℤ),
    (wrap 2 1 a b = 1 ↔ (iexp 2 1 a = 1 ∧ iexp 2 1 b = 1)) := by
  simp only [wrap, iexp_one]; decide

/-- leg 1: the telescope exponent table `⌊s·i(3)/2⌋ = (0,0,1,1)` for `s = 0…3`. -/
example : (List.range 4).map (fun s => s * iexp 2 1 3 / 2) = [0, 0, 1, 1] := by
  simp only [iexp_one]; decide

/-- leg 1: the same table through `Wfloor` at `f₂ = 3` (slot indexing `s = f₂ − t`) — the
misindexed-telescope mutant's kill site. -/
example : (List.range 3).map (fun t => Wfloor 2 1 3 3 t) = [1, 1, 0] := by
  simp only [Wfloor, iexp_one]; decide

/-! ### The discrete-log `𝔽₄` model (SD-6): `ω^k ↦ k : ZMod 3` -/

/-- gate-local data (D.65): the F4-JOINT discrete-log model, `ω^k ↦ k : ZMod 3`. -/
def gate65varthetaExp (s : ℕ) : ZMod 3 := ((s * iexp 2 1 3 / 2 : ℕ) : ZMod 3)

/-- gate-local data (D.65): the B-law-orientation exponent `Θ_s = ϑ_s⁻¹`, additively (SD-6:
in the discrete-log carrier the multiplicative inverse IS negation, so defect D-D1's
unspellable `ZMod.inv` never appears). -/
def gate65thetaExp (s : ℕ) : ZMod 3 := -gate65varthetaExp s

/-- gate-local data (D.65): `w = ω`, so `w^s ↦ s`. -/
def gate65wExp (s : ℕ) : ZMod 3 := (s : ZMod 3)

/-! ### Leg 2 — the telescope vector -/

/-- leg 2: the telescope vector `(ϑ_{1,0},…,ϑ_{1,3}) = (1, 1, ω, ω)` — `EFF.T1.34`'s `μ = 3`
leg, as exponents `(0,0,1,1)`. -/
example : (List.range 4).map (fun s => gate65varthetaExp s) = [0, 0, 1, 1] := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-! ### Leg 3 — the `μ = 3` canonical vector, all three entries (⚠ ASCENDING `s`, D-D9) -/

/-- leg 3: the `μ = 3` canonical vector, ALL THREE entries scored (`EFF.T1.39` check 5).
The three vectors are listed in ASCENDING `s` (= DESCENDING slot `t`) — the blueprint's own
order, which it never states; see finding D-D9. `Γ = (1, ω, ω)`. -/
example : ([1, 2, 3] : List ℕ).map (fun s => gate65varthetaExp s) = [0, 1, 1] := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-- leg 3: `u(β) = (ω, ω, ω²)` — D.32's B-law `Θ_s·w^s` at the instance (ascending `s`). -/
example : ([1, 2, 3] : List ℕ).map (fun s => gate65thetaExp s + gate65wExp s)
    = [1, 1, 2] := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-- leg 3: the full canonical coefficient vector `(ω, ω², 1)` — assembling to `(y + ω)³`
(D.58 + D.35), in ascending `s`. -/
example : ([1, 2, 3] : List ℕ).map
    (fun s => gate65varthetaExp s + (gate65thetaExp s + gate65wExp s))
    = [1, 2, 0] := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-- leg 3, the cancellation itself: `Γ_t·u(β_t) = c_t·w^s` for unit digits — D.33's
coefficient identity, exponentwise. -/
example : ∀ s ∈ ([1, 2, 3] : List ℕ),
    gate65varthetaExp s + (gate65thetaExp s + gate65wExp s) = gate65wExp s := by
  simp only [gate65thetaExp, gate65varthetaExp, gate65wExp, iexp_one]; decide

/-! ### Leg 4 — the quadratic triple: the corrected/naive separation and `ψ^{(w)}` -/

/-- leg 4: the corrected/naive separation — `ϑ₂ = ω ≠ 1`, so D.28 clause 3's criterion fires
and `R_naive = y² + y + 1 ≠ y² + y + ω = R_corr` (the gauge-naive mutant's kill site). In the
discrete-log carrier `ω ≠ 1` reads `exponent ≠ 0`. -/
example : gate65varthetaExp 2 ≠ 0 := by
  simp only [gate65varthetaExp, iexp_one]; decide

/-- leg 4: `ψ^{(w)} = y² + ωy + 1` from `(WF-psi)`'s coefficient law `c_t·w^{f−t}` at
`f = 2`, `w = ω`, `(c₁, c₀) = (1, ω)` — exponents `(0, 1) ↦ (1, 0)`. -/
example : ([(1, (0 : ZMod 3)), (0, (1 : ZMod 3))] : List (ℕ × ZMod 3)).map
    (fun p => p.2 + gate65wExp (2 - p.1)) = [1, 0] := by
  simp only [gate65wExp]; decide

end F4Joint

/-! ## Axiom footprint

The file signs no theorem, so there is no capstone-facing name to print; what the census can
check here is that the gate's DATA layer is Lean-core-clean (D.68(iv)'s discipline applied
locally). The executed `example`s are anonymous by construction and carry no footprint of their
own — their content is the fact that they elaborate at all. -/

section AxCheck

#print axioms gate65varthetaExp
#print axioms gate65thetaExp
#print axioms gate65wExp

end AxCheck
