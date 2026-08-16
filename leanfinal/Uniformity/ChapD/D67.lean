/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D17
import Uniformity.ChapD.D38
import Uniformity.ChapD.D40

/-!
# Uniformity.ChapD.D67 — the FRAME-C regression (`p = 5`): T3's declared battery frame, EXECUTED

**Chapter D, NODE D.67** [gate] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §10, the executable
gates; **amendment A-D.1 re-signs this node** — the schematic `…` rows of the composition-time
signature were replaced by the EXECUTED ones, findings D-D1/D-F2/D-F3 are folded in, and leg 4
(the `ϑ`-orientation table) was ADDED here because FRAME-C is the one frame where every quantity
of D.06's table is a concrete `𝔽₅`-unit). ENV-D5. No signed theorem: a gate file, whose content
is gate-local data plus executed `example`s.

*The frame* (`EFF.T3.29`, verbatim values): two port instances over `𝔽₅ = ZMod 5` at the level-1
arena `e₁ = 2, h = 1, η = 2` (matching `res(x²/5) = 2`), with `w = res(x/T) = 3`.

* **leg 1, the BR leg (`q_BR = 1`)**: the tables `U = (1,3,2,1,4)` and `ϑ = (1,1,2,2,4)` on
  `s = 0…4`; the two runner obligations `w^s = U(s)·ϑ_s` and `U(s) = Θ_s·w^s`, both scored from
  the ASSEMBLED definitions; the wrong-orientation kill at `s = 2`.
* **leg 2, the CMP leg (`q_CMP = 2`, `N̂(k) = x^k`, `H₀ = 6`, `D = 3`)**: `χ(k) = 2^{⌊k/2⌋}`, the
  **non-character** check `χ(1)² = 1 ≠ 2 = χ(2)`, `δ = χ(2) = 2`, `χ(6) = 3`, and the comparison
  `ρ_t = χ(H₀)·ρ̂_t·δ^{−t}` in both its coefficient and its `𝔽₅[Z]` form.
* **leg 3**: the coverage record (below) — `(T3-JOINT-OPEN)` stays OPEN.
* **leg 4**: D.06's four-row orientation table as arithmetic, with the two mutation-killers.

## The three riders that govern how these lines are written

1. **D-D1 (mandatory gate-writing rider).** `iexp` routes through `ZMod.inv`, whose
   `Nat.gcdA`/`Nat.xgcd` does NOT kernel-reduce: a bare `decide` FAILS on every line mentioning
   `iexp`, and `Θ_s = ϑ_s⁻¹` cannot be spelled at all. So every such line reduces through D.13's
   proved `iexp_one` first (`simp only [<local defs>, iexp_one]; decide`), and `Θ` is committed as
   LITERAL DATA and then CHECKED against `ϑ` by the involution leg. `δ⁻¹ = 3` is likewise stated
   multiplicatively, as `2·3 = 1`.
2. **`EFF.T3.29`'s own instruction: never define `U(s)` from the endpoint formula.** Only `ϑ` is
   ASSEMBLED (from D.18's exponent formula at `q_BR = 1`); `U` and `Θ` are committed tables, so
   the two runner obligations are genuine checks rather than unfoldings. This is the §8.4(3)
   endpoint-as-input mutant's kill.
3. **FINDING D-F2 — the committed range is ONE STEP TOO SHORT.** D.06's row-1/row-4 relation
   `ϑ_{G2}(t) = Θ(f₃−t)` at the BOTTOM slot `t = 0` reads the telescope at `s = f₃ = 5`, outside
   `EFF.T3.29`'s committed `s = 0…4`. The range is extended by the ASSEMBLED formula (never by
   the endpoint formula): `ϑ₅ = 2^{⌊5/2⌋} = 4`, `Θ₅ = 4`, so the committed `Θ` table here has
   **six** entries `(1,1,3,3,4,4)` and the involution is scored on `s = 0…5`.

## ⚠ FINDING D-F3 — the scoring rule for leg 4(v)

`ϑ_{G2}(t) ≠ Θ(t)` (the reflection is not the identity) **must be scored at `t = 1` or `t = 4`,
never at `t = 2`/`t = 3`.** FRAME-C has `ϑ₂ = ϑ₃ = 2` (both floors `⌊s/2⌋` equal `1`), hence
`Θ₂ = Θ₃ = 3`, so an **index-shift mutant SURVIVES at the middle slots**: an agent scoring only
the middle of the table would miss the very mutant the table exists to catch. The last line of
this file executes `Θ₂ = Θ₃` explicitly, as the standing warning.

## What this gate does NOT claim (leg 3, the coverage record)

FRAME-C has both axes live — `Θ ≠ 1` at `s ≥ 2` and `w = 3 ≠ 1` — but "its reference `T` is
formal … This machine-coverage gap is not a proof gap" (`EFF.T3.30`). So **`(T3-JOINT-OPEN)`
stays open** (D.64's last routing row): this file exhibits no realized p-adic tower, instantiates
no `GaugeArena` at these numbers, and instantiates neither D.38's `(T3-BR)` nor D.40's
`(T3-CMP)`. Every line below is arithmetic over `ZMod 5` on gate-local data that REPRODUCES the
corpus's committed tables; the abstract theorems those tables shadow are proved, separately and
in full generality, at D.38 and D.40.

**Relation to the landed D.06.** Node D.06 carries a `private` copy of the leg-1/leg-4 block in
its own file (the table's arithmetic scored at its source, `gate06*` names, inaccessible from
here). This file is the chapter's retained FRAME-C regression (GC-8, named
`verification/chapD_frameC` at fleet close), so its data is public — D.68's census re-executes
the headline `decide` anchors by name — and the duplication is deliberate: if either copy ever
drifts, the two nodes disagree and one of them goes red.

DEPENDS (blueprint): D.06 (the orientation table), D.08 (the two telescopes), D.10 (the
involution), D.12 (`χ`, and its no-character-law fence), D.17 (the level-1 arena), D.38
(`(T3-BR)`), D.39/D.40 (`(T3-CMP)`). Imported as D.17 + D.38 + D.40, which cover all eight
transitively; the executable content additionally uses D.13's `iexp` and `iexp_one`.

**PROOF.** reduce-then-`decide` over `ZMod 5` (§10's rider); `native_decide` appears NOWHERE
(repo policy: a `native_decide` anywhere in chapter D is a stop-the-line event). The one
non-`decide` leg is the polynomial form of the comparison, which is `Finset`-sum congruence plus
`ring`.

SOURCE: `EFF.T3.29` (the whole frame, verbatim values), `EFF.T3.30` (`(T3-JOINT-OPEN)`).

**TEETH.** T3 §8.4(1) (the character mutant — leg 2's `≠`), §8.4(2)–(4) (theta-free /
endpoint-as-input / inverse-orientation mutants — leg 1's two identities, scored from assembled
definitions) → **executed Lean gate**; and leg 4 is the append-#54 trap's battery (the
wrong-orientation B-law fails at `s = 2`, the orientation swap fails at `t = 1` and `t = 4`).

ENVIRONMENT: ENV-D5 (the `ZMod`-concrete gate arena; no `variable` block, no section variables).

## Status

Sorry-free, axiom-free (Lean core only): the file declares no theorem, and every `example`
closes by `decide` after a `simp only` reduction, or by `ring`.
-/

section FrameC

open Uniformity.Density.Gauge

/-! ### Leg 1 — the BR leg (`q_BR = 1`): the telescope, the two runner obligations, the kill -/

/-- gate-local data (D.67): FRAME-C's `ϑ`, ASSEMBLED from D.18's exponent formula
`ϑ_s = η^{⌊s·i(u₂)/e₁⌋}` at `e₁ = 2, h = 1, η = 2, u₂ = 1` — never from the endpoint formula
(`EFF.T3.29`'s own instruction). -/
def gate67vartheta (s : ℕ) : ZMod 5 := (2 : ZMod 5) ^ (s * iexp 2 1 1 / 2)

/-- gate-local data (D.67): the B-law-orientation telescope `Θ_s = ϑ_s⁻¹` (D.06 rows 2–3), as
LITERAL DATA (defect D-D1: `ZMod.inv` does not kernel-reduce, so the inverse cannot be spelled;
it is committed here and then CHECKED against `ϑ` by the involution below).  SIX entries, not
five — FINDING D-F2's bottom-slot extension. -/
def gate67thetaL : List (ZMod 5) := [1, 1, 3, 3, 4, 4]

/-- `Θ` as a function of the T1 two-index slot count `s`. -/
def gate67theta (s : ℕ) : ZMod 5 := gate67thetaL.getD s 0

/-- gate-local data (D.67): FRAME-C's committed `U` table, as LITERAL DATA — so the two
identities below are genuine checks, not unfoldings (the §8.4(3) endpoint-as-input mutant's
kill). -/
def gate67U : List (ZMod 5) := [1, 3, 2, 1, 4]

/-- leg 1: `ϑ = (1, 1, 2, 2, 4)` on `s = 0…4` — `EFF.T3.29`'s committed table, reproduced from
the assembled formula. -/
example : (List.range 5).map (fun s => gate67vartheta s) = [1, 1, 2, 2, 4] := by
  simp only [gate67vartheta, iexp_one]; decide

/-- leg 1, extension: FINDING D-F2 — the D.06 table's `ϑ_{G2}(t) = Θ(f₃−t)` at the BOTTOM slot
`t = 0` reads the telescope at `s = f₃ = 5`, one step BEYOND FRAME-C's committed `s = 0…4` range,
so the committed battery does not cover the bottom slot.  The assembled formula extends it:
`ϑ_5 = 2^{⌊5/2⌋} = 4`, `Θ_5 = 4`. -/
example : gate67vartheta 5 = 4 := by simp only [gate67vartheta, iexp_one]; decide

/-- leg 1: the runner obligation `w^s = U(s)·ϑ_s` at `w = 3`, all five `s`. -/
example : ∀ s ∈ List.range 5,
    (3 : ZMod 5) ^ s = gate67U.getD s 0 * gate67vartheta s := by
  simp only [gate67vartheta, gate67U, iexp_one]; decide

/-- leg 1: the runner obligation `U(s) = Θ_s·w^s`, all five `s` — the B-law orientation. -/
example : ∀ s ∈ List.range 5,
    gate67U.getD s 0 = gate67theta s * (3 : ZMod 5) ^ s := by
  simp only [gate67theta, gate67thetaL, gate67U]; decide

/-- leg 1: **the orientation tooth, EXECUTED.**  Writing the B-law in the WRONG orientation (`ϑ`
where `Θ` belongs) fails at `s = 2`: `ϑ₂·3² = 2·4 = 3 ≠ 2 = U(2)`.  The sign error
`EFF.T1.45`/append #54 says no battery catches now HAS a battery. -/
example : gate67U.getD 2 0 ≠ gate67vartheta 2 * (3 : ZMod 5) ^ 2 := by
  simp only [gate67vartheta, gate67U, iexp_one]; decide

/-! ### Leg 2 — the CMP leg (`q_CMP = 2`, `N̂(k) = x^k`, `H₀ = 6`, `D = 3`) -/

/-- gate-local data (D.67): FRAME-C's `χ(k) = 2^{⌊k/2⌋}` (D.12's `chi` at the two exponent-pair
sections, residue via D.17). -/
def gate67chi (k : ℕ) : ZMod 5 := (2 : ZMod 5) ^ (k / 2)

/-- leg 2: **the non-character check** `χ(1)·χ(1) = 1 ≠ 2 = χ(2)` — D.12's "no character law for
`χ` is assumed" fence, EXECUTED.  The §8.4(1) character mutant dies here. -/
example : gate67chi 1 * gate67chi 1 ≠ gate67chi 2 := by decide

/-- leg 2: `δ = χ(2) = 2` and `χ(6) = 2³ = 3`. -/
example : gate67chi 2 = 2 ∧ gate67chi 6 = 3 := by decide

/-- gate-local data (D.67): the CMP leg's explicit `ρ̂` coefficients (`H₀ = 6`, `D = 3`). -/
def gate67rhoHat : List (ZMod 5) := [1, 2, 3, 4]

/-- gate-local data (D.67): `ρ_t = χ(H₀)·ρ̂_t·δ^{−t} = 3·ρ̂_t·2^{−t}` (D.40's coefficient leg),
with `δ^{−1} = 3` substituted per the D-D1 rider — the inverse is not spelled, it is the unit `3`
certified by `2·3 = 1` below. -/
def gate67rho (t : ℕ) : ZMod 5 :=
  gate67chi 6 * gate67rhoHat.getD t 0 * (3 : ZMod 5) ^ t

/-- leg 2: the comparison `ρ_t = 3·ρ̂_t·2^{−t}` evaluated — the coefficient form of
`R(Z) = 3·R̂(Z/2)` in `𝔽₅[Z]` (D.40). -/
example : (List.range 4).map (fun t => gate67rho t) = [3, 3, 1, 4] := by decide

/-- leg 2: `δ⁻¹ = 3` in `𝔽₅`, the substitution scalar of `R̂(Z/δ)` — stated multiplicatively
(defect D-D1: `ZMod.inv` does not kernel-reduce). -/
example : (2 : ZMod 5) * 3 = 1 := by decide

/-- gate-local data: `R(Z) = Σ_t ρ_t Z^t` at `D = 3`, the blueprint STATEMENT's `R` (the
re-signed SIGNATURE renders leg 2 coefficientwise; this is the same data in `𝔽₅[Z]`). -/
private noncomputable def gate67R : Polynomial (ZMod 5) :=
  ∑ t : Fin 4, Polynomial.C (gate67rho (t : ℕ)) * Polynomial.X ^ (t : ℕ)

/-- gate-local data: `R̂(Z) = Σ_t ρ̂_t Z^t` at `D = 3`. -/
private noncomputable def gate67RHat : Polynomial (ZMod 5) :=
  ∑ t : Fin 4, Polynomial.C (gate67rhoHat.getD (t : ℕ) 0) * Polynomial.X ^ (t : ℕ)

/-- leg 2, the polynomial form: `R(Z) = χ(H₀)·R̂(Z/δ) = 3·R̂(3Z)` in `𝔽₅[Z]` — the blueprint
STATEMENT's `R(Z) = 3·R̂(Z/2)` display, executed at this frame's explicit coefficients (`Z/δ` is
`Polynomial.comp` with `C δ⁻¹ * X`, and `δ⁻¹ = 3` is the unit certified just above).  This is the
SHAPE of D.40's `compData_cmp_poly` at FRAME-C's numbers; it is NOT an instantiation of that
theorem, which would need a realized arena — see the coverage record `(T3-JOINT-OPEN)`. -/
example : gate67R
    = Polynomial.C (gate67chi 6) * gate67RHat.comp (Polynomial.C (3 : ZMod 5) * Polynomial.X) := by
  simp only [gate67R, gate67RHat, Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [gate67rho, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.C_mul, mul_pow, Polynomial.C_pow]
  ring

/-! ### Leg 4 — D.06's ϑ FOUR-WAY ORIENTATION TABLE, EXECUTED at FRAME-C (`f₃ = 5`)

The table's four rows as arithmetic, at the one frame where every quantity is a concrete
`𝔽₅`-unit.  Append #54's trap ("a sign error no battery catches") gets its battery here: rows
1/2/3 are ONE object, row 4 is its RECIPROCAL at the reflected index, and the two are numerically
DISTINCT — so a silent swap is a failing `decide`. -/

/-- row 1 (GENTOW2's `ϑ(t)`) = rows 2/3 (`Θ(f−t)`), the reference. -/
def gate06varthetaG2 (f t : ℕ) : ZMod 5 := gate67theta (f - t)

/-- row 4 (GENTOW5-A1's `theta_t`) = T1's `ϑ_{i,t}` at argument `t`, NOT `f−t`. -/
def gate06A1theta (t : ℕ) : ZMod 5 := gate67vartheta t

/-- rows 2–3, as the involution `Θ_s·ϑ_s = 1` on `s = 0…5` (D.06/D.10 at this frame) — this is
what certifies that the committed `gate67thetaL` really is the inverse-orientation telescope. -/
example : ∀ s ∈ List.range 6, gate67theta s * gate67vartheta s = 1 := by
  simp only [gate67theta, gate67thetaL, gate67vartheta, iexp_one]; decide

/-- **the top-slot normalization anchor** `ϑ(f₃−1) = 1` (`EFF.GENTOW2.41`; both orientations
agree at `s ∈ {0,1}`). -/
example : gate06varthetaG2 5 4 = 1 ∧ gate67vartheta 1 = 1 ∧ gate67theta 1 = 1 := by
  simp only [gate06varthetaG2, gate67theta, gate67thetaL, gate67vartheta, iexp_one]; decide

/-- **row 4's RECIPROCAL relation** `ϑ(t) = vartheta_{f₃−t}⁻¹` at `λ = u₃`
(`EFF-GENTOW2.md:1072`) — the exact GENTOW2/GENTOW5-A1 pair append #54 names, stated
multiplicatively. -/
example : ∀ t ∈ List.range 5,
    gate06varthetaG2 5 t * gate06A1theta (5 - t) = 1 := by
  simp only [gate06varthetaG2, gate06A1theta, gate67theta, gate67thetaL, gate67vartheta,
    iexp_one]
  decide

/-- **MUTATION-KILLER (part 1): the orientations are numerically DISTINCT** — a silent swap of
row 1 for row 4 is caught (`t = 2`: row 1 gives `3`, row 4 gives `2`). -/
example : gate06varthetaG2 5 2 ≠ gate06A1theta 2 := by
  simp only [gate06varthetaG2, gate06A1theta, gate67theta, gate67thetaL, gate67vartheta,
    iexp_one]
  decide

/-- **MUTATION-KILLER (part 2): the reflection `t ↦ f₃−t` is not the identity either**,
`ϑ_{G2}(t) ≠ Θ(t)`.  ⚠ FINDING D-F3: scored at `t = 1` AND `t = 4`, NOT at `t = 2`/`t = 3` —
FRAME-C has `ϑ₂ = ϑ₃ = 2` (both floors `⌊s/2⌋` equal `1`), so an index-shift mutant SURVIVES at
the middle slots, and an agent scoring only the middle of the table would miss it. -/
example : gate06varthetaG2 5 1 ≠ gate67theta 1 ∧ gate06varthetaG2 5 4 ≠ gate67theta 4 := by
  simp only [gate06varthetaG2, gate67theta, gate67thetaL]; decide

/-- FINDING D-F3's witness, executed so that no later reader re-scores the leg above at a middle
slot: FRAME-C really does have `Θ₂ = Θ₃`, the slots where the index-shift mutant survives. -/
example : gate67theta 2 = gate67theta 3 := by
  simp only [gate67theta, gate67thetaL]; decide

end FrameC

/-! ## Axiom footprint

The file signs no theorem, so there is no capstone-facing name to print; what the census can
check here is that the gate's DATA layer is Lean-core-clean (D.68(iv)'s discipline applied
locally). The executed `example`s are anonymous by construction and carry no footprint of their
own — their content is the fact that they elaborate at all. -/

section AxCheck

#print axioms gate67vartheta
#print axioms gate67thetaL
#print axioms gate67theta
#print axioms gate67U
#print axioms gate67chi
#print axioms gate67rhoHat
#print axioms gate67rho
#print axioms gate67R
#print axioms gate67RHat
#print axioms gate06varthetaG2
#print axioms gate06A1theta

end AxCheck
