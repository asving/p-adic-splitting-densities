/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Basic

/-!
# Uniformity.ChapC.C31 — the jump floor, the first bite, the jump drop

**Chapter C, NODE C.31** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §5, the descent
grammar; the A-C.1 amendment set governs, and the **D21 RE-SIGN** of 2026-08-16 is in force).
**ENV-C5** — the arithmetic arena: no `O`, no polygons, `ℕ` only. Three signed declarations.

The numeric floors that make the descent terminate. At a level jump on a side `(u, ℓ)` whose
residual carries the irreducible factor `r` with multiplicity `m_r ≥ 2` and `d_r = deg r`:

* `jump_floor` — **(i)+(ii)** the side length `L_λ ≥ m_r·(ℓ d_r) ≥ 2·2 = 4`, and since side
  lengths do not exceed the polygon's abscissa range, `μ ≥ 4` too;
* `first_bite` — **(iii)** at a composite frame (`2 ≤ D′`) the ambient degree `n = D′μ` is at
  least `8`: no jump can happen below degree 8;
* `jump_drop` — **(iv)** one jump at least halves the multiplicity: `2·μ₂ ≤ μ`, from the audited
  chain `μ₂ = deg f_S/D″ ≤ deg R_λ/d_r ≤ μ/(ℓd_r)` with `ℓd_r ≥ 2` at the last step.

`jump_drop` is what C.32 iterates into the jump-count bound `2^{J+2} ≤ 2μ`; `jump_floor`'s
`4 ≤ a j` is C.32's `hfloor`.

## Only the numerals appear (the ENV-C5 ruling, as at C.30)

Nothing here mentions a side, a residual or a block factor: `mr`, `ℓ`, `dr`, `L`, `μ`, `μ₂`,
`dfS` arrive as numerals already extracted by the consuming node. That is what lets level 1 and
level 2 instantiate the same three lemmas, and it is why the DEPENDS edge to C.33/C.35 is a
*forward supplier* edge (they produce `deg f_S ≤ D′L_λ` and `L_λ ≤ μ` as facts about real
histories) rather than an import: **this file imports only `Mathlib.Data.Nat.Basic`**, and
C.33/C.35 need not be landed for it to fire.

## ⚠ D21 — the third clause was FALSE as originally signed (re-signed; record kept)

As first committed, `jump_drop`'s third hypothesis read `hL : ℓ * dr * 2 ≤ 2 * μ` — an UPPER
bound `ℓd_r ≤ μ` where the argument needs the LOWER bound — and the clause was machine-refuted
at the stub gate: `(D, ℓ, d_r, μ, μ₂, deg f_S) = (1,1,1,1,1,1)` satisfies every hypothesis and
`2·1 ≤ 1` is false; **168 counterexamples** on `D, ℓ, d_r ∈ [1,4] × μ, μ₂ ∈ [0,12]` (the
executable refutation record is preserved verbatim in `leanspec/Leanspec/ChapC.lean`'s numeric
section, `jumpDropAsSigned`/`jumpDropCounterCount`). A-C.1 re-signed it with the source's own
jump hypothesis `hjump : 2 ≤ ℓ * dr` (`EFF.HE6R1.10`, verbatim: *"… ≤ μ/(ℓd_r), using LEMMA
HE6-3(b) … for the middle step and `ℓd_r ≥ 2` for the last"*), with zero counterexamples on the
larger box. **This file lands the RE-SIGNED form**, which is the twin's frozen type, and the
proof below is the two-line one the repair note predicted.

## Divergences from the blueprint text (GC-6.5; none is a new node)

* **`hℓ` and `hd` are bound and not consumed in `jump_drop`.** Positivity of `ℓ` and `d_r` is
  implied by `hjump : 2 ≤ ℓ * dr` (a product `≥ 2` has both factors nonzero), and the proof needs
  only `hjump` plus `hD`. The binders are kept byte-for-byte: the signature is signed, and the
  statement-fence forbids trimming a hypothesis list even when the trim would be sound. Likewise
  D17's finding on `jump_floor` (recorded at the gate: "four unused hypotheses and one unused
  binder") is **not** acted on — here all four hypotheses are in fact consumed (`hm`+`hjump` give
  `4 ≤ mr·(ℓd_r)`, then `hL`, then `hLμ`), and `dr` occurs only inside the product, exactly as
  the gate described.
* **`hfS`'s `μ / ℓ` is ℕ-division** — the gate's D17 flag: at `ℓ ∤ μ` this hypothesis is strictly
  WEAKER than the intended `deg f_S ≤ D′·L_λ`, so the landed theorem is correspondingly
  *stronger* (it concludes from less). The proof consumes it through `ℓ·(μ/ℓ) ≤ μ`
  (`Nat.div_mul_le_self`), which is where the truncation is absorbed; no step assumes `ℓ ∣ μ`.
* **Clause (iii)'s depth-3 half is NOT in the signature.** The blueprint's (iii) also records
  "depth-3 first bites at `n ≥ 16`" (iterate (iv) once: a second jump needs `μ₂ ≥ 4`, so `μ ≥ 8`,
  `n ≥ 16`). The signed `first_bite` states only `8 ≤ n`; the depth-3 numeral is a two-step
  composition of `jump_drop` with `first_bite` at the consuming node, and is not landed here
  because no signed declaration asks for it.

**DEPENDS.** C.30 (the trichotomy whose case (c) supplies `hm`/`hjump`) · C.33/C.35 (forward
suppliers of `deg f_S ≤ D′L_λ` and `L_λ ≤ μ`; not imported — see above) — by committed node ID
(GC-13(b)). Mathlib: `Nat.mul_le_mul`, `Nat.div_mul_le_self`, `Nat.le_of_mul_le_mul_left`.

**PROOF.** (i)/(ii): `2·2 ≤ mr·(ℓd_r) ≤ L ≤ μ`. (iii): `2·4 ≤ D·μ`. (iv): from `hμ₂` and `hfS`,
`μ₂·(D ℓ d_r) = deg f_S ≤ D·(ℓ·(μ/ℓ)) ≤ D·μ`; the left side dominates `D·(2μ₂)` by `hjump`, and
`D > 0` cancels.

**SOURCE.** `EFF.HE6R1.09`/`.10` (the displays and the compile-time audit *"`L_λ = ℓ·deg R_λ ≥
ℓ·m·d_r = m(ℓd_r) ≥ 4` ✓ … `μ₂ = deg f_S/D″ ≤ … ≤ μ/(ℓd_r)` ✓ every step exact"*);
`EFF.HE6.19` (the first-bite audit `n = D′μ ≥ 2·4 = 8`); `EFF.HE6.20` items 1–2;
`EFF.HE6R1.11` (both widened-box branches supply `ℓd_r ≥ 2` — why `hjump` is available at every
jump, the D21 repair's justification).

**TEETH.** `EFF.HE6.20`'s bite-frame numbers (`n = 8, μ = 4, D′ = 2, ℓ = 2, d = 2`, polygon
`(0,2u)–(4,0)`) → **Lean theorem instances** (the three `example`s below, at the source's own
numerals) plus the §13 regression rows; the D21 counterexample box stays an executable
`#guard` in the twin's numeric section (a Lean theorem cannot state "168 counterexamples").

**ENVIRONMENT.** ENV-C5.

## Status

Sorry-free. `#print axioms`: `jump_floor` and `first_bite` depend on no axioms at all;
`jump_drop` depends on `[propext]` (the two `simp` normalizations of the product) — Lean core
only, in every case.
-/

namespace Uniformity.Density.Tower

/-- **C.31 (i)+(ii) — the jump floor.** At a jump (`m_r ≥ 2`, `ℓd_r ≥ 2`) the side length is at
least `4`, and so is the polygon's multiplicity `μ` that bounds it. -/
theorem jump_floor (mr ℓ dr L μ : ℕ) (hm : 2 ≤ mr) (hjump : 2 ≤ ℓ * dr)
    (hL : mr * (ℓ * dr) ≤ L) (hLμ : L ≤ μ) : 4 ≤ L ∧ 4 ≤ μ := by
  have h4 : 4 ≤ mr * (ℓ * dr) := by simpa using Nat.mul_le_mul hm hjump
  have hL4 : 4 ≤ L := le_trans h4 hL
  exact ⟨hL4, le_trans hL4 hLμ⟩

/-- **C.31 (iii) — the first bite.** At a composite frame (`2 ≤ D′`) a jump needs ambient degree
at least `8`: `n = D′·μ ≥ 2·4`. -/
theorem first_bite (D μ n : ℕ) (hD : 2 ≤ D) (hμ : 4 ≤ μ) (hn : n = D * μ) : 8 ≤ n := by
  subst hn
  simpa using Nat.mul_le_mul hD hμ

set_option linter.unusedVariables false in
/-- **C.31 (iv) — the one-step multiplicity drop** (D21 re-signed form: the hypothesis is the
LOWER bound `2 ≤ ℓ·d_r`, the source's own). From `μ₂·(D′ℓd_r) = deg f_S ≤ D′·(ℓ·⌊μ/ℓ⌋) ≤ D′μ`
and `ℓd_r ≥ 2`: one jump at least halves the multiplicity, `2μ₂ ≤ μ`. `hℓ`/`hd` are bound by the
signed signature and not consumed (`hjump` implies both) — see the module docstring. -/
theorem jump_drop (D ℓ dr μ μ₂ dfS : ℕ) (hD : 0 < D) (hℓ : 0 < ℓ) (hd : 0 < dr)
    (hjump : 2 ≤ ℓ * dr)
    (hμ₂ : μ₂ * (D * ℓ * dr) = dfS) (hfS : dfS ≤ D * (ℓ * (μ / ℓ))) : 2 * μ₂ ≤ μ := by
  -- the ℕ-division in `hfS` is absorbed here, and nowhere is `ℓ ∣ μ` assumed
  have hdiv : ℓ * (μ / ℓ) ≤ μ := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self μ ℓ
  have h1 : dfS ≤ D * μ := le_trans hfS (Nat.mul_le_mul_left D hdiv)
  have h2 : D * (2 * μ₂) ≤ μ₂ * (D * ℓ * dr) := by
    have hstep : μ₂ * D * 2 ≤ μ₂ * D * (ℓ * dr) := Nat.mul_le_mul_left (μ₂ * D) hjump
    have e1 : D * (2 * μ₂) = μ₂ * D * 2 := by
      simp [Nat.mul_comm, Nat.mul_assoc]
    have e2 : μ₂ * D * (ℓ * dr) = μ₂ * (D * ℓ * dr) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    rw [e1, ← e2]
    exact hstep
  rw [hμ₂] at h2
  exact Nat.le_of_mul_le_mul_left (le_trans h2 h1) hD

/-! ### TEETH — `EFF.HE6.20`'s bite frame, at the source's own numerals

`n = 8`, `μ = 4`, `D′ = 2`, `ℓ = 2`, `d_r = 2`, `m_r = 2` (side length `L = 8`): the floor fires,
the first bite fires, and the drop forces `μ₂ ≤ 2` — a second jump would need `μ₂ ≥ 4`, so the
bite frame admits exactly one. -/

example : 4 ≤ 8 ∧ 4 ≤ 8 := jump_floor 2 2 2 8 8 (by decide) (by decide) (by decide)
  (by decide)

example : 8 ≤ 8 := first_bite 2 4 8 (by decide) (by decide) (by decide)

-- `D″ = D′ℓd_r = 8`, and a block of degree `deg f_S = 8` is `μ₂ = 1` copies of it
example : 2 * 1 ≤ 4 :=
  jump_drop 2 2 2 4 1 8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.jump_floor
#print axioms Uniformity.Density.Tower.first_bite
#print axioms Uniformity.Density.Tower.jump_drop

end AxCheck
