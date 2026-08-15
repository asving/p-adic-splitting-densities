/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Uniformity.ChapH.H95
import Uniformity.Density.DensityAPI
import Uniformity.Density.Statement

/-!
# Uniformity.ChapH.H98 — THE CAPSTONE, FROM THE PACKAGE (`GENIND.B` **Step 5** + `W-12.D`)

**Chapter H, NODE H.98** (`blueprint/CHAP-H_general_induction.md` §13). The chapter's assembly
node. Two signed conditionals:

* `drainage_of_package : (∀ n, InductionPackage n) → ∀ n, DrainageAt n` — the package's `(A2)`
  member (the `RateSpecies` bound on the undecided proportion) delivers drainage at every degree;
* `uniformity_of_package : UniformityStatementDecided → (∀ n, InductionPackage n) →
  UniformityStatement` — certified densities plus the package give THE capstone target.

DEPENDS: H.65 (`Induction.RateSpecies`), H.95 (`InductionPackage`) · landed
`Uniformity.Density.UniformityStatement`, `UniformityStatementDecided`,
`UniformityStatement.ofDecided`, `DrainageAt`, `UndecidedVanishes`, `gapSeq_le_undecidedSeq`,
`undecidedSeq`, `two_le_residueCard`, and `DensityAPI`'s `drainage_of_undecided_comp` (CN-11).

**On H.96 (`package_two`).** The blueprint's DEPENDS line names it, but it is a **citation, not a
proof dependency**: nothing below consumes `P(2)`. It is what makes `hp` non-vacuous at `n = 2`,
and it is censused next door at H.99. This file therefore does not import `ChapH.H96` (and so
does not drag chapter G into the assembly node's import graph); the non-vacuity claim is made at
the gate, where it is checkable.

SOURCE: `EFF.GENIND.60` (`§S6` Step 5, verbatim: *"By W12-S2.1 … *Step 5 (fire W-12.D).* `P(n)`'s
`(A0)+(A1)+(A2)` are W-12.D's hypotheses at degree `n`: THEOREM W-12.D (PROVED, @ pin) yields one
`R_τ(q) ∈ ℚ(q)` per splitting type of degree `n`, = the Haar density, same expression at every
prime power and characteristic, `Σ_τ R_τ = 1`. Strong induction over `n` completes THEOREM
GENIND.B. ∎"*); `EFF.GENIND.15` (the consequence clause and **its `n ≥ 8` widening**, honesty
item H-7).

## ⚠ WHAT THIS NODE IS NOT (blueprint, verbatim)

> It is **not** `THEOREM GENIND.B`. `GENIND.B` is the *reduction* `(IH) + [GENIND-H(n)] ⟹ P(n)`,
> whose composite-stage half is the whole open surface (honesty item H-1). This node is **Step 5
> only**: `P(n)` for all `n` ⟹ the capstone. The reduction's inductive step has **no node** in
> chapter H, for the reason H-1 gives: its content is the event grammar, the two transports and
> the stage clauses, i.e. geometry plus `StageInterface`'s fields. **A node claiming `GENIND.B`
> must be returned.** What chapter H delivers is: the two base cases (H.96, H.97), the rate
> calculus the inductive step consumes (§10), and Step 5 (this node) — the induction's *scaffold*
> with the geometric step left visible as the hypothesis `hp`.

**⚠ AND THE `n ≥ 8` CONDITIONALITY IS VISIBLE IN `hp`, NOT HIDDEN.** `EFF.GENIND.176`: at `n ≤ 7`
the conditionality is `[GENIND-H(n)]`; at `n ≥ 8` it is `[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] +
[GENHN-TOW-1]`. Because `hp : ∀ n, InductionPackage n` is a *hypothesis*, the widening costs this
node nothing and is recorded honestly: the reader must supply `InductionPackage n` at every `n`,
and the corpus's own statement of what that costs is §16's disposition table.

**⚠ AND `(A0)` IS VISIBLE TOO.** `InductionPackage` (H.95) carries the menu and the rate, not the
σ-decision at leaves; the σ-decision enters here as the *separate* hypothesis
`hdec : UniformityStatementDecided`. Neither conditional hides a decision inside a `def`.

## The proof, as transcribed

**`drainage_of_package`.** Fix `n` and `obtain ⟨K, B, c, hK, h⟩ := hp n`; the constants sit
outside the `∀ O`, which is what "a rate uniform in `O`" means. Fix `O` and `σ`, and take the rate
member `hrate : RateSpecies (residueCard O) K B c (undecidedSeq O n)`, i.e.
`undecidedSeq O n M ≤ K · M^B · (q^(M−c))⁻¹` for `M ≥ 1`.

The one analytic step is the private `tendsto_rateBound_zero`: a polynomial coefficient times a
geometric deficit tends to `0`. It is proved by squeezing the signed bound between `0` and the
honest polynomial-times-geometric `(K·q^c) · (M^B · (q⁻¹)^M)`, using

* `(q^(M−c))⁻¹ ≤ q^c · (q⁻¹)^M` **at every `M`** — cross-multiplying, this is
  `q^M ≤ q^(c + (M−c))`, and `M ≤ c + (M − c)` holds in `ℕ` *including* when `M < c`, where the
  truncated subtraction gives `c + 0 = c > M`. So no `M ≥ c` side condition is needed anywhere;
* mathlib's `tendsto_pow_const_mul_const_pow_of_lt_one` at `r = (q:ℝ)⁻¹ < 1` (`q ≥ 2` by
  `two_le_residueCard`), scaled by the constant `K·q^c`.

Then `squeeze_zero'` (with `undecidedSeq ≥ 0` everywhere and the rate valid eventually, from
`M ≥ 1`) gives `undecidedSeq O n M → 0`, and CN-11's `drainage_of_undecided_comp` at `φ = id`
turns that into `UndecidedVanishes O n σ` for **every** `σ` — that lemma is where
`gapSeq_le_undecidedSeq` and the antitone-infimum argument live, replayed from the landed `n = 2`
`drainage_two`.

**`uniformity_of_package`.** One application: `UniformityStatement.ofDecided` at the landed
argument order `(hd : ∀ n, DrainageAt n) (h : UniformityStatementDecided)`.

**TEETH.** `EFF.GENIND.60`: *"NONE — a theorem application"* → carried unchanged; the node's value
is that the application is machine-checked against `leanfinal`'s landed
`UniformityStatement.ofDecided` rather than cited to `W-12.D` (honesty item H-12).

## Status

Sorry-free, axiom-free (Lean core only). Both statements are CONDITIONAL, and both hypotheses are
explicit: `hp` (the package at every degree — the open surface, honesty item H-1) and `hdec` (the
σ-decision census — `(A0)`, honesty item H-5(4)).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open Filter Topology IsLocalRing

/-- The analytic step behind `drainage_of_package`: the `(A2-RATE)` right-hand side — a polynomial
coefficient `K·M^B` against an exponential deficit `(q^(M−c))⁻¹` with `q ≥ 2` — tends to `0`.

The truncated subtraction `M − c` is handled without a side condition: `(q^(M−c))⁻¹ ≤ q^c·(q⁻¹)^M`
holds at every `M`, because `M ≤ c + (M − c)` in `ℕ` even when `M < c`. Private: H.98's signed
contract is the two theorems below. -/
private theorem tendsto_rateBound_zero {q : ℕ} (hq : 2 ≤ q) {K : ℝ} (hK : 0 ≤ K) (B c : ℕ) :
    Tendsto (fun M : ℕ => K * (M : ℝ) ^ B * ((q : ℝ) ^ (M - c))⁻¹) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have h : (0 : ℕ) < q := by omega
    exact_mod_cast h
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h : (1 : ℕ) ≤ q := by omega
    exact_mod_cast h
  have hlt1 : (q : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    have h : (1 : ℕ) < q := by omega
    exact_mod_cast h
  have hgeom : Tendsto (fun M : ℕ => (K * (q : ℝ) ^ c) * ((M : ℝ) ^ B * ((q : ℝ)⁻¹) ^ M))
      atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_const_mul_const_pow_of_lt_one B (inv_nonneg.2 hq0.le) hlt1).const_mul
        (K * (q : ℝ) ^ c)
  have hbound : ∀ M : ℕ, ((q : ℝ) ^ (M - c))⁻¹ ≤ (q : ℝ) ^ c * ((q : ℝ)⁻¹) ^ M := by
    intro M
    rw [inv_pow, ← one_div, ← div_eq_mul_inv,
      div_le_div_iff₀ (pow_pos hq0 _) (pow_pos hq0 _), one_mul, ← pow_add]
    exact pow_le_pow_right₀ hq1 (by omega)
  refine squeeze_zero (fun M => ?_) (fun M => ?_) hgeom
  · exact mul_nonneg (mul_nonneg hK (pow_nonneg (Nat.cast_nonneg M) B))
      (inv_nonneg.2 (pow_nonneg hq0.le _))
  · calc K * (M : ℝ) ^ B * ((q : ℝ) ^ (M - c))⁻¹
        ≤ K * (M : ℝ) ^ B * ((q : ℝ) ^ c * ((q : ℝ)⁻¹) ^ M) :=
          mul_le_mul_of_nonneg_left (hbound M)
            (mul_nonneg hK (pow_nonneg (Nat.cast_nonneg M) B))
      _ = (K * (q : ℝ) ^ c) * ((M : ℝ) ^ B * ((q : ℝ)⁻¹) ^ M) := by ring

/-- **NODE H.98, first conditional — `GENIND.B` Step 5.** The package's `(A2)` member delivers
drainage at every degree: if `InductionPackage n` holds for every `n` (with rate constants
uniform in `O`, as `InductionPackage` demands), then `DrainageAt n` for every `n`.

This is **not** `THEOREM GENIND.B` — see the module docstring's fence. `hp` is a hypothesis; the
reduction that would supply it is the chapter's open surface. -/
theorem drainage_of_package (hp : ∀ n, InductionPackage n) : ∀ n, DrainageAt n := by
  intro n
  obtain ⟨K, B, c, hK, h⟩ := hp n
  intro O _ _ _ _ _ σ
  obtain ⟨-, hrate⟩ := h O
  have hlim : Tendsto (fun M : ℕ => undecidedSeq O n M) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_rateBound_zero (two_le_residueCard O) hK B c)
    · filter_upwards with M
      exact div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le
    · filter_upwards [eventually_ge_atTop 1] with M hM
      exact hrate M hM
  exact drainage_of_undecided_comp (φ := fun M => M) tendsto_id hlim σ

/-- **NODE H.98, second conditional — the capstone, assembled.** Certified densities
(`hdec`, the `(A0)` census) plus the package at every degree (`hp`) give `UniformityStatement`:
one rational function in `q` per `(n, σ)`, valid at every complete DVR with finite residue field,
over THE density `genuineDensity`.

`GENIND.B` Step 5's *"fire W-12.D"* is exactly this application of `leanfinal`'s landed
`UniformityStatement.ofDecided` — machine-checked here rather than cited. -/
theorem uniformity_of_package (hdec : UniformityStatementDecided)
    (hp : ∀ n, InductionPackage n) : UniformityStatement :=
  UniformityStatement.ofDecided (drainage_of_package hp) hdec

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.drainage_of_package
#print axioms Uniformity.Density.uniformity_of_package

end AxCheck
