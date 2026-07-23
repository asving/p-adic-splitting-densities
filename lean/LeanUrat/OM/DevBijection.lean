/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ChainMenu
import LeanUrat.OM.Development

/-!
# DevBijection — Wave W8a: the deg-φ = 2 development bijection + the Case-E stratum count

**Provenance.** `notes/WILD_WAVE8_BLUEPRINT_2026-07-23.md` §2-W8a, ground truth §1:
**Lemma D1m** (unitriangular development — the four explicit coefficient formulas, machine-checked
over 200 random instances AND independently re-derived), **Corollary D1m-count** (exact cylinder
transport: an affine map with unitriangular linear part and ℤ[s,t]-coefficients induces a
bijection of `(ℤ/p^N)⁴`, so development-digit conditions count EXACTLY their nominal cylinder
volume), and **Corollary D1m-CaseE** (the Case-E stratum ledger, `N ≥ 2` REQUIRED — at `N = 1`
the height-1 digit is unavailable).

## The mathematics

For monic `φ = x² + sx + t` and monic quartic `f = x⁴ + c₃x³ + c₂x² + c₁x + c₀`, the φ-adic
development is the unique `f = φ² + a₁φ + a₀` with `deg a₁, deg a₀ ≤ 1`. Writing
`a₁ = a₁₁x + a₁₀`, `a₀ = a₀₁x + a₀₀` (blueprint §1, Lemma D1m):

  a₁₁ = c₃ − 2s
  a₁₀ = c₂ − s·c₃ + (s² − 2t)
  a₀₁ = c₁ − s·c₂ + (s² − t)·c₃ + (2st − s³)
  a₀₀ = c₀ − t·c₂ + st·c₃ + (t² − s²t)

This module delivers, purely additively (general prime `p`):

* **A. The box equiv** `devEquiv p N s t : fourBox p N ≃ fourBox p N` — the displayed formulas
  as a bijection of `(ZMod (p^N))⁴` (4-tuples grouped `(a₁-pair, a₀-pair)`), parametrized by
  the `ZMod (p^N)`-images of `s, t`; inverse `devInv` by back-substitution, Equiv laws by `ring`.
* **B. The genuine division identity** `dev_division` / `dev_division_padic`: over any
  commutative ring (hence over `ℤ_[p]`), `f = φ² + a₁·φ + a₀` with the displayed coefficients —
  proved by `ring` after pushing `C` through; `a₁, a₀` are linear-form literals
  (`natDegree_linPair_le`).
* **C. Box commutation** `devMap_toZModPow`: `toZModPow N` of the four genuine development
  coefficients = `devEquiv` applied to the `toZModPow` of `(c₃, c₂, c₁, c₀)` — the formulas are
  ℤ[s,t]-polynomial, so they commute with any ring hom (`fourMap_devMap`).
* **D. The Case-E cylinder and its counts** (`N ≥ 2`): `CaseECell` = both `a₁`-coordinates
  `≡ 0 (mod p)`, both `a₀`-coordinates `≡ 0 (mod p)`, height-1 digit pair of `a₀` `≠ (0,0)`
  (i.e. `v_Gauss(a₁) ≥ 1`, `v_Gauss(a₀) = 1` exact — blueprint §1 remark 1: no F_Q-field
  structure is needed for the COUNT). `card_caseECell` = `(p²−1)·p^{2N−4}·p^{2(N−1)}`;
  **`card_caseE_original`** (THE point, Corollary D1m-count): the ORIGINAL-coordinate fiber
  `{c : devEquiv c ∈ CaseECell}` has the SAME count, by transport along the equiv;
  `caseE_mass` = `(Q−1)·Q^{−3}` at `Q = p²`, i.e. `(p²−1)/p⁶` of the `p^{4N}` box.
* **E. Gates**: `gate_caseE_p2_N2` (count `12` of `256` at `p = 2, N = 2`, original-coordinate
  fiber of the `s = t = 1` instance, by kernel `decide` — the machine-verified Case-E gate
  value), `gate_caseE_p3_N2` (count `72` at `p = 3, N = 2`), `gate_caseE_mass_p2` (`3/64`).
* The `s = t = 1` Case-E instance objects for phase 2: `caseEPhi = X² + X + 1` over `ℤ_[2]`
  (`caseEPhi_eq`, `caseEPhi_monic`, `caseEPhi_natDegree`), `caseEDevEquiv`,
  `caseEDevEquiv_toZModPow`.

## `OM/Development.lean` consumability

`Development.lean` formalizes the φ-adic development in `%ₘ`/`/ₘ` vocabulary (`develop`,
`developEquiv`); extracting the EXPLICIT 4-variable formulas from its division recursion is
awkward, so the identity is proved self-contained (`dev_division`, a `ring` identity) — per the
blueprint's design note. Compatibility is then PROVED, not remarked: `develop_eq_devMap` shows
via `Development.develop_unique` that the explicit formulas ARE the `develop`-digits of
`f − φ²` — exactly what `Development.developEquiv p N 2 2`'s forward map reads on a monic
quartic. Nothing in `Development.lean` was modified.

## External anchors (blueprint §0/§1 remark 4)

Case E PASSED 2026-07-23 (`verification/case_e_gate.py`, commit ad5c02e): stratum count `3/64`
EXACT at `p = 2, N = 2, 3, 4` by census in ORIGINAL coordinates (12 of 256 at `N = 2` — the
`decide` gate below reproduces this in-kernel), and 36/36 sampled type certificates `(e,f) =
(2,2)`. The census exercises precisely the Lemma-D1m mechanism this module formalizes.

## HONEST SCOPE (blueprint §1 remark 3 — read before consuming)

This module makes **NO type/leaf/faithfulness claim**: it is the **D1-MARGINAL counting
mechanism only** — the bijection and the stratum count for ONE deg-φ = 2 order-1 read at a
FIXED `(s, t)`. Keying/faithfulness (the `(2,2)` leaf master, menu re-scope) is phase 2 (W8b);
**JOINT-D1 at depth ≥ 1 remains OPEN** (reads at depth ≥ 1 recenter/rescale inside the previous
read's fiber; the joint ledger is not proved here and must NOT be cited from this module).

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck` at bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.DevBijection

open Polynomial
open LeanUrat.OM LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox LeanUrat.OM.ChainMenu

/-! ## 1. The development map over a general commutative ring (Lemma D1m, the four formulas)

The coefficient 4-tuples are grouped `(a₁-pair, a₀-pair)` = `((a₁₁, a₁₀), (a₀₁, a₀₀))` on the
development side and `((c₃, c₂), (c₁, c₀))` on the original side — descending degree within
each pair, matching the display above. -/

/-- A coefficient 4-tuple, grouped in two pairs: `((·₁₁, ·₁₀), (·₀₁, ·₀₀))` development-side,
`((c₃, c₂), (c₁, c₀))` original-side. -/
abbrev fourTuple (R : Type*) := (R × R) × (R × R)

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The development map** (blueprint §1 Lemma D1m): `(c₃, c₂, c₁, c₀) ↦ (a₁₁, a₁₀, a₀₁, a₀₀)`
by the four displayed formulas — an affine map over `ℤ[s,t]` with lower-unitriangular linear
part. -/
def devMap (s t : R) (c : fourTuple R) : fourTuple R :=
  ((c.1.1 - 2 * s,
    c.1.2 - s * c.1.1 + (s ^ 2 - 2 * t)),
   (c.2.1 - s * c.1.2 + (s ^ 2 - t) * c.1.1 + (2 * s * t - s ^ 3),
    c.2.2 - t * c.1.2 + s * t * c.1.1 + (t ^ 2 - s ^ 2 * t)))

/-- **The inverse by back-substitution** (solve `c₃` from the first line and substitute up) —
equivalently, REASSEMBLY: these are the coefficients of `φ² + a₁φ + a₀`. -/
def devInv (s t : R) (a : fourTuple R) : fourTuple R :=
  ((a.1.1 + 2 * s,
    a.1.2 + s * a.1.1 + (s ^ 2 + 2 * t)),
   (a.2.1 + s * a.1.2 + t * a.1.1 + 2 * s * t,
    a.2.2 + t * a.1.2 + t ^ 2))

/-- Back-substitution recovers the original coefficients (`ring`, coordinatewise). -/
theorem devInv_devMap (s t : R) (c : fourTuple R) : devInv s t (devMap s t c) = c := by
  obtain ⟨⟨c₃, c₂⟩, c₁, c₀⟩ := c
  simp only [devMap, devInv, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Development of the reassembly is the identity (`ring`, coordinatewise). -/
theorem devMap_devInv (s t : R) (a : fourTuple R) : devMap s t (devInv s t a) = a := by
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  simp only [devMap, devInv, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Apply a ring hom to all four coordinates. -/
def fourMap (g : R →+* S) (c : fourTuple R) : fourTuple S :=
  ((g c.1.1, g c.1.2), (g c.2.1, g c.2.2))

/-- **The development map commutes with every ring hom** (the formulas are ℤ[s,t]-polynomial) —
the general form of the box commutation (Corollary D1m-count's "commutes with reduction
mod `p^N`"). -/
theorem fourMap_devMap (g : R →+* S) (s t : R) (c : fourTuple R) :
    fourMap g (devMap s t c) = devMap (g s) (g t) (fourMap g c) := by
  obtain ⟨⟨c₃, c₂⟩, c₁, c₀⟩ := c
  simp only [devMap, fourMap, map_sub, map_add, map_mul, map_pow, map_ofNat]

end Ring

/-! ## 2. The box equiv (deliverable A) and the box commutation (deliverable C) -/

section Box

variable (p : ℕ) [hp : Fact p.Prime]

/-- The level-`N` coefficient box: 4-tuples over `ZMod (p^N)`, grouped
`(a₁-pair, a₀-pair)` / `((c₃, c₂), (c₁, c₀))`. -/
abbrev fourBox (N : ℕ) : Type := fourTuple (ZMod (p ^ N))

/-- **THE DEVELOPMENT BOX EQUIV** (Corollary D1m-count): at every level `N`, the development
map at the `ZMod (p^N)`-images of `s, t` is a bijection of the coefficient box — unitriangular
linear part, explicit inverse by back-substitution. -/
def devEquiv (N : ℕ) (s t : ZMod (p ^ N)) : fourBox p N ≃ fourBox p N where
  toFun := devMap s t
  invFun := devInv s t
  left_inv := devInv_devMap s t
  right_inv := devMap_devInv s t

theorem devEquiv_apply (N : ℕ) (s t : ZMod (p ^ N)) (c : fourBox p N) :
    devEquiv p N s t c = devMap s t c := rfl

theorem devEquiv_symm_apply (N : ℕ) (s t : ZMod (p ^ N)) (a : fourBox p N) :
    (devEquiv p N s t).symm a = devInv s t a := rfl

/-- **Box commutation (deliverable C)**: `toZModPow N` of the four GENUINE (ℤ_[p]-level)
development coefficients = `devEquiv` at the `toZModPow`-images of `s, t`, applied to the
`toZModPow` of `(c₃, c₂, c₁, c₀)`. (That `devMap s t c` IS the genuine development of the
quartic is `dev_division`/`develop_eq_devMap` below.) -/
theorem devMap_toZModPow (N : ℕ) (s t : ℤ_[p]) (c : fourTuple ℤ_[p]) :
    fourMap (PadicInt.toZModPow N) (devMap s t c)
      = devEquiv p N (PadicInt.toZModPow N s) (PadicInt.toZModPow N t)
          (fourMap (PadicInt.toZModPow N) c) :=
  fourMap_devMap (PadicInt.toZModPow N) s t c

end Box

/-! ## 3. The genuine division identity (deliverable B) and `Development.lean` compatibility -/

noncomputable section Poly

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monic quadratic key `φ = X² + C s·X + C t`. -/
def keyPoly (s t : R) : R[X] := X ^ 2 + C s * X + C t

/-- The monic quartic with coefficient tuple `((c₃, c₂), (c₁, c₀))`. -/
def quartic (c : fourTuple R) : R[X] :=
  X ^ 4 + C c.1.1 * X ^ 3 + C c.1.2 * X ^ 2 + C c.2.1 * X + C c.2.2

/-- The linear form `C a₁·X + C a₀` attached to a coefficient pair — the development digits
`a₁, a₀` as polynomials. -/
def linPair (a : R × R) : R[X] := C a.1 * X + C a.2

/-- The development digits are (at most) linear: `natDegree ≤ 1`. -/
theorem natDegree_linPair_le (a : R × R) : (linPair a).natDegree ≤ 1 :=
  natDegree_linear_le

/-- The development digits are (at most) linear: `degree ≤ 1`. -/
theorem degree_linPair_le (a : R × R) : (linPair a).degree ≤ 1 :=
  degree_linear_le

theorem keyPoly_monic (s t : R) : (keyPoly s t).Monic := by
  have h : keyPoly s t = X ^ 2 + (C s * X + C t) := by rw [keyPoly, add_assoc]
  rw [h]
  exact monic_X_pow_add (lt_of_le_of_lt degree_linear_le (by exact_mod_cast one_lt_two))

theorem keyPoly_natDegree [Nontrivial R] (s t : R) : (keyPoly s t).natDegree = 2 := by
  have hdlt : (C s * X + C t).degree < (X ^ 2 : R[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast one_lt_two)
  have h : keyPoly s t = X ^ 2 + (C s * X + C t) := by rw [keyPoly, add_assoc]
  rw [h]
  exact natDegree_eq_of_degree_eq_some
    (by rw [degree_add_eq_left_of_degree_lt hdlt, degree_X_pow])

/-- **THE GENUINE DIVISION IDENTITY (deliverable B; Lemma D1m's content)**: over ANY commutative
ring, `f = φ² + a₁·φ + a₀` with `a₁, a₀` the `devMap` linear forms — expand and `ring`. The
four displayed coefficient formulas are exactly what two long divisions by the monic `φ`
produce (`develop_eq_devMap` below certifies this against the classifier's `develop`). -/
theorem dev_division (s t : R) (c : fourTuple R) :
    quartic c
      = keyPoly s t ^ 2 + linPair (devMap s t c).1 * keyPoly s t + linPair (devMap s t c).2 := by
  obtain ⟨⟨c₃, c₂⟩, c₁, c₀⟩ := c
  simp only [quartic, keyPoly, linPair, devMap, map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The division identity over `ℤ_[p]`, fully spelled (the task-card form): for
`f = X⁴ + C c₃·X³ + C c₂·X² + C c₁·X + C c₀` and `φ = X² + C s·X + C t`,
`f = φ² + A₁·φ + A₀` with the four explicit coefficient formulas. -/
theorem dev_division_padic (p : ℕ) [Fact p.Prime] (s t c₃ c₂ c₁ c₀ : ℤ_[p]) :
    X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀
      = (X ^ 2 + C s * X + C t) ^ 2
        + (C (c₃ - 2 * s) * X + C (c₂ - s * c₃ + (s ^ 2 - 2 * t)))
            * (X ^ 2 + C s * X + C t)
        + (C (c₁ - s * c₂ + (s ^ 2 - t) * c₃ + (2 * s * t - s ^ 3)) * X
            + C (c₀ - t * c₂ + s * t * c₃ + (t ^ 2 - s ^ 2 * t))) :=
  dev_division s t ((c₃, c₂), (c₁, c₀))

/-- **`Development.lean` compatibility (proved, not remarked)**: the explicit `devMap` linear
forms ARE the classifier's φ-adic development digits of `f − φ²` — via
`Development.develop_unique` (degree bound + reassembly). Since `Development.developEquiv`'s
forward map reads `develop φ k (g − φ^k)`, this evaluates `developEquiv p N 2 2` on a monic
quartic in closed form. -/
theorem develop_eq_devMap [Nontrivial R] (s t : R) (c : fourTuple R) :
    Development.develop (keyPoly s t) 2 (quartic c - keyPoly s t ^ 2)
      = ![linPair (devMap s t c).2, linPair (devMap s t c).1] := by
  refine (Development.develop_unique (keyPoly_monic s t) 2 _ _ (fun j => ?_) ?_).symm
  · fin_cases j <;>
      · rw [keyPoly_natDegree]
        exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast one_lt_two)
  · have hdiv := dev_division s t c
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, mul_one]
    linear_combination -hdiv

/-- `keyPoly` commutes with coefficient maps. -/
theorem keyPoly_map (g : R →+* S) (s t : R) : (keyPoly s t).map g = keyPoly (g s) (g t) := by
  simp [keyPoly]

/-- `quartic` commutes with coefficient maps. -/
theorem quartic_map (g : R →+* S) (c : fourTuple R) :
    (quartic c).map g = quartic (fourMap g c) := by
  simp [quartic, fourMap]

/-- `linPair` commutes with coefficient maps. -/
theorem linPair_map (g : R →+* S) (a : R × R) :
    (linPair a).map g = linPair (g a.1, g a.2) := by
  simp [linPair]

end Poly

/-! ## 4. The Case-E cylinder and its counts (deliverable D; Corollary D1m-CaseE, `N ≥ 2`) -/

section CaseE

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The Case-E stratum cylinder in development coordinates** (Corollary D1m-CaseE): both
`a₁`-coordinates `≡ 0 (mod p)` (`v_Gauss(a₁) ≥ 1`), both `a₀`-coordinates `≡ 0 (mod p)` with
height-1 digit pair `≠ (0, 0)` (`v_Gauss(a₀) = 1` EXACT with unit residual digit pair —
blueprint §1 remark 1: the pair-nonvanishing IS the "unit F_Q-digit" condition; no F_Q-field
structure enters the count). Stated in the `ChainMenu`/`ChainMenuU` digit vocabulary
(`CellCard.digit p N 1`) for phase-2 consumption. -/
def CaseECell (N : ℕ) (a : fourBox p N) : Prop :=
  (p ∣ a.1.1.val ∧ p ∣ a.1.2.val)
    ∧ (p ∣ a.2.1.val ∧ p ∣ a.2.2.val)
    ∧ (digit p N 1 a.2.1, digit p N 1 a.2.2) ≠ (0, 0)

instance instDecidableCaseECell (N : ℕ) : DecidablePred (CaseECell p N) := fun _ => by
  unfold CaseECell; infer_instance

/-- The original-coordinate fiber of the Case-E cylinder is decidable (for the `decide` gates). -/
instance instDecidableCaseEFiber (N : ℕ) (s t : ZMod (p ^ N)) :
    DecidablePred (fun c : fourBox p N => CaseECell p N (devEquiv p N s t c)) := fun _ => by
  unfold CaseECell; infer_instance

/-- Audit spelling: the `a₁`-pair leg and the `a₀`-pair divisibility leg are staircase CLUSTER
conditions (`RecenterBox.ClusterPair`), the residual leg is the height-1 digit pair read. -/
theorem caseECell_iff (N : ℕ) (a : fourBox p N) :
    CaseECell p N a
      ↔ ClusterPair p N N a.1
          ∧ ClusterPair p N N a.2
          ∧ (digit p N 1 a.2.1, digit p N 1 a.2.2) ≠ (0, 0) :=
  Iff.rfl

/-- The `a₀`-pair count: both coordinates `p`-divisible with height-1 digit pair `≠ (0,0)` —
`(p² − 1)·p^{N−2}·p^{N−2}` (the digit-set counting bank `card_pair_digitSet` at the complement
of `{(0,0)}`). Needs `N ≥ 2` (the height-1 digit must be readable). -/
theorem card_caseEA0Pair (N : ℕ) (hN : 2 ≤ N) :
    Nat.card {v : ZMod (p ^ N) × ZMod (p ^ N) //
        (p ∣ v.1.val ∧ p ∣ v.2.val) ∧ (digit p N 1 v.1, digit p N 1 v.2) ≠ (0, 0)}
      = (p ^ 2 - 1) * (p ^ (N - 2) * p ^ (N - 2)) := by
  have e : {v : ZMod (p ^ N) × ZMod (p ^ N) //
        (p ∣ v.1.val ∧ p ∣ v.2.val) ∧ (digit p N 1 v.1, digit p N 1 v.2) ≠ (0, 0)}
      ≃ {v : ZMod (p ^ N) × ZMod (p ^ N) //
          p ^ 1 ∣ v.1.val ∧ p ^ 1 ∣ v.2.val
            ∧ (digit p N 1 v.1, digit p N 1 v.2)
                ∈ ({((0 : ZMod p), (0 : ZMod p))}ᶜ : Finset (ZMod p × ZMod p))} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [pow_one, Finset.mem_compl, Finset.mem_singleton]
      tauto)
  rw [Nat.card_congr e, card_pair_digitSet p (show 1 < N by omega) (show 1 < N by omega)]
  have hS : ({((0 : ZMod p), (0 : ZMod p))}ᶜ : Finset (ZMod p × ZMod p)).card = p ^ 2 - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_prod, ZMod.card, pow_two]
  have hexp : N - 1 - 1 = N - 2 := by omega
  rw [hS, hexp]

/-- **The Case-E stratum count in development coordinates** (Corollary D1m-CaseE, `N ≥ 2`):
`(p² − 1)·p^{2N−4}·p^{2(N−1)}` — the `a₀`-pair pool `(Q−1)·Q^{N−2}` times the free `a₁`-pair
`Q^{N−1}` at `Q = p²` (organized pool × free-digit powers as in `ChainMenuU`'s card lemmas). -/
theorem card_caseECell (N : ℕ) (hN : 2 ≤ N) :
    Nat.card {a : fourBox p N // CaseECell p N a}
      = (p ^ 2 - 1) * p ^ (2 * N - 4) * p ^ (2 * (N - 1)) := by
  have e : {a : fourBox p N // CaseECell p N a}
      ≃ {u : ZMod (p ^ N) × ZMod (p ^ N) // p ∣ u.1.val ∧ p ∣ u.2.val}
        × {v : ZMod (p ^ N) × ZMod (p ^ N) //
            (p ∣ v.1.val ∧ p ∣ v.2.val) ∧ (digit p N 1 v.1, digit p N 1 v.2) ≠ (0, 0)} :=
    Equiv.subtypeProdEquivProd
      (p := fun u : ZMod (p ^ N) × ZMod (p ^ N) => p ∣ u.1.val ∧ p ∣ u.2.val)
      (q := fun v : ZMod (p ^ N) × ZMod (p ^ N) =>
        (p ∣ v.1.val ∧ p ∣ v.2.val) ∧ (digit p N 1 v.1, digit p N 1 v.2) ≠ (0, 0))
  have h1 : Nat.card {u : ZMod (p ^ N) × ZMod (p ^ N) // p ∣ u.1.val ∧ p ∣ u.2.val}
      = p ^ (N + N - 2) := card_clusterPair p N N (by omega) (by omega)
  rw [Nat.card_congr e, Nat.card_prod, h1, card_caseEA0Pair p N hN]
  have h2 : p ^ (N - 2) * p ^ (N - 2) = p ^ (2 * N - 4) := by
    rw [← pow_add]; congr 1; omega
  have h3 : (p : ℕ) ^ (N + N - 2) = p ^ (2 * (N - 1)) := by congr 1; omega
  rw [h2, h3]
  ring

/-- **THE POINT (Corollary D1m-count applied)**: the ORIGINAL-coordinate fiber of the Case-E
cylinder — quartic coefficient boxes whose development digits satisfy the Case-E conditions —
has EXACTLY the nominal cylinder count, for EVERY `(s, t)`: transport along `devEquiv`.
This is the Lean form of "development-digit conditions count exactly their nominal cylinder
volume; the entire content is the unitriangular change of coordinates". -/
theorem card_caseE_original (N : ℕ) (hN : 2 ≤ N) (s t : ZMod (p ^ N)) :
    Nat.card {c : fourBox p N // CaseECell p N (devEquiv p N s t c)}
      = (p ^ 2 - 1) * p ^ (2 * N - 4) * p ^ (2 * (N - 1)) := by
  rw [Nat.card_congr (Equiv.subtypeEquiv (devEquiv p N s t) (fun c => Iff.rfl))]
  exact card_caseECell p N hN

/-- **The Case-E mass identity** (blueprint (★)): the original-coordinate Case-E fiber has mass
`(Q − 1)·Q^{−3}` at `Q = p²` of the `p^{4N}` coefficient box — level-independent for `N ≥ 2`. -/
theorem caseE_mass (N : ℕ) (hN : 2 ≤ N) (s t : ZMod (p ^ N)) :
    (Nat.card {c : fourBox p N // CaseECell p N (devEquiv p N s t c)} : ℚ) / (p : ℚ) ^ (4 * N)
      = ((p : ℚ) ^ 2 - 1) / (p : ℚ) ^ 6 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h2 : (1 : ℕ) ≤ p ^ 2 := Nat.one_le_pow 2 p hp.out.pos
  rw [card_caseE_original p N hN s t, div_eq_div_iff (pow_ne_zero _ hp0) (pow_ne_zero _ hp0)]
  push_cast [h2]
  have hkey : (p : ℚ) ^ (2 * N - 4) * (p : ℚ) ^ (2 * (N - 1)) * (p : ℚ) ^ 6
      = (p : ℚ) ^ (4 * N) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  linear_combination ((p : ℚ) ^ 2 - 1) * hkey

end CaseE

/-! ## 5. The `s = t = 1` Case-E instance (named objects for phase 2)

The gate's key is `φ = x² + x + 1` over `ℤ_[2]` (the canonical lift of THE irreducible
quadratic over `F₂`); its `ZMod (2^N)` box-equiv parameters are `s̄ = t̄ = 1`. -/

/-- The Case-E key polynomial `φ = X² + X + 1` over `ℤ_[2]`. -/
noncomputable def caseEPhi : (ℤ_[2])[X] := keyPoly 1 1

theorem caseEPhi_eq : caseEPhi = X ^ 2 + X + 1 := by
  rw [caseEPhi, keyPoly, map_one, one_mul]

theorem caseEPhi_monic : caseEPhi.Monic := keyPoly_monic 1 1

theorem caseEPhi_natDegree : caseEPhi.natDegree = 2 := keyPoly_natDegree 1 1

/-- The `s = t = 1` development box equiv at `p = 2` (the `caseEPhi` instance; reducible so
the `decide` gates and typeclass search see through it). -/
abbrev caseEDevEquiv (N : ℕ) : fourBox 2 N ≃ fourBox 2 N := devEquiv 2 N 1 1

/-- Box commutation for the `caseEPhi` instance: the genuine `ℤ_[2]` development coefficients
at `s = t = 1` reduce mod `2^N` to `caseEDevEquiv` of the reduced coefficients. -/
theorem caseEDevEquiv_toZModPow (N : ℕ) (c : fourTuple ℤ_[2]) :
    fourMap (PadicInt.toZModPow N) (devMap 1 1 c)
      = caseEDevEquiv N (fourMap (PadicInt.toZModPow N) c) := by
  have h := devMap_toZModPow 2 N 1 1 c
  rwa [map_one] at h

/-! ## 6. Gates (deliverable E; blueprint §0 anchor values) -/

/-- **The Case-E census gate at `p = 2, N = 2`** (kernel `decide`, ORIGINAL coordinates through
the `s = t = 1` equiv): count `12` of `256` — the machine-verified `case_e_gate.py` value
(`3/64` of the box). This re-runs the external census's Lemma-D1m mechanism inside the kernel. -/
theorem gate_caseE_p2_N2 :
    Nat.card {c : fourBox 2 2 // CaseECell 2 2 (caseEDevEquiv 2 c)} = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

set_option maxRecDepth 16000 in
/-- **The Case-E gate at `p = 3, N = 2`** (kernel `decide`, `6561`-point census at
`s = 0, t = 1`, i.e. `φ = x² + 1`, irreducible mod `3`): count `(9−1)·9⁰·9¹ = 72` ✓ — matching
`card_caseE_original` (which gives the same count for EVERY `(s, t)`). -/
theorem gate_caseE_p3_N2 :
    Nat.card {c : fourBox 3 2 // CaseECell 3 2 (devEquiv 3 2 0 1 c)} = 72 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-- **The Case-E mass gate at `p = 2`**: `12/2⁸ = 3/64` — the external gate's exact stratum
mass, from the `decide`-checked count. -/
theorem gate_caseE_mass_p2 :
    (Nat.card {c : fourBox 2 2 // CaseECell 2 2 (caseEDevEquiv 2 c)} : ℚ) / (2 : ℚ) ^ 8
      = 3 / 64 := by
  rw [gate_caseE_p2_N2]
  norm_num

/-! ## 7. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms devMap
#print axioms devInv
#print axioms devInv_devMap
#print axioms devMap_devInv
#print axioms fourMap
#print axioms fourMap_devMap
#print axioms devEquiv
#print axioms devEquiv_apply
#print axioms devEquiv_symm_apply
#print axioms devMap_toZModPow
#print axioms keyPoly
#print axioms quartic
#print axioms linPair
#print axioms natDegree_linPair_le
#print axioms degree_linPair_le
#print axioms keyPoly_monic
#print axioms keyPoly_natDegree
#print axioms dev_division
#print axioms dev_division_padic
#print axioms develop_eq_devMap
#print axioms keyPoly_map
#print axioms quartic_map
#print axioms linPair_map
#print axioms CaseECell
#print axioms instDecidableCaseECell
#print axioms instDecidableCaseEFiber
#print axioms caseECell_iff
#print axioms card_caseEA0Pair
#print axioms card_caseECell
#print axioms card_caseE_original
#print axioms caseE_mass
#print axioms caseEPhi
#print axioms caseEPhi_eq
#print axioms caseEPhi_monic
#print axioms caseEPhi_natDegree
#print axioms caseEDevEquiv
#print axioms caseEDevEquiv_toZModPow
#print axioms gate_caseE_p2_N2
#print axioms gate_caseE_p3_N2
#print axioms gate_caseE_mass_p2
end AxCheck

end LeanUrat.OM.DevBijection
