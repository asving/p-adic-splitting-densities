/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E15 — the multiset sandwich and the `(e,f)` forcing chain

**Chapter E, NODE E.15** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §4), ENV-E1 (clause ii) /
ENV-E2 (clause i's application).

`EFF.T2.30`'s counting step is two pieces of pure arithmetic, and this node lands exactly those
two — nothing about orbits, irreducibility, or ideals.

* **Clause (i), the sandwich** (`multiset_sandwich`). A finite family of counts that dominates a
  forced lower bound termwise and has the *same total* is EQUAL to that lower bound termwise:
  "Summing over disjoint exhaustive classes and using `(SIDE-COUNT)` and `(DEG-SUM)` forces
  equality term by term". At a separable side the instance supplies `lower ≤ count` from
  `hforce`, the two totals from E.14 (`(DEG-SUM)`) and `hexhaust`, and reads off
  `classCount p q = C.D * p.2` (linear) / `classCountHi p q = C.D * p.2 * q.1` (higher).

* **Clause (ii), the `(e,f)` forcing** (`ef_forcing`). If `a ∣ e`, `b ∣ f` and `e·f = a·b` with
  `a, b > 0`, then `e = a` and `f = b`: "equality in `(FUND)` forces equality in both local
  divisibilities". Instances take `a = e_𝒞·e′`, `b = f_𝒞·deg r′` and
  `e·f = |orbit| = D·e′·deg r′ = a·b` via `(DEG-EF)`.

## ⚠ WHAT THIS NODE DOES *NOT* PROVE (GC-3 / HYP.01 fence, transcribed from the blueprint)

The step from "class count `= De′deg r′`" to "the class is ONE GALOIS ORBIT = the root set of one
monic irreducible factor with local invariants `(e, f)`" consumes `(FUND)`
(`|Ω| = [K₀(ρ):K₀] = e·f`) and the field `hforce`'s orbit reading — that is CARRIER content, not
schema content. `(FUND)` at instances is the rank-form identity
`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
(`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`, GC-3); identifying the
polynomial-level `efPair` with the ideal-theoretic pair is `HYP.01` + `HYP.12`. Neither is done
here, silently or otherwise: `ef_forcing`'s hypotheses are three arithmetic facts about four
natural numbers, and its conclusion is an equation between natural numbers.

## ⚠ FENCE — CHAP-H §11 is NOT consumed

H.76 (`e₁ ∣ e, f₁ ∣ f, e·f ≤ e₁f₁ ⟹ …`) is the `μ = 2` σ-forcing analogue of clause (ii), but
H §11 is outside E's sanctioned slice (GC-5/H-14: only H.51–H.58). Clause (ii) is therefore
proved fresh here — cheaper than a fence violation, and this file imports no chapter-H module.

## Proof notes

`multiset_sandwich` is `Multiset.induction_on`: at a cons the tail's lower sum is `≤` its count
sum (`Multiset.sum_map_le_sum_map`), so the head equation `count a + Σcount = lower a + Σlower`
plus `lower a ≤ count a` splits by `omega` into `count a = lower a` AND equality of the tail
sums, which feeds the inductive hypothesis. `ef_forcing` writes `e = a*x`, `f = b*y`, cancels
`a*b > 0` from `a*b*(x*y) = a*b*1` and uses `x*y = 1 ⟹ x = y = 1`.

DEPENDS: E.12, E.14 (at the APPLICATION, not in these statements — both declarations here are
carrier-free) · mathlib `Multiset.sum_map_le_sum_map`, `Multiset.induction_on`,
`Nat.eq_of_mul_eq_mul_left`, `Nat.eq_one_of_mul_eq_one_right`.

SOURCE: `EFF.T2.30` (verbatim: "Local forcing and `(DEG-EF)` make every orbit in the class have
size at least `De′deg r′`. Summing over disjoint exhaustive classes and using `(SIDE-COUNT)` and
`(DEG-SUM)` forces equality term by term. The full class therefore has room for exactly one
orbit; equality in `(FUND)` forces equality in both local divisibilities."); `EFF.HE7.13`'s
sandwich ("the sandwich forces equality, each class is a single Galois orbit … `e ≥ e₁ℓℓ₂,
f ≥ f₁d_rd_{r₂}` with `ef = …` forces equality on both").

TEETH: S7 Pass 1 pure-mathematics theorem gate (`EFF.T2.30`) → **Lean theorem** (both clauses).
The gate below adds the two sharpness checks the fence invites: the sandwich FAILS without the
equal-totals hypothesis, and `ef_forcing` FAILS without positivity of `a` — both exhibited as
`example`s with explicit witnesses.

ENVIRONMENT: ENV-E1 (clause ii) / ENV-E2 (clause i application).

## Status

Sorry-free, axiom-free (Lean core only). Both declarations were transcribed from
`leanspec/Leanspec/ChapE.lean`'s signed stubs with binder names, order and explicitness
unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.15(i)** The multiset sandwich (`EFF.T2.30`): counts that dominate a forced lower bound
termwise, with equal totals, equal it termwise. -/
theorem multiset_sandwich {α : Type*} (s : Multiset α) (count lower : α → ℕ)
    (hle : ∀ q ∈ s, lower q ≤ count q)
    (hsum : (s.map count).sum = (s.map lower).sum) :
    ∀ q ∈ s, count q = lower q := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
      -- the tail already satisfies the inequality, so the head's slack is the total slack
      have htail : (t.map lower).sum ≤ (t.map count).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun i hi => hle i (Multiset.mem_cons_of_mem hi))
      have hahead : lower a ≤ count a := hle a (Multiset.mem_cons_self a t)
      have hA : count a = lower a := by omega
      have hT : (t.map count).sum = (t.map lower).sum := by omega
      intro q hq
      rcases Multiset.mem_cons.mp hq with rfl | hq
      · exact hA
      · exact ih (fun i hi => hle i (Multiset.mem_cons_of_mem hi)) hT q hq

/-- **E.15(ii)** The `(e,f)` forcing chain (`EFF.T2.30`): equality in `(FUND)` forces equality in
both local divisibilities. Pure arithmetic — see the HYP.01 fence in the module docstring. -/
theorem ef_forcing {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hae : a ∣ e) (hbf : b ∣ f) (hprod : e * f = a * b) : e = a ∧ f = b := by
  obtain ⟨x, rfl⟩ := hae
  obtain ⟨y, rfl⟩ := hbf
  have h : a * b * (x * y) = a * b * 1 :=
    calc a * b * (x * y) = a * x * (b * y) := by ring
      _ = a * b := hprod
      _ = a * b * 1 := (mul_one _).symm
  have hxy : x * y = 1 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha hb) h
  have hx : x = 1 := Nat.eq_one_of_mul_eq_one_right hxy
  have hy : y = 1 := Nat.eq_one_of_mul_eq_one_right (by rw [mul_comm]; exact hxy)
  subst hx; subst hy
  exact ⟨mul_one a, mul_one b⟩

/-! ## Gate (executed `example`s, not blueprint declarations)

Four checks: each clause fired at a witness, and each clause's load-bearing hypothesis shown to
be load-bearing by a counterexample to the statement without it. -/

section Gate

-- POSITIVE (i). The sandwich used the way instances use it: nothing is known about `count`
-- except the forced lower bound `1` at each of two classes and the total `2`; the conclusion
-- `count 0 = 1` is genuinely DERIVED, not read off.
example (count : ℕ → ℕ) (hle : ∀ q ∈ ({0, 1} : Multiset ℕ), 1 ≤ count q)
    (hsum : ((({0, 1} : Multiset ℕ)).map count).sum = 2) : count 0 = 1 :=
  multiset_sandwich ({0, 1} : Multiset ℕ) count (fun _ => 1) hle (by simpa using hsum) 0 (by simp)

-- SHARPNESS (i). The equal-totals hypothesis is load-bearing: termwise `≤` alone does not force
-- termwise equality.
example : ¬ (∀ (s : Multiset ℕ) (count lower : ℕ → ℕ),
    (∀ q ∈ s, lower q ≤ count q) → ∀ q ∈ s, count q = lower q) := by
  intro h
  have := h ({0} : Multiset ℕ) (fun _ => 1) (fun _ => 0) (by simp) 0 (by simp)
  omega

-- POSITIVE (ii). E.15's `ef_forcing` at the witness `(a, b) = (4, 2)`, `e·f = 8` — the same
-- witness `leanspec`'s E.67 gate uses.
example : (4 : ℕ) = 4 ∧ (2 : ℕ) = 2 :=
  ef_forcing (by norm_num) (by norm_num) dvd_rfl dvd_rfl (by norm_num)

-- SHARPNESS (ii). Positivity of `a` is load-bearing: at `(a, b, e, f) = (0, 1, 0, 7)` all three
-- arithmetic hypotheses hold (`0 ∣ 0`, `1 ∣ 7`, `0 * 7 = 0 * 1`) and `f = b` fails.
example : ¬ (∀ a b e f : ℕ, a ∣ e → b ∣ f → e * f = a * b → e = a ∧ f = b) := by
  intro h
  have := (h 0 1 0 7 dvd_rfl (one_dvd 7) (by norm_num)).2
  omega

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.multiset_sandwich
#print axioms Uniformity.Density.Ladder.ef_forcing

end AxCheck
