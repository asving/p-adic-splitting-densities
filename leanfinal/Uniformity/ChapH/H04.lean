/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Uniformity.ChapH.H03

/-!
# Uniformity.ChapH.H04 — the composite-type enumeration and the degree threshold

**Chapter H, NODE H.04** (`blueprint/CHAP-H_general_induction.md` §3). Three clauses, all
pure `ℕ`-arithmetic:

* **(i)** `keyDeg_two_cases` — if `e · f = 2` then `(e, f) = (2, 1)` or `(e, f) = (1, 2)`;
* **(ii)** `sideLen_four_cases` — if `e · μ · f = 4` with `2 ≤ μ` and `2 ≤ e · f`, then
  `(e, f, μ) = (2, 1, 2)` or `(e, f, μ) = (1, 2, 2)` — **exactly two solutions**;
* **(iii)** `four_le_of_sideLen_le` — if `G.sideLen ≤ m` and `m · D ≤ n` with `1 ≤ D`, then
  `4 ≤ m` and `4 ≤ n`.

Clause (ii) is the enumeration of the two composite *types* at the `n = 4` boundary: `(2,1,2)` is
genre E (`e₁ = 2`, `f₁ = 1`, stage residue cardinality `Q`) and `(1,2,2)` is genre F (`e₁ = 1`,
`f₁ = 2`, stage residue cardinality `Q²`). Clause (iii) is the passage from the abscissa-length
bound `4 ≤ L` (H.03) to the frame bound `4 ≤ m` and the degree bound `4 ≤ n`, made under the two
hypotheses the geometry supplies from outside this chapter (see the scope fence in H.03).

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.sideLen`), H.03
(`GenreDatum.four_le_sideLen`, for clause (iii)).

SOURCE: `EFF.GENIND.32` (the enumeration verbatim: *"the two composite types are
`(e, deg ψ, μ) = (2, 1, 2)` and `(1, 2, 2)` — the only solutions of `e·μ·deg ψ = 4` with `μ ≥ 2`
and `e·deg ψ ≥ 2`"*, with the spec's own ARITHMETIC AUDIT: *"Factorizations of 4 with `μ ≥ 2`:
`(μ, e·deg ψ) ∈ {(2,2), (4,1)}`; `(4,1)` fails `e·deg ψ ≥ 2`"*); `EFF.GENIND.11` (the degree
threshold); `EFF.GENIND.43`.

ARITHMETIC AUDIT (blueprint, recomputed): clause (ii) has no `q`. Cross-check of `sideLen` on the
two solutions: E gives `2·2·1 = 4` ✓, F gives `1·2·2 = 4` ✓ — both saturate the `n = 4` abscissa
budget. The `n = 6` genres give `sideLen = 6` in all four cases (`E3 = (2,1,3) → 6`,
`E31 = (3,1,2) → 6`, `F3 = (1,2,3) → 6`, `E13 = (1,3,2) → 6`), so the grammar bound
`4 ≤ e₁f₁μ ≤ 6` covers exactly the `n ≤ 6` genres. Both facts are re-executed in the numeric gate
below, which additionally enumerates *all* `(e, f, μ)` in `[0,9]³` and checks (i) and (ii) as
biconditionals against brute force.

TEETH: as H.03 — `GT-CRIT` (`EFF.GENIND.11`, executable regression + planted grammar-acceptance
mutant, §S11 P-8 "0/22") and `GN-T-CRIT` (`EFF.GENHN.07`, planted mutant, fired 2/2) — discharged
as **Lean theorem**; additionally `GT-CRIT`'s negative half ("ZERO CS events on all four `n = 3`
control rows") is the contrapositive of clause (iii), also a **Lean theorem** here.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.04(i).** The two factorizations of the entry-key degree `D′ = e · f = 2`: either the
slope denominator carries it (`e = 2`, `f = 1`, the ramified opening) or the residual degree does
(`e = 1`, `f = 2`, the inert opening). -/
theorem keyDeg_two_cases {e f : ℕ} (h : e * f = 2) : (e = 2 ∧ f = 1) ∨ (e = 1 ∧ f = 2) := by
  have he : e ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨f, h.symm⟩
  interval_cases e <;> omega

/-- **NODE H.04(ii).** *The composite-type enumeration.* The solutions of `e · μ · f = 4` under
the two genre constraints `2 ≤ μ` (a repeated residual factor) and `2 ≤ e · f` (a composite entry
key) are **exactly two**: `(e, f, μ) = (2, 1, 2)` (genre E) and `(e, f, μ) = (1, 2, 2)`
(genre F). -/
theorem sideLen_four_cases {e f m : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ e * f) (h : e * m * f = 4) :
    (e = 2 ∧ f = 1 ∧ m = 2) ∨ (e = 1 ∧ f = 2 ∧ m = 2) := by
  -- Regroup the product as `m * (e * f)` and abstract the key degree `e * f` to an atom `k`,
  -- so that fixing `m` by `interval_cases` leaves a linear equation.
  have hcomm : m * (e * f) = 4 := by rw [← h]; ring
  have hm4 : m ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨e * f, hcomm.symm⟩
  obtain ⟨k, hkdef⟩ : ∃ k, e * f = k := ⟨e * f, rfl⟩
  rw [hkdef] at hk hcomm
  -- `m = 3` is impossible (`3 ∤ 4`) and `m = 4` forces `k = 1`, contradicting `2 ≤ k`.
  have hk2 : k = 2 := by interval_cases m <;> omega
  subst hk2
  have hm2 : m = 2 := by omega
  have hef : e * f = 2 := hkdef
  rcases keyDeg_two_cases hef with ⟨he, hf⟩ | ⟨he, hf⟩
  · exact Or.inl ⟨he, hf, hm2⟩
  · exact Or.inr ⟨he, hf, hm2⟩

/-- **NODE H.04(iii).** *The degree threshold.* Once the composite block's abscissa length `L`
fits inside the frame (`G.sideLen ≤ m`) and the frame fits inside the degree with key degree
`D ≥ 1` (`m · D ≤ n`), the `4 ≤ L` bound of H.03 propagates: `4 ≤ m` and `4 ≤ n`. Contrapositive:
no CS event exists below degree `4`. -/
theorem four_le_of_sideLen_le {G : GenreDatum} {m D n : ℕ} (hD : 1 ≤ D)
    (hLm : G.sideLen ≤ m) (hmn : m * D ≤ n) : 4 ≤ m ∧ 4 ≤ n := by
  have h4m : 4 ≤ m := le_trans G.four_le_sideLen hLm
  have hmmD : m ≤ m * D := Nat.le_mul_of_pos_right m hD
  exact ⟨h4m, le_trans (le_trans h4m hmmD) hmn⟩

end Uniformity.Density.Induction

/-! ## Numeric gate — clauses (i) and (ii) as biconditionals against brute force.
`#guard` fails elaboration when the proposition evaluates to `false`, so these are build-time
checks, not print-outs. The sweep `[0,9]³` is the stub's own grid; it certifies that the two listed
solutions are not merely *solutions* but the *only* ones in range (a missing case would show up as
a `true`-hypothesis/`false`-conclusion row). -/

section NumericGate

-- Clause (i) over `(e, f) ∈ [0,9]²`.
#guard (List.range 10).all fun e => (List.range 10).all fun f =>
  !(e * f == 2) || ((e == 2 && f == 1) || (e == 1 && f == 2))

-- Clause (ii) over `(e, f, m) ∈ [0,9]³`.
#guard (List.range 10).all fun e => (List.range 10).all fun f => (List.range 10).all fun m =>
  !(decide (2 ≤ m) && decide (2 ≤ e * f) && e * m * f == 4) ||
    ((e == 2 && f == 1 && m == 2) || (e == 1 && f == 2 && m == 2))

-- The blueprint's `sideLen` cross-check: the two `n = 4` genres E `(2,1,2)` and F `(1,2,2)`
-- both saturate `L = 4`, and the four `n = 6` genres E3 `(2,1,3)`, E31 `(3,1,2)`, F3 `(1,2,3)`,
-- E13 `(1,3,2)` all give `L = 6` — so `4 ≤ e₁f₁μ ≤ 6` covers exactly the `n ≤ 6` genres.
#guard [((2, 1), 2), ((1, 2), 2)].all fun p => p.1.1 * p.2 * p.1.2 == 4

#guard [((2, 1), 3), ((3, 1), 2), ((1, 2), 3), ((1, 3), 2)].all fun p =>
  p.1.1 * p.2 * p.1.2 == 6

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.keyDeg_two_cases
#print axioms Uniformity.Density.Induction.sideLen_four_cases
#print axioms Uniformity.Density.Induction.four_le_of_sideLen_le

end AxCheck
