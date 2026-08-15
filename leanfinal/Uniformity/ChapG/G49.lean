/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G48

/-!
# Uniformity.ChapG.G49 — the `ℤ_[2]` and `ℤ_[3]` gates, exact

**Chapter G, NODE G.49** (`blueprint/CHAP-G_base_cases_menus.md` §7). The two concrete instances
of G.48: at the wild prime `q = 2` all three degree-2 types have density exactly `1/3`, and at
`q = 3` split and inert have `3/8` while ram has `1/4`.

DEPENDS: G.48 (`genuineDensity_two_exact`) · landed `residueCard_padicInt` (`LocalData.lean:343`),
the `Finite (ResidueField ℤ_[p])` instance (`LocalData.lean:336`).

**PROOF.** Instantiate G.48 at `O := ℤ_[2]` / `O := ℤ_[3]`, `rw [residueCard_padicInt]` to turn
`q` into the literal prime, then `norm_num`: `2/(2·(2+1)) = 1/3`, `1/(2+1) = 1/3`;
`3/(2·(3+1)) = 3/8`, `1/(3+1) = 1/4`. The `Fact (Nat.Prime 2)` / `Fact (Nat.Prime 3)` instances
are mathlib's and are found by instance search, exactly as in the landed
`Gates.lean:254 gate_padic_two_decided`.

**⚠ GATE SEMANTICS — a regression here is a stop-the-line event.** These values sit strictly
inside the landed brackets, and **this node closes those brackets to points**:

* `gate_bracket_padic_two_decided` (`Gates.lean:547`) brackets `ℤ_[2]` at
  split `[1/4, 11/16]`, inert `[1/4, 11/16]`, ram `[1/16, 1/2]`; all three exact values are `1/3`.
* `gate_bracket_padic_three_decided` (`Gates.lean:560`) brackets `ℤ_[3]` at
  split `[2/9, 71/81]`, inert `[1/9, 62/81]`, ram `[1/81, 2/3]`; the exact values are
  `3/8`, `3/8`, `1/4`.

The landed `gate_bracket_w11_two` / `gate_bracket_w11_three` assert exactly that containment as
`norm_num` facts; this node supersedes the containment check by the value itself. Note the
brackets are stated over `decidedDensity` and this node over `genuineDensity`; the two agree
unconditionally at `n = 2` by `genuineDensity_eq_decidedDensity_two`, which is what G.48 uses.

**⚠ ARITHMETIC CROSS-CHECK.** `Σ = 1` at both primes: `1/3 + 1/3 + 1/3 = 1` ✓ and
`3/8 + 3/8 + 1/4 = 1` ✓, matching the landed `sum_three_densities_eq_one`.

**TEETH.** `gate_bracket_w11_two`, `gate_bracket_w11_three` (landed) → Lean theorem.

## Status

Sorry-free, axiom-free (Lean core only). No section variables: both statements are about the
concrete rings `ℤ_[2]` and `ℤ_[3]`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

/-- **G.49, the `q = 2` gate, exact.** At the wild prime all three degree-2 types are equally
likely: `genuineDensity ℤ_[2] 2 σ = 1/3` for `σ ∈ {split, inert, ram}`. This closes the landed
bracket `gate_bracket_padic_two_decided` (`[1/4, 11/16]`, `[1/4, 11/16]`, `[1/16, 1/2]`) to a
point. -/
theorem gate_two_padic_two_exact :
    genuineDensity ℤ_[2] 2 splitType = 1 / 3 ∧ genuineDensity ℤ_[2] 2 inertType = 1 / 3
      ∧ genuineDensity ℤ_[2] 2 ramType = 1 / 3 := by
  obtain ⟨hs, hi, hr, -⟩ := genuineDensity_two_exact (O := ℤ_[2])
  rw [residueCard_padicInt 2] at hs hi hr
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; norm_num
  · rw [hi]; norm_num
  · rw [hr]; norm_num

/-- **G.49, the `q = 3` gate, exact.** `genuineDensity ℤ_[3] 2 split = inert = 3/8`,
`ram = 1/4`. This closes the landed bracket `gate_bracket_padic_three_decided`
(`[2/9, 71/81]`, `[1/9, 62/81]`, `[1/81, 2/3]`) to a point. -/
theorem gate_two_padic_three_exact :
    genuineDensity ℤ_[3] 2 splitType = 3 / 8 ∧ genuineDensity ℤ_[3] 2 inertType = 3 / 8
      ∧ genuineDensity ℤ_[3] 2 ramType = 1 / 4 := by
  obtain ⟨hs, hi, hr, -⟩ := genuineDensity_two_exact (O := ℤ_[3])
  rw [residueCard_padicInt 3] at hs hi hr
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; norm_num
  · rw [hi]; norm_num
  · rw [hr]; norm_num

section AxCheck

#print axioms Uniformity.Density.gate_two_padic_two_exact
#print axioms Uniformity.Density.gate_two_padic_three_exact

end AxCheck

end Uniformity.Density
