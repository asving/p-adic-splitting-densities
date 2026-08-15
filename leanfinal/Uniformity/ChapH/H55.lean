/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H54
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Uniformity.ChapH.H55 — `L_M` is integral, of degree `< D′`, and of exact height `M`

**Chapter H, NODE H.55** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer). The
three exponent facts about H.54's stage lift

`stageLift' G π i a lift = Σ_{s < f₁} (lift s · π^(a − s·h)) · X^(i + e₁·s)`,

under the standing hypotheses `i < e₁`, `i·h + e₁·a = M` (the defining equation of the height-`M`
normalizer, carried as a hypothesis because `stageLift'` takes `i` and `a` as arguments — H.54's
⚠ SIGNATURE NOTE) and `keyDeg·h < M` (the terminal-scope condition of H.10):

* `stageLift_index_lt` — **degree**: every `X`-exponent satisfies `i + e₁·s < D′ = keyDeg`, so the
  lift has degree `< D′` and is a legal entry-key remainder;
* `stageLift_integral` — **integrality**: `s·h ≤ a` for every `s < f₁`, so the `π`-exponent
  `a − s·h` is an honest `ℕ` and no summand needs a denominator;
* `stageLift_height` — **exact height**: `e₁·(a − s·h) + (i + e₁·s)·h = M` for every `s < f₁`, so
  every summand sits at `dv`-height exactly `M` — the `s·h` terms cancel identically.

Each clause is pure exponent arithmetic; none of them mentions `Polynomial O`. The last section of
the file records the polynomial consequence of the first clause (`degree < D′`) as an `example`,
so that the arithmetic bound is visibly the degree bound and not merely an inequality about
indices.

DEPENDS: H.01 (`GenreDatum`, for `he₁`, `hh`), H.02 (`GenreDatum.keyDeg = e₁ * f₁`), H.54
(`stageLift'`, the polynomial the three clauses describe) · mathlib `Nat.mul_le_mul`,
`Nat.lt_of_mul_lt_mul_left`, `Nat.exists_eq_add_of_le`.

SOURCE: `EFF.GENHN.81`'s PROOF, verbatim: *"Since `i+e_1s ≤ D'-1` and `M > D'h`,
`a-sh = (M-(i+e_1s)h)/e_1 ≥ 0`, so every summand is integral and has degree `< D'`. Its evaluated
height is `e_1(a-sh)+(i+e_1s)h = M`."*

**⚠ WHY `hbig` IS NEEDED FOR INTEGRALITY AND NOT FOR THE INDEX BOUND.** `stageLift_index_lt` is
about `i` and `s` alone and holds for every genre datum. `stageLift_integral` is the only place
the terminal-scope hypothesis `keyDeg·h < M` does work: it is what makes `(i + e₁ s)h < M`, hence
`e₁·(s·h) < e₁·a`, hence `s·h < a`. Drop `hbig` and the clause is FALSE — e.g. `e₁ = f₁ = h = 1`
is excluded by `hkey`, but at `(e₁, f₁, h) = (1, 2, 1)` (the D2b witness datum) with `i = 0`,
`a = 0`, `M = 0` and `s = 1` one has `s·h = 1 > 0 = a`, and indeed `keyDeg·h = 2` is not `< 0`.
`stageLift_height` inherits the hypothesis through `stageLift_integral`, since the `ℕ`-subtraction
`a − s·h` is only honest once `s·h ≤ a`.

**ARITHMETIC AUDIT (blueprint, reproduced).** `(e₁,f₁,h) = (3,1,1)`, `keyDeg·h = 3`, `M = 4`:
`i = 1, a = 1`; the single `s = 0` gives `0 ≤ 1` ✓, index `1 < 3` ✓, height `3·1 + 1·1 = 4` ✓.
`(e₁,f₁,h) = (2,3,1)`, `keyDeg·h = 6`, `M = 9`: `i = 1, a = 4`; `s ∈ {0,1,2}` gives `0,1,2 ≤ 4` ✓,
indices `1,3,5 < 6` ✓, heights `2·4+1 = 2·3+3 = 2·2+5 = 9` ✓ — three summands at ONE height, which
is the "one `K`-digit per height" content at `f₁ = 3`.

TEETH: **PROOF-ONLY** at `f₁ ≥ 2` (`EFF.GENHN.81`), with `EFF.GENHN.32`'s two exhaustive `f₁ = 3`
rows as foreign corroboration → **Lean theorem** (this file), covering every genre datum at once.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **H.55 (ii) — the degree clause.** Every `X`-exponent of `stageLift'` is `< D′ = keyDeg`:
`i + e₁·s ≤ (e₁ − 1) + e₁·(f₁ − 1) = e₁f₁ − 1`. No hypothesis on `M` is needed. -/
theorem stageLift_index_lt (G : GenreDatum) {i s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁) :
    i + G.e₁ * s < G.keyDeg := by
  have hs' : s + 1 ≤ G.f₁ := hs
  have hstep : G.e₁ * (s + 1) ≤ G.e₁ * G.f₁ := Nat.mul_le_mul (le_refl G.e₁) hs'
  have hexp : G.e₁ * (s + 1) = G.e₁ * s + G.e₁ := by ring
  simp only [GenreDatum.keyDeg]
  omega

/-- **H.55 (i) — the integrality clause.** Under the terminal-scope hypothesis `keyDeg·h < M` and
the normalizer equation `i·h + e₁·a = M`, every `π`-exponent `a − s·h` of `stageLift'` is an
honest natural number: `s·h ≤ a`. -/
theorem stageLift_integral (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) : s * G.h ≤ a := by
  have hidx : i + G.e₁ * s < G.keyDeg := stageLift_index_lt G hi hs
  have hh : 0 < G.h := G.hh
  have h1 : (i + G.e₁ * s) * G.h < G.keyDeg * G.h := Nat.mul_lt_mul_of_lt_of_le hidx (le_refl G.h) hh
  have hexp : (i + G.e₁ * s) * G.h = i * G.h + G.e₁ * (s * G.h) := by ring
  have h3 : G.e₁ * (s * G.h) < G.e₁ * a := by omega
  exact le_of_lt (Nat.lt_of_mul_lt_mul_left h3)

/-- **H.55 (iii) — the exact-height clause.** Every nonzero summand of `stageLift'` sits at
`dv`-height exactly `M`: `e₁·(a − s·h) + (i + e₁·s)·h = e₁·a + i·h = M`, the `s·h` terms
cancelling identically (the subtraction is honest by `stageLift_integral`). -/
theorem stageLift_height (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) :
    G.e₁ * (a - s * G.h) + (i + G.e₁ * s) * G.h = M := by
  have hsa : s * G.h ≤ a := stageLift_integral G hi hs hM hbig
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hsa
  subst hb
  have h1 : s * G.h + b - s * G.h = b := by omega
  rw [h1]
  have h2 : (i + G.e₁ * s) * G.h = i * G.h + G.e₁ * (s * G.h) := by ring
  have h3 : G.e₁ * (s * G.h + b) = G.e₁ * (s * G.h) + G.e₁ * b := by ring
  omega

section AxCheck
#print axioms Uniformity.Density.Induction.stageLift_index_lt
#print axioms Uniformity.Density.Induction.stageLift_integral
#print axioms Uniformity.Density.Induction.stageLift_height
end AxCheck

end Uniformity.Density.Induction

/-! ## The polynomial reading of clause (ii)

`stageLift_index_lt` is stated about exponents; the sentence the corpus writes is *"every summand
… has degree `< D'`"*. The `example` below is that reading, so the identification is checked by
the elaborator rather than asserted in prose. It is an `example`, not a declaration: H.55's signed
contract is the three theorems above, and consumers that need the degree bound derive it here in
one line. -/

section DegreeReading

open Uniformity.Density.Induction

/-- The lift's degree is `< D′ = keyDeg`, from the index bound summand by summand. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) {i : ℕ} (a : ℕ) (lift : ℕ → O)
    (hi : i < G.e₁) : (stageLift' G π i a lift).degree < (G.keyDeg : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)).2 ?_
  intro s hs
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast stageLift_index_lt G hi (Finset.mem_range.1 hs)

end DegreeReading
