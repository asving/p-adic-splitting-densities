/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapH.H65

/-!
# Uniformity.ChapH.H71 — `RecursionLegs`, and the REFUTATION of `rate_close` as signed

> **⚠ NODE H.71 IS *NOT* COMPLETE. `rate_close` IS **NOT** LANDED HERE: the signed statement is
> FALSE, and the falsity is machine-checked below.** This file lands only the node's first
> declaration, the `RecursionLegs` structure (in the blueprint's `[repaired: A-H.1/D6 + D7]`
> form), plus the counterexample that refutes the second. The node's status is **BLOCKED —
> statement-level defect, blueprint repair required**; it must not be counted as transcribed.

**Chapter H, NODE H.71** (`blueprint/CHAP-H_general_induction.md` §10, line 4394). `GENIND.C′`,
the quantitative vanishing clause: package the three legs of the `S5.2` recursion (head, α, β) as
a structure, and conclude that the normalized complement family `u` belongs to H.65's
`RateSpecies` with constants `B = m + B' + 1`, `c = c' + 1`.

## What is landed

`RecursionLegs Q m c u` — verbatim from the repaired SIGNATURE block: seven data fields
(`head`, `alpha`, `beta`, `K'`, `B'`, `c'`, `n₀`, one name per field, per A-H.1/D6) and seven
hypothesis fields (`hK'`, `hsplit`, `hu0`, `hhead`, `halpha`, `hbeta`, `hdesc`, the last with the
annotated binders and the `1 ≤ N` guard of A-H.1/D7). The structure is inhabited — two witnesses
are constructed in this file — so A-H.1/D7's repair did its job: the pre-repair field was
unsatisfiable and emptied the type.

## What is NOT landed, and why: `rate_close` is FALSE

```lean
theorem rate_close {Q m c : ℕ} (hQ : 2 ≤ Q) (hc : 1 ≤ c) (hm : 1 ≤ m)
    {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D)
```

Two independent counterexample families. **Neither is a `ℕ`-truncation accident and neither is
repaired by A-H.1/D6 or /D7** — those cured elaboration and inhabitation; these are about what the
fields do and do not say.

### DEFECT (α-0) — the window-`0` value `u D 0` is unconstrained, and the α-leg reads it

**Machine-checked below** (`legsWindowZero` + the `False` derivation).

`halpha` sums over **all** `k < n₀`, with no window condition, so at `N = m·(k+1)` the summand is
`u D 0`. The structure bounds `u D 0` only from below (`hu0 : 0 ≤ u D N`). But the conclusion's
`K` is quantified **before** `D` (`∃ K, ∀ D`), so a family whose window-`0` value is unbounded in
`D` cannot satisfy it, while satisfying every field.

Witness: `Q = 2`, `m = c = 1`, `n₀ = 1`, `K' = B' = c' = 0`, `head = beta = 0`,
`u D N := D · (2^N)⁻¹`, `alpha := u`. Every field holds — `hsplit` and `halpha` hold with
**equality** (`u D N = ½ · u D (N−1)` for `N ≥ 1` is exactly the α-leg at `Q = 2, c = 1`) — and
the conclusion at `M = 1` reads `u D 1 = D/2 ≤ K · 1^B · (2^0)⁻¹ = K` for every `D`. Take
`D > 2K`.

**Repair (blueprint-side, one field).** Either bound the window-`0` value uniformly — the intended
reading, since `u` is a *normalized* complement, so `hu1 : ∀ D, u D 0 ≤ 1` — or restore the α-leg's
WINDOW CONDITION and sum only over the `k` with `m·(k+1) ≤ N − 1` (`EFF.GENIND.09`'s
`mμ ≤ N−1`, which H.20's own note records as the realized-history rider, and which H.22(ii) says is
*empty* at `N = 1`). Either makes the α-leg's appeal to the induction hypothesis legitimate; as
signed, PROOF step 4's *"by the IH at each `N − m(k+1) < N`"* invokes an IH that does not exist,
because `RateSpecies` says nothing at `M = 0`.

### DEFECT (α-rate) — the α-leg's budget does not pay for its descent unless `m ≤ c`

**Verified numerically over `N ≤ 59`, not formalized here** (the refutation is asymptotic in `M`,
so it is not a one-point argument like (α-0); the arithmetic is elementary and reproduced below).

Each α-summand descends `m·(k+1)` windows but is discounted by only `Q^(−c·(k+1))`. Recomposing
the exponent, the `k`-th term of the IH bound carries
`Q^(−c(k+1)) · Q^(−(N − m(k+1) − C)) = Q^(−(N−C)) · Q^((m−c)(k+1))`,
so the geometric factor H.30 bounds by `1` is multiplied by `Q^((m−c)(k+1)) > 1` as soon as
`m > c`. This is precisely the *"delicate step"* the blueprint's own
⚠ [NEEDS-DERIVATION-EXPANSION] flags at step 4 — the corpus works with the sharper exponent
`c(m) = m(m+1)/2 ≥ m`, i.e. in the regime `m ≤ c`, and the abstract packaging drops that relation.

Witness: `Q = 2`, `c = 1`, `m = 2`, `n₀ = 4`, `K' = B' = c' = 0`, `head = beta = 0`, and
`u D N := (9/10)^N` (constant in `D`, and `u D 0 = 1`, so this one is immune to repair (α-0)).
`hsplit`/`halpha` need `Σ_{k<4} 2^(−(k+1)) · (9/10)^(N − 2(k+1)) ≥ (9/10)^N` with `ℕ`-truncated
exponents; the sum's coefficient at `N ≥ 8` is `Σ_{j=1}^{4} (50/81)^j = 1.3788… ≥ 1`, and the
truncated range `1 ≤ N ≤ 7` was checked term by term (`N = 1`: `0.9375 ≥ 0.9`; `N = 3`:
`0.8875 ≥ 0.729`; `N = 7`: `0.6524 ≥ 0.4783`; the full table `N ≤ 59` is clean). The conclusion
would give `(9/10)^M ≤ K · M^3 · (2^(M−1))⁻¹` for all `M ≥ 1`, i.e. `K ≥ 1.8^M / (2 M^3) → ∞`.
Two cells of that divergence are `#guard`ed at the bottom of this file: `K > 10^19` is forced at
`M = 100` and `K > 10^43` at `M = 200`.

**Repair (blueprint-side).** Add `m ≤ c` to `rate_close`'s hypotheses (it holds at every intended
instantiation, `c = c(m) = m(m+1)/2`), or state `halpha` with the sharper exponent
`Q^(−m(m+1)/2 · (k+1))` that H.16/H.17 land, which is what the corpus's locus step actually uses.

### Consequence for the node's `SIZE`/`SPLIT MANDATE`

The blueprint mandates a 3-way split (H.71a the `K`-choice, H.71b the leg bounds, H.71c the
assembly). Nothing is landed of any of the three: with (α-0) and (α-rate) open, H.71b's α-`calc`
is the step that cannot be written, and it is the step both defects sit in. H.71a's `K`-choice
(H.35 `pow_sub_dominance`) and H.71c's `Nat.strongRecOn` assembly are unaffected by the defects
and remain available once the two hypotheses are added.

DEPENDS: H.65 (`RateSpecies`) · H.30, H.35, H.66, H.69, H.70 (the proof's inputs, unused here).

SOURCE: `EFF.GENIND.153` (`ANNEX-THEOREM GENIND.C′`) with its `[ar1, MINOR-1]` `c`-choice rider
(*"`c := c′ + 1` … with `c = c′ + 1` the β-leg's `Q^{−(N−c′−1)} = Q^{−(N−c)}` EXACTLY"*), and the
spec's audit recording the compressed α-leg step: *"The α-leg's two exponent forms are both
correct at their own points but the passage does not spell out the intermediate step between
them."* **That compressed step is defect (α-rate): the two forms are not interchangeable in the
abstract, only under `m ≤ c`.**

TEETH: **PROOF-ONLY** (`EFF.GENIND.153`: *"the induction itself is unguarded — no battery row
exercises a lexicographic induction"*). The ground anchor is H.28. This file's teeth are the two
`RecursionLegs` witnesses: they are the first inhabitants of the structure anywhere in the corpus,
and (α-0)'s is what turns the suspicion into a refutation.

## Status

Sorry-free, axiom-free (Lean core only). **Node incomplete: `rate_close` withheld as REFUTED.**
-/

set_option linter.style.longLine false
-- `hdesc`'s `D` binder is unused BY DESIGN: A-H.1/D7 annotates it (`(D N k : ℕ)`) precisely
-- because the committed field left `D`'s type uninferable, and the signature is frozen, so the
-- binder stays and the unused-variable linter goes off for the file.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- The three-leg recursion hypothesis of `GENIND.C′`, packaged so the induction can be stated.

**Repair record [A-H.1/D6].** The committed SIGNATURE wrote `head alpha beta : ℕ → ℕ → ℝ` and
`B' c' n₀ : ℕ`. Lean 4 structure fields do not admit multiple names — `f a b : T` declares ONE
field `f : (a : _) → (b : _) → T` — so as committed the structure had no `alpha`, `beta`, `c'` or
`n₀` at all and every hypothesis field failed to elaborate. Split one name per field below.

**Repair record [A-H.1/D7].** `hdesc`'s binders are annotated (`D` occurs nowhere else in the
field, so its type was uninferable) and the `1 ≤ N` guard is restored, matching its three sibling
fields. Without the guard the field is FALSE at `N = 0, k = 0` whenever `1 ≤ m ∧ 1 ≤ n₀`
(`0 - m·1 < 0` in `ℕ`), so the structure was uninhabited and the α-leg silently switched off. -/
structure RecursionLegs (Q m c : ℕ) (u : ℕ → ℕ → ℝ) where
  /-- The head (no-drain) leg. -/
  head : ℕ → ℕ → ℝ
  /-- The α (drain-and-recur) leg. -/
  alpha : ℕ → ℕ → ℝ
  /-- The β (lower-degree) leg. -/
  beta : ℕ → ℕ → ℝ
  /-- The β-leg's coefficient, from H.69 at strictly lower degree. -/
  K' : ℝ
  /-- The β-leg's polynomial degree, from H.69. -/
  B' : ℕ
  /-- The β-leg's exponent offset, from H.69. -/
  c' : ℕ
  /-- The α-leg's multiplicity range. -/
  n₀ : ℕ
  hK' : 0 ≤ K'
  hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N
  hu0 : ∀ D N, 0 ≤ u D N
  hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹
  halpha : ∀ D N, 1 ≤ N → alpha D N ≤
    ∑ k ∈ Finset.range n₀, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
  hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹
  hdesc : ∀ (D N k : ℕ), 1 ≤ N → k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N

end Uniformity.Density.Induction

/-! ## The refutation of `rate_close` (DEFECT (α-0)), machine-checked

`uWindowZero D N := D · (2^N)⁻¹` is a legitimate three-leg family at `Q = 2`, `m = c = 1`: the
head and β legs are identically `0`, and the α leg IS the family, because
`u D N = ½ · u D (N−1)` is exactly the single α-summand at `Q = 2, c = 1, n₀ = 1`. Its window-`0`
value `u D 0 = D` is unbounded across `D`, which is what no field forbids and what the conclusion
cannot survive. -/

namespace Uniformity.Density.Induction

/-- The (α-0) counterexample family: `u D N = D · (2^N)⁻¹`. Not part of the node's contract. -/
private noncomputable def uWindowZero : ℕ → ℕ → ℝ := fun D N => (D : ℝ) * ((2 : ℝ) ^ N)⁻¹

/-- Every summand of the α-leg at `Q = 2, m = c = 1, n₀ = 1`, evaluated: for `N ≥ 1` the sum is
`½ · u D (N−1) = u D N`, so `halpha` holds with equality. -/
private theorem uWindowZero_alpha (D N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range 1,
        (((2 : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) ^ (1 * (k + 1)))⁻¹ * uWindowZero D (N - 1 * (k + 1))
      = uWindowZero D N := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  simp only [Finset.sum_range_one, uWindowZero, Nat.cast_ofNat]
  norm_num [pow_succ]
  ring

/-- **The witness.** `RecursionLegs 2 1 1 uWindowZero` — every one of the fourteen fields holds,
`hsplit` and `halpha` with equality. -/
private noncomputable def legsWindowZero : RecursionLegs 2 1 1 uWindowZero where
  head := fun _ _ => 0
  alpha := uWindowZero
  beta := fun _ _ => 0
  K' := 0
  B' := 0
  c' := 0
  n₀ := 1
  hK' := le_rfl
  hsplit := by intro D N _; simp
  hu0 := by intro D N; unfold uWindowZero; positivity
  hhead := by intro D N _; positivity
  halpha := by intro D N hN; exact (uWindowZero_alpha D N hN).ge
  hbeta := by intro D N _; simp
  hdesc := by intro D N k hN hk _; omega

end Uniformity.Density.Induction

section Refutation

open Uniformity.Density.Induction

/-- **DEFECT (α-0), machine-checked.** Had H.71's `rate_close` been landed at its signed type, it
would prove `False`: the hypothesis below is that statement verbatim, and `legsWindowZero`
instantiates it at `Q = 2, m = 1, c = 1`, where its conclusion at window `M = 1` demands
`D/2 ≤ K` for every `D`.

This is an `example` taking the theorem as a hypothesis rather than an `axiom`, precisely so that
nothing false enters the environment (the `G.23a` / D4 / D8 precedent). -/
example
    (rate_close : ∀ {Q m c : ℕ}, 2 ≤ Q → 1 ≤ c → 1 ≤ m → ∀ {u : ℕ → ℕ → ℝ}
      (L : RecursionLegs Q m c u),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D)) :
    False := by
  obtain ⟨K, _, hK⟩ :=
    rate_close (Q := 2) (m := 1) (c := 1) (by norm_num) le_rfl le_rfl legsWindowZero
  -- Pick a degree index whose window-`0` mass exceeds anything `K` can pay for.
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * K)
  have h1 : uWindowZero D 1 ≤ K * ((1 : ℕ) : ℝ) ^ (1 + legsWindowZero.B' + 1)
      * ((((2 : ℕ)) : ℝ) ^ (1 - (legsWindowZero.c' + 1)))⁻¹ := hK D 1 le_rfl
  simp only [legsWindowZero, uWindowZero] at h1
  norm_num at h1
  linarith

end Refutation

/-! ## DEFECT (α-rate): two cells of the divergence, as `#guard`s.

These are **illustrations, not the refutation** — a `#guard` cannot refute an `∃ K`. With
`Q = 2, c = 1, m = 2, n₀ = 4` and `u D N = (9/10)^N` (a family satisfying every `RecursionLegs`
field, checked numerically for `N ≤ 59`), the conclusion `u D M ≤ K · M^3 · (2^(M−1))⁻¹` rearranges
to `9^M · 2^(M−1) ≤ K · M^3 · 10^M`. The two cells below say that `K` would have to exceed `10^19`
at `M = 100` and `10^43` at `M = 200` — so no single `K` works, which is the divergence
`K ≥ 1.8^M / (2 M^3) → ∞` in integer form. -/

section RateDivergence

#guard 9 ^ 100 * 2 ^ 99 > 10 ^ 19 * (100 ^ 3 * 10 ^ 100)
#guard 9 ^ 200 * 2 ^ 199 > 10 ^ 43 * (200 ^ 3 * 10 ^ 200)

end RateDivergence

/-! ## Axiom footprint (the landed declaration only — `rate_close` is not landed) -/

section AxCheck

#print axioms Uniformity.Density.Induction.RecursionLegs
#print axioms Uniformity.Density.Induction.RecursionLegs.mk

end AxCheck
