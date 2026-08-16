/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D08
import Uniformity.ChapD.D12
import Uniformity.ChapD.D15
import Uniformity.ChapD.D17

/-!
# Uniformity.ChapD.D19 — `(C5-monomial-ratio)`: the `ϖ`-comparison and its residue

**Chapter D, NODE D.19** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1, A-D.2 govern — A-D.1/D-D10(i) records that `varpiSection`
is a BLUEPRINT def that §12's inventory omitted, and A-D.1/D-D8 + note SD-3 make
`chi_varpi_mem_ker` a PROVED sibling because the residue corollary cannot be STATED without
it). ENV-D1 + ENV-D2. Four signed declarations.

*`(C5-monomial-ratio)`, the `ϖ`-comparison.* Let `ϖ := n̂₁(1)` be the level-1 normalizer avatar
and `varpiSection e₁ h` the section `k ↦ ϖ^k` (a `NormSection`: powers of a fixed element, so
`n 0 = 1`). Then in the exponent lattice `Multiplicative (ℤ × ℤ)`

* `chi (levelOneSection e₁ h) (varpiSection e₁ h) k = ((e₁, −h))^{−q(k)}` — the corpus's
  `n̂₁(k)/ϖ^k = (x^{e₁}/π^h)^{−q(k)}`, written additively as
  `ofAdd ((−q(k)) • (e₁, −h))`;
* applying D.17's `res`, the residue is `η^{−q(k)}`.

The exponent `q(k)` is D.15's `qexp` and the base `(e₁, −h)` is the exponent pair of
`x^{e₁}/π^h`, i.e. the generator of the value-zero subgroup that D.17's `levelOneHeight_ker_dvd`
identifies.

## The consistency triangle (the STATEMENT's "moreover" clause)

The blueprint's second clause — *`(C5-carry)` (D.15) is exactly the coboundary law (D.12) of
this section pair* — carries **no separate signed name** (the SIGNATURE block signs the four
declarations below and no fifth), so it is landed as the unnamed, machine-checked `example` in
the `ConsistencyTriangle` section at the foot of this file: D.12's `chi_coboundary` applied to
`(levelOneSection, varpiSection)` and rewritten by `chi_varpi` gives
`χ(a)χ(b)/χ(a+b) = (x^{e₁}/π^h)^{wrap(a,b)}` **iff** D.15's `qexp_add` holds, and the `example`
scores the composite. That closure is the A2 regression's content.

## Statability fence (A-D.1 / D-D8) — discharged, not deferred

`res_chi_varpi` applies `(levelOneArena …).res` to a SUBTYPE element, so its membership proof
must mention `(levelOneArena …).v`. Had D.17 landed as an `axiom`, or with an opaque body, this
corollary (and D.21's `levelOne_rho`) would be UNSTATABLE without inventing extra membership
hypotheses. D.17 is landed with the A-D.1/D-D2 real bodies, so the fence is CLEARED here: the
statement below is the signed one, verbatim, and `chi_varpi_mem_ker` is a proved theorem, never
an `axiom`.

⚠ Direction check (the blueprint's own): `chi Nhat N k = n̂(k)·(n(k))⁻¹` (D.12) with
`Nhat := levelOneSection` (the exact-height section) and `N := varpiSection` — matching the
corpus's `n(k)/ϖ^k`, NOT its reciprocal.

## Faithfulness

`varpiSection` is a trust-boundary DEFINITION (`ϖ = n̂₁(1)`, powers thereof). It is spelled
`(levelOneSection e₁ h).n 1 ^ k` — the `zpow` of a fixed lattice point — so `n_zero` is
`zpow_zero` and no separate hypothesis is needed; nothing about `ϖ` beyond "the height-1
normalizer" enters. **Flagged for human review** (definition faithfulness).

DEPENDS: D.12 (`NormSection.chi`, `chi_coboundary`) · D.13 (`iexp`, `aexp`, `iexp_aexp_spec`) ·
D.14 (`wrap`, via D.15) · D.15 (`qexp`, `qexp_add`) · D.17 (`levelOneSection`, `levelOneArena`) ·
D.08 (`GaugeArena.mem_ker_div`, the engine of `chi_varpi_mem_ker`; imported directly — the
blueprint's DEPENDS field lists D.12/D.13/D.15/D.17, and `mem_ker_div` reaches this file only
through D.08, so that import is added and recorded here) ·
mathlib `toAdd_mul`/`toAdd_inv`/`toAdd_zpow`,
`Int.mul_ediv_cancel`, `Nat.isCoprime_iff_coprime` — all name-verified at the v4.31.0 pin.

**PROOF.** 1. Exponent subtraction: `chi` at `k` is the lattice point
`(i(k) − k·i₀, a(k) − k·a₀)`. 2. First coordinate `= −e₁·q(k)`: D.15's defining division
cleared, i.e. `e₁·q(k) = i₀·k − i(k)`, whose exactness is `hcop` (private helper
`qexp_mul_left`, D.15's `key` step re-derived — chapter D's copy is local to `qexp_add`).
3. Second coordinate `= h·q(k)`: subtract the two exact-height identities
`i(k)h + a(k)e₁ = k` and `k·(i₀h + a₀e₁) = k`, then substitute step 2 — "Exponent subtraction
gives the monomial ratio" (`EFF.T1.19`). 4. Residue: D.17's `res` is `(i,a) ↦ η^{i/e₁}` and
`(−q·e₁)/e₁ = −q` exactly (`Int.mul_ediv_cancel`, `e₁ ≠ 0`). 5. The coboundary consistency:
D.12 + D.15, scored as the `example` below. `chi_varpi_mem_ker`'s body is the gate-verified
`leanspec/Leanspec/ChapD.lean` stub body, with the landed namespace restored and its one `show`
spelled `change` (`linter.style.show`, which the isolated stub environment does not run).

SOURCE: `EFF.T1.19` (the boxed `(C5-monomial-ratio)`); `EFF.T1.26` (its first two pinned HETOW
displays are exactly this statement + its residue — consumed at D.27).

**TEETH.** T1 §4.2 check 4 ("guards the `−q(k)` sign") → **Lean theorem** (this node): the sign
is pinned by `chi_varpi`'s `−(qexp e₁ h k)` and again by `res_chi_varpi`'s `η ^ (-(qexp e₁ h k))`,
both of which would fail to elaborate against the opposite convention. The A2 consumption
regression → D.27 + §12. Nothing numeric is scored here (the statements are over an abstract
field `K`); the `η`-power tables run at gates D.65/D.66.

ENVIRONMENT: ENV-D1 + ENV-D2 (`{K : Type*} [Field K]`, `η : Kˣ` and the lattice arena, written
inline per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.19 — the `ϖ`-section.** `ϖ := n̂₁(1)` is the level-1 normalizer avatar and this is the
section `k ↦ ϖ^k` (`EFF.T1.19`). `n_zero` is `zpow_zero`: powers of a FIXED element, so no
exact-height clause is available or claimed — comparing it with `levelOneSection` is exactly
what `(C5-monomial-ratio)` measures.  [A-D.1/D-D10(i): a blueprint `def` that §12's inventory
omitted.] -/
def varpiSection (e₁ h : ℕ) : NormSection (Multiplicative (ℤ × ℤ)) where
  n k := (levelOneSection e₁ h).n 1 ^ k
  n_zero := zpow_zero _

/-- D.15's defining division, CLEARED: `e₁·q(k) = i₀·k − i(k)`.  Private helper — D.15 proves
this inside `qexp_add` as its step `key`, where it is local to that proof; the exactness of the
`Int` division is `hcop`. -/
private theorem qexp_mul_left (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    (e₁ : ℤ) * qexp e₁ h k = (iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ) := by
  have hcopZ : IsCoprime (e₁ : ℤ) (h : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have h1 := (iexp_aexp_spec e₁ h he hcop 1).2
  have hk := (iexp_aexp_spec e₁ h he hcop k).2
  have hmul : ((iexp e₁ h 1 : ℤ) * k - (iexp e₁ h k : ℤ)) * (h : ℤ)
      = (e₁ : ℤ) * (aexp e₁ h k - aexp e₁ h 1 * k) := by
    linear_combination k * h1 - hk
  exact Int.mul_ediv_cancel' (hcopZ.dvd_of_dvd_mul_right ⟨_, hmul⟩)

/-- **D.19 — `(C5-monomial-ratio)`** (`EFF.T1.19`): `n̂₁(k)/ϖ^k = (x^{e₁}/π^h)^{−q(k)}`, written
in the exponent lattice as `ofAdd ((−q(k)) • (e₁, −h))`.

⚠ **direction**: `chi Nhat N k = n̂(k)·(n(k))⁻¹` (D.12) with `Nhat := levelOneSection` and
`N := varpiSection`, matching the corpus's `n(k)/ϖ^k`.  ⚠ **sign**: the exponent is
`−q(k)` — T1 §4.2 check 4. -/
theorem chi_varpi (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (k : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k
      = Multiplicative.ofAdd ((-(qexp e₁ h k)) • ((e₁ : ℤ), -(h : ℤ))) := by
  have hq := qexp_mul_left e₁ h he hcop k
  have h1 := (iexp_aexp_spec e₁ h he hcop 1).2
  have hk := (iexp_aexp_spec e₁ h he hcop k).2
  refine Multiplicative.toAdd.injective (Prod.ext ?_ ?_) <;>
    simp only [NormSection.chi, varpiSection, levelOneSection, toAdd_mul, toAdd_inv, toAdd_zpow,
      toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
  · linear_combination hq
  · refine mul_left_cancel₀ (a := (e₁ : ℤ)) (by exact_mod_cast he.ne') ?_
    linear_combination hk - k * h1 - (h : ℤ) * hq

/-- **D.19 — the value-zero fact** (A-D.1/D-D8, note SD-3): the `χ`-ratio against the
`ϖ`-section lies in the kernel of the level-1 height hom, because BOTH sections sit at height
`k` there (`levelOneSection` by `exact_height`, `varpiSection` because `v` is a hom and
`ϖ` has height `1`).  PROVED, never an `axiom`: without it `res_chi_varpi` below — and D.21's
`levelOne_rho` — cannot be STATED at all. -/
theorem chi_varpi_mem_ker (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (k : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k
      ∈ MonoidHom.ker (levelOneArena e₁ h he hcop η).v := by
  refine (levelOneArena e₁ h he hcop η).mem_ker_div ?_
  have h2 : (levelOneArena e₁ h he hcop η).v ((varpiSection e₁ h).n k)
      = Multiplicative.ofAdd k := by
    change (levelOneArena e₁ h he hcop η).v ((levelOneSection e₁ h).n 1 ^ k) = _
    rw [map_zpow, (levelOneArena e₁ h he hcop η).exact_height]
    simp [← ofAdd_zsmul]
  rw [(levelOneArena e₁ h he hcop η).exact_height, h2]

/-- **D.19 — the residue corollary** (`EFF.T1.19`, `EFF.T1.26`): `res(n̂₁(k)/ϖ^k) = η^{−q(k)}`.
D.17's residue hom is `(i,a) ↦ η^{i/e₁}`, and `chi_varpi` puts the first coordinate at
`−q(k)·e₁`, so the division is exact.  ⚠ this is the statement the A-D.1/D-D8 statability fence
is about — see the module docstring. -/
theorem res_chi_varpi (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    {K : Type*} [Field K] (η : Kˣ) (k : ℤ) :
    (levelOneArena e₁ h he hcop η).res
        ⟨NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k,
          chi_varpi_mem_ker e₁ h he hcop η k⟩
      = η ^ (-(qexp e₁ h k)) := by
  have hne : (e₁ : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  change η ^ ((Multiplicative.toAdd
      (NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) k)).1 / (e₁ : ℤ)) = _
  rw [chi_varpi e₁ h he hcop k]
  simp only [toAdd_ofAdd, Prod.smul_fst, smul_eq_mul]
  rw [Int.mul_ediv_cancel _ hne]

end Uniformity.Density.Gauge

/-! ## The consistency triangle, EXECUTED (the STATEMENT's "moreover" clause)

`(C5-carry)` (D.15) IS the coboundary law (D.12) of the pair `(levelOneSection, varpiSection)`:
the coboundary of `χ` at `(a,b)` is the `wrap(a,b)`-th power of `x^{e₁}/π^h`. Unnamed by
design — the SIGNATURE block of D.19 signs four declarations and no fifth, so this closure is
scored as an `example` rather than added as a public name (GC-6.5). This is the A2 regression's
content. -/

section ConsistencyTriangle

open Uniformity.Density.Gauge

example (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁) (a b : ℤ) :
    NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) a
        * NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) b
        * (NormSection.chi (levelOneSection e₁ h) (varpiSection e₁ h) (a + b))⁻¹
      = Multiplicative.ofAdd ((wrap e₁ h a b : ℤ) • ((e₁ : ℤ), -(h : ℤ))) := by
  rw [chi_varpi e₁ h he hcop a, chi_varpi e₁ h he hcop b, chi_varpi e₁ h he hcop (a + b),
    qexp_add e₁ h he hcop a b]
  refine Multiplicative.toAdd.injective (Prod.ext ?_ ?_) <;>
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

end ConsistencyTriangle

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.varpiSection
#print axioms Uniformity.Density.Gauge.chi_varpi
#print axioms Uniformity.Density.Gauge.chi_varpi_mem_ker
#print axioms Uniformity.Density.Gauge.res_chi_varpi

end AxCheck
