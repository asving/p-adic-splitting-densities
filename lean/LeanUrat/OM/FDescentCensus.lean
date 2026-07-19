/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L3Gauss
import LeanUrat.L3Squarefree
import LeanUrat.OM.Necklace
import LeanUrat.OM.Order0Count
import LeanUrat.OM.ResidueCount

/-!
# LeanUrat.OM.FDescentCensus — the `f ≥ 2` child census reduces to the `f = 1` census at `q ↦ q^f`

Wave **W6b-f** (tier 1, the tractable census reduction). Blueprint §3 (two-step descent) records
that the residue-degree-`f` child restart over the unramified residue extension
`F_{q^f} = 𝔽_{p^{k·f}}` has the **same census** as the base `f = 1` restart over `F_q = 𝔽_{p^k}`,
with the single substitution `q ↦ q^f`. The mathematics is field-generic: every residual /
child-stratum count in `lean_urat` (`L3.card_monicDegree`, `L3Squarefree.card_squarefreeMonicDegree`,
`M0.nonSquarefreeMonicCount`, `Order0.necklaceQ_eq_card`, `Order0.card_sepStratum`) is a **universal
polynomial in `Q = Nat.card F`**. Instantiating those counts at the residue tower

* base   `F₁ := GaloisField p k`      with `Nat.card F₁ = p^k = q`,
* child  `F_f := GaloisField p (k·f)` with `Nat.card F_f = p^{k·f} = (p^k)^f = q^f`,

turns "the child census over `F_f`" into "the base census over `F₁` at the argument `q^f`" — the same
polynomial, evaluated at `q^f`. No new counting is proved here; the wave banks the *specialisation*.

## Contents (W6b-f deliverables)

1. **GaloisField card bridge** (`§1`): `galoisField_card_eq_q_pow_f`
   `Nat.card (GaloisField p (k*f)) = (p^k)^f`, i.e. `= q^f` with `q = p^k = Nat.card (GaloisField p k)`
   (`card_base_eq`). Instantiations of `mathlib`'s `GaloisField.card` (needs `[Fact p.Prime]`,
   exponent `≠ 0`) with `pow_mul`.
2. **Census reduction** (`§2`, the core): each field-generic residual/child count instantiated at
   `F = GaloisField p (k*f)` equals the `f = 1` census polynomial at `q^f`:
   * `monicCensus_f_eq_q_pow_f`         — `#monic deg m = (q^f)^m`;
   * `squarefreeCensus_f_eq_q_pow_f`    — `#squarefree monic deg m = (q^f)^m − (q^f)^{m-1}`;
   * `residualCensus_f_eq_q_pow_f`      — **the `T_BB3` residual oracle** `#non-squarefree deg m = (q^f)^{m-1}`;
   * `irreducibleCensus_f_eq_q_pow_f`   — `#Irr_d = necklaceQ d (q^f)` (the necklace value at `q^f`);
   * `shapeCensus_f_eq_q_pow_f`         — **the shape/necklace-poly census** `#sepStratum P = ∏_d C(avail F_f d, count_d)`,
     with every pool size `avail F_f d` read at `q^f` (`avail_f_eq_q_pow_f`).
   The head reduction `residualCensus_child_eq_base_at_q_pow_f` states it as the base-vs-child
   equality: the child census equals the base census with `q ↦ q^f`.
3. **Conjugate-block tier** (`§3`): the `f` Galois-conjugate blocks `G, Frob G, …, Frob^{f-1} G` of a
   degree-`f` child factor are pinned by `G` up to the residue Frobenius orbit. At the *census* level
   the block-count is the divisor identity `∑_{e ∣ d} e·N_e(F_f) = (Nat.card F_f)^d = (q^f)^d`
   (`L3Gauss.sum_e_mul_card_eq_pow`, the Frobenius-orbit partition of `F_f^d` by minimal-polynomial
   degree), instantiated at `F_f` (`conjugateBlock_orbit_count`). The *action-level* Frobenius-orbit
   bijection on `GaloisField p (k·f)` (the explicit `f`-to-`1` Weil-restriction map) is heavier than
   the census and is NAMED, not built (see §4, W6b-f2).

## §4 — Out of scope (NAMED, not built): the `O''`-ring digit restart at `f ≥ 2` (W6b-f2)

The full **digit-level** restart at `f ≥ 2` — `RphiExt = O''[X]/(X^e − c·p^h)` over the *unramified
degree-`f` ring* `O''` at level `N`, with residue field `GaloisField p (k·f)`, and the digit-level
`restartEquiv` analogue (cf. `LeanUrat.OM.RestartEquiv` / `RphiRing` at `f = 1`) — is INFRASTRUCTURE:
it needs the level-`N` unramified extension ring `O''` as a *new object* (the Witt/Teichmüller lift of
`GaloisField p (k·f)` truncated at level `N`), which does not yet exist in `lean_urat`. That object,
and the `restartEquiv`-analogue over it, is the follow-up wave **W6b-f2** and is deliberately OUT OF
SCOPE here. This module banks only the census tier (1)+(2) and the census-level orbit count (3); it
introduces no `O''` ring, and it contains no `sorry`/`axiom`.

Everything below is a thin field-generic specialisation of already-proved, `sorry`-free counts.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.FDescentCensus

open Polynomial

/-! ## §1 — GaloisField card bridge: `#𝔽_{p^{k·f}} = (p^k)^f = q^f` -/

section CardBridge

variable (p : ℕ) [Fact p.Prime] (k f : ℕ)

/-- **Base residue-field size.** `Nat.card (GaloisField p k) = p^k = q` (needs `k ≠ 0`). -/
theorem card_base_eq (hk : k ≠ 0) :
    Nat.card (GaloisField p k) = p ^ k :=
  GaloisField.card p k hk

/-- **GaloisField card bridge (the W6b-f card specialisation).** The residue-degree-`f` child field
`GaloisField p (k·f)` has `p^{k·f} = (p^k)^f = q^f` elements — the base size `q = p^k` raised to the
descent degree `f`. This is exactly the `q ↦ q^f` substitution at the level of cardinalities, and it
lets every field-generic count (which depends on `F` only through `Nat.card F`) specialise from the
base to the child. -/
theorem galoisField_card_eq_q_pow_f (hkf : k * f ≠ 0) :
    Nat.card (GaloisField p (k * f)) = (p ^ k) ^ f := by
  rw [GaloisField.card p (k * f) hkf, pow_mul]

/-- **Card bridge in `q`-form.** Writing `q = Nat.card (GaloisField p k)`, the child field has `q^f`
elements. This is the form consumed by the census reductions of §2 ("the base census at `q^f`"). -/
theorem galoisField_card_eq_base_pow (hk : k ≠ 0) (hkf : k * f ≠ 0) :
    Nat.card (GaloisField p (k * f)) = (Nat.card (GaloisField p k)) ^ f := by
  rw [galoisField_card_eq_q_pow_f p k f hkf, card_base_eq p k hk]

end CardBridge

/-! ## §2 — Census reduction: the `f ≥ 2` child census is the `f = 1` census at `q^f`

Each residual/child count is field-generic in `Q = Nat.card F`. Instantiating at
`F = GaloisField p (k·f)` and rewriting `Nat.card = q^f` via §1 gives the base census polynomial at
`q^f`. We abbreviate `q := p^k` throughout (`= Nat.card (GaloisField p k)`, the `f = 1` base size). -/

section CensusReduction

variable (p : ℕ) [Fact p.Prime] (k f : ℕ) (hkf : k * f ≠ 0)

include hkf

/-- **Monic census reduction.** `#{monic deg m over 𝔽_{q^f}} = (q^f)^m` — the `f = 1` monic census
polynomial `Q^m` evaluated at `Q = q^f`. (`L3.card_monicDegree` at `F = GaloisField p (k·f)`.) -/
theorem monicCensus_f_eq_q_pow_f (m : ℕ) :
    Nat.card (L3.monicDegree (GaloisField p (k * f)) m) = ((p ^ k) ^ f) ^ m := by
  rw [L3.card_monicDegree, galoisField_card_eq_q_pow_f p k f hkf]

/-- **Squarefree-monic census reduction.** `#{squarefree monic deg m over 𝔽_{q^f}} = (q^f)^m − (q^f)^{m-1}`
— the `f = 1` squarefree census polynomial `Q^m − Q^{m-1}` at `Q = q^f` (`m ≥ 2`).
(`L3Squarefree.card_squarefreeMonicDegree` at `F = GaloisField p (k·f)`.) -/
theorem squarefreeCensus_f_eq_q_pow_f (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (L3.squarefreeMonicDegree (GaloisField p (k * f)) m)
      = ((p ^ k) ^ f) ^ m - ((p ^ k) ^ f) ^ (m - 1) := by
  rw [L3Squarefree.card_squarefreeMonicDegree _ hm, galoisField_card_eq_q_pow_f p k f hkf]

/-- **Residual census reduction — the `T_BB3` oracle at `f ≥ 2`.** The descent-triggering
(non-squarefree) monic degree-`m` count over the child field `𝔽_{q^f}` is `(q^f)^{m-1}` — exactly the
`f = 1` residual census `Q^{m-1}` at `Q = q^f` (`m ≥ 2`). This is the residue-degree-`f` analogue of
the residual box factor `(q^δ)^{d_S-1}`, now with `q ↦ q^f`.
(`M0.nonSquarefreeMonicCount` at `F = GaloisField p (k·f)`.) -/
theorem residualCensus_f_eq_q_pow_f (m : ℕ) (hm : 2 ≤ m) :
    Nat.card {R : (GaloisField p (k * f))[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}
      = ((p ^ k) ^ f) ^ (m - 1) := by
  rw [M0.nonSquarefreeMonicCount (F := GaloisField p (k * f)) m hm,
    galoisField_card_eq_q_pow_f p k f hkf]

/-- **Irreducible / necklace census reduction.** The number of monic irreducible degree-`d`
polynomials over the child field `𝔽_{q^f}` equals the necklace value `necklaceQ d (q^f)` — the
`f = 1` necklace count polynomial evaluated at the alphabet size `q^f`
(`Order0.necklaceQ_eq_card` at `F = GaloisField p (k·f)`, rewriting `Nat.card = q^f`). -/
theorem irreducibleCensus_f_eq_q_pow_f (d : ℕ) (hd : 1 ≤ d) :
    (Nat.card (L3.monicIrreducibleDegree (GaloisField p (k * f)) d) : ℚ)
      = Necklace.necklaceQ d ((p ^ k) ^ f) := by
  rw [← Order0.necklaceQ_eq_card (GaloisField p (k * f)) d hd,
    galoisField_card_eq_q_pow_f p k f hkf]

/-- **Pool-size reduction.** The punctured degree-`d` factor pool `avail F d` over the child field is
read at `q^f`: `avail F_f 1 = q^f − 1`, and `avail F_f d = #Irr_d = necklaceQ d (q^f)` for `d ≠ 1`.
Both branches are the `f = 1` pool sizes with `q ↦ q^f`. -/
theorem avail_f_eq_q_pow_f (d : ℕ) :
    Order0.avail (GaloisField p (k * f)) d
      = if d = 1 then (p ^ k) ^ f - 1
        else Nat.card (L3.monicIrreducibleDegree (GaloisField p (k * f)) d) := by
  rcases eq_or_ne d 1 with rfl | hd
  · rw [Order0.avail_one, galoisField_card_eq_q_pow_f p k f hkf, if_pos rfl]
  · rw [Order0.avail_of_ne_one _ hd, if_neg hd]

/-- **Shape / necklace-polynomial census reduction (the full residual-shape count).** For a
factor-degree partition `P` of `n`, the child-field count of squarefree monics with factor-degree
multiset `P.parts` is the product of binomials `C(avail F_f d, count_d)` over the pool sizes read at
`q^f`. This is the `f = 1` shape-count polynomial `∏_d C(avail_d, count_d)` with `q ↦ q^f`: it is the
same universal polynomial in `Q` (each `avail_d` is a polynomial in `Q` via `necklaceQ`), evaluated at
`Q = q^f`. (`Order0.card_sepStratum` at `F = GaloisField p (k·f)`; the `q^f` substitution is exposed
per-pool through `avail_f_eq_q_pow_f`.) The residue field `GaloisField p (k·f)` is finite, hence
carries a (classical) `DecidableEq`; we take it as an instance argument, following the
`L3Squarefree`/`Order0Count` house pattern (the `Nat.card` value is independent of the choice). -/
theorem shapeCensus_f_eq_q_pow_f [DecidableEq (GaloisField p (k * f))] (n : ℕ) (P : n.Partition) :
    Nat.card (Order0.sepStratum (GaloisField p (k * f)) n P)
      = ∏ d ∈ P.parts.toFinset,
          (Order0.avail (GaloisField p (k * f)) d).choose (P.parts.count d) :=
  Order0.card_sepStratum (GaloisField p (k * f)) n P

/-! ### The base-vs-child head statement: child census = base census at `q ↦ q^f`

We now state the reduction in its "same polynomial, `q ↦ q^f`" form directly against the base field
`F₁ = GaloisField p k` (whose `Nat.card = q`). The child residual census over `F_f` equals the base
residual census read at the base size raised to `f`. -/

/-- **W6b-f core (base-vs-child, residual oracle).** The residue-degree-`f` child residual census
over `F_f = GaloisField p (k·f)` equals the base (`f = 1`) residual census polynomial `Q^{m-1}`
evaluated at `Q = q^f = (Nat.card F₁)^f`, i.e. the base census with the single substitution
`q ↦ q^f`. Concretely both sides are `(p^k)^{f·(m-1)}`. -/
theorem residualCensus_child_eq_base_at_q_pow_f (hk : k ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    Nat.card {R : (GaloisField p (k * f))[X] // R.Monic ∧ R.natDegree = m ∧ ¬ Squarefree R}
      = (Nat.card (GaloisField p k) ^ f) ^ (m - 1) := by
  rw [residualCensus_f_eq_q_pow_f p k f hkf m hm, card_base_eq p k hk]

/-- **W6b-f core (base-vs-child, monic census).** Same statement for the ambient monic census:
child `#monic deg m` over `F_f` is the base census `Q^m` at `Q = (Nat.card F₁)^f = q^f`. -/
theorem monicCensus_child_eq_base_at_q_pow_f (hk : k ≠ 0) (m : ℕ) :
    Nat.card (L3.monicDegree (GaloisField p (k * f)) m)
      = (Nat.card (GaloisField p k) ^ f) ^ m := by
  rw [monicCensus_f_eq_q_pow_f p k f hkf m, card_base_eq p k hk]

end CensusReduction

/-! ## §3 — Conjugate-block count (census level)

A degree-`d` child factor `G` over `𝔽_{q^f}` has `d` Galois conjugates `G, Frob G, …, Frob^{d-1} G`
under the residue Frobenius; the conjugates are pinned by `G` (they are the Frobenius orbit of a
single root). At the **census** level, the count of such blocks is governed by the divisor identity
that partitions `𝔽_{q^f}^d = F_f^{⊕d}` — equivalently the degree-`d` field elements — by the degree of
their minimal polynomial:

`∑_{e ∣ d} e · N_e(F_f) = (Nat.card F_f)^d = (q^f)^d`,

where `N_e = #{monic irreducible deg e}` counts the size-`e` Frobenius orbits (each contributing `e`
elements). This is `L3Gauss.sum_e_mul_card_eq_pow` instantiated at the child field, with the `q ↦ q^f`
substitution of §1. The explicit Frobenius-orbit *bijection* on `GaloisField p (k·f)` (the
action-level Weil-restriction map) is heavier and is NAMED in §4, not built. -/

section ConjugateBlock

variable (p : ℕ) [Fact p.Prime] (k f : ℕ) (hkf : k * f ≠ 0)

include hkf

/-- **Conjugate-block orbit count (census level).** Over the child field `F_f = 𝔽_{q^f}`, the
Frobenius-orbit partition of the degree-`d` elements by minimal-polynomial degree gives
`∑_{e ∣ d} e · N_e = (q^f)^d`, where `N_e = #{monic irreducible deg e}` is the number of size-`e`
Galois-conjugate blocks. This is the census-level statement of the `f` conjugate blocks
`G, Frob G, …` (each degree-`e` block is one Frobenius orbit of `e` roots), with `q ↦ q^f`.
(`L3Gauss.sum_e_mul_card_eq_pow` at `F = GaloisField p (k·f)`.) -/
theorem conjugateBlock_orbit_count (d : ℕ) (hd : 1 ≤ d) :
    (∑ e ∈ d.divisors, e * Nat.card (L3.monicIrreducibleDegree (GaloisField p (k * f)) e))
      = ((p ^ k) ^ f) ^ d := by
  rw [L3Gauss.sum_e_mul_card_eq_pow (F := GaloisField p (k * f)) d hd,
    galoisField_card_eq_q_pow_f p k f hkf]

end ConjugateBlock

end LeanUrat.OM.FDescentCensus
