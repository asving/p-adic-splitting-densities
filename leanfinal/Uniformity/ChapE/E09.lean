/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E02
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E09 — `useSite_margin`, the use-site margin of the level-1 calls

**Chapter E, NODE E.09** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §3, as amended by A-E.1),
ENV-E1 (the arithmetic arena: exponent and threshold bookkeeping on a rung datum, no carrier).

The single `ℕ`-arithmetic fact that makes the HE6-1L coset correction NON-PROPAGATING at every
HE7 use site. Read `R = (ℓ, d_r, u, D′h)` as the level-2 rung (E.01): a level-1 call is made at
height `k` written in the rung's slot coordinates `k = ℓ·m₀ + s₀·u` with `s₀ < ℓ`, the use-site
condition is `k > T₂ = ℓ d_r·u = R.nextT` (E.02), and the call's `t`-th slot (`t < g`) sits at
`m_t = m₀ − t·u`. The lemma's two clauses are the cleared (division-free) forms of the corpus's
two displayed inequalities `m_t > λ` and `m_t > T`:

* `R.ℓ * (m₀ - t * R.u) > R.u` — the cleared `m_t > λ = u/ℓ`;
* `m₀ - t * R.u > R.T` — hence, with `T = D′h`, the margin `m_t − (D′−1)h > h ≥ 1`
  that `EFF.HE7.25` reports.

The second clause is where E.01's **node condition** `ℓ * T < u` (`hnode`, i.e. `λ > T`) is
spent: it converts the first clause's `ℓ·m_t > u` into `ℓ·m_t > ℓ·T` and cancels `ℓ ≥ 1`.

⚠ **THE ℕ-SUBTRACTION IS NOT A TRUNCATION HERE, AND THE PROOF SHOWS IT.** `m₀ - t * R.u` is
truncated `ℕ` subtraction, so the statement would be VACUOUSLY reassuring if `t * R.u` could
exceed `m₀` (both clauses would then read `0 > R.u` / `0 > R.T`, i.e. would be FALSE, not
trivially true — truncation here weakens nothing, it would break the lemma). The proof
establishes `t * R.u < m₀` as an intermediate step (`hle`) from the same hypotheses and then
eliminates the subtraction by writing `m₀ = t * R.u + m`; the clauses are proved of the honest
`m`. A consumer may therefore read `m₀ - t * R.u` as a genuine difference.

HONESTY (blueprint E-1). This node is transcribed arithmetic, NOT an adjudication: the HE7
residual recorded at honesty E-1 concerns OTHER HE6 spans, and `EFF.HE7.25`'s verdict — "the
r1-corrected level-1 threshold is satisfied with margin > h at every §S4.3 use site, so no
statement of this note moves" — is a margin CHECK whose inequality chain is exactly what is
proved below.

DEPENDS: E.01 (`RungDatum`, `hnode`), E.02 (`nextT`, `slotCount`) · mathlib `Nat.mul_le_mul_left`,
`Nat.mul_le_mul_right`, `Nat.lt_of_mul_lt_mul_left`, `ring`.

PROOF SHAPE (the corpus display, cleared). From `hk` and `s₀ + 1 ≤ ℓ`:
`ℓ(t·u) + u + s₀u = ℓ(t·u) + (s₀+1)u ≤ ℓ(t·u) + ℓu = ℓ((t+1)u) ≤ ℓ(g·u) = ℓg·u < ℓm₀ + s₀u`,
cancel `s₀u`: `ℓ(t·u) + u < ℓm₀`. That single inequality yields both clauses.

SOURCE: `EFF.HE7.25` (the displayed chain "`m₀ = (k − s₀u)/ℓ ≥ (k − (ℓ−1)u)/ℓ > (ℓd_r·u −
(ℓ−1)u)/ℓ = (d_r − 1)u + u/ℓ = (d_r − 1)u + λ`" and "`m_t = m₀ − t·u ≥ m₀ − (d_r−1)u > λ > D′h >
(D′−1)h`, margin `m_t − (D′−1)h > λ − (D′−1)h > h ≥ 1`"); `EFF.HE7.24` (§S4.3's chain
`u₂ = ℓ₂κ₂ > ℓ₂T₂ ≥ T₂`, which supplies `huse` at the two use classes).

TEETH: no direct tooth (a hypothesis-margin check, `EFF.HE7.25`); its consequence is exercised
wherever (LIFT₂) fires (Q3's frames) → **Lean theorem** (this node).

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. `useSite_margin` reports exactly the Lean-core triple
`{propext, Classical.choice, Quot.sound}` — these arrive through mathlib's ordered-algebra
instance graph (`lt_of_le_of_lt`, `ring`), not through any project axiom. The type is checked
against the signed SIGNATURE verbatim (hypothesis names, order and binder explicitness
unchanged from `blueprint/CHAP-E_sigma_ladder.md` NODE E.09).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.09** the use-site margin: at a level-1 call made above the rung's next threshold
(`R.nextT < k`, `EFF.HE7.24`'s use-site condition), every consumed slot `t < R.g` of the
development `k = ℓ·m₀ + s₀·u` sits strictly above the slope (`ℓ·m_t > u`, the cleared
`m_t > λ`) and strictly above the threshold (`m_t > T`) — `EFF.HE7.25`'s margin chain. -/
theorem useSite_margin (R : RungDatum) {k m₀ s₀ t : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (huse : R.nextT < k) (ht : t < R.g) :
    R.ℓ * (m₀ - t * R.u) > R.u ∧ m₀ - t * R.u > R.T := by
  -- Unfold the use-site condition to `ℓ·g·u < ℓ·m₀ + s₀·u` (E.02's two definitions, then `hk`).
  simp only [RungDatum.nextT, RungDatum.slotCount] at huse
  rw [← hk] at huse
  -- `s₀ ≤ ℓ − 1` and `t ≤ g − 1`, cleared of subtraction.
  have h1 : (s₀ + 1) * R.u ≤ R.ℓ * R.u := Nat.mul_le_mul_right _ hs
  have h2 : R.ℓ * ((t + 1) * R.u) ≤ R.ℓ * (R.g * R.u) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ht)
  -- `EFF.HE7.25`'s chain, with `s₀·u` carried on both sides so nothing is subtracted.
  have hchain : R.ℓ * (t * R.u) + R.u + s₀ * R.u < R.ℓ * m₀ + s₀ * R.u :=
    calc R.ℓ * (t * R.u) + R.u + s₀ * R.u
        = R.ℓ * (t * R.u) + (s₀ + 1) * R.u := by ring
      _ ≤ R.ℓ * (t * R.u) + R.ℓ * R.u := Nat.add_le_add_left h1 _
      _ = R.ℓ * ((t + 1) * R.u) := by ring
      _ ≤ R.ℓ * (R.g * R.u) := h2
      _ = R.ℓ * R.g * R.u := by ring
      _ < R.ℓ * m₀ + s₀ * R.u := huse
  have hkey : R.ℓ * (t * R.u) + R.u < R.ℓ * m₀ := Nat.lt_of_add_lt_add_right hchain
  -- The ℕ-subtraction is honest: `t·u < m₀` (cancel `ℓ ≥ 1` in `ℓ(t·u) < ℓm₀`).
  have hlt : R.ℓ * (t * R.u) < R.ℓ * m₀ := lt_of_le_of_lt (Nat.le_add_right _ _) hkey
  have hle : t * R.u ≤ m₀ := le_of_lt (Nat.lt_of_mul_lt_mul_left hlt)
  obtain ⟨m, hm⟩ : ∃ m, m₀ = t * R.u + m := ⟨m₀ - t * R.u, (Nat.add_sub_cancel' hle).symm⟩
  subst hm
  rw [Nat.mul_add] at hkey
  -- Clause 1: `ℓ·m > u`.
  have hu : R.u < R.ℓ * m := Nat.lt_of_add_lt_add_left hkey
  -- Clause 2: the node condition `ℓ·T < u` chains through and cancels `ℓ ≥ 1`.
  have hT : R.T < m := Nat.lt_of_mul_lt_mul_left (lt_trans R.hnode hu)
  rw [Nat.add_sub_cancel_left]
  exact ⟨hu, hT⟩

/-! ## Non-vacuity gate (executed `example`s, not blueprint declarations)

`useSite_margin`'s hypotheses are a four-way conjunction on `(k, m₀, s₀, t)` over a rung that
already satisfies E.01's `hcop`/`hnode`; a lemma whose hypotheses were jointly unsatisfiable
would still typecheck. The gate exhibits a legal rung and fires the theorem at both ends of the
slot range, so the conclusion is asserted of real numbers. -/

section Gate

/-- A legal level-2 rung: `(ℓ, g, u, T) = (2, 2, 5, 2)` — coprime slope `5/2`, node condition
`2·2 = 4 < 5`. Its derived data (E.02): `slotCount = 4`, `nextT = 20`. -/
private def gateRung : RungDatum where
  ℓ := 2
  g := 2
  u := 5
  T := 2
  hℓ := by norm_num
  hg := by norm_num
  hcop := by decide
  hnode := by norm_num

-- `k = 21 > 20 = nextT`, written as `2·8 + 1·5`; slot `t = 0` gives `m₀ = 8`.
example : gateRung.ℓ * (8 - 0 * gateRung.u) > gateRung.u ∧ 8 - 0 * gateRung.u > gateRung.T :=
  useSite_margin gateRung (k := 21) (s₀ := 1) (by decide) (by decide) (by decide) (by decide)

-- The last consumed slot `t = g − 1 = 1`: `m_1 = 8 − 5 = 3`, still `2·3 = 6 > 5` and `3 > 2`.
example : gateRung.ℓ * (8 - 1 * gateRung.u) > gateRung.u ∧ 8 - 1 * gateRung.u > gateRung.T :=
  useSite_margin gateRung (k := 21) (s₀ := 1) (by decide) (by decide) (by decide) (by decide)

-- The margin is real, not slack: at `t = 1` the two clauses read `6 > 5` and `3 > 2`, so a rung
-- one notch coarser (`m₀ = 7`, i.e. `k = 19 ≤ nextT`) would fail the USE-SITE hypothesis rather
-- than the conclusion — the `huse` guard is what carries the margin.
example : ¬ (gateRung.nextT < 19) := by decide

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.useSite_margin

end AxCheck
