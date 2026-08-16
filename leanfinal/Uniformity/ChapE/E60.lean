/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E07

/-!
# Uniformity.ChapE.E60 — THEOREM HE7.C, schema form: the ladder is finite at every degree

**Chapter E, NODE E.60** [theorem] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §8), ENV-E1. One
signed declaration, `ladder_finite_bounds`, landed **at the A-E.1/E-D11 REPAIRED signature** —
see the next section, which is the one thing to read before consuming this node.

The four clauses, over a read history's mass sequence `μ : ℕ → ℕ` with `J` level jumps:

1. `1 ≤ J → 2 ^ (J + 1) ≤ μ 0` — the jump count is logarithmic in the initial mass
   (`EFF.HE7.15`'s `J ≤ log₂ μ − 1 ≤ log₂ n − 2`, cleared of division and of the logarithm);
2. `μ 0 = 4 → J ≤ 1` — the `n = 8` frame admits at most one jump;
3. `μ 0 ≤ 7 → ∀ 1 ≤ i ≤ J, μ i ≤ 3` — COROLLARY HE7.B(i)'s `μ₂ ≤ ⌊7/2⌋ = 3`, which is what
   gives the `n ≤ 15` coverage;
4. `2 ≤ J → 8 ≤ μ 0` — ANNEX R R3's rider, in the NECESSARY direction only: two jumps need mass
   8, i.e. *"level 3 / J = 2 is unreachable below n = 16; n = 16 is the first degree NOT EXCLUDED
   by the bound"*. No existence is claimed at `n = 16`; E.64 does the `n`-reading.

## ⚠ THE SIGNATURE IS THE REPAIRED ONE (A-E.1/E-D11), NOT THE `leanspec` STUB

`leanspec/Leanspec/ChapE.lean:1200-1203` still carries the pre-repair form
`(h4 : ∀ i ≤ J, 4 ≤ μ i)` with an unguarded clause 1; the stub file's own §0 note records that
E-D11 is statement-level, that statement-level defects are repaired blueprint-side, and that the
blueprint is the authority. What landed here is the blueprint's repaired signature:

* `h4` ranges over `i < J` — the states the jumps START from, not the ones they open;
* clause 1 is guarded by `1 ≤ J`.

`EFF.HE7.15` asserts the `μ ≥ 4` floor of *"a node requiring a level jump"* and asserts of the
problem that node *opens* only the halving `μ₂ ≤ μ/(ℓ·d_r) ≤ μ/2`. Under the committed
`∀ i ≤ J` the floor lands on the targets too, and then: clause 3's antecedent is unsatisfiable at
`J ≥ 1` (`2·μ 1 ≤ μ 0 ≤ 7` forces `μ 1 ≤ 3`, contradicting `4 ≤ μ 1`), so clause 3 was provable
and said nothing; clause 2 was slack; and all three configurations the corpus itself names —
`n = 8` (`μ = 4 → 2`), the HE7.B(i) edge (`μ = 7 → 3`), and ANNEX R R1.3's constructed `n = 16`
family (`μ = 8 → 4 → 2`, 79/79 machine witnesses) — were INADMISSIBLE. The last of these is the
decisive check: a hypothesis set that excludes the corpus's own machine-exhibited witness family
is wrong independently of the vacuity finding. All three are fired as gates at the end of this
file, together with the machine record that the committed form excludes them.

The `1 ≤ J` guard is forced and honest: with no jump the hypotheses are empty and
`2 ^ (0+1) ≤ μ 0` — "the mass is at least 2" — is not a corpus claim, since a terminal `μ = 1`
leaf is a configuration (`EFF.HE7.15` DERIVATION: *"μ = 1: a single irreducible factor of the
current key's degree, σ read off"*). The over-strong floor had been silently supplying it. The
gate `guard_is_necessary` exhibits the counterexample.

Nothing is weakened by the repair beyond `J = 0`, where the source claims nothing, and no
hypothesis is added that the source lacks. Full record, including the exhaustive sweep
(`μ ≤ 64`, `J ≤ 5`: 24,576 admissible sequences, zero counterexamples to any clause) and the
rejected alternative, is AMENDMENT A-E.1/E-D11 at the end of the blueprint.

## What does the work

Clause 1 IS E.07(iii) `jump_count_bound`, already landed at the repaired hypotheses
(`ChapE/E07.lean:83`); this node consumes it by name and does not re-run its induction. Clause 4
is clause 1 plus `2 ^ 3 ≤ 2 ^ (J + 1)`, and clause 2 is clause 4 contrapositively.

Clause 3 is the one worth reading. It uses **no floor at all** — only the halving chain — which
is precisely why imposing the floor on the jump target killed it. The local induction `hanti`
(`∀ j ≤ J, μ j ≤ μ 0`, from `μ (j+1) ≤ 2 · μ (j+1) ≤ μ j`) transports `μ 0 ≤ 7` down to
`μ (i−1) ≤ 7`, and then `hh (i−1) : 2 · μ i ≤ μ (i−1)` gives `μ i ≤ 3` by `omega` — the ℕ-division
form, so the `[r2, HE7-PE1 F-3]` floor-vs-round defect cannot recur here.

## Faithfulness

**⚠ Three recasts to check on the chapter cross-read.**

* *this is a SCHEMA over an abstract mass sequence, not a statement about read histories.* `μ` is
  any function `ℕ → ℕ` and `J` any bound satisfying the two hypotheses; that a real read history
  supplies them is the instances' obligation (`μ i` = the interface's `Σ len`, E.12's `hlen_sum`;
  the floor is E.59's `block_jump_gate` at each jump; the halving is E.07(ii)/E.17(ii)). The
  statement is pure ℕ-arithmetic and the blueprint says so.
* *"the read tree is finite" is NOT this theorem.* Clause (iv) of the node's prose — interleaved
  α-refines are finite (E.55), every other step strictly decreases `μ` (E.17/E.18) — is the
  packaging COMMENT; the composition into a finiteness statement is E.20's engine with E.55
  discharging the within-level well-foundedness. Reading `ladder_finite_bounds` as termination is
  the error the §14 cross-read entry warns about.
* *clause 4 is the necessary direction only.* `2 ≤ J → 8 ≤ μ 0` says two jumps REQUIRE mass 8. It
  does not say mass 8 admits two jumps; that direction is machine evidence (ANNEX R R1.3's
  family, fired below as an admissibility gate) and is never cited as a theorem.

**DEPENDS.** E.07 (`jump_count_bound`, imported and consumed by name). E.17 (`child_mass`, the
per-step halving supplier) and E.55 (the α-refine finiteness leg) are cited in the packaging
comment above; neither enters the statement, so neither is imported.

**SOURCE.** `EFF.HE7.15` (THEOREM HE7.C `[r1]`, statement + DERIVATION verbatim; ANNEX R R3's
rider); `EFF.HE7.16`(i) (COROLLARY HE7.B(i), the `μ ≤ 7 ⟹ μ₂ ≤ ⌊7/2⌋ = 3` floor, `[r2,
HE7-PE1 F-3]` repair); `EFF.HE7.57` (the `n = 8` frame's `μ₂ = 2`); AMENDMENT A-E.1/E-D11 (the
hypothesis range, the guard, the sweep and the witness table).

**TEETH.** Q1 (`n = 8`: one jump, `μ₂ = 2`, everywhere) + `he7annex_supp.py` (the `n = 16`
constructed family) → **Lean theorem**, necessary directions only; the three named configurations
are re-fired as gates below.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Ladder

/-- **NODE E.60 — THEOREM HE7.C, schema form** *[signed at the A-E.1/E-D11 repair: `h4` ranges
over the jump STARTS `i < J`, and clause 1 carries the `1 ≤ J` guard]*.

For a mass sequence `μ` whose `J` jump starts clear the floor `4` and whose jumps halve the mass:
(1) the jump count is logarithmic, `2 ^ (J+1) ≤ μ 0`; (2) at `μ 0 = 4` there is at most one jump;
(3) at `μ 0 ≤ 7` every jump target has mass `≤ 3` (COROLLARY HE7.B(i) — the `n ≤ 15` coverage);
(4) two jumps require `μ 0 ≥ 8` (ANNEX R R3's rider, necessary direction). -/
theorem ladder_finite_bounds (μ : ℕ → ℕ) (J : ℕ)
    (h4 : ∀ i < J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    (1 ≤ J → 2 ^ (J + 1) ≤ μ 0) ∧ (μ 0 = 4 → J ≤ 1)
    ∧ (μ 0 ≤ 7 → ∀ i, 1 ≤ i → i ≤ J → μ i ≤ 3)
    ∧ (2 ≤ J → 8 ≤ μ 0) := by
  -- Clause 1 is E.07(iii), landed at exactly these hypotheses; nothing is re-proved here.
  have c1 : 1 ≤ J → 2 ^ (J + 1) ≤ μ 0 := fun hJ => jump_count_bound μ J hJ h4 hh
  -- Clause 4: at `J ≥ 2` the bound already passes `2 ^ 3`.
  have c4 : 2 ≤ J → 8 ≤ μ 0 := by
    intro hJ
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ μ 0 := c1 (by omega)
  -- The halving chain alone makes the mass antitone up to `J`. No floor is used, which is what
  -- keeps clause 3 alive under the repaired hypothesis set.
  have hanti : ∀ j, j ≤ J → μ j ≤ μ 0 := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ k ih =>
      intro hk
      have hstep := hh k (by omega)
      have hprev := ih (by omega)
      omega
  refine ⟨c1, ?_, ?_, c4⟩
  · -- Clause 2: two jumps would force `8 ≤ μ 0 = 4`.
    intro h0
    by_contra hJ
    have h8 := c4 (by omega)
    omega
  · -- Clause 3: transport `μ 0 ≤ 7` down to the jump start `i − 1`, then halve once.
    intro h7 i hi1 hiJ
    have hstep := hh (i - 1) (by omega)
    have hidx : i - 1 + 1 = i := by omega
    rw [hidx] at hstep
    have hprev := hanti (i - 1) (by omega)
    omega

end Uniformity.Density.Ladder

/-! ## Gate: the corpus's three named configurations, and the guard

Executed `example`s, not blueprint declarations. Each of the three configurations `EFF.HE7.15`,
`EFF.HE7.16`(i), `EFF.HE7.57` and ANNEX R R1.3 name is checked to be (a) ADMISSIBLE under the
signature landed above and (b) INADMISSIBLE under the committed pre-repair hypothesis set
`∀ i ≤ J, 4 ≤ μ i`. That pair is A-E.1/E-D11's decisive check, and firing it here means a future
edit that silently restores the committed range breaks the build in this file.

The bounds are also shown TIGHT at these configurations, so no clause is slack decoration. -/

section Gate

open Uniformity.Density.Ladder

/-- The `n = 8` frame (`EFF.HE7.57`): one jump, `μ = 4 → 2`. -/
private def mu8 : ℕ → ℕ := fun i => if i = 0 then 4 else 2

/-- COROLLARY HE7.B(i)'s edge (`EFF.HE7.16`(i)): `μ = 7 → 3`, the `⌊7/2⌋` case. -/
private def mu7 : ℕ → ℕ := fun i => if i = 0 then 7 else 3

/-- ANNEX R R1.3's constructed `n = 16` family: two jumps, `μ = 8 → 4 → 2`. -/
private def mu16 : ℕ → ℕ := fun i => if i = 0 then 8 else if i = 1 then 4 else 2

/-- A terminal leaf with no jump: `μ ≡ 1`, `J = 0` (`EFF.HE7.15`'s `μ = 1` configuration). -/
private def mu1 : ℕ → ℕ := fun _ => 1

-- All three configurations satisfy the REPAIRED hypotheses and violate the COMMITTED one.
example : (∀ i < 1, 4 ≤ mu8 i) ∧ (∀ i < 1, 2 * mu8 (i + 1) ≤ mu8 i)
    ∧ ¬ (∀ i ≤ 1, 4 ≤ mu8 i) := by decide

example : (∀ i < 1, 4 ≤ mu7 i) ∧ (∀ i < 1, 2 * mu7 (i + 1) ≤ mu7 i)
    ∧ ¬ (∀ i ≤ 1, 4 ≤ mu7 i) := by decide

example : (∀ i < 2, 4 ≤ mu16 i) ∧ (∀ i < 2, 2 * mu16 (i + 1) ≤ mu16 i)
    ∧ ¬ (∀ i ≤ 2, 4 ≤ mu16 i) := by decide

/-- Clause 2 is TIGHT, not a slack statement about a forced `J = 0`: the `n = 8` frame has
`μ 0 = 4` and realises `J = 1`, and the theorem returns exactly `J ≤ 1`. -/
example : (1 : ℕ) ≤ 1 :=
  (ladder_finite_bounds mu8 1 (by decide) (by decide)).2.1 (by decide)

/-- Clause 3's antecedent is LIVE, and the bound is attained: at `μ 0 = 7` with one jump the
theorem gives `μ 1 ≤ 3`, and `μ 1` IS `3`. (Under the committed hypothesis set this antecedent
was unsatisfiable at `J ≥ 1` — the vacuity E-D11 found.) -/
example : mu7 1 ≤ 3 ∧ mu7 1 = 3 :=
  ⟨(ladder_finite_bounds mu7 1 (by decide) (by decide)).2.2.1 (by decide) 1 (by norm_num)
      (by norm_num),
   by decide⟩

/-- Clauses 1 and 4 are tight at the `n = 16` family: `2 ^ (2+1) = 8 = μ 0`. -/
example : 2 ^ (2 + 1) ≤ mu16 0 ∧ 8 ≤ mu16 0 :=
  ⟨(ladder_finite_bounds mu16 2 (by decide) (by decide)).1 (by norm_num),
   (ladder_finite_bounds mu16 2 (by decide) (by decide)).2.2.2 (by norm_num)⟩

/-- **The `1 ≤ J` guard is necessary.** At `J = 0` both hypotheses are empty, so an unguarded
clause 1 would assert `2 ≤ μ 0` of every terminal leaf — false at the corpus's own `μ = 1`
configuration. -/
example : (∀ i < 0, 4 ≤ mu1 i) ∧ (∀ i < 0, 2 * mu1 (i + 1) ≤ mu1 i)
    ∧ ¬ (2 ^ (0 + 1) ≤ mu1 0) := by decide

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.ladder_finite_bounds

end AxCheck
