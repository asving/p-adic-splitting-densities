/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E05

/-!
# Uniformity.ChapE.E06 — ladder telescoping: `D_i` is the seed times a product of slot counts

**Chapter E, NODE E.06** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §3), ENV-E1 (the arithmetic
arena: threshold and degree bookkeeping, no local base `O`).

E.05 defines the key degree along a ladder by the one-step recursion `D_{i+1} = D_i · L_i`
(`LadderData.degAt`, seeded at `D₀ · L_base`). This node closes that recursion:

> `Λ.degAt D₀ i = D₀ * ((Λ.base :: Λ.rungs.take i).map RungDatum.slotCount).prod`

— the level-`i` key degree is the seed times the product of ALL slot counts through level `i`
(the base's and the first `i` higher rungs'). In corpus letters: `D″ = D′·ℓd_r`
(`EFF.HE7.06`), `D_2 = D′·e₂f₂` (`EFF.T2.36`), and in general `D_{i+1} = D₀·Π_j L_j`.

## What this is the degree half OF

`EFF.HE7.48` (THEOREM HE7.D) displays the composed invariants of a ladder path as
`e = e₁ℓ_1⋯ℓ_{i+1}`, `f = f₁g_1⋯g_{i+1}`. Since E.02's slot count is `L_j = ℓ_j g_j`, the
PRODUCT `e·f` of those two displays is exactly the right-hand side above. So this lemma is the
`e·f` shadow of HE7.D's composed invariants — the part visible to the ladder's pure ℕ-arithmetic,
carrying no claim about `e` and `f` SEPARATELY. Splitting the product back into its two factors
is not available here and is not attempted: the separate `e`/`f` bookkeeping needs the carrier
layer (§4) and the σ dictionary (§7, GC-4), and the identification of `e·f` with an honest
degree is fenced at E.53 (`leaf_ef_finrank`). Read this node as: *the ladder's degree recursion
telescopes*, nothing more.

## The range hypothesis is real, and it is exactly `≤`

`hi : i ≤ Λ.rungs.length` is not decoration. E.05's recursion reads the `i`-th rung through
`Λ.rungs[i]?` with a `getD 1` default, so PAST the end of the list `degAt` silently stops
growing (it multiplies by `1`), while `List.take` also saturates — the two saturations agree, so
the identity happens to survive out of range as well. It is nevertheless signed with `hi`,
because the blueprint's contract (E.05's SIGNATURE NOTE) is that out-of-range reads are *not a
corpus configuration*: no consumer may rely on the default. The bound is `≤`, not `<`: at
`i = Λ.rungs.length` the product runs over the whole ladder, which is the case E.46/E.67 and the
seam layer actually consume. Only the successor step spends the hypothesis, in the strict form
`i < Λ.rungs.length`, which is where `Λ.rungs[i]? = some Λ.rungs[i]` comes from.

## Proof

Induction on `i`. The base case is the seed clause of `degAt` against the one-element list
`[Λ.base]`. The step rewrites `Λ.rungs.take (i+1) = Λ.rungs.take i ++ [Λ.rungs[i]]`
(`List.take_add_one` — `List.take_succ` is deprecated at the pin — plus
`List.getElem?_eq_getElem` for the in-range read), so the product picks up exactly the factor the
recursion multiplies by, and the two sides differ only by associativity.

DEPENDS: E.05 (`LadderData`, `LadderData.degAt`), E.02 (`RungDatum.slotCount`) · mathlib
`List.take_add_one`, `List.getElem?_eq_getElem`, `List.prod_cons`, `List.prod_append`,
`List.map_append`.

ARITHMETIC AUDIT (the corpus frame of E.05's own audit, re-run here through the closed form and
executed as gates below). Base rung `(ℓ,g,u,T) = (2,1,1,0)`, one higher rung `(2,1,5,2)` (the
`q = 3` level-2 frame; `T = 2 = base.nextT`, so `rungFollows` holds). With seed `D₀ = 1`:
`degAt 1 0 = 2 = D′` and `degAt 1 1 = 4 = D″ = D′·ℓd_r`, while the closed form reads
`1·(2·2) = 4` — the two agree, and the gate below checks the general statement AT this ladder
rather than only the numbers.

SOURCE: `EFF.HE7.48` (THEOREM HE7.D's composed `e`/`f` display); `EFF.HE7.06` (`D″ := D′ℓd_r`);
`EFF.T2.36` (`D = D₂ = D′e₂f₂`); `EFF.T2.30` (`(FUND)` — `|Ω| = ef`, whose ladder form this
feeds at E.15/E.53).

TEETH: Q1's per-member `Σef = 8` at `n = 8` (`EFF.HE7.36` TEETH) — degree conservation is the
checkable shadow of the composed invariants; E.46/E.67 carry the executable form.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, and the axiom footprint is Lean-core (`#print axioms` reports `[propext]` only, from
mathlib's list simp lemmas). Type checked against the signed SIGNATURE (binder names, order and
explicitness unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.06** *Ladder telescoping.* The level-`i` key degree is the seed `D₀` times the product of
every slot count through level `i` — `D_{i+1} = D₀·Π_j L_j`, the `e·f` shadow of `EFF.HE7.48`'s
composed invariants `e = e₁ℓ_1⋯ℓ_{i+1}`, `f = f₁g_1⋯g_{i+1}` (`L_j = ℓ_j g_j`). -/
theorem LadderData.degAt_eq_prod (Λ : LadderData) (D₀ : ℕ) (i : ℕ)
    (hi : i ≤ Λ.rungs.length) :
    Λ.degAt D₀ i = D₀ * ((Λ.base :: Λ.rungs.take i).map RungDatum.slotCount).prod := by
  induction i with
  | zero =>
      -- the seed clause against the one-element list `[Λ.base]`
      simp [LadderData.degAt]
  | succ i ih =>
      -- the only place `hi` is spent: the `i`-th read is in range, so no default is consulted
      have hi' : i < Λ.rungs.length := hi
      have hget : Λ.rungs[i]? = some Λ.rungs[i] := List.getElem?_eq_getElem hi'
      have htake : Λ.rungs.take (i + 1) = Λ.rungs.take i ++ [Λ.rungs[i]] := by
        rw [List.take_add_one, hget]
        rfl
      rw [LadderData.degAt, ih (le_of_lt hi'), hget, htake]
      -- both sides are now the same product, associated differently
      simp only [Option.map_some, Option.getD_some, List.map_cons, List.map_append,
        List.map_nil, List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc]

/-! ## Gate (executed `example`s, not blueprint declarations)

The telescoping identity is vacuously true of an empty ladder, so it is checked here on a REAL
corpus frame — E.05's own audit ladder, the `q = 3` level-2 frame — at both levels, together
with the two corpus numbers `D′ = 2` and `D″ = 4` it is supposed to reproduce. -/

section Gate

/-- The audit ladder: base rung `(ℓ,g,u,T) = (2,1,1,0)`, one higher rung `(2,1,5,2)`. -/
private def auditLadder : LadderData where
  base := ⟨2, 1, 1, 0, by decide, by decide, by decide, by decide⟩
  rungs := [⟨2, 1, 5, 2, by decide, by decide, by decide, by decide⟩]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

-- the corpus numbers: `D′ = 2` at level 0, `D″ = D′·ℓd_r = 4` at level 1.
example : auditLadder.degAt 1 0 = 2 := rfl
example : auditLadder.degAt 1 1 = 4 := by decide

-- the closed form, AT this ladder, at both levels (`i = 1` is the full-ladder case `i = length`).
example : auditLadder.degAt 1 1
    = 1 * ((auditLadder.base :: auditLadder.rungs.take 1).map RungDatum.slotCount).prod :=
  auditLadder.degAt_eq_prod 1 1 (by decide)

example : auditLadder.degAt 7 0
    = 7 * ((auditLadder.base :: auditLadder.rungs.take 0).map RungDatum.slotCount).prod :=
  auditLadder.degAt_eq_prod 7 0 (Nat.zero_le _)

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LadderData.degAt_eq_prod

end AxCheck
