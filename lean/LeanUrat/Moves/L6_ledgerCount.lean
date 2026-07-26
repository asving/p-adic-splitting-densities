/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L6_ledgerCount — the per-move measure ledger (§B2-DEF D.11)

`#stratum = p^{nN}·vol`: a stratum cut by `k` unitriangular digit equations is equinumerous
to its free digits (`n·N − k` of them, each ranging over `ZMod p`), so its cardinality is
`p^{n·N−k}`. Here the equinumerosity is packaged as the supplied equivalence `e`, and this
lemma is the counting endpoint: transport along `e` and count a finite function space.

FLAGGED-OK (blueprint gap G9): the single uniform `p^{−k}` model — the per-equation
alphabet-factor bookkeeping is collapsed to the exponent `k`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

theorem L6_ledgerCount {p : ℕ} [Fact p.Prime] (n N k : ℕ) (stratum : (Fin n → ZMod (p ^ N)) → Prop) (e : {x // stratum x} ≃ (Fin (n * N - k) → ZMod p)) : Nat.card {x // stratum x} = p ^ (n * N - k) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end LeanUrat.Moves
