/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1/DefsSpine — strata, transports, the per-level ledger objects (blueprint §2.4)

**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` (rev 2) §2.4. Reused UNCHANGED
from Moves (statement fence): `StratumData`, `LandingCylinderL`, `CarryTransportL`,
`carryDigit`, `K1At`, `IsSlotMinWeight`, `HasAnchorK`, `OrdPsiPoly`, `DigitSystem`
(all imported through the Defs chain). New: `childW` (the D.7 child valuation as a
FUNCTION, by choice against the attained-slot-min spec — S2 proves the spec is
inhabited and unique-valued for f ≠ 0) and `LevelMove` (the per-move D.8/D.10 data
pack at a tower level). Definitions only — no theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

open scoped Classical in
/-- the child valuation as a FUNCTION (D.7 head): `w′(Σ B_j Φ̂^j) := min_j (e′·w(B_j)
+ j·h′)`, via the monic Φ̂-development (Fact A existence + Fact B uniqueness, Moves
L0) — defined by choice against the attained-slot-min spec (the value is unique when
the spec holds; S2's content). Total: junk value 0 at f = 0 / off-spec. -/
noncomputable def childW (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (f : Polynomial ℤ_[p]) : ℤ :=
  if h : ∃ m : ℤ, ∀ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment Φhat f B N →
      SlotMinAttained m N (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ))
        (fun j => B j ≠ 0)
  then h.choose else 0

/-- level-k stratum/landing data bundle for the spine (the D.8/D.10 per-move pack,
at tower level k — all data in level-k's frame: descend polynomial ψ over the
level-k residue field, its degree g and ψ-order μ, the anchor a, the transported
pattern Cdig, and the slot cutoff N). -/
structure LevelMove (T : Tower p F) (k : Fin T.K) where
  ψ : Polynomial ↥(T.stg k.castSucc).K
  g : ℕ
  μ : ℕ
  a : ℤ
  Cdig : ℕ → Polynomial ↥(T.stg k.castSucc).K
  N : ℕ

end LeanUrat.HC1
