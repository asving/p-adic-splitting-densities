/- III-S8 probe scratch (to be deleted): can the (H6) row structure
`TerminalSeamHyps` (BP_III §1.3, consumed VERBATIM as III-S8's first binder)
elaborate?  Primed names to avoid collision with in-flight units III-S2/S3/H5;
`terminalDatum'` carries a STUB body (only its SIGNATURE is consumed here). -/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2t

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

structure TerminalDatum' where
  slope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

def terminalDatum' (f : Polynomial ℤ_[p]) (H : EHist p F) : TerminalDatum' :=
  { slope := H.nodes.getLast?.bind fun ν => some (ν.e, ν.h)
    verdict := (1, H.psi0.natDegree) }  -- STUB body (probe only)

def RCConsistent' (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ν : ENodeData) (EF : ℕ × ℕ) : Prop :=
  ν.sel = none ∧
  some (ν.e, ν.h) = (terminalDatum' f H).slope ∧
  EF = (terminalDatum' f H).verdict

-- Probe A: the §1.3 display VERBATIM (modulo primes).  RAN 2026-08-01,
-- FAILED as predicted at row `tVERD` (`EF = terminalDatum f H` equates
-- `ℕ × ℕ` with `TerminalDatum`); exact error:
--   ScratchS8.lean:40:34: error: Type mismatch
--     terminalDatum' f H
--   has type
--     TerminalDatum'
--   but is expected to have type
--     ℕ × ℕ
-- Quarantined by commenting (the ScratchG8 convention) so the scratch stays
-- green; the record of consequence is BLOCKED(III-S8) in CU2t.lean.
--
-- structure TerminalSeamHypsA (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
--   tDECdec : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
--     DecIrr H ∨ DecHen f H → H.nodes ≠ []
--   tDECcor : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
--     DecHen f H → H.a0 = 1 ∨
--       ∃ D : GMNData f (Theta H), D.rootOrder = 1
--   tREAD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
--     {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
--     ConsF f H D R → ∀ i S, R.side i = some S →
--       S ∈ D.principalSides i
--   tVERD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
--     {ν : ENodeData} {EF : ℕ × ℕ},
--     RCConsistent' f H ν EF → EF = terminalDatum' f H

-- Probe B: the same rows with tVERD's conclusion read as `.verdict`
-- (the only type-correct reading; NOT a licensed repair — probe only).
structure TerminalSeamHypsB (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  tDECdec : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
    DecIrr H ∨ DecHen f H → H.nodes ≠ []
  tDECcor : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
    DecHen f H → H.a0 = 1 ∨
      ∃ D : GMNData f (Theta H), D.rootOrder = 1
  tREAD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
    ConsF f H D R → ∀ i S, R.side i = some S →
      S ∈ D.principalSides i
  tVERD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {ν : ENodeData} {EF : ℕ × ℕ},
    RCConsistent' f H ν EF → EF = (terminalDatum' f H).verdict

end LeanUrat.Scaffold.DictIII
