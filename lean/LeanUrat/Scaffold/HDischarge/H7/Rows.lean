/-
HDISCHARGE_H7 §3.1 — `H7/Rows.lean`: the Tier-S row shapes (unit H7-A; MECH).
H7-A1 `SiteDatum` + `InGuard`, H7-A2 `ITauShadow`, H7-A3 `KLocCounts` —
transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H7.md` §3.1 (compile-probe
round 2, 2026-08-05).  TIER S THROUGHOUT: interface shadows only — never cite
any row in this file as evidence for (H7).
-/
import LeanUrat.Scaffold.ValueSide.KCount

namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

/-- H7-A1 [Tier S]: the abstract realized-site datum. Engine-side instantiation
(from `MovesT.SiteLedger` at the pinned canonical models) is Tier-M unit H7-W3a.
`one_le_thr`: every realized site has consumed at least the level-0 reduction read
(REV 2, review finding 9 — the IT-3 ceiling needs it). `branchCount` is
ROSTER-indexed, deliberately NOT `AdaptedCell.factorCount` (FINDING H7-F1). -/
structure SiteDatum (p n N : ℕ) [Fact p.Prime] where
  m : ℕ
  two_le_m : 2 ≤ m
  thr : ℕ
  one_le_thr : 1 ≤ thr
  rho : ℕ
  stratumCount : ℕ
  branchCount : Fin m → ℕ

/-- The D-8 guard at the site. -/
def InGuard {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  s.thr + 2 * s.rho ≤ N

/-- H7-A2 [Tier S — renamed from `ITauPresents` at REV 2, review finding 13]: the
COUNT-INTERFACE SHADOW of the (I-τ) row: some adapted-cell carrier with Smith
stability realizes the site's integers (ρ, a pin within the pricing, the K10b image
law, cell count = stratum count, roster-indexed domain law), with `sM` pinned to the
carrier's own Smith data (the s(M) formula — the one internal tie expressible now).
WARNING: satisfiable by synthetic carriers; NOT the semantic (I-τ), which is
`ITauSemantic` (Tier M, §3.7). Never cite this row as evidence for (H7). -/
def ITauShadow {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N) : Prop :=
  ∃ A : AdaptedCell p n N,
    SmithStable A.toMulFiberData ∧
    A.toMulFiberData.ρ = s.rho ∧
    A.toMulFiberData.τ ≤ s.thr + s.rho ∧
    A.sM = ∑ i, min (A.toMulFiberData.smithExp A.toMulFiberData.base i)
      (N - A.toMulFiberData.τ) ∧
    A.cellCount * p ^ A.sM = Nat.card A.Factor ∧
    A.cellCount = s.stratumCount ∧
    Nat.card A.Factor = ∏ j, s.branchCount j

/-- H7-A3 [Tier S]: the K-LOC COUNT SHAPE over an abstract event carrier. WARNING
(REV 2, review finding 14): vacuous at `Events := Empty` and freely engineerable at
arbitrary count functions — contentful ONLY at the Tier-M instantiation (H7-W3a:
`Events` := the ContFiber families, counts := their box cardinalities). It pins the
receipt VOCABULARY for wave-0; it must never be cited as evidence of K-LOC. -/
def KLocCounts {p n N : ℕ} [Fact p.Prime] (s : SiteDatum p n N)
    (Events : Type) (joint : Events → ℕ) (single : Events → Fin s.m → ℕ) : Prop :=
  ∀ E : Events, joint E * s.stratumCount ^ (s.m - 1) = ∏ j, single E j

end LeanUrat.Scaffold.HDischarge.H7
