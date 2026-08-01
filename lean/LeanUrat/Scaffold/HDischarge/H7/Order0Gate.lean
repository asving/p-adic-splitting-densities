/-
HDISCHARGE_H7 §3.5 — `H7/Order0Gate.lean`: the order-0 interface-fit gate
(unit H7-D1; W1d).  H7-D1a `f1Datum` (MECH, def displayed), H7-D1b
`gate_f1_iTauShadow` (MED), H7-D1c `gate_f1_guard` (MECH, proof displayed) —
statements transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H7.md` §3.5.
INTERFACE-FIT ONLY (REV 2, review finding 16): the synthetic carrier below
certifies that the row shape is satisfiable at the real F1 integers and that
the F1 arithmetic composes — it is NOT a non-vacuity certificate for the
semantic (I-τ); THAT gate is H7-W3a's `gate_order0_semantic`.  Never cite
anything in this file as evidence for (H7).
-/
import LeanUrat.Scaffold.HDischarge.H7.Rows

namespace LeanUrat.Scaffold.HDischarge.H7

open LeanUrat.Scaffold

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- H7-D1a [MECH; probe-typed]: the F1-shaped order-0 site datum — p = 5, n = 4,
N = 8; two continuing branches (the sealed CASE_SIB roster), residue-split ρ = 0;
stratum 5⁸ (the 14-pin Σ*), branches 5⁴ each; thr = 3 ≥ 1.
Integers from `verification/CASE_SIB_SEALED_PREDICTIONS.md`. -/
noncomputable def f1Datum : SiteDatum 5 4 8 where
  m := 2
  two_le_m := by norm_num
  thr := 3
  one_le_thr := by norm_num
  rho := 0
  stratumCount := 5 ^ 8
  branchCount := ![5 ^ 4, 5 ^ 4]

/-- The SYNTHETIC fiber carrier for the H7-D1b gate: τ = 1 (SEP: 0 + 1 ≤ 1),
ρ = 0, one-point carriers, ZERO Smith exponents (so sM = 0), identity chart.
Tier S: gate scaffolding only — no engine content. -/
def f1FiberData : MulFiberData 5 4 8 where
  τ := 1
  ρ := 0
  τ_sep := le_refl 1
  FactorPoint := Unit
  instFactorPoint := inferInstance
  base := ()
  polydisc := {()}
  Fiber := Unit
  instFiber := inferInstance
  FiberNonempty := True
  SolutionSet := Unit
  instSolutionSet := inferInstance
  smithExp := fun _ _ => 0
  chart := fun _ => Equiv.refl Unit

/-- The SYNTHETIC adapted-cell carrier for the H7-D1b gate: `Factor` is the
genuine two-branch product `Fin 2 → Fin 625` (625 = 5⁴ per branch, so
`Nat.card Factor = 5⁸` by `Nat.card_pi`); `factorCount` is the
DESIGNATED-ELEMENT function (the H7-F1 workaround: `Factor` is
carrier-indexed, not roster-indexed, so the carrier's own `domainCount_eq`
is discharged by loading the whole count on one designated index);
`sM = 0` from the zero Smith exponents.  Tier S: gate scaffolding only. -/
def f1Cell : AdaptedCell 5 4 8 where
  Factor := Fin 2 → Fin 625
  instFactor := inferInstance
  toMulFiberData := f1FiberData
  cellCount := 5 ^ 8
  factorCount := fun j => if j = (fun _ => 0) then 5 ^ 8 else 1
  sM := 0
  domainCount_eq := by
    rw [Nat.card_pi, Finset.prod_ite_eq']
    simp [Nat.card_eq_fintype_card]
  fiber_nonempty := trivial

/-- H7-D1b [MED; Tier S]: `ITauShadow f1Datum` is inhabited — the INTERFACE-FIT gate
(REV 2, review finding 16: a synthetic-carrier inhabitant certifies ONLY that the row
shape is satisfiable at real integers and that the F1 arithmetic composes — it is NOT
a non-vacuity certificate for the semantic (I-τ); THAT gate is H7-W3a's
`gate_order0_semantic`). Builder notes: `Factor := Fin 2 → Fin 625` (`Nat.card_pi`),
`sM = 0` with zero Smith exponents, designated-element `factorCount` for the carrier's
own `domainCount_eq` (H7-F1 workaround). -/
theorem gate_f1_iTauShadow : ITauShadow f1Datum := by
  refine ⟨f1Cell, ⟨fun h _ => rfl⟩, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · -- τ ≤ thr + ρ : 1 ≤ 3 + 0
    norm_num [f1Cell, f1FiberData, f1Datum]
  · -- sM = Σᵢ min 0 (8 − 1) = 0
    simp [f1Cell, f1FiberData]
  · -- cellCount · 5^sM = Nat.card Factor : 5⁸ · 5⁰ = 625²
    rw [show f1Cell.sM = 0 from rfl, pow_zero, mul_one]
    rw [show (Nat.card f1Cell.Factor) = ∏ _j : Fin 2, Nat.card (Fin 625)
          from Nat.card_pi]
    simp [Nat.card_eq_fintype_card]
    norm_num [f1Cell]
  · -- Nat.card Factor = ∏ j, branchCount j : 625² = 5⁴ · 5⁴
    show Nat.card (Fin 2 → Fin 625) = ∏ j : Fin 2, ![5 ^ 4, 5 ^ 4] j
    rw [Nat.card_pi, Fin.prod_univ_two, Fin.prod_univ_two]
    norm_num [Nat.card_eq_fintype_card]

/-- H7-D1c [probe-PROVED]: the gate site is in the D-8 guard (3 + 0 ≤ 8). -/
theorem gate_f1_guard : InGuard f1Datum := by
  unfold InGuard f1Datum
  norm_num

end LeanUrat.Scaffold.HDischarge.H7
