/-
Unit U11.root_height_of_inBox  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.root_height` docstring ("D.4's ROOT case: every side slope
≥ 1; the cluster zeros pin level 0, floor height 1").
deps: MovesD `InBox` (E-phase core).  difficulty: medium.  hypothesis_fields: hbox, hd4.
RISK (blueprint, pre-declared flex point): if MovesD's `InBox` turns out weaker than the
height bound, this unit's hypothesis must be upgraded to the D.4 root clause —
statement-fence event, sign-off required (never prove from junk).
N-5 RESTATEMENT (2026-07-28, sign-off round — §9 F-6 executed; the pre-declared RISK
FIRED): the unit was UNPROVABLE-AND-REFUTABLE as stated (a one-node coherent in-box
history with `ustar := −5` satisfies every hypothesis and fails the conclusion —
`ShapeWF` carries no height law; NO value bound on `ustar` exists anywhere in the
corpus, grep-confirmed corpus-wide at F-6). GAINS `hd4 : RootD4 H` (Defs N-5 addendum =
§B2-DEF D.4's root clause). Derivation route (F-6's sketch, records why the two
conjuncts suffice): root `Dwidth = 1` (hroot + hDwidth) and `STR = 1` give `slope = h/e`,
so `1 ≤ slope` IS D.4's "every side slope ≥ 1"; every interior base `b < μ·childWidth`
sits at least one step left of the vertex base, whence `line.at b ≥ ustar + slope ≥ 1`
by `hLineU`. Proof queued for the fleet round; the Shape-side alternative was REJECTED
(frozen MovesD Defs; silent shape-universe shrink).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The root line dominates the cluster floor (verbatim `JetSetup.root_height`'s type;
N-5: under the D.4 root clause `hd4`). -/
theorem root_height_of_inBox {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {H : History p F} (hcoh : HistoryCoherent H) (hbox : InBox n H)
    (hd4 : RootD4 H) :
    ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth →
      1 ≤ (H.nodes[0]'hj).line.at b := by
  intro hj b hb
  set ν := H.nodes[0]'hj with hν
  -- root frame width is 1 (coherence clause 1 + the frame-link `hDwidth`).
  have hΦ : ν.σ.Φ.natDegree = 1 := by rw [hν]; exact hcoh.1 hj
  have hDw : ν.Dwidth = 1 := by rw [ν.hDwidth, hΦ]
  -- D.4's root clause: `0 ≤ ustar` and `1 ≤ slope`.
  obtain ⟨hustar, hslope⟩ : 0 ≤ ν.ustar ∧ 1 ≤ ν.line.slope := by rw [hν]; exact hd4 hj
  -- `Ranch ≠ 0` (its top digit is nonzero).
  have hRne : ν.Ranch ≠ 0 := by
    have hc : ν.Ranch.coeff (ν.wSide / ν.e) = ν.pat (ν.wSide / ν.e) := by
      rw [ν.hRanch, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range]
    intro h0
    rw [h0, Polynomial.coeff_zero] at hc
    exact ν.hpatTop hc.symm
  -- `deg Ranch ≤ wSide/e`.
  have hdeg : ν.Ranch.natDegree ≤ ν.wSide / ν.e := by
    rw [ν.hRanch]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    simp only [Finset.mem_range] at hk
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (ν.pat k) k) (by omega)
  -- `μ·g ≤ deg Ranch ≤ wSide/e` via `ψ^μ ∣ Ranch`.
  have hμg : ν.μ * ν.g ≤ ν.wSide / ν.e := by
    have hpe : (ν.ψ ^ ν.μ).natDegree = ν.μ * ν.g := by
      rw [ν.hψmonic.natDegree_pow, ν.hψdeg]
    have hdvd : (ν.ψ ^ ν.μ).natDegree ≤ ν.Ranch.natDegree :=
      Polynomial.natDegree_le_of_dvd ν.hOrd.1 hRne
    omega
  -- clear the `e ∣ wSide` denominator: `μ·e·g ≤ wSide`.
  have hbound : ν.μ * ν.e * ν.g ≤ ν.wSide := by
    have hdmc : ν.wSide / ν.e * ν.e = ν.wSide := Nat.div_mul_cancel ν.hEdvd
    calc ν.μ * ν.e * ν.g = ν.μ * ν.g * ν.e := by ring
      _ ≤ ν.wSide / ν.e * ν.e := by gcongr
      _ = ν.wSide := hdmc
  -- `μ·childWidth = μ·e·g` (root: `childWidth = e·g`).
  have hcwv : ν.μ * ν.childWidth = ν.μ * ν.e * ν.g := by
    simp only [Node.childWidth, hDw, Nat.mul_one]; ring
  rw [hcwv] at hb
  -- so `b` sits strictly left of the vertex base `s0+wSide`.
  have hb2 : b < ν.s0 + ν.wSide := by omega
  -- the read line passes through `(s0+wSide, ustar)` at the root (Dwidth = 1).
  have hLU : ν.line.at (ν.s0 + ν.wSide) = ν.ustar := by
    have h := ν.hLineU; rwa [hDw, Nat.mul_one] at h
  simp only [Line.at] at hLU ⊢
  have hcastb : (b : ℚ) + 1 ≤ ((ν.s0 + ν.wSide : ℕ) : ℚ) := by
    have hle : b + 1 ≤ ν.s0 + ν.wSide := hb2
    exact_mod_cast hle
  -- one full step left of the vertex, times slope ≥ 1, clears 1.
  have key : (1 : ℚ) ≤ ν.line.slope * (((ν.s0 + ν.wSide : ℕ) : ℚ) - (b : ℚ)) := by
    have h1 : (1 : ℚ) ≤ ((ν.s0 + ν.wSide : ℕ) : ℚ) - (b : ℚ) := by linarith
    nlinarith [hslope, h1]
  -- `line.at b = ustar + slope·(vertexBase − b)`.
  have hval : ν.line.intercept - ν.line.slope * (b : ℚ)
      = ν.ustar + ν.line.slope * (((ν.s0 + ν.wSide : ℕ) : ℚ) - (b : ℚ)) := by
    rw [← hLU]; ring
  rw [hval]
  simp only [Nat.cast_one]
  linarith [key, hustar]

end LeanUrat.MovesJ
