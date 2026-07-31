/-
Unit HK-22 / THE 2-NODE GATE  (convergence unit, 2026-07-31; record:
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` CONVERGENCE section + the Asvin sign-off
"Item 3 (HK-06 wave) executes AFTER the in-flight HK-22 gate lands").

CHARGE: ONE compiled concrete 2-node `History` — a root node over the base pin `bStageP`
whose child rides the forged ramified transition (`MovesD/R7_ramifiedForge.lean`:
`ramifiedStage : Stage 2 F4`, `ramifiedStage_trans : TransitionCoreL bStageP ramifiedStage
U31.fq 2 5 U31.ν₀.zbar`) — satisfying `HistoryCoherent ∧ Realizable ∧ InBox n` in the
CURRENT (pre-HK-06) vocabulary.

VERDICT: **BLOCKED-FALSE — COMPILED.**  No such history exists; this file PROVES it.
The gate as charged cannot pass before the HK-06 re-key, and the obstruction is exactly
the child-keying defect the HK-06 wave (queue item 3, task #44) repairs.  The compiled
content, in dependency order:

1. `isNodeLift_fq_stride2_forces` — THE PARITY KERNEL.  `HistoryCoherent`'s i = 0
   non-recentering leg demands `IsNodeLift ν₀ σ₁.Φ` at the ROOT NODE's recorded pair,
   with the lift's Φ-adic stride = `ν₀.e` (MovesC/Defs round-3 keying).  The forged
   child has `σ₁.Φ = fq = X² + 2X + 4` and `TransitionCoreL`'s `child_e` pins
   `ν₀.e = ramifiedStage.e = 2`.  A stride-2 lift is supported on EVEN key-powers with
   coefficient polynomials of degree < deg Φ₀ = 1 (coherence clause 1), so evaluating
   the lift identity at the two points where `Φ₀` takes values `1` and `−1` gives the
   scalar equation `fq(1 − a) = fq(−1 − a)` (`Φ₀ = X + C a`, monic degree 1), i.e.
   `4·(1 − a) = 0`: THE ONLY monic linear key admitting a stride-2 lift of `fq` is
   `Φ₀ = X + C 1`.
2. `bw_X_add_C_one` — but `X + C 1` has base-pin weight `bw(X + C 1) = 0` (its normal
   form has 2-exponent 0: `θ(X + C 1) = 2X + 1`, unit residue).
3. `ramifiedChild_twoNode_incoherent` — THE GATE OBSTRUCTION, root frame UNPINNED:
   for ANY `H : History 2 F4` with `(H.nodes[1]).σ = ramifiedStage`, `¬HistoryCoherent H`.
   Chain: coherence clause 1 (root key monic degree 1) + the leg's `TransitionCoreL`
   (`child_e` pins the stride, `child_wPrev` chains `σ₀.w = ramifiedStage.wPrev = bStageP.w
   = bw` through the coherence record AND the forge record) + kernel (1) force
   `σ₀.Φ = X + C 1`; then the Stage law `hwΦ` (`σ₀.w σ₀.Φ = σ₀.h`) + (2) give
   `σ₀.h = 0`, contradicting `hh : 1 ≤ σ₀.h`.  NO root frame works — not just `bStageP`.
4. `isNodeLift_fq_stride2_false_at_bStageP` — the charge-keyed kernel corollary at the
   base pin (`bStageP.Φ = X`: `X = X + C 1` is absurd).
5. `twoNodeGate_isEmpty` — the packaged verdict: the charged conjunction (bStageP root,
   ramifiedStage child, `HistoryCoherent ∧ Realizable ∧ InBox n`) is unsatisfiable, ∀ n.

WHAT THIS MEANS (the fence upgrade).  The pre-HK-06 `HistoryCoherent` keys BOTH
`IsNodeLift`'s stride AND `TransitionCoreL` at the PARENT node's recorded pair, while the
PROVED transition engine (S9/`TransHyp`, D.5) builds the lift at the FRAME pair
(`IsStandardLift` stride `σ.e`) with the side `(e′, h′)` free.  At any genuinely ramified
read over the base pin (`e′ = 2 ≠ 1 = bStageP.e`) the two keyings collide and coherence
is UNSATISFIABLE — the V10/V11 incompatibility class, now machine-certified AT THE GATE
INSTANCE the four convergent obligations wanted (HK-22 gate, U10d instantiation,
U1_negWitness perimeter, U15 SEED-EXIST first test).  Consequences: (a) the HK-06 (S-a)
re-key is NECESSARY, not just ratified — no prover time may be spent seeking a pre-wave
2-node instance with an S9-forged child; (b) the U10d `zcStepConfineStmt_false_of_config`
instantiation and the U1_negWitness inhabitation stay parked BEHIND THE WAVE (their wall
is now a theorem, not a census note); (c) HK-21/HK-22 in the BP2 staging sense (the (NEW)
clause set) remain the only satisfiable forms — this file is the pre-wave half of that
gate pair, certifying the OLD leg empty at the ramified instance.

Perimeter honesty: the obstruction is specific to child frames carrying the forged
`(e′, h′) = (2, 5)` record (any `e′ ≠ 1` child over a degree-1-key root frame dies the
same way: parity generalizes to any even stride, and odd strides ≥ 3 fail degree
accounting — NOT compiled here; this file certifies the charged instance).  A pre-wave
2-node history with an `e′ = 1` HAND-BUILT child stage (e.g. a (1,2)-side linear-ψ read,
key `X + C 4`) is NOT excluded by this file — recorded in the unit note as the only
visible pre-wave alternative, priced at a bStage-scale build and OUTSIDE this charge.

M1 COEXISTENCE (clean).  This file proves negations of INSTANCE coherence, refuting no
sorried statement: its import cone (= the forge's cone + this leaf, verified sorry-free
2026-07-31, TreeCan-free) contains no sorried universal; HK15_gateChildCarrier's sorried
`gateChildStage` family (NOT imported) concerns the (e′,h′,s′,t′) child-carrier
construction, not history coherence, and is untouched by these theorems; G1_toyGate's
sorried toy pins (NOT imported) live at different carriers.

deps: MovesD/R7_ramifiedForge (the forged instance + its TransitionCoreL record; brings
MovesC/Defs, MovesD/Defs, HC2 U31/HK13R toolkits transitively — all proved).
Axioms: Lean core only (verified by the #print axioms at EOF).
-/
import Mathlib
import LeanUrat.MovesD.R7_ramifiedForge

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK22

/-! ### §1 — the parity kernel: stride-2 node lifts of `fq` force the key `X + C 1` -/

/-- **THE PARITY KERNEL.**  If a node `ν` with read stride `ν.e = 2` over a monic
degree-1 frame key admits `IsNodeLift ν fq` (the round-3 coherence leg's lift shape:
`fq = Φ₀^{2g} + Σ_{k<g} tt_k·Φ₀^{2k}`, coefficient polynomials of degree < 1), then the
frame key is EXACTLY `X + C 1`.  Route: evaluate the lift identity at the two points
where `Φ₀ = X + C a` takes the values `1` and `−1`; every right-hand term is invariant
under the value sign-flip (even powers, constant coefficients), so
`fq(1 − a) = fq(−1 − a)`, i.e. `4(1 − a) = 0`, i.e. `a = 1` (ℤ₂ is a domain). -/
theorem isNodeLift_fq_stride2_forces (ν : Node 2 F4) (he : ν.e = 2)
    (hdeg : ν.σ.Φ.natDegree = 1) (h : IsNodeLift ν U31.fq) :
    ν.σ.Φ = X + C 1 := by
  obtain ⟨tt, hzero, hconstr, heq⟩ := h
  have hΦ : ν.σ.Φ = X + C (ν.σ.Φ.coeff 0) := ν.σ.hmonic.eq_X_add_C hdeg
  set a : ℤ_[2] := ν.σ.Φ.coeff 0 with ha
  -- every coefficient polynomial of the lift is a constant (or zero)
  have httC : ∀ k, k < ν.g → ∃ c : ℤ_[2], tt k = C c := by
    intro k hk
    by_cases hψ : ν.ψ.coeff k = 0
    · exact ⟨0, by rw [hzero k hψ, map_zero]⟩
    · obtain ⟨-, hinC, -, -⟩ := hconstr k hk hψ
      have hd : (tt k).degree < 1 := by
        have hd0 : (tt k).degree < ν.σ.Φ.degree := hinC
        rwa [hΦ, degree_X_add_C] at hd0
      exact ⟨(tt k).coeff 0,
        Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hd)⟩
  -- the evaluated lift identity
  have hev : ∀ x : ℤ_[2], U31.fq.eval x
      = (ν.σ.Φ.eval x) ^ (ν.e * ν.g)
        + ∑ k ∈ Finset.range ν.g, (tt k).eval x * (ν.σ.Φ.eval x) ^ (ν.e * k) := by
    intro x
    conv_lhs => rw [heq]
    rw [eval_add, eval_pow, eval_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_pow]
  have hΦeval : ∀ x : ℤ_[2], ν.σ.Φ.eval x = x + a := by
    intro x
    rw [hΦ, eval_add, eval_X, eval_C]
  -- the sign-flip invariance of the right-hand side
  have hkeyEq : U31.fq.eval (1 - a) = U31.fq.eval (-1 - a) := by
    rw [hev (1 - a), hev (-1 - a), hΦeval, hΦeval]
    have e1 : (1 - a) + a = 1 := by ring
    have e2 : (-1 - a) + a = -1 := by ring
    rw [e1, e2, he]
    rw [Even.neg_one_pow ⟨ν.g, two_mul ν.g⟩, one_pow]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨c, hc⟩ := httC k (Finset.mem_range.mp hk)
    rw [Even.neg_one_pow ⟨k, two_mul k⟩, one_pow, hc, eval_C, eval_C]
  -- the scalar equation: 4(1 − a) = 0, hence a = 1
  have hfq : ∀ x : ℤ_[2], U31.fq.eval x = x ^ 2 + 2 * x + 4 := by
    intro x
    simp only [U31.fq, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [hfq, hfq] at hkeyEq
  have h4 : (4 : ℤ_[2]) * (1 - a) = 0 := by linear_combination hkeyEq
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp h4 with h4' | h4'
    · exact absurd h4' (by norm_num)
    · exact (sub_eq_zero.mp h4').symm
  rw [hΦ, ha1]

/-- The charge-keyed kernel corollary AT THE BASE PIN: no node over `bStageP` with read
stride 2 lifts to `fq` (`bStageP.Φ = X ≠ X + C 1`). -/
theorem isNodeLift_fq_stride2_false_at_bStageP (ν : Node 2 F4)
    (hσ : ν.σ = bStageP) (he : ν.e = 2) : ¬ IsNodeLift ν U31.fq := by
  intro h
  have hdeg : ν.σ.Φ.natDegree = 1 := by
    rw [hσ, bStageP_Phi_def]
    exact natDegree_X
  have hforce := isNodeLift_fq_stride2_forces ν he hdeg h
  rw [hσ, bStageP_Phi_def] at hforce
  have h1 : (C (1 : ℤ_[2]) : Polynomial ℤ_[2]) = 0 := by linear_combination -hforce
  exact one_ne_zero (Polynomial.C_eq_zero.mp h1)

/-! ### §2 — the base-pin weight of the forced key: `bw (X + C 1) = 0` -/

/-- Normal form of `θ(X + C 1) = 2X + 1`: 2-exponent 0, cofactor a mod-2 unit. -/
lemma NF_θ_X_add_C_one : U31.NF (U31.θ (X + C 1)) 0 (C 2 * X + 1) := by
  constructor
  · rw [pow_zero, one_mul, map_add, HK13R.θ_apply, eval₂_X, U31.θ_C, C_1]
  · intro hmap
    have h0 : ((C 2 * X + 1 : Polynomial ℤ_[2]).map U31.ρ).coeff 0
        = (0 : Polynomial ↥U31.K2).coeff 0 := by rw [hmap]
    have hc : ((C 2 * X + 1 : Polynomial ℤ_[2])).coeff 0 = 1 := by
      rw [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_one_zero]
    rw [coeff_map, hc, map_one, coeff_zero] at h0
    exact one_ne_zero h0

/-- The forced key sits at base-pin weight ZERO — below every legal stage weight. -/
lemma bw_X_add_C_one : U31.bw (X + C 1) = 0 := by
  exact_mod_cast U31.bw_eq NF_θ_X_add_C_one

/-! ### §3 — THE GATE OBSTRUCTION: no coherent 2-node history rides the forged
ramified transition (root frame UNPINNED — no root frame works) -/

/-- **THE 2-NODE GATE IS EMPTY AT HEAD** (pre-HK-06 vocabulary): any history whose
second node's frame is the forged `ramifiedStage` is INCOHERENT.  The i = 0 coherence
leg pins the root read pair to (2, 5) (`child_e`/`child_h` at the recorded child), the
root frame's valuation to `bw` (`child_wPrev` chained through the coherence record and
the forge record), and the root key to a monic degree-1 polynomial (clause 1) — then
the parity kernel forces the key `X + C 1`, whose `bw`-weight 0 violates the frame's own
`hwΦ`/`hh` laws. -/
theorem ramifiedChild_twoNode_incoherent (H : History 2 F4)
    (hlen : 1 < H.nodes.length)
    (hchild : (H.nodes[1]'hlen).σ = R7Forge.ramifiedStage) :
    ¬ HistoryCoherent H := by
  intro hcoh
  have h0 : 0 < H.nodes.length := by omega
  obtain ⟨hdeg1, -, -, hstep⟩ := hcoh
  have hne0 : (H.nodes[0]'h0).species ≠ ReadSpecies.recentering := by
    rw [(H.root_iff 0 h0).mpr rfl]
    exact fun hcontra => ReadSpecies.noConfusion hcontra
  obtain ⟨hlift, htrans⟩ := (hstep 0 hlen).2.1 hne0
  -- the child frame is the forged stage (index 0+1 ≡ 1)
  have hΦ1 : (H.nodes[0+1]'hlen).σ = R7Forge.ramifiedStage := hchild
  -- pin the root read's stride to 2
  have hce := htrans.base.child_e
  rw [hΦ1, R7Forge.ramifiedStage_e] at hce
  -- the child key is fq
  have hkey : (H.nodes[0+1]'hlen).σ.Φ = U31.fq := by
    rw [hΦ1]
    exact R7Forge.ramifiedStage_trans.base.child_key
  rw [hkey] at hlift
  -- the parity kernel forces the root key X + C 1
  have hΦforce : (H.nodes[0]'h0).σ.Φ = X + C 1 :=
    isNodeLift_fq_stride2_forces _ hce.symm (hdeg1 h0) hlift
  -- the root frame's valuation is bw (two child_wPrev records chained)
  have hwbw : ∀ f, (H.nodes[0]'h0).σ.w f = U31.bw f := by
    intro f
    have h1 := htrans.base.child_wPrev f
    have h2 := R7Forge.ramifiedStage_trans.base.child_wPrev f
    rw [hΦ1] at h1
    rw [← h1, h2, bStageP_w_def]
  -- the frame laws collapse: h = 0 < 1
  have hwphi := (H.nodes[0]'h0).σ.hwΦ
  rw [hΦforce, hwbw, bw_X_add_C_one] at hwphi
  have hh := (H.nodes[0]'h0).σ.hh
  omega

/-- **THE PACKAGED GATE VERDICT** (the charge's exact conjunction, ∀ n): no 2-node
history over the base pin riding the forged ramified transition satisfies
`HistoryCoherent ∧ Realizable ∧ InBox n`.  The `Realizable`/`InBox` conjuncts are
killed with the coherence leg; the root pin `bStageP` is not even needed
(`ramifiedChild_twoNode_incoherent` is root-frame-free). -/
theorem twoNodeGate_isEmpty (n : ℕ) :
    ¬ ∃ (H : History 2 F4) (hlen : 1 < H.nodes.length),
        (H.nodes[0]'(by omega)).σ = bStageP ∧
        (H.nodes[1]'hlen).σ = R7Forge.ramifiedStage ∧
        HistoryCoherent H ∧ Realizable H ∧ InBox n H := by
  rintro ⟨H, hlen, -, hchild, hcoh, -, -⟩
  exact ramifiedChild_twoNode_incoherent H hlen hchild hcoh

end HK22

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK22.isNodeLift_fq_stride2_forces
#print axioms LeanUrat.MovesJ.HK22.isNodeLift_fq_stride2_false_at_bStageP
#print axioms LeanUrat.MovesJ.HK22.bw_X_add_C_one
#print axioms LeanUrat.MovesJ.HK22.ramifiedChild_twoNode_incoherent
#print axioms LeanUrat.MovesJ.HK22.twoNodeGate_isEmpty

/- Verified output (per-file gate `lake env lean`, 2026-07-31 — 0 errors, 0 warnings):
each of the five theorems above depends on axioms [propext, Classical.choice, Quot.sound]
— Lean core only, no sorryAx. -/
