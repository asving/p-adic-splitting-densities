/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RestartEquiv
import LeanUrat.OM.GradedHensel
import LeanUrat.OM.OMCountV2

/-!
# HNode1 — Phase-B wave W4e: the ORDER-1 RESTART IDENTITY (`h_node1`)

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md`, W4 SPEC bullet W4e (assembly) on top of
the landed W4d ladder: `RestartEquiv` (W4d1, the margin-free single-block restart equivalence),
`BlockProduct` + `GradedHensel` (W4d2-1 + W4d2′, the multi-block graded product law), `CellCard`
(W4a/b), `OMCountV2` (R1).  This module CONSUMES those APIs and edits nothing existing.

**The statement family** (count-native, division-free, three graded scopes):

1. `h_node1_single` — the margin-free core: for the single-child order-1 cell (slope `−1/e`,
   residual `(X − c̄)^μ`, `μ < N`) and ANY predicate `Q` on the child digit space,

       #{f // InCellAt f ∧ Q (restartDigits' f)} = #{β // FreshClusterPattern β ∧ Q β}

   — `restartEquiv` transported through `Equiv.subtypeEquiv` (the forward map is `restartDigits`
   BY `rfl`, so the transport is free).  `h_node1_single_shape` specializes `Q := (R · = T')`
   for an ABSTRACT β-side reader `R : (Fin μ → Rphi) → α`: the child's stratum census IS a fresh
   stratum census, for EVERY reader.  (The reader is a parameter — the honest general form; the
   `Rphi`-side menu instantiation of `R` is W6 scope.)
2. `h_node1_selfLoop` — the `e = 1` instance (the RECENTERING step: `φ = X − c̃·p`,
   `Rphi ≅ ZMod (p^N)`; this is the self-loop step the tower induction consumes), plus the
   arithmetic cost tie `selfLoop_coset_index`: the `e = 1` pattern coset sits inside the level-`N`
   cluster box at index exactly `p^(w(μ)+1)` where `w = L5fix.selfLoopExponent` — the
   `countPivot` exponent `s(s+1)/2 − 1` at `s = μ`.
3. `h_node1_census` — the case-B multi-block node identity restated in the `omCount` vocabulary:
   the graded-law fiber census (`GradedHensel.caseB_image_card`, engine value 81 from
   `/workspace-vast/asving/tmp/phaseb_w4d2_0/case_B*`) relative to the level-3 monic box equals
   the `omCount` bracket `mCell · q^(−volExp)` at the case-B `NodeConfig` — the FIRST link
   between `omCount` and the classifier fibers beyond order 0.
4. `h_node1_general` — the hypothesis-gated multi-block form: per-block coset-card certificates
   + a `GradedChain` certificate give `#(node fiber image) · p^X = p^(Σ per-block exponents)`,
   from `GradedHensel.blocks_card_graded`.

Numeric gates (banked values reused): 2 (gate A parameters, self-loop), 16 = 8 + 8 (gate B
parameters, the fresh-determinacy split of the census), 81 · 9 = 27 · 27 (case B em-square),
and the case-B `omCount` tie 81/3¹² = 3⁻⁸.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints (checked with
`#print axioms`, prints removed after checking); no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.HNode1

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.RphiRing
open LeanUrat.OM.RestartEquiv
open LeanUrat.OM.BlockProduct
open LeanUrat.OM.GradedHensel
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.Order0

variable (p N e μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## 1. `h_node1_single` — the margin-free single-block restart identity -/

/-- **The census equivalence**: the `Q`-conditioned cell fiber is in bijection with the
`Q`-conditioned fresh-pattern coset — `restartEquiv` transported through the subtype
of the extra condition (free, because the forward map of `restartEquiv` IS
`restartDigits'` by `rfl`). -/
def censusEquiv (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (Q : (Fin μ → Rphi p N e 1 c) → Prop) :
    {f : QuotientBox.monicBox p N (μ * e) //
        InCellAt p N e μ c f ∧ Q (restartDigits' p N e μ c hN he f)}
      ≃ {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β ∧ Q β} :=
  calc {f : QuotientBox.monicBox p N (μ * e) //
          InCellAt p N e μ c f ∧ Q (restartDigits' p N e μ c hN he f)}
      ≃ {x : {f : QuotientBox.monicBox p N (μ * e) // InCellAt p N e μ c f} //
          Q (restartDigits' p N e μ c hN he x.1)} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    _ ≃ {y : {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β} // Q y.1} :=
        (restartEquiv p N e μ c hN he hμ2 hμN).subtypeEquiv fun x => by
          rw [restartEquiv_apply_val]
          exact Iff.rfl
    _ ≃ {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β ∧ Q β} :=
        Equiv.subtypeSubtypeEquivSubtypeInter _ _

/-- **`h_node1_single` (W4e deliverable 1, the margin-free core).** For the single-child
order-1 cell `c` (the `RestartEquiv` setting: slope `−1/e`, residual `(X − c̄)^μ`, `μ < N`)
and ANY predicate `Q` on the child digit space:

    #{f // InCellAt f ∧ Q (restartDigits' f)} = #{β // FreshClusterPattern β ∧ Q β}.

Count form, no division, no measure: every conditioned census of the cell fiber, read through
the digit avatars, IS the corresponding conditioned census of the fresh cluster coset. -/
theorem h_node1_single (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (Q : (Fin μ → Rphi p N e 1 c) → Prop) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) //
        InCellAt p N e μ c f ∧ Q (restartDigits' p N e μ c hN he f)}
      = Nat.card {β : Fin μ → Rphi p N e 1 c // FreshClusterPattern p N e μ c β ∧ Q β} :=
  Nat.card_congr (censusEquiv p N e μ c hN he hμ2 hμN Q)

/-- The child-side classification of a cell element: an arbitrary β-side reader `R` (the
θ-adic polygon/residual data of the digit tuple over `Rphi` — abstract here; the `Rphi`-menu
instantiation is W6 scope) composed with the digit avatars. -/
def childShape {α : Sort*} (hN : 0 < N) (he : 0 < e)
    (R : (Fin μ → Rphi p N e 1 c) → α) (f : QuotientBox.monicBox p N (μ * e)) : α :=
  R (restartDigits' p N e μ c hN he f)

/-- **`h_node1_single`, the node-identity specialization** (`Q := (R · = T')`): for EVERY
β-side reader `R` and every target shape `T'`, the child's stratum census inside the cell is
the fresh stratum census on the pattern coset:

    #{f // InCellAt f ∧ childShape R f = T'} = #{β // FreshClusterPattern β ∧ R β = T'}.

This is the order-1 restart identity in count form, reader-uniform: the specialization to
the concrete order-1 classification over `Rphi` is the instantiation of `R` (W6). -/
theorem h_node1_single_shape {α : Sort*} (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (R : (Fin μ → Rphi p N e 1 c) → α) (T' : α) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) //
        InCellAt p N e μ c f ∧ childShape p N e μ c hN he R f = T'}
      = Nat.card {β : Fin μ → Rphi p N e 1 c //
          FreshClusterPattern p N e μ c β ∧ R β = T'} :=
  h_node1_single p N e μ c hN he hμ2 hμN (fun β => R β = T')

/-! ### Numeric gate: the fresh-determinacy census split at gate-B parameters

The event `β 0 ∈ (θ)^(N·e)` is the ONE-LEVEL-DOWN UNDECIDEDNESS of the fresh cluster (the
d0-verified fresh determinacy law: decided ⟺ `vphi (β 0) < N·e`).  At the gate-B cell
`(p,N,e,μ) = (2,3,2,2)` the transported census gives `8` undecided, and the complement split
against the banked fiber card `16` (`RestartEquiv.gate_B`) forces `8` decided — the census
transport does genuine work on a nontrivial `Q`. -/

/-- The β-side count: pattern ∧ top-slot undecidedness = per-slot floors `![6, 3]` — the
`j = 0` floor deepens from the pattern's `e·μ+1 = 5` to `N·e = 6`. -/
theorem gate_undecided_pattern :
    Nat.card {β : Fin 2 → Rphi 2 3 2 1 1 // FreshClusterPattern 2 3 2 2 1 β ∧
        β 0 ∈ Ideal.span {theta 2 3 2 1 1} ^ 6} = 8 := by
  have hiff : ∀ β : Fin 2 → Rphi 2 3 2 1 1,
      (FreshClusterPattern 2 3 2 2 1 β ∧ β 0 ∈ Ideal.span {theta 2 3 2 1 1} ^ 6)
        ↔ ∀ j : Fin 2, β j ∈ Ideal.span {theta 2 3 2 1 1} ^ (![6, 3] j) := by
    intro β
    constructor
    · rintro ⟨hpat, hund⟩ j
      fin_cases j
      · exact hund
      · exact hpat 1
    · intro h
      refine ⟨fun j => ?_, h 0⟩
      fin_cases j
      · exact Ideal.pow_le_pow_right (by norm_num) (h 0)
      · exact h 1
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans Equiv.subtypePiEquivPi),
    Nat.card_pi]
  have h0 : Nat.card {b : Rphi 2 3 2 1 1 //
      b ∈ Ideal.span {theta 2 3 2 1 1} ^ ((![6, 3] : Fin 2 → ℕ) 0)} = 1 := by
    show Nat.card {b : Rphi 2 3 2 1 1 // b ∈ Ideal.span {theta 2 3 2 1 1} ^ 6} = 1
    simp only [span_theta_pow_eq]
    rw [card_span_theta_pow 2 3 2 1 (by norm_num) (by norm_num) 6 (by norm_num)]
    norm_num
  have h1 : Nat.card {b : Rphi 2 3 2 1 1 //
      b ∈ Ideal.span {theta 2 3 2 1 1} ^ ((![6, 3] : Fin 2 → ℕ) 1)} = 8 := by
    show Nat.card {b : Rphi 2 3 2 1 1 // b ∈ Ideal.span {theta 2 3 2 1 1} ^ 3} = 8
    simp only [span_theta_pow_eq]
    rw [card_span_theta_pow 2 3 2 1 (by norm_num) (by norm_num) 3 (by norm_num)]
    norm_num
  rw [Fin.prod_univ_two, h0, h1]
  norm_num

/-- The transported count: `8` of the `16` gate-B cell elements are child-undecided —
`h_node1_single` at the fresh-determinacy `Q`. -/
theorem gate_undecided_fiber :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) //
        InCellAt 2 3 2 2 1 f ∧
          restartDigits' 2 3 2 2 1 (by norm_num) (by norm_num) f 0 ∈
            Ideal.span {theta 2 3 2 1 1} ^ 6} = 8 :=
  (h_node1_single 2 3 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun β => β 0 ∈ Ideal.span {theta 2 3 2 1 1} ^ 6)).trans
    gate_undecided_pattern

/-- The complement split against the banked fiber card (`RestartEquiv.gate_B` = 16):
`8` decided.  Internal-consistency cross-check of the transported census. -/
theorem gate_decided_fiber :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) //
        InCellAt 2 3 2 2 1 f ∧
          ¬ (restartDigits' 2 3 2 2 1 (by norm_num) (by norm_num) f 0 ∈
              Ideal.span {theta 2 3 2 1 1} ^ 6)} = 8 := by
  have hsplit := CellCard.card_subtype_and_compl
    (α := QuotientBox.monicBox 2 3 (2 * 2)) (fun f => InCellAt 2 3 2 2 1 f)
    (fun f => restartDigits' 2 3 2 2 1 (by norm_num) (by norm_num) f 0 ∈
      Ideal.span {theta 2 3 2 1 1} ^ 6)
  rw [gate_B, gate_undecided_fiber] at hsplit
  omega

/-! ## 2. `h_node1_selfLoop` — the `e = 1` (recentering / self-loop) instance -/

/-- **`h_node1_selfLoop` (W4e deliverable 2).** The `e = 1` instance of the order-1 restart
identity.  RECENTERING remark: at `e = 1` the restart key is `φ = X − c̃·p` and
`Rphi p N 1 1 c ≅ ZMod (p^N)` (W1 `digitEquiv` at `e = 1`) — the equivalence is the pure
RECENTERING `f(X) ↦ f(X + c̃·p)`-digit bookkeeping.  This is exactly the self-loop step the
tower induction consumes: a size-`μ` cluster whose polygon step keeps residue degree 1
restarts INSIDE the same `ZMod (p^N)` frame, and its census cost per step is the coset index
`p^(w(μ)+1)` computed below (`selfLoop_coset_index`), `w = L5fix.selfLoopExponent` — the
`countPivot` exponent that the omCount recursion's geometric self-loop sum
`1/(1 − q^{−w(s)})` compensates. -/
theorem h_node1_selfLoop {α : Sort*} (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (R : (Fin μ → Rphi p N 1 1 c) → α) (T' : α) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ childShape p N 1 μ c hN one_pos R f = T'}
      = Nat.card {β : Fin μ → Rphi p N 1 1 c //
          FreshClusterPattern p N 1 μ c β ∧ R β = T'} :=
  h_node1_single_shape p N 1 μ c hN one_pos hμ2 hμN R T'

/-- The pattern-coset card at `e = 1`, `s = μ`: `p^(μ(N−1) − μ(μ+1)/2)` —
`card_freshPattern` with the `e = 1` arithmetic normalized. -/
theorem card_selfLoop_coset (hN : 0 < N) (hμN : μ < N) :
    Nat.card {β : Fin μ → Rphi p N 1 1 c // FreshClusterPattern p N 1 μ c β}
      = p ^ (μ * (N - 1) - μ * (μ + 1) / 2) := by
  rw [card_freshPattern p N 1 μ c hN one_pos hμN]
  congr 1
  rw [mul_one, one_mul]

/-- **The cost-exponent tie** (deliverable 2, arithmetic half): the deficit of the `e = 1`
pattern coset against the cluster box is EXACTLY `selfLoopExponent μ + 1`:

    (μ(N−1) − μ(μ+1)/2) + (w(μ) + 1) = μ(N−1),   w(μ) = μ(μ+1)/2 − 1.

`w` is `L5fix.selfLoopExponent`, the exponent of `MontesAxiom.countPivot` at cluster size `μ`
(`countPivot s q = 1 − q^{−w(s)}` for `s ≥ 2`). -/
theorem selfLoop_cost_tie (hμ1 : 1 ≤ μ) (hμN : μ < N) :
    (μ * (N - 1) - μ * (μ + 1) / 2) + (L5fix.selfLoopExponent μ + 1) = μ * (N - 1) := by
  unfold L5fix.selfLoopExponent
  have h2 : μ * (μ + 1) / 2 * 2 = μ * (μ + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self μ))
  have hk1 : 1 * 2 ≤ μ * (μ + 1) := Nat.mul_le_mul hμ1 (by omega)
  have hb : μ * (μ + 1) ≤ μ * (N - 1) * 2 := by
    calc μ * (μ + 1) ≤ μ * ((N - 1) * 2) := Nat.mul_le_mul_left μ (by omega)
      _ = μ * (N - 1) * 2 := by ring
  omega

/-- **The self-loop cost identity, count form**: the `e = 1` fresh-pattern coset sits inside
the level-`N` cluster box (`CellCard.card_clusterBox`, `p^(μ(N−1))` elements) at index
exactly `p^(selfLoopExponent μ + 1)` — the countPivot exponent, plus the puncture unit. -/
theorem selfLoop_coset_index (hN : 0 < N) (hμ1 : 1 ≤ μ) (hμN : μ < N) :
    Nat.card {β : Fin μ → Rphi p N 1 1 c // FreshClusterPattern p N 1 μ c β}
        * p ^ (L5fix.selfLoopExponent μ + 1)
      = Nat.card {f : QuotientBox.monicBox p N μ // CellCard.IsCluster p f} := by
  rw [card_selfLoop_coset p N μ c hN hμN, CellCard.card_clusterBox p hN, ← pow_add,
    selfLoop_cost_tie N μ hμ1 hμN]

/-- Numeric gate (banked values: gate-A fiber `2`; cluster box `16` at `(2,3,s=2)`;
`w(2) = 2`, `countPivot 2 q = 1 − q⁻²`): `2 · 2^(2+1) = 16`. -/
theorem gate_selfLoop :
    Nat.card {β : Fin 2 → Rphi 2 3 1 1 1 // FreshClusterPattern 2 3 1 2 1 β} = 2
      ∧ Nat.card {f : QuotientBox.monicBox 2 3 2 // CellCard.IsCluster 2 f} = 16
      ∧ L5fix.selfLoopExponent 2 = 2 ∧ (2 * 2 ^ (2 + 1) : ℕ) = 16 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [card_selfLoop_coset 2 3 2 1 (by norm_num) (by norm_num)]
    norm_num
  · rw [CellCard.card_clusterBox 2 (by norm_num)]
    norm_num
  · rfl

/-- The `e = 1` coset card agrees with the banked gate-A fiber card (both `2`):
the restart equivalence and the closed form meet. -/
theorem gate_selfLoop_matches_gate_A :
    Nat.card {β : Fin 2 → Rphi 2 3 1 1 1 // FreshClusterPattern 2 3 1 2 1 β}
      = Nat.card {f : QuotientBox.monicBox 2 3 (2 * 1) // InCellAt 2 3 1 2 1 f} := by
  rw [gate_A, gate_selfLoop.1]

/-! ## 3. `h_node1_census` — case B in the `omCount` vocabulary

The case-B cell (`p = 3, N = 3`: degree 4, single side `(0,2) → (4,0)` of slope `−1/2`, two
decided blocks `(e,μ,c̃) = (2,1,1)`, `(2,1,2)`, residual `(y−1)(y−2)`) has fiber census `81`
(engine: `/workspace-vast/asving/tmp/phaseb_w4d2_0/`, row B: fiber 81 = 27·27/3², shape-fiber
`1 × 81`), machine-checked as `GradedHensel.caseB_image_card` THROUGH the graded pair law.
Its `omCount` configuration: polygon ceilings `⌈2 − i/2⌉ = (2,2,1,1)` (newtonExponent 6), one
genuine punctured face `δ = 1` with shape `[(1,1),(1,1)]` (two linear residual factors,
`dF = 2`), no children — `volExp = 8`, and `mCell(3) = ff(3−1, 2)/2! = 1` (exactly the
shape-fiber count `1` of the gate table). -/

/-- The case-B lattice polygon: width 4, single side `(0,2) → (4,0)` of slope `−1/2`;
column ceilings `(2,2,1,1)`; the only lattice VERTEX among columns 0–3 is the left endpoint
(column 2 is an interior lattice point of the side, not a vertex). -/
def caseBPolygon : L4.LatticePolygon :=
  ⟨4, ![2, 2, 1, 1], fun i => decide (i.1 = 0)⟩

theorem newtonExponent_caseBPolygon : L4.newtonExponent caseBPolygon = 6 := by
  unfold L4.newtonExponent caseBPolygon
  simp [Fin.sum_univ_four]

/-- The case-B node configuration in the `omCount` vocabulary (PIN §1.2 `NodeConfig`):
the slope-`−1/2` polygon, ONE genuine face with two multiplicity-1 linear residual factors,
no descent children (both blocks decided). -/
def caseBConfig : NodeConfig :=
  { polygon := caseBPolygon
    faces := [{ δ := 1, shape := [(1, 1), (1, 1)], dF := 2, punctured := true }]
    children := [] }

theorem volExp_caseBConfig : volExp caseBConfig = 8 := by
  unfold volExp caseBConfig
  simp [newtonExponent_caseBPolygon]

/-- The case-B face choice count at `q = 3`: `ff(q−1, 2)/2! = (3−1)(3−2)/2 = 1` — exactly the
residual-assignment count of the gate table (case B shape-fiber `= 1 × 81`: the only unordered
pair of distinct nonzero residues in `F₃` is `{1, 2}`). -/
theorem choicePoly_caseB_eval :
    (choicePoly true [((1 : ℕ), (1 : ℕ)), (1, 1)]).eval (3 : ℚ) = 1 := by
  unfold choicePoly
  rw [show (([((1 : ℕ), (1 : ℕ)), (1, 1)]).map Prod.fst) = [1, 1] from rfl]
  rw [show ([1, 1] : List ℕ).toFinset = {1} from by decide]
  rw [Finset.prod_singleton]
  rw [show symFactor [((1 : ℕ), (1 : ℕ)), (1, 1)] 1 = 2 from by decide]
  rw [show ([1, 1] : List ℕ).count 1 = 2 from by decide]
  rw [show poolPoly true 1 = availPoly 1 from rfl]
  unfold ffPoly
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, availPoly_one_eval]
  norm_num [availPoly]

theorem mCell_caseBConfig : mCell caseBConfig 3 = 1 := by
  unfold mCell caseBConfig
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    Nat.cast_ofNat]
  exact choicePoly_caseB_eval

/-- **`h_node1_census` (W4e deliverable 3): the omCount tie at case B.**  The graded-law
block-product IMAGE count (`caseB_image_card = 81`, derived THROUGH `pair_card_graded`,
cross-checked against the tuple-level `BlockProduct.gateB_image_card`) relative to the full
level-3 monic box `3^(N·s) = 3^12` EQUALS the `omCount` root bracket `mCell · q^(−volExp)` at
the case-B `NodeConfig` and `q = p = 3`.  SCOPE (verifier finding 2026-07-05): the LHS counts
the image of the block-product map `Set.image mul (bSA ×ˢ bSB)`, NOT the classifier's
multi-block `InCell` fiber; identifying the two is the named obligation **W4d2-surj**
(theorem of the product at level N — gate-verified d2-0, not yet formalized).  What IS proven
here: the restart-side block-product count matches the counting recursion's node bracket.

    81 / 3^12  =  1 · 3^(−8).

This is the first machine-checked link between the `omCount` counting recursion and the
classifier fibers beyond order 0 (`omCount_sepShape_eq_rootCount` covers order 0).  (In the
cluster normalization the same bracket carries `volExp − s = 4` and the `countPivot 4`
divisor — that pivot compensates the self-loop tower, not the level-3 census, so the honest
finite-level tie is the ROOT bracket.) -/
theorem h_node1_census :
    (Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
        (bSA ×ˢ bSB)) : ℚ) / (3 : ℚ) ^ (3 * 4)
      = mCell caseBConfig 3 * ((3 : ℚ) ^ volExp caseBConfig)⁻¹ := by
  rw [caseB_image_card, mCell_caseBConfig, volExp_caseBConfig]
  norm_num

/-- The count-native (division-free) form of the tie: `81 · 3^volExp = mCell · 3^(3·4)`. -/
theorem h_node1_census_count :
    (Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
        (bSA ×ˢ bSB)) : ℚ) * (3 : ℚ) ^ volExp caseBConfig
      = mCell caseBConfig 3 * (3 : ℚ) ^ (3 * 4) := by
  rw [caseB_image_card, mCell_caseBConfig, volExp_caseBConfig]
  norm_num

/-- Numeric gate (banked em-square law): `81 · 3² = 27 · 27` — the case-B node identity in
block-product form, THROUGH the graded law and the coset cards. -/
theorem gate_caseB_em_square :
    Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
        (bSA ×ˢ bSB)) * 3 ^ 2 = 27 * 27 := by
  rw [caseB_law_graded, caseB_card_SA, caseB_card_SB]

/-! ## 4. `h_node1_general` — the hypothesis-gated multi-block node identity -/

/-- **`h_node1_general` (W4e deliverable 4).**  For ANY multi-block cell presented as a block
list `l` with per-block fresh-pattern coset-card certificates `#coset(b) = p^(κ b)` and a
`GradedHensel.GradedChain` certificate (the per-step graded margins M1/M2, conv floor,
pointwise upgrade, and kernel counts — the W4d2′ data), the block-product IMAGE obeys the
em-square product law

    #(imageSet l) · p^X = p^(Σ_b κ b).

Derived from `GradedHensel.blocks_card_graded`.  **SCOPE (verifier 2026-07-05):** `imageSet l`
is the image of the block-coset product under multiplication — the classifier's multi-block
`InCell` fiber is not yet defined, and `imageSet = fiber` (theorem-of-the-product surjectivity)
is the named obligation **W4d2-surj** (gate-verified d2-0, not formalized).  **Discharge status
today (2026-07-04):**
* **Case B** (`p=3, N=3`, blocks `(2,1,1)·(2,1,2)`): the pair-law instance is FULLY
  discharged — `caseB_upgrade` + `caseB_ker_card` supply the pointwise data,
  `caseB_law_graded` is the resulting law (`81·3² = 27·27`), cross-checked against the
  tuple-level `BlockProduct.gateB_image_card`.
* **Cases A** (`p=2, N=5`, blocks `(1,2)·(2,2)`) **and C** (`p=3, N=4`, blocks `(2,2)·(2,1)`):
  the graded margins M1 ∧ M2 HOLD (`gate_margin_graded_A/C`) and the closed-form coset
  products are banked (`BlockProduct.gateA_coset_product`/`gateC_coset_product`), but the
  pointwise `GradedUpgradeAt` + kernel-count certificates are the pending W4d2′ TODOs — at
  those cells this theorem is hypothesis-gated. -/
theorem h_node1_general {l : List (Block p N)} {X : ℕ} (h : GradedChain l X)
    (κ : Block p N → ℕ) (hκ : ∀ b ∈ l, Nat.card b.coset = p ^ κ b) :
    Nat.card (imageSet l) * p ^ X = p ^ ((l.map κ).sum) := by
  have hprod : ∀ (t : List (Block p N)), (∀ b ∈ t, Nat.card b.coset = p ^ κ b) →
      (t.map fun b => Nat.card b.coset).prod = p ^ ((t.map κ).sum) := by
    intro t
    induction t with
    | nil => intro _; simp
    | cons b t ih =>
        intro hbt
        rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, pow_add,
          hbt b (by simp), ih (fun x hx => hbt x (List.mem_cons_of_mem _ hx))]
  rw [blocks_card_graded h, hprod l hκ]

end

end LeanUrat.OM.HNode1
