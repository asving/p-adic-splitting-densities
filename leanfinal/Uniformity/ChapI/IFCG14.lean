/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG12
import Uniformity.ChapI.IFCG13
import Uniformity.ChapI.IFCG4
import Uniformity.ChapI.IFCG2
import Uniformity.ChapI.I02_I03w

/-!
# Uniformity.ChapI.IFCG14 — [A0GA 2026-08-29] the uniform-a0 ASSEMBLY
(nodes A0G-CL + A0G-AS + A0G-DS + A0G-ALL)

**Uniform-a0 campaign, THE ASSEMBLY UNIT** (`docs/in-progress/A0_GENERAL_2026-08-28.md`
§§5–6, rows `A0G-CL0/CL1`, `A0G-AS0/AS1`, `A0G-DS`, `A0G-ALL`; verdict
`runs/wave-c/verdict_A0GA.md`).

## ⚠ SCOPING DISPOSITION — read before consuming anything here

The blueprint's unconditional capstone `decidedSliceAt_all : ∀ n, DecidedSliceAt n` is
**NOT declared in this file**, because it is not reachable by assembly of the landed
inputs.  The landed cover (`IFCG12.finiteGenreCoverAt_strong_all`) is a POLYNOMIAL-level
realization statement and the landed weights (IFCG13) are cone-sum identities in `ℝ`; the
exact finite-level `decidedSeq` recurrence connecting them — blueprint row **A0G-FP0** —
is an explicitly recorded open socket (`runs/wave-c/verdict_A0GW.md`, "Recorded
remainders" item 3), as are the general-`δ` census (IFCG4's header) and the stage-field
base-change laws (row A0G-CL1).  This file therefore lands the four assembly nodes in the
blueprint §2's OWN second display — the named-package architecture — with exactly ONE
socket Prop (`ClusterRecursionAt`, needed only at masses `m ≥ 4`), plus every piece of the
assembly that IS unconditionally provable:

* **§1 A0G-CL** — `DecidedValueLaw` (blueprint §5's display; `Iff.rfl`-pinned to
  `DecidedSliceAt`), the loop-step recurrence carrier `LoopStepLaw` (shift `m`, decay
  `q^{-(T_m - 1)}`; IFC7's hard-coded shift-3/`q^{-5}` recovered by `decide`), and the
  **fixed-point bridge** `decidedValueLaw_of_loopStep`: an exact loop-step recurrence with
  rational base limit yields the rational value law, via IFCG3's
  `decidedDensity_eq_of_step_eq`, with BOTH denominator obligations carried (the
  `X^d − 1` factor never vanishes at `q ≥ 2`).
* **§2 the `n = 1` slice** — `decidedSliceAt_one` (NEW; nowhere landed): the unique monic
  linear type is `⟨{(1,1)}⟩`, values `1/1` and `0/1`.  No positivity guard.
* **§3 A0G-AS** — `Witnessed n σ` and the **off-menu 0/1 law at EVERY degree**
  (`decidedValueLaw_of_unwitnessed`, unconditional); the quantifier reduction
  `decidedSliceAt_of_witnessed_valueLaws`; finiteness of the witnessed labels via the
  landed uniform menu (`IFC6.exists_uniform_coveringMenu`); and the **masses-sum-to-one
  gates** at `n = 2` and `n = 3`, algebraic identities on IFCG13's assembled laws.
* **§4 A0G-DS** — the socket `ClusterRecursionAt m` (given all smaller-degree laws, every
  witnessed degree-`m` label satisfies the exact loop-step recurrence) and
  `decidedSliceAt_of_clusterRecursion` — the STRONG INDUCTION on the degree: `n ≤ 3` from
  the landed slices, `ih` threaded into each socket (all recursive calls syntactically
  `< m`), the one self-call solved only by the §1 fixed-point bridge.
* **§5 A0G-ALL** — `UniformClusterRecursion := ∀ m, 4 ≤ m → ClusterRecursionAt m`;
  `decidedSliceAt_all_of_recursion : UniformClusterRecursion → ∀ n, DecidedSliceAt n`
  (NO `0 < n` guard anywhere); unconditional instantiations at `n = 0, 1, 2, 3` routed
  THROUGH the DS socket; `n = 4` conditional on exactly `ClusterRecursionAt 4`.

## Axiom fence

Lean core everywhere, except the cover re-export pin `cover_for_recursion`
(Lean core + exactly the allowlisted `Uniformity.Density.Tower.exists_dvDissection`,
inherited from `IFCG12.finiteGenreCoverAt_strong_all`).  Zero `sorry` at landing; zero
new axioms; no landed file touched.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFCG14

open IsLocalRing Polynomial
open Uniformity.Density.IFCG3 (bigTLoop kappaLoop)
open Uniformity.Density.IFCG13

/-! ## §1 — node `A0G-CL`: the value-law carrier, the loop-step recurrence, and the
fixed-point bridge -/

section CL

/-- **Blueprint §5's `DecidedValueLaw`, verbatim shape**: one rational function of the
residue cardinality, both denominator obligations, equal to the DECIDED density at every
complete DVR.  Byte-parallel to the body of `DecidedSliceAt` (`I02.lean:98`); the
`Iff.rfl` pin below is the anti-drift regression. -/
def DecidedValueLaw (n : ℕ) (σ : FactorizationType) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        decidedDensity O n σ
          = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-- **THE ANTI-DRIFT PIN**: `DecidedSliceAt n` IS `∀ σ, σ.degree = n → DecidedValueLaw n σ`,
on the nose.  Fails the build the moment either body drifts by an instance binder. -/
example (n : ℕ) : Uniformity.Density.DecidedSliceAt n
    ↔ ∀ σ : FactorizationType, σ.degree = n → DecidedValueLaw n σ := Iff.rfl

/-- **The exact loop-step recurrence at mass `m`** (blueprint §5's scalar equation, at the
`decidedSeq` level): a base sequence `bs` — the non-loop cells' contribution, whose limit
is ONE rational function of `q` uniformly over `O` — plus the diagonal self-call with the
full-box loop weight `q^{1−T_m} = q^{-(T_m−1)}` (IFCG3's `loopVecN_weight` shape), stepping
the precision by the shift `m`.  This is row A0G-FP0's socket SHAPE; IFC7's cubic steps
(shift `3`, factor `q^{-5}`) are the `m = 3` instance (`step_exponent_three` below). -/
def LoopStepLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
      ∃ bs : ℕ → ℝ,
        Filter.Tendsto bs Filter.atTop
          (nhds ((num.eval ((residueCard O : ℕ) : ℚ)
            / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) ∧
        ∀ M : ℕ, bs M + ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M
          = decidedSeq O m σ (M + m)

/-- The step decay exponent at `m = 3` is IFC7's hard-coded `5` — the shape-template gate
(`IFC7.density_ge_of_step` used shift `3` and factor `q^{-5}`). -/
theorem step_exponent_three : bigTLoop 3 - 1 = 5 := by decide

/-- The step decay exponent at `m = 2` is `2` — IFC7 §5's quadratic-rescale factor. -/
theorem step_exponent_two : bigTLoop 2 - 1 = 2 := by decide

/-- The step decay exponent is positive from mass `2` on (`T_m = κ_m + m ≥ m ≥ 2`). -/
theorem step_exponent_pos {m : ℕ} (hm : 2 ≤ m) : 0 < bigTLoop m - 1 := by
  have h := IFCG3.bigTLoop_eq_kappaLoop_add m
  omega

/-- **The geometric denominator never vanishes at `γ ≥ 2`**: `γ^d − 1 ≥ 2^d − 1 ≥ 1` for
`d ≥ 1` — the AS/DS rows' second denominator obligation, isolated. -/
theorem eval_pow_sub_one_ne {d : ℕ} (hd : 0 < d) {γ : ℚ} (hγ : 2 ≤ γ) :
    ((X : Polynomial ℚ) ^ d - 1).eval γ ≠ 0 := by
  rw [eval_sub, eval_pow, eval_X, eval_one]
  have h2d : (1 : ℚ) < 2 ^ d := one_lt_pow₀ (by norm_num) hd.ne'
  have hγd : (2 : ℚ) ^ d ≤ γ ^ d := pow_le_pow_left₀ (by norm_num) hγ d
  intro h0
  have h1 : γ ^ d = 1 := by linarith [sub_eq_zero.mp h0]
  linarith

/-- ★ **THE FIXED-POINT BRIDGE (node A0G-CL's engine)**: an exact loop-step recurrence
with a uniform rational base limit yields the uniform rational VALUE LAW, by IFCG3's
equality solver `decidedDensity_eq_of_step_eq` and the solved fixed point
`B·q^d/(q^d − 1)`, packaged as the pair `(num·X^d, den·(X^d − 1))` — both denominator
obligations discharged (`den·(X^d−1) ≠ 0`, and its value at every `q ≥ 2` nonzero via
`eval_pow_sub_one_ne`).  The ONLY same-mass occurrence in the hypothesis is the diagonal
`decidedSeq O m σ M` term — the CL row's "self-call only under FP" gate. -/
theorem decidedValueLaw_of_loopStep {m : ℕ} (hm : 2 ≤ m) {σ : FactorizationType}
    (h : LoopStepLaw m σ) : DecidedValueLaw m σ := by
  obtain ⟨num, den, hden, hlaw⟩ := h
  have hdpos : 0 < bigTLoop m - 1 := step_exponent_pos hm
  refine ⟨num * X ^ (bigTLoop m - 1), den * (X ^ (bigTLoop m - 1) - 1), ?_, ?_⟩
  · -- the polynomial-level obligation: `X^d − 1 ≠ 0` since it is nonzero at `2`
    refine mul_ne_zero hden (fun hcontra => ?_)
    have h2 := eval_pow_sub_one_ne hdpos (le_refl (2 : ℚ))
    rw [hcontra] at h2
    simp at h2
  · intro O _ _ _ _ _
    obtain ⟨hne, bs, hbs, hstep⟩ := hlaw O
    have hq2 : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by
      exact_mod_cast two_le_residueCard O
    have hXd : ((X : Polynomial ℚ) ^ (bigTLoop m - 1) - 1).eval ((residueCard O : ℕ) : ℚ) ≠ 0 :=
      eval_pow_sub_one_ne hdpos hq2
    refine ⟨by rw [eval_mul]; exact mul_ne_zero hne hXd, ?_⟩
    have hsolve := IFCG3.decidedDensity_eq_of_step_eq (O := O) hdpos hbs hstep
    rw [hsolve, eval_mul, eval_mul, eval_pow, eval_X, eval_sub, eval_pow, eval_X, eval_one]
    have hqR2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
    have hdenR : ((den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hne
    have hqdR : (1 : ℝ) < (residueCard O : ℝ) ^ (bigTLoop m - 1) :=
      one_lt_pow₀ (by linarith) hdpos.ne'
    have hqdR' : (residueCard O : ℝ) ^ (bigTLoop m - 1) - 1 ≠ 0 := by linarith
    push_cast
    field_simp

/-- **The cover, re-exported at the point of its A0G-CL consumption** (the recurrence
socket's mathematical justification): EXHAUSTIVE ∧ DISJOINT ∧ DECREASING over the strong
carrier — `IFCG12.finiteGenreCoverAt_strong_all` verbatim.  The DECREASING clause is the
CL row's "all recursive calls syntactically `< m`" gate at the polynomial level; the
socket `ClusterRecursionAt` below quantifies its smaller-law input by `k < m`
accordingly.  Footprint: Lean core + exactly the C.33 dissection cite. -/
theorem cover_for_recursion :
    IFCG10.StrongCoverExhaustive ∧ IFCG10.StrongCoverDisjoint ∧
      ∀ m : ℕ, IFCG9.DecreasingGenreBankAt m :=
  IFCG12.finiteGenreCoverAt_strong_all

end CL

/-! ## §2 — the `n = 1` slice (new; the last unconditional low-degree slice) -/

section One

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Every monic linear `monicPoly a` has splitting type `⟨{(1,1)}⟩` — the landed
`typeOf_of_natDegree_one` at the coefficient-vector carrier. -/
theorem typeOf_monicPoly_one (a : Fin 1 → O) :
    typeOf (monicPoly a) = (⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ : FactorizationType) :=
  typeOf_of_natDegree_one (monicPoly_monic a) (monicPoly_natDegree a)

end One

/-- **The degree-one slice** (guard-free, like IFCG0's `decidedSliceAt_zero`): the decided
density of `⟨{(1,1)}⟩` is `1` (value `1/1`) and of every other degree-one label is `0`
(value `0/1`), at every complete DVR. -/
theorem decidedSliceAt_one : Uniformity.Density.DecidedSliceAt 1 := by
  intro σ _hσ
  by_cases hσ1 : σ = (⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ : FactorizationType)
  · refine ⟨1, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    have hset : ∀ N, decidedSet O 1 σ N = Set.univ := by
      intro N
      apply Set.eq_univ_of_forall
      intro c a _
      rw [typeOf_monicPoly_one a, hσ1]
    have hseq : ∀ N, decidedSeq O 1 σ N = 1 := by
      intro N
      have hcount : decidedCount O 1 σ N = residueCard O ^ (1 * N) := by
        unfold decidedCount
        rw [hset N, Nat.card_univ, card_coeff]
      have hqne : ((residueCard O : ℝ)) ^ (1 * N) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast (residueCard_pos O).ne')
      unfold decidedSeq
      rw [hcount]
      push_cast
      exact div_self hqne
    have hdensity : decidedDensity O 1 σ = 1 := by
      unfold decidedDensity
      have heq : decidedSeq O 1 σ = fun _ => (1 : ℝ) := funext hseq
      rw [heq]
      exact ciSup_const
    rw [hdensity]
    norm_num
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    have hset : ∀ N, decidedSet O 1 σ N = ∅ := by
      intro N
      apply Set.eq_empty_iff_forall_notMem.2
      intro c hc
      obtain ⟨a, ha⟩ := proj_surjective O 1 N c
      have hty := hc a ha
      rw [typeOf_monicPoly_one a] at hty
      exact hσ1 hty.symm
    have hseq : ∀ N, decidedSeq O 1 σ N = 0 := by
      intro N
      have hcount : decidedCount O 1 σ N = 0 := by
        unfold decidedCount
        rw [hset N]
        simp
      unfold decidedSeq
      rw [hcount]
      simp
    have hdensity : decidedDensity O 1 σ = 0 := by
      unfold decidedDensity
      have heq : decidedSeq O 1 σ = fun _ => (0 : ℝ) := funext hseq
      rw [heq]
      exact ciSup_const
    rw [hdensity]
    norm_num

/-! ## §3 — node `A0G-AS`: off-menu `0/1`, the witnessed reduction, menu finiteness, and
the masses-sum-to-one gates -/

section AS

/-- `σ` is **witnessed** at degree `n`: some monic degree-`n` coefficient vector over some
complete DVR has splitting type `σ`.  The complement is the blueprint §5's "off-menu"
locus. -/
def Witnessed (n : ℕ) (σ : FactorizationType) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    (_ : Finite (IsLocalRing.ResidueField O)) (a : Fin n → O),
    typeOf (monicPoly a) = σ

/-- **The off-menu `0/1` law, at EVERY degree, unconditional** (the AS row's "off-menu
0/1" gate): an unwitnessed label's decided set is empty at every level (every class has a
lift, and no lift has type `σ`), so its decided density is `0 = 0/1`. -/
theorem decidedValueLaw_of_unwitnessed {n : ℕ} {σ : FactorizationType}
    (h : ¬ Witnessed n σ) : DecidedValueLaw n σ := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  have hset : ∀ N, decidedSet O n σ N = ∅ := by
    intro N
    apply Set.eq_empty_iff_forall_notMem.2
    intro c hc
    obtain ⟨a, ha⟩ := proj_surjective O n N c
    exact h ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      a, hc a ha⟩
  have hseq : ∀ N, decidedSeq O n σ N = 0 := by
    intro N
    have hcount : decidedCount O n σ N = 0 := by
      unfold decidedCount
      rw [hset N]
      simp
    unfold decidedSeq
    rw [hcount]
    simp
  have hdensity : decidedDensity O n σ = 0 := by
    unfold decidedDensity
    have heq : decidedSeq O n σ = fun _ => (0 : ℝ) := funext hseq
    rw [heq]
    exact ciSup_const
  rw [hdensity]
  norm_num

/-- **The AS quantifier reduction**: value laws on the witnessed labels alone close the
whole slice — the unwitnessed remainder is `0/1` by the off-menu law. -/
theorem decidedSliceAt_of_witnessed_valueLaws (n : ℕ)
    (h : ∀ σ : FactorizationType, σ.degree = n → Witnessed n σ → DecidedValueLaw n σ) :
    Uniformity.Density.DecidedSliceAt n := by
  intro σ hσ
  by_cases hw : Witnessed n σ
  · exact h σ hσ hw
  · exact decidedValueLaw_of_unwitnessed hw

/-- **Menu finiteness of the witnessed labels** (the AS row's convolution boundary): the
witnessed degree-`n` labels lie in ONE finite menu, uniform over every base — the direct
consumption of the landed `IFC6.exists_uniform_coveringMenu`.  So
`decidedSliceAt_of_witnessed_valueLaws` leaves only FINITELY many obligations at each
degree. -/
theorem witnessed_types_in_menu (n : ℕ) :
    ∃ S : Finset FactorizationType, (∀ σ ∈ S, σ.degree = n) ∧
      ∀ σ : FactorizationType, Witnessed n σ → σ ∈ S := by
  obtain ⟨S, hdeg, hmenu⟩ := IFC6.exists_uniform_coveringMenu n
  refine ⟨S, hdeg, ?_⟩
  rintro σ ⟨O, i1, i2, i3, i4, i5, a, rfl⟩
  exact hmenu O a

/-- **Masses sum to one at `n = 2`** (the AS row's algebraic total-mass gate, mass-2
instance): the three assembled quadratic laws of IFCG13's weight calculus add to exactly
`1`. -/
theorem n2_masses_sum_to_one {q : ℝ} (hq : 2 ≤ q) :
    n2Density (q * (q - 1) / 2) (clusterP2 shallow2Split q) q
      + n2Density ((q ^ 2 - q) / 2) (clusterP2 shallow2Inert q) q
      + n2Density 0 (clusterP2 shallow2Ram q) q = 1 := by
  rw [n2_gate_split hq, n2_gate_inert hq, n2_gate_ram hq]
  have h1 : q + 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- **Masses sum to one at `n = 3`** (mass-3 instance): the five assembled cubic laws add
to exactly `1` — the algebraic mirror of H97b's `totalMass_three`, here PURELY from the
weight calculus's gate values. -/
theorem n3_masses_sum_to_one {q : ℝ} (hq : 2 ≤ q) :
    n3Density (q * (q - 1) * (q - 2) / 6) (clusterP2 shallow2Split q)
        (clusterP3 shallow3Split q) q
      + n3Density (q * ((q ^ 2 - q) / 2)) (clusterP2 shallow2Inert q)
        (clusterP3 shallow3LinInert q) q
      + n3Density ((q ^ 3 - q) / 3) 0 (clusterP3 shallow3Inert q) q
      + n3Density 0 (clusterP2 shallow2Ram q) (clusterP3 shallow3LinRam q) q
      + n3Density 0 0 (clusterP3 shallow3Ram q) q = 1 := by
  rw [n3_gate_split hq, n3_gate_linInert hq, n3_gate_inert hq, n3_gate_linRam hq,
    n3_gate_ram hq]
  have hq0 : 0 < q := by linarith
  have h1 : q + 1 ≠ 0 := by nlinarith
  have h2 : (0 : ℝ) < q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
    nlinarith [pow_pos hq0 4, pow_pos hq0 3, pow_pos hq0 2]
  field_simp
  ring

end AS

/-! ## §4 — node `A0G-DS`: the recursion socket and the strong induction -/

section DS

/-- **THE SOCKET (row A0G-FP0's remaining content, as ONE named Prop)**: at mass `m`,
GIVEN the value laws at every strictly smaller degree (the CL row's "all recursive calls
syntactically `< m`" — the `k < m` quantifier), every witnessed degree-`m` label
satisfies the exact loop-step recurrence with a uniform rational base limit.  Its future
discharge is the finite-level census tying the cover's cells (`cover_for_recursion`) to
the weights' cone sums — exactly the boundary recorded in `verdict_A0GW.md` item 3. -/
def ClusterRecursionAt (m : ℕ) : Prop :=
  (∀ k, k < m → ∀ σ : FactorizationType, σ.degree = k → DecidedValueLaw k σ) →
  ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ → LoopStepLaw m σ

/-- ★ **NODE A0G-DS — the slice socket** (`decidedSliceAt_of_clusterRecursion`): the
strong induction on the degree.  Degrees `0–3` are the landed slices (`IFCG0`,
`decidedSliceAt_one`, `I02_I03w`, `IFC7`); from `4` on, the induction hypothesis feeds
the socket, the off-menu remainder is `0/1`, and the witnessed labels are solved by the
§1 fixed-point bridge — the theorem body constructs the numerator/denominator pair with
both nonzeroness obligations (the DS row's gate). -/
theorem decidedSliceAt_of_clusterRecursion :
    ∀ n : ℕ, (∀ m, 4 ≤ m → m ≤ n → ClusterRecursionAt m) →
      Uniformity.Density.DecidedSliceAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hpack
    rcases Nat.lt_or_ge n 4 with hn | hn
    · -- the landed low-degree slices: 0 (IFCG0), 1 (§2 above), 2 (I02_I03w), 3 (IFC7)
      interval_cases n
      · exact IFCG0.decidedSliceAt_zero
      · exact decidedSliceAt_one
      · exact Uniformity.Density.decidedSliceAt_two
      · exact Uniformity.Density.IFC7.decidedSliceAt_three
    · -- from mass 4 on: off-menu labels are 0/1; witnessed labels get the socket's
      -- recurrence — fed with the STRICTLY SMALLER laws from the induction hypothesis
      -- (the CL row's "all recursive calls syntactically < m") — and the one
      -- same-degree occurrence is solved by the §1 fixed-point bridge alone.
      apply decidedSliceAt_of_witnessed_valueLaws
      intro σ hσ hwit
      have hsmaller : ∀ k, k < n → ∀ σ' : FactorizationType,
          σ'.degree = k → DecidedValueLaw k σ' := by
        intro k hk
        exact ih k hk (fun m' h4 hle => hpack m' h4 (le_trans hle (Nat.le_of_lt hk)))
      exact decidedValueLaw_of_loopStep (by omega)
        (hpack n (by omega) le_rfl hsmaller σ hσ hwit)

end DS

/-! ## §5 — node `A0G-ALL`: the capstone, in its honest conditional form -/

section ALL

/-- **The campaign's single remaining research input, packaged**: the exact loop-step
recurrence at every mass `≥ 4`.  (Masses `0–3` need no socket: their slices are landed.) -/
def UniformClusterRecursion : Prop := ∀ m, 4 ≤ m → ClusterRecursionAt m

/-- ★ **NODE A0G-ALL, conditional form**: the a0 capstone field at EVERY degree — with NO
`0 < n` guard — from the recursion package alone.  The blueprint §2's unconditional
`decidedSliceAt_all` is exactly this theorem with `UniformClusterRecursion` discharged;
that name is deliberately NOT declared here (see the header disposition). -/
theorem decidedSliceAt_all_of_recursion (h : UniformClusterRecursion) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  fun n => decidedSliceAt_of_clusterRecursion n (fun m h4 _ => h m h4)

-- **The ALL row's `#check` gate, conditional form.**
#check @decidedSliceAt_all_of_recursion

/-- The vacuous package at degrees `≤ 3`: no socket below mass `4`. -/
theorem vacuousPackage {n : ℕ} (hn : n ≤ 3) :
    ∀ m, 4 ≤ m → m ≤ n → ClusterRecursionAt m :=
  fun m h4 hle => absurd (le_trans h4 hle) (by omega)

-- **Instantiations (the ALL row's gate): `n = 0, 1, 2, 3` UNCONDITIONAL, routed through
-- the DS socket; `n = 4` conditional on exactly its own recurrence.**
example : Uniformity.Density.DecidedSliceAt 0 :=
  decidedSliceAt_of_clusterRecursion 0 (vacuousPackage (by omega))
example : Uniformity.Density.DecidedSliceAt 1 :=
  decidedSliceAt_of_clusterRecursion 1 (vacuousPackage (by omega))
example : Uniformity.Density.DecidedSliceAt 2 :=
  decidedSliceAt_of_clusterRecursion 2 (vacuousPackage (by omega))
example : Uniformity.Density.DecidedSliceAt 3 :=
  decidedSliceAt_of_clusterRecursion 3 (vacuousPackage (by omega))
example (h : ClusterRecursionAt 4) : Uniformity.Density.DecidedSliceAt 4 :=
  decidedSliceAt_of_clusterRecursion 4 (fun m h4 hle => by
    have hm : m = 4 := by omega
    exact hm ▸ h)

end ALL

end Uniformity.Density.IFCG14

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` on
every declaration EXCEPT `cover_for_recursion` (Lean core + exactly
`Uniformity.Density.Tower.exists_dvDissection`, inherited from the landed cover). -/

#print axioms Uniformity.Density.IFCG14.step_exponent_pos
#print axioms Uniformity.Density.IFCG14.eval_pow_sub_one_ne
#print axioms Uniformity.Density.IFCG14.decidedValueLaw_of_loopStep
#print axioms Uniformity.Density.IFCG14.cover_for_recursion
#print axioms Uniformity.Density.IFCG14.typeOf_monicPoly_one
#print axioms Uniformity.Density.IFCG14.decidedSliceAt_one
#print axioms Uniformity.Density.IFCG14.decidedValueLaw_of_unwitnessed
#print axioms Uniformity.Density.IFCG14.decidedSliceAt_of_witnessed_valueLaws
#print axioms Uniformity.Density.IFCG14.witnessed_types_in_menu
#print axioms Uniformity.Density.IFCG14.n2_masses_sum_to_one
#print axioms Uniformity.Density.IFCG14.n3_masses_sum_to_one
#print axioms Uniformity.Density.IFCG14.decidedSliceAt_of_clusterRecursion
#print axioms Uniformity.Density.IFCG14.decidedSliceAt_all_of_recursion
