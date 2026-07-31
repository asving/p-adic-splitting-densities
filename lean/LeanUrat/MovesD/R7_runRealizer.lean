/-
Unit R7-RUN  (O-14a′ wave-2 EXECUTION: the RunRealizerExists fill, 2026-07-31)

[Charge: `notes/openmath/O14ap_phaseB_attempt.md` §4.2 — the compiled critical-path
residue `RunRealizerExists p (ZMod p)` is PROVED AS MATHEMATICS (O-14a′ Theorem 1
(prime-field collapse) + Theorem 3 (last-node flank) + Corollary 4); this module is
the Lean fill per the recipe, so that TreeCan's (†15) pair `canPolicy`/`canPolicy_pin`
discharges through `R7_polFillReduction.canPolicyC_pin`.]

## What is proved here (0 sorry)

1. `subfield_zmod_eq_top` / `node_g_eq_one` — the PRIME-FIELD COLLAPSE (O-14a′ Thm 1(i)):
   every subfield of `ZMod p` is ⊤, so every node's descend polynomial ψ (irreducible
   over K = ⊤ with the recorded root z̄ ∈ F = K) is linear: g = 1 at EVERY node.
2. `frame_deg_one` — Thm 1(ii): every frame key of a coherent history over `ZMod p` is
   linear (width-chain induction; e = 1 from `hspecRec` at recenterings and from the
   RG-2 recording fence at interior non-recentering reads — the fence is RIDDEN AS A
   HYPOTHESIS exactly where the note's recipe says so; see the SCOPE note below).
3. `stage_w_key_sub_lift` — the Lemma-3.2(iii) NO-JUMP law: at an e = 1 stage,
   `w(Φ − t) = w(Φ)` for a center-realizer lift t (else `hRlt` + `hRΦ` force
   `T 1 = C c̃`, refuted at the coefficient level; c̃ ≠ 0 is node typing).
4. `anchor_threshold` content (Lemma 3.1, inlined in `terminal_center_realizer`):
   at the run-anchor b (last non-recentering read at b−1), `σ_b.wPrev(Φ_b) = h_{b−1}`
   — the regrade slot-minimum evaluated on the (e = g = 1)-collapsed `IsNodeLift`
   display — and `h_{b−1} < h_b` from the slope law (C2) + strict steepening (C7)
   (all scale factors = 1 over the prime field: `strFrame_eq_one`, `frame_deg_one`).
5. `terminal_center_realizer` — O-14a′ THEOREM 3 at F = ZMod p: at a coherent history
   whose FINAL node is a recentering, an (S6b) realizer exists at the terminal frame
   (apply `hS6b` at the anchor stage; transport along the recentering run by the
   `IsRecentering` w/digPrime records — Lemma 3.2 collapsed to the prime field, where
   `digPrime` transport suffices because every residual in sight is a T-0 constant).
6. `runRealizerExists_zmod` — **COROLLARY 4**: `RunRealizerExists p (ZMod p)` for every
   prime p.  Interior nodes: `interior_center_realizer_exists` (on file) + the support
   clause free at deg Φ = 1 (Thm 1(iii), `canRealizes_support_of_constant`).  Terminal
   node: (5).  This is THE one Prop `canPolicyC_pin` consumes: the (†15) pair fills.

## SCOPE (honesty, load-bearing — O-14a′ §0 items 2/4 and §5.5)

* Thm 1(ii) consumes the RG-2 recording fence (`HistoryCoherent`'s disclosed
  definitional scope restriction: interior non-recentering reads pinned to e = 1).
  This proof is exactly as conditional as the fence.  **FENCE-LIFT FLAG**: if RG-2 is
  ever lifted, (CR2) regains content at ZMod p and is then REFUTABLE at the intended
  stages (O-14a′ §5.5's weight-lattice mechanism over a unit-shifted root key) — the
  (CR2) re-adjudication to the faithful (S6b′-SUPP) law is a PREREQUISITE of any fence
  lift.  Recorded forward obligation, not a silent claim.
* THINNESS (disclosed): over the prime ambient field the recorded tree model carries
  only linear-key towers — the compiled typing's consequence (subfield-tracked residues
  in a prime field + the fence), consistent with the order-0-slice scope.  Report this
  whenever the (†15) discharge is cited: the pin is real, at this recorded scope.
* At general F the compiled support clause is REFUTED-AS-STATED (O-14a′ Thm 5, the
  (3, 𝔽₉) countermodel); nothing here quantifies beyond F = ZMod p.

moves_ref: O14ap_phaseB_attempt.md §§2–4 (Thm 1, Lemmas 3.1/3.2, Thm 3, Cor 4) +
PolPin/R7_polFillReduction (the consumer seam).
deps: R7_polFillReduction (CanRealizes/RunRealizerExists/canPolicyC), Moves.ResVal
(w_one/w_neg/CT_apply engine).
difficulty: medium (the terminal flank is a genuine two-lemma induction).
hypothesis_fields: none (everything proved; the fence rides inside `HistoryCoherent`).
-/
import Mathlib
import LeanUrat.MovesD.R7_polFillReduction
import LeanUrat.Moves.ResVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

open Polynomial LeanUrat.Moves LeanUrat.MovesC

/-! ## 1. The prime-field collapse (O-14a′ Theorem 1(i)) -/

section PrimeField

variable {p : ℕ} [Fact p.Prime]

/-- Every subfield of the prime field `ZMod p` is ⊤ (a subfield contains 1, hence the
image of ℕ, which is everything). O-14a′ Thm 1(i), first half. -/
theorem subfield_zmod_eq_top (K : Subfield (ZMod p)) : K = ⊤ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ext x
  simp only [Subfield.mem_top, iff_true]
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  exact natCast_mem K n

/-- **g = 1 at every node over the prime ambient field** (O-14a′ Thm 1(i)): the recorded
descend polynomial ψ is irreducible over K with the recorded root z̄ ∈ F = K (prime-field
collapse), hence linear; `hψdeg` reads g off it. -/
theorem node_g_eq_one (ν : Node p (ZMod p)) : ν.g = 1 := by
  have hK := subfield_zmod_eq_top ν.σ.K
  have hzmem : ((ν.zbar : (ZMod p)ˣ) : ZMod p) ∈ ν.σ.K := by rw [hK]; trivial
  set z : ↥ν.σ.K := ⟨((ν.zbar : (ZMod p)ˣ) : ZMod p), hzmem⟩ with hz
  have hroot : ν.ψ.IsRoot z := by
    have h0 : Polynomial.eval₂ ν.σ.K.subtype (ν.σ.K.subtype z) ν.ψ = 0 := ν.hzbarRoot
    rw [Polynomial.eval₂_at_apply] at h0
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp h0
  have hdeg1 : ν.ψ.degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_root ν.hψirr hroot
  have hnat : ν.ψ.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg1
  have := ν.hψdeg
  omega

end PrimeField

/-! ## 2. General-F stage lemmas: e = 1 pinnings, the no-jump law, digPrime readers -/

section StageLemmas

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- At an unramified stage the canonical Bézout pair is (1, 0): `s = 1`. -/
theorem stage_s_eq_one (σ : Stage p F) (he : σ.e = 1) : σ.s = 1 := by
  have ht := σ.he1t he
  have hb := σ.hbez
  rw [he, ht] at hb
  push_cast at hb
  linarith

/-- **The no-jump law** (O-14a′ Lemma 3.2(iii) kernel): at an `e = 1` stage, subtracting a
center-realizer lift (weight `w(Φ)`, digit a nonzero T-0 constant) does not raise the key
weight: `w(Φ − t) = w(Φ)`.  If it did, `hRlt` on `Φ = t + (Φ − t)` would force
`R(Φ) = R(t)`, i.e. `T 1 = C c̃ · T 0` — refuted at the coefficient at 0 (`c̃ ≠ 0`). -/
theorem stage_w_key_sub_lift (σ : Stage p F) (he : σ.e = 1) (cc : ↥σ.K)
    (tt : Polynomial ℤ_[p]) (hcc : cc ≠ 0) (htne : tt ≠ 0)
    (hwt : σ.w tt = σ.w σ.Φ)
    (hRt : σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T 0)
    (hsubne : σ.Φ - tt ≠ 0) :
    σ.w (σ.Φ - tt) = σ.w σ.Φ := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hwneg : σ.w (-tt) = σ.w tt := ResVal.w_neg σ tt htne
  -- ultrametric lower bound: w(Φ − t) ≥ w(Φ)
  have hge : σ.w σ.Φ ≤ σ.w (σ.Φ - tt) := by
    have h := σ.hwult σ.Φ (-tt) hΦne (neg_ne_zero.mpr htne)
      (by rwa [← sub_eq_add_neg])
    rw [hwneg, hwt, min_self, ← sub_eq_add_neg] at h
    exact h
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact heq.symm
  · exfalso
    have hsum : tt + (σ.Φ - tt) = σ.Φ := by ring
    have hReq : σ.R (tt + (σ.Φ - tt)) = σ.R tt :=
      σ.hRlt tt (σ.Φ - tt) htne hsubne (by rw [hsum]; exact hΦne)
        (by rw [hwt]; exact hlt)
    rw [hsum, σ.hRΦ, hRt, stage_s_eq_one σ he] at hReq
    -- hReq : T 1 = C cc * T 0 — compare coefficients at 0
    have hT1 : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ↥σ.K)
        = LaurentPolynomial.C (1 : ↥σ.K) * LaurentPolynomial.T 1 := by
      rw [map_one, one_mul]
    rw [hT1] at hReq
    have h0 := congrArg (fun x : LaurentPolynomial ↥σ.K => x (0 : ℤ)) hReq
    simp only [ResVal.CT_apply] at h0
    norm_num at h0
    exact hcc h0.symm

/-- Reading `digPrime` off a T-0 constant residual: `digPrime z̄ t = c` (any z̄). -/
theorem digPrime_of_R_C_T0 (σ : Stage p F) (zbar : Fˣ) (t : Polynomial ℤ_[p]) (c : ↥σ.K)
    (h : σ.R t = LaurentPolynomial.C c * LaurentPolynomial.T 0) :
    σ.digPrime zbar t = (c : F) := by
  unfold Stage.digPrime
  rw [h, LaurentPolynomial.T_zero, mul_one, LaurentPolynomial.eval₂_C]
  rfl

/-- **The regrade slot-minimum on the (e = g = 1)-collapsed lift display** (O-14a′
Lemma 3.1(b), prime-field form): if `Φb = Φp + t₀` with `t₀` either absent or a
realizer of weight `h'`, then the `(1, h')`-slot-minimum weight of `Φb` over `w` is
exactly `h'`. -/
theorem slotmin_w_linear_lift (σp : Stage p F) (wV : Polynomial ℤ_[p] → ℤ) (h' : ℕ)
    (hslot : IsSlotMinWeight wV σp.Φ 1 h' σp.w)
    (Φb t0 : Polynomial ℤ_[p]) (hΦbne : Φb ≠ 0)
    (ht0 : t0 = 0 ∨ (t0 ≠ 0 ∧ inC σp.Φ t0 ∧ σp.w t0 = (h' : ℤ)))
    (hdisp : Φb = σp.Φ + t0) :
    wV Φb = (h' : ℤ) := by
  have hΦpne : σp.Φ ≠ 0 := σp.hmonic.ne_zero
  have hΦpdeg : (0 : WithBot ℕ) < σp.Φ.degree := by
    have h1 : 1 ≤ σp.Φ.natDegree := σp.hdeg
    have h2 := Polynomial.degree_eq_natDegree hΦpne
    rw [h2]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hdev : IsDevelopment σp.Φ Φb
      (fun j => match j with | 0 => t0 | 1 => 1 | _ + 2 => 0) 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rcases j with _ | _ | k
      · show t0.degree < σp.Φ.degree
        rcases ht0 with h | ⟨-, hin, -⟩
        · rw [h, Polynomial.degree_zero]
          exact lt_of_le_of_lt bot_le hΦpdeg
        · exact hin
      · show (1 : Polynomial ℤ_[p]).degree < σp.Φ.degree
        rw [Polynomial.degree_one]
        exact hΦpdeg
      · show (0 : Polynomial ℤ_[p]).degree < σp.Φ.degree
        rw [Polynomial.degree_zero]
        exact lt_of_le_of_lt bot_le hΦpdeg
    · intro j hj
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      rfl
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      show Φb = t0 * σp.Φ ^ 0 + 1 * σp.Φ ^ 1
      rw [hdisp]; ring
  obtain ⟨hle, j, hjlt, hnz, heq⟩ := hslot Φb _ 2 hΦbne hdev
  have hw1 : σp.w 1 = 0 := ResVal.w_one σp
  -- both admissible slots weigh exactly h'
  interval_cases j
  · -- j = 0: the slot carries t0 ≠ 0, weight w(t0) + 0·h' = h'
    have hnz0 : t0 ≠ 0 := hnz
    rcases ht0 with h | ⟨-, -, hw⟩
    · exact absurd h hnz0
    · rw [heq]
      show ((1 : ℕ) : ℤ) * σp.w t0 + ((0 : ℕ) : ℤ) * (h' : ℤ) = (h' : ℤ)
      rw [hw]
      push_cast
      ring
  · -- j = 1: the slot carries 1, weight w(1) + 1·h' = h'
    rw [heq]
    show ((1 : ℕ) : ℤ) * σp.w 1 + ((1 : ℕ) : ℤ) * (h' : ℤ) = (h' : ℤ)
    rw [hw1]
    push_cast
    ring

/-- The (CR2) support clause is FREE at a constant realizer over an `e = 1` node
(O-14a′ Thm 1(iii)): take j₀ = 0 — the congruence is vacuous mod 1 and the support of a
degree-≤-0 polynomial is contained in {0} = {j₀ + 0·e}. -/
theorem canRealizes_support_of_constant (ν : Node p F) (he : ν.e = 1)
    (t : Polynomial ℤ_[p]) (hdeg : t.degree ≤ 0) :
    ∃ j₀ : ℕ, (j₀ : ℤ) % (ν.e : ℤ) = (bezT ν.e ν.h * ν.gam) % (ν.e : ℤ) ∧
      ∀ j ∈ t.support, ∃ k : ℕ, k < ν.g ∧ j = j₀ + k * ν.e := by
  refine ⟨0, ?_, ?_⟩
  · rw [he]
    simp
  · intro j hj
    have hle : j ≤ t.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    have hnat : t.natDegree = 0 :=
      Nat.le_zero.mp (Polynomial.natDegree_le_iff_degree_le.mpr (by simpa using hdeg))
    exact ⟨0, ν.hg, by omega⟩

/-- `inC` at a linear key forces a constant (degree ≤ 0). -/
theorem degree_le_zero_of_inC_linear {Φ t : Polynomial ℤ_[p]} (hΦne : Φ ≠ 0)
    (hΦ : Φ.natDegree = 1) (h : inC Φ t) : t.degree ≤ 0 := by
  have hΦdeg : Φ.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hΦne, hΦ]
    rfl
  have : t.degree < 1 := by rw [← hΦdeg]; exact h
  exact Nat.WithBot.lt_one_iff_le_zero.mp this

/-- Converse packaging: a constant is `inC` any linear key. -/
theorem inC_of_degree_le_zero_linear {Φ t : Polynomial ℤ_[p]} (hΦne : Φ ≠ 0)
    (hΦ : Φ.natDegree = 1) (h : t.degree ≤ 0) : inC Φ t := by
  have hΦdeg : Φ.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hΦne, hΦ]
    rfl
  rw [inC, hΦdeg]
  exact lt_of_le_of_lt h (by norm_num)

end StageLemmas

/-! ## 3. History-level collapse over the prime field -/

section HistoryLevel

variable {p : ℕ} [Fact p.Prime]

/-- Interior nodes read at stride e = 1: recenterings by `hspecRec`, non-recentering
reads by the RG-2 recording fence (the disclosed scope restriction this unit RIDES AS A
HYPOTHESIS — see the module header). -/
theorem interior_node_e_eq_one {F : Type*} [Field F] [Finite F] {H : History p F}
    (hH : HistoryCoherent H) {i : ℕ} (hi : i + 1 < H.nodes.length) :
    (H.nodes[i]'(by omega)).e = 1 := by
  by_cases hrec : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering
  · exact ((H.nodes[i]'(by omega)).hspecRec hrec).1
  · exact ((hH.2.2.2 i hi).2.1 hrec).1

/-- **O-14a′ Thm 1(ii)**: every frame key of a coherent history over `ZMod p` is linear
(width-chain induction; every interior stride and every descend degree is 1). -/
theorem frame_deg_one {H : History p (ZMod p)} (hH : HistoryCoherent H) :
    ∀ (i : ℕ) (hi : i < H.nodes.length), (H.nodes[i]'hi).σ.Φ.natDegree = 1 := by
  intro i
  induction i with
  | zero => intro hi; exact hH.1 hi
  | succ n ih =>
    intro hi
    have hn : n < H.nodes.length := by omega
    have hwidth := (hH.2.2.2 n hi).2.2.2.2.2.1
    have he := interior_node_e_eq_one hH hi
    have hg := node_g_eq_one (H.nodes[n]'hn)
    have hD : (H.nodes[n]'hn).Dwidth = 1 := by
      rw [(H.nodes[n]'hn).hDwidth]; exact ih hn
    have hcw : (H.nodes[n]'hn).childWidth = 1 := by
      unfold Node.childWidth; rw [he, hg, hD]
    have hD1 := (H.nodes[n+1]'hi).hDwidth
    rw [hwidth, hcw] at hD1
    omega

/-- Over the prime field the accumulated stretch is trivial: `STR_i = 1` (every factor is
an interior read's e = 1). -/
theorem strFrame_eq_one {F : Type*} [Field F] [Finite F] {H : History p F}
    (hH : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length) :
    H.strFrame i = 1 := by
  unfold History.strFrame
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨ν, hν, rfl⟩ := hx
  rw [List.mem_iff_getElem] at hν
  obtain ⟨j, hj, rfl⟩ := hν
  have hjlen : j < i := by
    have := hj
    rw [List.length_take] at this
    omega
  rw [List.getElem_take]
  exact interior_node_e_eq_one hH (by omega)

/-- The slope law (C2) + strict steepening (C7) collapse to `h_i < h_{i+1}` over the
prime field (all scale factors are 1) — O-14a′ Lemma 3.1(c), prime-field form. -/
theorem node_h_lt_h_succ {H : History p (ZMod p)} (hH : HistoryCoherent H) {i : ℕ}
    (hi : i + 1 < H.nodes.length)
    (he : (H.nodes[i]'(by omega)).e = 1) (he' : (H.nodes[i+1]'hi).e = 1) :
    (H.nodes[i]'(by omega)).h < (H.nodes[i+1]'hi).h := by
  have hC2i := hH.2.1 i (by omega)
  have hC2i1 := hH.2.1 (i+1) hi
  have hsteep := (hH.2.2.2 i hi).2.2.2.2.2.2
  have hSi := strFrame_eq_one hH i (by omega)
  have hSi1 := strFrame_eq_one hH (i+1) hi
  have hDi : (H.nodes[i]'(by omega)).Dwidth = 1 := by
    rw [(H.nodes[i]'(by omega)).hDwidth]; exact frame_deg_one hH i (by omega)
  have hDi1 : (H.nodes[i+1]'hi).Dwidth = 1 := by
    rw [(H.nodes[i+1]'hi).hDwidth]; exact frame_deg_one hH (i+1) hi
  rw [he, hSi, hDi] at hC2i
  rw [he', hSi1, hDi1] at hC2i1
  norm_num at hC2i hC2i1
  rw [hC2i, hC2i1] at hsteep
  exact_mod_cast hsteep

/-- The maximal terminal recentering run has a start: a last non-recentering read at
some index c < i, with every node in (c, i] a recentering.  (Node 0 is the root, so the
descent below i terminates strictly above 0.) -/
theorem exists_run_start {F : Type*} [Field F] [Finite F] {H : History p F}
    {i : ℕ} (hi : i < H.nodes.length)
    (hreci : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    ∃ c : ℕ, c < i ∧
      (∀ hc : c < H.nodes.length, (H.nodes[c]'hc).species ≠ ReadSpecies.recentering) ∧
      (∀ (j : ℕ) (hj : j < H.nodes.length), c < j → j ≤ i →
        (H.nodes[j]'hj).species = ReadSpecies.recentering) := by
  suffices h : ∀ (r : ℕ), r ≤ i →
      (∀ (j : ℕ) (hj : j < H.nodes.length), r ≤ j → j ≤ i →
        (H.nodes[j]'hj).species = ReadSpecies.recentering) →
      ∃ c : ℕ, c < i ∧
        (∀ hc : c < H.nodes.length, (H.nodes[c]'hc).species ≠ ReadSpecies.recentering) ∧
        (∀ (j : ℕ) (hj : j < H.nodes.length), c < j → j ≤ i →
          (H.nodes[j]'hj).species = ReadSpecies.recentering) by
    refine h i le_rfl (fun j hj h1 h2 => ?_)
    have hji : j = i := le_antisymm h2 h1
    subst hji
    exact hreci
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hri hrun
    match r with
    | 0 =>
      exfalso
      have h0len : 0 < H.nodes.length := by omega
      have hroot : (H.nodes[0]'h0len).species = ReadSpecies.root :=
        (H.root_iff 0 h0len).mpr rfl
      have hrec0 := hrun 0 h0len le_rfl (by omega)
      rw [hroot] at hrec0
      exact ReadSpecies.noConfusion hrec0
    | r' + 1 =>
      have hr'len : r' < H.nodes.length := by omega
      by_cases hprev : (H.nodes[r']'hr'len).species = ReadSpecies.recentering
      · refine ih r' (by omega) (by omega) (fun j hj h1 h2 => ?_)
        by_cases hjr : j = r'
        · subst hjr; exact hprev
        · exact hrun j hj (by omega) h2
      · exact ⟨r', by omega, fun _ => hprev,
          fun j hj h1 h2 => hrun j hj (by omega) h2⟩

end HistoryLevel

/-! ## 4. The last-node flank (O-14a′ Theorem 3 at F = ZMod p) and Corollary 4 -/

section Terminal

variable {p : ℕ} [Fact p.Prime]

/-- **O-14a′ THEOREM 3 (the last-node flank), at F = ZMod p**: at a coherent history whose
FINAL node is a recentering, a center realizer exists — nonzero, constant, in the
coefficient space, key weight, digit = the recorded center at position 0.  Proof: find the
run anchor b = c+1 (Lemma 3.1: the regrade slot-minimum on the collapsed lift display gives
`wPrev_b(Φ_b) = h_c`, and (C2)+(C7) give `h_c < h_b` — the (S6b) threshold); apply `hS6b`
at σ_b with the terminal center's value (nonzero by node typing, in K by the prime-field
collapse); transport along the recentering run by the `IsRecentering` w/digPrime records
(Lemma 3.2; the no-jump law keeps the key weight); read the digit back through `hS5`. -/
theorem terminal_center_realizer {H : History p (ZMod p)} (hH : HistoryCoherent H)
    {i : ℕ} (hi : i < H.nodes.length) (hlast : i + 1 = H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    ∃ t : Polynomial ℤ_[p], t ≠ 0 ∧ t.degree ≤ 0 ∧
      inC (H.nodes[i]'hi).σ.Φ t ∧
      (H.nodes[i]'hi).σ.w t = (H.nodes[i]'hi).σ.w (H.nodes[i]'hi).σ.Φ ∧
      (H.nodes[i]'hi).σ.R t
        = LaurentPolynomial.C (H.nodes[i]'hi).center * LaurentPolynomial.T 0 := by
  classical
  -- the terminal center, as an ambient-field value; nonzero by node typing (z̄ a unit)
  set cF : ZMod p := ((H.nodes[i]'hi).center : ZMod p) with hcF
  have hcFne : cF ≠ 0 := by
    have hcen := ((H.nodes[i]'hi).hspecRecCenter hrec).2
    rw [hcF, ← hcen]
    exact Units.ne_zero _
  -- the maximal terminal recentering run (c, i], anchor read at c
  obtain ⟨c, hci, hcnot, hcrun⟩ := exists_run_start hi hrec
  have hc1 : c + 1 < H.nodes.length := by omega
  have hclen : c < H.nodes.length := by omega
  -- ANCHOR (Lemma 3.1): the (C4-non) transition record at index c
  obtain ⟨-, hnonrec, -, -, -, -, -⟩ := hH.2.2.2 c hc1
  obtain ⟨hfence, σV, hreg, hlift, htrans⟩ := hnonrec (hcnot hclen)
  have hrecb : (H.nodes[c+1]'hc1).species = ReadSpecies.recentering :=
    hcrun (c+1) hc1 (by omega) (by omega)
  -- (a) σ_b.e = 1
  have hbe : (H.nodes[c+1]'hc1).σ.e = 1 := by
    rw [htrans.base.child_e]
    exact ((H.nodes[c+1]'hc1).hspecRec hrecb).1
  -- (b) σ_b.wPrev(Φ_b) = h_c via the regrade slot minimum on the collapsed lift display
  have hg := node_g_eq_one (H.nodes[c]'hclen)
  obtain ⟨tt, htt0, httlaw, hdisp⟩ := hlift
  rw [hfence, hg] at hdisp
  have hdisp' : (H.nodes[c+1]'hc1).σ.Φ = (H.nodes[c]'hclen).σ.Φ + tt 0 := by
    rw [hdisp, Finset.sum_range_one]
    norm_num
  have ht0alt : tt 0 = 0 ∨ (tt 0 ≠ 0 ∧ inC (H.nodes[c]'hclen).σ.Φ (tt 0) ∧
      (H.nodes[c]'hclen).σ.w (tt 0) = ((H.nodes[c]'hclen).h : ℤ)) := by
    by_cases hψ0 : (H.nodes[c]'hclen).ψ.coeff 0 = 0
    · exact Or.inl (htt0 0 hψ0)
    · obtain ⟨hne, hin, hw, -⟩ := httlaw 0 (by omega) hψ0
      refine Or.inr ⟨hne, hin, ?_⟩
      rw [hw, hg]
      push_cast
      ring
  have hslotm := hreg.2.2.2.2.2.2.2
  rw [hfence] at hslotm
  have hwV : σV.w ((H.nodes[c+1]'hc1).σ.Φ) = ((H.nodes[c]'hclen).h : ℤ) :=
    slotmin_w_linear_lift (H.nodes[c]'hclen).σ σV.w (H.nodes[c]'hclen).h hslotm
      ((H.nodes[c+1]'hc1).σ.Φ) (tt 0) ((H.nodes[c+1]'hc1).σ.hmonic.ne_zero) ht0alt hdisp'
  have hwPrevΦb : (H.nodes[c+1]'hc1).σ.wPrev ((H.nodes[c+1]'hc1).σ.Φ)
      = ((H.nodes[c]'hclen).h : ℤ) := by
    rw [htrans.base.child_wPrev]
    exact hwV
  -- (c) the strict threshold h_c < σ_b.h
  have hhlt : (H.nodes[c]'hclen).h < (H.nodes[c+1]'hc1).h :=
    node_h_lt_h_succ hH hc1 hfence ((H.nodes[c+1]'hc1).hspecRec hrecb).1
  have hbh : (H.nodes[c+1]'hc1).σ.h = (H.nodes[c+1]'hc1).h := htrans.base.child_h
  have hthr : (H.nodes[c+1]'hc1).σ.wPrev ((H.nodes[c+1]'hc1).σ.Φ)
      < ((H.nodes[c+1]'hc1).σ.h : ℤ) := by
    rw [hwPrevΦb, hbh]
    exact_mod_cast hhlt
  -- (S6b) at the anchor stage, digit scalar = the terminal center's value
  have hcmem : cF ∈ (H.nodes[c+1]'hc1).σ.K := by
    rw [subfield_zmod_eq_top (H.nodes[c+1]'hc1).σ.K]; trivial
  have helne : (⟨cF, hcmem⟩ : ↥(H.nodes[c+1]'hc1).σ.K) ≠ 0 := by
    intro h
    exact hcFne (by simpa using congrArg Subtype.val h)
  obtain ⟨B0, hB0ne, hB0in, hB0wprev, hB0R⟩ :=
    (H.nodes[c+1]'hc1).σ.hS6b ((H.nodes[c+1]'hc1).σ.h : ℤ) (Units.mk0 _ helne) hthr
  have hbt : (H.nodes[c+1]'hc1).σ.t = 0 := (H.nodes[c+1]'hc1).σ.he1t hbe
  rw [hbt] at hB0R
  simp only [Units.val_mk0, neg_zero, zero_mul] at hB0R
  have hB0w : (H.nodes[c+1]'hc1).σ.w B0 = ((H.nodes[c+1]'hc1).σ.h : ℤ) := by
    have hstr := (H.nodes[c+1]'hc1).σ.hStretch B0 hB0ne hB0in
    rw [hbe] at hstr
    rw [hstr, hB0wprev]
    push_cast
    ring
  have hB0deg : B0.degree ≤ 0 :=
    degree_le_zero_of_inC_linear ((H.nodes[c+1]'hc1).σ.hmonic.ne_zero)
      (frame_deg_one hH (c+1) hc1) hB0in
  have hB0dig : ∀ zbar : (ZMod p)ˣ, (H.nodes[c+1]'hc1).σ.digPrime zbar B0 = cF := by
    intro zbar
    exact digPrime_of_R_C_T0 (H.nodes[c+1]'hc1).σ zbar B0 _ hB0R
  -- TRANSPORT (Lemma 3.2): up the recentering run from b = c+1 to i
  have main : ∀ r, c + 1 ≤ r → ∀ _ : r ≤ i,
      (H.nodes[r]'(by omega)).σ.e = 1 ∧
      ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ B.degree ≤ 0 ∧
        (H.nodes[r]'(by omega)).σ.w B = ((H.nodes[r]'(by omega)).σ.h : ℤ) ∧
        ∀ zbar : (ZMod p)ˣ, (H.nodes[r]'(by omega)).σ.digPrime zbar B = cF := by
    intro r hcr
    induction r, hcr using Nat.le_induction with
    | base =>
      intro _
      exact ⟨hbe, B0, hB0ne, hB0deg, hB0w, hB0dig⟩
    | succ r hcr ih =>
      intro hr1
      obtain ⟨hre, B, hBne, hBdeg, hBw, hBdig⟩ := ih (by omega)
      have hrlen : r + 1 < H.nodes.length := by omega
      have hrrec : (H.nodes[r]'(by omega)).species = ReadSpecies.recentering :=
        hcrun r (by omega) (by omega) (by omega)
      obtain ⟨hrecleg, -, -, -, -, -, -⟩ := hH.2.2.2 r hrlen
      obtain ⟨-, hre', hccne, hinCt, htne, hwt, hRt, hΦ', hw', hwPrev', hK, -, -, hdig⟩ :=
        (hrecleg hrrec).base
      have hΦrdeg := frame_deg_one hH r (by omega)
      have hsubne : (H.nodes[r]'(by omega)).σ.Φ - (H.nodes[r]'(by omega)).lift ≠ 0 := by
        rw [← hΦ']
        exact (H.nodes[r+1]'hrlen).σ.hmonic.ne_zero
      have hnojump := stage_w_key_sub_lift (H.nodes[r]'(by omega)).σ hre _ _
        hccne htne hwt hRt hsubne
      have hheq : ((H.nodes[r+1]'hrlen).σ.h : ℤ) = ((H.nodes[r]'(by omega)).σ.h : ℤ) := by
        rw [← (H.nodes[r+1]'hrlen).σ.hwΦ, hΦ', hw', hnojump,
          (H.nodes[r]'(by omega)).σ.hwΦ]
      refine ⟨hre', B, hBne, hBdeg, ?_, ?_⟩
      · rw [hw', hBw]
        exact hheq.symm
      · intro zbar
        have hin : inC (H.nodes[r]'(by omega)).σ.Φ B :=
          inC_of_degree_le_zero_linear ((H.nodes[r]'(by omega)).σ.hmonic.ne_zero)
            hΦrdeg hBdeg
        rw [hdig B hBne hin zbar]
        exact hBdig zbar
  -- FINAL ASSEMBLY at the terminal node
  obtain ⟨hie, B, hBne, hBdeg, hBw, hBdig⟩ := main i (by omega) le_rfl
  have hΦideg := frame_deg_one hH i hi
  have hin : inC (H.nodes[i]'hi).σ.Φ B :=
    inC_of_degree_le_zero_linear ((H.nodes[i]'hi).σ.hmonic.ne_zero) hΦideg hBdeg
  obtain ⟨c', hc'⟩ := (H.nodes[i]'hi).σ.hS5 B hBne hin
  have hit : (H.nodes[i]'hi).σ.t = 0 := (H.nodes[i]'hi).σ.he1t hie
  rw [hit] at hc'
  simp only [neg_zero, zero_mul] at hc'
  have hval : ((c' : ↥(H.nodes[i]'hi).σ.K) : ZMod p) = cF := by
    have h1 := hBdig 1
    rw [digPrime_of_R_C_T0 (H.nodes[i]'hi).σ 1 B _ hc'] at h1
    exact h1
  have hc'center : (c' : ↥(H.nodes[i]'hi).σ.K) = (H.nodes[i]'hi).center :=
    Subtype.coe_injective (hval.trans hcF)
  refine ⟨B, hBne, hBdeg, hin, ?_, ?_⟩
  · rw [hBw, (H.nodes[i]'hi).σ.hwΦ]
  · rw [hc', hc'center]

/-- **O-14a′ COROLLARY 4 — THE RunRealizerExists FILL**: over the prime ambient field,
at every recentering node of every coherent history a `CanRealizes` witness exists.
Interior nodes: the recorded lift (`interior_center_realizer_exists`); terminal node:
`terminal_center_realizer`; the support clause is free at linear frames (Thm 1(iii)).
This is THE one Prop `canPolicyC_pin` consumes — the (†15) pair discharges from it. -/
theorem runRealizerExists_zmod (p : ℕ) [Fact p.Prime] : RunRealizerExists p (ZMod p) := by
  intro H hH i hi hν
  have he1 : (H.nodes[i]'hi).e = 1 := ((H.nodes[i]'hi).hspecRec hν).1
  have hΦdeg : (H.nodes[i]'hi).σ.Φ.natDegree = 1 := frame_deg_one hH i hi
  by_cases hint : i + 1 < H.nodes.length
  · -- INTERIOR: the recorded lift is the realizer (coherence-supplied CR clauses)
    obtain ⟨t, htne, hin, hw, hR⟩ := interior_center_realizer_exists hH hint hν
    have hdeg : t.degree ≤ 0 :=
      degree_le_zero_of_inC_linear ((H.nodes[i]'hi).σ.hmonic.ne_zero) hΦdeg hin
    exact ⟨t, htne, canRealizes_support_of_constant _ he1 t hdeg,
      fun _ => ⟨hin, hw, hR⟩⟩
  · -- TERMINAL: Theorem 3
    have hlast : i + 1 = H.nodes.length := by omega
    obtain ⟨t, htne, hdeg, hin, hw, hR⟩ := terminal_center_realizer hH hi hlast hν
    exact ⟨t, htne, canRealizes_support_of_constant _ he1 t hdeg,
      fun _ => ⟨hin, hw, hR⟩⟩

end Terminal

end LeanUrat.MovesD

-- Footprint gate (Lean core only expected):
#print axioms LeanUrat.MovesD.runRealizerExists_zmod
#print axioms LeanUrat.MovesD.terminal_center_realizer
#print axioms LeanUrat.MovesD.frame_deg_one
