/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.HNode1

/-!
# SelfLoopTower — Phase-B wave W6-lite: the SELF-LOOP TOWER at `e = 1`

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md` W6 scope, lite instance: instantiate the
abstract β-side reader `R` of `h_node1_single`/`h_node1_selfLoop` (W4e) at `e = 1`, where the
child ring is the base ring again — the FIRST genuine two-level classification theorem.

**The math.** At `e = 1`, `h = 1` the restart key is LINEAR: `φ = X − C(c·p)`, so evaluation at
`c·p` is a ring isomorphism `Rphi p N 1 1 c ≃+* ZMod (p^N)` (`ringIso`; mathlib's
`Polynomial.quotientSpanXSubCAlgEquiv`).  Under it `vphi = v_p` (`vphi_iso`, `v_p` spelled as
`PadicLift.zmodValuation`), and the D0-verified `FreshClusterPattern` (floors `e(μ−j)+1`)
becomes the plain divisibility pattern `p^(μ−j+1) ∣ γ_j` on the transported digit tuple
(`pattern_iso`, `GammaPattern`).  The RECENTERED polynomial `g_γ = X^μ + Σ γ_j X^j` is a monic
size-`μ` box element with all low coefficients `≡ 0 mod p²` (`recenter_coeff_sq`) — in
particular in the CLUSTER BOX (`recenter_mem_clusterBox`), so the order-1 menu classifier
`classify1` applies to it: the SECOND-LEVEL READ.

**Deliverables.**
1. `ringIso` + `ringIso_mk`/`ringIso_theta` + `vphi_iso` + `pattern_iso`.
2. `recenter` (`f ↦ β ↦ γ ↦ g_γ`, the composition through `restartDigits'`) +
   `recenter_mem_clusterBox` (mod-`p` form; the sharper mod-`p²` fact is `recenter_coeff_sq`).
3. **`two_level_census`** (THE TOWER THEOREM): for every `c' : Option NodeConfig`,
   `#{f // InCellAt f ∧ classify1 (recenter f) = c'} = #{γ // GammaPattern γ ∧ classify1 g_γ = c'}`
   — `h_node1_single` at `R := classify1 ∘ (γ ↦ g_γ)` transported through `ringIso` (no new
   counting).  Interpretation: `second_level_partition` (sum over `cellMenu μ N` plus the `none`
   tail recovers the full cell fiber) and the honest three-way drainage law
   `read2_eq_none_iff` (the second-level read has its OWN tail: readable ⟺ `v_p(γ₀) < N` —
   W0's law one level down; at deep levels `γ₀ ≡ 0 mod p^N` is possible).
4. Numeric-gate theorems at `(p, μ) = (2, 2)`, `N ∈ {4, 5}` (gate:
   `/workspace-vast/asving/tmp/phaseb_w6lite/gate_w6lite.py`, PASS, incl. PARI factorpadic
   cross-check of every decided two-level prediction on 4 lifts each):
   censuses `8 = 4(A) + 4(tail)` and `32 = 16(A) + 4(B2) + 4(self-loop-again) + 8(tail)`.
5. Stretch (`gate_iterated_selfLoop`): the k = 2 self-loop mass at `(2,2,5)` —
   `#{two successive self-loop reads} · p^(2(w(μ)+1)) = #clusterBox` — the first two terms of
   the `countPivot` geometric series grounded.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints (checked with
`#print axioms`, prints removed after checking); no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopTower

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.RphiRing
open LeanUrat.OM.RestartEquiv
open LeanUrat.OM.CellMenu
open LeanUrat.OM.CellCard
open LeanUrat.OM.HNode1

variable (p N μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## 1. Deliverable 1: the ring isomorphism `Rphi p N 1 1 c ≃+* ZMod (p^N)` at `e = 1`

The key is linear (`φ = X − C(c·p)`), so the quotient is the base ring, by evaluation at
`c·p` — mathlib's `Polynomial.quotientSpanXSubCAlgEquiv` through the span identification. -/

section RingIso

/-- The recentering point: `c·p ∈ ZMod (p^N)` (the root of the linear key `φ`). -/
def cp : ZMod (p ^ N) := (c : ZMod (p ^ N)) * (p : ZMod (p ^ N))

omit hp in
/-- At `e = h = 1` the key polynomial is linear: `φ = X − C(c·p)`. -/
theorem phi_e1 : phi p N 1 1 c = X - C (cp p N c) := by
  rw [phi_eq, pow_one, pow_one]
  rfl

omit hp in
theorem span_phi_eq :
    Ideal.span {phi p N 1 1 c} = Ideal.span {X - C (cp p N c)} := by
  rw [phi_e1]

/-- **Deliverable 1 (the iso).** At `e = 1` the child ring is the base ring again:
`Rphi p N 1 1 c ≃+* ZMod (p^N)`, by evaluation at `c·p` (`quotientSpanXSubCAlgEquiv`
transported through `span_phi_eq`). -/
def ringIso : Rphi p N 1 1 c ≃+* ZMod (p ^ N) :=
  RingEquiv.trans (Ideal.quotEquivOfEq (span_phi_eq p N c))
    (Polynomial.quotientSpanXSubCAlgEquiv (cp p N c)).toRingEquiv

omit hp in
/-- The iso is evaluation at `c·p` on representatives. -/
theorem ringIso_mk (g : (ZMod (p ^ N))[X]) :
    ringIso p N c (AdjoinRoot.mk (phi p N 1 1 c) g) = g.eval (cp p N c) :=
  rfl

omit hp in
/-- The uniformizer avatar maps to `c·p`. -/
theorem ringIso_theta : ringIso p N c (theta p N 1 1 c) = cp p N c := by
  have h := ringIso_mk p N c X
  rwa [eval_X] at h

/-- Ideal-power membership transports to plain `p`-power divisibility (the unit `c` is
absorbed). -/
theorem mem_span_theta_pow_iff (m : ℕ) (x : Rphi p N 1 1 c) :
    x ∈ Ideal.span {theta p N 1 1 c} ^ m ↔ (p : ZMod (p ^ N)) ^ m ∣ ringIso p N c x := by
  rw [span_theta_pow_eq, Ideal.mem_span_singleton]
  constructor
  · intro h
    have h2 := map_dvd (ringIso p N c) h
    rw [map_pow, ringIso_theta] at h2
    obtain ⟨t, ht⟩ := h2
    refine ⟨(c : ZMod (p ^ N)) ^ m * t, ?_⟩
    rw [ht]
    unfold cp
    ring
  · intro h
    have h2 := map_dvd (ringIso p N c).symm h
    rw [map_pow, map_natCast, RingEquiv.symm_apply_apply] at h2
    have hθp : theta p N 1 1 c ∣ ((p : ℕ) : Rphi p N 1 1 c) := by
      refine ⟨(((cUnit p N 1 1 c)⁻¹ : (Rphi p N 1 1 c)ˣ) : Rphi p N 1 1 c), ?_⟩
      rw [natCast_p_eq p N 1 c, pow_one]
      ring
    exact dvd_trans (pow_dvd_pow_of_dvd hθp m) h2

/-- **Deliverable 1 (`vphi_iso`).** Under the iso, the θ-adic reader `vphi` IS the base-ring
valuation `PadicLift.zmodValuation` (the `CellMenu`/`PadicLift` spelling of `v_p`); the junk
values agree too (`vphi 0 = N·1 = N = zmodValuation 0`). -/
theorem vphi_iso (hN : 0 < N) (x : Rphi p N 1 1 c) :
    vphi p N 1 c x = PadicLift.zmodValuation p N (ringIso p N c x) := by
  have hle : vphi p N 1 c x ≤ N := by
    have h := vphi_le p N 1 c x
    omega
  have hzle : PadicLift.zmodValuation p N (ringIso p N c x) ≤ N := by
    by_cases hx : ringIso p N c x = 0
    · rw [hx, PadicLift.zmodValuation_zero]
    · exact (PadicLift.zmodValuation_lt p hN hx).le
  apply le_antisymm
  · have hmem : x ∈ Ideal.span {theta p N 1 1 c ^ vphi p N 1 c x} :=
      mem_span_theta_pow_vphi p N 1 c x
    rw [← span_theta_pow_eq] at hmem
    have hdvd := (mem_span_theta_pow_iff p N c _ x).mp hmem
    have hval := (pow_dvd_iff_dvd_val p N hle _).mp hdvd
    exact (pow_dvd_val_iff p hle _).mp hval
  · have hval : (p : ℕ) ^ PadicLift.zmodValuation p N (ringIso p N c x)
        ∣ (ringIso p N c x).val := (pow_dvd_val_iff p hzle _).mpr le_rfl
    have hdvd := (pow_dvd_iff_dvd_val p N hzle _).mpr hval
    have hmem := (mem_span_theta_pow_iff p N c _ x).mpr hdvd
    rw [span_theta_pow_eq] at hmem
    exact (le_vphi_iff p N 1 c (by omega : PadicLift.zmodValuation p N (ringIso p N c x) ≤ N * 1)).mpr hmem

/-- The transported fresh-cluster pattern: plain divisibility floors `p^(μ−j+1) ∣ γ_j`. -/
def GammaPattern (γ : Fin μ → ZMod (p ^ N)) : Prop :=
  ∀ j : Fin μ, (p : ZMod (p ^ N)) ^ (μ - j.1 + 1) ∣ γ j

/-- **Deliverable 1 (`pattern_iso`).** At `e = 1` the D0-verified `FreshClusterPattern`
(floors `e(μ−j)+1 = μ−j+1`) IS the divisibility pattern of the transported tuple. -/
theorem pattern_iso (β : Fin μ → Rphi p N 1 1 c) :
    FreshClusterPattern p N 1 μ c β
      ↔ GammaPattern p N μ (fun j => ringIso p N c (β j)) := by
  unfold FreshClusterPattern GammaPattern
  refine forall_congr' fun j => ?_
  rw [one_mul]
  exact mem_span_theta_pow_iff p N c _ (β j)

end RingIso

/-! ## 2. Deliverable 2: the recentering map into the size-`μ` monic box -/

section Recenter

/-- The recentered second-level box element `g_γ = X^μ + Σ_j γ_j X^j` (`CellCard.lowPoly`). -/
def gpoly (hN : 0 < N) (γ : Fin μ → ZMod (p ^ N)) : QuotientBox.monicBox p N μ :=
  ⟨CellCard.lowPoly p γ, (CellCard.lowPoly_monic p hN γ).1, (CellCard.lowPoly_monic p hN γ).2⟩

theorem gpoly_coeff_lt (hN : 0 < N) (γ : Fin μ → ZMod (p ^ N)) (k : ℕ) (hk : k < μ) :
    ((gpoly p N μ hN γ).1).coeff k = γ ⟨k, hk⟩ := by
  show (CellCard.lowPoly p γ).coeff k = γ ⟨k, hk⟩
  rw [CellCard.lowPoly_coeff, dif_pos hk]

theorem gpoly_coeff_self (hN : 0 < N) (γ : Fin μ → ZMod (p ^ N)) :
    ((gpoly p N μ hN γ).1).coeff μ = 1 := by
  show (CellCard.lowPoly p γ).coeff μ = 1
  rw [CellCard.lowPoly_coeff, dif_neg (lt_irrefl μ), if_pos rfl]

/-- The transported digit tuple of a box element: `γ_j = ringIso (restartDigits'_j f)`. -/
def gammaOf (hN : 0 < N) (f : QuotientBox.monicBox p N (μ * 1)) : Fin μ → ZMod (p ^ N) :=
  fun j => ringIso p N c (restartDigits' p N 1 μ c hN one_pos f j)

/-- **Deliverable 2 (unbundled).** The recentered second-level read input of `f`:
`f ↦ β ↦ γ ↦ g_γ`. -/
def recenter' (hN : 0 < N) (f : QuotientBox.monicBox p N (μ * 1)) :
    QuotientBox.monicBox p N μ :=
  gpoly p N μ hN (gammaOf p N μ c hN f)

/-- **Deliverable 2.** `recenter` on the self-loop cell fiber (`c_loop`: slope `−1`, residual
`(X − c̄)^μ`, `s = μ` — the `RestartEquiv` setting at `e = 1`). -/
def recenter (hN : 0 < N)
    (f : {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f}) :
    QuotientBox.monicBox p N μ :=
  recenter' p N μ c hN f.1

/-- The transported digits of a cell element satisfy the divisibility pattern. -/
theorem gammaOf_pattern (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    {f : QuotientBox.monicBox p N (μ * 1)} (hf : InCellAt p N 1 μ c f) :
    GammaPattern p N μ (gammaOf p N μ c hN f) :=
  (pattern_iso p N μ c _).mp
    ((inCellAt_iff_pattern p N 1 μ c hN one_pos hμ2 hμN f).mp hf)

/-- **The sharper fact**: every low coefficient of the recentered polynomial is `≡ 0 mod p²`
(slot `j` carries `p^(μ−j+1)` and `μ − j + 1 ≥ 2`). -/
theorem recenter_coeff_sq (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f})
    (i : ℕ) (hi : i < μ) :
    (p : ZMod (p ^ N)) ^ 2 ∣ ((recenter p N μ c hN f).1).coeff i := by
  have hpat := gammaOf_pattern p N μ c hN hμ2 hμN f.2 ⟨i, hi⟩
  have hco : ((recenter p N μ c hN f).1).coeff i = gammaOf p N μ c hN f.1 ⟨i, hi⟩ :=
    gpoly_coeff_lt p N μ hN _ i hi
  rw [hco]
  exact dvd_trans (pow_dvd_pow _ (by omega : 2 ≤ μ - i + 1)) hpat

/-- **Deliverable 2 (`recenter_mem_clusterBox`).** The recentered polynomial lands in the
size-`μ` CLUSTER BOX (all low coefficients `≡ 0 mod p`; indeed `mod p²` —
`recenter_coeff_sq`), so `classify1` applies to it: the second-level read is well-posed. -/
theorem recenter_mem_clusterBox (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f}) :
    CellCard.IsCluster p (recenter p N μ c hN f) := by
  intro i hi
  have hsq := recenter_coeff_sq p N μ c hN hμ2 hμN f i hi
  have h1 : (p : ZMod (p ^ N)) ^ 1 ∣ ((recenter p N μ c hN f).1).coeff i :=
    dvd_trans (pow_dvd_pow _ (by omega)) hsq
  have hval := (pow_dvd_iff_dvd_val p N hN _).mp h1
  show 1 ≤ vOf p (recenter p N μ c hN f) i
  rw [vOf_eq]
  exact (pow_dvd_val_iff p hN _).mp hval

/-- Unbundled form of `recenter_mem_clusterBox` (for the classifier lemmas). -/
theorem recenter'_isCluster (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    {f : QuotientBox.monicBox p N (μ * 1)} (hf : InCellAt p N 1 μ c f) :
    CellCard.IsCluster p (recenter' p N μ c hN f) :=
  recenter_mem_clusterBox p N μ c hN hμ2 hμN ⟨f, hf⟩

end Recenter

/-! ## 3. Deliverable 3: THE TOWER THEOREM `two_level_census` and its interpretation -/

section Tower

/-- The two-level equivalence: the `classify1∘recenter`-conditioned cell fiber is in bijection
with the correspondingly conditioned divisibility-pattern coset — `censusEquiv`
(= `h_node1_single`'s engine) at `Q := (classify1 ∘ gpoly ∘ transport) = c'`, composed with
the `ringIso` transport of the digit space. -/
def towerEquiv (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N) (c' : Option NodeConfig) :
    {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ classify1 p (recenter' p N μ c hN f) = c'}
      ≃ {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ classify1 p (gpoly p N μ hN γ) = c'} :=
  (censusEquiv p N 1 μ c hN one_pos hμ2 hμN
      (fun β => classify1 p (gpoly p N μ hN (fun j => ringIso p N c (β j))) = c')).trans
    ((Equiv.piCongrRight fun _ => (ringIso p N c).toEquiv).subtypeEquiv fun β =>
      and_congr (pattern_iso p N μ c β) Iff.rfl)

/-- **THE TOWER THEOREM (deliverable 3, `two_level_census`).** For every menu verdict
`c' : Option NodeConfig` of the size-`μ` second-level read:

    #{f // InCellAt f c_loop ∧ classify1 (recenter f) = c'}
      = #{γ // (∀ j, p^(μ−j+1) ∣ γ_j) ∧ classify1 (g_γ) = c'}.

This is `h_node1_single` with `R := classify1 ∘ (γ ↦ g_γ)` transported through `ringIso` —
the census of the second-level classification INSIDE the first-level cell equals the plain
divisibility-coset census.  No new counting. -/
theorem two_level_census (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N) (c' : Option NodeConfig) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ classify1 p (recenter' p N μ c hN f) = c'}
      = Nat.card {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ classify1 p (gpoly p N μ hN γ) = c'} :=
  Nat.card_congr (towerEquiv p N μ c hN hμ2 hμN c')

/-- The generic list-partition of a conditioned census by the fibers of an
`Option NodeConfig`-valued reader over a `Nodup` list, with honest remainder. -/
theorem card_partition_list {α : Type*} [Finite α] (r : α → Option NodeConfig) :
    ∀ L : List NodeConfig, L.Nodup → ∀ P : α → Prop,
      Nat.card {a : α // P a}
        = (L.map fun c' => Nat.card {a : α // P a ∧ r a = some c'}).sum
          + Nat.card {a : α // P a ∧ ∀ c' ∈ L, ¬ r a = some c'} := by
  intro L
  induction L with
  | nil =>
      intro _ P
      rw [List.map_nil, List.sum_nil, Nat.zero_add]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun a =>
        ⟨fun h => ⟨h, fun c' hc' => absurd hc' (List.not_mem_nil)⟩, fun h => h.1⟩)
  | cons c0 L ih =>
      intro hnd P
      obtain ⟨hc0, hndL⟩ := List.nodup_cons.mp hnd
      have hsplit := CellCard.card_subtype_and_compl (α := α) P (fun a => r a = some c0)
      have hIH := ih hndL (fun a => P a ∧ ¬ r a = some c0)
      have hterm : ∀ c' ∈ L,
          Nat.card {a : α // (P a ∧ ¬ r a = some c0) ∧ r a = some c'}
            = Nat.card {a : α // P a ∧ r a = some c'} := by
        intro c' hc'
        refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
        constructor
        · rintro ⟨⟨hP, _⟩, hr⟩
          exact ⟨hP, hr⟩
        · rintro ⟨hP, hr⟩
          refine ⟨⟨hP, ?_⟩, hr⟩
          rw [hr]
          intro hEq
          exact hc0 (by rwa [Option.some_inj.mp hEq] at hc')
      have hmap : (L.map fun c' =>
            Nat.card {a : α // (P a ∧ ¬ r a = some c0) ∧ r a = some c'})
          = L.map fun c' => Nat.card {a : α // P a ∧ r a = some c'} :=
        List.map_congr_left hterm
      have hrem : Nat.card {a : α // (P a ∧ ¬ r a = some c0) ∧ ∀ c' ∈ L, ¬ r a = some c'}
          = Nat.card {a : α // P a ∧ ∀ c' ∈ c0 :: L, ¬ r a = some c'} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
        constructor
        · rintro ⟨⟨hP, h0⟩, hall⟩
          refine ⟨hP, fun c' hc' => ?_⟩
          rcases List.mem_cons.mp hc' with rfl | hc''
          · exact h0
          · exact hall c' hc''
        · rintro ⟨hP, hall⟩
          exact ⟨⟨hP, hall c0 (List.mem_cons.mpr (Or.inl rfl))⟩,
            fun c' hc' => hall c' (List.mem_cons_of_mem _ hc')⟩
      rw [List.map_cons, List.sum_cons]
      rw [hmap, hrem] at hIH
      omega

/-- **Deliverable 3 (interpretation).** Summing the two-level census over the size-`μ` menu
plus the `none` remainder recovers the full cell-fiber count: the second-level read PARTITIONS
the self-loop cell.  The three-way reading: the menu terms split into DECIDED cells and the
SELF-LOOP-AGAIN cell (the repeated-residual shape one level down; see the `(2,2,5)` gate), and
the `none` term is the second level's OWN TAIL (`read2_eq_none_iff`). -/
theorem second_level_partition (hN : 0 < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) // InCellAt p N 1 μ c f}
      = ((cellMenu μ N).map fun c' =>
          Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
            InCellAt p N 1 μ c f ∧ classify1 p (recenter' p N μ c hN f) = some c'}).sum
        + Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
            InCellAt p N 1 μ c f ∧ classify1 p (recenter' p N μ c hN f) = none} := by
  refine (card_partition_list (fun f => classify1 p (recenter' p N μ c hN f)) (cellMenu μ N)
      (nodup_cellMenu μ N) (fun f => InCellAt p N 1 μ c f)).trans ?_
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => and_congr_right fun _ => ?_)
  constructor
  · intro hall
    rcases hopt : classify1 p (recenter' p N μ c hN f) with _ | c₀
    · rfl
    · exact absurd hopt (hall c₀ (classify1_spec p hopt).1)
  · intro hnone c₀ _ hEq
    rw [hnone] at hEq
    simp at hEq

/-- The tail of the size-`μ` second-level read at any `γ` with dead constant slot. -/
theorem classify_gpoly_none (hN : 0 < N) (hμ : 0 < μ) (γ : Fin μ → ZMod (p ^ N))
    (h0 : γ ⟨0, hμ⟩ = 0) : classify1 p (gpoly p N μ hN γ) = none := by
  apply classify1_eq_none_of_tail p hN
  rw [gpoly_coeff_lt p N μ hN γ 0 hμ, h0]

/-- **W0's law one level down (the honest drainage statement).** For a cell element, the
second-level read is a TAIL (`classify1 = none`) exactly when the transported constant digit
is unreadable at level `N`: `¬ v_p(γ₀) < N`, i.e. `γ₀ ≡ 0 mod p^N`.  So the three-way split
of `second_level_partition` is genuinely `decided cell / self-loop-again / tail` — the deep
levels drain through their own `γ₀`-tail, exactly as at the first level. -/
theorem read2_eq_none_iff (hN : 0 < N) (hμ2 : 2 ≤ μ) (hμN : μ < N)
    (f : QuotientBox.monicBox p N (μ * 1)) (hf : InCellAt p N 1 μ c f) :
    classify1 p (recenter' p N μ c hN f) = none
      ↔ ¬ PadicLift.zmodValuation p N (gammaOf p N μ c hN f ⟨0, by omega⟩) < N := by
  have hμ : 0 < μ := by omega
  by_cases h0 : gammaOf p N μ c hN f ⟨0, hμ⟩ = 0
  · constructor
    · intro _
      rw [h0, PadicLift.zmodValuation_zero]
      omega
    · intro _
      exact classify_gpoly_none p N μ hN hμ _ h0
  · have hread : PadicLift.zmodValuation p N (gammaOf p N μ c hN f ⟨0, hμ⟩) < N :=
      PadicLift.zmodValuation_lt p hN h0
    constructor
    · intro hnone
      exfalso
      have hco : ((recenter' p N μ c hN f).1).coeff 0 = gammaOf p N μ c hN f ⟨0, hμ⟩ :=
        gpoly_coeff_lt p N μ hN _ 0 hμ
      have hsome := classify1_isSome p hN hμ (recenter' p N μ c hN f)
        (recenter'_isCluster p N μ c hN hμ2 hμN hf) (by
          rw [vOf_eq, hco]; exact hread)
      rw [hnone] at hsome
      simp at hsome
    · intro hdead
      exact absurd hread hdead

end Tower

end

/-! ## 4. THE NUMERIC GATE (deliverable 4) — `(p, μ) = (2, 2)`, `N ∈ {4, 5}`

Engine values (`/workspace-vast/asving/tmp/phaseb_w6lite/gate_w6lite.py`, GATE PASS, incl. the
PARI `factorpadic` cross-check: all 24 decided boxes match their two-level `(deg, e, f)`
prediction on 4 integer lifts each; all undecided boxes vary across probe lifts):

    N = 4: fiber  8 = 4 (cell A: `(0,3)→(2,0)`, `y+1`)                + 4 (tail)
    N = 5: fiber 32 = 16 (cell A) + 4 (cell B2: `(0,4)→(2,0)`, `y²+y+1`)
                       + 4 (SELF-LOOP-AGAIN: `(0,4)→(2,0)`, `(y+1)²`) + 8 (tail)

The γ-side censuses are proved here from the per-class `classify1` evaluations; the f-side
versions follow through `two_level_census` (the gate numbers are the acceptance test). -/

section Gates

/-! ### Counting and valuation helpers -/

/-- Valuation + unit-residue data of a `p = 2` element from divisibility witnesses (the odd
part of a nonzero element of `ZMod (2^N)` has residue `1` — `F₂ˣ` is trivial). -/
theorem val_data2 {N v : ℕ} {x : ZMod (2 ^ N)}
    (h1 : 2 ^ v ∣ x.val) (h2 : ¬ 2 ^ (v + 1) ∣ x.val) :
    PadicLift.zmodValuation 2 N x = v ∧ PadicLift.zmodUnitResidue 2 N x = 1 := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hv := zmodValuation_eq_of 2 x hx h1 h2
  obtain ⟨u, hu⟩ := h1
  have hodd : u % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · exfalso
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h
      exact h2 ⟨t, by rw [hu, ht, pow_succ]; ring⟩
    · exact h
  refine ⟨hv, ?_⟩
  have hres := zmodUnitResidue_eq 2 hx hv hu
  rw [hres]
  calc ((u : ℕ) : ZMod 2) = ((u % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod u 2).symm
    _ = 1 := by rw [hodd, Nat.cast_one]

theorem forall_fin_two {M : Type*} (Q : Fin 2 → M → Prop) (γ : Fin 2 → M) :
    (∀ j : Fin 2, Q j (γ j)) ↔ Q 0 (γ 0) ∧ Q 1 (γ 1) :=
  ⟨fun h => ⟨h 0, h 1⟩, fun h j => by
    fin_cases j
    · exact h.1
    · exact h.2⟩

/-- The `μ = 2` divisibility pattern, in `val` form. -/
theorem gammaPattern2_iff {N : ℕ} (hN3 : 3 ≤ N) (γ : Fin 2 → ZMod (2 ^ N)) :
    GammaPattern 2 N 2 γ ↔ 2 ^ 3 ∣ (γ 0).val ∧ 2 ^ 2 ∣ (γ 1).val := by
  refine Iff.trans
    (forall_fin_two (fun j x => ((2 : ℕ) : ZMod (2 ^ N)) ^ (2 - j.1 + 1) ∣ x) γ) ?_
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨(pow_dvd_iff_dvd_val 2 N (by omega) _).mp h0,
      (pow_dvd_iff_dvd_val 2 N (by omega) _).mp h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨(pow_dvd_iff_dvd_val 2 N (by omega) _).mpr h0,
      (pow_dvd_iff_dvd_val 2 N (by omega) _).mpr h1⟩

theorem card_subtype_eq {M : Type*} (a : M) : Nat.card {x : M // x = a} = 1 := by
  haveI hs : Subsingleton {x : M // x = a} := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  haveI hn : Nonempty {x : M // x = a} := ⟨⟨a, rfl⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩

/-- Exact-valuation slot count: `#{x : ZMod(p^N) | v_p(x.val) = m} = p^(N−m) − p^(N−m−1)`. -/
theorem card_slot_exact (p : ℕ) [Fact p.Prime] {N m k : ℕ} (hm : m < N) (hk : k = m + 1) :
    Nat.card {x : ZMod (p ^ N) // p ^ m ∣ x.val ∧ ¬ p ^ k ∣ x.val}
      = p ^ (N - m) - p ^ (N - k) := by
  subst hk
  have hsplit := CellCard.card_subtype_and_compl (α := ZMod (p ^ N))
    (fun x => p ^ m ∣ x.val) (fun x => p ^ (m + 1) ∣ x.val)
  have h1 : Nat.card {x : ZMod (p ^ N) // p ^ m ∣ x.val ∧ p ^ (m + 1) ∣ x.val}
      = p ^ (N - (m + 1)) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
      ⟨fun h => h.2, fun h => ⟨dvd_trans (pow_dvd_pow p (by omega)) h, h⟩⟩))]
    exact CellCard.card_dvd_subtype p (by omega)
  rw [h1, CellCard.card_dvd_subtype p (by omega : m ≤ N)] at hsplit
  omega

/-- Two-slot product count for `Fin 2`-tuples with independent slot predicates. -/
theorem card_pair_slots {M : Type*} [Finite M] (Q0 Q1 : M → Prop) :
    Nat.card {γ : Fin 2 → M // Q0 (γ 0) ∧ Q1 (γ 1)}
      = Nat.card {x : M // Q0 x} * Nat.card {y : M // Q1 y} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun γ => (⟨γ.1 0, γ.2.1⟩, ⟨γ.1 1, γ.2.2⟩)
      invFun := fun x => ⟨![x.1.1, x.2.1], by simpa using x.1.2, by simpa using x.2.2⟩
      left_inv := fun γ => by
        refine Subtype.ext (funext fun j => ?_)
        fin_cases j <;> simp
      right_inv := fun x => by
        rcases x with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        refine Prod.ext ?_ ?_ <;> exact Subtype.ext (by simp) }

/-! ### The three occupied second-level cells and their menu witnesses -/

/-- Second-level cell A: `(0,3) → (2,0)` (slope `−3/2`), residual `y + 1` — DECIDED
(`e = 2, f = 1`: ramified quadratic; PARI-confirmed on all its gate boxes). -/
def cellA : NodeConfig := mkCell 2 [(0, 3), (2, 0)] [[(1, 1)]]

/-- Second-level cell B2: `(0,4) → (2,0)` (slope `−2`), residual `y² + y + 1` — DECIDED
(`e = 1, f = 2`: unramified quadratic; PARI-confirmed). -/
def cellB2 : NodeConfig := mkCell 2 [(0, 4), (2, 0)] [[(2, 1)]]

/-- Second-level cell B1: `(0,4) → (2,0)` (slope `−2`), residual `(y + 1)²` — the
SELF-LOOP-AGAIN cell (repeated residual factor one level down; genuinely undecided at
level `N = 5`: the PARI probe lifts vary). -/
def cellB1 : NodeConfig := mkCell 2 [(0, 4), (2, 0)] [[(1, 2)]]

theorem menuPath_A {N : ℕ} (hN4 : 4 ≤ N) : MenuPath 2 N [(0, 3), (2, 0)] :=
  ⟨3, (2, 0), [], rfl, by norm_num, by omega, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem menuPath_B {N : ℕ} (hN5 : 5 ≤ N) : MenuPath 2 N [(0, 4), (2, 0)] :=
  ⟨4, (2, 0), [], rfl, by norm_num, by omega, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem shapes_A : ShapesFor [(0, 3), (2, 0)] [[(1, 1)]] := by
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_B2 : ShapesFor [(0, 4), (2, 0)] [[(2, 1)]] := by
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_B1 : ShapesFor [(0, 4), (2, 0)] [[(1, 2)]] := by
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem cellA_ne_B2 : cellA ≠ cellB2 := fun h =>
  absurd (mkCell_injective (menuPath_A (by norm_num : 4 ≤ 5)) (menuPath_B (by norm_num))
    shapes_A shapes_B2 h).1 (by decide)

theorem cellA_ne_B1 : cellA ≠ cellB1 := fun h =>
  absurd (mkCell_injective (menuPath_A (by norm_num : 4 ≤ 5)) (menuPath_B (by norm_num))
    shapes_A shapes_B1 h).1 (by decide)

theorem cellB2_ne_B1 : cellB2 ≠ cellB1 := fun h =>
  absurd (mkCell_injective (menuPath_B (by norm_num : 5 ≤ 5)) (menuPath_B (by norm_num))
    shapes_B2 shapes_B1 h).2 (by decide)

/-! ### The per-class second-level `classify1` evaluations -/

/-- Class A (`v(γ₀) = 3`, `v(γ₁) ≥ 2`, any `N ≥ 4`): the read is cell A. -/
theorem classify_gA {N : ℕ} (hN4 : 4 ≤ N) (γ : Fin 2 → ZMod (2 ^ N))
    (h0a : 2 ^ 3 ∣ (γ 0).val) (h0b : ¬ 2 ^ 4 ∣ (γ 0).val) (h1 : 2 ^ 2 ∣ (γ 1).val) :
    classify1 2 (gpoly 2 N 2 (by omega) γ) = some cellA := by
  have hN0 : (0 : ℕ) < N := by omega
  set g := gpoly 2 N 2 hN0 γ with hgdef
  have hd0 := val_data2 h0a h0b
  have hc0 : (g.1).coeff 0 = γ 0 := gpoly_coeff_lt 2 N 2 hN0 γ 0 (by norm_num)
  have hc1 : (g.1).coeff 1 = γ 1 := gpoly_coeff_lt 2 N 2 hN0 γ 1 (by norm_num)
  have hc2 : (g.1).coeff 2 = 1 := gpoly_coeff_self 2 N 2 hN0 γ
  have hv0 : vOf 2 g 0 = 3 := by rw [vOf_eq, hc0]; exact hd0.1
  have hv1 : 2 ≤ vOf 2 g 1 := by
    rw [vOf_eq, hc1]
    exact (pow_dvd_val_iff 2 (by omega) _).mp h1
  have hv2 : vOf 2 g 2 = 0 := vOf_leading 2 hN0 g
  have hsd := side_data (pr := ((0, 3), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 3), (2, 0))).e = 2 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 3), (2, 0))).h = -3 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 3), (2, 0))) = 1 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 N ((g.1).coeff 0) : ℤ)
      = ((mkSide ((0, 3), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 3), (2, 0))).h := by
    rw [hc0, hd0.1]
    simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 N ((g.1).coeff 2) : ℤ)
      = ((mkSide ((0, 3), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 3), (2, 0))).h := by
    have hval2 : PadicLift.zmodValuation 2 N ((g.1).coeff 2) = 0 := by
      have h := hv2
      rwa [vOf_eq] at h
    rw [hval2, hH]
    norm_num [mkSide]
  have hb0 : B.boxCoeffData 2 N (mkSide ((0, 3), (2, 0))) g 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0]
    exact hd0.2
  have hb1 : B.boxCoeffData 2 N (mkSide ((0, 3), (2, 0))) g 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 2) (by rw [hE]; decide) hg1, hc2]
    exact unitResidue_one 2 hN0
  have hR : residualOf 2 g ((0, 3), (2, 0)) = X + 1 := by
    rw [residual_deg_one 2 g _ hD, hb0, hb1, map_one, one_mul]
    ring
  have hexact : ∀ q ∈ ([(0, 3), (2, 0)] : List (ℕ × ℕ)), vOf 2 g q.1 = q.2 := by
    intro q hq
    fin_cases hq
    · exact hv0
    · exact hv2
  have habove : SideAbove 2 g ((0, 3), (2, 0)) := by
    intro i hi0 hi2
    have hi2' : i ≤ 2 := hi2
    interval_cases i
    · rw [hv0]
      norm_num [lineAt, slopeQ]
    · refine le_trans ?_ (by exact_mod_cast hv1 : (2 : ℚ) ≤ (vOf 2 g 1 : ℚ))
      norm_num [lineAt, slopeQ]
    · rw [hv2]
      norm_num [lineAt, slopeQ]
  have hmatch : Matches 2 g [(0, 3), (2, 0)] [[(1, 1)]] := by
    refine ⟨hexact, ?_⟩
    refine List.Forall₂.cons ⟨habove, ?_⟩ List.Forall₂.nil
    rw [hR, polyShape_X_add_one 2]
    simp
  exact (classify1_eq_some_iff 2).mpr
    ⟨[(0, 3), (2, 0)], [[(1, 1)]], menuPath_A hN4, shapes_A, rfl, hmatch⟩

/-- Constant-slot valuation/residue data shared by the two deep-cell reads at `N = 5`. -/
private theorem hv16 : PadicLift.zmodValuation 2 5 (16 : ZMod (2 ^ 5)) = 4 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

private theorem hu16 : PadicLift.zmodUnitResidue 2 5 (16 : ZMod (2 ^ 5)) = 1 := by
  simpa using zmodUnitResidue_eq 2 (x := (16 : ZMod (2 ^ 5))) (u := 1) (by decide) hv16 (by decide)

private theorem hone5 : PadicLift.zmodValuation 2 5 (1 : ZMod (2 ^ 5)) = 0 :=
  zmodValuation_eq_of 2 _ (by decide) (by decide) (by decide)

/-- Class B2 (`γ₀ = 16`, `v(γ₁) = 2` at `N = 5`): the read is cell B2 (irreducible residual). -/
theorem classify_gB2 (γ : Fin 2 → ZMod (2 ^ 5)) (h0 : γ 0 = 16)
    (h1a : 2 ^ 2 ∣ (γ 1).val) (h1b : ¬ 2 ^ 3 ∣ (γ 1).val) :
    classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB2 := by
  have hN0 : (0 : ℕ) < 5 := by norm_num
  set g := gpoly 2 5 2 hN0 γ with hgdef
  have hd1 := val_data2 h1a h1b
  have hc0 : (g.1).coeff 0 = 16 := by
    rw [gpoly_coeff_lt 2 5 2 hN0 γ 0 (by norm_num)]
    exact h0
  have hc1 : (g.1).coeff 1 = γ 1 := gpoly_coeff_lt 2 5 2 hN0 γ 1 (by norm_num)
  have hc2 : (g.1).coeff 2 = 1 := gpoly_coeff_self 2 5 2 hN0 γ
  have hv0 : vOf 2 g 0 = 4 := by rw [vOf_eq, hc0]; exact hv16
  have hv1 : vOf 2 g 1 = 2 := by rw [vOf_eq, hc1]; exact hd1.1
  have hv2 : vOf 2 g 2 = 0 := vOf_leading 2 hN0 g
  have hsd := side_data (pr := ((0, 4), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 4), (2, 0))).e = 1 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 4), (2, 0))).h = -2 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 4), (2, 0))) = 2 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 5 ((g.1).coeff 0) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc0, hv16]
    simp [mkSide]
  have hg1 : (PadicLift.zmodValuation 2 5 ((g.1).coeff 1) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc1, hd1.1, hH]
    norm_num [mkSide]
  have hg2 : (PadicLift.zmodValuation 2 5 ((g.1).coeff 2) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (2 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc2, hone5, hH]
    norm_num [mkSide]
  have hb0 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0]
    exact hu16
  have hb1 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 1 = 1 := by
    rw [bcd_eval 2 (t := 1) (j := 1) (by rw [hE]; decide) hg1, hc1]
    exact hd1.2
  have hb2 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 2 = 1 := by
    rw [bcd_eval 2 (t := 2) (j := 2) (by rw [hE]; decide) hg2, hc2]
    exact unitResidue_one 2 hN0
  have hR : residualOf 2 g ((0, 4), (2, 0)) = X ^ 2 + X + 1 := by
    rw [residual_deg_two 2 g _ hD, hb0, hb1, hb2, map_one, one_mul, one_mul]
    ring
  have hRdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Finset.mem_Icc, hRdeg]
      omega
    · intro x
      fin_cases x <;>
        simp only [Polynomial.IsRoot.def, eval_add, eval_pow, eval_X, eval_one] <;> decide
  have hexact : ∀ q ∈ ([(0, 4), (2, 0)] : List (ℕ × ℕ)), vOf 2 g q.1 = q.2 := by
    intro q hq
    fin_cases hq
    · exact hv0
    · exact hv2
  have habove : SideAbove 2 g ((0, 4), (2, 0)) := by
    intro i hi0 hi2
    have hi2' : i ≤ 2 := hi2
    interval_cases i
    · rw [hv0]
      norm_num [lineAt, slopeQ]
    · rw [hv1]
      norm_num [lineAt, slopeQ]
    · rw [hv2]
      norm_num [lineAt, slopeQ]
  have hmatch : Matches 2 g [(0, 4), (2, 0)] [[(2, 1)]] := by
    refine ⟨hexact, ?_⟩
    refine List.Forall₂.cons ⟨habove, ?_⟩ List.Forall₂.nil
    rw [hR, polyShape_irreducible_monic 2 hirr (by monicity!), hRdeg]
    simp
  exact (classify1_eq_some_iff 2).mpr
    ⟨[(0, 4), (2, 0)], [[(2, 1)]], menuPath_B (by norm_num), shapes_B2, rfl, hmatch⟩

/-- Class B1 (`γ₀ = 16`, `v(γ₁) ≥ 3` at `N = 5`): the read is the SELF-LOOP-AGAIN cell. -/
theorem classify_gB1 (γ : Fin 2 → ZMod (2 ^ 5)) (h0 : γ 0 = 16)
    (h1 : 2 ^ 3 ∣ (γ 1).val) :
    classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB1 := by
  have hN0 : (0 : ℕ) < 5 := by norm_num
  set g := gpoly 2 5 2 hN0 γ with hgdef
  have hc0 : (g.1).coeff 0 = 16 := by
    rw [gpoly_coeff_lt 2 5 2 hN0 γ 0 (by norm_num)]
    exact h0
  have hc1 : (g.1).coeff 1 = γ 1 := gpoly_coeff_lt 2 5 2 hN0 γ 1 (by norm_num)
  have hc2 : (g.1).coeff 2 = 1 := gpoly_coeff_self 2 5 2 hN0 γ
  have hv0 : vOf 2 g 0 = 4 := by rw [vOf_eq, hc0]; exact hv16
  have hv1 : 3 ≤ vOf 2 g 1 := by
    rw [vOf_eq, hc1]
    exact (pow_dvd_val_iff 2 (by norm_num) _).mp h1
  have hv2 : vOf 2 g 2 = 0 := vOf_leading 2 hN0 g
  have hsd := side_data (pr := ((0, 4), (2, 0))) (by decide) (by decide)
  have hE : (mkSide ((0, 4), (2, 0))).e = 1 := by rw [hsd.1]; decide
  have hH : (mkSide ((0, 4), (2, 0))).h = -2 := by rw [hsd.2.1]; decide
  have hD : M4.residualDeg (mkSide ((0, 4), (2, 0))) = 2 := by rw [hsd.2.2.1]; decide
  have hg0 : (PadicLift.zmodValuation 2 5 ((g.1).coeff 0) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (0 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc0, hv16]
    simp [mkSide]
  have hg1 : ¬ (PadicLift.zmodValuation 2 5 ((g.1).coeff 1) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (1 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc1, hH]
    intro hEq
    have hv1' : 3 ≤ PadicLift.zmodValuation 2 5 (γ 1) :=
      (pow_dvd_val_iff 2 (by norm_num) _).mp h1
    have h2 : (PadicLift.zmodValuation 2 5 (γ 1) : ℤ) = 2 := by
      rw [hEq]; norm_num [mkSide]
    omega
  have hg2 : (PadicLift.zmodValuation 2 5 ((g.1).coeff 2) : ℤ)
      = ((mkSide ((0, 4), (2, 0))).v₀ : ℤ) + (2 : ℕ) * (mkSide ((0, 4), (2, 0))).h := by
    rw [hc2, hone5, hH]
    norm_num [mkSide]
  have hb0 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 0 = 1 := by
    rw [bcd_eval 2 (t := 0) (j := 0) (by simp [mkSide]) hg0, hc0]
    exact hu16
  have hb1 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 1 = 0 :=
    bcd_zero 2 (t := 1) (j := 1) (by rw [hE]; decide) hg1
  have hb2 : B.boxCoeffData 2 5 (mkSide ((0, 4), (2, 0))) g 2 = 1 := by
    rw [bcd_eval 2 (t := 2) (j := 2) (by rw [hE]; decide) hg2, hc2]
    exact unitResidue_one 2 hN0
  have hR : residualOf 2 g ((0, 4), (2, 0)) = (X + 1) ^ 2 := by
    rw [residual_deg_two 2 g _ hD, hb0, hb1, hb2, map_one, map_zero, one_mul, zero_mul]
    have h2 : (2 : (ZMod 2)[X]) = 0 := by
      have hcast : (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (map_ofNat C 2).symm
      rw [hcast, show (2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination (-(X : (ZMod 2)[X])) * h2
  have hexact : ∀ q ∈ ([(0, 4), (2, 0)] : List (ℕ × ℕ)), vOf 2 g q.1 = q.2 := by
    intro q hq
    fin_cases hq
    · exact hv0
    · exact hv2
  have habove : SideAbove 2 g ((0, 4), (2, 0)) := by
    intro i hi0 hi2
    have hi2' : i ≤ 2 := hi2
    interval_cases i
    · rw [hv0]
      norm_num [lineAt, slopeQ]
    · refine le_trans ?_ (by exact_mod_cast hv1 : (3 : ℚ) ≤ (vOf 2 g 1 : ℚ))
      norm_num [lineAt, slopeQ]
    · rw [hv2]
      norm_num [lineAt, slopeQ]
  have hmatch : Matches 2 g [(0, 4), (2, 0)] [[(1, 2)]] := by
    refine ⟨hexact, ?_⟩
    refine List.Forall₂.cons ⟨habove, ?_⟩ List.Forall₂.nil
    rw [hR, polyShape_X_add_one_sq 2]
    simp
  exact (classify1_eq_some_iff 2).mpr
    ⟨[(0, 4), (2, 0)], [[(1, 2)]], menuPath_B (by norm_num), shapes_B1, rfl, hmatch⟩

/-! ### The γ-side census characterizations (per class, both `N`) -/

/-- `N = 4`: the A-census predicate is exactly `v(γ₀) = 3 ∧ v(γ₁) ≥ 2`. -/
theorem censusIff_A_N4 (γ : Fin 2 → ZMod (2 ^ 4)) :
    (GammaPattern 2 4 2 γ ∧ classify1 2 (gpoly 2 4 2 (by norm_num) γ) = some cellA)
      ↔ (2 ^ 3 ∣ (γ 0).val ∧ ¬ 2 ^ 4 ∣ (γ 0).val) ∧ 2 ^ 2 ∣ (γ 1).val := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    refine ⟨⟨hp0, fun h16 => ?_⟩, hp1⟩
    have hlt : (γ 0).val < 16 := by simpa using ZMod.val_lt (γ 0)
    obtain ⟨t, ht⟩ := h16
    have h00 : (γ 0).val = 0 := by omega
    have hz : γ 0 = 0 := (ZMod.val_eq_zero _).mp h00
    rw [classify_gpoly_none 2 4 2 (by norm_num) (by norm_num) γ hz] at hcl
    simp at hcl
  · rintro ⟨⟨h0a, h0b⟩, h1⟩
    exact ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨h0a, h1⟩,
      classify_gA (by norm_num) γ h0a h0b h1⟩

/-- `N = 4`: the tail predicate is exactly `γ₀ = 0 ∧ v(γ₁) ≥ 2`. -/
theorem censusIff_none_N4 (γ : Fin 2 → ZMod (2 ^ 4)) :
    (GammaPattern 2 4 2 γ ∧ classify1 2 (gpoly 2 4 2 (by norm_num) γ) = none)
      ↔ γ 0 = 0 ∧ 2 ^ 2 ∣ (γ 1).val := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    refine ⟨?_, hp1⟩
    by_contra hne
    have hvne : (γ 0).val ≠ 0 := fun h => hne ((ZMod.val_eq_zero _).mp h)
    have hlt : (γ 0).val < 16 := by simpa using ZMod.val_lt (γ 0)
    obtain ⟨t, ht⟩ := id hp0
    have hval8 : (γ 0).val = 8 := by omega
    have h0b : ¬ 2 ^ 4 ∣ (γ 0).val := by
      rw [hval8]
      decide
    rw [classify_gA (by norm_num) γ hp0 h0b hp1] at hcl
    simp at hcl
  · rintro ⟨h0, h1⟩
    refine ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨?_, h1⟩,
      classify_gpoly_none 2 4 2 (by norm_num) (by norm_num) γ h0⟩
    rw [h0]
    simp

/-- `N = 5`: the A-census predicate is exactly `v(γ₀) = 3 ∧ v(γ₁) ≥ 2`. -/
theorem censusIff_A_N5 (γ : Fin 2 → ZMod (2 ^ 5)) :
    (GammaPattern 2 5 2 γ ∧ classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellA)
      ↔ (2 ^ 3 ∣ (γ 0).val ∧ ¬ 2 ^ 4 ∣ (γ 0).val) ∧ 2 ^ 2 ∣ (γ 1).val := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    refine ⟨⟨hp0, fun h16 => ?_⟩, hp1⟩
    have hlt : (γ 0).val < 32 := by simpa using ZMod.val_lt (γ 0)
    obtain ⟨t, ht⟩ := h16
    have hval : (γ 0).val = 0 ∨ (γ 0).val = 16 := by omega
    rcases hval with h00 | h00
    · have hz : γ 0 = 0 := (ZMod.val_eq_zero _).mp h00
      rw [classify_gpoly_none 2 5 2 (by norm_num) (by norm_num) γ hz] at hcl
      simp at hcl
    · have h16v : γ 0 = 16 := by apply ZMod.val_injective; rw [h00]; decide
      by_cases h8 : 2 ^ 3 ∣ (γ 1).val
      · rw [classify_gB1 γ h16v h8] at hcl
        exact cellA_ne_B1 (Option.some_injective _ hcl).symm
      · rw [classify_gB2 γ h16v hp1 h8] at hcl
        exact cellA_ne_B2 (Option.some_injective _ hcl).symm
  · rintro ⟨⟨h0a, h0b⟩, h1⟩
    exact ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨h0a, h1⟩,
      classify_gA (by norm_num) γ h0a h0b h1⟩

/-- `N = 5`: the shared `γ₀ = 16` extraction for the two deep cells. -/
theorem gamma0_16_of_deep (γ : Fin 2 → ZMod (2 ^ 5)) (hp0 : 2 ^ 3 ∣ (γ 0).val)
    (hp1 : 2 ^ 2 ∣ (γ 1).val) {c₀ : NodeConfig}
    (hcl : classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some c₀)
    (hne : c₀ ≠ cellA) : γ 0 = 16 := by
  by_cases h16 : 2 ^ 4 ∣ (γ 0).val
  · have hlt : (γ 0).val < 32 := by simpa using ZMod.val_lt (γ 0)
    obtain ⟨t, ht⟩ := h16
    have hval : (γ 0).val = 0 ∨ (γ 0).val = 16 := by omega
    rcases hval with h00 | h00
    · exfalso
      have hz : γ 0 = 0 := (ZMod.val_eq_zero _).mp h00
      rw [classify_gpoly_none 2 5 2 (by norm_num) (by norm_num) γ hz] at hcl
      simp at hcl
    · apply ZMod.val_injective; rw [h00]; decide
  · exfalso
    rw [classify_gA (by norm_num) γ hp0 h16 hp1] at hcl
    exact hne (Option.some_injective _ hcl).symm

/-- `N = 5`: the B2-census predicate is exactly `γ₀ = 16 ∧ v(γ₁) = 2`. -/
theorem censusIff_B2_N5 (γ : Fin 2 → ZMod (2 ^ 5)) :
    (GammaPattern 2 5 2 γ ∧ classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB2)
      ↔ γ 0 = 16 ∧ (2 ^ 2 ∣ (γ 1).val ∧ ¬ 2 ^ 3 ∣ (γ 1).val) := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    have h16v : γ 0 = 16 :=
      gamma0_16_of_deep γ hp0 hp1 hcl (fun h => cellA_ne_B2 h.symm)
    refine ⟨h16v, hp1, fun h8 => ?_⟩
    rw [classify_gB1 γ h16v h8] at hcl
    exact cellB2_ne_B1 (Option.some_injective _ hcl).symm
  · rintro ⟨h0, h1a, h1b⟩
    have hp0 : 2 ^ 3 ∣ (γ 0).val := by
      rw [h0]
      decide
    exact ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨hp0, h1a⟩,
      classify_gB2 γ h0 h1a h1b⟩

/-- `N = 5`: the SELF-LOOP-AGAIN census predicate is exactly `γ₀ = 16 ∧ v(γ₁) ≥ 3`. -/
theorem censusIff_B1_N5 (γ : Fin 2 → ZMod (2 ^ 5)) :
    (GammaPattern 2 5 2 γ ∧ classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB1)
      ↔ γ 0 = 16 ∧ 2 ^ 3 ∣ (γ 1).val := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    have h16v : γ 0 = 16 :=
      gamma0_16_of_deep γ hp0 hp1 hcl (fun h => cellA_ne_B1 h.symm)
    refine ⟨h16v, ?_⟩
    by_contra h8
    rw [classify_gB2 γ h16v hp1 h8] at hcl
    exact cellB2_ne_B1 (Option.some_injective _ hcl)
  · rintro ⟨h0, h1⟩
    have hp0 : 2 ^ 3 ∣ (γ 0).val := by
      rw [h0]
      decide
    have hp1 : 2 ^ 2 ∣ (γ 1).val := dvd_trans (by norm_num) h1
    exact ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨hp0, hp1⟩,
      classify_gB1 γ h0 h1⟩

/-- `N = 5`: the tail predicate is exactly `γ₀ = 0 ∧ v(γ₁) ≥ 2`. -/
theorem censusIff_none_N5 (γ : Fin 2 → ZMod (2 ^ 5)) :
    (GammaPattern 2 5 2 γ ∧ classify1 2 (gpoly 2 5 2 (by norm_num) γ) = none)
      ↔ γ 0 = 0 ∧ 2 ^ 2 ∣ (γ 1).val := by
  constructor
  · rintro ⟨hpat, hcl⟩
    obtain ⟨hp0, hp1⟩ := (gammaPattern2_iff (by norm_num) γ).mp hpat
    refine ⟨?_, hp1⟩
    by_contra hne
    have hvne : (γ 0).val ≠ 0 := fun h => hne ((ZMod.val_eq_zero _).mp h)
    by_cases h16 : 2 ^ 4 ∣ (γ 0).val
    · have hlt : (γ 0).val < 32 := by simpa using ZMod.val_lt (γ 0)
      obtain ⟨t, ht⟩ := h16
      have h00 : (γ 0).val = 16 := by omega
      have h16v : γ 0 = 16 := by apply ZMod.val_injective; rw [h00]; decide
      by_cases h8 : 2 ^ 3 ∣ (γ 1).val
      · rw [classify_gB1 γ h16v h8] at hcl
        simp at hcl
      · rw [classify_gB2 γ h16v hp1 h8] at hcl
        simp at hcl
    · rw [classify_gA (by norm_num) γ hp0 h16 hp1] at hcl
      simp at hcl
  · rintro ⟨h0, h1⟩
    refine ⟨(gammaPattern2_iff (by norm_num) γ).mpr ⟨?_, h1⟩,
      classify_gpoly_none 2 5 2 (by norm_num) (by norm_num) γ h0⟩
    rw [h0]
    simp

/-! ### The γ-side census cards (the gate table, proved) -/

/-- Gate `N = 4`: `#A = 4`. -/
theorem census_A_N4 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 4) // GammaPattern 2 4 2 γ ∧
        classify1 2 (gpoly 2 4 2 (by norm_num) γ) = some cellA} = 4 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_A_N4)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 4) => 2 ^ 3 ∣ x.val ∧ ¬ 2 ^ 4 ∣ x.val)
      (fun x : ZMod (2 ^ 4) => 2 ^ 2 ∣ x.val)).trans ?_))
  rw [card_slot_exact 2 (by norm_num) (by norm_num : (4 : ℕ) = 3 + 1),
    CellCard.card_dvd_subtype 2 (by norm_num : (2 : ℕ) ≤ 4)]
  norm_num

/-- Gate `N = 4`: `#tail = 4`. -/
theorem census_none_N4 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 4) // GammaPattern 2 4 2 γ ∧
        classify1 2 (gpoly 2 4 2 (by norm_num) γ) = none} = 4 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_none_N4)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 4) => x = 0)
      (fun x : ZMod (2 ^ 4) => 2 ^ 2 ∣ x.val)).trans ?_))
  rw [card_subtype_eq (0 : ZMod (2 ^ 4)),
    CellCard.card_dvd_subtype 2 (by norm_num : (2 : ℕ) ≤ 4)]
  norm_num

/-- Gate `N = 5`: `#A = 16`. -/
theorem census_A_N5 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 5) // GammaPattern 2 5 2 γ ∧
        classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellA} = 16 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_A_N5)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 5) => 2 ^ 3 ∣ x.val ∧ ¬ 2 ^ 4 ∣ x.val)
      (fun x : ZMod (2 ^ 5) => 2 ^ 2 ∣ x.val)).trans ?_))
  rw [card_slot_exact 2 (by norm_num) (by norm_num : (4 : ℕ) = 3 + 1),
    CellCard.card_dvd_subtype 2 (by norm_num : (2 : ℕ) ≤ 5)]
  norm_num

/-- Gate `N = 5`: `#B2 = 4`. -/
theorem census_B2_N5 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 5) // GammaPattern 2 5 2 γ ∧
        classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB2} = 4 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_B2_N5)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 5) => x = 16)
      (fun x : ZMod (2 ^ 5) => 2 ^ 2 ∣ x.val ∧ ¬ 2 ^ 3 ∣ x.val)).trans ?_))
  rw [card_subtype_eq (16 : ZMod (2 ^ 5)),
    card_slot_exact 2 (by norm_num) (by norm_num : (3 : ℕ) = 2 + 1)]
  norm_num

/-- Gate `N = 5`: `#self-loop-again = 4`. -/
theorem census_B1_N5 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 5) // GammaPattern 2 5 2 γ ∧
        classify1 2 (gpoly 2 5 2 (by norm_num) γ) = some cellB1} = 4 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_B1_N5)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 5) => x = 16)
      (fun x : ZMod (2 ^ 5) => 2 ^ 3 ∣ x.val)).trans ?_))
  rw [card_subtype_eq (16 : ZMod (2 ^ 5)),
    CellCard.card_dvd_subtype 2 (by norm_num : (3 : ℕ) ≤ 5)]
  norm_num

/-- Gate `N = 5`: `#tail = 8`. -/
theorem census_none_N5 :
    Nat.card {γ : Fin 2 → ZMod (2 ^ 5) // GammaPattern 2 5 2 γ ∧
        classify1 2 (gpoly 2 5 2 (by norm_num) γ) = none} = 8 := by
  refine ((Nat.card_congr (Equiv.subtypeEquivRight censusIff_none_N5)).trans
    ((card_pair_slots (fun x : ZMod (2 ^ 5) => x = 0)
      (fun x : ZMod (2 ^ 5) => 2 ^ 2 ∣ x.val)).trans ?_))
  rw [card_subtype_eq (0 : ZMod (2 ^ 5)),
    CellCard.card_dvd_subtype 2 (by norm_num : (2 : ℕ) ≤ 5)]
  norm_num

/-! ### The f-side censuses through the tower theorem (the acceptance test) -/

/-- Gate `N = 4`, f-side: 4 of the 8 self-loop-cell elements read cell A at the second level. -/
theorem gate_fiber_A_N4 :
    Nat.card {f : QuotientBox.monicBox 2 4 (2 * 1) //
        InCellAt 2 4 1 2 1 f ∧
          classify1 2 (recenter' 2 4 2 1 (by norm_num) f) = some cellA} = 4 :=
  (two_level_census 2 4 2 1 (by norm_num) (by norm_num) (by norm_num) (some cellA)).trans
    census_A_N4

/-- Gate `N = 4`, f-side: 4 of the 8 drain into the second-level tail. -/
theorem gate_fiber_none_N4 :
    Nat.card {f : QuotientBox.monicBox 2 4 (2 * 1) //
        InCellAt 2 4 1 2 1 f ∧
          classify1 2 (recenter' 2 4 2 1 (by norm_num) f) = none} = 4 :=
  (two_level_census 2 4 2 1 (by norm_num) (by norm_num) (by norm_num) none).trans
    census_none_N4

/-- Gate `N = 5`, f-side: `#A = 16`. -/
theorem gate_fiber_A_N5 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellA} = 16 :=
  (two_level_census 2 5 2 1 (by norm_num) (by norm_num) (by norm_num) (some cellA)).trans
    census_A_N5

/-- Gate `N = 5`, f-side: `#B2 = 4`. -/
theorem gate_fiber_B2_N5 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB2} = 4 :=
  (two_level_census 2 5 2 1 (by norm_num) (by norm_num) (by norm_num) (some cellB2)).trans
    census_B2_N5

/-- Gate `N = 5`, f-side: `#self-loop-again = 4`. -/
theorem gate_fiber_B1_N5 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB1} = 4 :=
  (two_level_census 2 5 2 1 (by norm_num) (by norm_num) (by norm_num) (some cellB1)).trans
    census_B1_N5

/-- Gate `N = 5`, f-side: `#tail = 8`. -/
theorem gate_fiber_none_N5 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = none} = 8 :=
  (two_level_census 2 5 2 1 (by norm_num) (by norm_num) (by norm_num) none).trans
    census_none_N5

/-- Gate `N = 4` total: the two second-level classes exhaust the fiber, `8 = 4 + 4`. -/
theorem gate_total_N4 :
    Nat.card {f : QuotientBox.monicBox 2 4 (2 * 1) // InCellAt 2 4 1 2 1 f} = 4 + 4 := by
  rw [card_restart_fiber 2 4 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **The gate three-way split at `(2,2,5)`** (deliverable 3's interpretation, grounded):
`32 = (16 + 4) decided + 4 self-loop-again + 8 tail`. -/
theorem gate_threeway_N5 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) // InCellAt 2 5 1 2 1 f}
      = (Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
            InCellAt 2 5 1 2 1 f ∧
              classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellA}
          + Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
            InCellAt 2 5 1 2 1 f ∧
              classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB2})
        + Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
            InCellAt 2 5 1 2 1 f ∧
              classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB1}
        + Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
            InCellAt 2 5 1 2 1 f ∧
              classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = none} := by
  rw [gate_fiber_A_N5, gate_fiber_B2_N5, gate_fiber_B1_N5, gate_fiber_none_N5,
    card_restart_fiber 2 5 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ## 5. STRETCH (deliverable 5): the iterated self-loop mass at `k = 2` -/

/-- **The `k = 2` iterated self-loop identity at `(p, μ, N) = (2, 2, 5)`.**  The mass of TWO
successive self-loop reads (`f` in the root-refined self-loop cell, and its recentered read
again of self-loop shape) times `p^(k·(w(μ)+1))` at `k = 2` is EXACTLY the cluster-box card:

    4 · 2^(2·(w(2)+1)) = 4 · 2⁶ = 2⁸ = #clusterBox(2, 5, s = 2),

`w = L5fix.selfLoopExponent` (the `countPivot` exponent).  This grounds the first two terms of
the `omCount` self-loop geometric series `Σ_k q^(−k(w+1))` — the `countPivot` resummation's
base case — one genuine level down the tower (in particular the `≤ #clusterBox` mass bound of
the resummation holds with equality here). -/
theorem gate_iterated_selfLoop :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        InCellAt 2 5 1 2 1 f ∧
          classify1 2 (recenter' 2 5 2 1 (by norm_num) f) = some cellB1}
        * 2 ^ (2 * (L5fix.selfLoopExponent 2 + 1))
      = Nat.card {f : QuotientBox.monicBox 2 5 2 // CellCard.IsCluster 2 f} := by
  rw [gate_fiber_B1_N5, CellCard.card_clusterBox 2 (by norm_num)]
  norm_num [L5fix.selfLoopExponent]

end Gates

end LeanUrat.OM.SelfLoopTower
