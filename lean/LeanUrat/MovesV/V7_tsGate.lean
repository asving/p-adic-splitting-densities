/-  MovesV unit V7-3b `degcons_kmat_gate` — DegCons + KmatHyp AT THE GATE
    INSTANCE.
    N1 DE-VACUIFICATION (round-4 ratification verdict, 2026-07-29: the old
    statement concluded `→ True` by `trivial`, establishing neither gate
    property).  The theorem now has real content: GIVEN the C-side roster
    facts (member positivity, per-block size-sum bound, kcol-member size
    law — the gate decide legs, deferred with DefsGate's roster deviation,
    hence hypotheses), the PINNED gate instance (`TablePins C T`, V7-3a)
    satisfies `MovesS.DegCons` AND `MovesS.KmatHyp` at every block —
    derived by transporting the odata member-list tie (size, δ,
    status-with-target-skeleton) across the pins; `routeOf` transports
    because the tie preserves lengths and status sides. -/
import LeanUrat.MovesV.V7_ts
import LeanUrat.MovesV.V2_degcons

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.MovesV

theorem degcons_kmat_gate {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n))
    (hpos : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m),
      ∀ mu ∈ (C.bd s).omem m o, 1 ≤ mu.size)
    (hsum : ∀ e ∈ Finset.Icc 1 n, ∀ s : Skeleton n, skBlk s = e →
      ∀ (m : (C.bd s).Letter) (o : (C.bd s).Outc m),
      (((C.bd s).omem m o).map OMember.size).sum ≤ e)
    (hkc : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m),
      (((C.bd s).omem m o).filter (fun mu => mu.status.isRight)).length ≠ 0 →
      ((C.bd s).omem m o).length = 1 →
      ∀ mu ∈ (C.bd s).omem m o, mu.size = skBlk s) :
    ∃ T : MovesS.TableShape n,
      TablePins C T ∧ MovesS.DegCons T ∧
      ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e := by
  classical
  obtain ⟨T, hpins, -⟩ := tableShape_inst C hfin
  obtain ⟨hv, hst, hws, hOT⟩ := hpins
  -- the transported roster facts, per (e, τ, o)
  have key : ∀ (e : ℕ) (τ : T.State e) (o : T.Out e τ),
      ∃ (m : (C.bd ((hst e) τ).1.1).Letter)
        (oc : (C.bd ((hst e) τ).1.1).Outc m),
        (T.odata e τ o).mem.map MovesS.Member.size
          = ((C.bd ((hst e) τ).1.1).omem m oc).map OMember.size ∧
        (T.odata e τ o).mem.map (fun μ => μ.status.isRight)
          = ((C.bd ((hst e) τ).1.1).omem m oc).map
              (fun mu => mu.status.isRight) := by
    intro e τ o
    obtain ⟨ho, hwl, htie⟩ := hOT e τ
    refine ⟨(ho o).1, (ho o).2, ?_, ?_⟩
    · have h1 := congrArg
        (List.map (fun t : ℕ × ℕ+ × (VLabel n ⊕ Skeleton n) => t.1)) (htie o)
      rw [List.map_map, List.map_map] at h1
      exact h1
    · have h2 := congrArg
        (List.map (fun t : ℕ × ℕ+ × (VLabel n ⊕ Skeleton n) => t.2.2.isRight))
        (htie o)
      rw [List.map_map, List.map_map] at h2
      calc (T.odata e τ o).mem.map (fun μ => μ.status.isRight)
          = (T.odata e τ o).mem.map
            ((fun t : ℕ × ℕ+ × (VLabel n ⊕ Skeleton n) => t.2.2.isRight) ∘
              (fun μ => (μ.size, μ.δ,
                Sum.map hv (fun σ => ((hst μ.size) σ).1.1) μ.status))) :=
            List.map_congr_left (fun μ _ => by
              cases hμ : μ.status <;> simp [hμ])
        _ = _ := h2
        _ = ((C.bd ((hst e) τ).1.1).omem (ho o).1 (ho o).2).map
              (fun mu => mu.status.isRight) := rfl
  refine ⟨T, ⟨hv, hst, hws, hOT⟩, ⟨?_, ?_⟩, ?_⟩
  · -- DegCons.size_pos via the size-list tie
    intro e τ o μ hμ
    obtain ⟨m, oc, hsz, -⟩ := key e τ o
    have hmem : μ.size ∈ ((C.bd ((hst e) τ).1.1).omem m oc).map OMember.size := by
      rw [← hsz]; exact List.mem_map_of_mem hμ
    obtain ⟨mu, hmu, hEq⟩ := List.mem_map.mp hmem
    exact hEq ▸ hpos _ m oc mu hmu
  · -- DegCons.size_sum via the size-list tie + the block law skBlk = e
    intro e he τ o
    obtain ⟨m, oc, hsz, -⟩ := key e τ o
    rw [hsz]
    exact hsum e he ((hst e) τ).1.1 ((hst e) τ).2 m oc
  · -- KmatHyp: kcol routes transport (lengths + status sides preserved)
    intro e he τ o hroute μ hμ
    obtain ⟨m, oc, hsz, hsr⟩ := key e τ o
    -- decode routeOf = kcol into (c ≠ 0, m = 1)
    have hcm : (T.odata e τ o).c ≠ 0 ∧ (T.odata e τ o).m = 1 := by
      by_cases hc : (T.odata e τ o).c = 0
      · exfalso
        unfold MovesS.routeOf at hroute
        rw [if_pos hc] at hroute
        exact absurd hroute (by decide)
      · by_cases hm1 : (T.odata e τ o).m = 1
        · exact ⟨hc, hm1⟩
        · exfalso
          unfold MovesS.routeOf at hroute
          rw [if_neg hc, if_neg hm1] at hroute
          exact absurd hroute (by decide)
    -- transport m: lengths agree
    have hlen : ((C.bd ((hst e) τ).1.1).omem m oc).length = 1 := by
      have hl := congrArg List.length hsz
      rw [List.length_map, List.length_map] at hl
      rw [← hl]; exact hcm.2
    -- transport c: countP of isRight agrees
    have hcnt : (((C.bd ((hst e) τ).1.1).omem m oc).filter
        (fun mu => mu.status.isRight)).length ≠ 0 := by
      intro hzero
      apply hcm.1
      have h2 := congrArg (List.countP (fun b : Bool => b)) hsr
      rw [List.countP_map, List.countP_map] at h2
      have h2' : List.countP (fun μ : MovesS.Member T.VType T.State =>
            μ.status.isRight) (T.odata e τ o).mem
          = List.countP (fun mu : OMember n => mu.status.isRight)
              ((C.bd ((hst e) τ).1.1).omem m oc) := h2
      show ((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).length = 0
      rw [← List.countP_eq_length_filter, h2', List.countP_eq_length_filter]
      exact hzero
    -- the member's size through the tie, then the kcol size law
    have hmem : μ.size ∈ ((C.bd ((hst e) τ).1.1).omem m oc).map OMember.size := by
      rw [← hsz]; exact List.mem_map_of_mem hμ
    obtain ⟨mu, hmu, hEq⟩ := List.mem_map.mp hmem
    rw [← hEq, hkc _ m oc hcnt hlen mu hmu]
    exact ((hst e) τ).2

end LeanUrat.MovesV
