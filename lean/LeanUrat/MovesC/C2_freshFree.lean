/-
Unit C2.freshFree  (moves_ref: §C.1(ii): E_fresh's realizations constrain only coordinates
FREE on Σ_i (round-3: statement unchanged; the JetSetup beneath is rebuilt — audit R2 F27/55))

Proof: i = 0 is J.init (nothing pinned before the root read). i = i'+1: J.fresh_band places
every fresh support coordinate STRICTLY ABOVE the cumulative floor (2nd band conjunct) at an
interior base index (1st band conjunct = the rim threshold of node i', matching the (ZC) rim);
the (ZC-a) EXACT DOWNSET (J.zc i').downset_exact says pinned ↔ height ≤ floor there, so
floor < height forces pinned = false.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C2_freshFree {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) (hi : i < H.nodes.length) : ∀ cl ∈ (J.fresh i).clauses, ∀ c ∈ cl.support, (J.Sigma i).pinned c = false := by
  cases i with
  | zero =>
    -- Nothing is pinned before the root read: Σ_0 is the full box.
    intro cl _ c _
    exact J.init c
  | succ i' =>
    intro cl h_cl c h_c
    have hi' : i' < H.nodes.length := Nat.lt_of_succ_lt hi
    -- The fresh support lies in read (i'+1)'s band: interior of node i''s rim (hrim) and
    -- STRICTLY ABOVE the cumulative floor at frame (i'+1) (hfloor).
    have hband := J.fresh_band (i'+1) hi cl h_cl c h_c
    obtain ⟨hrim, hfloor, -⟩ := hband
    -- The band's rim bound `prevRim n (i'+1)` IS the (ZC) rim threshold of node i'.
    have hrimEq : H.prevRim n (i'+1)
        = (H.nodes[i']'hi').μ * (H.nodes[i']'hi').childWidth := by
      simp [History.prevRim, List.getElem?_eq_getElem hi']
    have hrim' : (J.coordOf c).2 < (H.nodes[i']'hi').μ * (H.nodes[i']'hi').childWidth :=
      hrimEq ▸ hrim
    -- (ZC-a) exact downset on Σ (i'+1): pinned ↔ height ≤ floor at this interior index.
    have hde := (J.zc i' hi').downset_exact c hrim'
    -- floor < height (hfloor) contradicts height ≤ floor, so the coordinate is NOT pinned.
    have hnp : ¬ ((J.Sigma (i'+1)).pinned c = true) :=
      fun h => (not_le.mpr hfloor) (hde.mp h)
    simpa using hnp

end LeanUrat.MovesC
