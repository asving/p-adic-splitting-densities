/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RestartEquivGenH
import LeanUrat.OM.RphiRingGenH
import LeanUrat.OM.RphiGenHCount
import LeanUrat.OM.SelfLoopTower

/-!
# TowerRestartGenH — wave W6c-2: the ORDER-2 two-level restart census at GENERAL `(e, h)`

**Provenance.** `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §4 (order-`r` tower
recursion, `v_r` compounding) + §5.3 (RESOLVED 2026-07-06 — the W6c precondition gate:
"COMPOUNDS CLEANLY, zero gap-interaction", PROCEED). Gate ground truth:
`/workspace-vast/asving/tmp/phaseb_w6c_gate/` (compounded count, 0-mismatch) +
`/workspace-vast/asving/tmp/phaseb_w6d/` (order-2 census). Generalizes the banked
`SelfLoopTower.two_level_census` (the `e = 1, h = 1` order-2 TEMPLATE) to the GAPPED
child ring `R1 = RphiRingGenH.Rphi p N e h c` (gapped when `h ≥ 2`).

**The route.** Order 2 = "restart (`RestartEquivGenH.restartEquivGenH`, level 1, over the
order-1 gapped child ring `R1`), then classify the `β`-tuple over `R1` by its order-1 data (a
second restart)". The level-1 restart is the banked `restartEquivGenH`; the level-2 read is any
`R1`-valued classifier `Q` of the `β`-avatars (the deeper `R1`-menu classifier is the
undeveloped machinery, so — exactly as `HNode1.h_node1_single_shape` stays uniform in the
child reader `R` — the census is stated reader-uniform in `Q`; the concrete order-2 read is
its instantiation). The forward transport IS `restartDigitsGenH` by `rfl`
(`restartEquivGenH_apply_val`), so no new counting is introduced.

**Deliverables (order-2 CLOSED).**
1. `two_level_census_genH` (+ `censusEquivGenH`, `two_level_census_genH_shape`): the order-2
   census of a cluster refined by key `φ1 = X^e − c·p^h` (`h ≥ 1` general, gapped when `h ≥ 2`)
   — `Q`-conditioned cell fiber ≃ `Q`-conditioned fresh-cluster coset. At `h = 1` the fiber
   collapses to the banked shape (`card_two_level_genH_h_one_collapse`), matching
   `SelfLoopTower`'s banked value (`gate_h_one_matches_selfLoopBanked`).
2. `card_two_level_genH` (+ `card_two_level_genH_perslot`): the order-2 fiber card = the
   compounded per-digit product `∏_{j<μ} ∏_{i<e} p^(N − min N ⌈(e·h·(μ−j)+1 − i·h)/e⌉⁺)`,
   equivalently the per-slot product `∏_{j<μ} card_{R1}(filtIdeal (e·h·(μ−j)+1))` (the
   "restart over R1" form — the level-`j` slot counted by R1's own W6a count).
3. `order_r_induction_skeleton`: the order-2 case (the tractable core) PROVEN; the order-`r`
   recursion STATEMENT is documented below with the per-level obligation named.

**The order-`r ≥ 3` closure (STATED, not proven — the named residual).** The induction of
blueprint §4 is: `childRing_r := RphiRingGenH.Rphi` built OVER `childRing_{r−1}` (a TOWER of
finite local rings `R_r = R_{r−1}[t_r]/(t_r^{e_r} − c_r·Π^{h_r})`, residue = the GaloisField
tower); `freshClusterPattern_r` reuses blueprint §1 with `vL_r` (floor `e_r·h_r·(μ_r − j) + 1`
in `vL_r` units); the census factors as `∏_slot card_{R_{r−1}}(per-slot)`. The W6c gate (§5.3)
established this COMPOUNDS CLEANLY (the two tower generators occupy DISTINCT power-basis
monomials, so they stay independent in each graded piece `F_m / F_{m+1}` — no cross-level
cancellation, hence **no new cancellation lemma needed**). The single remaining proof
obligation PER LEVEL is the already-W6a-shaped per-slot strictness (the `⟨e_r, h_r⟩`-graded
filtration count, `RphiGenHCount.card_filtIdeal` re-proved with `R_{r−1}` — a finite local ring
with residue field `F_{q^f}` — as the coefficient ring in place of `ZMod (p^N)`).

**PRECISELY the missing piece for `r ≥ 3`:** a `RphiRingGenH`/`RphiGenHCount` layer whose
COEFFICIENT ring is a general finite local ring `R_{r−1}` (not the base `ZMod (p^N)`). This is
a mechanical reindex of `RphiRingGenH` (the `Rphi` construction, `digitEquiv`, `filtIdeal`,
`vL`) and `RphiGenHCount` (`card_filtIdeal` per-digit product) over that ring; every proof there
is written against `ZMod (p^N)` only through: (i) `digitEquiv` (free-module power basis — holds
over any base), (ii) the `p`-adic ball count `ball_count` (needs the base's own filtration count
— supplied inductively by `card_{R_{r−1}}`). Once that layer exists, `restartEquivGenH` and
`card_restartGenH_fiber` port verbatim (statement shape frozen), and `order_r_induction_skeleton`
extends to `r` by structural recursion on the tower height. That coefficient-ring generalization
of `RphiRingGenH`/`RphiGenHCount` is the named residual; it is NOT stated as a theorem here.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprint
`[propext, Classical.choice, Quot.sound]` (checked with `#print axioms`, prints removed after);
no existing module touched (purely additive over `RestartEquivGenH`/`RphiRingGenH`/
`RphiGenHCount`/`SelfLoopTower`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.TowerRestartGenH

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.RphiRing
open LeanUrat.OM.RphiRingGenH
open LeanUrat.OM.RphiGenHCount
open LeanUrat.OM.RestartEquivGenH

variable (p N e h μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## Deliverable 1: the Q-uniform order-2 census bijection -/

section Census

/-- **The general-`(e,h)` two-level census equivalence** (the order-2 core). -/
def censusEquivGenH (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (Q : (Fin μ → Rphi p N e h c) → Prop) :
    {f : QuotientBox.monicBox p N (μ * e) //
        InCellAtGenH p N e h μ c f ∧ Q (restartDigitsGenH' p N e h μ c hN he f)}
      ≃ {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β ∧ Q β} :=
  calc {f : QuotientBox.monicBox p N (μ * e) //
          InCellAtGenH p N e h μ c f ∧ Q (restartDigitsGenH' p N e h μ c hN he f)}
      ≃ {x : {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f} //
          Q (restartDigitsGenH' p N e h μ c hN he x.1)} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    _ ≃ {y : {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β} // Q y.1} :=
        (restartEquivGenH p N e h μ c hN he hh hμ2 hcop hhμN).subtypeEquiv fun x => by
          rw [restartEquivGenH_apply_val]
          exact Iff.rfl
    _ ≃ {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β ∧ Q β} :=
        Equiv.subtypeSubtypeEquivSubtypeInter _ _

/-- **Deliverable 1 — `two_level_census_genH`.** -/
theorem two_level_census_genH (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (Q : (Fin μ → Rphi p N e h c) → Prop) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) //
        InCellAtGenH p N e h μ c f ∧ Q (restartDigitsGenH' p N e h μ c hN he f)}
      = Nat.card {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β ∧ Q β} :=
  Nat.card_congr (censusEquivGenH p N e h μ c hN he hh hμ2 hcop hhμN Q)

/-- The level-2 classification of a level-1 cell element by an arbitrary R1-valued reader. -/
def childShapeGenH {α : Sort*} (hN : 0 < N) (he : 0 < e)
    (R : (Fin μ → Rphi p N e h c) → α) (f : QuotientBox.monicBox p N (μ * e)) : α :=
  R (restartDigitsGenH' p N e h μ c hN he f)

/-- **The order-2 census, node-identity form** (`Q := (R · = T')`). -/
theorem two_level_census_genH_shape {α : Sort*} (hN : 0 < N) (he : 0 < e) (hh : 0 < h)
    (hμ2 : 2 ≤ μ) (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (R : (Fin μ → Rphi p N e h c) → α) (T' : α) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) //
        InCellAtGenH p N e h μ c f ∧ childShapeGenH p N e h μ c hN he R f = T'}
      = Nat.card {β : Fin μ → Rphi p N e h c //
          FreshClusterPatternGenH p N e h μ c β ∧ R β = T'} :=
  two_level_census_genH p N e h μ c hN he hh hμ2 hcop hhμN (fun β => R β = T')

end Census

/-! ## Deliverable 2: the order-2 fiber card = the compounded per-digit product -/

section Card

/-- **Deliverable 2 — `card_two_level_genH`.** -/
theorem card_two_level_genH (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}
      = ∏ j : Fin μ, ∏ i : Fin e,
          p ^ (N - min N (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ))) :=
  card_restartGenH_fiber p N e h μ c hN he hh hμ2 hcop hhμN

/-- **`card_two_level_genH` in per-slot `card_{R1}(filtIdeal)` form** (the "restart over R1"). -/
theorem card_two_level_genH_perslot (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}
      = ∏ j : Fin μ, Nat.card (filtIdeal p N e h c (e * h * (μ - j.1) + 1)) := by
  rw [card_two_level_genH p N e h μ c hN he hh hμ2 hcop hhμN]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [card_filtIdeal p N e h c hN he (e * h * (μ - j.1) + 1)]

end Card

/-! ## Deliverable 3: the order-r induction skeleton -/

section OrderR

/-- **Deliverable 3 — order-`r` induction skeleton (order-2 base case, PROVEN).**

This is the order-2 step of the blueprint-§4 induction, in reader-uniform form: the level-1
restart over the gapped child ring `R1 = Rphi p N e h c` factors the `Q`-conditioned cell census
(for any level-2 `R1`-classifier `Q`) as the `Q`-conditioned fresh-cluster coset census. It IS
`two_level_census_genH`; naming it `order_r_induction_skeleton` records that the order-2 case is
the base+step-1 of the tower recursion.

The order-`r ≥ 3` extension (see the module header for the full statement + the precisely-named
missing piece — the coefficient-ring generalization of `RphiRingGenH`/`RphiGenHCount` over the
tower `R_{r−1}`, whose ONLY substantial obligation per level is the already-W6a-shaped per-slot
strictness `card_filtIdeal` over `R_{r−1}`) is NOT proven here and is deliberately not stated as
a theorem. -/
theorem order_r_induction_skeleton (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (Q : (Fin μ → Rphi p N e h c) → Prop) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) //
        InCellAtGenH p N e h μ c f ∧ Q (restartDigitsGenH' p N e h μ c hN he f)}
      = Nat.card {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β ∧ Q β} :=
  two_level_census_genH p N e h μ c hN he hh hμ2 hcop hhμN Q

end OrderR

/-! ## h1 = 1 collapse -/

section Collapse

/-- **`card_two_level_genH` at `h = 1` collapse.** -/
theorem card_two_level_genH_h_one_collapse (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ)
    (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e 1 μ c f}
      = p ^ (μ * (N * e - 1) - e * μ * (μ + 1) / 2) :=
  card_restartGenH_fiber_h_one_collapse p N e μ c hN he hμ2 hμN

end Collapse

/-! ## GATES -/

section Gates

/-- **Gate DG (doubly-gapped ⟨2,3⟩ over ⟨2,3⟩, level-1 fiber card).** -/
theorem gate_DG_level1_2323 :
    Nat.card {f : QuotientBox.monicBox 2 7 (2 * 2) // InCellAtGenH 2 7 2 3 2 1 f} = 1024 := by
  rw [card_two_level_genH 2 7 2 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  decide

/-- **Gate: the per-slot `card_{R1}(filtIdeal)` DG numbers** (level-2 fresh floors). -/
theorem gate_DG_perslot_2323 :
    Nat.card (filtIdeal 2 7 2 3 (1 : (ZMod (2 ^ 7))ˣ) 13) = 4
      ∧ Nat.card (filtIdeal 2 7 2 3 (1 : (ZMod (2 ^ 7))ˣ) 7) = 256 := by
  refine ⟨?_, ?_⟩
  · rw [card_filtIdeal 2 7 2 3 (1 : (ZMod (2 ^ 7))ˣ) (by norm_num) (by norm_num) 13]; decide
  · rw [card_filtIdeal 2 7 2 3 (1 : (ZMod (2 ^ 7))ˣ) (by norm_num) (by norm_num) 7]; decide

/-- **Gate DG order-2 compounded count (doubly-gapped ⟨2,3⟩ over ⟨2,3⟩, N=4, W=16).**
The genuinely order-2 doubly-gapped number `card(filtIdeal2 16) = 32` reconstructed as the
compounded "restart over R1" product `∏_{j<e2} card_{R1}(filtIdeal1 ⌈(16 − e1·h2·j)/e2⌉⁺)
= card_{R1}(filtIdeal1 8) · card_{R1}(filtIdeal1 5) = 2 · 16 = 32`, where R1 = ⟨2,3⟩ at N=4.
Matches `phaseb_w6c_gate/w6c_results.json` DG_doublygapped_2323 `card_compounded_over_R1["16"]`. -/
theorem gate_DG_order2_compounded_W16 :
    Nat.card (filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) 8)
        * Nat.card (filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) 5) = 32 := by
  rw [card_filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) (by norm_num) (by norm_num) 8,
    card_filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) (by norm_num) (by norm_num) 5]
  decide

/-- **Gate DG order-2 compounded count (W=13): `128`.** `card_{R1}(filtIdeal1 7) ·
card_{R1}(filtIdeal1 4) = 4 · 32 = 128`. Matches DG `card_compounded_over_R1["13"]`. -/
theorem gate_DG_order2_compounded_W13 :
    Nat.card (filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) 7)
        * Nat.card (filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) 4) = 128 := by
  rw [card_filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) (by norm_num) (by norm_num) 7,
    card_filtIdeal 2 4 2 3 (1 : (ZMod (2 ^ 4))ˣ) (by norm_num) (by norm_num) 4]
  decide

/-- **Gate: the h = 1 collapse value** matches the banked `RestartEquivGenH` fiber. -/
theorem gate_h_one_collapse :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAtGenH 2 3 2 1 2 1 f} = 16 := by
  rw [card_two_level_genH_h_one_collapse 2 3 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- **Gate: h = 1 collapse consistency with SelfLoopTower's banked value.** -/
theorem gate_h_one_matches_selfLoopBanked :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAtGenH 2 3 2 1 2 1 f}
      = Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // RestartEquiv.InCellAt 2 3 2 2 1 f} :=
  gate_S_h_one_matches_banked

end Gates

end

end LeanUrat.OM.TowerRestartGenH
