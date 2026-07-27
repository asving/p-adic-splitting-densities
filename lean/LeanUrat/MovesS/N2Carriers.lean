/-
Unit `n2_carriers` (medium; S5 construction batch) — the MeasuredSide instance:
Box/Cell/Rep carriers + boxpos/rep_ne (Codex#6-13 split).  The remaining
MeasuredSide data groups are pinned by their own units (n2_events, n2_pools,
n2_heights, n2_ent_flow).
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/- `n2M` is assembled by obligation group (R43/R48): the Pools group is the
`n2_pools` unit's fill ("Pools := all prime powers"); the counting-carrier and
cell/representative groups are the `n2_carriers` fill; the height group is the
`n2_heights` fill (singleton exact height class per cell, gwt = the R26 one-step
masses — chosen so the events unit can realize them as card ratios: at q₀ = Q ≥ 2
the box has Q³ points and the three block-2 masses have integer event cards
1, Q³ − Q², Q² − 1, a partition of Q³); the cell-event/measured-row group is the
`n2_events` fill; the kernel-flow/activity and entrance groups are the
`n2_ent_flow` fill.  All obligation groups are now filled. -/
noncomputable def n2M : MeasuredSide n2T where
  -- Pools group (unit n2_pools)
  Pools := {q : ℚ | ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q = (p : ℚ) ^ (δ : ℕ)}
  pools_prime_pow := fun _ hq₀ => hq₀
  pools_closed := by
    rintro q₀ ⟨p, hp, d, rfl⟩ δ
    exact ⟨p, hp, d * δ, by rw [PNat.mul_coe, pow_mul]⟩
  pools_infinite :=
    Set.infinite_of_injective_forall_mem
      (f := fun p : Nat.Primes => ((p : ℕ) : ℚ))
      (fun _ _ h => Subtype.ext (Nat.cast_injective h))
      (fun p => ⟨p, p.prop, 1, by rw [PNat.one_coe, pow_one]⟩)
  -- counting carrier (unit n2_carriers): the level-N residue boxes, of size q₀³
  -- at every pool q₀ = p^δ (N-independent at this instance; the `max 1 _` clamp
  -- keeps every box inhabited off-pools, where all events are ∅)
  Box := fun q₀ _ => Fin (max 1 (q₀.num.toNat ^ 3))
  finB := fun _ _ => inferInstance
  boxpos := fun _ _ => ⟨⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩⟩
  -- cells / representatives (unit n2_carriers): one cell per roster outcome at the
  -- block-2 layer (the three-outcome roster), ONE cell (the (1,1)-terminal mass-1
  -- cell) at every other layer; representatives are a singleton (rep-independence
  -- by construction)
  Cell := fun e _ => Fin (if e = 2 then 3 else 1)
  finC := fun _ _ => inferInstance
  cellOut := fun _ _ c => (⟨c.1 % 3, by omega⟩ : Fin 3)
  Rep := fun _ _ => Fin 1
  rep_ne := fun _ _ _ => ⟨0⟩
  cellLvl := fun _ _ _ => 0
  cellInst := fun _ _ _ _ _ => {⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩}
  -- heights (unit n2_heights): ONE exact height class (0 : ℕ) per cell; gwt at
  -- the class = the R26 one-step mass of the cell's outcome (single monomials:
  -- q₀⁻³ / 1 − q₀⁻¹ / q₀⁻¹ − q₀⁻³ at block 2, the full mass 1 elsewhere), and 0
  -- off the class
  Hgt := ℕ
  HDom := fun _ _ _ => {0}
  gwt := fun e _ c h q₀ =>
    if h = 0 then
      if e = 2 then
        if c.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
        else if c.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
        else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3
      else 1
    else 0
  -- cell events / measured rows (unit n2_events): the three block-2 events are the
  -- interval partition of the Q³-point box (Q := q₀.num.toNat), thresholds 1 and
  -- max 1 Q² — so d4r0-disjointness is unconditional, including off-pools where
  -- Q may be 0.  At every pool (Q = q₀ ≥ 2) the cards are 1 · Q³ − Q² · Q² − 1:
  -- the R26 row masses q₀⁻³ · 1 − q₀⁻¹ · q₀⁻¹ − q₀⁻³ as EXACT card ratios
  -- (N-independent, so meas_card holds with N₀ = 0).  Every other layer carries
  -- its full box (the single mass-1 cell); events vanish off the height class
  -- {0} (xhd_no_orphan) and ignore the representative (rep-independence by
  -- construction).  μcell = gwt at the height class; rowVal is keyed by the
  -- outcome exactly as μcell is keyed by the cell, matching cellOut = c.1 % 3
  -- (single cell ↦ outcome 0 at e ≠ 2), so rep_indep/part1 hold by evaluation.
  cellEvt := fun e _ _ c h q₀ _ =>
    if h = 0 then
      if e = 2 then
        if c.1 = 0 then Finset.univ.filter (fun x => x.1 < 1)
        else if c.1 = 1 then
          Finset.univ.filter (fun x => max 1 (q₀.num.toNat ^ 2) ≤ x.1)
        else Finset.univ.filter (fun x => 1 ≤ x.1 ∧ x.1 < max 1 (q₀.num.toNat ^ 2))
      else Finset.univ
    else ∅
  μcell := fun e _ _ c q₀ =>
    if e = 2 then
      if c.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
      else if c.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
      else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3
    else 1
  rowVal := fun e _ o q₀ =>
    if e = 2 then
      if o.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
      else if o.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
      else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3
    else if o.1 = 0 then 1 else 0
  -- kernel flow / activity (unit n2_ent_flow): the 1×1 kernel entry q₀⁻³ on the
  -- block-2 layer, no continuation elsewhere; kstep k = the k-th scalar power
  -- (so kstep 0 = 1 and the HMC scalar law kstep (k+1) = kstep k · kstep 1 holds
  -- on every layer); all states active at all q₀ (R45 all-active — act_target's
  -- inactive case is vacuous)
  kstep := fun k e _ _ q₀ => (if e = 2 then ((q₀ : ℝ))⁻¹ ^ 3 else 0) ^ k
  activeState := fun _ _ _ => True
  decA := fun _ _ _ => .isTrue trivial
  -- entrance side (unit n2_ent_flow): ONE entrance shape ε per block (the root
  -- entrance, mass 1).  Its height data mirrors the cell side: ιDom = {0} is the
  -- one exact height class (comp_once = a genuine one-term sum), ιshH = 1 at the
  -- class is realized by the FULL box (entEvtH = univ: 1 · #Box = #univ, the
  -- init_count card-ratio tie), so ιsh = ιval = 1; entInst is a singleton at
  -- entLvl 0, so entCount = 1 (ι-side presentation: countT = countS = 1,
  -- degree bounds Went = 0).  markedVal = 1 = ι(1 − K)⁻¹b at both blocks (the
  -- W1m-consistent value; the identification is the pinned seam, never claimed).
  EntShape := fun _ _ => Unit
  finE := fun _ _ => inferInstance
  hent := fun _ _ _ => 0
  Went := fun _ _ _ => 0
  entEvtH := fun _ _ _ h _ _ => if h = 0 then Finset.univ else ∅
  ιDom := fun _ _ _ => {0}
  ιshH := fun _ _ _ h _ => if h = 0 then 1 else 0
  ιsh := fun _ _ _ _ => 1
  ιval := fun _ _ _ => 1
  entCount := fun _ _ _ _ => 1
  entLvl := fun _ _ _ => 0
  entInst := fun _ _ _ _ _ => {⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩}
  markedVal := fun _ _ => 1

theorem n2_carriers :
    (∀ e (τ : n2T.State e), Nonempty (n2M.Cell e τ)) ∧
    (∀ e (τ : n2T.State e), Nonempty (n2M.Rep e τ)) ∧
    (∀ e (τ : n2T.State e) (c c' : n2M.Cell 2 n2τ),
      n2M.cellOut 2 n2τ c = n2M.cellOut 2 n2τ c' → c = c') := by
  refine ⟨fun e τ => ⟨⟨0, ?_⟩⟩, fun _ _ => ⟨⟨0, Nat.one_pos⟩⟩, fun _ _ c c' h => ?_⟩
  · show 0 < if e = 2 then 3 else 1
    split <;> omega
  · -- `cellOut 2 n2τ` is `c ↦ ⟨c.1 % 3, _⟩` on `Fin 3`, where `% 3` is the
    -- identity — so equal images force equal cells.
    have hv : c.1 % 3 = c'.1 % 3 := congrArg Fin.val h
    have hc : c.1 < 3 := c.2
    have hc' : c'.1 < 3 := c'.2
    exact Fin.ext (by omega)

end LeanUrat.MovesS
