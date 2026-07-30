/-
Unit HK-37  (BRIDGE campaign, area BP2, cluster Block K — COUNTERMODEL GATE, executed)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block K, unit HK-37; risk R-3.

CHARGE: "COUNTERMODEL attempt (BEFORE HK-38): the badSeed lifted one read up AGAINST
the landed laws — construct a lawful seed (all ZCSeedLaws fields incl. theta_norm)
with a nonzero strip correction at read i+1, or prove the construction blocked by
theta_norm (expected: blocked — the shifted coordinate sits at-or-below the step
floor, exactly theta_norm's guard)."

VERDICT: **BLOCKED — COMPILED.** The statement `zc_step_interiorZero` (U10_zcStep.lean,
sorried) SURVIVES this attack. This file does NOT import U10_zcStep; it proves the
BLOCKING LEMMA against the landed `ZCSeedLaws.theta_norm` (Defs.lean), so no negation
witness coexists with any sorried universal.

THE ATTEMPT (recorded per the countermodel-gate discipline).  The U9c-era badSeed
(`scratch_U7_recursion_false.lean`, now dead at the root by `theta_norm`) is the
constant unitriangular shift `Θ x c = x c + 1` (corr ≡ 1) attached at the read whose
strip clauses it poisons: post-DC-3 the chosen system's strip solve is `−corr`, so a
nonzero correction at a STRIP coordinate makes `interior_zero`'s literal-zero goal
false.  The lift one read up must therefore place a nonzero `Theta (i+1)`-correction
at a coordinate `c` that
  (a) carries a strip clause of read i+1 — i.e. `c ∈ stripSet H n N (i+1) ν_{i+1}`,
      whose defining condition includes the FRESH BAND's upper edge
      `htH (i+1) c ≤ slotVal (fineSlot c.2)`; and
  (b) is INTERIOR to the new rim (`(coordOf c).2 < μ_{i+1}·childWidth_{i+1}`) — else
      it never enters `zc_step_interiorZero`'s guard and refutes nothing.
NO CONCRETE 2-NODE GATE EXISTS ON DISK YET (HK-15/HK-18 are sorried skeletons, HK-22
pending), but no instance is needed: the blocking proof below is UNIVERSAL — at EVERY
coherent history, every (a)∧(b) site is covered by `theta_norm`'s guard, so a lawful
seed's correction VANISHES there.  The countermodel construction is contradictory
before any concrete data is chosen.

THE MECHANISM (the exact cancellation; this is also the general-step floor bridge of
the HK-55 spec — the `kappaH`/`innerslotH` arithmetic replacing U9a's root collapse):
with `b := (coordOf c).2`, `ν := nodes[i+1]`, `Dw := ν.Dwidth`, `cw := ν.childWidth
= (e·g)·Dw`, `m := innerslotH (i+1) b = (b % cw)/Dw`:
  htH (i+2) c = htH (i+1) c + m·κ_{i+1}                       (htH is a level sum)
  κ_{i+1}     = h/(e·STR_{i+1}) = slope_{i+1}·Dw              (coherence slope law)
  (b/Dw)·Dw   = (b/cw)·cw + m·Dw                              (block decomposition)
  ⟹ htH (i+2) c ≤ line.at((b/Dw)·Dw) + m·slope·Dw = line.at((b/cw)·cw)
              = staircase_{i+1}(b)  [interior branch, needs (b)]
              ≤ floorH (i+2) b      [C2_floorH_succ max]
— the line's descent across the `m` fine slots of `b`'s coarse block EXACTLY cancels
the new level's height increment `m·κ`.  The shifted coordinate lands at-or-below the
step floor: `theta_norm`'s guard, which forces `Theta (i+1) x c = x c` for ALL raw
digit vectors `x` (the unconditional-in-`x` form the 2026-07-28 U10c escalation
sharpening demanded).  So corr = 0 at every admissible shift site: the badSeed lift
is LAWLESS wherever it would refute, and lawful only where it is harmless (band
coordinates AT-OR-BEYOND the new rim — (ZC-b) lead territory, outside the goal).

RESIDUE HANDED FORWARD (what this gate does NOT close — R-3's remaining legs, for
HK-36/HK-38/HK-55; NOT reachable by a strip correction, hence outside HK-37's charge):
  (1) VALUE-interior coordinates at step reads (root_shape is root-only): a value
      clause's solve is the emitted vOf digit, spec-unconstrained — HK-36 audit
      item (b); if underivable from window containment + rim orientation, the Q8
      STEP-shape ZCSeedLaws field fires (D5-fence event, pre-declared at R-3).
  (2) OLD-pin transport sites (IsFreshAttach clause (4), solve = −corr again): for an
      old pin with innerslot m = 0 the guard fires unconditionally
      (`HK37_step_floor_guard_of_old_pin` below); for m ≥ 1 the guard reduces by the
      SAME cancellation to `htH (i+1) c ≤ slotVal_{i+1}(fineSlot b)` — i.e. the old
      pin must sit at-or-below read-(i+1)'s band edge.  An old-floor pin PAST the
      (γ)-crossing of the new line would evade; excluding it under
      coherence+realizability is exactly the line-dominance chain (HK-30/HK-31's
      floor leg, risk R-2) — at 2-node histories (SAE) forbids it directly.  HK-38's
      interior-zero assembly must consume one of these two routes for clause-(4)
      sites; flagged, not silently assumed.

deps consumed: HC2.Defs (the landed theta_norm — the D5-fence field), MovesC
C2_floorH_succ (PROVED).  HK-36's audit report is not on disk; this gate's verdict is
independent of it (the blocking needs no coverage audit).  HK-06's HistoryCoherent
re-key does not touch the three clauses used here (root degree / slope law / γ-tie
positions are wave-stable; the re-key is the child-keying leg).
Axioms: Lean core only (verified by the #print axioms at EOF).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.MovesC.C2_floorH_succ

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK37

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### §1 — the level-sum recursion and the slope-law form of κ -/

/-- `htH` grows one level per step: the frame-(k+1) height is the frame-k height plus
the level-k inner slot times the level-k weight. -/
private lemma htH_succ (H : History p F) (k : ℕ) (c : Coord) :
    H.htH (k+1) c = H.htH k c + (H.innerslotH k c.2 : ℚ) * H.kappaH k := by
  unfold History.htH
  rw [Finset.sum_range_succ]
  ring

/-- The accumulated stretch is positive (every recorded read has `e ≥ 1`). -/
private lemma strFrame_pos (H : History p F) (k : ℕ) : 0 < H.strFrame k := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  unfold History.strFrame at h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨ν, -, hν⟩ := List.mem_map.mp h0
  exact absurd hν.symm (Nat.one_le_iff_ne_zero.mp ν.he).symm

/-- Under coherence's slope law, the level-k weight is the recorded line's slope times
the frame width: `κ_k = h/(e·STR) = slope·Dwidth`. -/
private lemma kappaH_eq_slope_mul {H : History p F} (hcoh : HistoryCoherent H)
    (k : ℕ) (hk : k < H.nodes.length) :
    H.kappaH k = (H.nodes[k]'hk).line.slope * ((H.nodes[k]'hk).Dwidth : ℚ) := by
  have hnode : H.nodes[k]? = some (H.nodes[k]'hk) := by
    rw [List.getElem?_eq_getElem]
  have he0 : ((H.nodes[k]'hk).e : ℚ) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp (H.nodes[k]'hk).he
  have hstr0 : ((H.strFrame k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (strFrame_pos H k)
  have hκ : H.kappaH k = ((H.nodes[k]'hk).h : ℚ)
      / (((H.nodes[k]'hk).e : ℚ) * ((H.strFrame k : ℕ) : ℚ)) := by
    unfold History.kappaH
    rw [hnode]
    rfl
  rw [hκ, ← hcoh.2.1 k hk, div_eq_iff (mul_ne_zero he0 hstr0)]
  ring

/-- The level-k inner slot, unfolded at a recorded index. -/
private lemma innerslotH_eq (H : History p F) (k : ℕ) (hk : k < H.nodes.length) (b : ℕ) :
    H.innerslotH k b = (b % (H.nodes[k]'hk).childWidth) / (H.nodes[k]'hk).Dwidth := by
  unfold History.innerslotH
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- Block decomposition of the fine-slot left edge: the fine left edge of `b` is its
coarse left edge plus the inner-slot offset (`Dw ∣ cw` via `cw = k·Dw`). -/
private lemma div_block_decomp (b k Dw : ℕ) :
    b / Dw * Dw = b / (k * Dw) * (k * Dw) + b % (k * Dw) / Dw * Dw := by
  rcases Nat.eq_zero_or_pos Dw with h0 | hpos
  · subst h0; simp
  · have hb : b = b % (k * Dw) + b / (k * Dw) * k * Dw := by
      calc b = b % (k * Dw) + k * Dw * (b / (k * Dw)) :=
            (Nat.mod_add_div b (k * Dw)).symm
        _ = b % (k * Dw) + b / (k * Dw) * k * Dw := by ring
    calc b / Dw * Dw
        = (b % (k * Dw) + b / (k * Dw) * k * Dw) / Dw * Dw := by rw [← hb]
      _ = (b % (k * Dw) / Dw + b / (k * Dw) * k) * Dw := by
          rw [Nat.add_mul_div_right _ _ hpos]
      _ = b / (k * Dw) * (k * Dw) + b % (k * Dw) / Dw * Dw := by ring

/-! ### §2 — THE BLOCKING LEMMA: the general-step floor bridge -/

/-- **The general-step floor bridge** (the HK-37 blocking mechanism; also the HK-55
spec's content): at a coherent history, any coordinate at-or-below read-(i+1)'s fresh
band upper edge (`htH (i+1) ≤ slotVal ∘ fineSlot` — inFreshBand's third clause) whose
base index is INTERIOR to the new rim sits AT-OR-BELOW THE STEP FLOOR at frame i+2.
The line's descent across the inner slots exactly cancels the new level's height
increment (`κ_{i+1} = slope·Dwidth`, the coherence slope law). -/
theorem step_floor_guard {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) (c : Coord)
    (hedge : H.htH (i+1) c
      ≤ (H.nodes[i+1]'hi1).slotVal ((H.nodes[i+1]'hi1).fineSlot c.2))
    (hint : c.2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) :
    ((H.htH (i+2) c : ℚ) : WithBot ℚ) ≤ H.floorH (i+2) c.2 := by
  have hfl : H.floorH (i+2) c.2
      = max (H.floorH (i+1) c.2) ((H.nodes[i+1]'hi1).staircase c.2) :=
    C2_floorH_succ H (i+1) hi1 c.2
  -- the ℚ-level bound against the new staircase's interior value
  have hQ : H.htH (i+2) c
      ≤ (H.nodes[i+1]'hi1).line.at
          (c.2 / (H.nodes[i+1]'hi1).childWidth * (H.nodes[i+1]'hi1).childWidth) := by
    have hrec : H.htH (i+2) c
        = H.htH (i+1) c + (H.innerslotH (i+1) c.2 : ℚ) * H.kappaH (i+1) :=
      htH_succ H (i+1) c
    have hκ := kappaH_eq_slope_mul hcoh (i+1) hi1
    have hm := innerslotH_eq H (i+1) hi1 c.2
    -- the block decomposition, cast to ℚ (childWidth = (e·g)·Dwidth definitionally)
    have hdivN : c.2 / (H.nodes[i+1]'hi1).Dwidth * (H.nodes[i+1]'hi1).Dwidth
        = c.2 / (H.nodes[i+1]'hi1).childWidth * (H.nodes[i+1]'hi1).childWidth
          + c.2 % (H.nodes[i+1]'hi1).childWidth / (H.nodes[i+1]'hi1).Dwidth
            * (H.nodes[i+1]'hi1).Dwidth :=
      div_block_decomp c.2 ((H.nodes[i+1]'hi1).e * (H.nodes[i+1]'hi1).g)
        (H.nodes[i+1]'hi1).Dwidth
    have hcast : ((c.2 / (H.nodes[i+1]'hi1).Dwidth * (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)
        = ((c.2 / (H.nodes[i+1]'hi1).childWidth * (H.nodes[i+1]'hi1).childWidth : ℕ) : ℚ)
          + ((c.2 % (H.nodes[i+1]'hi1).childWidth / (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)
            * (((H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ) := by
      exact_mod_cast hdivN
    -- the band edge, with Line.at unfolded (slotVal ∘ fineSlot is definitionally
    -- the line at the fine left edge)
    have hedge' : H.htH (i+1) c
        ≤ (H.nodes[i+1]'hi1).line.intercept - (H.nodes[i+1]'hi1).line.slope
            * ((c.2 / (H.nodes[i+1]'hi1).Dwidth * (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ) :=
      hedge
    have hline : (H.nodes[i+1]'hi1).line.intercept - (H.nodes[i+1]'hi1).line.slope
          * ((c.2 / (H.nodes[i+1]'hi1).Dwidth * (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)
        = ((H.nodes[i+1]'hi1).line.intercept - (H.nodes[i+1]'hi1).line.slope
            * ((c.2 / (H.nodes[i+1]'hi1).childWidth * (H.nodes[i+1]'hi1).childWidth : ℕ) : ℚ))
          - ((c.2 % (H.nodes[i+1]'hi1).childWidth / (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)
            * ((H.nodes[i+1]'hi1).line.slope * (((H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)) := by
      rw [hcast]
      ring
    rw [hrec, hm, hκ]
    show H.htH (i+1) c
        + ((c.2 % (H.nodes[i+1]'hi1).childWidth / (H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ)
          * ((H.nodes[i+1]'hi1).line.slope * (((H.nodes[i+1]'hi1).Dwidth : ℕ) : ℚ))
      ≤ (H.nodes[i+1]'hi1).line.intercept - (H.nodes[i+1]'hi1).line.slope
          * ((c.2 / (H.nodes[i+1]'hi1).childWidth * (H.nodes[i+1]'hi1).childWidth : ℕ) : ℚ)
    linarith [hline ▸ hedge']
  -- assemble through the max and the staircase's interior branch
  rw [hfl]
  refine le_trans ?_ (le_max_right _ _)
  unfold Node.staircase
  rw [if_pos hint, WithBot.coe_le_coe]
  exact hQ

/-! ### §3 — THE COUNTERMODEL IS BLOCKED -/

/-- **HK-37, main corollary** — the badSeed lift is BLOCKED at every admissible shift
site: at a coherent history, a LAWFUL seed's move map `Theta (i+1)` is LITERAL (zero
correction, for ALL raw digit vectors) at every read-(i+1) fresh-band coordinate
interior to the new rim.  The strip solve of the chosen system at such a coordinate is
`−corr = 0`: `zc_step_interiorZero`'s strip-clause sites cannot be poisoned. -/
theorem theta_norm_blocks_band {n N : ℕ} {H : History p F}
    {keys : ℕ → Polynomial ℤ_[p]} (S : PresentSeed p F H n N keys)
    (hcoh : HistoryCoherent H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (c : Fin (n * N))
    (hband : inFreshBand H n (boxChart n N) (i+1) (H.nodes[i+1]'hi1) c)
    (hint : (boxChart n N c).2
      < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) :
    ∀ x : Fin (n * N) → ZMod p, S.Theta (i+1) x c = x c := by
  intro x
  exact S.zcSeed.theta_norm (i+1) hi1 c
    (step_floor_guard hcoh i hi1 (boxChart n N c) hband.2.2 hint) x

/-- The same, keyed at the exact shift sites of the attempted countermodel: members of
read-(i+1)'s STRIP roster (the coordinates that receive literal-zero strip clauses,
whose chosen-system solve is `−corr`).  A lawful lift of the badSeed to read i+1 with
a nonzero strip correction at an interior strip coordinate is CONTRADICTORY. -/
theorem theta_norm_blocks_stripSet {n N : ℕ} {H : History p F}
    {keys : ℕ → Polynomial ℤ_[p]} (S : PresentSeed p F H n N keys)
    (hcoh : HistoryCoherent H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (c : Fin (n * N))
    (hc : c ∈ stripSet H n N (i+1) (H.nodes[i+1]'hi1))
    (hint : (boxChart n N c).2
      < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) :
    ∀ x : Fin (n * N) → ZMod p, S.Theta (i+1) x c = x c := by
  classical
  have hband : inFreshBand H n (boxChart n N) (i+1) (H.nodes[i+1]'hi1) c := by
    unfold stripSet at hc
    rw [Finset.mem_filter] at hc
    exact hc.2.1
  exact theta_norm_blocks_band S hcoh i hi1 c hband hint

/-! ### §4 — the residue boundary (clause-(4) old-pin sites), innerslot-0 leg -/

/-- OLD-pin transport sites with inner slot 0 are guarded UNCONDITIONALLY (no
coherence, no band edge): the height does not move (`htH (i+2) = htH (i+1)` at
`m = 0`) and the floor only grows.  The `m ≥ 1` old-pin case reduces by the §2
cancellation to the band-edge condition — the line-dominance residue recorded in the
header (HK-30/HK-31 geometry; (SAE) closes it at 2-node histories). -/
theorem step_floor_guard_of_old_pin {H : History p F}
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) (c : Coord)
    (hold : ((H.htH (i+1) c : ℚ) : WithBot ℚ) ≤ H.floorH (i+1) c.2)
    (hm : H.innerslotH (i+1) c.2 = 0) :
    ((H.htH (i+2) c : ℚ) : WithBot ℚ) ≤ H.floorH (i+2) c.2 := by
  have hfl : H.floorH (i+2) c.2
      = max (H.floorH (i+1) c.2) ((H.nodes[i+1]'hi1).staircase c.2) :=
    C2_floorH_succ H (i+1) hi1 c.2
  have heq : H.htH (i+2) c = H.htH (i+1) c := by
    have hrec : H.htH (i+2) c
        = H.htH (i+1) c + (H.innerslotH (i+1) c.2 : ℚ) * H.kappaH (i+1) :=
      htH_succ H (i+1) c
    rw [hrec, hm]
    push_cast
    ring
  rw [hfl, heq]
  exact le_trans hold (le_max_left _ _)

end HK37

-- Axiom audit: Lean core only ({propext, Classical.choice, Quot.sound}).
#print axioms HK37.step_floor_guard
#print axioms HK37.theta_norm_blocks_band
#print axioms HK37.theta_norm_blocks_stripSet
#print axioms HK37.step_floor_guard_of_old_pin

end LeanUrat.MovesJ
