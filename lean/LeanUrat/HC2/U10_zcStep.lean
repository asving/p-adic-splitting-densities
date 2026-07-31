/-
Unit U10.zc_step  (HC-2 campaign, E-phase — blueprint §5 Layer B: THE HARD CORE OF THE
HARD CORE; the pre-declared escalation-risk center)
moves_ref: §C C.1.5 (per-step conditional exactness): "(1) multiplies the mass by exactly
vol_nom(E_fresh(ν_{i+1})); (2) re-establishes (ZC)".
deps: U3–U7, S (zcSeed, Theta_uni, pres_block), C0.pinTransport, C2.freshFree, C3.lineDom,
hreal (per-step `TransitionAdmissible` via `Realizable`).  difficulty: HARD ×4.
PRE-SPLIT (mandatory, blueprint): U10a floor-monotone downset transport; U10b fresh-cut
downset exactness; U10c interior zeros; U10d rim-lead placement/confinement. The E-phase
renderings below are the elaborator's best-faith decomposition (flagged in MANIFEST;
prover refinement authorized). Whatever step resists derivation is a candidate zcSeed law
(D5's fence) — via the stuck rule, NEVER a silent axiom.
hypothesis_fields: S.zcSeed, hreal.

PROVER RECORD (2026-07-31, hc2-p-phase-hard round): U10a and U10b are PROVED, ih-free
(statements byte-unchanged).  The engine is the file-private kernel below, implementing
the HK-29 stall-record geometry (F3 rim chain / F4-collapsed grid dominance via the
PROVED `C3_lineDom` / F5 floor window-constancy) in five pieces:
* `pin_src` — pin PROVENANCE: every pin of `mkSigma m` traces down the choice chain to a
  fresh-clause cut of some read `k < m` (fallback branches keep pins; `Σ₀` has none);
* `bridge_ht` — THE GENERAL-STEP FLOOR BRIDGE (replaces U9a's root-specific `STR₀ = 1`,
  `Dwidth = 1` collapse): a read-`k` band upper edge `htH k ≤ slotVal_k(fineSlot_k)`
  transports to `htH (M+1) ≤ staircase_M` for ANY `k ≤ M` with the coordinate interior
  to node `M`'s factor interior.  Mechanism: `κ_r = slope_r·D_r` (coherence slope law),
  the ℕ edge TELESCOPE `(b/D_k)·D_k = (b/cW_M)·cW_M + Σ_{r∈[k,M]} islot_r·D_r` (width
  chain `D_{r+1} = cW_r`), slope monotonicity (`C3_steeperChain`), and line dominance at
  the k-edge (`C3_lineDom`);
* `bridge_rev` — the single-step bridge run BACKWARDS (the reduction is by equalities);
* `floorH_collapse` — F5: on node `M`'s factor interior the cumulative floor IS node
  `M`'s staircase (every earlier staircase is dominated via `C3_lineDom` + left-edge
  comparison on the divisibility-chained grids), hence WINDOW-CONSTANT on fine slots;
* `rim_step` — F3: `μ_{m+1}·cW_{m+1} ≤ μ_m·cW_m` (`C3_widthConfine` + coherence
  containment + width chain).
U10a = provenance + bridge at `M := i+1`.  U10b = the ordinary induction
`downset_pinned` (base = the PROVED U9b `zc_root_downset_mpr`): at each step the
at-or-below-floor coordinate either was already at-or-below the PREVIOUS floor (IH +
rim chain + pin persistence) or is strictly fresh (case B), where the reverse bridge
puts it in the read's band and the strip/value dichotomy covers it — the VALUE roster's
whole-level-set band condition is discharged by `floorH_collapse` (floor
window-constancy makes every level-set sibling inherit the witness's band membership;
the U4 `levelSet_no_straddle` sorry is NOT consumed).  `freshAttach_exists`'s
`hunpinned` leg is discharged ih-free: an old pin under a read-(m+1) fresh support
would sit at-or-below `floorH (m+1)` (provenance + bridge) yet strictly above it (U3
band) — absurd.
U10c and `zc_step`: STOP UPHELD, see the records at their sorries.  U10d: NEW
BLOCKED-SUSPECT-FALSE record at its sorry (over-quantification: OLD pins persist beyond
the shrinking rim).

QUEUE ITEM 17 EXECUTED (2026-07-31, Asvin sign-off on the consolidated queue; this
round): THE UNIT IS NOW SORRY-FREE.
* U10d `zc_step_confine` RESTATED to the adjudicated fresh-cut restriction (the §C rim
  rule confines FRESH cuts only) and PROVED from U3's `mkFresh_band`; the old ∀-pins
  form's compiled negation witness is `U10d_negWitness.lean` (leaf intact, M1 note
  appended there).
* U10c `zc_step_interiorZero` PROVED: the NEW `ZCSeedLaws.step_shape` law (the Q8-class
  D5-fence designer addendum, HC2/Defs — root_shape's all-reads generalization)
  excludes interior value pins; strip pins close by spec clause (3) + `theta_norm` at
  the bridge bound; OLD pins close by the recorded ih-threading (statement gains the
  `ih : ZCData …` row that `zc_step` already carries) + spec clause (4) + `theta_norm`.
* `zc_step` PROVED (statement byte-unchanged): downset_exact mp = provenance + bridge
  at pins of `Σ_{i+2}`, mpr = `zc_step_freshExact`, interior_zero = U10c.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedZC
import LeanUrat.HC2.U3_freshBand
import LeanUrat.HC2.U7_sigmaRec
import LeanUrat.HC2.U9_zcRoot
import LeanUrat.MovesC.C2_floorH_succ
import LeanUrat.MovesC.C2_floorH_root
import LeanUrat.MovesC.C3_lineDom
import LeanUrat.MovesC.C3_steeperChain
import LeanUrat.MovesC.C3_widthConfine

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedZC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### The shared (ZC)-step kernel (file-private; see the PROVER RECORD in the header).

Numeric conventions (all from `MovesC/Defs`): `Line.at b = intercept − slope·b`
(descending, `slope > 0` from the coherence slope law); `staircase_M b` = the line at
the LEFT EDGE of `b`'s `childWidth`-block on the factor interior, `⊥` outside;
`slotVal_M (fineSlot_M b)` = the line at the left edge of `b`'s `Dwidth`-block;
`htH (i+1) c = htH i c + islot_i(c.2)·κ_i` with `κ_r = h_r/(e_r·STR_r) = slope_r·D_r`. -/

private lemma strFrame_pos (H : History p F) (r : ℕ) : 0 < H.strFrame r := by
  unfold History.strFrame
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  rw [List.mem_map] at h0
  obtain ⟨ν, hν, hν0⟩ := h0
  have := ν.he
  omega

private lemma Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) {r : ℕ}
    (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).Dwidth := by
  rw [Nat.pos_iff_ne_zero]
  intro hD0
  have hslope := hcoh.2.1 r hr
  rw [hD0] at hslope
  simp only [Nat.cast_zero, mul_zero] at hslope
  have hh := (H.nodes[r]'hr).hh
  have h1 : ((H.nodes[r]'hr).h : ℚ) = 0 := hslope.symm
  have h2 : (H.nodes[r]'hr).h = 0 := by exact_mod_cast h1
  omega

private lemma slope_pos {H : History p F} (hcoh : HistoryCoherent H) {r : ℕ}
    (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).line.slope := by
  have hslope := hcoh.2.1 r hr
  have h1 : (0:ℚ) < ((H.nodes[r]'hr).e : ℚ) := by exact_mod_cast (H.nodes[r]'hr).he
  have h2 : (0:ℚ) < ((H.strFrame r : ℕ) : ℚ) := by exact_mod_cast strFrame_pos H r
  have h3 : (0:ℚ) < ((H.nodes[r]'hr).Dwidth : ℚ) := by exact_mod_cast Dwidth_pos hcoh hr
  have h4 : (0:ℚ) < ((H.nodes[r]'hr).h : ℚ) := by exact_mod_cast (H.nodes[r]'hr).hh
  by_contra hns
  rw [not_lt] at hns
  have hX : (0:ℚ) < ((H.nodes[r]'hr).e : ℚ) * ((H.strFrame r : ℕ) : ℚ)
      * ((H.nodes[r]'hr).Dwidth : ℚ) := mul_pos (mul_pos h1 h2) h3
  have h5 := mul_le_mul_of_nonneg_right hns (le_of_lt hX)
  rw [zero_mul, hslope] at h5
  linarith

private lemma kappa_eq_slope_mul {H : History p F} (hcoh : HistoryCoherent H) {r : ℕ}
    (hr : r < H.nodes.length) :
    H.kappaH r = (H.nodes[r]'hr).line.slope * ((H.nodes[r]'hr).Dwidth : ℚ) := by
  have hnode : H.nodes[r]? = some (H.nodes[r]'hr) := List.getElem?_eq_getElem hr
  have hk : H.kappaH r = ((H.nodes[r]'hr).h : ℚ)
      / (((H.nodes[r]'hr).e : ℚ) * ((H.strFrame r : ℕ) : ℚ)) := by
    unfold History.kappaH
    rw [hnode]
    rfl
  have hslope := hcoh.2.1 r hr
  have h1 : ((H.nodes[r]'hr).e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    have := (H.nodes[r]'hr).he; omega)
  have h2 : ((H.strFrame r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    have := strFrame_pos H r; omega)
  rw [hk, ← hslope]
  field_simp

private lemma kappaH_nonneg (H : History p F) (r : ℕ) : 0 ≤ H.kappaH r := by
  unfold History.kappaH
  cases hnode : H.nodes[r]? with
  | none => exact le_refl 0
  | some ν =>
      show (0:ℚ) ≤ (ν.h : ℚ) / ((ν.e : ℚ) * ((H.strFrame r : ℕ) : ℚ))
      positivity

private lemma htH_le_succ (H : History p F) (c : Coord) (i : ℕ) :
    H.htH i c ≤ H.htH (i+1) c := by
  unfold History.htH
  rw [Finset.sum_range_succ]
  have h1 : 0 ≤ (H.innerslotH i c.2 : ℚ) * H.kappaH i :=
    mul_nonneg (Nat.cast_nonneg _) (kappaH_nonneg H i)
  linarith

private lemma innerslot_eq {H : History p F} {r : ℕ} (hr : r < H.nodes.length) (b : ℕ) :
    H.innerslotH r b
      = b % (H.nodes[r]'hr).childWidth / (H.nodes[r]'hr).Dwidth := by
  unfold History.innerslotH
  rw [List.getElem?_eq_getElem hr]
  rfl

private lemma dwOpt_eq {H : History p F} {r : ℕ} (hr : r < H.nodes.length) :
    (H.nodes[r]?).elim 0 Node.Dwidth = (H.nodes[r]'hr).Dwidth := by
  rw [List.getElem?_eq_getElem hr]
  rfl

/-- Single-block split: for `D ∣ cw`, the fine `D`-edge decomposes as the coarse
`cw`-edge plus the inner-slot offset (the one-step edge telescope, ℕ). -/
private lemma div_block_split (b D cw : ℕ) (hD : 0 < D) (hdvd : D ∣ cw) :
    b / D * D = b / cw * cw + b % cw / D * D := by
  obtain ⟨q, rfl⟩ := hdvd
  have h1 : b % (D * q) + b / (D * q) * (D * q) = b := Nat.mod_add_div' b (D * q)
  have h2 : b / D = b % (D * q) / D + b / (D * q) * q := by
    conv_lhs => rw [← h1]
    rw [show b / (D * q) * (D * q) = b / (D * q) * q * D by ring]
    rw [Nat.add_mul_div_right _ _ hD]
  rw [h2]
  ring

/-- The coarse block's left edge sits at-or-left of the fine block's left edge. -/
private lemma div_mul_le_div_mul {d D : ℕ} (hdvd : d ∣ D) (hd : 0 < d) (b : ℕ) :
    b / D * D ≤ b / d * d := by
  obtain ⟨q, rfl⟩ := hdvd
  rw [show b / (d * q) * (d * q) = b / (d * q) * q * d by ring]
  apply mul_le_mul_right'
  rw [Nat.le_div_iff_mul_le hd]
  calc b / (d * q) * q * d = b / (d * q) * (d * q) := by ring
    _ ≤ b := Nat.div_mul_le_self _ _

private lemma dwidth_dvd_chain {H : History p F} (hcoh : HistoryCoherent H) {s : ℕ}
    (hs : s < H.nodes.length) :
    ∀ t, s ≤ t → ∀ (ht : t < H.nodes.length),
      (H.nodes[s]'hs).Dwidth ∣ (H.nodes[t]'ht).Dwidth := by
  intro t
  induction t with
  | zero =>
      intro hst h0
      have hs0 : s = 0 := by omega
      subst hs0
      exact dvd_refl _
  | succ t iht =>
      intro hst ht1
      by_cases hst' : s ≤ t
      · have ht : t < H.nodes.length := by omega
        have hF : (H.nodes[t+1]'ht1).Dwidth = (H.nodes[t]'(by omega)).childWidth :=
          (hcoh.2.2.2 t ht1).2.2.2.2.2.1
        rw [hF]
        refine dvd_trans (iht hst' ht) ?_
        show (H.nodes[t]'ht).Dwidth ∣ (H.nodes[t]'(by omega)).childWidth
        unfold Node.childWidth
        exact dvd_mul_left _ _
      · have hst'' : s = t + 1 := by omega
        subst hst''
        exact dvd_refl _

private lemma childWidth_dvd_chain {H : History p F} (hcoh : HistoryCoherent H) {r M : ℕ}
    (hrl : r < H.nodes.length) (hrM : r ≤ M) (hM : M < H.nodes.length) :
    (H.nodes[r]'hrl).childWidth ∣ (H.nodes[M]'hM).childWidth := by
  rcases eq_or_lt_of_le hrM with heq | hlt
  · subst heq
    exact dvd_refl _
  · have hr1 : r + 1 < H.nodes.length := by omega
    have hcw : (H.nodes[r]'hrl).childWidth = (H.nodes[r+1]'hr1).Dwidth := by
      have hF : (H.nodes[r+1]'hr1).Dwidth = (H.nodes[r]'(by omega)).childWidth :=
        (hcoh.2.2.2 r hr1).2.2.2.2.2.1
      exact hF.symm
    rw [hcw]
    refine dvd_trans (dwidth_dvd_chain hcoh hr1 M hlt hM) ?_
    unfold Node.childWidth
    exact dvd_mul_left _ _

private lemma childWidth_pos {H : History p F} (hcoh : HistoryCoherent H) {r : ℕ}
    (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).childWidth := by
  unfold Node.childWidth
  have h1 := (H.nodes[r]'hr).he
  have h2 := (H.nodes[r]'hr).hg
  have h3 := Dwidth_pos hcoh hr
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) h3

private lemma prevRim_succ {H : History p F} (n : ℕ) {m : ℕ} (hm : m < H.nodes.length) :
    H.prevRim n (m+1) = (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by
  show (H.nodes[m]?).elim n (fun ν => ν.μ * ν.childWidth) = _
  rw [List.getElem?_eq_getElem hm]
  rfl

/-- F3 (rim chain, one step): the factor-interior rim shrinks along the history —
`C3_widthConfine` (`μ·cW ≤ wSide·D`, pure node laws) + coherence containment
(`s0+wSide ≤ μ_parent`) + the width chain (`D_child = cW_parent`). -/
private lemma rim_step {H : History p F} (hcoh : HistoryCoherent H) {m : ℕ}
    (hm1 : m + 1 < H.nodes.length) :
    (H.nodes[m+1]'hm1).μ * (H.nodes[m+1]'hm1).childWidth
      ≤ (H.nodes[m]'(by omega)).μ * (H.nodes[m]'(by omega)).childWidth := by
  have h1 := C3_widthConfine (H.nodes[m+1]'hm1)
  have hE : (H.nodes[m+1]'hm1).s0 + (H.nodes[m+1]'hm1).wSide
      ≤ (H.nodes[m]'(by omega : m < H.nodes.length)).μ :=
    (hcoh.2.2.2 m hm1).2.2.2.2.1
  have hF : (H.nodes[m+1]'hm1).Dwidth
      = (H.nodes[m]'(by omega : m < H.nodes.length)).childWidth :=
    (hcoh.2.2.2 m hm1).2.2.2.2.2.1
  calc (H.nodes[m+1]'hm1).μ * (H.nodes[m+1]'hm1).childWidth
      ≤ (H.nodes[m+1]'hm1).wSide * (H.nodes[m+1]'hm1).Dwidth := h1
    _ ≤ (H.nodes[m]'(by omega)).μ * (H.nodes[m]'(by omega)).childWidth := by
        rw [hF]
        exact mul_le_mul_right' (by omega) _

private lemma htH_split (H : History p F) (c : Coord) {k M : ℕ} (hk : k ≤ M + 1) :
    H.htH (M+1) c
      = H.htH k c + ∑ r ∈ Finset.Ico k (M+1), (H.innerslotH r c.2 : ℚ) * H.kappaH r := by
  have h1 := Finset.sum_Ico_consecutive
    (fun r => (H.innerslotH r c.2 : ℚ) * H.kappaH r) (Nat.zero_le k) hk
  unfold History.htH
  simp only [Finset.range_eq_Ico]
  linarith [h1]

/-- The ℕ EDGE TELESCOPE: the read-`k` fine edge = the node-`M` coarse edge plus the
accumulated inner-slot offsets, along the coherence width chain `D_{r+1} = cW_r`. -/
private lemma edge_telescope {H : History p F} (hcoh : HistoryCoherent H) (b : ℕ) {k : ℕ}
    (hkl : k < H.nodes.length) :
    ∀ M, k ≤ M → ∀ (hM : M < H.nodes.length),
      b / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth
        = b / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth
          + ∑ r ∈ Finset.Ico k (M+1),
              H.innerslotH r b * (H.nodes[r]?).elim 0 Node.Dwidth := by
  intro M
  induction M with
  | zero =>
      intro hk0 h0
      have hk : k = 0 := by omega
      subst hk
      rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
      rw [innerslot_eq h0 b, dwOpt_eq h0]
      exact div_block_split b _ _ (Dwidth_pos hcoh h0)
        ⟨(H.nodes[0]'h0).e * (H.nodes[0]'h0).g, by unfold Node.childWidth; ring⟩
  | succ M ihM =>
      intro hkM1 hM1
      by_cases hkM : k ≤ M
      · have hM : M < H.nodes.length := by omega
        rw [Finset.sum_Ico_succ_top (by omega : k ≤ M + 1)]
        rw [ihM hkM hM]
        have hF : (H.nodes[M+1]'hM1).Dwidth = (H.nodes[M]'(by omega)).childWidth :=
          (hcoh.2.2.2 M hM1).2.2.2.2.2.1
        rw [innerslot_eq hM1 b, dwOpt_eq hM1]
        have hsingle := div_block_split b (H.nodes[M+1]'hM1).Dwidth
          (H.nodes[M+1]'hM1).childWidth (Dwidth_pos hcoh hM1)
          ⟨(H.nodes[M+1]'hM1).e * (H.nodes[M+1]'hM1).g, by unfold Node.childWidth; ring⟩
        have hlift : b / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth
            = b / (H.nodes[M+1]'hM1).Dwidth * (H.nodes[M+1]'hM1).Dwidth := by
          rw [hF]
        rw [hlift, hsingle]
        ring
      · have hk : k = M + 1 := by omega
        subst hk
        rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
        rw [innerslot_eq hM1 b, dwOpt_eq hM1]
        exact div_block_split b _ _ (Dwidth_pos hcoh hM1)
          ⟨(H.nodes[M+1]'hM1).e * (H.nodes[M+1]'hM1).g, by unfold Node.childWidth; ring⟩

/-- THE GENERAL-STEP FLOOR BRIDGE: a read-`k` band upper edge transports to the node-`M`
staircase at frame-`(M+1)` heights, for any `k ≤ M` and any coordinate interior to node
`M`'s factor interior.  (At `k = M` this is the forward single-step bridge; U9a's root
bridge is the `k = M = 0` instance.) -/
private lemma bridge_ht {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    {k M : ℕ} (hkl : k < H.nodes.length) (hkM : k ≤ M) (hM : M < H.nodes.length)
    (c : Coord) (hb : c.2 < (H.nodes[M]'hM).μ * (H.nodes[M]'hM).childWidth)
    (hedge : H.htH k c ≤ (H.nodes[k]'hkl).slotVal ((H.nodes[k]'hkl).fineSlot c.2)) :
    ((H.htH (M+1) c : ℚ) : WithBot ℚ) ≤ (H.nodes[M]'hM).staircase c.2 := by
  unfold Node.staircase
  rw [if_pos hb, WithBot.coe_le_coe]
  have hsplit := htH_split H c (show k ≤ M + 1 by omega)
  have htel := edge_telescope hcoh c.2 hkl M hkM hM
  have hterm : ∀ r ∈ Finset.Ico k (M+1),
      (H.innerslotH r c.2 : ℚ) * H.kappaH r
        ≤ (H.nodes[M]'hM).line.slope
            * ((H.innerslotH r c.2 * (H.nodes[r]?).elim 0 Node.Dwidth : ℕ) : ℚ) := by
    intro r hr
    obtain ⟨hkr, hrM1⟩ := Finset.mem_Ico.mp hr
    have hrl : r < H.nodes.length := by omega
    rw [kappa_eq_slope_mul hcoh hrl, dwOpt_eq hrl]
    push_cast
    have hsl : (H.nodes[r]'hrl).line.slope ≤ (H.nodes[M]'hM).line.slope := by
      rcases Nat.lt_or_ge r M with hlt | hge
      · exact le_of_lt (C3_steeperChain H hcoh r M hM hlt)
      · have hrM : r = M := by omega
        subst hrM
        exact le_refl _
    have hnn : (0:ℚ) ≤ (H.innerslotH r c.2 : ℚ) * ((H.nodes[r]'hrl).Dwidth : ℚ) := by
      positivity
    calc (H.innerslotH r c.2 : ℚ)
          * ((H.nodes[r]'hrl).line.slope * ((H.nodes[r]'hrl).Dwidth : ℚ))
        = (H.nodes[r]'hrl).line.slope
            * ((H.innerslotH r c.2 : ℚ) * ((H.nodes[r]'hrl).Dwidth : ℚ)) := by ring
      _ ≤ (H.nodes[M]'hM).line.slope
            * ((H.innerslotH r c.2 : ℚ) * ((H.nodes[r]'hrl).Dwidth : ℚ)) :=
          mul_le_mul_of_nonneg_right hsl hnn
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  rw [show (∑ r ∈ Finset.Ico k (M+1),
        ((H.innerslotH r c.2 * (H.nodes[r]?).elim 0 Node.Dwidth : ℕ) : ℚ))
      = ((∑ r ∈ Finset.Ico k (M+1),
          H.innerslotH r c.2 * (H.nodes[r]?).elim 0 Node.Dwidth : ℕ) : ℚ)
    from (Nat.cast_sum _ _).symm] at hsum
  have hdom' : (H.nodes[k]'hkl).line.at
        (c.2 / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth)
      ≤ (H.nodes[M]'hM).line.at
        (c.2 / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth) :=
    C3_lineDom H hcoh hreal M hM k hkM _ (lt_of_le_of_lt (Nat.div_mul_le_self _ _) hb)
  have hedge' : H.htH k c ≤ (H.nodes[k]'hkl).line.at
      (c.2 / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth) := hedge
  have hcast : ((c.2 / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth : ℕ) : ℚ)
      = ((c.2 / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth : ℕ) : ℚ)
        + ((∑ r ∈ Finset.Ico k (M+1),
            H.innerslotH r c.2 * (H.nodes[r]?).elim 0 Node.Dwidth : ℕ) : ℚ) := by
    exact_mod_cast htel
  have hexp : (H.nodes[M]'hM).line.slope
        * ((c.2 / (H.nodes[k]'hkl).Dwidth * (H.nodes[k]'hkl).Dwidth : ℕ) : ℚ)
      = (H.nodes[M]'hM).line.slope
          * ((c.2 / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth : ℕ) : ℚ)
        + (H.nodes[M]'hM).line.slope
          * ((∑ r ∈ Finset.Ico k (M+1),
              H.innerslotH r c.2 * (H.nodes[r]?).elim 0 Node.Dwidth : ℕ) : ℚ) := by
    rw [hcast]; ring
  rw [hsplit]
  unfold Line.at at hedge' hdom' ⊢
  linarith [hsum, hdom', hedge', hexp]

/-- The single-step bridge run BACKWARDS (the reduction is by exact equalities):
below-staircase at frame `M+1` forces the band's upper-edge bound at frame `M`. -/
private lemma bridge_rev {H : History p F} (hcoh : HistoryCoherent H) {M : ℕ}
    (hM : M < H.nodes.length) (c : Coord)
    (hb : c.2 < (H.nodes[M]'hM).μ * (H.nodes[M]'hM).childWidth)
    (hst : ((H.htH (M+1) c : ℚ) : WithBot ℚ) ≤ (H.nodes[M]'hM).staircase c.2) :
    H.htH M c ≤ (H.nodes[M]'hM).slotVal ((H.nodes[M]'hM).fineSlot c.2) := by
  unfold Node.staircase at hst
  rw [if_pos hb, WithBot.coe_le_coe] at hst
  have hsucc : H.htH (M+1) c = H.htH M c + (H.innerslotH M c.2 : ℚ) * H.kappaH M := by
    unfold History.htH
    rw [Finset.sum_range_succ]
    ring
  have hblock := div_block_split c.2 (H.nodes[M]'hM).Dwidth (H.nodes[M]'hM).childWidth
    (Dwidth_pos hcoh hM)
    ⟨(H.nodes[M]'hM).e * (H.nodes[M]'hM).g, by unfold Node.childWidth; ring⟩
  have hcast : ((c.2 / (H.nodes[M]'hM).Dwidth * (H.nodes[M]'hM).Dwidth : ℕ) : ℚ)
      = ((c.2 / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth : ℕ) : ℚ)
        + ((c.2 % (H.nodes[M]'hM).childWidth / (H.nodes[M]'hM).Dwidth
            * (H.nodes[M]'hM).Dwidth : ℕ) : ℚ) := by
    exact_mod_cast hblock
  have hterm : (H.innerslotH M c.2 : ℚ) * H.kappaH M
      = (H.nodes[M]'hM).line.slope
        * ((c.2 % (H.nodes[M]'hM).childWidth / (H.nodes[M]'hM).Dwidth
            * (H.nodes[M]'hM).Dwidth : ℕ) : ℚ) := by
    rw [kappa_eq_slope_mul hcoh hM, innerslot_eq hM c.2]
    push_cast
    ring
  show H.htH M c ≤ (H.nodes[M]'hM).line.at
      (c.2 / (H.nodes[M]'hM).Dwidth * (H.nodes[M]'hM).Dwidth)
  rw [hsucc] at hst
  have hexp : (H.nodes[M]'hM).line.slope
        * ((c.2 / (H.nodes[M]'hM).Dwidth * (H.nodes[M]'hM).Dwidth : ℕ) : ℚ)
      = (H.nodes[M]'hM).line.slope
          * ((c.2 / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth : ℕ) : ℚ)
        + (H.nodes[M]'hM).line.slope
          * ((c.2 % (H.nodes[M]'hM).childWidth / (H.nodes[M]'hM).Dwidth
              * (H.nodes[M]'hM).Dwidth : ℕ) : ℚ) := by
    rw [hcast]; ring
  unfold Line.at at hst ⊢
  linarith [hst, hterm, hexp]

/-- Staircase dominance on the LAST factor interior: every earlier staircase sits
at-or-below node `M`'s (via `C3_lineDom` at the fine edge + the descending line at the
coarser edge on the divisibility-chained grids). -/
private lemma staircase_mono {H : History p F} (hcoh : HistoryCoherent H)
    (hreal : Realizable H) {r M : ℕ} (hrl : r < H.nodes.length) (hrM : r ≤ M)
    (hM : M < H.nodes.length) {b : ℕ}
    (hb : b < (H.nodes[M]'hM).μ * (H.nodes[M]'hM).childWidth) :
    (H.nodes[r]'hrl).staircase b ≤ (H.nodes[M]'hM).staircase b := by
  unfold Node.staircase
  by_cases hbr : b < (H.nodes[r]'hrl).μ * (H.nodes[r]'hrl).childWidth
  · rw [if_pos hbr, if_pos hb, WithBot.coe_le_coe]
    have h1 : (H.nodes[r]'hrl).line.at
          (b / (H.nodes[r]'hrl).childWidth * (H.nodes[r]'hrl).childWidth)
        ≤ (H.nodes[M]'hM).line.at
          (b / (H.nodes[r]'hrl).childWidth * (H.nodes[r]'hrl).childWidth) :=
      C3_lineDom H hcoh hreal M hM r hrM _ (lt_of_le_of_lt (Nat.div_mul_le_self _ _) hb)
    have h2 : b / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth
        ≤ b / (H.nodes[r]'hrl).childWidth * (H.nodes[r]'hrl).childWidth :=
      div_mul_le_div_mul (childWidth_dvd_chain hcoh hrl hrM hM)
        (childWidth_pos hcoh hrl) b
    have h3 : (H.nodes[M]'hM).line.at
          (b / (H.nodes[r]'hrl).childWidth * (H.nodes[r]'hrl).childWidth)
        ≤ (H.nodes[M]'hM).line.at
          (b / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth) := by
      unfold Line.at
      have h4 : ((b / (H.nodes[M]'hM).childWidth * (H.nodes[M]'hM).childWidth : ℕ) : ℚ)
          ≤ ((b / (H.nodes[r]'hrl).childWidth * (H.nodes[r]'hrl).childWidth : ℕ) : ℚ) := by
        exact_mod_cast h2
      have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt (slope_pos hcoh hM))
      linarith
    exact le_trans h1 h3
  · rw [if_neg hbr]
    exact bot_le

private lemma floorH_le {H : History p F} {b : ℕ} {x : WithBot ℚ} :
    ∀ i, i ≤ H.nodes.length →
      (∀ r, r < i → ∀ (hrl : r < H.nodes.length), (H.nodes[r]'hrl).staircase b ≤ x) →
      H.floorH i b ≤ x := by
  intro i
  induction i with
  | zero =>
      intro _ _
      rw [C2_floorH_root]
      exact bot_le
  | succ i ih =>
      intro hi1 hall
      have hi : i < H.nodes.length := by omega
      rw [C2_floorH_succ H i hi b]
      exact max_le (ih (by omega) (fun r hr hrl => hall r (by omega) hrl))
        (hall i (by omega) hi)

/-- F5 (floor collapse): on node `M`'s factor interior the cumulative floor IS node
`M`'s staircase — hence WINDOW-CONSTANT on each frame-`(M+1)` fine slot (the staircase
is a left-edge evaluation on aligned `cW_M`-blocks). -/
private lemma floorH_collapse {H : History p F} (hcoh : HistoryCoherent H)
    (hreal : Realizable H) {M : ℕ} (hM : M < H.nodes.length) {b : ℕ}
    (hb : b < (H.nodes[M]'hM).μ * (H.nodes[M]'hM).childWidth) :
    H.floorH (M+1) b = (H.nodes[M]'hM).staircase b := by
  refine le_antisymm ?_ ?_
  · exact floorH_le (M+1) (by omega)
      (fun r hr hrl => staircase_mono hcoh hreal hrl (by omega) hM hb)
  · rw [C2_floorH_succ H M hM b]
    exact le_max_right _ _

/-- Pin PROVENANCE: every pin of the state chain traces down the choice chain to a
fresh-clause cut of some earlier read (`Σ₀` has no pins; the no-witness and
beyond-history branches keep pins). -/
private lemma pin_src {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) :
    ∀ (m : ℕ) (c : Fin (n * N)), (mkSigma H n N S vOf m).pinned c = true →
      ∃ (k : ℕ) (hk : k < H.nodes.length), k < m ∧
        ∃ cl ∈ (mkFresh H n N S vOf k hk).clauses, c ∈ cl.support := by
  intro m
  induction m with
  | zero =>
      intro c hc
      rw [show (mkSigma H n N S vOf 0).pinned c = false from rfl] at hc
      exact Bool.noConfusion hc
  | succ m ih =>
      intro c hc
      by_cases hm : m < H.nodes.length
      · have hsig : mkSigma H n N S vOf (m+1)
            = pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m)
                (mkFresh H n N S vOf m hm) := by
          show (if hi : m < H.nodes.length then
              pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m)
                (mkFresh H n N S vOf m hi)
            else mkSigma H n N S vOf m) = _
          rw [dif_pos hm]
        rw [hsig] at hc
        by_cases hEx : ∃ D' : Locus p (n * N),
            IsFreshAttach (mkSigma H n N S vOf m) (S.Theta m)
              (mkFresh H n N S vOf m hm) D'
        · have spec := pinTransportSystem_spec (mkSigma H n N S vOf m) (S.Theta m)
            (mkFresh H n N S vOf m hm) hEx
          rcases (spec.2.1 c).mp hc with hold | hfresh
          · obtain ⟨k, hk, hkm, hcl⟩ := ih c hold
            exact ⟨k, hk, by omega, hcl⟩
          · exact ⟨m, hm, by omega, hfresh⟩
        · unfold pinTransportSystem at hc
          rw [dif_neg hEx] at hc
          obtain ⟨k, hk, hkm, hcl⟩ := ih c hc
          exact ⟨k, hk, by omega, hcl⟩
      · have hsig : mkSigma H n N S vOf (m+1) = mkSigma H n N S vOf m := by
          show (if hi : m < H.nodes.length then
              pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m)
                (mkFresh H n N S vOf m hi)
            else mkSigma H n N S vOf m) = _
          rw [dif_neg hm]
        rw [hsig] at hc
        obtain ⟨k, hk, hkm, hcl⟩ := ih c hc
        exact ⟨k, hk, by omega, hcl⟩

/-- The value clause's support IS its slot's level set (`C1_TYP_toClause`'s support law;
file-private replica of U9's — the two `choose`s agree by proof irrelevance). -/
private lemma valueClause_support' {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    (valueClause H n N S vOf i hi j hsp).support = levelSet H n N i (H.nodes[i]'hi) j := by
  classical
  have hcard : Nat.card (Fin (levelSet H n N i (H.nodes[i]'hi) j).card → ZMod p)
      = p ^ (levelSet H n N i (H.nodes[i]'hi) j).card := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    simp [Nat.card_eq_fintype_card, ZMod.card]
  exact (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro
        (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card
    hcard).choose_spec.1

/-- THE CUMULATIVE ⊇ (U10b's engine, ordinary induction on the read index; base = the
PROVED U9b): after read `m`, every coordinate interior to node `m`'s factor interior
sitting at-or-below the new floor is pinned. -/
private theorem downset_pinned {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N) :
    ∀ (m : ℕ) (hm : m < H.nodes.length) (j : Fin (n * N)),
      (boxChart n N j).2 < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth →
      ((H.htH (m+1) (boxChart n N j) : ℚ) : WithBot ℚ)
          ≤ H.floorH (m+1) (boxChart n N j).2 →
      (mkSigma H n N S vOf (m+1)).pinned j = true := by
  classical
  intro m
  induction m with
  | zero =>
      intro hm j hj hfloor
      exact zc_root_downset_mpr S vOf hcoh hreal hbox hN hm j hj hfloor
  | succ m ih =>
      intro hm1 j hj hfloor
      have hm : m < H.nodes.length := by omega
      have hjm : (boxChart n N j).2 < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth :=
        lt_of_lt_of_le hj (rim_step hcoh hm1)
      -- hunpinned at read m+1, ih-free: an old pin under a read-(m+1) fresh support
      -- would sit at-or-below floorH (m+1) (provenance + bridge) yet strictly above it
      -- (U3 band) — absurd.
      have hunp : ∀ c : Fin (n * N), (mkSigma H n N S vOf (m+1)).pinned c = true →
          ¬ ∃ cl ∈ (mkFresh H n N S vOf (m+1) hm1).clauses, c ∈ cl.support := by
        intro c hc hex
        obtain ⟨cl, hcl, hcs⟩ := hex
        have hband := mkFresh_band H n N S vOf (m+1) hm1 cl hcl c hcs
        obtain ⟨k, hk, hkm, cl', hcl', hcs'⟩ := pin_src S vOf (m+1) c hc
        have hedge := (mkFresh_band H n N S vOf k hk cl' hcl' c hcs').2.2
        have hrim : (boxChart n N c).2
            < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by
          have h1 := hband.1
          rwa [prevRim_succ n hm] at h1
        have hbr := bridge_ht hcoh hreal hk (by omega : k ≤ m) hm
          (boxChart n N c) hrim hedge
        have hfl : (H.nodes[m]'hm).staircase (boxChart n N c).2
            ≤ H.floorH (m+1) (boxChart n N c).2 := by
          rw [C2_floorH_succ H m hm]
          exact le_max_right _ _
        exact absurd (lt_of_lt_of_le hband.2.1 (le_trans hbr hfl)) (lt_irrefl _)
      have hasg : ∀ cl ∈ (mkFresh H n N S vOf (m+1) hm1).clauses,
          ∃ u : Fin (n * N) → ZMod p, ∀ x, cl.sat x ↔ ∀ c ∈ cl.support, x c = u c :=
        fun cl hcl => clause_assign cl (mkFresh_codim S vOf (m+1) hm1 cl hcl)
      have hEx : ∃ D' : Locus p (n * N),
          IsFreshAttach (mkSigma H n N S vOf (m+1)) (S.Theta (m+1))
            (mkFresh H n N S vOf (m+1) hm1) D' :=
        freshAttach_exists (mkSigma H n N S vOf (m+1)) (S.Theta_uni (m+1))
          (mkFresh H n N S vOf (m+1) hm1) hasg hunp
      have spec := pinTransportSystem_spec (mkSigma H n N S vOf (m+1)) (S.Theta (m+1))
        (mkFresh H n N S vOf (m+1) hm1) hEx
      have hsig : mkSigma H n N S vOf (m+2)
          = pinTransportSystem (mkSigma H n N S vOf (m+1)) (S.Theta (m+1))
              (mkFresh H n N S vOf (m+1) hm1) := by
        show (if hi : m+1 < H.nodes.length then
            pinTransportSystem (mkSigma H n N S vOf (m+1)) (S.Theta (m+1))
              (mkFresh H n N S vOf (m+1) hi)
          else mkSigma H n N S vOf (m+1)) = _
        rw [dif_pos hm1]
      rw [hsig]
      refine (spec.2.1 j).mpr ?_
      by_cases hA : ((H.htH (m+1) (boxChart n N j) : ℚ) : WithBot ℚ)
          ≤ H.floorH (m+1) (boxChart n N j).2
      · -- CASE A: already at-or-below the previous floor — pinned by the IH (rim
        -- chain shrinks the guard), and pins persist through the transport.
        exact Or.inl (ih hm j hjm hA)
      · -- CASE B: strictly fresh — the reverse bridge puts j in read (m+1)'s band;
        -- the strip/value dichotomy covers it by a fresh clause.
        refine Or.inr ?_
        have hlt : H.floorH (m+1) (boxChart n N j).2
            < ((H.htH (m+1) (boxChart n N j) : ℚ) : WithBot ℚ) := not_le.mp hA
        have hstair : ((H.htH (m+2) (boxChart n N j) : ℚ) : WithBot ℚ)
            ≤ (H.nodes[m+1]'hm1).staircase (boxChart n N j).2 := by
          rw [C2_floorH_succ H (m+1) hm1 (boxChart n N j).2] at hfloor
          rcases le_max_iff.mp hfloor with hcase | hcase
          · exfalso
            have hmono : ((H.htH (m+1) (boxChart n N j) : ℚ) : WithBot ℚ)
                ≤ ((H.htH (m+2) (boxChart n N j) : ℚ) : WithBot ℚ) := by
              rw [WithBot.coe_le_coe]
              exact htH_le_succ H (boxChart n N j) (m+1)
            exact absurd (le_trans hmono hcase) hA
          · exact hcase
        have hrev : H.htH (m+1) (boxChart n N j)
            ≤ (H.nodes[m+1]'hm1).slotVal
                ((H.nodes[m+1]'hm1).fineSlot (boxChart n N j).2) :=
          bridge_rev hcoh hm1 (boxChart n N j) hj hstair
        have hband : inFreshBand H n (boxChart n N) (m+1) (H.nodes[m+1]'hm1) j := by
          refine ⟨?_, hlt, hrev⟩
          rw [prevRim_succ n hm]
          exact hjm
        by_cases hv : IsValueCoord H (boxChart n N) (m+1) (H.nodes[m+1]'hm1) j
        · -- VALUE coordinate: the roster's whole-level-set band condition is
          -- discharged by F5 floor window-constancy (`floorH_collapse`): every
          -- sibling of the level set shares j's fine slot, hence j's rim bound,
          -- j's floor value, and the exact height — in-band with j.
          have hspan : (H.nodes[m+1]'hm1).spanSlot
              ((H.nodes[m+1]'hm1).fineSlot (boxChart n N j).2) := hv.1
          have hhtv : H.htH (m+1) (boxChart n N j)
              = (H.nodes[m+1]'hm1).slotVal
                  ((H.nodes[m+1]'hm1).fineSlot (boxChart n N j).2) := hv.2
          set j0 := (H.nodes[m+1]'hm1).fineSlot (boxChart n N j).2 with hj0def
          have hj_level : j ∈ levelSet H n N (m+1) (H.nodes[m+1]'hm1) j0 := by
            unfold levelSet
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ j, hj0def.symm, hhtv⟩
          have hDpos : 0 < (H.nodes[m+1]'hm1).Dwidth := Dwidth_pos hcoh hm1
          have hDcw : (H.nodes[m+1]'hm1).Dwidth = (H.nodes[m]'hm).childWidth :=
            (hcoh.2.2.2 m hm1).2.2.2.2.2.1
          have hj0b : (boxChart n N j).2 / (H.nodes[m+1]'hm1).Dwidth = j0 := by
            have h := hj0def
            simp only [Node.fineSlot] at h
            exact h.symm
          have hj0lt : j0 + 1 ≤ (H.nodes[m]'hm).μ := by
            have h1 : j0 * (H.nodes[m+1]'hm1).Dwidth ≤ (boxChart n N j).2 := by
              rw [← hj0b]
              exact Nat.div_mul_le_self _ _
            have h1' : j0 * (H.nodes[m]'hm).childWidth ≤ (boxChart n N j).2 := by
              rw [← hDcw]
              exact h1
            have h2 : j0 * (H.nodes[m]'hm).childWidth
                < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth :=
              lt_of_le_of_lt h1' hjm
            exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
          have hfloorj : H.floorH (m+1) (boxChart n N j).2
              = (H.nodes[m]'hm).staircase (boxChart n N j).2 :=
            floorH_collapse hcoh hreal hm hjm
          have hbcw : (boxChart n N j).2 / (H.nodes[m]'hm).childWidth = j0 := by
            rw [← hDcw]
            exact hj0b
          have hstj : (H.nodes[m]'hm).staircase (boxChart n N j).2
              = (((H.nodes[m]'hm).line.at (j0 * (H.nodes[m]'hm).childWidth) : ℚ)
                  : WithBot ℚ) := by
            unfold Node.staircase
            rw [if_pos hjm, hbcw]
          have hroster : ∀ c' ∈ levelSet H n N (m+1) (H.nodes[m+1]'hm1) j0,
              inFreshBand H n (boxChart n N) (m+1) (H.nodes[m+1]'hm1) c' := by
            intro c' hc'
            have hc'' := hc'
            unfold levelSet at hc''
            rw [Finset.mem_filter] at hc''
            obtain ⟨-, hfs', hht'⟩ := hc''
            have hfs'b : (boxChart n N c').2 / (H.nodes[m+1]'hm1).Dwidth = j0 := by
              have h := hfs'
              simp only [Node.fineSlot] at h
              exact h
            have hwin : (boxChart n N c').2 < (j0 + 1) * (H.nodes[m+1]'hm1).Dwidth := by
              have h3 : (H.nodes[m+1]'hm1).Dwidth
                    * ((boxChart n N c').2 / (H.nodes[m+1]'hm1).Dwidth)
                  + (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth
                  = (boxChart n N c').2 := Nat.div_add_mod _ _
              rw [hfs'b] at h3
              have h4 : (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth
                  < (H.nodes[m+1]'hm1).Dwidth := Nat.mod_lt _ hDpos
              calc (boxChart n N c').2
                  = (H.nodes[m+1]'hm1).Dwidth * j0
                    + (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth := h3.symm
                _ < (H.nodes[m+1]'hm1).Dwidth * j0 + (H.nodes[m+1]'hm1).Dwidth :=
                    Nat.add_lt_add_left h4 _
                _ = (j0 + 1) * (H.nodes[m+1]'hm1).Dwidth := by ring
            have hrim' : (boxChart n N c').2
                < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by
              calc (boxChart n N c').2 < (j0 + 1) * (H.nodes[m+1]'hm1).Dwidth := hwin
                _ ≤ (H.nodes[m]'hm).μ * (H.nodes[m+1]'hm1).Dwidth :=
                    mul_le_mul_right' hj0lt _
                _ = (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by rw [hDcw]
            have hbcw' : (boxChart n N c').2 / (H.nodes[m]'hm).childWidth = j0 := by
              rw [← hDcw]
              exact hfs'b
            have hfloor' : H.floorH (m+1) (boxChart n N c').2
                = (((H.nodes[m]'hm).line.at (j0 * (H.nodes[m]'hm).childWidth) : ℚ)
                    : WithBot ℚ) := by
              rw [floorH_collapse hcoh hreal hm hrim']
              unfold Node.staircase
              rw [if_pos hrim', hbcw']
            refine ⟨?_, ?_, ?_⟩
            · rw [prevRim_succ n hm]
              exact hrim'
            · rw [hfloor', hht']
              rw [hfloorj, hstj, hhtv] at hlt
              exact hlt
            · rw [hfs']
              exact le_of_eq hht'
          have hj0_val : j0 ∈ valueSlots H n N (m+1) (H.nodes[m+1]'hm1) := by
            unfold valueSlots
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨?_, hspan, ⟨j, hj_level⟩, hroster⟩
            have := hspan.2
            omega
          refine ⟨valueClause H n N S vOf (m+1) hm1 j0 (valueSlots_spanSlot hj0_val),
            ?_, ?_⟩
          · show valueClause H n N S vOf (m+1) hm1 j0 (valueSlots_spanSlot hj0_val)
                ∈ mkFreshClauses H n N S vOf (m+1) hm1
            unfold mkFreshClauses
            rw [List.mem_append]
            right
            rw [List.mem_map]
            exact ⟨⟨j0, hj0_val⟩,
              by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, rfl⟩
          · rw [valueClause_support' S vOf (m+1) hm1 j0 (valueSlots_spanSlot hj0_val)]
            exact hj_level
        · -- STRIP coordinate: covered by its own strip clause (the U9b pattern at
          -- read m+1).
          have hj_strip : j ∈ stripSet H n N (m+1) (H.nodes[m+1]'hm1) := by
            unfold stripSet
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ j, hband, hv⟩
          have hspec := (C1_stripClause (p := p) j).choose_spec
          refine ⟨(C1_stripClause (p := p) j).choose, ?_, ?_⟩
          · show (C1_stripClause (p := p) j).choose
                ∈ mkFreshClauses H n N S vOf (m+1) hm1
            unfold mkFreshClauses
            rw [List.mem_append]
            left
            rw [List.mem_map]
            exact ⟨j, by rw [Finset.mem_toList]; exact hj_strip, rfl⟩
          · rw [hspec.1]
            exact Finset.mem_singleton_self j

/-- U10a — floor-monotone downset TRANSPORT: pins standing before read `i+1` that stay
interior to the NEW rim sit at-or-below the NEW floor (at the new frame's heights). -/
theorem zc_step_transport {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+1)).pinned j = true →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
        ≤ H.floorH (i+2) (boxChart n N j).2 := by
  -- STATUS (2026-07-31, hc2-p-phase-hard round): PROVED, ih-free (the DC-3 route
  -- refined): pin PROVENANCE (`pin_src`) traces the pin to a fresh cut of some read
  -- k ≤ i; U3 `mkFresh_band` supplies the band's upper edge at read k; the
  -- GENERAL-STEP FLOOR BRIDGE (`bridge_ht`: κ = slope·D, the ℕ edge telescope along
  -- the width chain, `C3_steeperChain` slope monotonicity, `C3_lineDom` at the
  -- k-edge) transports it to node (i+1)'s staircase at frame-(i+2) heights, which
  -- `C2_floorH_succ` places under the new floor.  Statement byte-unchanged.
  intro j hj hpin
  obtain ⟨k, hk, hkm, cl, hcl, hcs⟩ := pin_src S vOf (i+1) j hpin
  have hedge := (mkFresh_band H n N S vOf k hk cl hcl j hcs).2.2
  have hbr := bridge_ht hcoh hreal hk (by omega : k ≤ i + 1) hi1 (boxChart n N j) hj hedge
  refine le_trans hbr ?_
  rw [C2_floorH_succ H (i+1) hi1]
  exact le_max_right _ _

/-- U10b — fresh-cut downset EXACTNESS: an interior at-or-below-new-floor coordinate is
pinned after read `i+1` (old pin or fresh cut — the downset grows by exactly the strip
zeros + the sub-line levels). -/
theorem zc_step_freshExact {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
          ≤ H.floorH (i+2) (boxChart n N j).2 →
      (mkSigma H n N S vOf (i+2)).pinned j = true := by
  -- STATUS (2026-07-31, hc2-p-phase-hard round): PROVED via `downset_pinned` (ordinary
  -- induction on the read index, base = the PROVED U9b `zc_root_downset_mpr`; the
  -- at-or-below-OLD-floor case rides the IH through the rim chain + pin persistence,
  -- the strictly-fresh case rides the reverse bridge into the band and the strip/value
  -- dichotomy — the value roster's whole-level-set condition is discharged by F5 floor
  -- window-constancy, NOT by U4's sorried `levelSet_no_straddle`).  `hunpinned` is
  -- derived ih-free (provenance + bridge vs. the U3 band's strict floor clause).
  -- Statement byte-unchanged.
  intro j hj hfloor
  exact downset_pinned S vOf hcoh hreal hbox hN (i+1) hi1 j hj hfloor

/-- U10c — interior ZEROS: interior pins of the new state solve to the literal 0.

QUEUE ITEM 17 EXECUTED (2026-07-31, Asvin sign-off on the consolidated queue): the
STOP-record's two named residues are both discharged —
* the STEP-READ value-interior-exclusion law is now the `ZCSeedLaws.step_shape` field
  (the Q8-class D5-fence designer addendum, `HC2/Defs.lean`; root_shape's all-reads
  generalization) — interior pins of read `i+1` are STRIP pins;
* the OLD-pin leg's `ih`-threading (named by the third-prover record as part of the
  block) is executed: the statement GAINS the `ih : ZCData …` hypothesis row that the
  assembled `zc_step` already carries (hypothesis-side, matching zc_step's own binder;
  zc_step's statement stays byte-unchanged) — old interior pins have literal-zero old
  solves (`ih.interior_zero` through the rim chain), which spec clause (4) + `theta_norm`
  carry to the new state.
Proof: every interior pin of `Σ_{i+2}` sits at-or-below the new floor (provenance +
the general-step bridge — the U10a machinery), so `theta_norm` makes `Θ_{i+1}` literal
there; the pin's provenance dichotomy (spec clause (2)) is strip-clause (clause (3)),
value-clause (EXCLUDED by `step_shape` at read `i+1`), or old pin (clause (4) +
`ih.interior_zero`); both live legs close by the U9c tail (`u9c_probe_tail`). -/
theorem zc_step_interiorZero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (ih : ZCData (mkSigma H n N S vOf (i+1)) (boxChart n N) (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth →
      (mkSigma H n N S vOf (i+2)).pinned j = true →
      ∀ f : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf (i+2)).solve j f = 0 := by
  -- (The full pre-repair STOP/escalation history — DC-3 obstruction, badSeed, the
  -- second- and third-prover confirmations — is preserved in git history and the
  -- BRIDGE_BP2 §5 R-3 risk record; the queue-17 record above supersedes it.)
  classical
  intro j hj hpin f
  have hm : i < H.nodes.length := by omega
  have hsig : mkSigma H n N S vOf (i+2)
      = pinTransportSystem (mkSigma H n N S vOf (i+1)) (S.Theta (i+1))
          (mkFresh H n N S vOf (i+1) hi1) := by
    show (if hi : i + 1 < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf (i+1)) (S.Theta (i+1))
          (mkFresh H n N S vOf (i+1) hi)
      else mkSigma H n N S vOf (i+1)) = _
    rw [dif_pos hi1]
  -- witness existence at read i+1 (the downset_pinned block, ih-free)
  have hunp : ∀ c : Fin (n * N), (mkSigma H n N S vOf (i+1)).pinned c = true →
      ¬ ∃ cl ∈ (mkFresh H n N S vOf (i+1) hi1).clauses, c ∈ cl.support := by
    intro c hc hex
    obtain ⟨cl, hcl, hcs⟩ := hex
    have hband := mkFresh_band H n N S vOf (i+1) hi1 cl hcl c hcs
    obtain ⟨k, hk, hkm, cl', hcl', hcs'⟩ := pin_src S vOf (i+1) c hc
    have hedge := (mkFresh_band H n N S vOf k hk cl' hcl' c hcs').2.2
    have hrim : (boxChart n N c).2
        < (H.nodes[i]'hm).μ * (H.nodes[i]'hm).childWidth := by
      have h1 := hband.1
      rwa [prevRim_succ n hm] at h1
    have hbr := bridge_ht hcoh hreal hk (by omega : k ≤ i) hm (boxChart n N c) hrim hedge
    have hfl : (H.nodes[i]'hm).staircase (boxChart n N c).2
        ≤ H.floorH (i+1) (boxChart n N c).2 := by
      rw [C2_floorH_succ H i hm]
      exact le_max_right _ _
    exact absurd (lt_of_lt_of_le hband.2.1 (le_trans hbr hfl)) (lt_irrefl _)
  have hasg : ∀ cl ∈ (mkFresh H n N S vOf (i+1) hi1).clauses,
      ∃ u : Fin (n * N) → ZMod p, ∀ x, cl.sat x ↔ ∀ c ∈ cl.support, x c = u c :=
    fun cl hcl => clause_assign cl (mkFresh_codim S vOf (i+1) hi1 cl hcl)
  have hEx : ∃ D' : Locus p (n * N),
      IsFreshAttach (mkSigma H n N S vOf (i+1)) (S.Theta (i+1))
        (mkFresh H n N S vOf (i+1) hi1) D' :=
    freshAttach_exists (mkSigma H n N S vOf (i+1)) (S.Theta_uni (i+1))
      (mkFresh H n N S vOf (i+1) hi1) hasg hunp
  have spec := pinTransportSystem_spec (mkSigma H n N S vOf (i+1)) (S.Theta (i+1))
    (mkFresh H n N S vOf (i+1) hi1) hEx
  have hpin' : (pinTransportSystem (mkSigma H n N S vOf (i+1)) (S.Theta (i+1))
      (mkFresh H n N S vOf (i+1) hi1)).pinned j = true := by
    rw [← hsig]; exact hpin
  -- the Θ-normalization bound: the interior pin is at-or-below the NEW floor
  -- (provenance + the general-step bridge, exactly the U10a machinery)
  have hbound : ((H.htH (i+2) (boxChart n N j) : ℚ) : WithBot ℚ)
      ≤ H.floorH (i+2) (boxChart n N j).2 := by
    obtain ⟨k, hk, hkm, cl, hcl, hcs⟩ := pin_src S vOf (i+2) j hpin
    have hedge := (mkFresh_band H n N S vOf k hk cl hcl j hcs).2.2
    have hbr := bridge_ht hcoh hreal hk (by omega : k ≤ i + 1) hi1 (boxChart n N j) hj hedge
    refine le_trans hbr ?_
    rw [C2_floorH_succ H (i+1) hi1]
    exact le_max_right _ _
  have hthetalit : ∀ x : Fin (n * N) → ZMod p, S.Theta (i+1) x j = x j :=
    fun x => S.zcSeed.theta_norm (i+1) hi1 j hbound x
  rw [hsig]
  -- pin provenance at THIS step (spec clause (2)): old pin ∨ fresh cut of read i+1
  rcases (spec.2.1 j).mp hpin' with hold | ⟨cl, hclmem, hjsup⟩
  · -- OLD pin: interior to the OLD rim (rim chain), so ih gives literal-zero old
    -- solves; clause (4) + theta_norm carry them to the new state.
    have hjold : (boxChart n N j).2 < (H.nodes[i]'hm).μ * (H.nodes[i]'hm).childWidth :=
      lt_of_lt_of_le hj (rim_step hcoh hi1)
    have hzero : ∀ g : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf (i+1)).solve j g = 0 :=
      fun g => ih.interior_zero j hjold hold g
    exact u9c_probe_tail _ _ j f (fun x hx => spec.2.2.2 j hold hzero x hx) hthetalit
  · -- FRESH cut of read i+1: strip (clause (3)) or value (EXCLUDED by step_shape)
    rcases List.mem_append.mp hclmem with hstrip | hval
    · obtain ⟨c, hcmem, rfl⟩ := List.mem_map.mp hstrip
      have hjc : j = c :=
        Finset.mem_singleton.mp ((C1_stripClause (p := p) c).choose_spec.1 ▸ hjsup)
      subst hjc
      exact u9c_probe_tail _ _ j f
        (fun x hx => spec.2.2.1 j ⟨(C1_stripClause (p := p) j).choose, hclmem,
          (C1_stripClause (p := p) j).choose_spec.1,
          (C1_stripClause (p := p) j).choose_spec.2.2⟩ x hx)
        hthetalit
    · exfalso
      obtain ⟨jh, hjhmem, rfl⟩ := List.mem_map.mp hval
      rw [valueClause_support' S vOf (i+1) hi1 jh.1 (valueSlots_spanSlot jh.2)] at hjsup
      unfold levelSet at hjsup
      obtain ⟨-, hfs, hhtv⟩ := Finset.mem_filter.mp hjsup
      exact S.zcSeed.step_shape (i+1) hi1 j hj
        ⟨by rw [hfs]; exact valueSlots_spanSlot jh.2, by rw [hfs]; exact hhtv⟩

/-- U10d — rim-lead PLACEMENT/CONFINEMENT, FRESH-CUT RESTRICTED (QUEUE ITEM 17
EXECUTED, 2026-07-31, Asvin sign-off — the adjudicated preferred option): every FRESH
cut of the standing read `i+1` sits inside the read's constraint region (base index
`< prevRim n (i+1)` — §C rim rule / DOM(3), which confines FRESH cuts only).
The former ∀-pins form was an E-phase over-quantification, REFUTED-as-stated by the
compiled negation witness `U10d_negWitness.lean` (`confine_bound_fails` /
`zcStepConfineStmt_false_of_config`: old pins PERSIST beyond the shrinking rim — the
BLOCKED-SUSPECT-FALSE record of the hc2-p-phase-hard round, upgraded to
evidence-complete at PROBE-C; full mechanism in that leaf's header). Zero in-tree
consumers were re-pointed (grep: only U13 consumes `zc_step`, never this). -/
theorem zc_step_confine {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (∃ cl ∈ (mkFresh H n N S vOf (i+1) hi1).clauses, j ∈ cl.support) →
      (boxChart n N j).2 < H.prevRim n (i + 1) := by
  -- The restricted content IS U3's band confinement: a fresh cut lies in the read's
  -- band, whose first clause is the rim bound.
  intro j hex
  obtain ⟨cl, hcl, hcs⟩ := hex
  exact (mkFresh_band H n N S vOf (i+1) hi1 cl hcl j hcs).1

/-- U10 assembled — the inductive step: (ZC) at prefix `i+1` re-establishes (ZC) at
prefix `i+2` (the `i+1` instance of `JetSetup.zc` from the `i` instance). -/
theorem zc_step {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (ih : ZCData (mkSigma H n N S vOf (i+1)) (boxChart n N) (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) :
    ZCData (mkSigma H n N S vOf (i+2)) (boxChart n N) (H.htH (i+2)) (H.floorH (i+2))
      ((H.nodes[i+1]'hi1).μ * (H.nodes[i+1]'hi1).childWidth) := by
  -- QUEUE ITEM 17 EXECUTED (2026-07-31): PROVED, statement byte-unchanged, exactly as
  -- the hc2-p-phase-hard update predicted — `downset_exact` mp by the U10a machinery
  -- at pins of `Σ_{i+2}` (provenance + `bridge_ht` at M := i+1), mpr by the PROVED
  -- `zc_step_freshExact`; `interior_zero` by the now-PROVED U10c
  -- (`zc_step_interiorZero`, closed by the `step_shape` zcSeed law + the recorded
  -- ih-threading — see its queue-17 record).
  refine ⟨fun j hj => ⟨fun hpin => ?_, zc_step_freshExact S vOf hcoh hreal hbox hN i hi1 j hj⟩,
    fun j hj hpin f =>
      zc_step_interiorZero S vOf hcoh hreal hbox hN i hi1 ih j hj hpin f⟩
  obtain ⟨k, hk, hkm, cl, hcl, hcs⟩ := pin_src S vOf (i+2) j hpin
  have hedge := (mkFresh_band H n N S vOf k hk cl hcl j hcs).2.2
  have hbr := bridge_ht hcoh hreal hk (by omega : k ≤ i + 1) hi1 (boxChart n N j) hj hedge
  refine le_trans hbr ?_
  rw [C2_floorH_succ H (i+1) hi1]
  exact le_max_right _ _

end LeanUrat.MovesJ
