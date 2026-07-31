/-
Unit U4.mkFresh_cover  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `fresh_cover` docstring ("every band coordinate lies in SOME clause's
support — EXACTLY one, by disj").
deps: D6, U2.  difficulty: easy-medium.  hypothesis_fields: none.
sketch: dichotomy on `IsValueCoord c`: value → c is in its slot's level set = that value
clause's support; non-value → its strip clause exists by D6's strip roster.

*** OBSTRUCTION (P-phase, 2026-07-27; dual-confirmed by Codex gpt-5.6-sol, fresh context) ***
U4 IS NOT PROVABLE AS STATED — `hypothesis_fields: none` is insufficient; the value case is
FALSE on a legal countermodel.  The strip case and ALL list/clause plumbing DO close (proved
below); the entire theorem reduces to the single leftover goal at the `sorry`:
    the value slot `j := ν.fineSlot (boxChart n N c).2` lies in `valueSlots H n N i ν`,
whose defining filter (`Defs.lean` `valueSlots`, lines ~328-332) carries the ROSTER clause
    `∀ c' ∈ levelSet H n N i ν j, inFreshBand H n (boxChart n N) i ν c'`
— the ENTIRE height-level set of slot `j` must be in-band.  U4 hands us this for ONE member
(`c`) only.  `levelSet j` (`Defs.lean` ~310-313) collects EVERY box coordinate at fine slot
`j` and height `ν.slotVal j`, with NO band filter; `inFreshBand` (MovesC `Defs.lean` ~750-754)
imposes the per-BASE-INDEX conditions `(boxChart c').2 < H.prevRim n i` and
`H.floorH i (boxChart c').2 < ν.slotVal j`.  `H.floorH` reads ONLY the `Node.line`/`staircase`
data of the EARLIER nodes (r < i); `ν.slotVal`/`H.htH` read node-i's line and the level/kappa
data.  In U4 (no `HistoryCoherent`, no `Realizable`) the Node structure constraints are all
PER-NODE and never cross-link node-i's line to the earlier nodes' lines, so `floorH` is
adversarially FREE relative to `slotVal`/`htH`, and it varies across the base indices of a
single fine slot (staircase blocks have width `childWidth_r`, unrelated to node-i's `Dwidth`).
Hence `levelSet j` can STRADDLE the floor-crossing: an in-band `c` and an out-of-band sibling
`c'` at the same fine slot and same height `slotVal j`.  Then `j ∉ valueSlots`, its value
clause is absent, and `c` (a value coord, so excluded from every strip) is UNCOVERED.
Countermodel skeleton (Codex, with `h ≥ 1` repair): `n=N=2`, `i=1`, nodes `[ρ, ν]`, `ρ`
supplies a `line` with `floorH 1 0 = 0` but `floorH 1 1 = 2`; `ν` has `Dwidth=2` so bases 0,1
share fine slot 0 with `slotVal 0 = 1`; coords `(1,0)` and `(1,1)` are both in `levelSet 0`
at height 1, yet only `(1,0)` is in-band.  (Root case `i=0` is clean: `floorH 0 = ⊥`,
`prevRim n 0 = n`, so every level-set member is in-band — the straddle needs `i ≥ 1`.)
ROOT CAUSE: the blueprint's U3/U4 sketch treats `levelSet` as ALREADY band-restricted ("value
slots past the (γ) crossing have empty level sets IN THE BAND"), but the E-phase Defs made
`levelSet` the FULL level set with a separate roster in `valueSlots`; the two co-satisfy U3
(band) + U5 (IsValueSupport = full level set) but make U4 (cover) unsatisfiable on straddling
slots.  FIX (statement/Defs-fence — needs human SIGN-OFF, NOT applied here): either (i) add
`HistoryCoherent`+`Realizable` to U4 AND supply the genuine geometric no-straddle lemma (the
SAE strict span-entry keeps node-i's line strictly above the floor across span slots — this is
hard-core content), or (ii) redesign `levelSet`/`IsValueSupport`/`valueSlots` to be band-aware
(intersect the level set with the band), which then also touches U3/U5/U6.

*** N-6 SIGN-OFF EXECUTED (2026-07-28 — §9 F-7's ruling: OPTION (i), the RECOMMENDED
route; option (ii) rejected as non-minimal — it re-opens proved U3/U5/U6 + Defs). ***
`mkFresh_cover` GAINS `hcoh : HistoryCoherent H` + `hreal : Realizable H`; the roster
goal is discharged by the NEW named geometric lemma `levelSet_no_straddle` (below,
sorried — the (SAE)/C.1.5 line-dominance content, the U10 wave's family; QUEUED for the
fleet). U4's own theorem body is now complete modulo that named lemma; the countermodel
above is closed by hypothesis (its adversarial `floorH` needs an incoherent H).
Consumer update: U13 threads `hcoh hreal` (it holds both).

*** QUEUE ITEM 12 — REPAIR ADJUDICATION PACKAGE + EXECUTION (2026-07-31, Asvin
sign-off on the consolidated queue; the /goal authority adjudicates: the option that
MAKES THE PROOF WORK wins). ***
EVIDENCE RE-READ. The queue row carried forward the dual-confirmed 2026-07-27
countermodel ("NOT PROVABLE AS STATED — value case false on a legal countermodel").
That countermodel (above) targets the PRE-N-6, hypothesis-free form: its adversarial
`floorH` step data (`floorH 1 0 = 0` while `floorH 1 1 = 2` INSIDE one node-1 fine
slot) requires `childWidth₀ ≠ Dwidth₁`, i.e. an INCOHERENT history — under
`HistoryCoherent`'s width chain `D_{i+1} = cW_i`, the cumulative floor is
WINDOW-CONSTANT on each fine slot (the F5 floor collapse, PROVED in the U10
hc2-p-phase-hard round: `floorH (m+1) = staircase_m` on the factor interior, a
left-edge evaluation on aligned `cW_m`-blocks). So the evidence refutes the OLD form
only; the CURRENT statement (post-N-6, carrying `hcoh + hreal`) is not touched by it.
REPAIR OPTIONS ENUMERATED.
 (o-i) STATEMENT STANDS; prove it via the U10 F5 kernel (floor window-constancy +
       the fine-slot window's rim containment). Zero statement changes.
 (o-ii) Add further hypotheses (an explicit no-straddle seed law / rim guard) —
       unnecessary if (o-i) closes; rejected as non-minimal.
 (o-iii) Band-aware `levelSet`/`valueSlots` redesign — REJECTED already at N-6
       (re-opens proved U3/U5/U6 + Defs); unchanged here.
ADJUDICATION: (o-i) — executed below and PROVED. The proof engine is a file-private
replica block of the U10 floor-collapse kernel (`Dwidth_pos`/`slope_pos`/
`staircase_mono`/`floorH_collapse` etc. are `private` in `U10_zcStep.lean`; the
`valueClause_support'` replica precedent applies; the block is a dedup target for the
queue's item-8 de-privatize sweep). Proof shape: (rim) the fine-slot window of the
straddle-free slot `j` sits inside the standing rim (`j+1 ≤ μ_{i−1}` from the in-band
member + the coherence width chain), so every level-set sibling is rim-interior;
(floor) F5 window-constancy gives `floorH i` the SAME value at all siblings of the
slot, so the in-band member's strict floor clause transfers; (edge) the level set
sits AT `slotVal j` — the band's upper edge — by membership. Root case `i = 0` is the
clean corner (`floorH 0 = ⊥`, `prevRim n 0 = n`).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedZC
import LeanUrat.MovesC.C2_floorH_succ
import LeanUrat.MovesC.C2_floorH_root
import LeanUrat.MovesC.C3_lineDom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedZC

/-! ### The file-private F5 floor-collapse kernel (queue item 12, 2026-07-31).
Byte-faithful replicas of the `private` U10 kernel (`LeanUrat/HC2/U10_zcStep.lean`,
hc2-p-phase-hard round) — the `valueClause_support'` replica precedent; a dedup
target for the item-8 de-privatize sweep. Provenance per lemma: the identically-named
`private` original in U10_zcStep. -/

section StraddleKernel

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

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

private lemma floorH_collapse {H : History p F} (hcoh : HistoryCoherent H)
    (hreal : Realizable H) {M : ℕ} (hM : M < H.nodes.length) {b : ℕ}
    (hb : b < (H.nodes[M]'hM).μ * (H.nodes[M]'hM).childWidth) :
    H.floorH (M+1) b = (H.nodes[M]'hM).staircase b := by
  refine le_antisymm ?_ ?_
  · exact floorH_le (M+1) (by omega)
      (fun r hr hrl => staircase_mono hcoh hreal hrl (by omega) hM hb)
  · rw [C2_floorH_succ H M hM b]
    exact le_max_right _ _

end StraddleKernel

/-- THE GEOMETRIC NO-STRADDLE LEMMA (N-6 option (i), 2026-07-28): under coherence +
realizability, a span slot's exact-valuation level set cannot STRADDLE the floor — if
one member is in-band, every member is. Content: the (SAE) strict span-entry / C.1.5
line-dominance keeps node-i's line strictly above the accumulated floor across the whole
window, so the per-base floor variation of the earlier staircases cannot cross a level
set sitting AT `slotVal j` (the U10 wave's family; the root case i = 0 is clean —
`floorH 0 = ⊥`).
QUEUE ITEM 12 EXECUTED (2026-07-31): PROVED, statement unchanged (adjudication option
(o-i) — see the header package). Rim leg: the slot's fine window sits inside the
standing rim (`j+1 ≤ μ_{i−1}` from the in-band member, coherence width chain
`D_i = cW_{i−1}`). Floor leg: F5 floor window-constancy (`floorH_collapse` — the
cumulative floor IS node (i−1)'s staircase on the factor interior, a left-edge
evaluation constant across each fine slot), so the in-band member's strict floor
clause transfers to every sibling. Edge leg: level-set membership IS the band's upper
edge (`htH = slotVal j`). -/
theorem levelSet_no_straddle {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ)
    (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (c c' : Fin (n * N))
    (hc : c ∈ levelSet H n N i (H.nodes[i]'hi) j)
    (hband : inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c)
    (hc' : c' ∈ levelSet H n N i (H.nodes[i]'hi) j) :
    inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c' := by
  classical
  have hcm := hc
  unfold levelSet at hcm
  rw [Finset.mem_filter] at hcm
  obtain ⟨-, hcfs, hcht⟩ := hcm
  have hcm' := hc'
  unfold levelSet at hcm'
  rw [Finset.mem_filter] at hcm'
  obtain ⟨-, hcfs', hcht'⟩ := hcm'
  obtain ⟨hrim, hfl, -⟩ := hband
  rcases i with _ | m
  · -- ROOT READ: rim = the whole box, floor = ⊥ — every level-set member is in-band.
    refine ⟨?_, ?_, ?_⟩
    · exact (boxChart_lt n N c').2
    · rw [C2_floorH_root]
      exact WithBot.bot_lt_coe _
    · rw [hcfs']
      exact le_of_eq hcht'
  · -- STEP READ i = m+1: rim containment of the fine window + F5 window-constancy.
    have hm : m < H.nodes.length := by omega
    have hm1 : m + 1 < H.nodes.length := hi
    have hDcw : (H.nodes[m+1]'hm1).Dwidth = (H.nodes[m]'hm).childWidth :=
      (hcoh.2.2.2 m hm1).2.2.2.2.2.1
    have hDpos : 0 < (H.nodes[m+1]'hm1).Dwidth := Dwidth_pos hcoh hm1
    -- the standing rim in node-m form
    have hrimc : (boxChart n N c).2 < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by
      have h1 := hrim
      rwa [prevRim_succ n hm] at h1
    -- the slot's window sits inside the rim: j + 1 ≤ μ_m
    have hj0b : (boxChart n N c).2 / (H.nodes[m+1]'hm1).Dwidth = j := by
      have h := hcfs
      simp only [Node.fineSlot] at h
      exact h
    have hj1 : j + 1 ≤ (H.nodes[m]'hm).μ := by
      have h1 : j * (H.nodes[m+1]'hm1).Dwidth ≤ (boxChart n N c).2 := by
        rw [← hj0b]
        exact Nat.div_mul_le_self _ _
      have h1' : j * (H.nodes[m]'hm).childWidth ≤ (boxChart n N c).2 := by
        rw [← hDcw]
        exact h1
      have h2 : j * (H.nodes[m]'hm).childWidth
          < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := lt_of_le_of_lt h1' hrimc
      exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
    -- c' shares the window, hence also sits inside the rim
    have hj0b' : (boxChart n N c').2 / (H.nodes[m+1]'hm1).Dwidth = j := by
      have h := hcfs'
      simp only [Node.fineSlot] at h
      exact h
    have hwin' : (boxChart n N c').2 < (j + 1) * (H.nodes[m+1]'hm1).Dwidth := by
      have h3 : (H.nodes[m+1]'hm1).Dwidth
            * ((boxChart n N c').2 / (H.nodes[m+1]'hm1).Dwidth)
          + (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth = (boxChart n N c').2 :=
        Nat.div_add_mod _ _
      rw [hj0b'] at h3
      have h4 : (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth
          < (H.nodes[m+1]'hm1).Dwidth := Nat.mod_lt _ hDpos
      calc (boxChart n N c').2
          = (H.nodes[m+1]'hm1).Dwidth * j
            + (boxChart n N c').2 % (H.nodes[m+1]'hm1).Dwidth := h3.symm
        _ < (H.nodes[m+1]'hm1).Dwidth * j + (H.nodes[m+1]'hm1).Dwidth :=
            Nat.add_lt_add_left h4 _
        _ = (j + 1) * (H.nodes[m+1]'hm1).Dwidth := by ring
    have hrimc' : (boxChart n N c').2
        < (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by
      calc (boxChart n N c').2 < (j + 1) * (H.nodes[m+1]'hm1).Dwidth := hwin'
        _ ≤ (H.nodes[m]'hm).μ * (H.nodes[m+1]'hm1).Dwidth := mul_le_mul_right' hj1 _
        _ = (H.nodes[m]'hm).μ * (H.nodes[m]'hm).childWidth := by rw [hDcw]
    -- F5 window-constancy: both floors are node m's staircase at the SAME left edge
    have hbcw : (boxChart n N c).2 / (H.nodes[m]'hm).childWidth = j := by
      rw [← hDcw]
      exact hj0b
    have hbcw' : (boxChart n N c').2 / (H.nodes[m]'hm).childWidth = j := by
      rw [← hDcw]
      exact hj0b'
    have hfle : H.floorH (m+1) (boxChart n N c').2 = H.floorH (m+1) (boxChart n N c).2 := by
      rw [floorH_collapse hcoh hreal hm hrimc', floorH_collapse hcoh hreal hm hrimc]
      unfold Node.staircase
      rw [if_pos hrimc', if_pos hrimc, hbcw, hbcw']
    refine ⟨?_, ?_, ?_⟩
    · rw [prevRim_succ n hm]
      exact hrimc'
    · rw [hfle, hcht']
      rw [hcht] at hfl
      exact hfl
    · rw [hcfs']
      exact le_of_eq hcht'

/-- Every band coordinate is covered by some constructed clause's support (verbatim
`JetSetup.fresh_cover`'s field type at `mkFresh`; N-6 RESTATEMENT: under
coherence + realizability — the sign-off's option (i)). -/
theorem mkFresh_cover {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ c : Fin (n * N), inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c →
      ∃ cl ∈ (mkFresh H n N S vOf i hi).clauses, c ∈ cl.support := by
  classical
  set ν := H.nodes[i]'hi with hν
  intro c hband
  by_cases hv : IsValueCoord H (boxChart n N) i ν c
  · -- VALUE case: c sits in its slot's level set = a value clause's support
    set j := ν.fineSlot ((boxChart n N c).2) with hj
    have hspan : ν.spanSlot j := hv.1
    have hht : H.htH i (boxChart n N c) = ν.slotVal j := hv.2
    -- c belongs to slot j's level set
    have hc_level : c ∈ levelSet H n N i ν j := by
      unfold levelSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ c, rfl, hht⟩
    -- slot j is rostered as a value slot
    have hj_val : j ∈ valueSlots H n N i ν := by
      unfold valueSlots
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hspan, ⟨c, hc_level⟩, ?_⟩
      · have := hspan.2; omega
      · -- ROSTER: the WHOLE level set of slot `j` is in-band — the N-6 no-straddle
        -- lemma fired at the in-band member `c` (the former dual-confirmed obstruction,
        -- closed by the option-(i) hypothesis addition; see the header record).
        intro c' hc'
        exact levelSet_no_straddle H n N hcoh hreal i hi j c c' hc_level hband hc'
    -- the value clause at slot j
    set vcl := valueClause H n N S vOf i hi j (valueSlots_spanSlot hj_val) with hvcl
    -- C4 hoist (2026-07-30): the digit-alphabet count consumed from `SharedZC.card_fin_fun'`
    -- (formerly an inline re-proof; a `Prop` arg to `C1_TYP_toClause`, proof-irrelevant).
    have hcard : Nat.card (Fin (levelSet H n N i ν j).card → ZMod p)
        = p ^ (levelSet H n N i ν j).card := card_fin_fun' _
    have hsupp : vcl.support = levelSet H n N i ν j := by
      rw [hvcl]
      unfold valueClause
      exact (C1_TYP_toClause _ _ (levelSet H n N i ν j).card hcard).choose_spec.1
    refine ⟨vcl, ?_, ?_⟩
    · -- vcl is in the value part of the clause list
      show vcl ∈ mkFreshClauses H n N S vOf i hi
      unfold mkFreshClauses
      rw [List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨⟨j, hj_val⟩, by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, rfl⟩
    · rw [hsupp]; exact hc_level
  · -- STRIP case: c is a non-value band coordinate, covered by its strip clause
    have hc_strip : c ∈ stripSet H n N i ν := by
      unfold stripSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hband, hv⟩
    set cl := (C1_stripClause (p := p) c).choose with hcl
    have hspec := (C1_stripClause (p := p) c).choose_spec
    refine ⟨cl, ?_, ?_⟩
    · show cl ∈ mkFreshClauses H n N S vOf i hi
      unfold mkFreshClauses
      rw [List.mem_append]
      left
      rw [List.mem_map]
      exact ⟨c, by rw [Finset.mem_toList]; exact hc_strip, rfl⟩
    · rw [hspec.1]; exact Finset.mem_singleton_self c

end LeanUrat.MovesJ
