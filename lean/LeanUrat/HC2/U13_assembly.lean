/-
Unit U13.jetSetup_of_seed  (HC-2 campaign, E-phase — blueprint §5 Layer B assembly)
moves_ref: MovesC `JetSetup` structure (all 29 fields — rev 2, audit GAP-7(i)).
deps: D1 (boxChart + its two laws), U1 (discharges `hkeys` at call sites), U2–U11
(+U9/U10 for `zc`), D5–D7.  difficulty: medium (assembly only).
hypothesis_fields: S (SEED-EXIST's payload), hkeys (U1-dischargeable), hN, hbox, hd4
(N-5), vOf, hunp (K2).
sketch: field-by-field packaging; `coordOf := boxChart n N` with D1's laws,
`keys := keys` with `hkeys`'s two laws, `coherent := hcoh`, `realizable := hreal`,
`root_height` from U11, seed fields verbatim, constructed fields with their U-layer laws
(`fresh i` = `mkFresh` for `i < len`, `emptyFresh` junk beyond).
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1).
[2026-07-30 verify-2 fold-in: the former "Sorries retained for the next fleet round"
boilerplate here was misleadingly placed and is removed — THIS unit is 0-sorry in-body;
only its lemma DEPS carry open sorries (`jetSetup_of_seed` footprint = sorryAx through
the U10 cone, re-verified 2026-07-30), as the N-queue paragraph below already records.]
N-QUEUE RESTATEMENT (2026-07-28, sign-off round): gains `hd4 : RootD4 H` (N-5 — threads
to U11's `root_height_of_inBox`) and `hunp : SeedFreshUnpinned H n N S vOf` (K2 —
threads to the restated `mkSigma_recursion`, whose bare form is retired); the `fc` leg
threads `hcoh`/`hreal` into the N-6-restated `mkFresh_cover`. Re-verified: the assembly
still closes (this unit stays sorry-free in its own right; its lemma deps carry the
open sorries).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U3_freshBand
import LeanUrat.HC2.U4_freshCover
import LeanUrat.HC2.U5_freshAssembled
import LeanUrat.HC2.U6_mstarEq
import LeanUrat.HC2.U7_sigmaRec
import LeanUrat.HC2.U8_inhImplied
import LeanUrat.HC2.U9_zcRoot
import LeanUrat.HC2.U10_zcStep
import LeanUrat.HC2.U11_rootHeight

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A lawful key tower + a graded seed + coherence/realizability/box data assemble to a
`JetSetup` — the HC-2 bridge's core deliverable (MovesC's honest boundary, discharged
from the seed). -/
theorem jetSetup_of_seed {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (hkeys : KeysLawful H keys) (S : PresentSeed p F H n N keys) (hN : 1 ≤ N)
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H)
    (hd4 : RootD4 H) (vOf : VOf p (n * N)) (hunp : SeedFreshUnpinned H n N S vOf) :
    Nonempty (JetSetup H n N (n * N)) := by
  -- the fresh-data field: `mkFresh` inside the history's range, `emptyFresh` junk beyond.
  set freshFn : ℕ → FreshData p (n * N) :=
    fun i => if hi : i < H.nodes.length then mkFresh H n N S vOf i hi
             else emptyFresh p (n * N) with hfreshFn
  have hfresh : ∀ (i : ℕ) (hi : i < H.nodes.length),
      freshFn i = mkFresh H n N S vOf i hi := by
    intro i hi; rw [hfreshFn]; exact dif_pos hi
  refine ⟨{
    hm := rfl
    hN := hN
    coordOf := boxChart n N
    coordOf_sorted := boxChart_sorted n N
    coordOf_lt := boxChart_lt n N
    coherent := hcoh
    realizable := hreal
    root_height := root_height_of_inBox hcoh hbox hd4
    Sigma := mkSigma H n N S vOf
    init := mkSigma_init H n N S vOf
    fresh := freshFn
    Theta := S.Theta
    Theta_uni := S.Theta_uni
    keys := keys
    keys_mid := hkeys.1
    landing := hkeys.2
    pres := S.pres
    pres_zero := S.pres_zero
    pres_total := S.pres_total
    pres_theta := S.pres_theta
    pres_block := S.pres_block
    stratum := mkStratum H n N S vOf
    recursion := mkSigma_recursion H n N S vOf hunp
    inh_implied := ?inh
    zc := ?zc
    fresh_band := ?fb
    fresh_cover := ?fc
    fresh_assembled := ?fa
    mstar_eq := ?me
  }⟩
  case inh =>
    intro i hi y hy
    rw [hfresh i hi]
    exact mkStratum_inh H n N S vOf i hi y hy
  case zc =>
    intro i
    induction i with
    | zero => intro hi; exact zc_root S vOf hcoh hreal hbox hN hi
    | succ k ihk =>
        intro hi
        exact zc_step S vOf hcoh hreal hbox hN k hi (ihk (by omega))
  case fb =>
    intro i hi cl hcl c hc
    rw [hfresh i hi] at hcl
    exact mkFresh_band H n N S vOf i hi cl hcl c hc
  case fc =>
    intro i hi c hband
    rw [hfresh i hi]
    exact mkFresh_cover H n N S vOf hcoh hreal i hi c hband
  case fa =>
    intro i hi cl hcl
    rw [hfresh i hi] at hcl
    exact mkFresh_assembled H n N S vOf i hi cl hcl
  case me =>
    intro i hi
    rw [hfresh i hi]
    exact mkFresh_mstar H n N S vOf hcoh hreal i hi

end LeanUrat.MovesJ
