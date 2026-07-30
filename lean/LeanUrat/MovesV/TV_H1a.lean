/-  TV-H1a (BRIDGE BP3, cluster c2; E-phase skeleton) — [GATE, countermodel-
    first, risk R2; runs BEFORE TV-H3] COUNTERMODEL CARRIERS for the banked
    W17ii clause (ii) (`w17ii_wave4`, MovesV/V7_w17ii.lean:48, the ONE banked
    [3t] sorry, C14): the degenerate table + all-inactive MeasuredSide + the
    degenerate RatBurdens over it + the DetHyp inhabitation check.  Pure
    carrier work — the ~30-field RS4Chain ASSEMBLY is TV-H1b's.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.G + §4 (TV-H1a).
    deps: none.

    SEALED PREDICTION (the standing fence-rule record, quoted §3.G): a
    from-scratch RS4Chain with shDom INFINITE and shWeightH ≡ 1 satisfies
    every card law (shweight_card via shEvtH := univ; wshval_card ties WshVal)
    while clause (ii)'s HasSum over the infinite shDom FAILS — clause (ii) is
    plausibly FALSE as stated; nothing in the chain forces summability over an
    infinite shDom.

    TYPING-TIME RESOLUTION (recorded — a deviation from the sketch's MECHANISM,
    same deliverable):
    (1) the sketch's route "activeState ≡ False ⟹ allActivePools = ∅ ⟹
      sh_realized (and every guarded law) vacuous" is BLOCKED by
      `RatBurdens.act_iff` at any carrier with a nonempty block state:
      act_iff + cellP_nonzero + finC + pools_infinite force activeState TRUE
      at all but finitely many pools (finitely many nonzero cellP polynomials
      have finitely many roots), so allActivePools = ∅ is unreachable there;
      and at EMPTY block states `allActivePools = M.Pools` (the ∀-τ condition
      is vacuously true), not ∅.  The blueprint's parenthetical "(allowed: no
      MeasuredSide law forces activity)" is true of MeasuredSide alone but not
      of the RatBurdens the chain also carries.
    (2) MINIMAL RESOLUTION adopted for the attempt: n := 1 with EMPTY block
      states (State e := PEmpty genre).  Then activeState ≡ False holds
      VACUOUSLY (the pin `negMS_inactive` below is still exactly the
      blueprint's stated pin); every ∀-τ law of LedgerIV / RatBurdens /
      RS1Bundle / PoolHyp is vacuous or empty-indexed; allActivePools =
      M.Pools, so `sh_realized` must instead be met with genuinely NONEMPTY
      shEvt — TV-H1b takes shEvtH := univ, visH := a singleton (shEvt = the
      full box, nonempty by boxpos), which simultaneously discharges
      shweight_card at weight ≡ 1 and forces WshVal ≡ 1 through wshval_card;
      clause (ii) then demands HasSum of the constant 1 over the infinite
      shDom — false at EVERY value, so the refutation no longer needs
      WshVal = 0.
    (3) DetHyp INHABITATION CHECK (the unit's explicit duty; predicted branch
      stated as `negDetHyp` below): at empty block states Kmat is a matrix
      over the empty index, det (1 − Kmat) = 1 ≠ 0, so DetHyp IS inhabited —
      hence rsh_interp/legs_read are NOT hdet-vacuous and must be discharged
      for real (they are TV-H1b's recorded plausible blockers, with legs_reg;
      PrimePools is forced total by prime_base).
    Allowed outcome per the blueprint: any piece may come back "blocked by
    law L" with L named — record at both fence sites, never force. -/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV.W17iiNeg

/-- TV-H1a piece 1: the countermodel TABLE (n := 1; empty block states per
the header resolution; VType = the forced (1,1) verdict singleton). -/
noncomputable def negTable : MovesS.TableShape 1 :=
  sorry

/-- TV-H1a piece 2: the degenerate MeasuredSide — Pools := the prime powers,
Box := a one-point carrier, Hgt := ℕ (infinite, so shDom can be infinite),
activeState ≡ False, entrance/cell fields empty-indexed. -/
noncomputable def negMS : MovesS.MeasuredSide negTable :=
  sorry

/-- TV-H1a pin: the blueprint's "activeState ≡ False" (at the adopted
carrier: vacuously — see header resolution (2)). -/
theorem negMS_inactive :
    ∀ (q₀ : ℚ) (e : ℕ) (τ : negTable.State e),
      ¬ negMS.activeState q₀ e τ := by
  sorry

/-- TV-H1a piece 3: the degenerate RatBurdens over (negTable, negMS) — every
per-τ field empty-indexed; act_iff vacuous at empty states (header (1)/(2)). -/
noncomputable def negRB : MovesS.RatBurdens negTable negMS :=
  sorry

/-- TV-H1a piece 4: DegCons at the degenerate table (vacuous at empty
states) — an RS4Chain index. -/
theorem negDegCons : MovesS.DegCons negTable := by
  sorry

/-- TV-H1a piece 5: KmatHyp on the block range (vacuous at empty states) —
an RS4Chain index. -/
theorem negKmatHyp : ∀ e, e ∈ Finset.Icc 1 1 → MovesS.KmatHyp negTable e := by
  sorry

/-- TV-H1a piece 6: THE DetHyp INHABITATION CHECK — predicted INHABITED
(det of the empty-index matrix = 1 ≠ 0; header resolution (3)).  Consequence,
recorded per the unit's duty: rsh_interp/legs_read are NOT hdet-vacuous at
this carrier.  If the prover instead finds DetHyp uninhabitable, record WHICH
law blocks and flip the H1b vacuity route accordingly. -/
theorem negDetHyp : MovesS.DetHyp negTable negRB negKmatHyp := by
  sorry

end LeanUrat.MovesV.W17iiNeg
