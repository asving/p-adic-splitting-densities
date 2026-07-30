/-  MovesV unit V4-6b `part1_null` · HARD — the 1 ≤ v lower bound via the
    restored leg-(d) `fh_exact` equality at H = 0.
    [TITLE CORRECTED 2026-07-30 (verify-2 fold-in, A20): the E-phase title
    credited "the remainder-null limit from leg (c) + the monotone assembly
    bound", but the proof below consumes ONLY `hd.fh_exact` — neither `hb`
    (P1CtblAdd) nor `hc` (P1NullRem, leg (c)) is used; the dead leg-(c)
    threading part1_null → part1 → part2_row/part2_ge → ctsM is a
    statement-fence matter, queued for sign-off in
    GOLF_CAMPAIGN_2026-07-30.md.]
    PROVED 2026-07-30 after the ADJUDICATED leg-(d) repair: the restored
    `fh_exact` equality (V4_part1A — the blueprint V4 PART-1 row's "(d) each
    fixed-height block sums by C.1.5(1)'s conditional exactness", dropped by
    DEV D15's headline form; countermodel `μcellH ≡ 0` on file with the
    fleet) pins the below-H blocks + H-strip total to 1 at every truncation;
    at H = 0 the below-strip is empty and the strip is the whole partition,
    so the assembled value is exactly 1. -/
import LeanUrat.MovesV.V4_part1A

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem part1_null {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (v : ℝ) (hv : HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) v) :
    1 ≤ v := by
  have hex := hd.fh_exact x hzc hq hact 0
  -- the below-0 head is a sum over the empty subtype
  haveI hempty : IsEmpty {ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D //
      (∑ i, ch.2.2 i) < 0} := ⟨fun ch => Nat.not_lt_zero _ ch.2⟩
  rw [tsum_empty, zero_add] at hex
  -- the 0-strip is the whole partition
  have htail : (∑' ch : {ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D //
      0 ≤ ∑ i, ch.2.2 i}, μcellH V X x ch.1.1 ch.1.2) = v := by
    rw [← hv.tsum_eq]
    exact (Equiv.subtypeUnivEquiv (fun ch => Nat.zero_le _)).tsum_eq
      (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D => μcellH V X x ch.1 ch.2)
  rw [htail] at hex
  exact hex.ge
end LeanUrat.MovesV
