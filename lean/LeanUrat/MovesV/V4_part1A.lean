/-  MovesV unit V4-6a `part1_ctbl` (suite V4-6, REV 4 Codex-16) — the
    countable-partition HasSum from legs (a)/(b)/(d).  The NAME→HOME defs
    `DCellAll`/`cdomAllMem`/`μcellH` + the leg carriers.  [E-PHASE NOTE: the
    leg structures land in HEADLINE form (full field-by-field typing = prover
    duty) — MANIFEST deviations.] -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the all-outcomes digit-cell Σ-carrier at a source (IS `CellOf`). -/
def DCellAll {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (τ : S.Cell) : Type := V.CellOf τ

/-- the Σ-embedded listed domain of an all-outcomes cell. -/
def cdomAllMem {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {τ : S.Cell} :
    DCellAll V τ → (Σ D : ℕ, Hpt D) → Prop
  | .inl ⟨d, c⟩, ⟨D, h⟩ =>
      ∃ e : D = S.dim (V.moveOf d.1), (V.cdom d.1 c).Mem (castHpt e h)
  | .inr ⟨_, d, c⟩, ⟨D, h⟩ =>
      ∃ e : D = S.dimT (V.moveOfT d.1), (V.cdomT d.1 c).Mem (castHpt e h)

open Classical in
/-- the per-(cell, height) conditional mass (count × XHD-w monomial). -/
noncomputable def μcellH {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) :
    DCellAll V τ → (Σ D : ℕ, Hpt D) → ℝ
  | .inl ⟨d, c⟩, ⟨D, h⟩ =>
      if e : D = S.dim (V.moveOf d.1) then
        (V.cntc d.1 (cast (congrArg (S.Hist q₀) d.2.symm) x) c (castHpt e h) : ℝ)
          * (q₀ : ℝ) ^ (-(((X.E (V.moveOf d.1)).eval (castHpt e h) : ℕ) : ℤ))
      else 0
  | .inr ⟨_, d, c⟩, ⟨D, h⟩ =>
      if e : D = S.dimT (V.moveOfT d.1) then
        (V.cntcT d.1 (cast (congrArg (S.Hist q₀) d.2.symm) x) c (castHpt e h) : ℝ)
          * (q₀ : ℝ) ^ (-(((X.ET (V.moveOfT d.1)).eval (castHpt e h) : ℕ) : ℤ))
      else 0

/-- leg (b) COUNTABLE ADDITIVITY (headline form). -/
structure P1CtblAdd {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) : Prop where
  ctbl_add : ∀ {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ), S.zc x →
    q₀ ∈ V.Pools → V.activeState q₀ τ →
    Summable (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2)

/-- leg (c) NULL REMAINDER (headline form: the strip masses tend to 0). -/
structure P1NullRem {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) : Prop where
  null_rem : ∀ {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ), S.zc x →
    q₀ ∈ V.Pools → V.activeState q₀ τ →
    Filter.Tendsto (fun H : ℕ =>
      ∑' ch : {ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D //
          H ≤ ∑ i, ch.2.2 i}, μcellH V X x ch.1.1 ch.1.2)
      Filter.atTop (nhds 0)

/-- leg (d) FIXED-HEIGHT EXACTNESS (C.1.5(1)'s conditional exactness per
fixed-height block; the partial sums are bounded by 1).
ADJUDICATED STATEMENT REPAIR 2026-07-30: the E-phase headline form (DEV D15)
had dropped the EXACTNESS EQUALITY and kept only the upper bounds — the
prover fleet's countermodel: `μcellH ≡ 0` satisfies all three legs while
`part1_null`'s `1 ≤ v` fails.  The equality field `fh_exact` is RESTORED per
the blueprint V4 PART-1 row (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V4-6a/b/c):
"(d) each fixed-height block sums by C.1.5(1)'s conditional exactness"
(moves_ref V.3(iv): "together, the per-cell ratios over the whole partition
sum to 1 … mass 1 is NOT a finite-pool identity") — typed at leg (c)'s own
strip display: at EVERY truncation height H, the below-H fixed-height blocks
PLUS the H-strip (the identical `∑'`-tail leg (c) sends to 0) carry exactly
the unit conditional mass.  `fh_bound` (the monotone assembly bound
`part1_ctbl` consumes) is kept. -/
structure P1FixedHeightExact {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) : Prop where
  fh_bound : ∀ {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ), S.zc x →
    q₀ ∈ V.Pools → V.activeState q₀ τ →
    ∀ s : Finset (Σ c : DCellAll V τ, Σ D : ℕ, Hpt D),
      ∑ ch ∈ s, μcellH V X x ch.1 ch.2 ≤ 1
  fh_exact : ∀ {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ), S.zc x →
    q₀ ∈ V.Pools → V.activeState q₀ τ →
    ∀ H : ℕ,
      (∑' ch : {ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D //
          (∑ i, ch.2.2 i) < H}, μcellH V X x ch.1.1 ch.1.2)
        + (∑' ch : {ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D //
            H ≤ ∑ i, ch.2.2 i}, μcellH V X x ch.1.1 ch.1.2) = 1

theorem part1_ctbl {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ) :
    ∃ v : ℝ, v ≤ 1 ∧ HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) v := by
  exact ⟨∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D, μcellH V X x ch.1 ch.2,
    (hb.ctbl_add x hzc hq hact).tsum_le_of_sum_le (hd.fh_bound x hzc hq hact),
    (hb.ctbl_add x hzc hq hact).hasSum⟩

end LeanUrat.MovesV
