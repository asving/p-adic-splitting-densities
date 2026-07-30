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
    law L" with L named — record at both fence sites, never force.

    EXECUTION RECORD (prover pass, 2026-07-30): ALL SIX PIECES FILLED, module
    green under per-module `lake build`.  The concrete carriers: State e :=
    Fin 0 (the PEmpty genre, ℕ-friendly), VType := the forced (1,1) subtype
    singleton (vEquiv := Equiv.refl), Pools := the prime powers (the
    N2Carriers idiom verbatim), Box := Fin 1, Hgt := ℕ, activeState ≡ False
    (literally — and vacuously, per resolution (2)).  The DetHyp check
    CONFIRMED the predicted branch: det (1 − Kmat) = 1 ≠ 0 by
    `Matrix.det_isEmpty` at the empty state index — DetHyp INHABITED, so
    TV-H1b's rsh_interp/legs_read are NOT hdet-vacuous (and were discharged
    for real there). -/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV.W17iiNeg

/-- The n = 1 structural verdict carrier: the (e, f) pairs with e·f ≤ 1 —
a subsingleton (only (1,1) qualifies). -/
private abbrev negVType : Type := {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ 1}

private lemma negVType_bound (v : negVType) : (v.1.1 : ℕ) < 2 ∧ (v.1.2 : ℕ) < 2 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  have ha := a.pos
  have hb := b.pos
  simp only at h
  constructor <;> nlinarith [ha, hb, h]

private noncomputable instance : Fintype negVType :=
  Fintype.ofInjective
    (fun v : negVType => ((⟨(v.1.1 : ℕ), (negVType_bound v).1⟩ : Fin 2),
                          (⟨(v.1.2 : ℕ), (negVType_bound v).2⟩ : Fin 2)))
    (by
      intro v w hvw
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hvw
      exact Subtype.ext (Prod.ext (PNat.coe_injective hvw.1) (PNat.coe_injective hvw.2)))

/-- TV-H1a piece 1: the countermodel TABLE (n := 1; empty block states per
the header resolution; VType = the forced (1,1) verdict singleton). -/
noncomputable def negTable : MovesS.TableShape 1 where
  State := fun _ => Fin 0
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  VType := negVType
  deqV := inferInstance
  finV := inferInstance
  vdeg := fun v => v.1.1 * v.1.2
  vEquiv := Equiv.refl _
  vdeg_spec := fun v => PNat.mul_coe v.1.1 v.1.2
  Out := fun _ _ => Fin 0
  finO := fun _ _ => inferInstance
  odata := fun _ _ o => o.elim0
  Wloc := fun _ _ _ => 0
  Wstate := fun _ _ => 0

/-- TV-H1a piece 2: the degenerate MeasuredSide — Pools := the prime powers,
Box := a one-point carrier, Hgt := ℕ (infinite, so shDom can be infinite),
activeState ≡ False, entrance/cell fields empty-indexed. -/
noncomputable def negMS : MovesS.MeasuredSide negTable where
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
  Box := fun _ _ => Fin 1
  finB := fun _ _ => inferInstance
  boxpos := fun _ _ => ⟨0⟩
  Cell := fun _ _ => Fin 0
  finC := fun _ _ => inferInstance
  cellOut := fun _ _ c => c.elim0
  Rep := fun _ _ => PUnit
  rep_ne := fun _ _ _ => ⟨PUnit.unit⟩
  cellLvl := fun _ _ c => c.elim0
  cellInst := fun _ _ c => c.elim0
  Hgt := ℕ
  HDom := fun _ _ c => c.elim0
  gwt := fun _ _ c => c.elim0
  cellEvt := fun _ _ _ c => c.elim0
  μcell := fun _ _ _ c => c.elim0
  rowVal := fun _ _ o => o.elim0
  kstep := fun _ _ τ => τ.elim0
  activeState := fun _ _ _ => False
  decA := fun _ _ τ => τ.elim0
  EntShape := fun _ _ => Fin 0
  finE := fun _ _ => inferInstance
  hent := fun _ _ ε => ε.elim0
  Went := fun _ _ ε => ε.elim0
  entEvtH := fun _ _ ε => ε.elim0
  ιDom := fun _ _ ε => ε.elim0
  ιshH := fun _ _ ε => ε.elim0
  ιsh := fun _ _ ε => ε.elim0
  ιval := fun _ τ => τ.elim0
  entCount := fun _ _ ε => ε.elim0
  entLvl := fun _ _ ε => ε.elim0
  entInst := fun _ _ ε => ε.elim0
  markedVal := fun _ _ => 0

/-- TV-H1a pin: the blueprint's "activeState ≡ False" (at the adopted
carrier: vacuously — see header resolution (2)). -/
theorem negMS_inactive :
    ∀ (q₀ : ℚ) (e : ℕ) (τ : negTable.State e),
      ¬ negMS.activeState q₀ e τ :=
  fun _ _ τ => τ.elim0

/-- TV-H1a piece 3: the degenerate RatBurdens over (negTable, negMS) — every
per-τ field empty-indexed; act_iff vacuous at empty states (header (1)/(2)). -/
noncomputable def negRB : MovesS.RatBurdens negTable negMS where
  tgP := fun _ τ => τ.elim0
  jP := fun _ τ => τ.elim0
  ιP := fun _ τ => τ.elim0
  tg_ok := fun _ τ => τ.elim0
  j_ok := fun _ τ => τ.elim0
  ι_ok := fun _ τ => τ.elim0
  tg_interp := fun _ τ => τ.elim0
  j_interp := fun _ τ => τ.elim0
  ι_interp := fun _ τ => τ.elim0
  ι_countS_one := fun _ τ => τ.elim0
  ι_count := fun _ τ => τ.elim0
  tg_degT := fun _ τ => τ.elim0
  tg_degS := fun _ τ => τ.elim0
  j_degT := fun _ τ => τ.elim0
  j_degS := fun _ τ => τ.elim0
  ι_degT := fun _ τ => τ.elim0
  ι_degS := fun _ τ => τ.elim0
  cellP := fun _ τ => τ.elim0
  cellP_deg := fun _ τ => τ.elim0
  cellP_nonzero := fun _ _ τ => τ.elim0
  cellP_count := fun _ τ => τ.elim0
  act_iff := fun _ _ _ _ τ => τ.elim0
  jPCell := fun _ τ => τ.elim0
  jcell_ok := fun _ τ => τ.elim0
  jcell_interp := fun _ τ => τ.elim0
  jcell_sum := fun _ τ => τ.elim0

/-- TV-H1a piece 4: DegCons at the degenerate table (vacuous at empty
states) — an RS4Chain index. -/
theorem negDegCons : MovesS.DegCons negTable :=
  ⟨fun _ τ => τ.elim0, fun _ _ τ => τ.elim0⟩

/-- TV-H1a piece 5: KmatHyp on the block range (vacuous at empty states) —
an RS4Chain index. -/
theorem negKmatHyp : ∀ e, e ∈ Finset.Icc 1 1 → MovesS.KmatHyp negTable e :=
  fun _ _ τ => τ.elim0

/-- TV-H1a piece 6: THE DetHyp INHABITATION CHECK — predicted INHABITED
(det of the empty-index matrix = 1 ≠ 0; header resolution (3)).  Consequence,
recorded per the unit's duty: rsh_interp/legs_read are NOT hdet-vacuous at
this carrier.  If the prover instead finds DetHyp uninhabitable, record WHICH
law blocks and flip the H1b vacuity route accordingly. -/
theorem negDetHyp : MovesS.DetHyp negTable negRB negKmatHyp := by
  intro e he
  haveI : IsEmpty (negTable.State e) := ⟨fun τ => τ.elim0⟩
  rw [Matrix.det_isEmpty]
  exact one_ne_zero

end LeanUrat.MovesV.W17iiNeg
