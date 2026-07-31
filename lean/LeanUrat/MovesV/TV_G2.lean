/-  TV-G2 (BRIDGE BP3, cluster c2; E-phase skeleton) — the ALGEBRAIC LAWS of
    the SCSData supply at TV-G1's `scsSupplyCore`:
    ℓpos / window_comp / flank_zero / sel_mem / res_sum / stage_D / stage_W /
    cluster_parent.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §4 (TV-G2).
    deps: TV-G1 (the supply + the gate census; the gate's escalation exits
    bind here too — if a law fails at the sourced supply, STOP and escalate,
    never bend the supply to fake it).
    Statements mirror the corresponding `MovesS.SCSData` law fields
    (MovesS/Defs.lean:114-132) verbatim at the supply.
    Sketch (per the header source map of TV_G1.lean): ℓpos from the species
    WellTyped clause; window_comp from species coherence (G1)
    (W = s₀′ + e·ℓ + right-flank, lflank.sum = s₀′) MODULO the stride-vs-block
    census flag; flank_zero from the composition positivity (no parts ⟹ zero
    span); sel_mem/res_sum from (G4); stage_D/stage_W from the StageLaws
    D.5/D.8/D.10 outputs (D′ = e·g·D, W′ = μ); cluster_parent from skBlk's
    definition (e = sp.W · sp.D).

    QUEUE ITEM 15 EXECUTED (Asvin sign-off 2026-07-31; ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 15): every statement
    gains the ratified `SpeciesStageRow` parameter (the TV-G1 escalation row
    — the supply now READS it), and ALL EIGHT LAWS ARE PROVED: ℓpos/res_sum
    from `rec_coh` (WellTyped/(G4)); window_comp from (G1) + the row's
    `rec_stride` (the header-flagged stride-vs-block tension, now a named
    row law); flank_zero by composition collapse; sel_mem from the row's
    `sel_mem`; stage_D/stage_W rfl at the supply's StageLaws-output
    definitions; cluster_parent from the row's `rec_cluster`.  The G cluster
    opens: TV-G2 fully (8/8), TV-G1 fully (gate census proved); TV-G3's
    roster DATA (selIdx/memberOf + their four laws) remain open — see the
    TV_G3 record. -/
import LeanUrat.MovesV.TV_G1

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- TV-G2 law 1 (mirrors `SCSData.ℓpos`; source: the row's species coherence,
WellTyped clause 1 ≤ ℓ). -/
theorem scs_ℓpos {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      1 ≤ (scsSupplyCore C T hp R).ℓ e τ o := by
  intro e τ o
  exact (R.rec_coh e τ o).1.2.2.2.2.1

/-- TV-G2 law 2 (mirrors `SCSData.window_comp`).  The gate's stride-vs-block
census flag (TV_G1 header, duty (i)) lands exactly here — discharged by the
row's `rec_stride` law (species (G1): W = s₀′ + e·ℓ + right-flank with
lflank.sum = s₀′, at stride = block size). -/
theorem scs_window_comp {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (scsSupplyCore C T hp R).W e τ o
        = e * (scsSupplyCore C T hp R).ℓ e τ o
          + (scsSupplyCore C T hp R).flankWidth e τ o := by
  intro e τ o
  obtain ⟨-, ⟨hcomp, hspan, -⟩, -, -, -, -⟩ := R.rec_coh e τ o
  have hst := R.rec_stride e τ o
  have hls := hcomp.2
  show (R.spRec e τ o).W
      = e * (R.spRec e τ o).ell
        + ((R.spRec e τ o).lflank.sum + (R.spRec e τ o).rflank.sum)
  unfold MovesSp.Species.wraw at hspan
  rw [hst] at hspan
  omega

/-- TV-G2 law 3 (mirrors `SCSData.flank_zero`; no parts ⟹ zero span). -/
theorem scs_flank_zero {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (scsSupplyCore C T hp R).flankCount e τ o = 0 →
      (scsSupplyCore C T hp R).flankWidth e τ o = 0 := by
  intro e τ o h
  have hcount : (R.spRec e τ o).lflank.length + (R.spRec e τ o).rflank.length
      = 0 := h
  have h1 : (R.spRec e τ o).lflank = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have h2 : (R.spRec e τ o).rflank = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  show (R.spRec e τ o).lflank.sum + (R.spRec e τ o).rflank.sum = 0
  rw [h1, h2]
  simp

/-- TV-G2 law 4 (mirrors `SCSData.sel_mem`; source: the row's selection
membership — the (G6) terminal fallback is resolved inside the row). -/
theorem scs_sel_mem {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      ((scsSupplyCore C T hp R).g e τ o, (scsSupplyCore C T hp R).μsel e τ o)
        ∈ (scsSupplyCore C T hp R).resFactors e τ o := by
  intro e τ o
  exact R.sel_mem e τ o

/-- TV-G2 law 5 (mirrors `SCSData.res_sum`; source = the species (G4) clause
Σ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ — gate duty (iii)). -/
theorem scs_res_sum {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (((scsSupplyCore C T hp R).resFactors e τ o).map
          (fun x => x.1 * x.2)).sum
        = (scsSupplyCore C T hp R).ℓ e τ o := by
  intro e τ o
  exact (R.rec_coh e τ o).2.2.2.2.1.1

/-- TV-G2 law 6 (mirrors `SCSData.stage_D`; StageLaws output D′ = e·g·D —
rfl at the supply's defining read). -/
theorem scs_stage_D {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (scsSupplyCore C T hp R).D' e τ o
        = e * (scsSupplyCore C T hp R).g e τ o
          * (scsSupplyCore C T hp R).D e τ o := by
  intro e τ o
  rfl

/-- TV-G2 law 7 (mirrors `SCSData.stage_W`; StageLaws output W′ = μ — rfl at
the supply's defining read). -/
theorem scs_stage_W {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (scsSupplyCore C T hp R).W' e τ o
        = (scsSupplyCore C T hp R).μsel e τ o := by
  intro e τ o
  rfl

/-- TV-G2 law 8 (mirrors `SCSData.cluster_parent`; source = the row's
`rec_cluster` — the gate's duty-(iii) arithmetic law, carried as the named
hypothesis after the skBlk-vs-letter-record tension fired). -/
theorem scs_cluster_parent {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n)
    (hp : TablePins C T) (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      (scsSupplyCore C T hp R).W e τ o * (scsSupplyCore C T hp R).D e τ o
        = e := by
  intro e τ o
  exact R.rec_cluster e τ o

end LeanUrat.MovesV
