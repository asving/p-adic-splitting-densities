/-  TV-G1 (BRIDGE BP3, cluster c2; E-phase skeleton) — [GATE, runs BEFORE
    TV-G3 may assert the roster construction] the SCSData DATA SUPPLY over the
    pinned table + the widened gate census (blueprint REV 2, findings 5 + 10).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.F + §4 (TV-G1).
    deps: none.  Consumers: TV-G2 (algebraic laws), TV-G3 (roster laws +
    assembly of `scs_data_supply`).

    GATE DUTIES (the sealed protocol; deliverables (i)-(iii)):
    (i) TEN-FIELD SOURCE MAP — verify the CTS letters' species/catalogue
      records reach all ten SCSData data fields (W, D, ℓ, g, μsel, W′, D′,
      flankCount, flankWidth, resFactors).  CANDIDATE MAP (typing-time read of
      MovesSp.Species at MovesSp/Defs.lean:37 + BlockData at MovesV/Defs.lean
      :226): per (e, τ, o) with source skeleton s := τ's skeleton and letter m,
      W/D := s.sp.W / s.sp.D (so cluster_parent W·D = e is skBlk's own
      definition, MovesV/Defs.lean:216); ℓ/g/μsel/resFactors/flanks from the
      species record reached through `letterSp m` (Sum.inl case): sp.ell,
      sp.sel (the Option (g, μ) selection; (G6) sel = none ↔ W = 1 covers the
      terminal-letter fallback — pick any lam member, lam ≠ ∅ whenever
      Coherent since (G4) forces Σ g·μ = ℓ ≥ 1), sp.lam,
      sp.lflank.length + sp.rflank.length / sp.lflank.sum + sp.rflank.sum;
      `tgt_sp` ties the letter to the TARGET species for the primed fields
      (W′ = μsel, D′ = e·g·D — the StageLaws D.5/D.8/D.10 outputs).
      FLAGGED FOR THE CENSUS (typing-time tension, recorded): window_comp
      (W = e·ℓ + flankWidth) reads the TABLE block size e = skBlk s = W·D,
      while a species' own coherence (G1) gives sp.W = sp.e·sp.ell + flanks at
      the species STRIDE sp.e — the census must verify stride = block size
      (sp.e = skBlk s) at every reachable catalogue member, or re-source
      W/ℓ/flanks from the member whose stride matches.
    (ii) ROSTER-CARDINALITY CENSUS (the memberOf injection demand, §3.F REV 2):
      per outcome, mem.length ≥ 1 + flankCount + (resFactors.erase (g, μsel)).card
      — stated as `scs_roster_census` below; a field-reachability check does
      NOT certify this.
    (iii) ARITHMETIC-LAW SOURCES for cluster_parent (W·D = e) and res_sum
      (Σ g·μ over resFactors = ℓ) — candidate sources: skBlk's definition and
      the species (G4) clause; the law statements themselves are TV-G2's.

    ESCALATION EXIT (risk R6, binding): IF any field lacks a CTS/MovesSp
    source OR the roster census FAILS at a reachable outcome, the prover
    STOPS and escalates to adjudication (a named hypothesis row supplying the
    species stage record — the M1-failure-mode-safe form); data are NEVER
    invented (the recorded trivial-supply failure shows free data cannot fake
    sel_continuing/cluster_child).  If (ii) fails, `scs_data_supply` may be
    FALSE for this supply genre: stop and escalate, never force.

    RESOLUTION (recorded): "define the supply over tableShape_inst's table" is
    realized PARAMETRICALLY over any pinned pair (T, hp : TablePins C T) — the
    pins carry exactly the equivs/roster ties the supply reads through
    (V7_ts.lean:56); the TV-G3 assembly instantiates at `tableShape_inst`'s
    witness, where every equiv is `Equiv.refl` and the reads are literal.

    QUEUE ITEM 15 EXECUTED (Asvin sign-off 2026-07-31; ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 15 — the round-3
    escalation of THIS file's R6 exit): the gate's escalation FIRED — the
    header's own census flags are the obstruction (the stride-vs-block
    tension at window_comp; cluster_parent's W·D = e at the LETTER record;
    the roster-cardinality demand), none sourceable from typing alone — so
    the adjudicated NAMED HYPOTHESIS ROW `SpeciesStageRow` below now
    supplies the species-stage record per outcome, read through a recorded
    keying (E-DEV-9/SeamKeys precedent).  ANTI-VACUITY (trivial fills
    forbidden): `rec_read` pins the record to the CTS letter's own
    `letterSp` species at continuing keys (the §3.F source map's read;
    `tgt_sp` makes it the target species), and `key_roster` pins the
    roster read; a free-floating record cannot satisfy them against a real
    C.  NOT TIED (boundary-record rule): the key's agreement with
    TablePins' own equivs (the hp-faithfulness of `key` itself is the
    Phase-B discharge duty, exactly as SeamKeys' pins constrain-not-
    determine), and the record at TERMINAL keys (letterSp = Sum.inr — no
    species source exists in-corpus; the row's laws still bind there).
    `scsSupplyCore` + `scs_roster_census` are now PROVED under the row;
    the row's own discharge at the real catalogue is Phase B. -/
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- TV-G1 carrier: the ten SCSData DATA fields (laws excluded — TV-G2/G3's),
typed in the consuming unit per the E-DEV-9 pattern.  Field names and types
mirror `MovesS.SCSData` (MovesS/Defs.lean:97) verbatim. -/
structure SCSSupplyCore {n : ℕ} (T : MovesS.TableShape n) where
  W : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D : ∀ e (τ : T.State e), T.Out e τ → ℕ
  ℓ : ∀ e (τ : T.State e), T.Out e τ → ℕ
  g : ∀ e (τ : T.State e), T.Out e τ → ℕ
  μsel : ∀ e (τ : T.State e), T.Out e τ → ℕ
  W' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankCount : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankWidth : ∀ e (τ : T.State e), T.Out e τ → ℕ
  resFactors : ∀ e (τ : T.State e), T.Out e τ → Multiset (ℕ × ℕ)

/-- TV-G1 THE NAMED HYPOTHESIS ROW (queue item 15; the file header's R6
escalation exit executed): the species-stage record per table outcome, read
through a recorded keying into the CTS (skeleton, letter, outcome) triples.
DATA: `rec` the species-stage record; `sel` the selected residual factor
(g, μ) — the (G6) terminal fallback resolved in-row; `key` the outcome
keying.  FAITHFULNESS TIES: `rec_read` (the record IS the letter's
`letterSp` species at continuing keys) + `key_roster` (the roster-length
read).  CENSUS LAWS (the gate's three unsourceable duties, carried as the
adjudicated hypotheses): `rec_coh` (species coherence), `rec_stride`
(stride = block size — the header's flagged tension), `rec_cluster`
(cluster_parent's W·D = e at the record), `sel_mem` (selection membership),
`roster_card` (the memberOf injection demand).  Phase B discharges the row
at the real catalogue; trivial fills cannot pass `rec_read`/`key_roster`
against a real C (recorded in the header). -/
structure SpeciesStageRow {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T) where
  key : ∀ e (τ : T.State e), T.Out e τ →
    Σ s : Skeleton n, Σ m : (C.bd s).Letter, (C.bd s).Outc m
  spRec : ∀ e (τ : T.State e), T.Out e τ → MovesSp.Species
  sel : ∀ e (τ : T.State e), T.Out e τ → ℕ × ℕ
  rec_read : ∀ e (τ : T.State e) (o : T.Out e τ),
    (C.bd (key e τ o).1).cont (key e τ o).2.1 (key e τ o).2.2 →
    (C.bd (key e τ o).1).letterSp (key e τ o).2.1 = Sum.inl (spRec e τ o)
  key_roster : ∀ e (τ : T.State e) (o : T.Out e τ),
    (T.odata e τ o).mem.length
      = ((C.bd (key e τ o).1).omem (key e τ o).2.1 (key e τ o).2.2).length
  rec_coh : ∀ e (τ : T.State e) (o : T.Out e τ), MovesSp.Coherent (spRec e τ o)
  rec_stride : ∀ e (τ : T.State e) (o : T.Out e τ), (spRec e τ o).e = e
  rec_cluster : ∀ e (τ : T.State e) (o : T.Out e τ),
    (spRec e τ o).W * (spRec e τ o).D = e
  sel_mem : ∀ e (τ : T.State e) (o : T.Out e τ), sel e τ o ∈ (spRec e τ o).lam
  roster_card : ∀ e (τ : T.State e) (o : T.Out e τ),
    1 + ((spRec e τ o).lflank.length + (spRec e τ o).rflank.length)
      + ((spRec e τ o).lam.erase (sel e τ o)).card
      ≤ (T.odata e τ o).mem.length

/-- TV-G1 (i): THE SUPPLY — the ten stage fields read from the species-stage
record row (queue item 15: the row parameter is the ratified statement
change; the old row-free form had no CTS source for the census duties and
its body was the gate's STOP).  The primed fields are DEFINED by the
StageLaws outputs (W′ = μsel, D′ = e·g·D), making TV-G2's stage_D/stage_W
rfl-genre. -/
def scsSupplyCore {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) : SCSSupplyCore T where
  W := fun e τ o => (R.spRec e τ o).W
  D := fun e τ o => (R.spRec e τ o).D
  ℓ := fun e τ o => (R.spRec e τ o).ell
  g := fun e τ o => (R.sel e τ o).1
  μsel := fun e τ o => (R.sel e τ o).2
  W' := fun e τ o => (R.sel e τ o).2
  D' := fun e τ o => e * (R.sel e τ o).1 * (R.spRec e τ o).D
  flankCount := fun e τ o =>
    (R.spRec e τ o).lflank.length + (R.spRec e τ o).rflank.length
  flankWidth := fun e τ o =>
    (R.spRec e τ o).lflank.sum + (R.spRec e τ o).rflank.sum
  resFactors := fun e τ o => (R.spRec e τ o).lam

/-- TV-G1 (ii): THE ROSTER-CARDINALITY CENSUS — the `memberOf` injection
demand of `MovesS.SCSData` (an injection `Fin flankCount ⊕ Fin (resFactors
.erase (g, μsel)).card → Fin mem.length` AVOIDING selIdx exists only if this
inequality holds); gated HERE, before TV-G3 may assert the construction.
[ITEM 15: PROVED under the row — the census IS the row's `roster_card`.] -/
theorem scs_roster_census {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      1 + (scsSupplyCore C T hp R).flankCount e τ o
        + (((scsSupplyCore C T hp R).resFactors e τ o).erase
            ((scsSupplyCore C T hp R).g e τ o,
             (scsSupplyCore C T hp R).μsel e τ o)).card
        ≤ (T.odata e τ o).mem.length :=
  fun e τ o => R.roster_card e τ o

end LeanUrat.MovesV
