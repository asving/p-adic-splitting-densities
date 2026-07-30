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
    witness, where every equiv is `Equiv.refl` and the reads are literal. -/
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

/-- TV-G1 (i): THE SUPPLY — the ten stage fields read from the CTS letters'
species records through the `TablePins` equivs (candidate source map in the
file header; gate protocol binding).  Body = the gate's construction duty. -/
noncomputable def scsSupplyCore {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T) : SCSSupplyCore T :=
  sorry

/-- TV-G1 (ii): THE ROSTER-CARDINALITY CENSUS — the `memberOf` injection
demand of `MovesS.SCSData` (an injection `Fin flankCount ⊕ Fin (resFactors
.erase (g, μsel)).card → Fin mem.length` AVOIDING selIdx exists only if this
inequality holds); gated HERE, before TV-G3 may assert the construction.
FAILURE AT A REACHABLE OUTCOME = STOP + ESCALATE (never force). -/
theorem scs_roster_census {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      1 + (scsSupplyCore C T hp).flankCount e τ o
        + (((scsSupplyCore C T hp).resFactors e τ o).erase
            ((scsSupplyCore C T hp).g e τ o,
             (scsSupplyCore C T hp).μsel e τ o)).card
        ≤ (T.odata e τ o).mem.length := by
  sorry

end LeanUrat.MovesV
