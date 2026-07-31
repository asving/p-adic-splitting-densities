/-  TV-G3 (BRIDGE BP3, cluster c2; E-phase skeleton) — the ROSTER LAWS +
    ASSEMBLY: selIdx / memberOf / memberOf_inj / memberOf_ne_sel /
    sel_continuing / cluster_child at TV-G1's supply, then `scs_data_supply`
    discharged (T := tableShape_inst's witness, TablePins from it).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.F + §4 (TV-G3).
    deps: TV-G1 (the supply + the ROSTER-CARDINALITY CENSUS — this unit may
    NOT assert the roster construction until `scs_roster_census` is proved or
    the gate has escalated), TV-G2 (stage_D/stage_W feed cluster_child).
    Sketch: selIdx = the roster position from the `omem_sel`/`tcellM_sel`
    choice (the selected continuing member realizing the target skeleton);
    memberOf = the roster injection enumerating the flank members and the
    non-selected residual factors, avoiding selIdx (existence exactly the
    TV-G1 census); sel_continuing from `cont_iff` + the selected member's
    Sum.inr status → continuing flag (kcol routes are continuing:
    `kcol_route_c_ne`); cluster_child from `omem_size` (skBlk sk = mu.size)
    + TV-G2's stage_D/stage_W once (W′, D′) are read from the member's own
    record.  Assembly: package `scsSupplyCore` + the TV-G2 laws + the four
    roster laws into `Nonempty (MovesS.SCSData T)` at `tableShape_inst`'s
    witness.
    NOTE (no-existing-file rule): the sorried duty `scs_data_supply`
    (V7_scsData.lean:46) is byte-identical in statement to
    `scs_data_supply_pack` below; the prover fills the V7_scsData sorry from
    this pack (or inlines the same proof there) — this file adds the
    producer, it does not touch the existing declaration.

    QUEUE ITEM 15 RIPPLE RECORD (Asvin sign-off 2026-07-31; ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 15): the supply-
    reading statements below gain the ratified `SpeciesStageRow` parameter
    (TV-G1's escalation row).  G-CLUSTER OPENING REPORT (the item's charge):
    TV-G1 opens FULLY (supply constructed + census proved = the row's
    roster_card); TV-G2 opens FULLY (8/8 laws proved).  TV-G3 REMAINS OPEN —
    what each residual needs, exactly:
    (a) `scsSelIdx` (no supply parameter): the selected member's ROSTER
        POSITION.  In-corpus source = `omem_sel`/`tcellM_sel` through
        TablePins' odata (size, δ, status) list tie (V7_ts:63-67) — but the
        tie reaches the CTS roster only through hp's ∃-bound equivs; a
        faithful position read needs either a keyed row extension (a
        `selPos` field with a status tie, the SpeciesStageRow genre) or the
        hp-choice plumbing.  Left the named sorried duty.
    (b) `scsMemberOf` + inj/ne_sel: pure combinatorics ONCE selIdx is fixed
        (an embedding of `Fin fc ⊕ Fin rc` into the selIdx-complement, whose
        card bound IS `scs_roster_census`) — blocked only on (a); proving
        them against the sorried (a) would ride sorryAx for no content.
    (c) `scs_sel_continuing`: needs the kcol-route ⟹ selected-member-
        continuing read (cont_iff + the status tie) — same TablePins
        plumbing as (a).
    (d) `scs_cluster_child`: needs `omem_size` (skBlk sk = mu.size) at the
        selected member + the row's primed-field reads (stage_D/stage_W now
        proved, TV-G2) — blocked on (a) + a member-size tie through the
        keying (`key_roster` ties LENGTH only; the (size, δ, status)
        pointwise tie is the natural row extension).
    (e) `scs_data_supply_pack` (statement UNCHANGED — it does not read the
        supply): blocked on (a)-(d) + discharging a `SpeciesStageRow` at
        `tableShape_inst`'s witness (the row's Phase-B duty).  -/
import LeanUrat.MovesV.TV_G2

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- TV-G3 datum 1: the SELECTED-MEMBER position (mirrors `SCSData.selIdx`) —
the roster index from the `omem_sel`/`tcellM_sel` choice at continuing
outcomes; at terminal outcomes any position serves (sel_continuing is
kcol-guarded, and kcol outcomes are continuing).  [ITEM 15 record: stays the
named sorried duty — residual (a) in the header report.] -/
noncomputable def scsSelIdx {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    Fin (T.odata e τ o).mem.length :=
  sorry

/-- TV-G3 datum 2: the ROSTER INJECTION (mirrors `SCSData.memberOf`) — flank
members ⊕ non-selected residual factors → roster positions; its existence at
the sourced supply is EXACTLY TV-G1's `scs_roster_census` (gate-first
discipline: this def may be filled only after the census verdict).  [ITEM 15
record: census now PROVED (the row's roster_card); the construction is the
selIdx-complement embedding — blocked only on residual (a), see header.] -/
noncomputable def scsMemberOf {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp)
    (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    (Fin ((scsSupplyCore C T hp R).flankCount e τ o) ⊕
      Fin (((scsSupplyCore C T hp R).resFactors e τ o).erase
        ((scsSupplyCore C T hp R).g e τ o,
         (scsSupplyCore C T hp R).μsel e τ o)).card) →
    Fin (T.odata e τ o).mem.length :=
  sorry

/-- TV-G3 roster law 1 (mirrors `SCSData.memberOf_inj`).  [ITEM 15 record:
blocked on residual (a)/(b), see header.] -/
theorem scs_memberOf_inj {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      Function.Injective (scsMemberOf C T hp R e τ o) := by
  sorry

/-- TV-G3 roster law 2 (mirrors `SCSData.memberOf_ne_sel`).  [ITEM 15 record:
blocked on residual (a)/(b), see header.] -/
theorem scs_memberOf_ne_sel {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ) i,
      scsMemberOf C T hp R e τ o i ≠ scsSelIdx C T hp e τ o := by
  sorry

/-- TV-G3 roster law 3 (mirrors `SCSData.sel_continuing`): at kcol routes the
selected member is continuing — from `cont_iff` + the `omem_sel` member's
Sum.inr status through the TablePins roster tie.  [ITEM 15 record: blocked on
residual (c), see header.] -/
theorem scs_sel_continuing {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      MovesS.routeOf (T.odata e τ o) = .kcol →
      ((T.odata e τ o).mem.get (scsSelIdx C T hp e τ o)).continuing := by
  sorry

/-- TV-G3 roster law 4 (mirrors `SCSData.cluster_child`): the selected
continuing member's size is the child cluster W′·D′ — from `omem_size`
(skBlk sk = mu.size) + TV-G2's stage_D/stage_W.  [ITEM 15 record: blocked on
residual (d), see header.] -/
theorem scs_cluster_child {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ)
      (i : Fin (T.odata e τ o).mem.length),
      ((T.odata e τ o).mem.get i).continuing →
      i = scsSelIdx C T hp e τ o →
      ((T.odata e τ o).mem.get i).size
        = (scsSupplyCore C T hp R).W' e τ o
          * (scsSupplyCore C T hp R).D' e τ o := by
  sorry

/-- TV-G3 ASSEMBLY: the `scs_data_supply` producer — statement byte-identical
to the named open duty at MovesV/V7_scsData.lean:41-46 (premise row (C, hfin);
conclusion ∃ T, TablePins ∧ Nonempty (SCSData T)).  Proof sketch: T :=
`tableShape_inst`'s witness with its proved TablePins; SCSData from
`scsSupplyCore` + the TV-G2 laws + the four roster laws above.  The existing
sorried `scs_data_supply` is then discharged from this pack by the prover
(that fill is the ONLY edit to the existing file, made at prover phase).
[ITEM 15 record: statement UNCHANGED (it does not read the supply); blocked
on residuals (a)-(d) + the row's Phase-B discharge at the witness — header
residual (e).] -/
theorem scs_data_supply_pack {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      TablePins C T ∧
      Nonempty (MovesS.SCSData T) := by
  sorry

end LeanUrat.MovesV
