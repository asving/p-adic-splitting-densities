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
        `tableShape_inst`'s witness (the row's Phase-B duty).

    TV-G3 RESIDUALS PASS (tv-g3-residuals, 2026-07-31; every fenced
    statement byte-unchanged, new leaves only):
    (a) FILLED — by the item-15 record's hp-CHOICE PLUMBING option (NO row
        extension): `tpHv`/`tpHst`/`tpSk`/`tpHout`/`tpTie`/`tpLen` extract
        `TablePins`' ∃-bound equivs by `Exists.choose`; `scsSelIdx` is the
        chosen index of `scsSelIdx_exists`, whose spec carries BOTH the
        kcol-continuing clause (= residual (c)) AND the faithful selected-
        member tie: at continuing hp-keys the position holds the
        `tcellM_sel` selected member (CTS status `Sum.inr tgtSk`), read
        through the pointwise roster tie (`tpPt`/`tpIsRight`/`tpSize`).
    (b) FILLED — `scsMemberOf` = the value-level skip-selIdx embedding
        (k ↦ k / k+1 across `finSumFinEquiv`), total by the PROVED census
        `scs_roster_census`; `scs_memberOf_inj`/`scs_memberOf_ne_sel` from
        the value law `scs_memberOf_val` + omega.
    (c) FILLED — `scs_sel_continuing` = the spec's clause 1 (kcol forces
        `cont` at the hp-key via `tpContOfKcol`; the selected member's
        `Sum.inr` status rides back through `tpIsRight`).
    (d) STAYS OPEN, residue now COMPILED: `scs_cluster_child_of_selStage`
        proves the law from ONE hypothesis `hselStage` —
          (R.sel e τ o).2 * (e * (R.sel e τ o).1 * (R.spRec e τ o).D)
            = skBlk (tgtSk at the hp-key)   at continuing hp-keys —
        everything else (cont from the continuing member, the clause-2
        status pin, `omem_size`, the size transport) is PROVED.  NOT
        derivable from the landed row: `rec_read`/`rec_cluster` tie `spRec`
        at `R.key` only; nothing ties `sel`'s stage output to `hp`'s keyed
        target.  PROPOSED FENCE ITEM (exact `SpeciesStageRow` field):
          sel_stage : ∀ e (τ : T.State e) (o : T.Out e τ)
            (hc : (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2),
            (sel e τ o).2 * (e * (sel e τ o).1 * (spRec e τ o).D)
              = skBlk ((C.bd (tpSk C T hp e τ)).tgtSk
                  (tpHout C T hp e τ o).1 (tpHout C T hp e τ o).2 hc)
        (then scs_cluster_child := scs_cluster_child_of_selStage C T hp R
        (R.sel_stage) — a one-line fill once the row grows the field).
    (e) STAYS PHASE-B (needs (d) + a `SpeciesStageRow` discharged at
        `tableShape_inst`'s witness — the wave-D duty).  -/
import LeanUrat.MovesV.TV_G2

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-! ### tv-g3-residuals plumbing (2026-07-31): the TablePins choice extraction

Residual (a)'s recorded second route — NO row extension: `TablePins` is an
∃-bundle, so its equivs are extracted by `Exists.choose`; the selected-member
position is then read from `C.tcellM_sel` at the keyed CTS outcome and
transported through the roster tie.  New leaves only; every fenced statement
below is byte-unchanged. -/

section TpPlumbing

variable {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n) (hp : TablePins C T)

/-- [(a) plumbing] the VType equiv extracted from `hp` by choice. -/
noncomputable def tpHv : T.VType ≃ VLabel n := Exists.choose hp

/-- [(a) plumbing] the per-block state equiv extracted from `hp` by choice. -/
noncomputable def tpHst : ∀ e, T.State e ≃ StateOf n C e :=
  (Exists.choose_spec hp).choose

/-- [(a) plumbing] the (e, τ) block's source skeleton under `hp`'s keying. -/
noncomputable def tpSk (e : ℕ) (τ : T.State e) : Skeleton n :=
  ((tpHst C T hp e) τ).1.1

/-- [(a) plumbing] the per-(e, τ) outcome equiv extracted from `hp` by choice. -/
noncomputable def tpHout (e : ℕ) (τ : T.State e) :
    T.Out e τ ≃ Σ m : (C.bd (tpSk C T hp e τ)).Letter,
      (C.bd (tpSk C T hp e τ)).Outc m :=
  ((Exists.choose_spec hp).choose_spec.2 e τ).choose

/-- [(a) plumbing] the odata ↔ omem roster tie at `hp`'s extracted choices
(the `TablePins` member-list clause, keyed by `tpHout`). -/
theorem tpTie (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    (T.odata e τ o).mem.map (fun μ =>
        (μ.size, μ.δ, Sum.map (tpHv C T hp)
          (fun σ => ((tpHst C T hp μ.size) σ).1.1) μ.status))
      = ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
            (tpHout C T hp e τ o).2).map
          (fun mu => (mu.size, mu.δ, mu.status)) :=
  ((Exists.choose_spec hp).choose_spec.2 e τ).choose_spec.2 o

/-- [(a) plumbing] the roster-length tie at `hp`'s extracted choices. -/
theorem tpLen (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    (T.odata e τ o).mem.length
      = ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2).length := by
  have h := congrArg List.length (tpTie C T hp e τ o)
  simpa using h

/-- [(a) plumbing] the pointwise (size, δ, status) tie at `hp`'s choices. -/
theorem tpPt (e : ℕ) (τ : T.State e) (o : T.Out e τ) (j : ℕ)
    (hj : j < (T.odata e τ o).mem.length)
    (hj' : j < ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
        (tpHout C T hp e τ o).2).length) :
    (((T.odata e τ o).mem[j]'hj).size, ((T.odata e τ o).mem[j]'hj).δ,
        Sum.map (tpHv C T hp)
          (fun σ => ((tpHst C T hp ((T.odata e τ o).mem[j]'hj).size) σ).1.1)
          ((T.odata e τ o).mem[j]'hj).status)
      = ((((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2)[j]'hj').size,
         (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2)[j]'hj').δ,
         (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2)[j]'hj').status) := by
  have h := congrArg (fun l => l[j]?) (tpTie C T hp e τ o)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj', Option.map_some] at h
  exact Option.some.inj h

/-- [(a) plumbing] isRight (continuing-flag) transfer across the tie. -/
theorem tpIsRight (e : ℕ) (τ : T.State e) (o : T.Out e τ) (j : ℕ)
    (hj : j < (T.odata e τ o).mem.length)
    (hj' : j < ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
        (tpHout C T hp e τ o).2).length) :
    (((T.odata e τ o).mem[j]'hj).status).isRight
      = ((((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
            (tpHout C T hp e τ o).2)[j]'hj').status).isRight := by
  have h := congrArg (fun t : ℕ × ℕ+ × (VLabel n ⊕ Skeleton n) => t.2.2.isRight)
    (tpPt C T hp e τ o j hj hj')
  simpa [Sum.isRight_map] using h

/-- [(a) plumbing] size transfer across the tie. -/
theorem tpSize (e : ℕ) (τ : T.State e) (o : T.Out e τ) (j : ℕ)
    (hj : j < (T.odata e τ o).mem.length)
    (hj' : j < ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
        (tpHout C T hp e τ o).2).length) :
    ((T.odata e τ o).mem[j]'hj).size
      = (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2)[j]'hj').size := by
  have h := congrArg (fun t : ℕ × ℕ+ × (VLabel n ⊕ Skeleton n) => t.1)
    (tpPt C T hp e τ o j hj hj')
  simpa using h

/-- [(a)/(c) plumbing] a kcol route at the table forces `cont` at the hp-key:
kcol means c ≥ 1, the tie transfers some member's isRight flag into the CTS
roster, and `cont_iff` closes. -/
theorem tpContOfKcol (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : MovesS.routeOf (T.odata e τ o) = .kcol) :
    (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2 := by
  have hc : (T.odata e τ o).c ≠ 0 := by
    intro h0
    unfold MovesS.routeOf at hk
    rw [if_pos h0] at hk
    exact MovesS.Route.noConfusion hk
  have hne : (T.odata e τ o).mem.filter (fun μ => μ.status.isRight) ≠ [] := by
    intro hnil
    exact hc (by unfold MovesS.Outcome.c; rw [hnil]; rfl)
  obtain ⟨μ, hμ⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hmem, hright⟩ := List.mem_filter.mp hμ
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hj' : j < ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2).length := by
    rw [← tpLen C T hp e τ o]; exact hj
  refine ((C.bd (tpSk C T hp e τ)).cont_iff _ _).mpr
    ⟨_, List.getElem_mem hj', ?_⟩
  rw [← tpIsRight C T hp e τ o j hj hj', hget]
  exact hright

/-- [(a) THE SPEC] the selected-member position EXISTS with both clauses:
clause 1 = residual (c)'s demand (kcol ⟹ the member at the position is
continuing); clause 2 = the FAITHFUL TIE (at continuing hp-keys the position
holds the `tcellM_sel` selected member: CTS status `Sum.inr tgtSk`).  Source:
`C.tcellM_sel` at the keyed outcome, cast through `tpLen`; at non-continuing
keys position 0 serves (kcol would force `cont` via `tpContOfKcol`). -/
theorem scsSelIdx_exists (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    ∃ i : Fin (T.odata e τ o).mem.length,
      (MovesS.routeOf (T.odata e τ o) = .kcol →
        ((T.odata e τ o).mem.get i).continuing) ∧
      (∀ hc : (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2,
        (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2).get
            (Fin.cast (tpLen C T hp e τ o) i)).status
          = Sum.inr ((C.bd (tpSk C T hp e τ)).tgtSk (tpHout C T hp e τ o).1
              (tpHout C T hp e τ o).2 hc)) := by
  by_cases hcont : (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2
  · obtain ⟨i0, hs, -⟩ := C.tcellM_sel (tpSk C T hp e τ)
      (tpHout C T hp e τ o).1 (tpHout C T hp e τ o).2 hcont
    have hi0 : (i0 : ℕ) < (T.odata e τ o).mem.length := by
      rw [tpLen C T hp e τ o]; exact i0.isLt
    refine ⟨⟨(i0 : ℕ), hi0⟩, ?_, ?_⟩
    · intro _
      have hj' : (i0 : ℕ) < ((C.bd (tpSk C T hp e τ)).omem
          (tpHout C T hp e τ o).1 (tpHout C T hp e τ o).2).length := i0.isLt
      change ((T.odata e τ o).mem[(i0 : ℕ)]'hi0).status.isRight = true
      rw [tpIsRight C T hp e τ o (i0 : ℕ) hi0 hj']
      change (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2).get i0).status.isRight = true
      rw [hs]
      rfl
    · intro hc'
      have hcast : Fin.cast (tpLen C T hp e τ o) ⟨(i0 : ℕ), hi0⟩ = i0 := rfl
      rw [hcast]
      exact hs
  · refine ⟨⟨0, List.length_pos_of_ne_nil (T.odata e τ o).hm⟩, ?_,
      fun hc' => absurd hc' hcont⟩
    intro hk
    exact absurd (tpContOfKcol C T hp e τ o hk) hcont

end TpPlumbing

/-- TV-G3 datum 1: the SELECTED-MEMBER position (mirrors `SCSData.selIdx`) —
the roster index from the `omem_sel`/`tcellM_sel` choice at continuing
outcomes; at terminal outcomes any position serves (sel_continuing is
kcol-guarded, and kcol outcomes are continuing).  [ITEM 15 record: stays the
named sorried duty — residual (a) in the header report.] -/
noncomputable def scsSelIdx {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    Fin (T.odata e τ o).mem.length :=
  (scsSelIdx_exists C T hp e τ o).choose

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
  fun i =>
    ⟨if (finSumFinEquiv i : ℕ) < (scsSelIdx C T hp e τ o : ℕ)
        then (finSumFinEquiv i : ℕ)
        else (finSumFinEquiv i : ℕ) + 1, by
      have hcen := scs_roster_census C T hp R e τ o
      have hk := (finSumFinEquiv i).isLt
      have hx := (scsSelIdx C T hp e τ o).isLt
      split_ifs <;> omega⟩

/-- [(b) value law — tv-g3-residuals leaf] `scsMemberOf`'s underlying value is
the skip-`scsSelIdx` embedding k ↦ (k below the selected position, k+1 at or
above it), across `finSumFinEquiv`. -/
theorem scs_memberOf_val {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp)
    (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (i : Fin ((scsSupplyCore C T hp R).flankCount e τ o) ⊕
      Fin (((scsSupplyCore C T hp R).resFactors e τ o).erase
        ((scsSupplyCore C T hp R).g e τ o,
         (scsSupplyCore C T hp R).μsel e τ o)).card) :
    (scsMemberOf C T hp R e τ o i : ℕ)
      = if (finSumFinEquiv i : ℕ) < (scsSelIdx C T hp e τ o : ℕ)
          then (finSumFinEquiv i : ℕ)
          else (finSumFinEquiv i : ℕ) + 1 := rfl

/-- TV-G3 roster law 1 (mirrors `SCSData.memberOf_inj`).  [ITEM 15 record:
blocked on residual (a)/(b), see header.] -/
theorem scs_memberOf_inj {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      Function.Injective (scsMemberOf C T hp R e τ o) := by
  intro e τ o a b hab
  have h := congrArg Fin.val hab
  rw [scs_memberOf_val C T hp R e τ o a,
    scs_memberOf_val C T hp R e τ o b] at h
  have hv : (finSumFinEquiv a : ℕ) = (finSumFinEquiv b : ℕ) := by
    split_ifs at h <;> omega
  exact finSumFinEquiv.injective (Fin.ext hv)

/-- TV-G3 roster law 2 (mirrors `SCSData.memberOf_ne_sel`).  [ITEM 15 record:
blocked on residual (a)/(b), see header.] -/
theorem scs_memberOf_ne_sel {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp) :
    ∀ e (τ : T.State e) (o : T.Out e τ) i,
      scsMemberOf C T hp R e τ o i ≠ scsSelIdx C T hp e τ o := by
  intro e τ o i hcontra
  have h := congrArg Fin.val hcontra
  rw [scs_memberOf_val C T hp R e τ o i] at h
  split_ifs at h <;> omega

/-- TV-G3 roster law 3 (mirrors `SCSData.sel_continuing`): at kcol routes the
selected member is continuing — from `cont_iff` + the `omem_sel` member's
Sum.inr status through the TablePins roster tie.  [ITEM 15 record: blocked on
residual (c), see header.] -/
theorem scs_sel_continuing {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T) :
    ∀ e (τ : T.State e) (o : T.Out e τ),
      MovesS.routeOf (T.odata e τ o) = .kcol →
      ((T.odata e τ o).mem.get (scsSelIdx C T hp e τ o)).continuing := by
  intro e τ o hk
  exact (scsSelIdx_exists C T hp e τ o).choose_spec.1 hk

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

/-- [(d) COMPILED REDUCTION — tv-g3-residuals leaf, 2026-07-31]
`scs_cluster_child` holds GIVEN the one missing row law `hselStage`: the row's
selected stage output W′·D′ = μsel·(e·g·D) equals the block size of the
hp-keyed target skeleton at continuing hp-keys.  Everything else is PROVED
here: the continuing member at `scsSelIdx` forces `cont` at the hp-key (tie
transfer `tpIsRight` + `cont_iff`), the `scsSelIdx_exists` clause-2 pins its
CTS status to `Sum.inr tgtSk`, `omem_size` reads its size as `skBlk tgtSk`,
and `tpSize` transports that size back to the table roster.  `hselStage` is
exactly the PROPOSED FENCE FIELD `sel_stage` for `SpeciesStageRow` (see the
file-header record); it is NOT derivable from the landed row (`rec_read`/
`rec_cluster` tie `spRec` at `R.key` only — nothing ties `sel`'s stage output
to `hp`'s keyed target). -/
theorem scs_cluster_child_of_selStage {n : ℕ} (C : CtsFamily n)
    (T : MovesS.TableShape n) (hp : TablePins C T)
    (R : SpeciesStageRow C T hp)
    (hselStage : ∀ e (τ : T.State e) (o : T.Out e τ)
      (hc : (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
        (tpHout C T hp e τ o).2),
      (R.sel e τ o).2 * (e * (R.sel e τ o).1 * (R.spRec e τ o).D)
        = skBlk ((C.bd (tpSk C T hp e τ)).tgtSk (tpHout C T hp e τ o).1
            (tpHout C T hp e τ o).2 hc)) :
    ∀ e (τ : T.State e) (o : T.Out e τ)
      (i : Fin (T.odata e τ o).mem.length),
      ((T.odata e τ o).mem.get i).continuing →
      i = scsSelIdx C T hp e τ o →
      ((T.odata e τ o).mem.get i).size
        = (scsSupplyCore C T hp R).W' e τ o
          * (scsSupplyCore C T hp R).D' e τ o := by
  intro e τ o i hcont hisel
  subst hisel
  have hj : ((scsSelIdx C T hp e τ o) : ℕ) < (T.odata e τ o).mem.length :=
    (scsSelIdx C T hp e τ o).isLt
  have hj' : ((scsSelIdx C T hp e τ o) : ℕ)
      < ((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2).length := by
    rw [← tpLen C T hp e τ o]; exact hj
  -- cont at the hp-key, from the continuing member at the position
  have hright : ((((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2)[((scsSelIdx C T hp e τ o) : ℕ)]'hj').status).isRight
      = true := by
    rw [← tpIsRight C T hp e τ o _ hj hj']
    exact hcont
  have hc : (C.bd (tpSk C T hp e τ)).cont (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2 :=
    ((C.bd (tpSk C T hp e τ)).cont_iff _ _).mpr
      ⟨_, List.getElem_mem hj', hright⟩
  -- the spec's clause 2 at the landed position
  have hs : (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
        (tpHout C T hp e τ o).2).get
      (Fin.cast (tpLen C T hp e τ o) (scsSelIdx C T hp e τ o))).status
      = Sum.inr ((C.bd (tpSk C T hp e τ)).tgtSk (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2 hc) :=
    (scsSelIdx_exists C T hp e τ o).choose_spec.2 hc
  -- the selected member's size at the CTS roster = skBlk tgtSk
  have hsz : skBlk ((C.bd (tpSk C T hp e τ)).tgtSk (tpHout C T hp e τ o).1
      (tpHout C T hp e τ o).2 hc)
      = (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2).get
        (Fin.cast (tpLen C T hp e τ o) (scsSelIdx C T hp e τ o))).size :=
    (C.bd (tpSk C T hp e τ)).omem_size _ _ _ (List.get_mem _ _) _ hs
  -- transport the size back to the table roster
  have hmem : ((T.odata e τ o).mem.get (scsSelIdx C T hp e τ o)).size
      = (((C.bd (tpSk C T hp e τ)).omem (tpHout C T hp e τ o).1
          (tpHout C T hp e τ o).2).get
        (Fin.cast (tpLen C T hp e τ o) (scsSelIdx C T hp e τ o))).size :=
    tpSize C T hp e τ o _ hj hj'
  rw [hmem, ← hsz]
  exact (hselStage e τ o hc).symm

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
