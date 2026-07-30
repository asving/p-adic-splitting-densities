/-  TV-F3 (BRIDGE BP3, cluster c5; E-phase skeleton) — INTERP + DEGREE LAWS:
    the six degree ties at tableShape_inst's REAL Wloc/Wstate against cp's
    degree laws, plus the ι countS = 1 leg (PROVED here, inherited from
    TV-F1's choice-spec projection).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F3).
    deps: TV-F2 (the seam carrier + coherence bundle).  Consumers: TV-F5.

    RESOLUTIONS (recorded):
    (1) The interp laws themselves (tg_interp/j_interp routeOf case split,
      ι_interp, jcell_interp) are the `SeamCoherent` value fields of TV-F2 —
      already in RatBurdens' evalAt form there; this unit adds what remains
      of the RatBurdens law roster on the polynomial side: the SIX degree
      ties (tg_degT/tg_degS/j_degT/j_degS/ι_degT/ι_degS) and ι_countS_one.
      ι_count is `SeamCoherent.iota_count` (TV-F2) — noted, not re-typed.
    (2) The degree ties are FIELDS of a Prop bundle (`SeamDegreeLaws`), not
      parametric universals: for an arbitrary keying K they can fail, and a
      sorried false universal is barred (honest-sorries discipline).  The ∃
      below asserts them at the co-designed witness only.
    (3) Typing-time observation for the prover (recorded, not resolved): the
      pack bounds are cp's C.Wloc-genre bounds (`jcellPG.degBoundT = C.Wloc
      d.s d.m`, `tgPGof`'s per TV-F1's pins), while the tie targets are the
      pinned table's `T.Wloc e τ o = C.Wloc τ.s (hout o).1` and `T.Wstate e τ
      = (C.bd τ.s).Wstate` (V7_ts TablePins clauses (3)-(4)) — the ties hold
      exactly when the keying matches the TablePins equivs; that match is the
      co-design content, proved at the witness. -/
import LeanUrat.MovesV.TV_F2

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-F3 (ι countS leg, PROVED): `RatBurdens.ι_countS_one` at the seam pack —
inherited from TV-F1's `iotaPGof_countS_one` (the choose_spec projection of
the PROVED `ratBurdens_iota` ∃), for EVERY keying. -/
theorem seamIotaP_countS_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) (e : ℕ) (τ : T.State e) (ε : M.EntShape e τ) :
    (seamIotaP V X hEU hEC hA hdom K e τ ε).countS = 1 :=
  iotaPGof_countS_one V X hEU hEC hA hdom (K.entKey e τ ε).1 (K.entKey e τ ε).2

/-- TV-F3 THE DEGREE-TIE BUNDLE: the six `RatBurdens` degree laws at the seam
packs — countT bounds tied to the pinned table's REAL `Wloc`, countS bounds
to `Wstate`, and the entrance pack's bounds to `M.Went` (mirroring
tg_degT/tg_degS/j_degT/j_degS/ι_degT/ι_degS field-for-field). -/
structure SeamDegreeLaws {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) : Prop where
  tg_degT : ∀ e (τ : T.State e) (o : T.Out e τ),
    (seamTgP V X cp K e τ o).degBoundT = T.Wloc e τ o
  tg_degS : ∀ e (τ : T.State e) (o : T.Out e τ),
    (seamTgP V X cp K e τ o).degBoundS = T.Wstate e τ
  j_degT : ∀ e (τ : T.State e) (o : T.Out e τ),
    (seamJP V X cp J K e τ o).degBoundT = T.Wloc e τ o
  j_degS : ∀ e (τ : T.State e) (o : T.Out e τ),
    (seamJP V X cp J K e τ o).degBoundS = T.Wstate e τ
  ι_degT : ∀ e (τ : T.State e) (ε : M.EntShape e τ),
    (seamIotaP V X hEU hEC hA hdom K e τ ε).degBoundT = M.Went e τ ε
  ι_degS : ∀ e (τ : T.State e) (ε : M.EntShape e τ),
    (seamIotaP V X hEU hEC hA hdom K e τ ε).degBoundS = M.Went e τ ε

/-- TV-F3 UNIT CLAIM: the TV-F2 witness additionally carries the degree ties
(the cumulative ∃ — one witness thread through the cluster, so the seam stays
SHARED; separate ∃-eliminations do not compose, blueprint finding 7).
Sketch: at the co-designed witness the tg/j ties are cp's `deg`/`T_deg`
bounds read through TablePins' literal equivs (V7_ts installs `Wloc := C.Wloc`,
`Wstate := (C.bd s).Wstate`); the ι ties are the `initRat_comp` pack's Went
bounds at E2's entrance shapes. -/
theorem seam_degree_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T)
      (K : SeamKeys V T M),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      SeamCoherent V X cp J hEU hEC hA hdom K ∧
      SeamDegreeLaws V X cp J hEU hEC hA hdom K := by
  sorry

end LeanUrat.MovesV
