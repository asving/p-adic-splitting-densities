/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.O12.Family

/-!
# Scaffold/HDischarge/H5/Defs — Wave-0 carriers [HDISCHARGE_H5 units D1, D2]

Transcription of `lean/blueprints/HDISCHARGE_H5.md` §4.2 (statements VERBATIM,
compile-probed at the blueprint session). This file is the H5 trust surface:
Codex statement-audit REQUIRED before any consumption.

Unit D1: the carriers `ExitData` / `tRow` / `displayedRow`.
Unit D2 (REVISION 2 form): the carriers `REWitness` / `MassFacts`.

Faithfulness deltas for D2, DISPLAYED (blueprint §2.5, §4.2) — granularity
residues are displayed, never claimed discharged:
* (δ1) the corpus `BookingSystem` carries ONE booking for the whole member, so
  "EVERY block booked re-entrantly" compiles to the single-field disequality
  `booking_reentrant` — faithful at the corpus's own granularity (BP_II
  transcribed 𝔅_n that way).
* (δ4) the no-α adjudication: "(RE): the member carries NO allocation datum at
  any block" CANNOT compile as field-absence (the corpus `BnCoordinates`
  carries an `allocation` coordinate on every member). Its compilation here is
  the ROW-FORM pair `row_eq_displayed` + `trow_canonical`: the member's carried
  rows equal the canonical assembly with ONLY the displayed booking adjustments
  — any α-adjustment term (the `gramOver_allocAdjust` shape) would refute the
  equality, so α-freeness of the ROWS is a consequence, while the inert
  coordinate remains as data. HONESTY RESIDUE: the (RE) sentence is STRONGER as
  worded (a member could carry a spurious α that feeds nothing); a consumer
  needing the literal no-datum clause must add it at the instance — displayed,
  not smuggled. `REWitness` carries (RE)'s OPERATIVE content; the r1 claim
  "types the (RE) conjunction exactly" is WITHDRAWN in favor of this display.
* Granularity residue (row roster): `BnMember.entries` is an un-indexed
  `Finset`, so `row_mem_entries` is the strongest member-side tie the corpus
  carrier admits; the σ-indexed identification of REALIZED table rows with
  `row` stays route-a/route-b territory — never claimed here. The O2′/O3
  presented-row conformance at a REALIZED table is likewise route-a/route-b
  (clause-4-class), NOT smuggled into D2.

Faithfulness pins (blueprint §4.2, D1):
* `rowOf` is the landed II-R8 §2.3(iv) transcription — REUSED, never redefined.
* The (O2′) leg's coefficient is PINNED = `kappa1 e` (the leaf's
  "coefficient pinned = κ₁").
* The (O3) scalar is the landed `gramOver_o3scale` shape.
* `E.idx : Type` + `Fintype` matches the finite exit roster; a Finset-based
  variant is REJECTED (`comp` needs a Π-type over per-F tuple length).
* (δ3) GUARDED-API DISCIPLINE: the `Booking.O2` branch of `displayedRow` is a
  guarded placeholder (= the unadjusted t), NEVER consumed under
  `booking_reentrant` — the same junk-value-plus-guard convention as
  `Booking.kernel` at e ≤ 1. `displayedRow` is public and its TYPE carries no
  guard, so every H5 theorem about it is keyed by an explicit booking equality
  or a `booking_reentrant` binder; an unguarded generic consumer reading the
  O2 branch reads fabricated data.
* (δ2) `ExitData` is the per-EXIT-STRATUM refinement of the per-BLOCK corpus
  aggregates (`BnCoordinates.handoffs/composition`); the aggregation
  compatibility proposition is chartered as follow-on unit F1 (BP_II-side).
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst)

/-- Per-exit-stratum data at one block: the finite exit roster `idx`, each
stratum's mass `m(F)`, hand-off list `H(F)`, and composition datum `comp_F`
(brief §2.3(iv), per-stratum refinement of the corpus per-block aggregates —
blueprint (δ2)). [HDISCHARGE_H5 unit D1] -/
structure ExitData (n : ℕ) where
  idx : Type
  instF : Fintype idx
  mass : idx → Qq
  handoff : idx → List (ℕ × ℕ+)
  comp : ∀ F : idx,
    ((i : Fin (handoff F).length) → SplittingType n) → SplittingType n

attribute [instance] ExitData.instF

/-- The canonical (unadjusted) row t: the sum over exit strata of the II-R8
verdict rows `rowOf` (REUSED landed transcription, never redefined).
[HDISCHARGE_H5 unit D1] -/
noncomputable def tRow {n : ℕ} (β : ℕ → SplittingType n → Qq)
    (E : ExitData n) (σ : SplittingType n) : Qq :=
  ∑ F : E.idx, rowOf β (E.mass F) (E.handoff F) (E.comp F) σ

/-- The per-booking displayed row: t unadjusted at (O1); the (O2′) additive
adjustment with coefficient PINNED = `kappa1 e`; the (O3) scaling in the landed
`gramOver_o3scale` shape. The `Booking.O2` branch is a GUARDED PLACEHOLDER
(= the unadjusted t) — never consumed under `booking_reentrant`; see (δ3) in
the module docstring. [HDISCHARGE_H5 unit D1] -/
noncomputable def displayedRow {n : ℕ} (b : Booking) (e : ℕ)
    (β : ℕ → SplittingType n → Qq) (E : ExitData n)
    (σ : SplittingType n) : Qq :=
  match b with
  | Booking.O1 => tRow β E σ
  | Booking.O2 => tRow β E σ   -- guarded placeholder; never consumed under (RE)
  | Booking.O2r => tRow β E σ + kappa1 e * β e σ
  | Booking.O3 => qX ^ blockE e * (qX ^ blockE e - 1)⁻¹ * tRow β E σ

/-! ## Unit D2 — carriers `REWitness` / `MassFacts` (REVISION 2 form) -/

/-- (RE) at the corpus carrier: re-entrant booking; ROW-INDEXED canonical
    rows tied to the member's entry roster; L4 descent. See the no-α
    adjudication (δ4) below — this witness carries (RE)'s OPERATIVE content
    at the corpus granularity, with the compilation choices displayed. -/
structure REWitness {n : ℕ} (T : BnMember n) where
  exits : ℕ → ExitData n
  handoff_lt : ∀ e, ∀ F : (exits e).idx, ∀ x ∈ (exits e).handoff F, x.1 < e
  booking_reentrant : T.booking ≠ Booking.O2
  trow_canonical : ∀ e (he : 2 ≤ e), (T.blocks e he).trow = tRow T.β (exits e)
  row : ℕ → SplittingType n → Qq
  row_eq_displayed : ∀ e, 2 ≤ e → e ≤ n → ∀ σ,
    row e σ = displayedRow T.booking e T.β (exits e) σ
  row_mem_entries : ∀ e σ, 2 ≤ e → e ≤ n → row e σ ∈ T.entries e

/-- The M1 shadow at the member: (EXM) + (BASE) + regularity + (MNN).
    NOT (RE) clauses. -/
structure MassFacts {n : ℕ} (T : BnMember n) (W : REWitness T) : Prop where
  base_total : ∀ e ≤ 1, (∑ σ : SplittingType n, T.β e σ) = 1
  base_nonneg : ∀ e ≤ 1, ∀ σ (q₀ : ℚ), 2 ≤ q₀ →
    ∀ h : T.β e σ ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨T.β e σ, h⟩
  mass_complete : ∀ e, 2 ≤ e → e ≤ n →
    (∑ F : (W.exits e).idx, (W.exits e).mass F) = 1 - kappa0 e - kappa1 e
  mass_memRcyc : ∀ e, ∀ F : (W.exits e).idx, MemRcyc ((W.exits e).mass F)
  mass_nonneg : ∀ e, ∀ F : (W.exits e).idx, ∀ q₀ : ℚ, 2 ≤ q₀ →
    ∀ h : (W.exits e).mass F ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨(W.exits e).mass F, h⟩

end LeanUrat.Scaffold.HDischarge.H5
