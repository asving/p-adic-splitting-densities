/-
BP_VI §1.1 — the (ROOT-C) hypothesis surface (`Hypotheses.lean`).
Units in this file: VI-H0 (module header, below) · VI-H1 (`RootHyps`) ·
VI-H2 (`ClauseRHyps`/`ClauseUBHyps`/`clauseR_of_clauseUB`) · VI-H3
(`trivialRootHyps` + honesty gate).
-/
import Mathlib

/-!
# The (ROOT-C) hypothesis surface [SHARED, wave VI-0]

**PROVENANCE (unit VI-H0; BP_VI §1.1 head).**

* Blueprint: `lean/blueprints/BP_VI.md` §1.1 (units VI-H0–VI-H3 land here).
* Authority: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"AUTHORITY (Asvin,
  2026-08-03): THE LEAN CONVERSION SWARM" (ground rules) + §"AUTHORITY (Asvin,
  2026-08-01): THE PROOF SCAFFOLD" (the target statement shape).
* Math source of record: `docs/ROOT_ASSEMBLY_2026-08-02.md` at **REVISION 5** —
  §1 (ROOT)/(ROOT-C), §3.1 rows (H1)–(H6).
* Imports: `Mathlib` only (deliberately light — every division imports this file).

## ROOT §3.1 row map (field ↔ ledger row, with revision pointers)

Division-interface contract (binding on BP_I–BP_V): every division statement
consuming a §3.1 [M] row takes `H : RootHyps n` and names the field in its
binder list (e.g. `(hadm : H.h3_adm)`) — never a fresh anonymous `Prop`, never
a parallel second hypothesis surface.

| field | ROOT §3.1 row | revision pointer |
|---|---|---|
| `h1_grb` | (H1) = (GR-B): anchored-march residue-structure package at OM orders ≥ 2 (frame tie + residual-dictionary march, FGMN Thm 4.2 model, properness proviso) | order ≤ 1 PROVED (VERIFIED leaf #4, GD23) |
| `h2_fresh` | (H2) = (FRESH): joint-with-parent level-determinacy separation (O-9's named open), incl. clause (c) = the former JUNCTION-PIN | REVISION 1, finding 4 |
| `h3_d12r` | (H3) leg 1 = D-12r: TB-CAP's (τ-irr) completeness perimeter | — |
| `h3_en` | (H3) leg 2 = (E-N): O-1thr Theorem 3(c)'s exhaustion caveat | — |
| `h3_adm` | (H3) leg 3 = (ADM), THE OPERATIVE FORM (O-9 r4, FULL attainment): dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d at every on-line lattice slot; automatic at r = 0 ONLY | NEW at REVISION 2 (V2-5); rewritten at REVISION 4 (VC4-2) |
| `h4a_r1r4` | (H4a) = (R1)–(R4): the T-1 stage-tower laws verbatim over O_δ = W(F_{p^δ}); NOT clause-(UB)-only (clause (R) consumes it through Step 18's K3-c) | re-scoped at REVISION 2 (V2-2) |
| `h4b_rebase` | (H4b)(a) = (UB-X)(a): the per-leaf O_δ re-base audit | (UB-X) NEW at REVISION 1 (finding 7) |
| `h4b_stable` | (H4b)(b) = (UB-X)(b): δ-stable position classes exhaust the realized ledger at every δ | — |
| `h4b_k3delta` | (K3-δ) = (UB-X)(b) RESTRICTED to Step-18 K3-c's realized δ > 1 pools — the named fragment clause (R) consumes | REVISION 4 (VC4-1) |
| `stable_implies_k3delta` | the fragment law, DISPLAYED: full (UB-X)(b) implies its (K3-δ) fragment | REVISION 4 (VC4-1) |
| `h4b_commute` | (H4b)(c) = (UB-X)(c): full solve + type aggregation commute with unramified base change | — |
| `h5_pack` | (H5) = (PACK): the actual-pack correspondence (D-11's open clause 4) — the concrete assembled pack = the intended 𝔅_n instantiation entry-for-entry | NEW at REVISION 4 (VC4-3) |
| `h6_tdec` | (H6)(a1) = (T-DEC): CU-2t terminal row — emission discipline at decided sites ((T-DEC-dec)) + the corner fence ((T-DEC-cor)) | (H6) group NEW at REVISION 5 (VC5-1/VC5-2) |
| `h6_tread` | (H6)(a2) = (T-READ): emitted shape/position fields = the (c1)-shape polygon-side datum ((RC-read) supply; GD-2/GD-5 family per CU-2t R4) | REVISION 5 (VC5-1/VC5-2) |
| `h6_tverd` | (H6)(a3) = (T-VERD): terminal verdict-field conformance | REVISION 5 (VC5-1/VC5-2) |
| `h6_vii` | (H6)(b) = D-11 widened-charge item (vii): general-n H.6 in-fence conformance of the built tables (consumed at Step 18's K3-a) | REVISION 5 (VC5-1) |

Per-clause attribution (ROOT §1, the (ROOT-C) attribution display; clauses
(0)/(SQ) unconditional — REVISION 4, finding VC4-4 — so they get NO selector):
clause (R) ← (H1)–(H3) + (H4a) + (H5) + (K3-δ) + (H6);
clause (UB) ← (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6).

## Design rule (the theoremU precedent)

Per `MovesU/U10_theoremU.lean` round-2 CRITICAL 1 + the wave-4-boundary record:
a row whose owner vocabulary is ABSENT from the built corpus stays a bare
`Prop` — but as a NAMED, VISIBLE field, never an axiom, never a bundled tag.
At blueprint time ALL sixteen rows are bare `Prop` fields, True-instantiable:
the conditionality claim of record MUST list consumed fields as UNPINNED named
assumptions until their typed carriers land. The standing upgrade path is
FIELD REFINEMENT (bare `Prop` → typed `Prop` over built carriers), executed as
a REVISION of this file when a division lands the carrier.

## Sync duty (BP_VI §5; owner: BP_VI)

This file transcribes ROOT ASSEMBLY at REVISION 5. If a further ROOT revision
changes the (ROOT-C) hypothesis list or the per-clause attribution, the DELTA
lands FIRST in BP_VI §1.1/§1.2, THEN here — the ledger's math-revision sync
duty. Field refinement lands HERE (one revision, BP_VI owner, Codex
plan-review per the standing rule) and the division re-keys. Standing honesty
rule: `RootHyps` presence is UNPINNED until field refinement — no acceptance
claim may read a consumed field as discharged.
-/

namespace LeanUrat.Scaffold

/-- **`RootHyps n` — the (ROOT-C) hypothesis rows (H1)–(H6), ROOT §3.1 verbatim.**
    THE swarm's shared hypothesis surface: every division statement that consumes
    a §3.1 [M] row takes `H : RootHyps n` and names the field. TRANSCRIPTION
    DEVICE at E-phase (the theoremU wave-4-boundary rule): all fields are bare
    `Prop`, True-instantiable (see `trivialRootHyps`) — the conditionality claim
    of record MUST list consumed fields as UNPINNED named assumptions until their
    typed carriers land. `n` is the degree key (phantom until fields are typed). -/
structure RootHyps (n : ℕ) where
  /-- (H1) = (GR-B) at OM orders ≥ 2: the anchored-march residue-structure package
      (frame tie + residual-dictionary march, FGMN Thm 4.2 model, properness
      proviso). Order ≤ 1 is PROVED (VERIFIED leaf #4, GD23). -/
  h1_grb      : Prop
  /-- (H2) = (FRESH): the joint-with-parent level-determinacy separation clause
      (O-9's named open), incl. clause (c) = the former JUNCTION-PIN. -/
  h2_fresh    : Prop
  /-- (H3), leg 1 = D-12r: TB-CAP's (τ-irr) completeness perimeter. -/
  h3_d12r     : Prop
  /-- (H3), leg 2 = (E-N): O-1thr Theorem 3(c)'s exhaustion caveat. -/
  h3_en       : Prop
  /-- (H3), leg 3 = (ADM), THE OPERATIVE FORM (O-9 r4, FULL attainment):
      dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d at every on-line lattice slot.
      Automatic at r = 0 ONLY (ROOT REVISION 4, finding VC4-2). -/
  h3_adm      : Prop
  /-- (H4a) = (R1)–(R4): the T-1 stage-tower laws verbatim over O_δ = W(F_{p^δ}).
      NOT clause-(UB)-only — consumed by clause (R) through Step 18's K3-c. -/
  h4a_r1r4    : Prop
  /-- (H4b)(a) = (UB-X)(a): the per-leaf O_δ re-base audit. -/
  h4b_rebase  : Prop
  /-- (H4b)(b) = (UB-X)(b): δ-stable position classes exhaust the realized
      ledger at every δ. -/
  h4b_stable  : Prop
  /-- (K3-δ) = (UB-X)(b) RESTRICTED to Step-18 K3-c's realized δ > 1 pools —
      the named fragment clause (R) consumes (ROOT REVISION 4, finding VC4-1). -/
  h4b_k3delta : Prop
  /-- The fragment law, DISPLAYED: full (UB-X)(b) implies its (K3-δ) fragment. -/
  stable_implies_k3delta : h4b_stable → h4b_k3delta
  /-- (H4b)(c) = (UB-X)(c): full solve + type aggregation commute with
      unramified base change. -/
  h4b_commute : Prop
  /-- (H5) = (PACK): the actual-pack correspondence (D-11's open clause 4) —
      the concrete assembled pack = the intended 𝔅_n instantiation
      entry-for-entry (ROOT REVISION 4, finding VC4-3). -/
  h5_pack     : Prop
  /-- (H6)(a1) = (T-DEC): CU-2t terminal row — emission discipline at decided
      sites ((T-DEC-dec)) + the corner fence ((T-DEC-cor)). -/
  h6_tdec     : Prop
  /-- (H6)(a2) = (T-READ): emitted shape/position fields = the (c1)-shape
      polygon-side datum (the (RC-read) supply; GD-2/GD-5 family per CU-2t R4). -/
  h6_tread    : Prop
  /-- (H6)(a3) = (T-VERD): terminal verdict-field conformance. -/
  h6_tverd    : Prop
  /-- (H6)(b) = D-11 widened-charge item (vii): general-n H.6 in-fence
      conformance of the built tables (consumed at Step 18's K3-a). -/
  h6_vii      : Prop

/- Unit VI-H2: per-clause selectors — the attribution display of ROOT §1
(ROOT-C), transcribed EXACTLY (clauses (0)/(SQ) unconditional — REVISION 4,
finding VC4-4 — so they get NO selector; clause (R) ← (H1)–(H3) + (H4a) +
(H5) + (K3-δ) + (H6); clause (UB) ← (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6)).
Deps: VI-H1. -/

/-- Clause (R)'s hypothesis set, per the (ROOT-C) attribution display. -/
def ClauseRHyps {n : ℕ} (H : RootHyps n) : Prop :=
  H.h1_grb ∧ H.h2_fresh ∧ (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_k3delta ∧ H.h5_pack ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii)

/-- Clause (UB)'s hypothesis set, transcribed directly: full (H4b)(b) is
    primitive here; the K3-δ fragment is derived only when clause (R) is needed. -/
def ClauseUBHyps {n : ℕ} (H : RootHyps n) : Prop :=
  H.h1_grb ∧ H.h2_fresh ∧ (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_rebase ∧ H.h4b_stable ∧ H.h4b_commute ∧ H.h5_pack ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii)

theorem clauseR_of_clauseUB {n : ℕ} {H : RootHyps n} :
    ClauseUBHyps H → ClauseRHyps H :=
  fun ⟨h1, h2, h3, h4a, _, hstable, _, h5, h6⟩ =>
    ⟨h1, h2, h3, h4a, H.stable_implies_k3delta hstable, h5, h6⟩

/- Unit VI-H3: the all-`True` instance + the honesty gate. Deps: VI-H2. -/

/-- The all-`True` instance of `RootHyps` (every hypothesis-row field `True`,
    the fragment law `id`) — the honesty gate's witness that the rows are
    True-instantiable at E-phase. -/
def trivialRootHyps (n : ℕ) : RootHyps n where
  h1_grb      := True
  h2_fresh    := True
  h3_d12r     := True
  h3_en       := True
  h3_adm      := True
  h4a_r1r4    := True
  h4b_rebase  := True
  h4b_stable  := True
  h4b_k3delta := True
  stable_implies_k3delta := id
  h4b_commute := True
  h5_pack     := True
  h6_tdec     := True
  h6_tread    := True
  h6_tverd    := True
  h6_vii      := True

/-- HONESTY GATE (the wave-4-boundary display, machine-checked): `RootHyps` and
    its selectors are transcription devices, not mathematical discharge. Any
    theorem claiming `RootC` must also expose the typed division results that
    consume the selected rows; `ClauseRHyps`/`ClauseUBHyps` alone is insufficient. -/
theorem trivialRootHyps_ub (n : ℕ) : ClauseUBHyps (trivialRootHyps n) := by
  simp [ClauseUBHyps, trivialRootHyps]

end LeanUrat.Scaffold
