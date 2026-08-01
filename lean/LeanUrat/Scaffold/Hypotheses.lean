/-
BP_VI §1.1 — the (ROOT-C) hypothesis surface (`Hypotheses.lean`).
Units in this file: VI-H0 (module header, below) · VI-H1 (`RootHyps`) ·
VI-H2 (`ClauseRHyps`/`ClauseUBHyps`/`clauseR_of_clauseUB`) · VI-H3
(`trivialRootHyps` + honesty gate) · VI-H4 (the twelve-row ROOT sync,
SYNTHESIS_PASS3 finding F5 — this file's REVISION 1).
-/
import Mathlib

/-!
# The (ROOT-C) hypothesis surface [SHARED, wave VI-0]

**PROVENANCE (unit VI-H0; BP_VI §1.1 head).**

* Blueprint: `lean/blueprints/BP_VI.md` §1.1 (units VI-H0–VI-H3 land here).
* Authority: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"AUTHORITY (Asvin,
  2026-08-03): THE LEAN CONVERSION SWARM" (ground rules) + §"AUTHORITY (Asvin,
  2026-08-01): THE PROOF SCAFFOLD" (the target statement shape).
* Math source of record: `docs/ROOT_ASSEMBLY_2026-08-02.md` at **REVISION 13** —
  §1 (ROOT)/(ROOT-C), §3.1 the TWELVE rows ↔ groups (H1)–(H9). [REVISION 1 of
  this file = unit VI-H4, executing `docs/SYNTHESIS_PASS3_2026-08-05.md` finding
  F5: the original transcription was at ROOT REVISION 5 (rows (H1)–(H6) only) —
  the exact stale-hypothesis-enumeration genre ROOT's REVISION-12 global
  enumeration audit killed at doc level, alive here until this sync. Extension,
  not rewrite: every pre-existing field declaration is byte-stable.]
* Imports: `Mathlib` only (deliberately light — every division imports this file).
  Consequence for VI-H4: new-row fields stay BARE `Prop` even where a division
  carrier exists (the H8 `CutDefs`/`CutSeam` vocabulary, the H9 `NsfKeyProp`
  record import `MovesT`/`MovesU` — binding them here would push that graph into
  every division and invert the import direction). The docstrings NAME the
  carriers; binding is FIELD REFINEMENT per the design rule below.

## ROOT §3.1 row map (field ↔ ledger row, with revision pointers)

Division-interface contract (binding on BP_I–BP_V): every division statement
consuming a §3.1 [M] row takes `H : RootHyps n` and names the field in its
binder list (e.g. `(hadm : H.h3_adm)`) — never a fresh anonymous `Prop`, never
a parallel second hypothesis surface.

ROOTC-ENUM-AUDIT (grep anchor, keyed to ROOT §1 (ROOT-C) + §3.1 at REVISION 13;
per SYNTHESIS_PASS3 F5 this line is the loud-failure hook for the next ROOT
revision): the §3.1 roster is TWELVE rows ↔ groups (H1)–(H9); `RootHyps` carries
27 hypothesis-row `Prop` fields + 1 displayed fragment law
(`stable_implies_k3delta`); the clause selectors consume OPEN members only —
(NSF-KEY) is RETIRED (ROOT REVISION 13, r14), its field `h9_nsfkey` carried for
row fidelity and selected by NO clause.

| field | ROOT §3.1 row | revision pointer |
|---|---|---|
| `h1_grb` | (H1)(a) = (GR-B): anchored-march residue-structure package at OM orders ≥ 2 (frame tie + residual-dictionary march, FGMN Thm 4.2 model; properness-proviso LEG single-homed at the §3.3 (KP)/(KPirr) [T] row per REVISION 7, VC7-4) | order ≤ 1 PROVED (VERIFIED leaf #4, GD23); group ENLARGED at REVISION 6 (F-2/F-3) |
| `h1_gd1` | (H1)(b) = GD-1 beyond order 1 (= O-2a's open lemma OL-2a-1): the (KP)/(KPirr) representative-admissibility clauses beyond order 1 | ADDED at REVISION 6 (F-2/F-3) |
| `h1_gd6` | (H1)(c) = GD-6 conformance instances at orders ≥ 2 (= OL-2a-6's consumed face) | ADDED at REVISION 6 (F-2/F-3) |
| `h1_key1` | (H1)(d) = the order-≥ 2 KEY1 block, at READ ORDER | ADDED at REVISION 7 (VC7-1); REQUANTIFIED at REVISION 8 (VC8-1) |
| `h2_fresh` | (H2) = (FRESH): joint-with-parent level-determinacy separation (O-9's named open), incl. clause (c) = the former JUNCTION-PIN | REVISION 1, finding 4 |
| `h3_d12r` | (H3) leg 1 = D-12r: TB-CAP's (τ-irr) completeness perimeter | REWRITTEN at REVISION 13 (r14, H3 lead D12R-U4); [M]→§4 reclassification VC-GATED (rides VC16) — stays a row field until adjudicated |
| `h3_en` | (H3) leg 2 = (E-N): O-1thr Theorem 3(c)'s exhaustion caveat | REWRITTEN at the (H3) discharge adjudication (EN-U5, VC-gated) |
| `h3_adm` | (H3) leg 3 = (ADM), THE OPERATIVE FORM (O-9 r4, FULL attainment): dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d at every on-line lattice slot; automatic at r = 0 ONLY | NEW at REVISION 2 (V2-5); rewritten at REVISION 4 (VC4-2) |
| `h4a_r1r4` | (H4a) = (R1)–(R4): the T-1 stage-tower laws verbatim over O_δ = W(F_{p^δ}); NOT clause-(UB)-only (clause (R) consumes it through Step 18's K3-c) | re-scoped at REVISION 2 (V2-2) |
| `h4b_rebase` | (H4b)(a) = (UB-X)(a): the per-leaf O_δ re-base audit | (UB-X) NEW at REVISION 1 (finding 7) |
| `h4b_stable` | (H4b)(b) = (UB-X)(b): δ-stable position classes exhaust the realized ledger at every δ | — |
| `h4b_k3delta` | (K3-δ) = (UB-X)(b) RESTRICTED to Step-18 K3-c's realized δ > 1 pools — the named fragment clause (R) consumes | REVISION 4 (VC4-1) |
| `stable_implies_k3delta` | the fragment law, DISPLAYED: full (UB-X)(b) implies its (K3-δ) fragment | REVISION 4 (VC4-1) |
| `h4b_commute` | (H4b)(c) = (UB-X)(c): full solve + type aggregation commute with unramified base change | — |
| `h5_pack` | (H5) head = (PACK): the actual-pack correspondence (D-11's open clause 4) — the concrete assembled pack = the intended 𝔅_n instantiation entry-for-entry | NEW at REVISION 4 (VC4-3) |
| `h5_pack_i` | (PACK-i) = rsh_interp, row-law at the 𝔅_n rows; Step 18's K2 evaluation glue | ENLARGED at REVISION 7 (VC7-2) |
| `h5_pack_ii` | (PACK-ii) = r_bdd; Step 18's K2 evaluation glue | REVISION 7 (VC7-2) |
| `h5_pack_iii` | (PACK-iii) = wsh_ok; the membership input to Step 18's K3 evaluation ring-hom (with D-6) | REVISION 7 (VC7-2) |
| `h5_pack_iv` | (PACK-iv) = sem_alloc, the semantic verdict-row form at the intended member (D-11 r4 Thm M2's (RE)); CLOSED two-edge set: Step 18b DIRECT + Step 17's E1 delivery of (ROW-Σ) | ENLARGED AGAIN at REVISION 10 (r11, edit E4); carried into the §1 display at REVISION 12 (VC13-1) |
| `h6_tdec` | (H6)(a1) = (T-DEC): CU-2t terminal row — emission discipline at decided sites ((T-DEC-dec)) + the corner fence ((T-DEC-cor)) | (H6) group NEW at REVISION 5 (VC5-1/VC5-2) |
| `h6_tread` | (H6)(a2) = (T-READ): emitted shape/position fields = the (c1)-shape polygon-side datum ((RC-read) supply; GD-2/GD-5 family per CU-2t R4) | REVISION 5 (VC5-1/VC5-2) |
| `h6_tverd` | (H6)(a3) = (T-VERD): terminal verdict-field conformance | REVISION 5 (VC5-1/VC5-2) |
| `h6_vii` | (H6)(b) = D-11 widened-charge item (vii): general-n H.6 in-fence conformance of the built tables (consumed at Step 18's K3-a) | REVISION 5 (VC5-1) |
| `h7_itau` | (H7) leg 1 = (I-τ): the engine's realized site strata present as O-10's ρ-separated adapted cells | (H7) row NEW at REVISION 6 (F-1: O-11 r2's declared D-b) |
| `h7_kloc` | (H7) leg 2 = K-LOC (= M07 OL-3, an exactly-stated OPEN lemma): continuation reads of branch j = OM reads of f_j up to cell-constant normalization | REVISION 6 (F-1) |
| `h8_kcut` | (H8) = (K-CUT): the shallow-cut decomposition kernel — M04 Lemma 3.3's hypothesis, inside Step 18's K1 regrouping | NEW at REVISION 10 (r11, finding G-2); provenance disambiguated at REVISION 12 (VC13-4) |
| `h9_nsfint` | (H9) OPEN member = (NSF-INT): the interface implication chain pin → predicate → corpus, its TWO displayed premises (the §1.4 marks-vocabulary premise; (K1-CANON)) housed in-member | (H9) row NEW at REVISION 10 (r11) |
| `h9_nsfkey` | (H9) member (NSF-KEY): as-built keying conformance — **RETIRED**, selected by NO clause | RETIRED at REVISION 13 (r14, H9 lead adjudication; compiled record H9-U1) |

Per-clause attribution (ROOT §1, the (ROOT-C) attribution display; clauses
(0)/(SQ) unconditional — (SQ) consumes NO §3.1 row per REVISION 4, finding
VC4-4 — so they get NO selector):
clause (R) ← (H1) [all four members] + (H2) + (H3) + (H4a) + (H5) [head +
PACK-i..iv] + (K3-δ) + (H6) + (H7) + (H8) + (H9) [open member (NSF-INT)];
clause (UB) ← (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6) + (H7) + (H8) + (H9)
[open member] — the transported K1/K4 chain at q ↦ q^δ. NO clause other than
(UB) consumes (H4b) BEYOND its (K3-δ) fragment.

## Design rule (the theoremU precedent)

Per `MovesU/U10_theoremU.lean` round-2 CRITICAL 1 + the wave-4-boundary record:
a row whose owner vocabulary is ABSENT from the built corpus stays a bare
`Prop` — but as a NAMED, VISIBLE field, never an axiom, never a bundled tag.
At this revision ALL 27 hypothesis-row fields are bare `Prop`, True-instantiable:
the conditionality claim of record MUST list consumed fields as UNPINNED named
assumptions until their typed carriers land. The standing upgrade path is
FIELD REFINEMENT (bare `Prop` → typed `Prop` over built carriers), executed as
a REVISION of this file when a division lands the carrier. Refinement targets
already on file (named at their fields): the H8 cut vocabulary
(`Scaffold/HDischarge/H8/CutDefs.lean`, residual seam `VTreeCutSeam` in
`CutSeam.lean`) and the H9 (NSF-KEY) compiled record
(`Scaffold/HDischarge/H9/NsfKeyProp.lean`).

## Sync duty (BP_VI §5; owner: BP_VI)

This file transcribes ROOT ASSEMBLY at REVISION 13 (VI-H4 sync, per
SYNTHESIS_PASS3 finding F5, riding the r14 batch window — F6). If a further
ROOT revision changes the (ROOT-C) hypothesis list or the per-clause
attribution, the DELTA lands FIRST in BP_VI §1.1/§1.2, THEN here — the ledger's
math-revision sync duty; the ROOTC-ENUM-AUDIT anchor above is the greppable
check. Field refinement lands HERE (one revision, BP_VI owner, Codex
plan-review per the standing rule) and the division re-keys. Standing honesty
rule: `RootHyps` presence is UNPINNED until field refinement — no acceptance
claim may read a consumed field as discharged.
-/

namespace LeanUrat.Scaffold

/-- **`RootHyps n` — the (ROOT-C) hypothesis rows (H1)–(H9), ROOT §3.1 verbatim
    (the TWELVE-row roster at ROOT REVISION 13; VI-H4 sync).**
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
  /-- (H1)(b) = GD-1 beyond order 1 (= O-2a's exactly-stated open lemma OL-2a-1):
      the (KP)/(KPirr) representative-admissibility clauses beyond order 1 — the
      canonical key lifts form one GMN-admissible representative family at every
      order (the properness-proviso LEG stays [T] at the §3.3 (KP)/(KPirr) row).
      Group ENLARGED at ROOT REVISION 6, findings F-2/F-3. -/
  h1_gd1      : Prop
  /-- (H1)(c) = GD-6 conformance instances at orders ≥ 2 (= OL-2a-6's consumed
      face): the run-decomposition-conformance instances Step 10's conditionality
      line consumes — held on proof-by-construction ROUTES on record, which are
      not proofs (ROOT REVISION 6, findings F-2/F-3). -/
  h1_gd6      : Prop
  /-- (H1)(d) = the order-≥ 2 KEY1 block, at READ ORDER (REQUANTIFIED at ROOT
      REVISION 8, finding VC8-1): the key-compliance block KEY1 proves at order
      ≤ 1, asserted at EVERY realized site of Step 6's machine at OM order ≥ 2,
      IRRESPECTIVE of the current key's degree (degree-1-key order-≥ 2 sites,
      e.g. e·g = 1 refinement chains, INCLUDED) — exactly the complement of the
      proved order-≤ 1 slice (ADDED at ROOT REVISION 7, finding VC7-1). -/
  h1_key1     : Prop
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
  /-- (PACK-i) = rsh_interp: the first named row-law at the 𝔅_n rows, an
      explicit clause of (H5) (ROOT REVISION 7, finding VC7-2 — entry-for-entry
      equality transfers a law only if a displayed theorem supplies it on the
      𝔅_n side, and none is on file). Consumed at Step 18's K2 evaluation glue. -/
  h5_pack_i   : Prop
  /-- (PACK-ii) = r_bdd (ROOT REVISION 7, finding VC7-2). Consumed at Step 18's
      K2 evaluation glue. -/
  h5_pack_ii  : Prop
  /-- (PACK-iii) = wsh_ok (ROOT REVISION 7, finding VC7-2). The membership input
      to Step 18's K3 evaluation ring-hom (with D-6). -/
  h5_pack_iii : Prop
  /-- (PACK-iv) = sem_alloc: the semantic verdict-row form at the intended member
      (the premise D-11 r4's Theorem M2 names as (RE)) — the FOURTH row-law,
      ADDED at ROOT REVISION 10 (r11, edit E4; carried into the §1 display at
      REVISION 12, finding VC13-1). Consumed at its CLOSED two-edge set:
      Step 18b DIRECT + Step 17's E1 delivery display of (ROW-Σ). -/
  h5_pack_iv  : Prop
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
  /-- (H7), leg 1 = (I-τ): the engine's realized site strata present as O-10's
      ρ-separated adapted cells (the adapted-cell conformance face of O-11 r2's
      declared D-b; row NEW at ROOT REVISION 6, finding F-1). Consumed by clause
      (R) at Step 15's application-to-engine-strata line and Step 18's K1;
      clause (UB) inherits through the transported chain. -/
  h7_itau     : Prop
  /-- (H7), leg 2 = K-LOC (= M07 OL-3, an exactly-stated OPEN lemma):
      continuation reads of branch j = OM reads of f_j up to cell-constant
      normalization (ROOT REVISION 6, finding F-1). -/
  h7_kloc     : Prop
  /-- (H8) = (K-CUT): the shallow-cut decomposition kernel (row NEW at ROOT
      REVISION 10, r11, from finding G-2; provenance disambiguated at REVISION
      12, finding VC13-4): exactly-one shallow decomposition with
      exhaustive-exclusive read ownership + the weight-preserving product law
      μ(fiber T) = W(Ŝ)·∏ᵢ weight(Dᵢ) — M04 Lemma 3.3's hypothesis, consumed
      inside Step 18's K1 regrouping. FIELD-REFINEMENT TARGET on file: the H8
      division's cut vocabulary (`Scaffold/HDischarge/H8/CutDefs.lean`) and
      residual seam `VTreeCutSeam` (`Scaffold/HDischarge/H8/CutSeam.lean`);
      this field is the owed "one-line `RootHyps` extension" of
      `Scaffold/HDischarge/H8/R2RootSync.lean` §E.2, landed at VI-H4. -/
  h8_kcut     : Prop
  /-- (H9) OPEN member = (NSF-INT): the ns-routing interface implication chain
      pin → predicate → corpus, its TWO displayed premises (the §1.4
      marks-vocabulary premise and (K1-CANON)) housed in-member (row NEW at ROOT
      REVISION 10, r11; the (K1-CANON) discharge is owed). Enters Step 18's
      K1/K4 chain and Step 17's M3 leg (via Steps 11/12). -/
  h9_nsfint   : Prop
  /-- (H9) member (NSF-KEY): as-built keying conformance — **RETIRED at ROOT
      REVISION 13 (r14, the H9 lead's ledger adjudication)**: holds at HEAD by
      construction of (†7) over the guarded carrier; compiled-proposition record
      H9-U1, `Scaffold/HDischarge/H9/NsfKeyProp.lean` (Lean-core). Carried here
      for twelve-row fidelity ONLY; consumed by NO clause selector below. -/
  h9_nsfkey   : Prop

/- Unit VI-H2: per-clause selectors — the attribution display of ROOT §1
(ROOT-C), transcribed EXACTLY at REVISION 13 (clauses (0)/(SQ) unconditional —
REVISION 4, finding VC4-4 — so they get NO selector; clause (R) ← (H1) [four
members] + (H2) + (H3) + (H4a) + (H5) [head + PACK-i..iv] + (K3-δ) + (H6) +
(H7) + (H8) + (H9); clause (UB) ← (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6) +
(H7) + (H8) + (H9). (H9) enters through its OPEN member (NSF-INT) only:
(NSF-KEY) is RETIRED (REVISION 13, r14), so selecting `h9_nsfkey` would
misdisplay a discharged member as an open assumption. NO clause other than
(UB) consumes (H4b) beyond its (K3-δ) fragment). Deps: VI-H1. -/

/-- Clause (R)'s hypothesis set, per the (ROOT-C) attribution display
    (ROOT REVISION 13; (H9) through its open member (NSF-INT)). -/
def ClauseRHyps {n : ℕ} (H : RootHyps n) : Prop :=
  (H.h1_grb ∧ H.h1_gd1 ∧ H.h1_gd6 ∧ H.h1_key1) ∧ H.h2_fresh ∧
    (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_k3delta ∧
    (H.h5_pack ∧ H.h5_pack_i ∧ H.h5_pack_ii ∧ H.h5_pack_iii ∧ H.h5_pack_iv) ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii) ∧
    (H.h7_itau ∧ H.h7_kloc) ∧ H.h8_kcut ∧ H.h9_nsfint

/-- Clause (UB)'s hypothesis set, transcribed directly: full (H4b)(b) is
    primitive here; the K3-δ fragment is derived only when clause (R) is needed
    ((H9) through its open member (NSF-INT)). -/
def ClauseUBHyps {n : ℕ} (H : RootHyps n) : Prop :=
  (H.h1_grb ∧ H.h1_gd1 ∧ H.h1_gd6 ∧ H.h1_key1) ∧ H.h2_fresh ∧
    (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_rebase ∧ H.h4b_stable ∧ H.h4b_commute ∧
    (H.h5_pack ∧ H.h5_pack_i ∧ H.h5_pack_ii ∧ H.h5_pack_iii ∧ H.h5_pack_iv) ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii) ∧
    (H.h7_itau ∧ H.h7_kloc) ∧ H.h8_kcut ∧ H.h9_nsfint

theorem clauseR_of_clauseUB {n : ℕ} {H : RootHyps n} :
    ClauseUBHyps H → ClauseRHyps H :=
  fun ⟨h1, h2, h3, h4a, _, hstable, _, h5, h6, h7, h8, h9⟩ =>
    ⟨h1, h2, h3, h4a, H.stable_implies_k3delta hstable, h5, h6, h7, h8, h9⟩

/- Unit VI-H3: the all-`True` instance + the honesty gate. Deps: VI-H2. -/

/-- The all-`True` instance of `RootHyps` (every hypothesis-row field `True`,
    the fragment law `id`) — the honesty gate's witness that the rows are
    True-instantiable at E-phase. -/
def trivialRootHyps (n : ℕ) : RootHyps n where
  h1_grb      := True
  h1_gd1      := True
  h1_gd6      := True
  h1_key1     := True
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
  h5_pack_i   := True
  h5_pack_ii  := True
  h5_pack_iii := True
  h5_pack_iv  := True
  h6_tdec     := True
  h6_tread    := True
  h6_tverd    := True
  h6_vii      := True
  h7_itau     := True
  h7_kloc     := True
  h8_kcut     := True
  h9_nsfint   := True
  h9_nsfkey   := True

/-- HONESTY GATE (the wave-4-boundary display, machine-checked): `RootHyps` and
    its selectors are transcription devices, not mathematical discharge. Any
    theorem claiming `RootC` must also expose the typed division results that
    consume the selected rows; `ClauseRHyps`/`ClauseUBHyps` alone is insufficient. -/
theorem trivialRootHyps_ub (n : ℕ) : ClauseUBHyps (trivialRootHyps n) := by
  simp [ClauseUBHyps, trivialRootHyps]

end LeanUrat.Scaffold
